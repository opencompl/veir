import Veir.Parser.Parser
import Veir.IR.Basic

open Veir.Parser.Lexer
open Veir.Parser

namespace Veir.AttrParser

structure AttrParserState

abbrev AttrParserM := StateT AttrParserState (EStateM String ParserState)

/--
  Execute the action with the given initial state.
  Returns the result along with the final state, or an error message.
-/
def AttrParserM.run (self : AttrParserM α)
  (attrState : AttrParserState) (parserState: ParserState) : Except String (α × AttrParserState × ParserState) :=
  match (StateT.run self attrState).run parserState with
  | .ok (a, attrState) parserState => .ok (a, attrState, parserState)
  | .error err _ => .error err

/--
  Execute the action with the given initial state.
  Returns the result or an error message.
-/
def AttrParserM.run' (self : AttrParserM α)
  (attrState : AttrParserState) (parserState: ParserState) : Except String α :=
  match self.run attrState parserState with
  | .ok (a, _, _) => .ok a
  | .error err => .error err

/--
  Parse an optional integer type.
  An integer type is represented as `i` followed by a positive integer indicating its width, e.g., `i32`.
-/
def parseOptionalIntegerType : AttrParserM (Option IntegerType) := do
  match ← peekToken with
  | { kind := .bareIdent, slice := slice } =>
    if slice.size < 2 then
      return none
    if (← (getThe ParserState)).input.getD slice.start 0 == 'i'.toUInt8 then
      let bitwidthSlice : Slice := {start := slice.start + 1, stop := slice.stop}
      let identifier := bitwidthSlice.of (← (getThe ParserState)).input
      let some bitwidth := (String.fromUTF8? identifier).bind String.toNat? | return none
      let _ ← consumeToken
      return some (IntegerType.mk bitwidth)
    return none
  | _ => return none

/--
  Parse the MLIR builtin `index` type. Spelled `index` as a bare keyword
  (no `!` prefix and no parameters).
-/
def parseOptionalIndexType : AttrParserM (Option IndexType) := do
  if ← parseOptionalKeyword "index".toByteArray then
    return some IndexType.mk
  return none

/--
  Parse an optional register type, which is fundamentally a wrapper for `i64`.
  A register type is represented as `!reg`.
-/
def parseOptionalRegisterType : AttrParserM (Option RegisterType) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "reg".toByteArray then return none
  let _ ← consumeToken
  return some RegisterType.mk

/--
  Parse an integer type, throwing an error if it is not present.
  An integer type is represented as `i` followed by a positive integer indicating
  its width, e.g., `i32`.
-/
def parseIntegerType (errorMsg : String := "integer type expected") : AttrParserM IntegerType := do
  match ← parseOptionalIntegerType with
  | some integerType => return integerType
  | none => throw errorMsg

/--
  Parse a register type, throwing an error if it is not present.
  An integer type is represented as `!reg`
-/
def parseRegisterType (errorMsg : String := "register type expected") : AttrParserM RegisterType := do
  match ← parseOptionalRegisterType with
  | some registerType => return registerType
  | none => throw errorMsg

/--
  Parse an integer attribute, if present.
  An integer attribute has the form `false`, `true` or `value : type`, where `value` is an
  integer literal and `type` is an integer type.
-/
def parseOptionalIntegerAttr : AttrParserM (Option IntegerAttr) := do
  if (← parseOptionalKeyword "false".toByteArray) then
    return some (IntegerAttr.mk 0 (IntegerType.mk 1))
  if (← parseOptionalKeyword "true".toByteArray) then
    return some (IntegerAttr.mk 1 (IntegerType.mk 1))

  let some value ← parseOptionalInteger false true
    | return none
  parsePunctuation ":"
  let integerType ← parseIntegerType "integer type expected after ':' in integer attribute"
  return some (IntegerAttr.mk value integerType)

/--
  Parse a string attribute, if present.
  Its syntax is a string literal enclosed in double quotes, e.g., `"foo"`.
-/
def parseOptionalStringAttr : AttrParserM (Option StringAttr) := do
  let some str ← parseOptionalStringLiteral
    | return none
  return some (StringAttr.mk str.toByteArray)

/--
  Parse a string attribute.
  Its syntax is a string literal enclosed in double quotes, e.g., `"foo"`.
-/
def parseStringAttr (errorMsg : String := "string attribute expected") :
    AttrParserM StringAttr := do
  match ← parseOptionalStringAttr with
  | some stringAttr => return stringAttr
  | none => throw errorMsg

/--
  Parse a unit attribute, if present.
  Its syntax is the keyword `unit`.
-/
def parseOptionalUnitAttr : AttrParserM (Option UnitAttr) := do
  if ← parseOptionalKeyword "unit".toByteArray then
    return some UnitAttr.mk
  return none

/--
  Parse a dense array attribute, if present.
  Its syntax is `array<iN>` or `array<iN: v1, v2, ...>`.
-/
def parseOptionalDenseArrayAttr : AttrParserM (Option DenseArrayAttr) := do
  if !(← parseOptionalKeyword "array".toByteArray) then
    return none
  parsePunctuation "<"
  let elementType ← parseIntegerType "integer type expected in dense array attribute"
  let mut values : Array Int := #[]
  if ← parseOptionalPunctuation ":" then
    values ← parseList (parseInteger false true)
  parsePunctuation ">"
  return some (DenseArrayAttr.mk elementType values)

def isClosingBracket (kind : TokenKind) : Bool :=
  kind = .greater || kind = .rParen || kind = .rSquare || kind = .rBrace

def isOpeningBracket (kind : TokenKind) : Bool :=
  kind = .less || kind = .lParen || kind = .lSquare || kind = .lBrace

def matchingBracket! (kind : TokenKind) : TokenKind :=
  match kind with
  | .greater => .less
  | .rParen => .lParen
  | .rSquare => .lSquare
  | .rBrace => .lBrace
  | .less => .greater
  | .lParen => .rParen
  | .lSquare => .rSquare
  | _ => .rBrace

/--
  Parse the body of an unregistered attribute, which is a balanced
  string for `<`, `(`, `[`, `{`, and may contain string literals.
  The opening token is expected to have already been consumed when this function is called.
  The ending token (by default `>`) is not consumed by this function.
-/
private def parseUnregisteredAttrBody (endToken : TokenKind := .greater) (startPos : Option Nat := none) : AttrParserM String := do
  let startPos := startPos.getD (← peekToken).slice.start

  /- This stack corresponds to the brackets that are still open. -/
  let mut bracketStack : Array TokenKind := #[]
  let mut endPos : Nat := 0

  /- Read tokens one by one until we close the last `>` -/
  repeat
    let token ← peekToken

    /- Open a new bracket -/
    if isOpeningBracket token.kind then
      let _ ← consumeToken
      bracketStack := bracketStack.push token.kind

    /- Close a bracket -/
    else if isClosingBracket token.kind then
      let expected := matchingBracket! token.kind
      let closingName := match token.kind with
        | .greater => "`>`" | .rParen => "`)`" | .rSquare => "`]`" | _ => "`}`"
      /- If we don't have any open bracket, either we end the parsing if
         the bracket is the last `>`, or we raise an error. -/
      if bracketStack.isEmpty then
        if token.kind == endToken then
          endPos := token.slice.start
          break
        throw s!"unexpected closing bracket {closingName} in attribute body"
      /- If we have an open bracket, check that we are closing it
         with the right bracket kind. -/
      if bracketStack.back! != expected then
        throw s!"unexpected closing bracket {closingName} in attribute body"
      let _ ← consumeToken
      bracketStack := bracketStack.pop

    /- Checking for unexpected EOF -/
    else if token.kind == .eof then
      throw "unexpected end of file before closing of attribute body"

    /- Other tokens -/
    else
      let _ ← consumeToken
  let input := (← getThe ParserState).input
  let body := (Slice.mk startPos endPos).of input
  match String.fromUTF8? body with
  | some s => return s
  | none => throw "failed converting attribute body to string"

/--
  Parse a dialect type, if present.
  A dialect attribute has the form `!dialect.name` or `!dialect.name<body>`.
-/
partial def parseOptionalDialectType : AttrParserM (Option TypeAttr) := do
  let startPos ← getPos
  let dialectName ← parseOptionalPrefixedKeyword .exclamationIdent
  let some dialectName := dialectName | return none
  if let true ← parseOptionalPunctuation "<" then
    let _ ← parseUnregisteredAttrBody
    let endPos := (← peekToken).slice.stop
    parsePunctuation ">"
    let value := (Slice.mk startPos endPos).of (← getThe ParserState).input
    return some (⟨UnregisteredAttr.mk (String.fromUTF8! value) true, by grind⟩)
  else
    return some (⟨UnregisteredAttr.mk ("!" ++ String.fromUTF8! dialectName) true, by grind⟩)

/--
  Parse a dialect attribute, if present.
  A dialect attribute has the form `#dialect.name<body>`.
-/
partial def parseOptionalDialectAttr : AttrParserM (Option Attribute) := do
  let startPos ← getPos
  let dialectName ← parseOptionalPrefixedKeyword .hashIdent
  let some dialectName := dialectName | return none
  parsePunctuation "<"
  let _ ← parseUnregisteredAttrBody
  let endPos := (← peekToken).slice.stop
  parsePunctuation ">"
  let value := (Slice.mk startPos endPos).of (← getThe ParserState).input
  return some (UnregisteredAttr.mk (String.fromUTF8! value) false)

/--
  Parse a flat symbol reference attribute, if present.
  Its syntax is `@ident` or `@"string"`.
-/
def parseOptionalFlatSymbolRefAttr : AttrParserM (Option FlatSymbolRefAttr) := do
  let some name ← parseOptionalPrefixedKeyword .atIdent | return none
  return some (FlatSymbolRefAttr.mk ("@" ++ String.fromUTF8! name))

/--
  Parse a symbol reference — flat form only for now (`@name`).

  Nested form (`@outer::@inner::@deep`) is **deferred**: VEIR's lexer
  doesn't tokenize `::` as a punctuation symbol, so supporting the
  nested form requires a lexer extension. No current dialect needs
  nested refs at parse time — they're a Phase G.2/G.3 concern
  (Polymorphic and Struct's `LLZKSymbolTable` references). The
  `SymbolRefAttr` data structure exists in `Veir/IR/Attribute.lean`
  for forward compatibility; this parser entry point will be
  extended when a consumer arrives.

  Until then, this function is a thin wrapper around
  `parseOptionalFlatSymbolRefAttr` that returns the `Attribute`
  directly to match the dispatcher's expected type.
-/
def parseOptionalAnySymbolRef : AttrParserM (Option Attribute) := do
  let some flat ← parseOptionalFlatSymbolRefAttr | return none
  return some (.flatSymbolRefAttr flat)

/--
  Parse a location attribute, if present.
  A location attribute has the form `loc(body)`.
-/
partial def parseOptionalLocationAttr : AttrParserM (Option Attribute) := do
  if !(← parseOptionalKeyword "loc".toByteArray) then
    return none
  parsePunctuation "("
  let body ← parseUnregisteredAttrBody .rParen
  parsePunctuation ")"
  return some (LocationAttr.mk body)

/--
  Parse an LLVM pointer type `!llvm.ptr`, if present.
-/
partial def parseOptionalLLVMPointerType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "llvm.ptr".toByteArray then return none
  let _ ← consumeToken
  return some LLVM.PointerType.mk

/--
  Parse cuda-tile's pointer type, if present
  Its syntax is `!cuda_tile.ptr<type>`, where type will be a CudaTileNumberType
  At present, this is just integer types.
-/
partial def parseOptionalCudaTilePointerType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "cuda_tile.ptr".toByteArray then return none
  let _ ← consumeToken
  parsePunctuation "<"
  let some intTy ← parseOptionalIntegerType
    | throw "integer type expected"
  parsePunctuation ">"
  return some (CudaTile.PointerType.mk intTy)

/--
  Parse HEIR's modarith type, if present.
  Its syntax is `!mod_arith.int<modulus>` or `!mod_arith.int<modulus : iN>`.
-/
def parseOptionalModArithType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "mod_arith.int".toByteArray then
    return none
  let _ ← consumeToken
  parsePunctuation "<"
  let some modulus ← parseOptionalInteger false false
    | throw "modarith type modulus expected"
  let modulusType ←
    if ← parseOptionalPunctuation ":" then
      some <$> parseIntegerType "integer type expected after ':' in modarith type"
    else
      pure none
  parsePunctuation ">"
  return some (ModArithType.mk modulus modulusType)

/--
  Parse an LLZK string type, if present. Syntax: `!string.type` (no parameters).
-/
def parseOptionalStringType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "string.type".toByteArray then
    return none
  let _ ← consumeToken
  return some StringType.mk

/--
  Parse an LLZK felt type, if present.
  Its syntax is `!felt.type` (unspecified field) or `!felt.type<"name">`
  (with a named field).
-/
def parseOptionalFeltType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "felt.type".toByteArray then
    return none
  let _ ← consumeToken
  if ← parseOptionalPunctuation "<" then
    let some name ← parseOptionalStringLiteral
      | throw "felt type field name (string literal) expected"
    parsePunctuation ">"
    return some (FeltType.mk (some name.toByteArray))
  return some (FeltType.mk none)

/--
  Parse an LLZK felt-const attribute, if present.
  Syntax: `#felt<const N> : !felt.type` or `#felt<const N> : !felt.type<"name">`.
  First per-dialect structured attribute in VEIR — pattern for future
  `#bool<...>`, `#poly<...>`, etc. Note the dialect mnemonic is `felt`
  (not `felt.const`); `const` is a keyword in the body.

  Must come after `parseOptionalFeltType` in this file because it
  invokes that parser for the type-annotation suffix.
-/
def parseOptionalFeltConstAttr : AttrParserM (Option FeltConstAttr) := do
  let token ← peekToken
  let .hashIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let name := { token.slice with start := token.slice.start + 1 }.of input
  if name ≠ "felt".toByteArray then return none
  let _ ← consumeToken
  parsePunctuation "<"
  -- Body is `const <integer>`. The "const" is a Lean keyword; use the
  -- generic keyword parser to consume it.
  if !(← parseOptionalKeyword "const".toByteArray) then
    throw "#felt<...> attribute body must begin with `const`"
  -- allowNegative := true so the parse∘print round-trip closes on
  -- negative felt values (the printer always emits a leading `-`).
  let some val ← parseOptionalInteger false true
    | throw "#felt<const ...> expects an integer value"
  parsePunctuation ">"
  parsePunctuation ":"
  -- Field type: !felt.type or !felt.type<"name">.
  let some ftAttr ← parseOptionalFeltType
    | throw "#felt<const N> expects `: !felt.type[...]` annotation"
  -- Project the FeltType out of the TypeAttr wrapper.
  let Attribute.feltType ft := ftAttr.val
    | throw "#felt<const N>'s type annotation must be !felt.type"
  return some (FeltConstAttr.mk val ft)

/--
  Parse CIRCT's HW dialect's `ModulePort::Direction` type.
  Its syntax is `(input|output|inout)`.
-/
def parseOptionalHWModulePortDirection : AttrParserM (Option HW.ModulePort.Direction) := do
  if (← parseOptionalKeyword "input".toByteArray) then
    return some .input
  if (← parseOptionalKeyword "output".toByteArray) then
    return some .output
  if (← parseOptionalKeyword "inout".toByteArray) then
    return some .inout
  return none

/--
  Parse CIRCT's HW dialect's `ModulePort` type.
  Its syntax is `(input|output|inout) name : iN`.
-/
def parseOptionalHWModulePort : AttrParserM (Option HW.ModulePort) := do
  let .some dir ← parseOptionalHWModulePortDirection | return none
  let name := String.fromUTF8! (← parseIdentifier)
  parsePunctuation ":"
  let type ← parseIntegerType
  return some { dir, name, type }

def parseHWModulePort (errorMsg : String := "module port expected") : AttrParserM (HW.ModulePort) := do
  match ← parseOptionalHWModulePort with
  | some ty => return ty
  | none => throw errorMsg

/--
  Parse CIRCT's HW dialect's `ModuleType` type.
  Its syntax is `!hw.modty<ports>` where `ports` is a comma delimited list of `ModulePort`s.
-/
def parseOptionalHWModuleType : AttrParserM (Option HW.ModuleType) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "hw.modty".toByteArray then return none
  let _ ← consumeToken
  let ports ← parseDelimitedList .angle parseHWModulePort
  return some { ports }

mutual

/--
  Parse a function type, if present.
  A function type has the form `(input1, input2, ...) -> (output1, output2, ...)` or
  `(input1, input2, ...) -> output`.
-/
partial def parseOptionalFunctionType : AttrParserM (Option FunctionType) := do
  -- Parse the input types.
  let some inputs ← parseOptionalDelimitedList .paren parseType
    | return none
  -- Convert the parsed types to attributes, as FunctionType stores attributes instead
  -- of types.
  let inputs := inputs.map (fun x => x.val)
  parsePunctuation "->"
  -- Parse the output types as a list.
  match ← parseOptionalDelimitedList .paren parseType with
  | some outputs =>
    -- Convert the parsed types to attributes, as FunctionType stores attributes instead
    -- of types.
    let outputs := outputs.map (fun x => x.val)
    return some (FunctionType.mk inputs outputs)
  | none =>
    -- If there is no list of output, check for a single output type.
    let outputType ← parseType "function type output expected"
    return some (FunctionType.mk inputs #[outputType])

/--
  Parse a type, if present.
-/
partial def parseOptionalType : AttrParserM (Option TypeAttr) := do
  if let some integerType ← parseOptionalIntegerType then
    return some integerType
  if let some indexType ← parseOptionalIndexType then
    return some indexType
  if let some registerType ← parseOptionalRegisterType then
    return some registerType
  if let some modArithType ← parseOptionalModArithType then
    return some modArithType
  if let some feltType ← parseOptionalFeltType then
    return some feltType
  if let some stringType ← parseOptionalStringType then
    return some stringType
  if let some llvmPointerType := ← parseOptionalLLVMPointerType then
    return some llvmPointerType
  if let some cudaTilePointerType := ← parseOptionalCudaTilePointerType then
    return some cudaTilePointerType
  if let some hwModuleType ← parseOptionalHWModuleType then
    return some hwModuleType
  if let some dialectType ← parseOptionalDialectType then
    return some dialectType
  else if let some functionType := ← parseOptionalFunctionType then
    return some functionType
  else
    return none

/--
  Parse a type, throwing an error if it is not present.
-/
partial def parseType (errorMsg : String := "type expected") : AttrParserM TypeAttr := do
  match ← parseOptionalType with
  | some ty => return ty
  | none => throw errorMsg

/--
  Parse an entry in an attribute dictionary, which has the form `name = value`
  or the shorthand `name` (equivalent to `name = unit`).
-/
partial def parseAttributeDictionaryEntry : AttrParserM (ByteArray × Attribute) := do
  let name ← parseIdentifierOrStringLiteral
  if ← parseOptionalPunctuation "=" then
    let value ← parseAttribute
    return (name, value)
  else
    return (name, UnitAttr.mk)

/--
  Parse an attribute dictionary, if present.
-/
partial def parseOptionalAttributeDictionary :
    AttrParserM (Option (Array (ByteArray × Attribute))) := do
  parseOptionalDelimitedList .braces parseAttributeDictionaryEntry

/--
  Parse an attribute dictionary, throwing an error if it is not present.
-/
partial def parseAttributeDictionary (errorMsg : String := "attribute dictionary expected") :
    AttrParserM (Array (ByteArray × Attribute)) := do
  match ← parseOptionalAttributeDictionary with
  | some dict => return dict
  | none => throw errorMsg

/--
  Parse an array attribute, if present.
  Its syntax is a bracket-enclosed comma-separated list of attributes, e.g., `[1 : i32, "foo"]`.
-/
partial def parseOptionalArrayAttr : AttrParserM (Option ArrayAttr) := do
  let some elems ← parseOptionalDelimitedList .square parseAttribute
    | return none
  return some (ArrayAttr.mk elems)

/--
  Parse a dictionary attribute, if present.
  A dictionary attribute has the form `{key = value, key2 = value2, ...}`.
-/
partial def parseOptionalDictionaryAttr : AttrParserM (Option DictionaryAttr) := do
  let some entries ← parseOptionalDelimitedList .braces parseAttributeDictionaryEntry
    | return none
  return some (DictionaryAttr.fromArray entries)

/--
  Parse an attribute, if present.
-/
partial def parseOptionalAttribute : AttrParserM (Option Attribute) := do
  -- Per-dialect structured attributes come before the dialectAttr
  -- fallthrough (which captures unknown `#dialect.name<...>` as
  -- UnregisteredAttr). Slot any new structured attr here, before the
  -- fallthrough.
  if let some feltConstAttr ← parseOptionalFeltConstAttr then
    return some feltConstAttr
  if let some dialectAttr ← parseOptionalDialectAttr then
    return some dialectAttr
  else if let some locationAttr ← parseOptionalLocationAttr then
    return some locationAttr
  else if let some type ← parseOptionalType then
    return some type.val
  else if let some integerAttr ← parseOptionalIntegerAttr then
    return some integerAttr
  else if let some stringAttr ← parseOptionalStringAttr then
    return some stringAttr
  else if let some denseArrayAttr ← parseOptionalDenseArrayAttr then
    return some denseArrayAttr
  else if let some unitAttr ← parseOptionalUnitAttr then
    return some unitAttr
  else if let some arrayAttr ← parseOptionalArrayAttr then
    return some arrayAttr
  else if let some dictAttr ← parseOptionalDictionaryAttr then
    return some dictAttr
  else if let some symRef ← parseOptionalAnySymbolRef then
    -- Returns either a `.flatSymbolRefAttr` or a `.symbolRefAttr`
    -- (nested) — both already as `Attribute`. Replaces the prior
    -- flat-only call to `parseOptionalFlatSymbolRefAttr`.
    return some symRef
  else
    return none

/--
  Parse an attribute, throwing an error if it is not present.
-/
partial def parseAttribute (errorMsg : String := "attribute expected") :
    AttrParserM Attribute := do
  match ← parseOptionalAttribute with
  | some attr => return attr
  | none => throw errorMsg

end

end Veir.AttrParser
