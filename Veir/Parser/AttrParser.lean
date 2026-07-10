import Veir.Parser.Parser
import Veir.IR.Basic
import Veir.IR.Attribute

open Veir.Parser.Lexer
open Veir.Parser
open Veir

namespace Veir.AttrParser

open Veir.Parser.ParserError

structure AttrParserState where
  allowUnregisteredDialect : Bool := false

abbrev AttrParserM := StateT AttrParserState (EStateM ParserError ParserState)

/--
  Execute the action with the given initial state.
  Returns the result along with the final state, or an error message.
-/
def AttrParserM.run (self : AttrParserM α)
  (attrState : AttrParserState) (parserState: ParserState) : Except ParserError (α × AttrParserState × ParserState) :=
  match (StateT.run self attrState).run parserState with
  | .ok (a, attrState) parserState => .ok (a, attrState, parserState)
  | .error err _ => .error err

/--
  Execute the action with the given initial state.
  Returns the result or an error message.
-/
def AttrParserM.run' (self : AttrParserM α)
  (attrState : AttrParserState) (parserState: ParserState) : Except ParserError α :=
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
    if (← (getThe ParserState)).input.getD slice.start.byteOffset 0 == 'i'.toUInt8 then
      let bitwidthSlice : Slice := {start := slice.start + 1, stop := slice.stop}
      let identifier := bitwidthSlice.of (← (getThe ParserState)).input
      let some bitwidth := (String.fromUTF8? identifier).bind String.toNat? | return none
      let _ ← consumeToken
      return some (IntegerType.mk bitwidth)
    return none
  | _ => return none

/--
  Parse an optional float type.
  A float type is represented as `f` followed by a positive integer indicating its width, e.g., `f32`.
-/
def parseOptionalFloatType : AttrParserM (Option FloatType) := do
  match ← peekToken with
  | { kind := .bareIdent, slice := slice } =>
    if slice.size < 2 then
      return none
    if (← (getThe ParserState)).input.getD slice.start.byteOffset 0 == 'f'.toUInt8 then
      let bitwidthSlice : Slice := {start := slice.start + 1, stop := slice.stop}
      let identifier := bitwidthSlice.of (← (getThe ParserState)).input
      let some bitwidth := (String.fromUTF8? identifier).bind String.toNat? | return none
      let _ ← consumeToken
      return some (FloatType.mk bitwidth)
    return none
  | _ => return none

/--
  Parse an optional byte type.
  A byte type is represented as `!llvm.byte<bitwidth>` where bitwidth is a positive integer.
-/
def parseOptionalByteType : AttrParserM (Option LLVM.ByteType) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "llvm.byte".toByteArray then return none
  let _ ← consumeToken
  parsePunctuation "<"
  let bitwidth ← parseInteger false false
  parsePunctuation ">"
  return some (LLVM.ByteType.mk bitwidth.toNat)

/--
  Parse an optional register type, which is fundamentally a wrapper for `i64`.
  An unallocated register type is represented as `!riscv.reg`.
  Allocated register types range from `!riscv.reg<x0>` to `!riscv.reg<x31>`.
-/
def parseOptionalRegisterType : AttrParserM (Option RegisterType) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "riscv.reg".toByteArray then return none
  let _ ← consumeToken
  if ← parseOptionalPunctuation "<" then
    match ← peekToken with
    | { kind := .bareIdent, slice := slice } =>
      if slice.size < 2 then
        throwAtCurrentPos "expected RV64 register of the form xID"
      if (← (getThe ParserState)).input.getD slice.start.byteOffset 0 == 'x'.toUInt8 then
        let bitwidthSlice : Slice := {start := slice.start + 1, stop := slice.stop}
        let identifier := bitwidthSlice.of (← (getThe ParserState)).input
        let some reg := (String.fromUTF8? identifier).bind String.toNat? | return none
        if reg > 31 then throwAtCurrentPos "RV64 registers range from x0 to x31"
        let _ ← consumeToken
        parsePunctuation ">"
        return some (RegisterType.mk (some reg))
      throwAtCurrentPos "expected RV64 register of the form xID"
    | _ => throwAtCurrentPos "expected RV64 register of the form xID"
  else
    return some $ RegisterType.mk none

/--
  Parse an integer type, throwing an error if it is not present.
  An integer type is represented as `i` followed by a positive integer indicating
  its width, e.g., `i32`.
-/
def parseIntegerType (errorMsg : String := "integer type expected") : AttrParserM IntegerType := do
  match ← parseOptionalIntegerType with
  | some integerType => return integerType
  | none => throwAtCurrentPos errorMsg

/--
  Parse a register type, throwing an error if it is not present.
  An integer type is represented as `!riscv.reg`
-/
def parseRegisterType (errorMsg : String := "register type expected") : AttrParserM RegisterType := do
  match ← parseOptionalRegisterType with
  | some registerType => return registerType
  | none => throwAtCurrentPos errorMsg

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
Parse a float attribute, if present.
Only `1.0 : f64` is supported; the value is stored as Lean's `Float`.
-/
def parseOptionalFloatAttr : AttrParserM (Option FloatAttr) := do
  let some tok ← parseOptionalToken .floatLit | return none
  let str := String.fromUTF8! (tok.slice.of (← getThe ParserState).input)
  if str ≠ "1.0" then
    throwAtCurrentPos s!"unsupported floating-point literal '{str}', only '1.0 : f64' is supported"
  parsePunctuation ":"
  let some floatType ← parseOptionalFloatType
    | throwAtCurrentPos "float type expected after ':' in float attribute"
  if floatType.bitwidth ≠ 64 then
    throwAtCurrentPos "unsupported float type, only f64 is supported"
  return some (Veir.FloatAttr.mk 1.0 floatType)

/--
  Parse a string attribute.
  Its syntax is a string literal enclosed in double quotes, e.g., `"foo"`.
-/
def parseStringAttr (errorMsg : String := "string attribute expected") :
    AttrParserM StringAttr := do
  match ← parseOptionalStringAttr with
  | some stringAttr => return stringAttr
  | none => throwAtCurrentPos errorMsg

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

def parseFastMathFlag : AttrParserM FastMathFlagsAttr := do
  if (← parseOptionalKeyword "fast".toByteArray) then
    return { nnan := true, ninf := true, nsz := true }
  else if (← parseOptionalKeyword "nnan".toByteArray) then
    return { nnan := true, ninf := false, nsz := false }
  else if (← parseOptionalKeyword "ninf".toByteArray) then
    return { nnan := false, ninf := true, nsz := false }
  else if (← parseOptionalKeyword "nsz".toByteArray) then
    return { nnan := false, ninf := false, nsz := true }
  else if (← parseOptionalKeyword "none".toByteArray) then
    return { nnan := false, ninf := false, nsz := false }
  else
    return { nnan := false, ninf := false, nsz := false }

/--
  Parse an optional fastmath flags attribute, if present.
-/
def parseFloatFastMathFlagsAttr : AttrParserM (Option FastMathFlagsAttr) := do
  parsePunctuation "<"
  let values ← parseList parseFastMathFlag
  parsePunctuation ">"
  let mut floatFastMathFlags := FastMathFlagsAttr.mk false false false
  for flag in values do
    floatFastMathFlags := { floatFastMathFlags with
      nnan := floatFastMathFlags.nnan || flag.nnan,
      ninf := floatFastMathFlags.ninf || flag.ninf,
      nsz := floatFastMathFlags.nsz || flag.nsz }
  return some floatFastMathFlags

def parseIntegerOverflowFlag : AttrParserM (Bool × Bool) := do
  if ← parseOptionalKeyword "none".toByteArray then
    return (false, false)
  if ← parseOptionalKeyword "nsw".toByteArray then
    return (true, false)
  if ← parseOptionalKeyword "nuw".toByteArray then
    return (false, true)
  throwAtCurrentPos "expected integer overflow flag to be one of: none, nsw, nuw"

def parseIntegerOverflowFlags : AttrParserM (Bool × Bool) := do
  parsePunctuation "<"
  let values ← parseList parseIntegerOverflowFlag
  parsePunctuation ">"
  let mut nsw := false
  let mut nuw := false
  for (flagNsw, flagNuw) in values do
    nsw := nsw || flagNsw
    nuw := nuw || flagNuw
  return (nsw, nuw)

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
private def parseUnregisteredAttrBody (endToken : TokenKind := .greater)
    (startPos : Option Parser.Location := none) : AttrParserM String := do
  let startPos := startPos.getD (← peekToken).slice.start

  /- This stack corresponds to the brackets that are still open. -/
  let mut bracketStack : Array TokenKind := #[]
  let mut endPos : Parser.Location := { byteOffset := 0 }

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
        throwAt token.slice.start s!"unexpected closing bracket {closingName} in attribute body"
      /- If we have an open bracket, check that we are closing it
         with the right bracket kind. -/
      if bracketStack.back! != expected then
        throwAt token.slice.start s!"unexpected closing bracket {closingName} in attribute body"
      let _ ← consumeToken
      bracketStack := bracketStack.pop

    /- Checking for unexpected EOF -/
    else if token.kind == .eof then
      throwAt token.slice.start "unexpected end of file before closing of attribute body"

    /- Other tokens -/
    else
      let _ ← consumeToken
  let input := (← getThe ParserState).input
  let body := (Slice.mk startPos endPos).of input
  match String.fromUTF8? body with
  | some s => return s
  | none => throwAt startPos "failed converting attribute body to string"

/--
  Parse a dialect type, if present.
  A dialect attribute has the form `!dialect.name` or `!dialect.name<body>`.
-/
partial def parseOptionalDialectType : AttrParserM (Option TypeAttr) := do
  let startPos ← getPos
  let dialectName ← parseOptionalPrefixedKeyword .exclamationIdent
  let some dialectName := dialectName | return none
  if !(← getThe AttrParserState).allowUnregisteredDialect then
    throwAt startPos s!"type is not registered. Consider using --allow-unregistered-dialect."
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

  if dialectName = "llvm.fastmath".toByteArray then do
    return ← parseFloatFastMathFlagsAttr

  if dialectName = "arith.overflow".toByteArray then do
    let (nsw, nuw) ← parseIntegerOverflowFlags
    return some (ArithIntegerOverflowFlagsAttr.mk nsw nuw : Attribute)

  if dialectName = "llvm.cconv".toByteArray then do
    parsePunctuation "<"
    let body ← parseUnregisteredAttrBody
    parsePunctuation ">"
    return some (CConvAttr.mk body : Attribute)

  if dialectName = "llvm.linkage".toByteArray then do
    parsePunctuation "<"
    let body ← parseUnregisteredAttrBody
    parsePunctuation ">"
    return some (LinkageAttr.mk body : Attribute)

  if dialectName = "llvm.framePointerKind".toByteArray then do
    parsePunctuation "<"
    let body ← parseUnregisteredAttrBody
    parsePunctuation ">"
    return some (FramePointerKindAttr.mk body : Attribute)

  if dialectName = "llvm.uwtableKind".toByteArray then do
    parsePunctuation "<"
    let body ← parseUnregisteredAttrBody
    parsePunctuation ">"
    return some (UwtableKindAttr.mk body : Attribute)

  if dialectName = "llvm.tailcallkind".toByteArray then do
    parsePunctuation "<"
    let body ← parseUnregisteredAttrBody
    parsePunctuation ">"
    return some (TailCallKindAttr.mk body : Attribute)

  if dialectName = "llvm.mlir.module_flag".toByteArray then do
    parsePunctuation "<"
    let body ← parseUnregisteredAttrBody
    parsePunctuation ">"
    return some (ModuleFlagAttr.mk body : Attribute)

  if dialectName = "llvm.target_features".toByteArray then do
    parsePunctuation "<"
    let body ← parseUnregisteredAttrBody
    parsePunctuation ">"
    return some (TargetFeaturesAttr.mk body : Attribute)

  if dialectName = "dlti.dl_spec".toByteArray then do
    parsePunctuation "<"
    let body ← parseUnregisteredAttrBody
    parsePunctuation ">"
    return some (DlSpecAttr.mk body : Attribute)

  if !(← getThe AttrParserState).allowUnregisteredDialect then
    throwAt startPos s!"attribute is not registered. Consider using --allow-unregistered-dialect."
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
  Parse an LLVM void type `!llvm.void`, if present.
-/
partial def parseOptionalLLVMVoidType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "llvm.void".toByteArray then return none
  let _ ← consumeToken
  return some LLVM.VoidType.mk

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
    | throwAtCurrentPos "integer type expected"
  parsePunctuation ">"
  return some (CudaTile.PointerType.mk intTy)

/--
  Parse HEIR's modarith type, if present.
  Its syntax is `!mod_arith.int<{IntegerAttr}>`, e.g., `!mod_arith.int<17 : i32>`.
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
  let some modulus ← parseOptionalIntegerAttr
    | throwAtCurrentPos "modarith type modulus expected"
  parsePunctuation ">"
  return some (ModArithType.mk modulus)

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
  | none => throwAtCurrentPos errorMsg

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

/-- A parsed entry in an LLVM function type's parameter list. -/
inductive LLVMFuncParam
  | type (ty : TypeAttr)
  | ellipsis

mutual

/--
  Parse an LLVM array type, if present.
  Its syntax is `!llvm.array<size x type>`,
  or (exclusively) the shorter form `array<size x type>` if the corresponding argument is set.
-/
partial def parseOptionalLLVMArrayType (short := false) : AttrParserM (Option TypeAttr) := do
  if short then
    let .true ← parseOptionalKeyword "array".toByteArray | return none
  else
    let token ← peekToken
    let .exclamationIdent := token.kind | return none
    let input := (← getThe ParserState).input
    let typeName := { token.slice with start := token.slice.start + 1 }.of input
    if typeName ≠ "llvm.array".toByteArray then return none
    let _ ← consumeToken
  parsePunctuation "<"
  let size ← parseInteger false false
  parseKeyword "x".toByteArray
  let ty ← parseLLVMType
  parsePunctuation ">"
  return some (LLVM.ArrayType.mk size.toNat ty)

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
    return some (FunctionType.mk inputs outputs (isVarArg := false))
  | none =>
    -- If there is no list of output, check for a single output type.
    let outputType ← parseType "function type output expected"
    return some (FunctionType.mk inputs #[outputType] (isVarArg := false))

/--
  Parse an LLVM struct type, if present.
  Its syntax is `!llvm.struct<...>`, or (exclusively) the shorter form
  `struct<...>` if the corresponding argument is set.

  LIMITATION: the struct is parsed *opaquely* as an `UnregisteredAttr` holding the
  body as text. There is no structured representation: the struct name (for
  identified structs like `struct<"name", (...)>`), the element list, and the
  packed flag all live only as a substring of the stored text, so VeIR cannot
  compare struct types semantically, resolve a recursive reference
  (`struct<"node">`) against its definition, or inspect fields.

  A proper fix would introduce a dedicated `LLVM.StructType` (mirroring the
  existing `LLVM.ArrayType`): an inductive constructor carrying the literal vs.
  identified distinction, the packed flag, and the element list, with the
  identity/recursion handling that identified structs require. That is a larger
  change and unnecessary until a pass needs to reason about struct layout or
  identity; until then the opaque representation parses and roundtrips correctly,
  which is all that is currently required.
-/
partial def parseOptionalLLVMStructType (short := false) : AttrParserM (Option TypeAttr) := do
  if short then
    let .true ← parseOptionalKeyword "struct".toByteArray | return none
  else
    let token ← peekToken
    let .exclamationIdent := token.kind | return none
    let input := (← getThe ParserState).input
    let typeName := { token.slice with start := token.slice.start + 1 }.of input
    if typeName ≠ "llvm.struct".toByteArray then return none
    let _ ← consumeToken
  -- Capture the `struct<...>` body opaquely and normalize to the full
  -- `!llvm.struct<...>` spelling, so both forms produce identical output.
  let startPos ← getPos
  parsePunctuation "<"
  let _ ← parseUnregisteredAttrBody
  let endPos := (← peekToken).slice.stop
  parsePunctuation ">"
  let body := (Slice.mk startPos endPos).of (← getThe ParserState).input
  return some ⟨UnregisteredAttr.mk ("!llvm.struct" ++ String.fromUTF8! body) true, by grind⟩

/--
  Parse a type within an LLVM-dialect type body, accepting the LLVM "pretty-print"
  sugar keywords `void`, `ptr`, and the bare nested forms `array<...>` and
  `struct<...>` in addition to the regular MLIR type forms.

  The bare nested form exists because the LLVM dialect has a custom directive
  `PrettyLLVMType`, which allows types from the LLVM dialect to be written
  without the `!llvm.` prefix when they're already nested inside a LLVM-dialect
  type. For example, `!llvm.array<2 x struct<...>>` is the same as
  `!llvm.array<2 x !llvm.struct<...>>`.

  In practice, this syntax (`PrettyLLVMType`) is used almost everywhere in the
  LLVM dialect wherever a nested type is allowed. So we can always turn on the
  shorthand whenever we know that we're parsing a LLVM-dialect type.

  Upstream MLIR handles this convenience syntax by rolling their own parser and
  printer. VeIR needs to do the same. We only handle the parser part for now
  since always printing the full `!llvm.` prefix is still valid syntax.

  Source: see `dispatchParse` and `LLVM::parsePrettyLLVMType` in
  `mlir/lib/Dialect/LLVMIR/IR/LLVMTypeSyntax.cpp`.
-/
partial def parseLLVMType (errorMsg : String := "type expected") : AttrParserM TypeAttr := do
  if ← parseOptionalKeyword "void".toByteArray then
    return LLVM.VoidType.mk
  if ← parseOptionalKeyword "ptr".toByteArray then
    return (LLVM.PointerType.mk : TypeAttr)
  if let some type ← parseOptionalLLVMArrayType true then
    return type
  if let some type ← parseOptionalLLVMStructType true then
    return type
  parseType errorMsg

/--
  Parse an LLVM function type `!llvm.func<resultType (paramTypes,...)>`, if present.
  A trailing `...` parameter marks the function as variadic; the ellipsis is invalid
  in any position other than the last.
-/
partial def parseOptionalLLVMFunctionType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "llvm.func".toByteArray then return none
  let _ ← consumeToken
  parsePunctuation "<"
  let result ← parseLLVMType "llvm.func result type expected"
  let params ← parseDelimitedList .paren do
    if (← parseOptionalToken .ellipsis).isSome then
      return LLVMFuncParam.ellipsis
    return LLVMFuncParam.type (← parseLLVMType)
  parsePunctuation ">"
  if params.pop.any (· matches .ellipsis) then
    throwAtCurrentPos "'...' is only valid as the last parameter of an LLVM function type"
  let isVarArg := params.any (· matches .ellipsis)
  let paramTypes := params.filterMap fun
    | .type ty => some ty.val
    | .ellipsis => none
  let ft := FunctionType.mk paramTypes #[result.val] isVarArg
  return some ⟨.llvmFunctionType ft, by rfl⟩

/--
  Parse a type, if present.
-/
partial def parseOptionalType : AttrParserM (Option TypeAttr) := do
  if let some integerType ← parseOptionalIntegerType then
    return some integerType
  if let some floatType ← parseOptionalFloatType then
    return some floatType
  if let some byteType ← parseOptionalByteType then
    return some byteType
  if let some registerType ← parseOptionalRegisterType then
    return some registerType
  if let some modArithType ← parseOptionalModArithType then
    return some modArithType
  if let some llvmVoidType := ← parseOptionalLLVMVoidType then
    return some llvmVoidType
  if let some llvmPointerType := ← parseOptionalLLVMPointerType then
    return some llvmPointerType
  if let some llvmArrayType := ← parseOptionalLLVMArrayType then
    return some llvmArrayType
  if let some llvmStructType ← parseOptionalLLVMStructType then
    return some llvmStructType
  if let some llvmFunctionType ← parseOptionalLLVMFunctionType then
    return some llvmFunctionType
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
  | none => throwAtCurrentPos errorMsg

/--
  Parse a dense elements attribute, if present.
  Its syntax is `dense<value> : type`, e.g. `dense<0> : tensor<4xi8>`.
  Both the value body and the type are stored as raw strings pending full
  tensor/vector type support.
-/
partial def parseOptionalDenseElementsAttr : AttrParserM (Option DenseElementsAttr) := do
  if !(← parseOptionalKeyword "dense".toByteArray) then
    return none
  parsePunctuation "<"
  let value ← parseUnregisteredAttrBody
  parsePunctuation ">"
  parsePunctuation ":"
  -- tensor<4xi8> is an unregistered type: capture it as a balanced string
  -- using the same scheme as parseOptionalDialectAttr's fallback case.
  let typeStartPos ← getPos
  parseKeyword "tensor".toByteArray
  parsePunctuation "<"
  let _ ← parseUnregisteredAttrBody
  let typeEndPos := (← peekToken).slice.stop
  parsePunctuation ">"
  let typeStr := (Slice.mk typeStartPos typeEndPos).of (← getThe ParserState).input
  return some (DenseElementsAttr.mk value (String.fromUTF8! typeStr))

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
  | none => throwAtCurrentPos errorMsg

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
  if let some dialectAttr ← parseOptionalDialectAttr then
    return some dialectAttr
  else if let some locationAttr ← parseOptionalLocationAttr then
    return some locationAttr
  else if let some type ← parseOptionalType then
    return some type.val
  else if let some integerAttr ← parseOptionalIntegerAttr then
    return some integerAttr
  else if let some floatAttr ← parseOptionalFloatAttr then
    return some floatAttr
  else if let some stringAttr ← parseOptionalStringAttr then
    return some stringAttr
  else if let some denseArrayAttr ← parseOptionalDenseArrayAttr then
    return some denseArrayAttr
  else if let some denseElementsAttr ← parseOptionalDenseElementsAttr then
    return some denseElementsAttr
  else if let some unitAttr ← parseOptionalUnitAttr then
    return some unitAttr
  else if let some arrayAttr ← parseOptionalArrayAttr then
    return some arrayAttr
  else if let some dictAttr ← parseOptionalDictionaryAttr then
    return some dictAttr
  else if let some symRefAttr ← parseOptionalFlatSymbolRefAttr then
    return some symRefAttr
  else
    return none

/--
  Parse an attribute, throwing an error if it is not present.
-/
partial def parseAttribute (errorMsg : String := "attribute expected") :
    AttrParserM Attribute := do
  match ← parseOptionalAttribute with
  | some attr => return attr
  | none => throwAtCurrentPos errorMsg

end

end Veir.AttrParser
