module

public import Veir.Parser.Parser
public import Veir.IR.Attribute
public import Std.Data.HashMap

public section

open Veir.Parser.Lexer
open Veir.Parser
open Veir

namespace Veir.AttrParser

open Veir.Parser.ParserError

structure AttrParserState where
  allowUnregisteredDialect : Bool := false
  /-- Type aliases in scope, keyed by name without the `!`. -/
  typeAliases : Std.HashMap ByteArray TypeAttr := {}

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
  Parse the `x` separator in a shaped type.

  The lexer treats canonical fragments such as `x4xi32` as one identifier. If
  the current identifier starts with `x`, consume just that leading byte and
  re-lex the suffix so the following dimension or element type can be parsed
  normally.
-/
private def parseShapeSeparator : AttrParserM Unit := do
  let token ← peekToken
  let input := (← getThe ParserState).input
  if token.kind != .bareIdent || input.getD token.slice.start.byteOffset 0 != 'x'.toUInt8 then
    throwAtCurrentPos "expected keyword 'x'"
  resetToken (token.slice.start + 1)

/--
Parse one decimal vector dimension, if present.

Numbers in the form `0x...` are parsed as `0`, since `x` is the separator for the next vector
dimension, rather than a hexadecimal prefix.
-/
private def parseOptionalVectorDimension : AttrParserM (Option Nat) := do
  let token ← peekToken
  let .intLit := token.kind | return none
  let spelling := token.slice.of (← getThe ParserState).input
  let mut decimalLength := 0
  while h : decimalLength < spelling.size do
    if spelling[decimalLength].isDigit then
      decimalLength := decimalLength + 1
    else
      break
  let decimalSpelling := spelling.extract 0 decimalLength
  let some dimension := (String.fromUTF8? decimalSpelling).bind String.toNat?
    | throwAtCurrentPos "vector dimension must be a decimal integer"
  if dimension = 0 then
    throwAt token.slice.start "0 is not a supported dimension"
  resetToken (token.slice.start + decimalLength)
  return some dimension

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

/-- Parse the MLIR builtin `index` type. -/
def parseOptionalIndexType : AttrParserM (Option IndexType) := do
  if ← parseOptionalKeyword "index".toByteArray then
    return some IndexType.mk
  return none

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
  Resolve a just-consumed `!name` as a type alias. Returns `none` when the name denotes a dialect
  type instead, i.e. it contains a `.` or is directly followed by `<body>`.
-/
def resolveOptionalTypeAlias (startPos : Location) (name : ByteArray) :
    AttrParserM (Option TypeAttr) := do
  let next ← peekToken
  -- `startPos + 1 + name.size` is the end of the `!name` token, so this `<` has no space before it.
  let hasBody := next.kind == .less
    && next.slice.start.byteOffset == startPos.byteOffset + 1 + name.size
  if hasBody || name.toList.contains '.'.toUInt8 then
    return none
  let some type := (← getThe AttrParserState).typeAliases[name]?
    | throwAt startPos s!"undefined symbol alias id '{String.fromUTF8! name}'"
  return some type

/--
  Parse a builtin type via `parseOptional`, or a `!name` alias whose definition is an `α`. Used
  where MLIR requires a specific builtin type but still accepts an alias for it, e.g. the type of
  `1 : i32` or the element type of `array<i32: 1, 2>`.
-/
def parseBuiltinTypeOrAlias {α : Type} [IsTypeAttr α] (parseOptional : AttrParserM (Option α))
    (errorMsg : String) : AttrParserM α := do
  if let some type ← parseOptional then
    return type
  let startPos ← getPos
  let some name ← parseOptionalPrefixedKeyword .exclamationIdent | throwAtCurrentPos errorMsg
  let some type := (← resolveOptionalTypeAlias startPos name).bind (·.cast? α)
    | throwAt startPos errorMsg
  return type

/--
  Parse an integer type, throwing an error if it is not present.
  An integer type is represented as `i` followed by a positive integer indicating
  its width, e.g., `i32`, or by a type alias standing for one.
-/
def parseIntegerType (errorMsg : String := "integer type expected") : AttrParserM IntegerType :=
  parseBuiltinTypeOrAlias parseOptionalIntegerType errorMsg

/--
  Parse a float type, throwing an error if it is not present.
  A float type is represented as `f` followed by its width, e.g., `f64`, or by a type alias
  standing for one.
-/
def parseFloatType (errorMsg : String := "float type expected") : AttrParserM FloatType :=
  parseBuiltinTypeOrAlias parseOptionalFloatType errorMsg

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
  let some bytes ← parseOptionalStringLiteral
    | return none
  return some (StringAttr.mk bytes)

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
  let floatType ← parseFloatType "float type expected after ':' in float attribute"
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
  Parse a dialect type or a type alias, if present.
  A dialect type has the form `!dialect.name`, `!dialect.name<body>` or `!name<body>`; a bare
  `!name` is an alias.
-/
partial def parseOptionalDialectType : AttrParserM (Option TypeAttr) := do
  let startPos ← getPos
  let dialectName ← parseOptionalPrefixedKeyword .exclamationIdent
  let some dialectName := dialectName | return none
  if let some type ← resolveOptionalTypeAlias startPos dialectName then
    return some type
  if !(← getThe AttrParserState).allowUnregisteredDialect then
    throwAt startPos s!"type '!{String.fromUTF8! dialectName}' is not registered. \
      Consider using --allow-unregistered-dialect."
  if let true ← parseOptionalPunctuation "<" then
    let _ ← parseUnregisteredAttrBody
    let endPos := (← peekToken).slice.stop
    parsePunctuation ">"
    let value := (Slice.mk startPos endPos).of (← getThe ParserState).input
    return some (⟨UnregisteredAttr.mk (String.fromUTF8! value) true none, by grind⟩)
  else
    return some (⟨UnregisteredAttr.mk ("!" ++ String.fromUTF8! dialectName) true none, by grind⟩)

/--
  Attributes VeIR registers but does not interpret: everything between `<` and
  `>` is kept verbatim and printed back unchanged.
-/
private def verbatimBodyAttrs : List (ByteArray × (String → Attribute)) :=
  [ ("llvm.cconv".toByteArray, fun body => (CConvAttr.mk body : Attribute)),
    ("llvm.linkage".toByteArray, fun body => (LinkageAttr.mk body : Attribute)),
    ("llvm.framePointerKind".toByteArray, fun body => (FramePointerKindAttr.mk body : Attribute)),
    ("llvm.uwtableKind".toByteArray, fun body => (UwtableKindAttr.mk body : Attribute)),
    ("llvm.tailcallkind".toByteArray, fun body => (TailCallKindAttr.mk body : Attribute)),
    ("llvm.mlir.module_flag".toByteArray, fun body => (ModuleFlagAttr.mk body : Attribute)),
    ("llvm.constant_range".toByteArray, fun body => (ConstantRangeAttr.mk body : Attribute)),
    ("llvm.tbaa_tag".toByteArray, fun body => (TbaaTagAttr.mk body : Attribute)),
    ("llvm.target_features".toByteArray, fun body => (TargetFeaturesAttr.mk body : Attribute)),
    ("dlti.dl_spec".toByteArray, fun body => (DlSpecAttr.mk body : Attribute)) ]

/--
  Parse a dialect attribute, if present.
  A dialect attribute has the form `#dialect.name` or `#dialect.name<body>`. Attributes VeIR
  understands are decoded; any other one is kept as an `UnregisteredAttr` when unregistered
  dialects are allowed. Its optional trailing `: type` is parsed by `parseOptionalAttribute`,
  since the type parser is defined further down.
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

  if let some (_, toAttr) := verbatimBodyAttrs.find? (fun (name, _) => dialectName == name) then
    parsePunctuation "<"
    let body ← parseUnregisteredAttrBody
    parsePunctuation ">"
    return some (toAttr body)

  if !(← getThe AttrParserState).allowUnregisteredDialect then
    throwAt startPos s!"attribute '#{String.fromUTF8! dialectName}' is not registered. \
      Consider using --allow-unregistered-dialect."
  /- The body is optional: `#foo.bar` is as valid as `#foo.bar<baz>`. -/
  if !(← parseOptionalPunctuation "<") then
    return some (UnregisteredAttr.mk ("#" ++ String.fromUTF8! dialectName) false none)
  let _ ← parseUnregisteredAttrBody
  let endPos := (← peekToken).slice.stop
  parsePunctuation ">"
  let value := (Slice.mk startPos endPos).of (← getThe ParserState).input
  return some (UnregisteredAttr.mk (String.fromUTF8! value) false none)

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
  Parse a PDL range handle type `!pdl.range<...>`, if present. MLIR restricts
  the element to the four handle types, so a range never nests.
-/
partial def parseOptionalPDLRangeType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "pdl.range".toByteArray then return none
  let _ ← consumeToken
  parsePunctuation "<"
  let element ←
    if ← parseOptionalKeyword "attribute".toByteArray then
      pure PDL.RangeElement.attribute
    else if ← parseOptionalKeyword "operation".toByteArray then
      pure PDL.RangeElement.operation
    else if ← parseOptionalKeyword "type".toByteArray then
      pure PDL.RangeElement.type
    else if ← parseOptionalKeyword "value".toByteArray then
      pure PDL.RangeElement.value
    else
      throwAtCurrentPos "expected the element of a '!pdl.range' to be one of 'attribute', 'operation', 'type' or 'value'"
  parsePunctuation ">"
  return some (PDL.RangeType.mk element)

/--
  Parse a PDL attribute handle type `!pdl.attribute`, if present.
-/
partial def parseOptionalPDLAttributeType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "pdl.attribute".toByteArray then return none
  let _ ← consumeToken
  return some PDL.AttributeType.mk

/--
  Parse a PDL operation handle type `!pdl.operation`, if present.
-/
partial def parseOptionalPDLOperationType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "pdl.operation".toByteArray then return none
  let _ ← consumeToken
  return some PDL.OperationType.mk

/--
  Parse a PDL value handle type `!pdl.value`, if present.
-/
partial def parseOptionalPDLValueType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "pdl.value".toByteArray then return none
  let _ ← consumeToken
  return some PDL.ValueType.mk

/--
  Parse a PDL type handle type `!pdl.type`, if present.
-/
partial def parseOptionalPDLTypeType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "pdl.type".toByteArray then return none
  let _ ← consumeToken
  return some PDL.TypeType.mk

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
  let intTy ← parseIntegerType
  parsePunctuation ">"
  return some (CudaTile.PointerType.mk intTy)

/--
  Parse the IO address type `!io.address`, if present.
-/
partial def parseOptionalIoAddressType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "io.address".toByteArray then return none
  let _ ← consumeToken
  return some Io.AddressType.mk

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
  Parse an optional felt-type field-name annotation: `<"name">`.
-/
def parseOptionalFeltFieldName : AttrParserM (Option ByteArray) := do
  if ← parseOptionalPunctuation "<" then
    let some name ← parseOptionalStringLiteral
      | throwString "felt type field name (string literal) expected"
    parsePunctuation ">"
    return some name
  return none

/--
  Parse an LLZK felt type, if present.
  Its syntax is `!felt.type` or `!felt.type<"name">`.
-/
def parseOptionalFeltType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "felt.type".toByteArray then
    return none
  let _ ← consumeToken
  let fieldName ← parseOptionalFeltFieldName
  return some (FeltType.mk fieldName)

/--
  Parse an LLZK felt-const attribute, if present.
  Current named-field syntax is `#felt<const N : !felt.type<"name">>`;
  unnamed constants use `#felt<const N>`. Legacy named-field spellings and
  outer type annotations are accepted and canonicalized when printed.
-/
def parseOptionalFeltConstAttr : AttrParserM (Option FeltConstAttr) := do
  let token ← peekToken
  let .hashIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let name := { token.slice with start := token.slice.start + 1 }.of input
  if name ≠ "felt".toByteArray then return none
  let _ ← consumeToken
  parsePunctuation "<"
  if !(← parseOptionalKeyword "const".toByteArray) then
    throwString "#felt<...> attribute body must begin with `const`"
  let some val ← parseOptionalInteger false true
    | throwString "#felt<const ...> expects an integer value"

  -- Current LLZK syntax carries a named felt type inside the attribute body.
  if ← parseOptionalPunctuation ":" then
    if let some ftAttr ← parseOptionalFeltType then
      parsePunctuation ">"
      let Attribute.feltType ft := ftAttr.val
        | throwString "#felt<const N>'s type annotation must be !felt.type"
      return some (FeltConstAttr.mk val ft)

    -- Compatibility with the historical `: <"name">` spelling.
    let some innerFieldName ← parseOptionalFeltFieldName
      | throwString "#felt<const N : ...> expects a !felt.type"
    parsePunctuation ">"
    parsePunctuation ":"
    let some ftAttr ← parseOptionalFeltType
      | throwString "#felt<const N> expects a !felt.type annotation"
    let Attribute.feltType ft := ftAttr.val
      | throwString "#felt<const N>'s type annotation must be !felt.type"
    if ft.fieldName ≠ some innerFieldName then
      throwString "#felt<const N : <\"...\">> inner field name disagrees with outer !felt.type<\"...\"> annotation"
    return some (FeltConstAttr.mk val ft)

  -- Also accept the original legacy body `N <"name">`.
  let innerFieldName ← parseOptionalFeltFieldName
  parsePunctuation ">"
  if ← parseOptionalPunctuation ":" then
    let some ftAttr ← parseOptionalFeltType
      | throwString "#felt<const N> expects a !felt.type annotation"
    let Attribute.feltType ft := ftAttr.val
      | throwString "#felt<const N>'s type annotation must be !felt.type"
    if let some inner := innerFieldName then
      if ft.fieldName ≠ some inner then
        throwString "#felt<const N : <\"...\">> inner field name disagrees with outer !felt.type<\"...\"> annotation"
    return some (FeltConstAttr.mk val ft)
  return some (FeltConstAttr.mk val (FeltType.mk innerFieldName))

/-! ## ClangIR (`cir`) types and attributes -/

/--
  Parse ClangIR's integer type, if present.
  Its syntax is `!cir.int<s, N>` (signed) or `!cir.int<u, N>` (unsigned).
-/
def parseOptionalCirIntType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "cir.int".toByteArray then return none
  let _ ← consumeToken
  parsePunctuation "<"
  let isSigned ←
    if ← parseOptionalKeyword "s".toByteArray then pure true
    else if ← parseOptionalKeyword "u".toByteArray then pure false
    else throwAtCurrentPos "cir.int signedness expected ('s' or 'u')"
  parsePunctuation ","
  let some width ← parseOptionalInteger false false
    | throwAtCurrentPos "cir.int bitwidth expected"
  if width ≤ 0 then throwAtCurrentPos "cir.int bitwidth must be positive"
  parsePunctuation ">"
  return some (CirIntType.mk isSigned width.toNat)

/-- Parse ClangIR's boolean type `!cir.bool`, if present. -/
def parseOptionalCirBoolType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "cir.bool".toByteArray then return none
  let _ ← consumeToken
  return some CirBoolType.mk

/--
  Parse ClangIR's integer attribute, if present.
  Its syntax is `#cir.int<N> : !cir.int<s|u, W>`; the type annotation is mandatory.
-/
def parseOptionalCirIntAttr : AttrParserM (Option CirIntAttr) := do
  let token ← peekToken
  let .hashIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let name := { token.slice with start := token.slice.start + 1 }.of input
  if name ≠ "cir.int".toByteArray then return none
  let _ ← consumeToken
  parsePunctuation "<"
  let some value ← parseOptionalInteger false true
    | throwAtCurrentPos "#cir.int<...> expects an integer value"
  parsePunctuation ">"
  parsePunctuation ":"
  let some tyAttr ← parseOptionalCirIntType
    | throwAtCurrentPos "#cir.int<N> expects a !cir.int type annotation"
  let .cirIntType ty := tyAttr.val
    | throwAtCurrentPos "#cir.int<N> expects a !cir.int type annotation"
  return some (CirIntAttr.mk value ty)

/-- Parse ClangIR's boolean attribute `#cir.bool<true|false> : !cir.bool`, if present. -/
def parseOptionalCirBoolAttr : AttrParserM (Option CirBoolAttr) := do
  let token ← peekToken
  let .hashIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let name := { token.slice with start := token.slice.start + 1 }.of input
  if name ≠ "cir.bool".toByteArray then return none
  let _ ← consumeToken
  parsePunctuation "<"
  let value ←
    if ← parseOptionalKeyword "true".toByteArray then pure true
    else if ← parseOptionalKeyword "false".toByteArray then pure false
    else throwAtCurrentPos "#cir.bool<...> expects `true` or `false`"
  parsePunctuation ">"
  parsePunctuation ":"
  let some _ ← parseOptionalCirBoolType
    | throwAtCurrentPos "#cir.bool<b> expects a !cir.bool type annotation"
  return some (CirBoolAttr.mk value)

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
  Parse a builtin fixed-size vector type, if present.
  Its syntax is `vector<dimension-list x element-type>`, e.g. `vector<2x4xi32>`;
  the dimension list may be empty, as in `vector<i32>`.
-/
partial def parseOptionalVectorType : AttrParserM (Option TypeAttr) := do
  if !(← parseOptionalKeyword "vector".toByteArray) then
    return none
  parsePunctuation "<"
  let mut shape := #[]
  while let some dim ← parseOptionalVectorDimension do
    shape := shape.push dim
    parseShapeSeparator
  let elementType ← parseType "vector element type expected"
  parsePunctuation ">"
  return some (VectorType.mk shape elementType)

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
  return some ⟨UnregisteredAttr.mk ("!llvm.struct" ++ String.fromUTF8! body) true none, by grind⟩

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
  return some ⟨.llvmFunctionType ft, by simp⟩

/--
  Parse ClangIR's function type, if present.
  Its syntax is `!cir.func<(inputs) -> result>`, or `!cir.func<(inputs)>` for a function
  without results. A trailing `...` in the inputs marks a variadic function.
-/
partial def parseOptionalCirFuncType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "cir.func".toByteArray then return none
  let _ ← consumeToken
  parsePunctuation "<"
  let params ← parseDelimitedList .paren do
    if (← parseOptionalToken .ellipsis).isSome then
      return LLVMFuncParam.ellipsis
    return LLVMFuncParam.type (← parseType)
  if params.pop.any (· matches .ellipsis) then
    throwAtCurrentPos "'...' is only valid as the last parameter of a cir function type"
  let isVarArg := params.any (· matches .ellipsis)
  let inputs := params.filterMap fun
    | .type ty => some ty.val
    | .ellipsis => none
  let outputs ←
    if ← parseOptionalPunctuation "->" then
      match ← parseOptionalDelimitedList .paren parseType with
      | some outputs => pure (outputs.map (·.val))
      | none => pure #[(← parseType "cir.func result type expected").val]
    else
      pure #[]
  parsePunctuation ">"
  let ft := FunctionType.mk inputs outputs isVarArg
  return some ⟨.cirFuncType (CirFuncType.mk ft), by simp⟩

/--
  Parse a `match` optional handle type `!match.optional<...>`, if present.

  The wrapped type is parsed with the general type parser rather than a fixed
  enumeration: MLIR's `!match.optional` takes any type, and it is the verifier
  that narrows it to a PDL handle. That recursion is why this sits in the
  mutual block with `parseType`, unlike the PDL handle parsers above.
-/
partial def parseOptionalMatchOptionalType : AttrParserM (Option TypeAttr) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  let typeName := { token.slice with start := token.slice.start + 1 }.of input
  if typeName ≠ "match.optional".toByteArray then return none
  let _ ← consumeToken
  parsePunctuation "<"
  let inner ← parseType "expected the wrapped type of a '!match.optional'"
  parsePunctuation ">"
  return some (Match.OptionalType.mk inner)

/--
  Parse a type, if present.
-/
partial def parseOptionalType : AttrParserM (Option TypeAttr) := do
  if let some integerType ← parseOptionalIntegerType then
    return some integerType
  if let some indexType ← parseOptionalIndexType then
    return some indexType
  if let some floatType ← parseOptionalFloatType then
    return some floatType
  if let some vectorType ← parseOptionalVectorType then
    return some vectorType
  if let some byteType ← parseOptionalByteType then
    return some byteType
  if let some registerType ← parseOptionalRegisterType then
    return some registerType
  if let some modArithType ← parseOptionalModArithType then
    return some modArithType
  if let some feltType ← parseOptionalFeltType then
    return some feltType
  if let some cirIntType ← parseOptionalCirIntType then
    return some cirIntType
  if let some cirBoolType ← parseOptionalCirBoolType then
    return some cirBoolType
  if let some cirFuncType ← parseOptionalCirFuncType then
    return some cirFuncType
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
  if let some ioAddressType := ← parseOptionalIoAddressType then
    return some ioAddressType
  if let some hwModuleType ← parseOptionalHWModuleType then
    return some hwModuleType
  if let some pdlRangeType ← parseOptionalPDLRangeType then
    return some pdlRangeType
  if let some pdlAttributeType ← parseOptionalPDLAttributeType then
    return some pdlAttributeType
  if let some pdlOperationType ← parseOptionalPDLOperationType then
    return some pdlOperationType
  if let some pdlValueType ← parseOptionalPDLValueType then
    return some pdlValueType
  if let some pdlTypeType ← parseOptionalPDLTypeType then
    return some pdlTypeType
  if let some matchOptionalType ← parseOptionalMatchOptionalType then
    return some matchOptionalType
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
  Its syntax is `dense<value> : type`, e.g. `dense<0> : tensor<4xi8>`
  or `dense<[32, 64]> : vector<2xi64>`.
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
  -- tensor<4xi8> and vector<2xi64> are unregistered types: capture them as a balanced string
  -- using the same scheme as parseOptionalDialectAttr's fallback case.
  let typeStartPos ← getPos
  if !(← parseOptionalKeyword "tensor".toByteArray) then
    parseKeyword "vector".toByteArray
      "'tensor' or 'vector' type expected in dense elements attribute"
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
  Parse the optional trailing `: type` of an unregistered dialect attribute.
  MLIR lets any dialect attribute carry one, e.g. `#foo.bar<baz> : i32`. Nothing else can
  follow a dialect attribute with a `:`, so the token is unambiguous.
-/
partial def parseOptionalUnregisteredAttrType (attr : Attribute) : AttrParserM Attribute := do
  let .unregisteredAttr ⟨value, false, none⟩ := attr | return attr
  if ← parseOptionalPunctuation ":" then
    return (UnregisteredAttr.mk value false (some (← parseType).val) : Attribute)
  return attr

/--
  Parse an attribute, if present.
-/
partial def parseOptionalAttribute : AttrParserM (Option Attribute) := do
  if let some feltConstAttr ← parseOptionalFeltConstAttr then
    return some feltConstAttr
  if let some cirIntAttr ← parseOptionalCirIntAttr then
    return some cirIntAttr
  if let some cirBoolAttr ← parseOptionalCirBoolAttr then
    return some cirBoolAttr
  if let some dialectAttr ← parseOptionalDialectAttr then
    return some (← parseOptionalUnregisteredAttrType dialectAttr)
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
