module

public import Veir.Parser.Parser
public import Veir.IR.Attribute
public import Std.Data.HashMap

public section

open Veir.Parser.Lexer
open Veir.Parser
open Veir
open Lean

namespace Veir.AttrParser

open Veir.Parser.ParserError

structure AttrParserState where
  allowUnregisteredDialect : Bool := false
  /-- Type aliases in scope, keyed by name without the `!`. -/
  typeAliases : Std.HashMap ByteArray TypeAttr := {}
  /--
    Keep integer literals exactly as written instead of range-checking them and
    normalizing them to their width the way MLIR does. Set only for `mod_arith`
    moduli and properties.
  -/
  rawIntegerLiterals : Bool := false

abbrev AttrParserM := StateT AttrParserState (EStateM ParserError ParserState)

/--
  Run `x` with `rawIntegerLiterals` set, restoring the previous setting after.
-/
def withRawIntegerLiterals (x : AttrParserM α) : AttrParserM α := do
  let saved := (← get).rawIntegerLiterals
  modify ({ · with rawIntegerLiterals := true })
  let result ← x
  modify ({ · with rawIntegerLiterals := saved })
  return result

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

/-- The type name `!name` of the current token, if it is a `!`-prefixed identifier. -/
private def peekTypeName : AttrParserM (Option ByteArray) := do
  let token ← peekToken
  let .exclamationIdent := token.kind | return none
  let input := (← getThe ParserState).input
  return some ({ token.slice with start := token.slice.start + 1 }.of input)

/--
  Parse an optional integer type.
  An integer type is represented as `i` followed by a positive integer indicating its width, e.g., `i32`.
-/
def parseOptionalIntegerType : AttrParserM (Option IntegerType) := do
  match ← peekToken with
  | { kind := .bareIdent, slice := slice } =>
    let identifier := slice.of (← getThe ParserState).input
    if identifier.size < 2 || identifier[0]! != 'i'.toUInt8 then return none
    let some bitwidth := (String.fromUTF8? (identifier.extract 1 identifier.size)).bind String.toNat?
      | return none
    let _ ← consumeToken
    return some (IntegerType.mk bitwidth)
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
    let giveOut (bitwidth : Nat) : AttrParserM (Option FloatType) := do
      let _ ← consumeToken
      return some (FloatType.mk bitwidth)
    let input := slice.of (← (getThe ParserState)).input
    match String.fromUTF8? input with
    | some "f16" => giveOut 16
    | some "f32" => giveOut 32
    | some "f64" => giveOut 64
    | some "bf16" => giveOut 16
    | some "f80" => giveOut 80
    | some "f128" => giveOut 128
    | some "f8E5M2" => giveOut 8
    | some "f8E4M3FN" => giveOut 8
    | some "f8E4M3FNUZ" => giveOut 8
    | _ => return none
  | _ => return none

/--
  Parse an optional register type `!riscv.reg` or `!riscv.reg<xN>`.
  The allocated register is not retained by this branch's `RegisterType`.
-/
def parseOptionalRegisterType : AttrParserM (Option RegisterType) := do
  let some typeName ← peekTypeName | return none
  if typeName ≠ "riscv.reg".toByteArray && typeName ≠ "reg".toByteArray then return none
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
        return some RegisterType.mk
      throwAtCurrentPos "expected RV64 register of the form xID"
    | _ => throwAtCurrentPos "expected RV64 register of the form xID"
  else
    return some RegisterType.mk

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
  Parse a builtin type via `parseOptional`, or a `!name` alias whose definition is accepted by
  `cast`. Used where MLIR requires a specific builtin type but still accepts an alias for it, e.g.
  the type of `1 : i32` or the element type of `array<i32: 1, 2>`.
-/
def parseBuiltinTypeOrAlias {α : Type} (parseOptional : AttrParserM (Option α))
    (cast : TypeAttr → Option α) (errorMsg : String) : AttrParserM α := do
  if let some type ← parseOptional then
    return type
  let startPos ← getPos
  let some name ← parseOptionalPrefixedKeyword .exclamationIdent | throwAtCurrentPos errorMsg
  let some type := (← resolveOptionalTypeAlias startPos name).bind cast
    | throwAt startPos errorMsg
  return type

/-- View a type attribute as an integer type. -/
def TypeAttr.asIntegerType? (type : TypeAttr) : Option IntegerType :=
  match type.val with
  | .integerType t => some t
  | _ => none

/-- View a type attribute as a float type. -/
def TypeAttr.asFloatType? (type : TypeAttr) : Option FloatType :=
  match type.val with
  | .floatType t => some t
  | _ => none

/--
  Parse an integer type, throwing an error if it is not present.
  An integer type is represented as `i` followed by a positive integer indicating
  its width, e.g., `i32`, or by a type alias standing for one.
-/
def parseIntegerType (errorMsg : String := "integer type expected") : AttrParserM IntegerType :=
  parseBuiltinTypeOrAlias parseOptionalIntegerType TypeAttr.asIntegerType? errorMsg

/--
  Parse a float type, throwing an error if it is not present.
-/
def parseFloatType (errorMsg : String := "float type expected") : AttrParserM FloatType :=
  parseBuiltinTypeOrAlias parseOptionalFloatType TypeAttr.asFloatType? errorMsg

/--
  Parse a string attribute, if present.
  Its syntax is a string literal enclosed in double quotes, e.g., `"foo"`.
-/
def parseOptionalStringAttr : AttrParserM (Option StringAttr) := do
  let some bytes ← parseOptionalStringLiteral
    | return none
  return some (StringAttr.mk bytes)

/-- Convert a parsed base-10 float into a `Float`. -/
private def floatOfParsed (f : ParsedFloat) : Float :=
  let magnitude := Float.ofScientific f.significand (f.exponent < 0) f.exponent.natAbs
  if f.negative then -magnitude else magnitude

/--
  Parse an integer or floating-point attribute, if present.
  The attribute has the form `false`, `true` or `value : type`.
  For an integer type, `value` must be a (possibly negated) integer literal in decimal or
  `0x`-prefixed hexadecimal form.
  For a floating-point type, `value` may be a (possibly negated) decimal floating-point
  literal, or a `0x`-prefixed hexadecimal integer literal interpreted as the raw IEEE-754
  bit pattern of the type.

  MLIR accepts the following floating point numbers: [-+]?[0-9]+[.][0-9]*([eE][-+]?[0-9]+)?
-/
def parseOptionalNumericAttr : AttrParserM (Option Attribute) := do
  if (← parseOptionalKeyword "false".toByteArray) then
    return some (IntegerAttr.mk 0 (IntegerType.mk 1) : Attribute)
  if (← parseOptionalKeyword "true".toByteArray) then
    return some (IntegerAttr.mk 1 (IntegerType.mk 1) : Attribute)

  -- Parse the optional leading '-'.
  let isNegative := Option.isSome (← parseOptionalToken .minus)

  -- Parse the value literal (integer or floating-point). At most one of the two is present.
  let valueStartPos ← getPos
  let valueInput := (← getThe ParserState).input
  let intTok : Option Token ← parseOptionalToken .intLit
  let floatTok : Option Token ← parseOptionalToken .floatLit
  let valueTokOpt : Option Token := match intTok, floatTok with
    | some t, _ => some t
    | none, some t => some t
    | none, none => none
  let some valueToken := valueTokOpt
    | if isNegative then
        throwAtCurrentPos "expected number after '-'"
      else
        return none
  let value := valueToken.slice.of valueInput
  let isFloatLit : Bool := valueToken.kind == .floatLit

  parsePunctuation ":"
  let startPos ← getPos

  -- Build the integer attribute from the parsed literal.
  let integerAttr (integerType : IntegerType) : AttrParserM Attribute := do
    if isFloatLit then
      throwAtCurrentPos "integer literal expected in integer attribute"
    let some n := numericValueToNat? value
      | throwAt startPos s!"invalid integer literal '{String.fromUTF8! value}'"
    let literal := if isNegative then Int.negOfNat n else Int.ofNat n
    if (← get).rawIntegerLiterals then
      return IntegerAttr.mk literal integerType
    let bits := BitVec.ofInt integerType.bitwidth literal
    if (isNegative && n == 0) ∨ (literal ≠ bits.toInt ∧ literal ≠ bits.toNat) then
      throwAt valueStartPos "integer constant out of range for attribute"
    return IntegerAttr.mk literal integerType

  -- Compute the floating-point value from the parsed literal.
  let floatValue (floatType : FloatType) : AttrParserM Float := do
    if isFloatLit then
      let str := if isNegative then "-" ++ String.fromUTF8! value else String.fromUTF8! value
      match parseDecimalFloat str with
      | some f => return floatOfParsed f
      | none   => throwAtCurrentPos s!"invalid floating-point literal '{str}'"
    else
      if isNegative then
        throwAt valueStartPos "unexpected '-' before float bit pattern"
      else if isHexValue value then
        let some n := numericValueToNat? value
          | throwAt valueStartPos s!"invalid hex bit pattern '{String.fromUTF8! value}'"
        if n ≥ 2 ^ floatType.bitwidth then
          throwAt valueStartPos "hexadecimal float constant out of range for type"
        return Float.ofBits n.toUInt64
      else
        throwAt valueStartPos "expected a decimal float or 0x-prefixed hex bit pattern in float attribute"

  -- Determine the type after ':'.
  if let some integerType ← parseOptionalIntegerType then
    return some (← integerAttr integerType)
  else if let some floatType ← parseOptionalFloatType then
    return some (FloatAttr.mk (← floatValue floatType) floatType : Attribute)
  else if let some name ← parseOptionalPrefixedKeyword .exclamationIdent then
    let some typeAttr := (← resolveOptionalTypeAlias startPos name)
      | throwAt startPos "integer or float type expected after ':' in numeric attribute"
    if let some integerType := TypeAttr.asIntegerType? typeAttr then
      return some (← integerAttr integerType)
    else if let some floatType := TypeAttr.asFloatType? typeAttr then
      return some (FloatAttr.mk (← floatValue floatType) floatType : Attribute)
    else
      throwAt startPos "integer or float type expected after ':' in numeric attribute"
  else
    throwAt startPos "integer or float type expected after ':' in numeric attribute"

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

/-- An unregistered type attribute holding its source text. -/
def unregisteredType (text : String) : TypeAttr :=
  ⟨.unregisteredAttr (UnregisteredAttr.mk text true), by simp⟩

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
    return some (unregisteredType (String.fromUTF8! value))
  else
    return some (unregisteredType ("!" ++ String.fromUTF8! dialectName))

/--
  Consume the type name `!name`, or (exclusively) `name` without the dialect prefix when
  `short`. Consumes nothing if the name is not there.
-/
private def parseOptionalTypeName (name : String) (short : Bool) : AttrParserM Bool := do
  if short then
    let mnemonic := match name.splitOn "." with
      | _dialect :: mnemonic@(_ :: _) => ".".intercalate mnemonic
      | _ => name
    return ← parseOptionalKeyword mnemonic.toByteArray
  let some typeName ← peekTypeName | return false
  if typeName ≠ name.toByteArray then return false
  let _ ← consumeToken
  return true

/--
  The LLVM types that take no parameters. `void` and `ptr` have their own parsers.
-/
private def llvmParameterlessTypes : List String :=
  ["llvm.x86_amx", "llvm.ppc_fp128", "llvm.label", "llvm.metadata", "llvm.token"]

/--
  Parse the parameterless type `!name`, or (exclusively) `name` without the dialect prefix
  when `short`.
-/
def parseOptionalUnregisteredSingletonType (name : String) (short := false) :
    AttrParserM (Option TypeAttr) := do
  if !(← parseOptionalTypeName name short) then return none
  return some (unregisteredType ("!" ++ name))

/--
  Parse the type `!dialect.name<...>`, or (exclusively) `name<...>` without the dialect prefix when
  `short`. The body is kept as written, so both spellings print as `!dialect.name<...>`.
-/
def parseOptionalUnregisteredType (name : String) (short := false) :
    AttrParserM (Option TypeAttr) := do
  if !(← parseOptionalTypeName name short) then return none
  let startPos ← getPos
  parsePunctuation "<"
  let _ ← parseUnregisteredAttrBody
  let endPos := (← peekToken).slice.stop
  parsePunctuation ">"
  let body := (Slice.mk startPos endPos).of (← getThe ParserState).input
  return some (unregisteredType ("!" ++ name ++ String.fromUTF8! body))

/--
  Attributes VeIR registers but does not interpret: everything between `<` and
  `>` is kept verbatim and printed back unchanged.
-/
private def verbatimBodyAttrs : List ByteArray :=
  [ "llvm.cconv".toByteArray, "llvm.linkage".toByteArray, "llvm.framePointerKind".toByteArray,
    "llvm.uwtableKind".toByteArray, "llvm.tailcallkind".toByteArray,
    "llvm.mlir.module_flag".toByteArray, "llvm.constant_range".toByteArray,
    "llvm.tbaa_tag".toByteArray, "llvm.memory_effects".toByteArray,
    "llvm.loop_annotation".toByteArray, "llvm.target_features".toByteArray,
    "dlti.dl_spec".toByteArray ]

/--
  Parse a dialect attribute, if present.
  A dialect attribute has the form `#dialect.name` or `#dialect.name<body>`. Attributes VeIR
  understands are decoded; any other one is kept as an `UnregisteredAttr` when unregistered
  dialects are allowed.
-/
partial def parseOptionalDialectAttr : AttrParserM (Option Attribute) := do
  let startPos ← getPos
  let dialectName ← parseOptionalPrefixedKeyword .hashIdent
  let some dialectName := dialectName | return none

  if dialectName = "llvm.fastmath".toByteArray then do
    return (← parseFloatFastMathFlagsAttr).map (.fastMathFlagsAttr ·)

  if dialectName = "arith.overflow".toByteArray then do
    /- This branch encodes overflow flags as the `overflowFlags` integer property. -/
    let (nsw, nuw) ← parseIntegerOverflowFlags
    let flags : Nat := (if nsw then 1 else 0) + (if nuw then 2 else 0)
    return some (IntegerAttr.mk flags (IntegerType.mk 32) : Attribute)

  if verbatimBodyAttrs.contains dialectName then
    parsePunctuation "<"
    let body ← parseUnregisteredAttrBody
    parsePunctuation ">"
    return some (UnregisteredAttr.mk ("#" ++ String.fromUTF8! dialectName ++ "<" ++ body ++ ">") false)

  if !(← getThe AttrParserState).allowUnregisteredDialect then
    throwAt startPos s!"attribute '#{String.fromUTF8! dialectName}' is not registered. \
      Consider using --allow-unregistered-dialect."
  /- The body is optional: `#foo.bar` is as valid as `#foo.bar<baz>`. -/
  if !(← parseOptionalPunctuation "<") then
    return some (UnregisteredAttr.mk ("#" ++ String.fromUTF8! dialectName) false)
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
  Parse a symbol reference attribute, if present: a flat reference `@root`,
  optionally followed by nested references as in `@comdat::@selector`. Nested references
  are kept textually in a flat symbol reference.
-/
def parseOptionalSymbolRefAttr : AttrParserM (Option Attribute) := do
  let some root ← parseOptionalFlatSymbolRefAttr | return none
  let mut text := root.value
  repeat
    if (← peekToken).kind != .colon then break
    parsePunctuation ":"
    parsePunctuation ":" "Expected '::' before a nested symbol reference"
    let pos := (← peekToken).slice.start
    let some name ← parseOptionalFlatSymbolRefAttr
      | throwAt pos "Expected a symbol reference after '::'"
    text := text ++ "::" ++ name.value
  return some (.flatSymbolRefAttr (FlatSymbolRefAttr.mk text))

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
  if !(← parseOptionalTypeName "llvm.void" false) then return none
  return some LLVM.VoidType.mk

/--
  Parse an LLVM pointer type `!llvm.ptr`, if present.
-/
partial def parseOptionalLLVMPointerType : AttrParserM (Option TypeAttr) := do
  if !(← parseOptionalTypeName "llvm.ptr" false) then return none
  return some LLVM.PointerType.mk

/--
  Parse cuda-tile's pointer type, if present
  Its syntax is `!cuda_tile.ptr<type>`, where type will be a CudaTileNumberType
  At present, this is just integer types.
-/
partial def parseOptionalCudaTilePointerType : AttrParserM (Option TypeAttr) := do
  if !(← parseOptionalTypeName "cuda_tile.ptr" false) then return none
  parsePunctuation "<"
  let intTy ← parseIntegerType
  parsePunctuation ">"
  return some (CudaTile.PointerType.mk intTy)

/--
  Parse HEIR's modarith type, if present.
  Its syntax is `!mod_arith.int<{IntegerAttr}>`, e.g., `!mod_arith.int<17 : i32>`.
  The modulus is kept as written (see `AttrParserState.rawIntegerLiterals`).
-/
def parseOptionalModArithType : AttrParserM (Option TypeAttr) := do
  if !(← parseOptionalTypeName "mod_arith.int" false) then return none
  parsePunctuation "<"
  let some modulus ← withRawIntegerLiterals parseOptionalNumericAttr
    | throwAtCurrentPos "modarith type modulus expected"
  let .integerAttr modulus := modulus
    | throwAtCurrentPos "modarith type modulus expected"
  parsePunctuation ">"
  return some (ModArithType.mk modulus.value (some modulus.type))

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
  if !(← parseOptionalTypeName "hw.modty" false) then return none
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
  if !(← parseOptionalTypeName "llvm.array" short) then return none
  parsePunctuation "<"
  let size ← parseInteger false false
  parseKeyword "x".toByteArray
  let ty ← parseLLVMType
  parsePunctuation ">"
  return some (LLVM.ArrayType.mk size.toNat ty.val)

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
    let outputs := outputs.map (fun x => x.val)
    return some (FunctionType.mk inputs outputs (isVarArg := false))
  | none =>
    -- If there is no list of output, check for a single output type.
    let outputType ← parseType "function type output expected"
    return some (FunctionType.mk inputs #[outputType] (isVarArg := false))

/--
  Parse an LLVM struct type, if present.
  Its syntax is `!llvm.struct<...>`, or (exclusively) the shorter form
  `struct<...>` if the corresponding argument is set. The struct is kept as an
  `UnregisteredAttr` holding its text.
-/
partial def parseOptionalLLVMStructType (short := false) : AttrParserM (Option TypeAttr) := do
  if !(← parseOptionalTypeName "llvm.struct" short) then return none
  let startPos ← getPos
  parsePunctuation "<"
  let _ ← parseUnregisteredAttrBody
  let endPos := (← peekToken).slice.stop
  parsePunctuation ">"
  let body := (Slice.mk startPos endPos).of (← getThe ParserState).input
  return some (unregisteredType ("!llvm.struct" ++ String.fromUTF8! body))

/--
  Parse a type within an LLVM-dialect type body, accepting the LLVM "pretty-print"
  sugar keywords `void`, `ptr`, `x86_amx`, `ppc_fp128`, `label`, `metadata`, `token`, and
  the bare nested forms `array<...>`, `struct<...>`, `func<...>`, and
  `target<...>` in addition to the regular MLIR type forms.
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
  if let some type ← parseOptionalLLVMFunctionType true then
    return type
  for name in llvmParameterlessTypes do
    if let some type ← parseOptionalUnregisteredSingletonType name true then
      return type
  if let some type ← parseOptionalUnregisteredType "llvm.target" true then
    return type
  parseType errorMsg

/--
  Parse an LLVM function type `!llvm.func<...>`, or `func<...>` when `short`, if present.
  A trailing `...` parameter marks the function as variadic; the ellipsis is invalid
  in any position other than the last.
-/
partial def parseOptionalLLVMFunctionType (short := false) : AttrParserM (Option TypeAttr) := do
  if !(← parseOptionalTypeName "llvm.func" short) then return none
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
  Parse a type, if present.
-/
partial def parseOptionalType : AttrParserM (Option TypeAttr) := do
  if let some integerType ← parseOptionalIntegerType then
    return some integerType
  if let some floatType ← parseOptionalFloatType then
    return some floatType
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
  for name in llvmParameterlessTypes do
    if let some llvmParameterlessType ← parseOptionalUnregisteredSingletonType name then
      return some llvmParameterlessType
  if let some llvmTargetType ← parseOptionalUnregisteredType "llvm.target" then
    return some llvmTargetType
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
  Its syntax is `dense<value> : type`, e.g. `dense<0> : tensor<4xi8>`
  or `dense<[32, 64]> : vector<2xi64>`.
  The whole attribute is kept as its source text.
-/
partial def parseOptionalDenseElementsAttr : AttrParserM (Option Attribute) := do
  let startPos ← getPos
  if !(← parseOptionalKeyword "dense".toByteArray) then
    return none
  parsePunctuation "<"
  let _ ← parseUnregisteredAttrBody
  parsePunctuation ">"
  parsePunctuation ":"
  if !(← parseOptionalKeyword "tensor".toByteArray) then
    parseKeyword "vector".toByteArray
      "'tensor' or 'vector' type expected in dense elements attribute"
  parsePunctuation "<"
  let _ ← parseUnregisteredAttrBody
  let endPos := (← peekToken).slice.stop
  parsePunctuation ">"
  let text := (Slice.mk startPos endPos).of (← getThe ParserState).input
  return some (UnregisteredAttr.mk (String.fromUTF8! text) false)

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
  MLIR lets any dialect attribute carry one, e.g. `#foo.bar<baz> : i32`. The type is kept
  textually with the attribute.
-/
partial def parseOptionalUnregisteredAttrType (attr : Attribute) : AttrParserM Attribute := do
  let .unregisteredAttr ⟨value, false⟩ := attr | return attr
  if ← parseOptionalPunctuation ":" then
    let type ← parseType
    return (UnregisteredAttr.mk (value ++ " : " ++ toString type) false : Attribute)
  return attr

/--
  Parse an attribute, if present.
-/
partial def parseOptionalAttribute : AttrParserM (Option Attribute) := do
  if let some dialectAttr ← parseOptionalDialectAttr then
    return some (← parseOptionalUnregisteredAttrType dialectAttr)
  else if let some locationAttr ← parseOptionalLocationAttr then
    return some locationAttr
  else if let some type ← parseOptionalType then
    return some type.val
  else if let some numericAttr ← parseOptionalNumericAttr then
    return some numericAttr
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
  else if let some symRefAttr ← parseOptionalSymbolRefAttr then
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
