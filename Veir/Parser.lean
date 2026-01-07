import Std.Internal.Parsec
import Veir.IR.Basic
import Veir.Rewriter.Basic
import Veir.Printer

open Std.Internal.Parsec
open Std.Internal.Parsec.ByteArray

namespace Veir
namespace Parser

@[inline]
def tryParse (parser : Parser α) : Parser (Option α) := do
  attempt (some <$> parser) <|> return none

@[inline]
def ensureParse (parser : Parser (Option α)) (message : String) : Parser α := do
  match (← parser) with
  | some res => return res
  | none => fail message

@[inline]
def parseCharacter (c : Char) : Parser UInt8 := do
  pbyte c.toUInt8

def parseOptionalStringLiteral : Parser (Option ByteArray) := do
  ws
  if (← tryParse (parseCharacter '"')) = none then
    return none
  let chars ← many (satisfy (· ≠ '"'.toUInt8))
  let _ ← parseCharacter '"'
  return ByteArray.mk chars

def parseStringLiteral : Parser ByteArray := do
  ensureParse parseOptionalStringLiteral "string literal expected"

/-- Check if a byte is a letter (a-z, A-Z) -/
@[inline]
def isLetter (b : UInt8) : Bool :=
  (b >= 'a'.toUInt8 && b <= 'z'.toUInt8) || (b >= 'A'.toUInt8 && b <= 'Z'.toUInt8)

/-- Check if a byte is an underscore -/
@[inline]
def isUnderscore (b : UInt8) : Bool :=
  b == '_'.toUInt8

/-- Check if a byte is a digit (0-9) -/
@[inline]
def isDigitByte (b : UInt8) : Bool :=
  b >= '0'.toUInt8 && b <= '9'.toUInt8

/-- Check if a byte is an id-punct character ($, .) -/
@[inline]
def isIdPunct (b : UInt8) : Bool :=
  b == '$'.toUInt8 || b == '.'.toUInt8

/-- Check if a byte can start a bare-id (letter or underscore) -/
@[inline]
def isBareIdStart (b : UInt8) : Bool :=
  isLetter b || isUnderscore b

/-- Check if a byte can continue a bare-id (letter, digit, underscore, $, or .) -/
@[inline]
def isBareIdContinue (b : UInt8) : Bool :=
  isLetter b || isDigitByte b || isUnderscore b || isIdPunct b

/-- Check if a byte can start a suffix-id (digit, letter, or id-punct) -/
@[inline]
def isSuffixIdStart (b : UInt8) : Bool :=
  isDigitByte b || isLetter b || isIdPunct b

/-- Check if a byte can continue a suffix-id (letter, digit, or id-punct) -/
@[inline]
def isSuffixIdContinue (b : UInt8) : Bool :=
  isLetter b || isDigitByte b || isIdPunct b

def parseIdPunctuation : Parser UInt8 := do
  parseCharacter '$' <|> parseCharacter '.' <|> parseCharacter '-' <|> parseCharacter '_'

@[inline]
def parseAsciiLetter : Parser UInt8 := do
  let l ← asciiLetter
  return l.toUInt8

@[inline]
def parseDigit : Parser UInt8 := do
  let d ← digit
  return d.toUInt8

def parseOptionalBareId : Parser (Option ByteArray) := do
  match ← tryParse (parseAsciiLetter <|> pbyte '_'.toUInt8) with
  | none => return none
  | some start =>
    let rest ← many (parseAsciiLetter <|> parseDigit)
    return ByteArray.mk (#[start] ++ rest)

def parseBareId : Parser ByteArray := do
  ensureParse parseOptionalBareId "bare-id expected"

/-- Parse a suffix-id: (digit+ | ((letter|id-punct) (letter|id-punct|digit)*))
    Returns the parsed suffix as a ByteArray -/
def parseSuffixId : Parser ByteArray := do
  match ← many parseDigit with
  | #[] =>
    let start ← parseAsciiLetter <|> parseIdPunctuation
    let rest ← many (parseAsciiLetter <|> parseIdPunctuation <|> parseDigit)
    return ByteArray.mk (#[start] ++ rest)
  | digits => return ByteArray.mk digits

/-- Parse a value-id: `%` suffix-id
    Returns the suffix-id part (without the %) -/
def parseOptionalValue (map : Std.HashMap ByteArray ValuePtr) : Parser (Option ValuePtr) := do
  match ← tryParse (parseCharacter '%') with
  | some _ =>
    let suffix ← parseSuffixId
    match map[suffix]? with
    | some valuePtr => return some valuePtr
    | none => fail s!"unknown value id: %{String.fromUTF8! suffix}"
  | none => return none

def parseValue (map : Std.HashMap ByteArray ValuePtr) : Parser ValuePtr := do
  ensureParse (parseOptionalValue map) "value expected"

def opName (opType: Nat) : String :=
  match opType with
  | 0 => "builtin.module"
  | 1 => "arith.constant"
  | 2 => "arith.addi"
  | 3 => "return"
  | 4 => "arith.muli"
  | 5 => "arith.andi"
  | 99 => "test.test"
  | _ => "UNREGISTERED"

set_option linter.unusedVariables false in
def getOpId (name : ByteArray) : Nat :=
  match String.fromUTF8! name with
  | "builtin.module" => 0
  | "arith.constant" => 1
  | "arith.addi" => 2
  | "return" => 3
  | "arith.muli" => 4
  | "arith.andi" => 5
  | "test.test" => 99
  | _ => 1000000

def parseOptionalOpResult : Parser (Option ByteArray) := do
  ws
  match ← tryParse (parseCharacter '%') with
  | some _ => parseSuffixId
  | none => return none

def parseOpResult : Parser ByteArray := do
  ensureParse parseOptionalOpResult "opresult expected"

def parseOpResults : Parser (Array ByteArray) := do
  ws
  match ← parseOptionalOpResult with
  | none => return #[]
  | some name =>
    let mut results := #[name]
    while true do
      ws
      match ← tryParse (parseCharacter ',') with
      | some _ =>
        ws
        let name2 ← parseOpResult
        results := results.push name2
      | none => break
    let _ ← parseCharacter '='
    return results

mutual
partial def parseOptionalBlock (ctx : IRContext) (ip : Option BlockInsertPoint) (nameToValues : Std.HashMap ByteArray ValuePtr) : Parser (Option (IRContext × BlockPtr)) := do
  ws
  match Rewriter.createBlock ctx ip (by sorry) (by sorry) with
  | none => fail "internal error: failed to create block"
  | some (ctx', block) =>
    let mut nameToValues := nameToValues
    let mut ctx := ctx'
    while true do
      match ← parseOptionalOperation ctx nameToValues with
      | none => break
      | some (ctx', op, nameToValues') =>
        ctx := ctx'
        nameToValues := nameToValues'
        match Rewriter.insertOp? ctx op (InsertPoint.atEnd block) (by sorry) (by sorry) (by sorry) with
        | none => fail "internal error: failed to insert operation"
        | some ctx'' =>
          ctx := ctx''
    return some (ctx, block)

partial def parseBlock (ctx : IRContext) (ip : Option BlockInsertPoint) (nameToValues : Std.HashMap ByteArray ValuePtr) : Parser (IRContext × BlockPtr) := do
  ensureParse (parseOptionalBlock ctx ip nameToValues) "block expected"

partial def parseOptionalRegion (ctx : IRContext) (nameToValues : Std.HashMap ByteArray ValuePtr) : Parser (Option (IRContext × RegionPtr)) := do
  ws
  match ← tryParse (parseCharacter '{') with
  | some _ =>
    match Rewriter.createRegion ctx with
    | some (ctx', region) =>
      let (ctx'', block) ← parseBlock ctx' (BlockInsertPoint.atEnd region) nameToValues
      let _ ← parseCharacter '}'
      return (ctx'', region)
    | none => fail "internal error: failed to create region"
  | none => return none

partial def parseRegion (ctx : IRContext) (nameToValues : Std.HashMap ByteArray ValuePtr) : Parser (IRContext × RegionPtr) := do
  ensureParse (parseOptionalRegion ctx nameToValues) "region expected"

partial def parseOpRegions (ctx : IRContext) (nameToValues : Std.HashMap ByteArray ValuePtr) : Parser (IRContext × Array RegionPtr) := do
  ws
  let mut ctx := ctx
  let mut regions : Array RegionPtr := #[]
  match ← (tryParse (parseCharacter '(')) with
  | none => return (ctx, regions)
  | some _ =>
    ws
    match (← tryParse (parseCharacter ')')) with
    | some _ => return (ctx, regions)
    | none => do
      ws
      let (ctx', firstRegion) ← parseRegion ctx nameToValues
      ctx := ctx'
      while true do
        ws
        match ← tryParse (parseCharacter ')') with
        | some _ => break
        | none =>
          ws
          let _ ← parseCharacter ','
          ws
          match ← parseOptionalRegion ctx nameToValues with
          | some (ctx', region) =>
            ctx := ctx'
            regions := regions.push region
          | none => break
      return (ctx, #[firstRegion] ++ regions)

partial def parseOperands (ctx : IRContext) (nameToValues : Std.HashMap ByteArray ValuePtr) : Parser (IRContext × Array ValuePtr) := do
  ws
  let _ ← parseCharacter '('
  ws
  match (← tryParse (parseCharacter ')')) with
  | some _ => return (ctx, #[])
  | none => do
    ws
    let mut ctx := ctx
    let mut operands : Array ValuePtr := #[]
    let operand ← parseValue nameToValues
    operands := operands.push operand
    while true do
      ws
      match ← tryParse (parseCharacter ')') with
      | some _ => break
      | none => do
        ws
        let _ ← parseCharacter ','
        ws
        let operand ← parseValue nameToValues
        operands := operands.push operand
    return (ctx, operands)

partial def parseOptionalOperation (ctx : IRContext) (nameToValues : Std.HashMap ByteArray ValuePtr) : Parser (Option (IRContext × OperationPtr × Std.HashMap ByteArray ValuePtr)) := do
  ws
  let results ← parseOpResults
  ws
  match ← parseOptionalStringLiteral with
  | some name =>
    let id := getOpId name
    let (ctx, operands) ← parseOperands ctx nameToValues
    let (ctx, regions) ← parseOpRegions ctx nameToValues
    match Rewriter.createOp ctx id results.size operands regions 0 none (by sorry) (by grind) (by sorry) with
    | none => fail "internal error: failed to create operation"
    | some (ctx, op) =>
      let mut nameToValues := nameToValues
      for i in [0:results.size] do
        let resultName := results[i]!
        let resultPtr := ValuePtr.opResult (op.getResult i)
        nameToValues := nameToValues.insert resultName resultPtr
      return some (ctx, op, nameToValues)
  | none => return none

partial def parseOperation (ctx : IRContext) (nameToValues : Std.HashMap ByteArray ValuePtr) : Parser (IRContext × OperationPtr × Std.HashMap ByteArray ValuePtr) := do
  ensureParse (parseOptionalOperation ctx nameToValues) "operation expected"

end

partial def parseModule : Parser IRContext := do
  match IRContext.create with
  | some (ctx, op) =>
    let (ctx, op', _) ← parseOperation ctx ∅
    let ctx := {ctx with topLevelOp := op'}
    let ctx := Rewriter.eraseOp ctx op (by sorry) (by sorry)
    return ctx
  | none => fail "internal error: failed to create IR context"

partial def roundtrip (string : ByteArray) : IO Unit :=
  let a := Parser.run parseModule string
  match a with
  | .ok a => Printer.printModule a a.topLevelOp
  | .error err => IO.print s!"Parse error: {err}"

#eval! roundtrip ("%x = \"builtin.module\"() ({
  %a = \"arith.constant\"()
  %x = \"arith.addi\"(%a, %a)
})".toByteArray)
--#eval! (Parser.run parseModule ("\"builtin.module\"() ({})".toByteArray))
