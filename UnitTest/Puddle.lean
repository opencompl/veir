import Veir.PatternRewriter.Puddle.Builders

open Veir
open Veir.Puddle

/-- Match an arithmetic constant of a given value. -/
def matchConstant (returnType : Handle OpCode .type) (constant : Int)
    : MatchProg.Builder (Handle OpCode .value) := do
  let op ← MatchProg.operation (.arith .constant) #[] #[returnType]
    (fun properties => properties.value.value = constant)
  return op.res[0]!

/-- Rewrite `x + 0` to `x`. -/
private def addZero : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let cstVal ← matchConstant returnType 0
      let _ ← MatchProg.root (.arith .addi) #[x, cstVal] #[returnType]
      return x)
    pure
    (fun x => x)

/-- Rewrite `x * 2` to `x + x`. -/
private def mulTwo : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let cstVal ← matchConstant returnType 2
      let _ ← MatchProg.root (.arith .muli) #[x, cstVal] #[returnType]
      return (returnType, x))
    (fun (returnType, x) => do
      let properties ← CreateProg.property (.arith .addi)
        (default : propertiesOf (.arith .addi : OpCode))
      let add ← CreateProg.operation (.arith .addi) #[x, x] #[returnType] properties
      return add)
    (fun result => result)
