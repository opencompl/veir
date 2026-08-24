import Veir.PatternRewriter.Puddle.Builders

open Veir
open Veir.Puddle

/-- Match an arithmetic constant of a given value. -/
def matchConstant (returnType : Handle OpCode .type) (constant : Int)
    : MatchProg.Builder (Handle OpCode .value) := do
  let x ← MatchProg.value returnType
  let _ ← MatchProg.root (.arith .constant) #[] #[returnType]
    (fun properties => properties.value.value = constant)
  return x

/-- Match an `arith.addi` whose right-hand operand is the constant zero. -/
private def matchAddZero : MatchProg OpCode (Handle OpCode .value) :=
  MatchProg.build do
    let returnType ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value returnType
    let cstVal ← matchConstant returnType 0
    let _ ← MatchProg.root (.arith .addi) #[x, cstVal] #[returnType]
    return x
