import Veir.Passes.ArithCanonicalize.ConstSupport
import Veir.Passes.ArithCanonicalize.SelectSupport

/-! Constant-fold signed minimum for scalar integers. -/
namespace Veir.ArithCanonicalize.F127

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize.SelectSupport

private def folded (w : Nat) (a b : Int) : BitVec w :=
  let a := BitVec.ofInt w a
  let b := BitVec.ofInt w b
  if a.sle b then a else b

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.arith .constant) #[] #[ty]
      let b ← MatchProg.operation (.arith .constant) #[] #[ty]
      let _ ← MatchProg.root (.arith .minsi) #[a.res[0]!, b.res[0]!] #[ty]
      return (ty, a.properties, b.properties))
    (fun (ty, a, b) => do
      let p ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.arith .constant))) (ty, a, b)
        (fun (ty, a, b) => do
          let some intTy := ty.cast? IntegerType | none
          let bits := folded intTy.bitwidth a.value.value b.value.value
          some { value := IntegerAttr.ofInt bits.toInt intTy })
      CreateProg.operation (.arith .constant) #[] #[ty] p)
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  unfold pattern
  provePuddleValid
  simp only [IsTypeAttr.cast?_of]
  rintro ⟨w, s⟩ pa va ha pb vb hb p v hv
  obtain rfl := (constant_iff _ _ _).mp ha
  obtain rfl := (constant_iff _ _ _).mp hb
  obtain rfl := (minsi_iff _ _ _ _).mp hv
  refine ⟨.int w (.val (folded w pa.value.value pb.value.value)), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    congr 1
    rw [ofInt_ofInt, BitVec.ofInt_toInt]
  · simp [folded, LLVM.Int.smin, RuntimeValue.isRefinedBy,
      isRefinedBy, Id.run]

end Veir.ArithCanonicalize.F127
