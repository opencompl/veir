import Veir.Passes.ArithCanonicalize.ConstSupport
import Veir.Passes.ArithCanonicalize.SelectSupport

/-! Constant-fold scalar integer comparison under all ten predicates. -/
namespace Veir.ArithCanonicalize.F087

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize.SelectSupport

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType)
        (fun t => t == IntegerType.signless 1)
      let a ← MatchProg.operation (.arith .constant) #[] #[ty]
      let b ← MatchProg.operation (.arith .constant) #[] #[ty]
      let root ← MatchProg.root (.arith .cmpi) #[a.res[0]!, b.res[0]!] #[boolTy]
      return (ty, boolTy, a.properties, b.properties, root.properties))
    (fun (ty, boolTy, a, b, root) => do
      let p ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.arith .constant))) (ty, a, b, root)
        (fun (ty, a, b, root) => do
          let some intTy := ty.cast? IntegerType | none
          let x := BitVec.ofInt intTy.bitwidth a.value.value
          let y := BitVec.ofInt intTy.bitwidth b.value.value
          let bit : Int := if LLVM.IntPred.eval root.predicate x y then 1 else 0
          some { value := IntegerAttr.ofInt bit (IntegerType.signless 1) })
      CreateProg.operation (.arith .constant) #[] #[boolTy] p)
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  unfold pattern
  provePuddleValid
  simp only [IsTypeAttr.cast?_of]
  rintro ⟨w, s⟩ boolTy ⟨bw, bs⟩ hTy hBool pa va ha pb vb hb p v hv
  cases hTy
  cases hBool
  obtain rfl := (constant_iff _ _ _).mp ha
  obtain rfl := (constant_iff _ _ _).mp hb
  obtain rfl := (cmpi_iff _ _ _ _ _).mp hv
  refine ⟨.int 1 (.val (BitVec.ofBool
    (LLVM.IntPred.eval p.predicate
      (BitVec.ofInt w pa.value.value) (BitVec.ofInt w pb.value.value)))), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    simp [IntegerAttr.ofInt, IntegerAttr.normalizeValue]
    cases h : LLVM.IntPred.eval p.predicate
      (BitVec.ofInt w pa.value.value) (BitVec.ofInt w pb.value.value) <;> rfl
  · simp [LLVM.Int.icmp, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

end Veir.ArithCanonicalize.F087
