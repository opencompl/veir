import Veir.Passes.ArithCanonicalize.SelectSupport

/-! Pinned fold `cmpi eq, x:i1, 1 -> x`. -/
namespace Veir.ArithCanonicalize.F085

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle Veir.ArithCanonicalize.SelectSupport

private theorem i1_cases (v : BitVec 1) : v = 0#1 ∨ v = 1#1 := by
  bv_decide

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let x ← MatchProg.value ty
      let one ← matchConstant ty 1
      let _ ← MatchProg.root (.arith .cmpi) #[x, one] #[ty]
        (fun p => p.predicate == .eq)
      return x)
    pure
    (fun x => x)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, matchConstant]
  provePuddleValid
  rintro ty ⟨w, sign⟩ rfl hWidth x hx oneProp oneVal hOne hOneInterp
    rootProp result hPred hResult
  dsimp at hWidth
  subst w
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  obtain rfl := (constant_iff _ _ _).mp hOneInterp
  obtain rfl := (cmpi_iff _ _ _ _ _).mp hResult
  cases x with
  | poison => simp [LLVM.Int.icmp, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val v =>
    have hv := i1_cases v
    rcases hv with hv | hv <;> subst v <;>
      simp [hPred, hOne, LLVM.Int.icmp, LLVM.IntPred.eval,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

end Veir.ArithCanonicalize.F085
