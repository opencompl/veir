import Veir.Passes.ArithCanonicalize.SelectSupport

/-! Pinned fold `cmpi ne, x:i1, 0 -> x`. -/
namespace Veir.ArithCanonicalize.F084

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle Veir.ArithCanonicalize.SelectSupport

private theorem i1_cases (v : BitVec 1) : v = 0#1 ∨ v = 1#1 := by
  bv_decide

theorem ne_zero_refines (x : LLVM.Int 1) :
    RuntimeValue.int 1 (LLVM.Int.icmp x (.val (0#1)) .ne) ⊒ .int 1 x := by
  cases x with
  | poison => simp [LLVM.Int.icmp, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val v =>
    rcases i1_cases v with h | h <;> subst v <;>
      simp [LLVM.Int.icmp, LLVM.IntPred.eval,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let x ← MatchProg.value ty
      let zero ← matchConstant ty 0
      let _ ← MatchProg.root (.arith .cmpi) #[x, zero] #[ty]
        (fun p => p.predicate == .ne)
      return x)
    pure
    (fun x => x)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern, matchConstant]
  provePuddleValid
  rintro ty ⟨w, sign⟩ rfl hWidth x hx zeroProp zeroVal hZero hZeroInterp
    rootProp result hPred hResult
  dsimp at hWidth
  subst w
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  obtain rfl := (constant_iff _ _ _).mp hZeroInterp
  obtain rfl := (cmpi_iff _ _ _ _ _).mp hResult
  cases x with
  | poison => simp [LLVM.Int.icmp, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val v =>
    have hv := i1_cases v
    rcases hv with hv | hv <;> subst v <;>
      simp [hPred, hZero, LLVM.Int.icmp, LLVM.IntPred.eval,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

end Veir.ArithCanonicalize.F084
