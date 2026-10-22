import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
/-- Pinned LLVM IS6666: cancellation of two identical bit permutations. -/
def IS6666 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 16 || t.bitwidth == 32 || t.bitwidth == 64)
    let x ← MatchProg.value ty
    let inner ← MatchProg.operation (.llvm .intr__bswap) #[x] #[ty]
    let _ ← MatchProg.root (.llvm .intr__bswap) inner.res #[ty]
    return x)
  pure (fun x => x)

theorem IS6666_valid : Pattern.Valid IS6666 := by
  simp only [IS6666]
  provePuddleValid
  rintro _ ⟨w,s⟩ rfl hw
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x
  rintro ip iv ii
  obtain rfl := (bswap_iff _ _ _ _).mp ii
  rintro rp rv ri
  obtain rfl := (bswap_iff _ _ _ _).mp ri
  cases x with
  | poison => simp [LLVM.Int.bswap, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
  | val x =>
    by_cases h16 : w = 16
    · subst w
      suffices LLVM.Int.bswap16BV (LLVM.Int.bswap16BV x) = x by
        simp [LLVM.Int.bswap, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure, this]
      simp only [LLVM.Int.bswap16BV, LLVM.Int.bswap32BV, LLVM.Int.bswap64BV]
      bv_decide
    by_cases h32 : w = 32
    · subst w
      suffices LLVM.Int.bswap32BV (LLVM.Int.bswap32BV x) = x by
        simp [LLVM.Int.bswap, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure, this]
      simp only [LLVM.Int.bswap16BV, LLVM.Int.bswap32BV, LLVM.Int.bswap64BV]
      bv_decide
    by_cases h64 : w = 64
    · subst w
      suffices LLVM.Int.bswap64BV (LLVM.Int.bswap64BV x) = x by
        simp [LLVM.Int.bswap, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure, this]
      simp only [LLVM.Int.bswap16BV, LLVM.Int.bswap32BV, LLVM.Int.bswap64BV]
      bv_decide
    simp [LLVM.Int.bswap, h16, h32, h64, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
end Veir.InstSimplify
