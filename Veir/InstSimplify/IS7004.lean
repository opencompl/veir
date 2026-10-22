import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem ctlz_ashr_negative_refines (w : Nat) (a : BitVec w) (ha : a.msb = true)
    (x : LLVM.Int w) (exact zp : Bool) :
    RuntimeValue.int w (LLVM.Int.ctlz (LLVM.Int.ashr (.val a) x exact) zp) ⊒ .int w (.val 0) := by
  cases x with
  | poison => simp [LLVM.Int.ashr, LLVM.Int.ctlz, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val x =>
    have hc : LLVM.Int.ashr (.val a) (.val x) exact = .poison ∨
        LLVM.Int.ashr (.val a) (.val x) exact = .val (a.sshiftRight' x) := by
      simp only [LLVM.Int.ashr, Id.run, pure]
      repeat' split <;> simp_all
      all_goals grind
    rcases hc with hc | hc
    · rw [hc]
      simp [LLVM.Int.ctlz, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    · rw [hc, ctlz_negative _ (by simpa [BitVec.msb_sshiftRight'] using ha) zp]
      exact RuntimeValue.isRefinedBy_refl _

/-- Source m_Negative matches any signed-negative APInt, not only all-ones. -/
def IS7004 (n : Int) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← matchBitConstant ty n
    MatchProg.matchNative ty (fun t => match t.val with | .integerType t => (BitVec.ofInt t.bitwidth n).msb | _ => false)
    let x ← MatchProg.value ty
    let shifted ← MatchProg.operation (.llvm .ashr) #[a,x] #[ty]
    let _ ← MatchProg.root (.llvm .intr__ctlz) shifted.res #[ty]
    return ty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__zero) ()
    let z ← CreateProg.operation (.llvm .mlir__zero) #[] #[ty] p
    return z.res[0]!) (fun x => x)
theorem IS7004_valid (n : Int) : Pattern.Valid (IS7004 n) := by
  simp only [IS7004, matchBitConstant]
  provePuddleValid
  rintro ⟨w,s⟩ cp cv ci
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x
  rintro sp sv si rp rv ri hc hn
  obtain rfl := matched_bit_constant_eq _ _ _ _ ci hc
  have hn : (BitVec.ofInt w n).msb = true := by simpa [TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of] using hn
  obtain rfl := (ashr_iff _ _ _ _ _).mp si
  obtain rfl := (ctlz_iff _ _ _ _).mp ri
  refine ⟨.int w (.val 0), ?_, ?_⟩
  · exact (zero_iff _ _ _).mpr rfl
  · exact ctlz_ashr_negative_refines _ _ hn _ _ _
end Veir.InstSimplify
