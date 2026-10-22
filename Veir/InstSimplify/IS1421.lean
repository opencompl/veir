import Veir.InstSimplify.LogicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1421
private theorem negative_shl_refines (a b : LLVM.Int w) (ns : Bool)
    (ha : ∀ v, a = .val v → v.msb = true) :
    RuntimeValue.int w (LLVM.Int.shl a b ns true) ⊒ .int w a := by
  cases a with
  | poison => simp [LLVM.Int.shl, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  | val a =>
    have ha := ha a rfl
    have noShift (b : BitVec w) (h : (a <<< b) >>> b = a) : b.toNat = 0 := by
      have hm := congrArg BitVec.msb h
      change ((a <<< b.toNat) >>> b.toNat).msb = a.msb at hm
      simp only [BitVec.msb_ushiftRight, ha, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hm
      omega
    cases b <;> simp [LLVM.Int.shl, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    grind

/-- shl nuw C,X → C when C is a negative scalar integer constant. -/
def pattern (n : Int) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty n
      let _ ← MatchProg.root (.llvm .shl) #[c,x] #[ty] (fun p => p.nuw)
      MatchProg.matchNative ty (fun t => match t.val with
        | .integerType it => (BitVec.ofInt it.bitwidth n).msb
        | _ => false)
      return c)
    pure (fun x => x)

theorem valid (n : Int) : Pattern.Valid (pattern n) := by
  simp only [pattern, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hp hi hz hn
  obtain rfl := matched_bit_constant_eq _ cp n cv hc hz
  obtain rfl := (shl_iff w p _ x v).mp hi
  change (BitVec.ofInt w n).msb = true at hn
  rw [hp]
  apply negative_shl_refines
  intro v hv
  cases hv
  exact hn
end Veir.InstSimplify.IS1421
