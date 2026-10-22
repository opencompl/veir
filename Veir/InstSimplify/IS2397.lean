import Veir.InstSimplify.RotateSupport
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS2397
/-- Parameterize which shift contains C-X, and the enclosing OR order. -/
def pattern (constant : Int) (subOnLeft commute : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let c ← matchBitConstant ty constant
    let onesL ← matchBitConstant ty (-1)
    let onesR ← matchBitConstant ty (-1)
    let b ← MatchProg.operation (.llvm .sub) #[c,a] #[ty]
    let l ← MatchProg.operation (.llvm .shl) #[onesL,cond subOnLeft b.res[0]! a] #[ty]
    let r ← MatchProg.operation (.llvm .lshr) #[onesR,cond subOnLeft a b.res[0]!] #[ty]
    let _ ← MatchProg.root (.llvm .or) (cond commute #[r.res[0]!,l.res[0]!] #[l.res[0]!,r.res[0]!]) #[ty]
    MatchProg.matchNative ty (fun ty => match ty.val with
      | .integerType t => decide ((BitVec.ofInt t.bitwidth constant).toNat ≤ t.bitwidth)
      | _ => false)
    return onesL) pure (fun x => x)

theorem semantic (w : Nat) (a : LLVM.Int w) (c : BitVec w)
    (subNSW subNUW shlNSW shlNUW exact disjoint subOnLeft : Bool) (hc : c.toNat ≤ w) :
    RuntimeValue.int w (LLVM.Int.or
      (LLVM.Int.shl (.val (BitVec.allOnes w))
        (cond subOnLeft (LLVM.Int.sub (.val c) a subNSW subNUW) a) shlNSW shlNUW)
      (LLVM.Int.lshr (.val (BitVec.allOnes w))
        (cond subOnLeft a (LLVM.Int.sub (.val c) a subNSW subNUW)) exact) disjoint) ⊒
      .int w (.val (BitVec.allOnes w)) := by
  cases a with
  | poison => cases subOnLeft <;>
      simp [LLVM.Int.sub,LLVM.Int.shl,LLVM.Int.lshr,LLVM.Int.or,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy,cond]
  | val a =>
    rcases sub_outcomes c a subNSW subNUW with hs | hs
    · cases subOnLeft
      · simp only [hs,cond,LLVM.Int.lshr,Id.run,pure]
        cases h : LLVM.Int.shl (.val (BitVec.allOnes w)) (.val a) shlNSW shlNUW <;>
          simp [h,LLVM.Int.or,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy]
      · simp [hs,LLVM.Int.shl,LLVM.Int.lshr,LLVM.Int.or,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy,cond]
    · cases subOnLeft
      · simpa only [cond,hs] using rotate_shifts_refine a (c-a) c shlNSW shlNUW exact disjoint hc rfl
      · have hrev : a = c-(c-a) := by
          symm
          apply BitVec.sub_eq_iff_eq_add.mpr
          rw [BitVec.add_comm]
          exact (BitVec.sub_add_cancel c a).symm
        simpa only [cond,hs] using rotate_shifts_refine (c-a) a c shlNSW shlNUW exact disjoint hc hrev

theorem valid (constant : Int) (subOnLeft commute : Bool) :
    Pattern.Valid (pattern constant subOnLeft commute) := by
  cases subOnLeft <;> cases commute
  all_goals
    simp only [pattern,matchBitConstant]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType,forall_exists_index,forall_eq_apply_imp_iff]
    rintro ⟨w,s⟩ a cp cv hci olp olv holi orp orv hori sp sv hsi lp lv hli rp rv hri rootp rootv hroot hc hol hor hbound
    obtain rfl := matched_bit_constant_eq _ _ constant _ hci hc
    obtain rfl := matched_bit_constant_eq _ _ (-1) _ holi hol
    obtain rfl := matched_bit_constant_eq _ _ (-1) _ hori hor
    obtain rfl := (sub_iff _ _ _ _ _).mp hsi
    obtain rfl := (shl_iff _ _ _ _ _).mp hli
    obtain rfl := (lshr_iff _ _ _ _ _).mp hri
    obtain rfl := (or_iff _ _ _ _ _).mp hroot
    have hbound : (BitVec.ofInt w constant).toNat ≤ w := by
      simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hbound
    first
    | simpa only [const_negOne,logic_or_comm,cond] using semantic w a (BitVec.ofInt w constant) sp.nsw sp.nuw lp.nsw lp.nuw rp.exact rootp.disjoint false hbound
    | simpa only [const_negOne,logic_or_comm,cond] using semantic w a (BitVec.ofInt w constant) sp.nsw sp.nuw lp.nsw lp.nuw rp.exact rootp.disjoint true hbound
end Veir.InstSimplify.IS2397
