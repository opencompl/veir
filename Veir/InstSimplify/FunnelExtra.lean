import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
theorem rotate_select_eq_zero (left swap : Bool) {w : Nat} (x : LLVM.Int w) (c r : BitVec w)
 (hr : r.toNat = c.toNat % w) :
 LLVM.Int.select (match swap with | false => LLVM.Int.icmp (.val r) (.val (0#w)) .eq | true => LLVM.Int.icmp (.val (0#w)) (.val r) .eq) x
  ((match left with | true => LLVM.Int.fshl | false => LLVM.Int.fshr) x x (.val c)) =
  ((match left with | true => LLVM.Int.fshl | false => LLVM.Int.fshr) x x (.val c)) := by
 cases left <;> cases swap <;> cases x
 all_goals
  by_cases hz : r = 0#w
  · have hc : c.toNat % w = 0 := by rw [← hr,hz]; rfl
    simp [LLVM.Int.icmp,LLVM.IntPred.eval,LLVM.Int.select,LLVM.Int.fshl,LLVM.Int.fshr,hz,hc,
      BitVec.extractLsb'_append_eq_left,BitVec.setWidth_append_eq_right,Id.run,pure]
  · simp [LLVM.Int.icmp,LLVM.IntPred.eval,LLVM.Int.select,hz,Ne.symm hz,Id.run,pure]
theorem funnel_recombine_left {w : Nat} (x : BitVec w) (a b : Nat)
 (ha : a < w) (hb : b < w) (hab : a+b=w) :
 (((x >>> a) ++ (x <<< b)) <<< a).extractLsb' w w = x := by
 rw [funnel_left_decompose _ _ _ ha]
 have hba : w-a=b := by omega
 rw [hba]
 apply BitVec.eq_of_getLsbD_eq
 intro i
 by_cases hi : i < w
 · by_cases hia : i < a
   · simp [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,hi,hia,Nat.add_comm,
       show ¬a≤i by omega,show i+b<w by omega,show b≤i+b by omega] <;> omega
   · simp [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,hi,hia,Nat.add_comm,
       show a≤i by omega,show i+b≥w by omega,show i-a<w by omega,show i-a+a=i by omega]
 · simp [BitVec.getLsbD_of_ge,show w≤i by omega]
theorem funnel_recombine_right {w : Nat} (x : BitVec w) (a b : Nat)
 (ha : a < w) (hb : b < w) (hab : a+b=w) :
 (((x >>> a) ++ (x <<< b)) >>> b).truncate w = x := by
 rw [funnel_right_decompose _ _ _ hb]
 have hba : w-b=a := by omega
 rw [hba]
 apply BitVec.eq_of_getLsbD_eq
 intro i
 by_cases hi : i < w
 · by_cases hia : i < a
   · simp [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,hi,hia,Nat.add_comm,
       show ¬a≤i by omega,show i+b<w by omega,show b≤i+b by omega] <;> omega
   · simp [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,hi,hia,Nat.add_comm,
       show a≤i by omega,show i+b≥w by omega,show i-a<w by omega,show i-a+a=i by omega]
 · simp [BitVec.getLsbD_of_ge,show w≤i by omega]
theorem twice_width_le_pow (w : Nat) : 2*w ≤ 2^w := by
 cases w with
 | zero => decide
 | succ n =>
  induction n with
  | zero => decide
  | succ n ih => simp only [Nat.pow_succ] at *; omega

theorem funnel_recombine_semantic (left : Bool) {w : Nat} (x : LLVM.Int w) (a b c : BitVec w)
 (ex nsw nuw : Bool) (hab : a+b=BitVec.ofNat w w)
 (hc : c.toNat % w = (match left with | true => a | false => b).toNat) :
 RuntimeValue.int w ((match left with | true => LLVM.Int.fshl | false => LLVM.Int.fshr)
   (LLVM.Int.lshr x (.val a) ex) (LLVM.Int.shl x (.val b) nsw nuw) (.val c)) ⊒ .int w x := by
 cases x with
 | poison => cases left <;> simp [LLVM.Int.lshr,LLVM.Int.shl,LLVM.Int.fshl,LLVM.Int.fshr,RuntimeValue.isRefinedBy,isRefinedBy,Id.run]
 | val x =>
  have hl : LLVM.Int.lshr (.val x) (.val a) ex = .poison ∨ LLVM.Int.lshr (.val x) (.val a) ex = .val (x >>> a) := by
   simp only [LLVM.Int.lshr,Id.run,pure]
   repeat' split <;> simp_all
   all_goals grind
  have hr : LLVM.Int.shl (.val x) (.val b) nsw nuw = .poison ∨ LLVM.Int.shl (.val x) (.val b) nsw nuw = .val (x <<< b) := by
   simp only [LLVM.Int.shl,Id.run,pure]
   repeat' split <;> simp_all
   all_goals grind
  rcases hl with hl | hl
  · rw [hl]; cases left <;> simp [LLVM.Int.fshl,LLVM.Int.fshr,RuntimeValue.isRefinedBy,isRefinedBy,Id.run]
  rcases hr with hr | hr
  · rw [hl,hr]; cases left <;> simp [LLVM.Int.fshl,LLVM.Int.fshr,RuntimeValue.isRefinedBy,isRefinedBy,Id.run]
  have ha : a.toNat < w := by
   by_cases ht : a.toNat < w
   · exact ht
   · have hg : BitVec.ofNat w w ≤ a := by simp only [BitVec.le_def,BitVec.toNat_ofNat,Nat.mod_two_pow_self];omega
     simp [LLVM.Int.lshr,hg,Id.run,pure] at hl
  have hb : b.toNat < w := by
   by_cases ht : b.toNat < w
   · exact ht
   · have hg : BitVec.ofNat w w ≤ b := by simp only [BitVec.le_def,BitVec.toNat_ofNat,Nat.mod_two_pow_self];omega
     simp [LLVM.Int.shl,hg,Id.run,pure] at hr
  have hs := congrArg BitVec.toNat hab
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_two_pow_self] at hs
  have hslt : a.toNat+b.toNat < 2^w := by have := twice_width_le_pow w;omega
  rw [Nat.mod_eq_of_lt hslt] at hs
  rw [hl,hr]
  cases left
  · simp only [LLVM.Int.fshr,Id.run,pure,hc]
    rw [BitVec.ushiftRight_eq',BitVec.shiftLeft_eq',funnel_recombine_right x _ _ ha hb hs]
    exact RuntimeValue.isRefinedBy_refl _
  · simp only [LLVM.Int.fshl,Id.run,pure,hc]
    rw [BitVec.ushiftRight_eq',BitVec.shiftLeft_eq',funnel_recombine_left x _ _ ha hb hs]
    exact RuntimeValue.isRefinedBy_refl _
end Veir.InstSimplify
