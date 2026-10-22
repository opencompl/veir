import Veir.InstSimplify.LogicExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify

theorem double_width_le_power (w : Nat) : 0 < w → 2*w ≤ 2^w := by
  induction w with
  | zero => omega
  | succ w ih =>
    intro hw
    cases w with
    | zero => decide
    | succ w =>
      have h := ih (by omega)
      have hp : 2 ≤ 2^(w+1) := by
        simpa using Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ w+1 by omega)
      rw [Nat.pow_succ]
      omega

theorem shift_bounds_of_lt (x : BitVec w) (h : x < BitVec.ofNat w w) : x.toNat < w := by
  have h' : x.toNat < (BitVec.ofNat w w).toNat := h
  have hm := Nat.mod_le w (2^w)
  simp only [BitVec.toNat_ofNat] at h'
  omega

theorem logic_shl_cases (x y : BitVec w) (nsw nuw : Bool) :
    LLVM.Int.shl (.val x) (.val y) nsw nuw = .poison ∨
    (y.toNat < w ∧ LLVM.Int.shl (.val x) (.val y) nsw nuw = .val (x <<< y)) := by
  simp only [LLVM.Int.shl,Id.run,pure]
  split
  · exact Or.inl rfl
  · rename_i h
    have hb : y.toNat < w := shift_bounds_of_lt y (by exact BitVec.not_le.mp h)
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · exact Or.inr ⟨hb,rfl⟩

theorem logic_lshr_cases (x y : BitVec w) (ex : Bool) :
    LLVM.Int.lshr (.val x) (.val y) ex = .poison ∨
    (y.toNat < w ∧ LLVM.Int.lshr (.val x) (.val y) ex = .val (x >>> y)) := by
  simp only [LLVM.Int.lshr,Id.run,pure]
  split
  · exact Or.inl rfl
  · rename_i h
    have hb : y.toNat < w := shift_bounds_of_lt y (by exact BitVec.not_le.mp h)
    split
    · exact Or.inl rfl
    · exact Or.inr ⟨hb,rfl⟩

theorem rotate_allones_bits (x y : Nat) (h : x+y ≤ w) :
    (BitVec.allOnes w <<< x) ||| (BitVec.allOnes w >>> y) = BitVec.allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hx : x ≤ i
  · simp [BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight,hi,hx]
  · have hright : y+i < w := by omega
    simp [BitVec.getLsbD_shiftLeft,BitVec.getLsbD_ushiftRight,hi,hright]

theorem rotate_amounts_sum (x y c : BitVec w) (hx : x.toNat < w) (hy : y.toNat < w)
    (hc : c.toNat ≤ w) (hrel : y = c-x) : x.toNat+y.toNat ≤ w := by
  have hw : 0 < w := by omega
  have hpow := double_width_le_power w hw
  have hsum : x.toNat + y.toNat < 2^w := by omega
  have he : x+y = c := by rw [hrel,BitVec.add_comm]; exact BitVec.sub_add_cancel c x
  have hn := congrArg BitVec.toNat he
  rw [BitVec.toNat_add,Nat.mod_eq_of_lt hsum] at hn
  omega

theorem rotate_shifts_refine (x y c : BitVec w) (nsw nuw ex disjoint : Bool)
    (hc : c.toNat ≤ w) (hrel : y = c-x) :
    RuntimeValue.int w (LLVM.Int.or
      (LLVM.Int.shl (.val (BitVec.allOnes w)) (.val x) nsw nuw)
      (LLVM.Int.lshr (.val (BitVec.allOnes w)) (.val y) ex) disjoint) ⊒
      .int w (.val (BitVec.allOnes w)) := by
  rcases logic_shl_cases (BitVec.allOnes w) x nsw nuw with hl | ⟨hx,hl⟩
  · simp [hl,LLVM.Int.or,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy]
  · rcases logic_lshr_cases (BitVec.allOnes w) y ex with hr | ⟨hy,hr⟩
    · simp [hl,hr,LLVM.Int.or,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy]
    · have hs := rotate_amounts_sum x y c hx hy hc hrel
      have hb := rotate_allones_bits x.toNat y.toNat hs
      simp only [hl,hr,LLVM.Int.or,Id.run,pure,BitVec.shiftLeft_eq',BitVec.ushiftRight_eq']
      split <;> simp [RuntimeValue.isRefinedBy,isRefinedBy,hb]
end Veir.InstSimplify
