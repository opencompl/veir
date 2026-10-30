module

public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.Casting
public import Veir.Dialects.GMIR.Semantics

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect

import Veir.ForLean
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.Dialects.GMIR.Semantics

public section

namespace Veir.Data.LLVM

/--
Prove the correctness of `llvm.add` widening with anyext.
-/
theorem add_widening_32_64 (i i' : LLVM.Int 32) (ext ext' : BitVec 32) (nuw nsw : Bool) :
    LLVM.Int.add i i' nuw nsw ⊒
      LLVM.Int.trunc (LLVM.Int.add
        (LLVM.Int.ext i 64 ext (by grind))
        (LLVM.Int.ext i' 64 ext' (by grind))
        false false
      ) 32 false false (by grind) := by
  veir_bv_decide

/--
Prove the correctness of `widenBlockArguments`: a block argument of width `n` that is widened to
`64` bits carries the `g_anyext` of the value its predecessor passes, whatever the high bits, and
the `g_trunc` at the start of the block recovers that value.
-/
theorem block_argument_widening (n : Nat) (h : n < 64) (x : LLVM.Int n) (e : BitVec (64 - n)) :
    x ⊒ LLVM.Int.trunc (LLVM.Int.ext x 64 e h) n false false h := by
  veir_bv_normalize
  simp [BitVec.eq_of_getElem_eq_iff]
  grind

/--
Prove the correctness of combining `g_anyext (g_trunc x)` to `x`, at every width and whatever the
`nsw` and `nuw` flags of the `g_trunc`.
-/
theorem anyext_trunc_same (w n : Nat) (h : n < w) (x : LLVM.Int w) (nsw nuw : Bool) :
    ∃ ext : BitVec (w - n), LLVM.Int.ext (LLVM.Int.trunc x n nsw nuw h) w ext h ⊒ x :=
  ⟨x.getValueD.extractLsb' n (w - n), by
    veir_bv_normalize
    simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_append]
    grind⟩

/--
Prove the correctness of combining `g_anyext (g_trunc x)` to a narrower `g_trunc x`, at every
width.
-/
theorem anyext_trunc_narrower (w n m : Nat) (hn : n < m) (hm : m < w) (x : LLVM.Int w)
    (nsw nuw : Bool) :
    ∃ ext : BitVec (m - n),
      LLVM.Int.ext (LLVM.Int.trunc x n nsw nuw (by omega)) m ext hn ⊒
        LLVM.Int.trunc x m false false hm :=
  ⟨x.getValueD.extractLsb' n (m - n), by
    veir_bv_normalize
    simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_append]
    grind⟩

/--
Prove the correctness of combining `g_anyext (g_trunc x)` to a wider `g_anyext x`, at every width
and whatever the high bits `ext'` of the new `g_anyext` are.
-/
theorem anyext_trunc_wider (w n m : Nat) (hn : n < w) (hw : w < m) (x : LLVM.Int w)
    (ext' : BitVec (m - w)) (nsw nuw : Bool) :
    ∃ ext : BitVec (m - n),
      LLVM.Int.ext (LLVM.Int.trunc x n nsw nuw hn) m ext (by omega) ⊒
        LLVM.Int.ext x m ext' hw :=
  ⟨(ext' ++ x.getValueD.extractLsb' n (w - n)).cast (by omega), by
    veir_bv_normalize
    simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_append]
    grind⟩

/--
Prove the correctness of combining `g_anyext (g_anyext x)` to `g_anyext x`, at every width.
-/
theorem anyext_anyext (w n m : Nat) (hn : w < n) (hm : n < m) (x : LLVM.Int w)
    (ext : BitVec (m - w)) :
    ∃ ext₁ : BitVec (n - w), ∃ ext₂ : BitVec (m - n),
      LLVM.Int.ext (LLVM.Int.ext x n ext₁ hn) m ext₂ hm ⊒ LLVM.Int.ext x m ext (by omega) :=
  ⟨ext.extractLsb' 0 (n - w), ext.extractLsb' (n - w) (m - n), by
    veir_bv_normalize
    simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_append]
    grind⟩

/--
Prove the correctness of combining `g_trunc (g_trunc x)` to `g_trunc x`, at every width and whatever
the flags of both `g_trunc`s.
-/
theorem trunc_trunc (w n m : Nat) (hn : n < m) (hm : m < w) (x : LLVM.Int w)
    (nsw nuw nsw' nuw' : Bool) :
    LLVM.Int.trunc (LLVM.Int.trunc x m nsw nuw hm) n nsw' nuw' hn ⊒
      LLVM.Int.trunc x n false false (by omega) := by
  veir_bv_normalize
  simp [BitVec.setWidth_setWidth_of_le _ (Nat.le_of_lt hn)]

/-- Bit `i` of the mask `2 ^ n - 1` is set exactly when `i < n`. -/
private theorem getElem_ofInt_two_pow_sub_one {m n i : Nat} (hi : i < m) :
    (BitVec.ofInt m (2 ^ n - 1))[i] = decide (i < n) := by
  rw [show (2 ^ n - 1 : _root_.Int) = ((2 ^ n - 1 : Nat) : _root_.Int) by
    simp [Int.natCast_sub Nat.one_le_two_pow]]
  simp [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, hi]

/--
Prove the correctness of lowering `g_zext` to a `g_and` of a `g_anyext` with the mask of the source
width, at every width.
-/
theorem zext_and_anyext (n m : Nat) (h : n < m) (x : LLVM.Int n) (nneg : Bool)
    (ext : BitVec (m - n)) :
    LLVM.Int.zext x m nneg h ⊒
      LLVM.Int.and (LLVM.Int.ext x m ext h) (LLVM.Int.constant m (2 ^ n - 1)) := by
  veir_bv_normalize
  simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_append, getElem_ofInt_two_pow_sub_one]
  grind

/-- `x` is refined by its low bits after any extension. -/
private theorem trunc_ext_self {n m : Nat} (h : n < m) (x : LLVM.Int n) (ext : BitVec (m - n)) :
    x ⊒ LLVM.Int.trunc (LLVM.Int.ext x m ext h) n false false h := by
  veir_bv_normalize
  simp [BitVec.eq_of_getElem_eq_iff]
  grind

/--
Prove the correctness of widening the values of `g_select` with `g_anyext`, at every width and
whatever the high bits of the extended values are: the selected value is truncated back.
-/
theorem select_widen_values (n m wc : Nat) (h : n < m) (c : LLVM.Int wc) (x y : LLVM.Int n)
    (ext ext' : BitVec (m - n)) :
    GMIR.selectNonzero c x y ⊒
      LLVM.Int.trunc
        (GMIR.selectNonzero c (LLVM.Int.ext x m ext h) (LLVM.Int.ext y m ext' h))
        n false false h := by
  cases c with
  | poison => simp [GMIR.selectNonzero, LLVM.Int.trunc, Id.run, isRefinedBy]
  | val c =>
    simp only [GMIR.selectNonzero, Id.run]
    split
    · exact trunc_ext_self h x ext
    · exact trunc_ext_self h y ext'

/--
Prove the correctness of widening the condition of `g_select` with `g_zext`, at every width: the
zero-extended condition is nonzero exactly when the condition is.
-/
theorem select_widen_cond (n m w : Nat) (h : n < m) (c : LLVM.Int n) (x y : LLVM.Int w) :
    GMIR.selectNonzero c x y ⊒ GMIR.selectNonzero (LLVM.Int.zext c m false h) x y := by
  cases c with
  | poison => simp [GMIR.selectNonzero, LLVM.Int.zext, Id.run, isRefinedBy]
  | val c =>
    have hz : c.setWidth m = 0#m ↔ c = 0#n := by
      constructor
      · intro hz
        apply BitVec.eq_of_getElem_eq
        intro i hi
        have := congrArg (fun b => b[i]'(by omega)) hz
        simpa [BitVec.getElem_setWidth, hi] using this
      · rintro rfl
        simp
    simp [GMIR.selectNonzero, LLVM.Int.zext, Id.run, hz]

/--
Prove the correctness of combining `g_and (g_icmp p x y), 1` to `g_icmp p x y`, at every width: a
`g_icmp` wider than `i1` is its `i1` comparison zero-extended.
-/
theorem and_icmp_one (m : Nat) (h : 1 < m) (c : LLVM.Int 1) :
    LLVM.Int.zext c m false h ⊒
      LLVM.Int.and (LLVM.Int.zext c m false h) (LLVM.Int.constant m 1) := by
  veir_bv_normalize
  simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_and]
  grind

/-! ### Power-of-two division combines

The created shift amounts are the constants `k`, `w - 1` and `w - k`, and the created operations
have no flags. The `i64` divisor `2^k` (or `-2^k`) is the one that `slog2At? 64`/`ulog2At? 64`
recognizes.
-/

/-- Prove the correctness of `udiv_by_pow2_pattern` at `i64`, whatever the `exact` flag. -/
theorem udiv_by_pow2 (x : LLVM.Int 64) (k : BitVec 6) (exact : Bool) :
    LLVM.Int.udiv x (LLVM.Int.val (1#64 <<< k)) exact ⊒ LLVM.Int.lshr x (LLVM.Int.val (k.setWidth 64)) := by
  veir_bv_decide

/-- Prove the correctness of `sdiv_exact_by_pow2_pattern` at `i64` for a positive divisor. -/
theorem sdiv_exact_by_pow2_pos (x : LLVM.Int 64) (k : BitVec 6) (hk : k < 63) :
    LLVM.Int.sdiv x (LLVM.Int.val (1#64 <<< k)) true ⊒ LLVM.Int.ashr x (LLVM.Int.val (k.setWidth 64)) := by
  veir_bv_decide

/-- Prove the correctness of `sdiv_exact_by_pow2_pattern` at `i64` for a negative divisor,
    including `-2^63`. -/
theorem sdiv_exact_by_pow2_neg (x : LLVM.Int 64) (k : BitVec 6) :
    LLVM.Int.sdiv x (LLVM.Int.val (-(1#64 <<< k))) true ⊒
      LLVM.Int.sub (LLVM.Int.constant 64 0) (LLVM.Int.ashr x (LLVM.Int.val (k.setWidth 64))) := by
  veir_bv_decide

/-- Prove the correctness of `sdiv_by_pow2_pattern` at `i64` for a positive divisor. -/
theorem sdiv_by_pow2_pos (x : LLVM.Int 64) (k : BitVec 6) (hk0 : 0 < k) (hk : k < 63) :
    LLVM.Int.sdiv x (LLVM.Int.val (1#64 <<< k)) false ⊒
      LLVM.Int.ashr
        (LLVM.Int.add x
          (LLVM.Int.lshr (LLVM.Int.ashr x (LLVM.Int.constant 64 63))
            (LLVM.Int.val (64 - k.setWidth 64))))
        (LLVM.Int.val (k.setWidth 64)) := by
  veir_bv_decide

/-- Prove the correctness of `sdiv_by_pow2_pattern` at `i64` for a negative divisor, including
    `-2^63`. -/
theorem sdiv_by_pow2_neg (x : LLVM.Int 64) (k : BitVec 6) (hk0 : 0 < k) :
    LLVM.Int.sdiv x (LLVM.Int.val (-(1#64 <<< k))) false ⊒
      LLVM.Int.sub (LLVM.Int.constant 64 0)
        (LLVM.Int.ashr
          (LLVM.Int.add x
            (LLVM.Int.lshr (LLVM.Int.ashr x (LLVM.Int.constant 64 63))
              (LLVM.Int.val (64 - k.setWidth 64))))
          (LLVM.Int.val (k.setWidth 64))) := by
  veir_bv_decide

/-! ### Power-of-two word division combines

The word divisions read the low 32 bits of their `i64` divisor `c`, which is all the hypotheses
constrain. Each word operation that the combines create chooses its own high bits `e₁`, `e₂`, ...,
and the final choice is also one for the source division.
-/

/-- Prove the correctness of `sub_to_add` for `i64`: `nuw` is dropped, and `nsw` is dropped when
    `C` is the minimum signed value. -/
theorem sub_to_add (x : LLVM.Int 64) (c : BitVec 64) (nsw nuw : Bool) :
    LLVM.Int.sub x (LLVM.Int.val c) nsw nuw ⊒
      LLVM.Int.add x (LLVM.Int.val (-c)) (nsw && c != BitVec.intMin 64) false := by
  veir_bv_decide

/-- Prove the correctness of `sub_to_addw`: the negation of the low 32 bits of `C` is
    sign-extended, and the flags are those of `sub_to_add` at 32 bits. -/
theorem subw_to_addw (x : LLVM.Int 64) (c : BitVec 64) (nsw nuw : Bool) (e : BitVec 32) :
    ∃ e', GMIR.word (LLVM.Int.sub · · nsw nuw) x (LLVM.Int.val c) e' ⊒
      GMIR.word (LLVM.Int.add · · (nsw && c.setWidth 32 != BitVec.intMin 32) false) x
        (LLVM.Int.val ((-c.setWidth 32).signExtend 64)) e :=
  ⟨e, by unfold GMIR.word; veir_bv_decide⟩

/-- Prove the correctness of `udiv_by_pow2_pattern` for `g_udivw`, whatever the `exact` flag. -/
theorem udivw_by_pow2 (x : LLVM.Int 64) (c : BitVec 64) (k : BitVec 5)
    (hc : c.setWidth 32 = 1#32 <<< k) (exact : Bool) (e : BitVec 32) :
    ∃ e', GMIR.word (LLVM.Int.udiv · · exact) x (LLVM.Int.val c) e' ⊒
      GMIR.word (LLVM.Int.lshr · ·) x (LLVM.Int.val (k.setWidth 64)) e :=
  ⟨e, by unfold GMIR.word; veir_bv_decide⟩

/-- Prove the correctness of `sdiv_exact_by_pow2_pattern` for `g_sdivw` and a positive divisor. -/
theorem sdivw_exact_by_pow2_pos (x : LLVM.Int 64) (c : BitVec 64) (k : BitVec 5) (hk : k < 31)
    (hc : c.setWidth 32 = 1#32 <<< k) (e : BitVec 32) :
    ∃ e', GMIR.word (LLVM.Int.sdiv · · true) x (LLVM.Int.val c) e' ⊒
      GMIR.word (LLVM.Int.ashr · ·) x (LLVM.Int.val (k.setWidth 64)) e :=
  ⟨e, by unfold GMIR.word; veir_bv_decide⟩

/-- Prove the correctness of `sdiv_exact_by_pow2_pattern` for `g_sdivw` and a negative divisor,
    including `-2^31`. -/
theorem sdivw_exact_by_pow2_neg (x : LLVM.Int 64) (c : BitVec 64) (k : BitVec 5)
    (hc : c.setWidth 32 = -(1#32 <<< k)) (e₁ e₂ : BitVec 32) :
    ∃ e', GMIR.word (LLVM.Int.sdiv · · true) x (LLVM.Int.val c) e' ⊒
      GMIR.word (LLVM.Int.sub · ·) (LLVM.Int.constant 64 0)
        (GMIR.word (LLVM.Int.ashr · ·) x (LLVM.Int.val (k.setWidth 64)) e₁) e₂ :=
  ⟨e₂, by unfold GMIR.word; veir_bv_decide⟩

/-- Prove the correctness of `sdiv_by_pow2_pattern` for `g_sdivw` and a positive divisor. -/
theorem sdivw_by_pow2_pos (x : LLVM.Int 64) (c : BitVec 64) (k : BitVec 5) (hk0 : 0 < k)
    (hk : k < 31) (hc : c.setWidth 32 = 1#32 <<< k) (e₁ e₂ e₃ e₄ : BitVec 32) :
    ∃ e', GMIR.word (LLVM.Int.sdiv · · false) x (LLVM.Int.val c) e' ⊒
      (let sign := GMIR.word (LLVM.Int.ashr · ·) x (LLVM.Int.constant 64 31) e₁
       let bias := GMIR.word (LLVM.Int.lshr · ·) sign (LLVM.Int.val (32 - k.setWidth 64)) e₂
       let sum := GMIR.word (LLVM.Int.add · ·) x bias e₃
       GMIR.word (LLVM.Int.ashr · ·) sum (LLVM.Int.val (k.setWidth 64)) e₄) :=
  ⟨e₄, by unfold GMIR.word; veir_bv_decide⟩

/-- Prove the correctness of `sdiv_by_pow2_pattern` for `g_sdivw` and a negative divisor, including
    `-2^31`. -/
theorem sdivw_by_pow2_neg (x : LLVM.Int 64) (c : BitVec 64) (k : BitVec 5) (hk0 : 0 < k)
    (hc : c.setWidth 32 = -(1#32 <<< k)) (e₁ e₂ e₃ e₄ e₅ : BitVec 32) :
    ∃ e', GMIR.word (LLVM.Int.sdiv · · false) x (LLVM.Int.val c) e' ⊒
      (let sign := GMIR.word (LLVM.Int.ashr · ·) x (LLVM.Int.constant 64 31) e₁
       let bias := GMIR.word (LLVM.Int.lshr · ·) sign (LLVM.Int.val (32 - k.setWidth 64)) e₂
       let sum := GMIR.word (LLVM.Int.add · ·) x bias e₃
       let quotient := GMIR.word (LLVM.Int.ashr · ·) sum (LLVM.Int.val (k.setWidth 64)) e₄
       GMIR.word (LLVM.Int.sub · ·) (LLVM.Int.constant 64 0) quotient e₅) :=
  ⟨e₅, by unfold GMIR.word; veir_bv_decide⟩

/-! ### Constant folds -/

/--
Prove the correctness of combining `g_sext (g_trunc c)` to a constant, at every width and whatever
the flags of the `g_trunc`. With `m = w`, this is also the folding of `g_sext_inreg c, n`, which
`GMIR.interpretOp'` defines as the `sext` of the `trunc`.
-/
theorem sext_trunc_constant (w n m : Nat) (hn : n < w) (hm : n < m) (c : BitVec w)
    (nsw nuw : Bool) :
    LLVM.Int.sext (LLVM.Int.trunc (LLVM.Int.val c) n nsw nuw hn) m hm ⊒
      LLVM.Int.val ((c.setWidth n).signExtend m) := by
  veir_bv_normalize

/-- Prove the correctness of combining `g_zext (g_trunc c)` to a constant, at every width and
    whatever the flags. -/
theorem zext_trunc_constant (w n m : Nat) (hn : n < w) (hm : n < m) (c : BitVec w)
    (nsw nuw nneg : Bool) :
    LLVM.Int.zext (LLVM.Int.trunc (LLVM.Int.val c) n nsw nuw hn) m nneg hm ⊒
      LLVM.Int.val ((c.setWidth n).setWidth m) := by
  veir_bv_normalize

/-- Prove the correctness of combining `g_sext c` to a constant, at every width. -/
theorem sext_constant (n m : Nat) (hm : n < m) (c : BitVec n) :
    LLVM.Int.sext (LLVM.Int.val c) m hm ⊒ LLVM.Int.val (c.signExtend m) := by
  simp [LLVM.Int.sext, Id.run, isRefinedBy]

/-- Prove the correctness of combining `g_zext c` to a constant, at every width. -/
theorem zext_constant (n m : Nat) (hm : n < m) (c : BitVec n) (nneg : Bool) :
    LLVM.Int.zext (LLVM.Int.val c) m nneg hm ⊒ LLVM.Int.val (c.setWidth m) := by
  veir_bv_normalize

/-- Prove the correctness of folding `g_and`, `g_or` and `g_xor` of two constants. -/
theorem and_constant (w : Nat) (a b : BitVec w) :
    LLVM.Int.and (LLVM.Int.val a) (LLVM.Int.val b) ⊒ LLVM.Int.val (a &&& b) := by
  simp [LLVM.Int.and, Id.run, isRefinedBy]

theorem or_constant (w : Nat) (a b : BitVec w) (disjoint : Bool) :
    LLVM.Int.or (LLVM.Int.val a) (LLVM.Int.val b) disjoint ⊒ LLVM.Int.val (a ||| b) := by
  veir_bv_normalize

theorem xor_constant (w : Nat) (a b : BitVec w) :
    LLVM.Int.xor (LLVM.Int.val a) (LLVM.Int.val b) ⊒ LLVM.Int.val (a ^^^ b) := by
  simp [LLVM.Int.xor, Id.run, isRefinedBy]

end Veir.Data.LLVM

end
