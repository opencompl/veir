module

public import Veir.Data.PBV.Lemmas
public import Veir.Data.PBV.Mask
public meta import Veir.Meta.Tactic.PBVDecide.PBVPushSimp

/-! # Rewriting a parametric expression into a concrete, single-width one.

`eq_iff` introduces a `setWidth o` at the root of the goal, and the remaining
lemmas push it down towards the leaves, masking the result of every
width-sensitive operation. See `Veir.Data.PBV` for more details.

## Supported `BitVec` operations

An operation is supported if there is a lemma pushing `setWidth o` through it
(here, or registered from core in `Veir.Meta.Tactic.PBVDecide.Main`).
Operations without a push theorem (`—`) are abstracted as opaque variables by `bv_decide`.

| Operation                       | `BitVec` definition          | Push theorem                       |
|---------------------------------|------------------------------|------------------------------------|
| Equality (`=`)                  | `Eq`                         | `eq_iff`                           |
| Bool equality (`==`)            | `BEq`                        | —                                  |
| Unsigned `<`                    | `BitVec.ult`                 | —                                  |
| Unsigned `≤`                    | `BitVec.ule`                 | —                                  |
| Signed `<`                      | `BitVec.slt`                 | —                                  |
| Signed `≤`                      | `BitVec.sle`                 | —                                  |
| Literal (`n#w`)                 | `BitVec.ofNat`               | `setWidth_ofNat`                   |
| Zero (`0#w`)                    | `BitVec.zero`                | `BitVec.setWidth_zero`             |
| All ones                        | `BitVec.allOnes`             | —                                  |
| Signed min                      | `BitVec.intMin`              | —                                  |
| Signed max                      | `BitVec.intMax`              | —                                  |
| Power of two                    | `BitVec.twoPow`              | —                                  |
| From `Int`                      | `BitVec.ofInt`               | —                                  |
| From `Bool`                     | `BitVec.ofBool`              | —                                  |
| Fill                            | `BitVec.fill`                | —                                  |
| Set width                       | `BitVec.setWidth`            | `setWidth_setWidth`                |
| Zero extend                     | `BitVec.zeroExtend`          | `setWidth_setWidth`                |
| Truncate                        | `BitVec.truncate`            | `setWidth_setWidth`                |
| Sign extend                     | `BitVec.signExtend`          | `setWidth_signExtend`              |
| Append (`++`)                   | `BitVec.append`              | `setWidth_append`                  |
| Extract (SMT-Lib)               | `BitVec.extractLsb`          | —                                  |
| Extract                         | `BitVec.extractLsb'`         | `setWidth_extractLsb'`             |
| Replicate                       | `BitVec.replicate`           | —                                  |
| Concat bit                      | `BitVec.concat`              | —                                  |
| Cons bit                        | `BitVec.cons`                | —                                  |
| Shift left, extend              | `BitVec.shiftLeftZeroExtend` | `BitVec.shiftLeftZeroExtend_eq`    |
| Add (`+`)                       | `BitVec.add`                 | `setWidth_add`                     |
| Sub (`-`)                       | `BitVec.sub`                 | `setWidth_sub`                     |
| Neg (`-`)                       | `BitVec.neg`                 | `setWidth_neg`                     |
| Mul (`*`)                       | `BitVec.mul`                 | `setWidth_mul`                     |
| Unsigned div (`/`)              | `BitVec.udiv`                | `setWidth_udiv`                    |
| Unsigned mod (`%`)              | `BitVec.umod`                | `setWidth_umod`                    |
| Pow (`^`)                       | `BitVec.pow`                 | —                                  |
| Abs                             | `BitVec.abs`                 | —                                  |
| Signed div                      | `BitVec.sdiv`                | —                                  |
| Signed rem                      | `BitVec.srem`                | —                                  |
| Signed mod                      | `BitVec.smod`                | —                                  |
| SMT unsigned div                | `BitVec.smtUDiv`             | —                                  |
| SMT signed div                  | `BitVec.smtSDiv`             | —                                  |
| And (`&&&`)                     | `BitVec.and`                 | `setWidth_and`                     |
| Or (`\|\|\|`)                   | `BitVec.or`                  | `setWidth_or`                      |
| Xor (`^^^`)                     | `BitVec.xor`                 | `setWidth_xor`                     |
| Not (`~~~`)                     | `BitVec.not`                 | `setWidth_not`                     |
| Shift left by `Nat` (`<<<`)     | `BitVec.shiftLeft`           | `setWidth_shiftLeft'`              |
| Shift left by `BitVec` (`<<<`)  | `BitVec.shiftLeft`           | `setWidth_shiftLeft`               |
| Shift right by `Nat` (`>>>`)    | `BitVec.ushiftRight`         | `setWidth_ushiftRight'`            |
| Shift right by `BitVec` (`>>>`) | `BitVec.ushiftRight`         | `setWidth_ushiftRight`             |
| Arith shift right by `Nat`      | `BitVec.sshiftRight`         | —                                  |
| Arith shift right by `BitVec`   | `BitVec.sshiftRight'`        | —                                  |
| Rotate left                     | `BitVec.rotateLeft`          | —                                  |
| Rotate right                    | `BitVec.rotateRight`         | —                                  |
| MSB                             | `BitVec.msb`                 | `msb_eq_and_signBitOfMask_ne_zero` |
| Bit, from LSB                   | `BitVec.getLsbD`             | —                                  |
| Bit, from MSB                   | `BitVec.getMsbD`             | —                                  |
| Reverse                         | `BitVec.reverse`             | —                                  |
| Popcount                        | `BitVec.cpop`                | —                                  |
| Leading zeros                   | `BitVec.clz`                 | —                                  |
| Trailing zeros                  | `BitVec.ctz`                 | —                                  |
| Unsigned add overflow           | `BitVec.uaddOverflow`        | —                                  |
| Signed add overflow             | `BitVec.saddOverflow`        | —                                  |
| Unsigned sub overflow           | `BitVec.usubOverflow`        | —                                  |
| Signed sub overflow             | `BitVec.ssubOverflow`        | —                                  |
| Neg overflow                    | `BitVec.negOverflow`         | —                                  |
| Unsigned mul overflow           | `BitVec.umulOverflow`        | —                                  |
| Signed mul overflow             | `BitVec.smulOverflow`        | —                                  |
| Signed div overflow             | `BitVec.sdivOverflow`        | —                                  |
-/

namespace Veir.Data.PBV

public section

attribute [pbv_push] signBitOfMask_eq maskOfWidth_zero BitVec.setWidth_zero
  BitVec.ofNat_eq_ofNat BitVec.shiftLeftZeroExtend_eq

attribute [pbv_push low] BitVec.setWidth_eq

/-- Introducing `setWidth o` at the root.
`o` must be the first binder, since it should be bound to the concrete width
being used in the proof..
 -/
@[pbv_lift]
theorem eq_iff (o : Nat) {w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a = b) = (a.setWidth o = b.setWidth o) := by
  apply propext
  exact ⟨fun hab => hab ▸ rfl, fun hab => BitVec.setWidth_inj h hab⟩

/-! ## Pushing `setWidth o` towards the leaves — leaves and width changes -/

@[pbv_push low]
theorem setWidth_setWidth {o w u : Nat} (h : w ≤ o) (a : BitVec u) :
    (a.setWidth w).setWidth o = a.setWidth o &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_mod_pow_of_le h]

/-! ## Push `setWidth` into arithmetic -/

@[pbv_push]
theorem setWidth_add {o w : Nat} (h : w ≤ o) (a b : BitVec w):
    (a + b).setWidth o = (a.setWidth o + b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_add, BitVec.toNat_setWidth_of_le h, BitVec.toNat_setWidth_of_le h,
    Nat.mod_mod_pow_of_le h, BitVec.toNat_add]

@[pbv_push]
theorem setWidth_mul {w o : Nat} (h : w ≤ o) :
    ∀ (a b : BitVec w),
      (a * b).setWidth o = (a.setWidth o * b.setWidth o) &&& maskOfWidth o w := by
  intro a b
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth_of_le h, BitVec.toNat_setWidth_of_le h,
    Nat.mod_mod_pow_of_le h, BitVec.toNat_mul]

@[pbv_push]
theorem setWidth_neg {w o : Nat} (h : w ≤ o) (b : BitVec w) :
    (- b).setWidth o = (- b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_neg, BitVec.toNat_neg, Nat.mod_mod_pow_of_le h, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (x := b) h), Nat.two_pow_sub_mod_of_le h (by grind)]

@[pbv_push]
theorem setWidth_sub {w o : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a - b).setWidth o = (a.setWidth o - b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_setWidth_of_le h,
    BitVec.toNat_setWidth_of_le h, Nat.mod_mod_pow_of_le h, Nat.add_mod,
    Nat.two_pow_sub_mod_of_le h (Nat.le_of_lt b.isLt), ← Nat.add_mod]

@[pbv_push]
theorem setWidth_udiv {w o : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a / b).setWidth o = (a.setWidth o / b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.toNat_udiv, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le h),
    Nat.div_mod_eq_div a.isLt]

@[pbv_push]
theorem setWidth_umod {w o : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a % b).setWidth o = (a.setWidth o % b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.toNat_umod, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le h),
    Nat.mod_mod_eq_mod_of_lt_right a.isLt]

/-- ## Push `setWidth` into `BitVec` ops -/

@[pbv_push]
theorem setWidth_shiftLeft {w o : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a <<< b).setWidth o = (a.setWidth o <<< b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.shiftLeft_eq', BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (x := b) h),
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_mul_mod, Nat.mod_mod_pow_of_le h]
@[pbv_push]
theorem setWidth_shiftLeft' {w o : Nat} (h : w ≤ o) (a : BitVec w) (b : Nat) :
    (a <<< b).setWidth o = (a.setWidth o <<< b) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq, Nat.mod_mul_mod, Nat.mod_mod_pow_of_le h]

@[pbv_push]
theorem setWidth_ushiftRight {w o : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a >>> b).setWidth o = (a.setWidth o >>> b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.ushiftRight_eq', BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le h),
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_mod_eq_div a.isLt]

@[pbv_push]
theorem setWidth_ushiftRight' {w o : Nat} (h : w ≤ o) (a : BitVec w) (b : Nat) :
    (a >>> b).setWidth o = (a.setWidth o >>> b) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le h),
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_mod_eq_div a.isLt]

/-- Sign extension fills above the source width `v` with the sign bit,
and then masks to the target width. -/
@[pbv_push]
theorem setWidth_signExtend {o t v : Nat} (hvo : v ≤ o) (a : BitVec v) :
    (a.signExtend t).setWidth o
      = ((a.setWidth o) ||| (cond a.msb (~~~(maskOfWidth o v)) 0#o)) &&& maskOfWidth o t := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_setWidth, getLsbD_maskOfWidth]
  by_cases hiv : i < v
  · -- Below the source width: the sign fill is masked out.
    have hio : i < o := by lia
    have hmask : (maskOfWidth o v)[i] = true := by
      rw [getElem_maskOfWidth i hio]; simp [hiv]
    cases hmsb : a.msb <;> grind
  · -- At or above the source width: `a` has no bit here, so the result is the sign bit.
    rw [BitVec.getLsbD_of_ge a i (by lia)]
    cases hmsb : a.msb <;>
      simp [hiv, getLsbD_maskOfWidth, Bool.and_comm]

/-- `a ++ b` shifts `a` up by the width of `b` and combines them with `|||`. -/
@[pbv_push]
theorem setWidth_append {o w v : Nat} (h : w ≤ o) (a : BitVec v) (b : BitVec w) (hvw: v + w ≤ o) :
    (a ++ b).setWidth o
      = ((a.setWidth o) <<< BitVec.cpop (maskOfWidth o w)) ||| b.setWidth o := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_setWidth_of_le, hvw, h,
      BitVec.toNat_append, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft]
  congr 1
  rw [toNat_cpop_maskOfWidth_eq_width h, BitVec.toNat_setWidth_of_le (by lia), Nat.mod_eq_of_lt]
  have a_lt_vw := Nat.mul_lt_mul_of_lt_of_le a.isLt (Nat.le_refl _) (Nat.two_pow_pos w)
  grind [Nat.pow_le_pow_right (n := 2) (by lia) hvw]

/-- `setWidth` of a constant is the constant anded with the mask. -/
@[pbv_push]
theorem setWidth_ofNat {o w n : Nat} (h : w ≤ o) :
    BitVec.setWidth o (BitVec.ofNat w n) = (BitVec.ofNat o n) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.toNat_ofNat, Nat.mod_mod_pow_of_le h]

/-- ExtractLsb is converted to shift and mask. -/
@[pbv_push]
theorem setWidth_extractLsb' {w o len start : Nat} (a : BitVec w) (h: w ≤ o) (hlen : len ≤ o):
    (a.extractLsb' start len).setWidth o
      = ((a.setWidth o) >>> start) &&& maskOfWidth o len := by
  by_cases hs : start ≤ w
  · refine setWidth_eq_and_maskOfWidth (by lia) ?_
    simp [Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le h)]
  · have : a.toNat < 2 ^ start := by
      have := a.isLt
      have : start > w := by lia
      grind [Nat.pow_lt_pow_right (a:=2) (by decide) this]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_zero (hn := this),
      Nat.zero_mod, BitVec.toNat_and, BitVec.toNat_ushiftRight,
      Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le h), Nat.zero_and]

/-! ## Push `setWidth` into bitwise ops -/

@[pbv_push]
theorem setWidth_and {o w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a &&& b).setWidth o = (a.setWidth o &&& b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, Nat.and_mod_two_pow, Nat.mod_mod_pow_of_le h,
    BitVec.toNat_mod_cancel]

@[pbv_push]
theorem setWidth_or {o w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a ||| b).setWidth o = (a.setWidth o ||| b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.toNat_or, BitVec.toNat_setWidth, Nat.or_mod_two_pow, Nat.mod_mod_pow_of_le h,
    BitVec.toNat_mod_cancel]

@[pbv_push]
theorem setWidth_xor {o w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a ^^^ b).setWidth o = (a.setWidth o ^^^ b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.toNat_xor, BitVec.toNat_setWidth, Nat.xor_mod_two_pow, Nat.mod_mod_pow_of_le h,
    BitVec.toNat_mod_cancel]

@[pbv_push]
theorem setWidth_not {o w : Nat} (h : w ≤ o) (a : BitVec w) :
    (~~~a).setWidth o = (~~~(a.setWidth o)) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.toNat_not, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le h), Nat.sub_sub]
  rw [Nat.two_pow_sub_mod_of_le h (by grind), Nat.mod_eq_of_lt (by grind)]

/-! ### Other ops in terms of `maskOfWidth` -/

/-- `a.msb` can be implemented by masking the sign bit,
which are definitions the bitblaster can see. -/
@[pbv_push_bound]
theorem msb_eq_and_signBitOfMask_ne_zero (o : Nat) {w : Nat} (h : w ≤ o) (a : BitVec w) :
    a.msb = (((a.setWidth o) &&& signBitOfMask (maskOfWidth o w)) != 0#o) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · -- `BitVec 0` has no bits, so both sides are `false`.
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_of_ge _ _ (by lia)]
    simp
  · rw [signBitOfMask_maskOfWidth_eq_twoPow_of_pos h hw,
      BitVec.and_twoPow, BitVec.getLsbD_setWidth,
      BitVec.msb_eq_getLsbD_last]
    have hlt : w - 1 < o := by lia
    simp only [hlt, decide_true, Bool.true_and]
    cases a.getLsbD (w - 1)
    · simp
    · simp [BitVec.twoPow_ne_zero hlt]

/-- Push a variable `Nat` which corresponds to a mask into a `cpop` of the mask. -/
@[pbv_push]
theorem ofNat_eq_cpop_of_maskOfWidth {o w : Nat} {m : BitVec o} (h : w ≤ o) (hm : m = maskOfWidth o w) :
    BitVec.ofNat o w = BitVec.cpop m := by
  symm
  exact cpop_eq_width_of_maskOfWidth h hm
