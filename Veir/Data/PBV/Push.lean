module

public import Veir.Data.PBV.Lemmas
public import Veir.Data.PBV.Mask
public meta import Veir.Meta.Tactic.PBVDecide.PBVPushSimp

/-! # Rewriting a parametric expression into a concrete, single-width one.

`pbv_lift` lemmas introduce a `setWidth o` at the root of `BitVec` expressions,
the `pbv_push` lemmas push it down towards the leaves, converting `setWidth`s
of a width variable into masks of every operation.
See `Veir.Data.PBV` for more details.

## Supported `BitVec` operations

An operation is supported if there is a lemma pushing `setWidth o` through it
(here, or registered from core in `Veir.Meta.Tactic.PBVDecide.Main`).
Operations without a push theorem (`—`) are abstracted as opaque variables by `bv_decide`.

| Operation                       | `BitVec` definition          | Push theorem                       |
|---------------------------------|------------------------------|------------------------------------|
| Equality (`=`)                  | `Eq`                         | `eq_setWidth`                      |
| Inequality (`≠`)                | `Ne`                         | `ne_setWidth`                      |
| Bool equality (`==`)            | `BEq`                        | `beq_setWidth`                     |
| Bool inequality (`!=`)          | `BNe`                        | `bne_setWidth`                     |
| `<`                             | `BitVec.lt`                  | `lt_setWidth`                      |
| `≤`                             | `BitVec.le`                  | `le_setWidth`                      |
| Unsigned `<`                    | `BitVec.ult`                 | `ult_setWidth`                     |
| Unsigned `≤`                    | `BitVec.ule`                 | `ule_setWidth`                     |
| Signed `<`                      | `BitVec.slt`                 | `slt_setWidth`                     |
| Signed `≤`                      | `BitVec.sle`                 | `sle_setWidth`                     |
| Conditional (bif/cond)          | `cond`                       | `setWidth_bif`                     |
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
| Cast                            | `BitVec.cast`                | `BitVec.setWidth_cast`             |
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
| Signed div                      | `BitVec.sdiv`                | `sdiv_eq_bif_udiv`                 |
| Signed rem                      | `BitVec.srem`                | `srem_eq_bif_umod`                 |
| Signed mod                      | `BitVec.smod`                | `smod_eq_bif_umod`                 |
| SMT unsigned div                | `BitVec.smtUDiv`             | `setWidth_smtUDiv`                 |
| SMT signed div                  | `BitVec.smtSDiv`             | `smtSDiv_eq_bif_smtUDiv`           |
| And (`&&&`)                     | `BitVec.and`                 | `setWidth_and`                     |
| Or (`\|\|\|`)                   | `BitVec.or`                  | `setWidth_or`                      |
| Xor (`^^^`)                     | `BitVec.xor`                 | `setWidth_xor`                     |
| Not (`~~~`)                     | `BitVec.not`                 | `setWidth_not`                     |
| Shift left by `Nat` (`<<<`)     | `BitVec.shiftLeft`           | `setWidth_shiftLeft'`              |
| Shift left by `BitVec` (`<<<`)  | `BitVec.shiftLeft`           | `setWidth_shiftLeft`               |
| Shift right by `Nat` (`>>>`)    | `BitVec.ushiftRight`         | `setWidth_ushiftRight'`            |
| Shift right by `BitVec` (`>>>`) | `BitVec.ushiftRight`         | `setWidth_ushiftRight`             |
| Arith shift right by `Nat`      | `BitVec.sshiftRight`         | `setWidth_sshiftRight`             |
| Arith shift right by `BitVec`   | `BitVec.sshiftRight'`        | `setWidth_sshiftRight'`            |
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
  BitVec.ofNat_eq_ofNat BitVec.setWidth_cast BitVec.shiftLeftZeroExtend_eq

attribute [pbv_push low] BitVec.setWidth_eq

/-- Introducing `setWidth o` at the root.
`o` must be the first binder, since it should be bound to the concrete width
being used in the proof.
-/
@[pbv_lift]
theorem eq_setWidth (o : Nat) {w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a = b) = (a.setWidth o = b.setWidth o) := by
  grind[BitVec.setWidth_inj]

@[pbv_lift]
theorem ne_setWidth (o : Nat) {w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a ≠ b) = (a.setWidth o ≠ b.setWidth o) := by
  grind[BitVec.setWidth_inj]

@[pbv_lift]
theorem beq_setWidth (o : Nat) {w : Nat} (h : w ≤ o) (a b : BitVec w) :
  (a == b) = (a.setWidth o == b.setWidth o) := by
  grind [BitVec.setWidth_inj]

@[pbv_lift]
theorem bne_setWidth (o : Nat) {w : Nat} (h : w ≤ o) (a b : BitVec w) :
  (a != b) = (a.setWidth o != b.setWidth o) := by
  grind [BitVec.setWidth_inj]

@[pbv_lift]
theorem lt_setWidth (o : Nat) {w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a < b) = (a.setWidth o < b.setWidth o) := by
  simp only [BitVec.lt_def, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le h)]

@[pbv_lift]
theorem le_setWidth (o : Nat) {w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a ≤ b) = (a.setWidth o ≤ b.setWidth o) := by
  simp only [BitVec.le_def, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le h)]

@[pbv_lift]
theorem ult_setWidth (o : Nat) {w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a.ult b) = (a.setWidth o).ult (b.setWidth o) := by
  simp only [BitVec.ult_eq_decide, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le h)]

@[pbv_lift]
theorem ule_setWidth (o : Nat) {w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a.ule b) = (a.setWidth o).ule (b.setWidth o) := by
  simp only [BitVec.ule_eq_decide, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le h)]

@[pbv_lift]
theorem slt_setWidth (o : Nat) {w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a.slt b) = (a.msb != b.msb).xor ((a.setWidth o).ult (b.setWidth o)) := by
  rw [BitVec.slt_eq_ult, ← ult_setWidth o h]

@[pbv_lift]
theorem sle_setWidth (o : Nat) {w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a.sle b) = (a.msb != b.msb).xor ((a.setWidth o).ule (b.setWidth o)) := by
  rw [BitVec.sle_eq_ule, ← ule_setWidth o h]

@[pbv_push]
theorem setWidth_bif {c : Bool} {o w : Nat} (a b : BitVec w) :
    (bif c then a else b).setWidth o
      = bif c then (a.setWidth o) else (b.setWidth o) := by grind

/-! ## Pushing `setWidth o` towards the leaves — leaves and width changes -/

@[pbv_push low]
theorem setWidth_setWidth {o w u : Nat} (h : w ≤ o) (a : BitVec u) :
    (a.setWidth w).setWidth o = a.setWidth o &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_mod_pow_of_le h]

/-! ## Push `setWidth` into arithmetic -/

@[pbv_push]
theorem setWidth_add {o w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a + b).setWidth o = (a.setWidth o + b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_add, BitVec.toNat_setWidth_of_le h, BitVec.toNat_setWidth_of_le h,
    Nat.mod_mod_pow_of_le h, BitVec.toNat_add]

@[pbv_push]
theorem setWidth_mul {o w : Nat} (h : w ≤ o) :
    ∀ (a b : BitVec w),
      (a * b).setWidth o = (a.setWidth o * b.setWidth o) &&& maskOfWidth o w := by
  intro a b
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth_of_le h, BitVec.toNat_setWidth_of_le h,
    Nat.mod_mod_pow_of_le h, BitVec.toNat_mul]

@[pbv_push]
theorem setWidth_neg {o w : Nat} (h : w ≤ o) (b : BitVec w) :
    (- b).setWidth o = (- b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_neg, BitVec.toNat_neg, Nat.mod_mod_pow_of_le h, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (x := b) h), Nat.two_pow_sub_mod_of_le h (by grind)]

@[pbv_push]
theorem setWidth_sub {o w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a - b).setWidth o = (a.setWidth o - b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_setWidth_of_le h,
    BitVec.toNat_setWidth_of_le h, Nat.mod_mod_pow_of_le h, Nat.add_mod,
    Nat.two_pow_sub_mod_of_le h (Nat.le_of_lt b.isLt), ← Nat.add_mod]

@[pbv_push]
theorem setWidth_udiv {o w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a / b).setWidth o = (a.setWidth o / b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.toNat_udiv, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le h),
    Nat.div_mod_eq_div a.isLt]

@[pbv_push]
theorem setWidth_smtUDiv {o w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a.smtUDiv b).setWidth o =
      bif (b.setWidth o == (0#w).setWidth o)
      then maskOfWidth o w
      else (a / b).setWidth o := by
  rw [BitVec.smtUDiv_eq, ← beq_setWidth o h, maskOfWidth_eq_allOnes h, ← setWidth_bif]
  simp only [cond_eq_ite, beq_iff_eq]

@[pbv_push]
theorem setWidth_umod {o w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a % b).setWidth o = (a.setWidth o % b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.toNat_umod, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le h),
    Nat.mod_mod_eq_mod_of_lt_right a.isLt]

@[pbv_push]
theorem sdiv_eq_bif_udiv {w : Nat} (a b : BitVec w) :
    a.sdiv b =
      let div := (bif a.msb then -a else a) / (bif b.msb then -b else b)
      bif a.msb ^^ b.msb then -div else div := by
  rw [BitVec.sdiv_eq]
  cases a.msb <;> cases b.msb <;> rfl

@[pbv_push]
theorem smtSDiv_eq_bif_smtUDiv {w : Nat} (a b : BitVec w) :
    a.smtSDiv b =
      let div := (bif a.msb then -a else a).smtUDiv (bif b.msb then -b else b)
      bif a.msb ^^ b.msb then -div else div := by
  rw [BitVec.smtSDiv_eq]
  cases a.msb <;> cases b.msb <;> rfl

@[pbv_push]
theorem srem_eq_bif_umod {w : Nat} (a b : BitVec w) :
    a.srem b =
      let rem := (bif a.msb then -a else a) % (bif b.msb then -b else b)
      bif a.msb then -rem else rem := by
  rw [BitVec.srem_eq]
  cases a.msb <;> cases b.msb <;> rfl

@[pbv_push_bound]
theorem smod_eq_bif_umod (o : Nat) {w : Nat} (h : w ≤ o) (a b : BitVec w) :
    a.smod b =
      let rem := (bif a.msb then -a else a) % (bif b.msb then -b else b)
      bif a.msb ^^ b.msb then
        bif (rem.setWidth o == (0#w).setWidth o) then rem else (bif b.msb then b + rem else b - rem)
      else bif a.msb && b.msb then -rem else rem := by
  simp only [BitVec.smod_eq, ← beq_setWidth o h]
  cases a.msb <;> cases b.msb <;> simp [BitVec.add_comm]


/-- ## Push `setWidth` into `BitVec` ops -/

@[pbv_push]
theorem setWidth_shiftLeft {o w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a <<< b).setWidth o = (a.setWidth o <<< b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.shiftLeft_eq', BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (x := b) h),
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_mul_mod, Nat.mod_mod_pow_of_le h]

@[pbv_push]
theorem setWidth_shiftLeft' {o w : Nat} (h : w ≤ o) (a : BitVec w) (b : Nat) :
    (a <<< b).setWidth o = (a.setWidth o <<< BitVec.ofNatClamp o b) &&& maskOfWidth o w := by
  have : w < 2^o := by grind[Nat.lt_pow_self]
  rw [BitVec.shiftLeft_eq_shiftLeft_ofNatClamp this]
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq, Nat.mod_mul_mod, Nat.mod_mod_pow_of_le h,
    BitVec.shiftLeft_eq', BitVec.toNat_ofNatClamp]

@[pbv_push]
theorem setWidth_ushiftRight {o w : Nat} (h : w ≤ o) (a b : BitVec w) :
    (a >>> b).setWidth o = (a.setWidth o >>> b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.ushiftRight_eq', BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le h),
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_mod_eq_div a.isLt]

@[pbv_push]
theorem setWidth_ushiftRight' {o w : Nat} (h : w ≤ o) (a : BitVec w) (b : Nat) :
    (a >>> b).setWidth o = (a.setWidth o >>> BitVec.ofNatClamp o b) &&& maskOfWidth o w := by
  have : w < 2^o := by grind[Nat.lt_pow_self]
  rw [BitVec.ushiftRight_eq_ushiftRight_ofNatClamp this]
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le h), BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNatClamp, BitVec.ushiftRight_eq']
  rw [Nat.mod_eq_of_lt (by grind[Nat.shiftRight_le])]

@[pbv_push]
theorem setWidth_sshiftRight' {o w v: Nat} (hw : w ≤ o) (hv : v ≤ o) (a : BitVec w) (b : BitVec v) :
    (a.sshiftRight' b).setWidth o =
      bif a.msb
      then (~~~(((~~~a).setWidth o) >>> (b.setWidth o))) &&& maskOfWidth o w
      else (a.setWidth o) >>> (b.setWidth o) &&& maskOfWidth o w := by
  by_cases amsb : a.msb
  · simp [amsb, BitVec.sshiftRight_eq_of_msb_true]
    refine setWidth_eq_and_maskOfWidth hw ?_
    simp only [BitVec.toNat_not, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow]
    have := Nat.div_le_self (2^w - 1 - a.toNat) (2^b.toNat)
    have := Nat.pow_le_pow_right (n := 2) (by decide) hw
    rw [Nat.mod_eq_of_lt (a := 2^w - 1 - a.toNat) (by lia), Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le hv),
      Nat.sub_sub, Nat.two_pow_sub_mod_of_le hw (by lia), Nat.mod_eq_of_lt (by lia), ← Nat.sub_sub]
  · simp only [BitVec.sshiftRight_eq', BitVec.sshiftRight_eq_of_msb_false (by simp [amsb] : a.msb = false), amsb,
    BitVec.ushiftRight_eq', BitVec.toNat_setWidth, cond_eq_ite, Bool.false_eq_true, ↓reduceIte]
    rw [setWidth_ushiftRight' hw, ← BitVec.ushiftRight_eq_ushiftRight_ofNatClamp (by exact Nat.lt_pow_self (a := 2) (by decide)),
        Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le hv)]

@[pbv_push]
theorem setWidth_sshiftRight {o w : Nat} (h : w ≤ o) (a : BitVec w) (b : Nat) :
    (a.sshiftRight b).setWidth o =
      bif a.msb
      then ~~~(((~~~a).setWidth o) >>> (BitVec.ofNatClamp o b)) &&& maskOfWidth o w
      else (a.setWidth o) >>> (BitVec.ofNatClamp o b) &&& maskOfWidth o w := by
  have : w < 2^o := by lia [Nat.lt_two_pow_self]
  rw [BitVec.sshiftRight_eq_sshiftRight'_ofNatClamp this, setWidth_sshiftRight' h (by exact Nat.le_refl o)]
  simp [BitVec.setWidth_eq, BitVec.ushiftRight_eq', cond_eq_ite]

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
theorem setWidth_append {o w v : Nat} (h : w ≤ o) (a : BitVec v) (b : BitVec w) (hvw : v + w ≤ o) :
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
theorem setWidth_extractLsb' {o w len start : Nat} (a : BitVec w) (hlen : len ≤ o):
    (a.extractLsb' start len).setWidth o
      = (a >>> start).setWidth o &&& maskOfWidth o len := by
  by_cases hs : start ≤ w
  · refine setWidth_eq_and_maskOfWidth (by lia) ?_
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.mod_mod_pow_of_le (x := 2) hlen,
    BitVec.extractLsb'_toNat]
  · have : a.toNat < 2 ^ start := by apply BitVec.toNat_lt_twoPow_of_le (by omega)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_zero (hn := this),
      Nat.zero_mod, BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.zero_and]

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

/-- Convert a `NatClamp` of a variable which corresponds to a mask into a `cpop` of the mask. -/
@[pbv_push]
theorem ofNatClamp_eq_cpop_of_maskOfWidth {o w : Nat} {m : BitVec o} (h : w ≤ o) (hm : m = maskOfWidth o w) :
    BitVec.ofNatClamp o w = BitVec.cpop m := by
  rw [BitVec.ofNatClamp_eq_ofNat]
  exact ofNat_eq_cpop_of_maskOfWidth h hm
  by_cases hwo : w = o
  · subst hwo
    exact Nat.lt_pow_self (by grind)
  · apply Nat.lt_trans (Nat.lt_pow_self (a := 2) (by decide)) ?_
    exact Nat.pow_lt_pow_right (a := 2) (by decide) (by lia)
