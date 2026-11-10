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
(defined here, or a core lemma registered here with `attribute [pbv_push]`).
The table lists every user-facing `BitVec` operation in core.
Operations without a push theorem (`—`) are abstracted as opaque variables by `bv_decide`.

| Operation                       | `BitVec` definition          | Push theorem                             |
|---------------------------------|------------------------------|------------------------------------------|
| Equality (`=`)                  | `Eq`                         | `eq_setWidth`                            |
| Inequality (`≠`)                | `Ne`                         | `ne_setWidth`                            |
| Bool equality (`==`)            | `BEq`                        | `beq_setWidth`                           |
| Bool inequality (`!=`)          | `BNe`                        | `bne_setWidth`                           |
| `<`                             | `BitVec.lt`                  | `lt_setWidth`                            |
| `≤`                             | `BitVec.le`                  | `le_setWidth`                            |
| Unsigned `<`                    | `BitVec.ult`                 | `ult_setWidth`                           |
| Unsigned `≤`                    | `BitVec.ule`                 | `ule_setWidth`                           |
| Signed `<`                      | `BitVec.slt`                 | `slt_setWidth`                           |
| Signed `≤`                      | `BitVec.sle`                 | `sle_setWidth`                           |
| Conditional (bif/cond)          | `cond`                       | `setWidth_bif`                           |
| Conditional (if/ite)            | `ite`                        | `setWidth_ite`                           |
| Literal (`n#w`)                 | `BitVec.ofNat`               | `setWidth_ofNat`                         |
| Literal, with bound proof       | `BitVec.ofNatLT`             | —                                        |
| Literal, saturating             | `BitVec.ofNatClamp`          | `ofNatClamp_eq_cpop_of_maskOfWidth` †    |
| Zero (`0#w`)                    | `BitVec.zero`                | `BitVec.setWidth_zero`                   |
| Empty (`BitVec 0`)              | `BitVec.nil`                 | —                                        |
| All ones                        | `BitVec.allOnes`             | `setWidth_allOnes`                       |
| Signed min                      | `BitVec.intMin`              | `setWidth_ofIntMin`                      |
| Signed max                      | `BitVec.intMax`              | `setWidth_ofIntMax`                      |
| Power of two                    | `BitVec.twoPow`              | `setWidth_twoPow`                        |
| From `Int`                      | `BitVec.ofInt`               | `setWidth_ofInt`                         |
| From `Bool`                     | `BitVec.ofBool`              | —                                        |
| From `List Bool` (big-endian)   | `BitVec.ofBoolListBE`        | —                                        |
| From `List Bool` (little-end.)  | `BitVec.ofBoolListLE`        | —                                        |
| Fill                            | `BitVec.fill`                | `BitVec.fill_eq`                         |
| To `Nat`                        | `BitVec.toNat`               | `BitVec.ofNat_toNat` †                   |
| To `Int`                        | `BitVec.toInt`               | `BitVec.ofInt_toInt` †                   |
| Set width                       | `BitVec.setWidth`            | `setWidth_setWidth`                      |
| Set width, with bound proof     | `BitVec.setWidth'`           | —                                        |
| Zero extend                     | `BitVec.zeroExtend`          | `setWidth_setWidth`                      |
| Truncate                        | `BitVec.truncate`            | `setWidth_setWidth`                      |
| Sign extend                     | `BitVec.signExtend`          | `setWidth_signExtend`                    |
| Cast                            | `BitVec.cast`                | `BitVec.setWidth_cast`                   |
| Append (`++`)                   | `BitVec.append`              | `setWidth_append`                        |
| Extract (SMT-Lib)               | `BitVec.extractLsb`          | unfolded to `extractLsb'`                |
| Extract                         | `BitVec.extractLsb'`         | `setWidth_extractLsb'`                   |
| Replicate                       | `BitVec.replicate`           | —                                        |
| Concat bit                      | `BitVec.concat`              | `setWidth_concat`                        |
| Cons bit                        | `BitVec.cons`                | `setWidth_cons`                          |
| Shift in bit from LSB           | `BitVec.shiftConcat`         | —                                        |
| Flatten list                    | `BitVec.flattenList`         | —                                        |
| Shift left, extend              | `BitVec.shiftLeftZeroExtend` | `BitVec.shiftLeftZeroExtend_eq`          |
| Add (`+`)                       | `BitVec.add`                 | `setWidth_add`                           |
| Sub (`-`)                       | `BitVec.sub`                 | `setWidth_sub`                           |
| Neg (`-`)                       | `BitVec.neg`                 | `setWidth_neg`                           |
| Mul (`*`)                       | `BitVec.mul`                 | `setWidth_mul`                           |
| Unsigned div (`/`)              | `BitVec.udiv`                | `setWidth_udiv`                          |
| Unsigned mod (`%`)              | `BitVec.umod`                | `setWidth_umod`                          |
| Pow (`^`)                       | `BitVec.pow`                 | —                                        |
| Abs                             | `BitVec.abs`                 | `BitVec.abs_eq`                          |
| Signed div                      | `BitVec.sdiv`                | `sdiv_eq_bif_udiv`                       |
| Signed rem                      | `BitVec.srem`                | `srem_eq_bif_umod`                       |
| Signed mod                      | `BitVec.smod`                | `smod_eq_bif_umod`                       |
| SMT unsigned div                | `BitVec.smtUDiv`             | `setWidth_smtUDiv`                       |
| SMT signed div                  | `BitVec.smtSDiv`             | `smtSDiv_eq_bif_smtUDiv`                 |
| And (`&&&`)                     | `BitVec.and`                 | `setWidth_and`                           |
| Or (`\|\|\|`)                   | `BitVec.or`                  | `setWidth_or`                            |
| Xor (`^^^`)                     | `BitVec.xor`                 | `setWidth_xor`                           |
| Not (`~~~`)                     | `BitVec.not`                 | `setWidth_not`                           |
| Shift left by `Nat` (`<<<`)     | `BitVec.shiftLeft`           | `setWidth_shiftLeft'`                    |
| Shift left by `BitVec` (`<<<`)  | `BitVec.shiftLeft`           | `setWidth_shiftLeft`                     |
| Shift right by `Nat` (`>>>`)    | `BitVec.ushiftRight`         | `setWidth_ushiftRight'`                  |
| Shift right by `BitVec` (`>>>`) | `BitVec.ushiftRight`         | `setWidth_ushiftRight`                   |
| Arith shift right by `Nat`      | `BitVec.sshiftRight`         | `setWidth_sshiftRight`                   |
| Arith shift right by `BitVec`   | `BitVec.sshiftRight'`        | `setWidth_sshiftRight'`                  |
| Rotate left                     | `BitVec.rotateLeft`          | `BitVec.rotateLeft_def` †                |
| Rotate right                    | `BitVec.rotateRight`         | `BitVec.rotateRight_def` †               |
| MSB                             | `BitVec.msb`                 | `msb_eq_and_signBitOfMask_ne_zero`       |
| Bit, from LSB                   | `BitVec.getLsbD`             | `getLsbD_eq_setWidth_ushiftRight`        |
| Bit, from MSB                   | `BitVec.getMsbD`             | `getMsbD_eq_and_signBitOfMask_ne_zero` † |
| Bit indexing (`x[i]`)           | `GetElem.getElem`            | `BitVec.getLsbD_eq_getElem` (←)          |
| Bit, from LSB (`Fin` index)     | `BitVec.getLsb`              | —                                        |
| Bit, from MSB (`Fin` index)     | `BitVec.getMsb`              | —                                        |
| Bit, from LSB (`Option`)        | `BitVec.getLsb?`             | —                                        |
| Bit, from MSB (`Option`)        | `BitVec.getMsb?`             | —                                        |
| Reverse                         | `BitVec.reverse`             | `setWidth_reverse`                       |
| Popcount                        | `BitVec.cpop`                | `setWidth_cpop`                          |
| Leading zeros                   | `BitVec.clz`                 | `setWidth_clz`                           |
| Trailing zeros                  | `BitVec.ctz`                 | `setWidth_ctz`                           |
| Unsigned add overflow           | `BitVec.uaddOverflow`        | `uaddOverflow_eq_ult_setWidth`           |
| Signed add overflow             | `BitVec.saddOverflow`        | `BitVec.saddOverflow_eq`                 |
| Unsigned sub overflow           | `BitVec.usubOverflow`        | `usubOverflow_eq_ult_setWidth`           |
| Signed sub overflow             | `BitVec.ssubOverflow`        | `BitVec.ssubOverflow_eq`                 |
| Neg overflow                    | `BitVec.negOverflow`         | `negOverflow_eq_beq_setWidth`            |
| Unsigned mul overflow           | `BitVec.umulOverflow`        | —                                        |
| Signed mul overflow             | `BitVec.smulOverflow`        | —                                        |
| Signed div overflow             | `BitVec.sdivOverflow`        | `sdivOverflow_eq_negOverflow_and`        |

† Only applies to some forms of the operation:
- `ofNatClamp o n` is pushed when `n` is a width variable `w`, or `w - k`, `t - w`, `k % w` or
  `w - k % w`, for a numeral `k` in the `%` forms.
- `rotateLeft`/`rotateRight` are pushed when the amount is a numeral or the width itself.
- `getMsbD x i` is pushed when the index `i` is a numeral.
- `toNat` and `toInt` are eliminated only directly under `BitVec.ofNat`/`BitVec.ofInt`
  (`BitVec.ofNat v x.toNat = x.setWidth v`, `BitVec.ofInt w x.toInt = x`).
-/

namespace Veir.Data.PBV

public section

attribute [pbv_push] signBitOfMask_eq BitVec.setWidth_zero BitVec.ofNat_eq_ofNat
  BitVec.setWidth_cast BitVec.shiftLeftZeroExtend_eq BitVec.setWidth_and Nat.sub_zero
  BitVec.extractLsb BitVec.ofInt_natCast BitVec.ofNat_toNat BitVec.umod_eq
  BitVec.ofInt_toInt

attribute [pbv_push low] BitVec.setWidth_eq

-- Operations that unfold into supported ones. `x[i]` is rewritten to `x.getLsbD i`, which
-- `getLsbD_eq_setWidth_ushiftRight` pushes.
attribute [pbv_push] BitVec.abs_eq BitVec.fill_eq BitVec.rotateLeft_def BitVec.rotateRight_def
  Nat.mod_self
attribute [pbv_push ←] BitVec.getLsbD_eq_getElem

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

@[pbv_push]
theorem setWidth_ite {c : Prop} {o w : Nat} (a b : BitVec w) [Decidable c] :
    (if c then a else b).setWidth o
      = if c then (a.setWidth o) else (b.setWidth o) := by grind

/-! ## Pushing `setWidth o` towards the leaves — leaves and width changes -/

@[pbv_push low]
theorem setWidth_setWidth {o w u : Nat} (h : w ≤ o) (a : BitVec u) :
    (a.setWidth w).setWidth o = a.setWidth o &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_mod_pow_of_le h]

theorem setWidth_toMask {o w : Nat} (h : w ≤ o) (a : BitVec w) :
    a.setWidth o = a.setWidth o &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_setWidth, Nat.mod_mod_pow_of_le h, Nat.mod_eq_of_lt (a.isLt)]

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
theorem setWidth_shiftLeft {o w v : Nat} (hw : w ≤ o) (hv : v ≤ o) (a : BitVec w) (b : BitVec v) :
    (a <<< b).setWidth o = (a.setWidth o <<< b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth hw ?_
  simp only [BitVec.shiftLeft_eq', BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le (x := b) hv),
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_mul_mod, Nat.mod_mod_pow_of_le hw]

@[pbv_push]
theorem setWidth_shiftLeft' {o w : Nat} (h : w ≤ o) (a : BitVec w) (b : Nat) :
    (a <<< b).setWidth o = (a.setWidth o <<< BitVec.ofNatClamp o b) &&& maskOfWidth o w := by
  have : w < 2^o := by grind[Nat.lt_pow_self]
  rw [BitVec.shiftLeft_eq_shiftLeft_ofNatClamp this]
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq, Nat.mod_mul_mod, Nat.mod_mod_pow_of_le h,
    BitVec.shiftLeft_eq', BitVec.toNat_ofNatClamp]

@[pbv_push]
theorem setWidth_ushiftRight {o w v : Nat} (hw : w ≤ o) (hv : v ≤ o) (a : BitVec w) (b : BitVec v) :
    (a >>> b).setWidth o = (a.setWidth o >>> b.setWidth o) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth hw ?_
  simp only [BitVec.ushiftRight_eq', BitVec.toNat_setWidth, Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le hw),
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_mod_eq_div a.isLt,
    Nat.mod_eq_of_lt (BitVec.toNat_lt_twoPow_of_le hv)]

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

/-- `x.concat b` shifts `x` up by one and puts `b` in the lowest bit.
The proof does not need `w ≤ o`, but the bound keeps the lemma from firing at other widths
(e.g. `o := w`), where the mask it introduces would be left behind. -/
@[pbv_push]
theorem setWidth_concat {o w : Nat} (_h : w ≤ o) (x : BitVec w) (b : Bool) :
    (x.concat b).setWidth o
      = ((x.setWidth o <<< 1) ||| (bif b then 1#o else 0#o)) &&& ((maskOfWidth o w <<< 1) ||| 1#o) := by
  ext i hi
  cases b <;> simp [BitVec.getLsbD_concat, BitVec.getElem_shiftLeft, BitVec.getElem_one] <;> grind

/-- `cons b x` puts `b` above the top bit of `x`, at `2 ^ w = maskOfWidth o w + 1`. -/
@[pbv_push]
theorem setWidth_cons {o w : Nat} (h : w ≤ o) (b : Bool) (x : BitVec w) :
    (BitVec.cons b x).setWidth o = x.setWidth o ||| (bif b then maskOfWidth o w + 1#o else 0#o) := by
  rw [maskOfWidth_add_one_eq_twoPow h]
  ext i hi
  cases b <;> simp [BitVec.getLsbD_cons] <;> grind

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

@[pbv_push]
theorem setWidth_cpop {o w : Nat} (h : w ≤ o) (a : BitVec w) :
    (a.cpop).setWidth o = (a.setWidth o).cpop &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_cpop_setWidth_eq_of_le h, BitVec.toNat_cpop, Nat.mod_eq_of_lt]
  apply Nat.lt_of_le_of_lt (by apply BitVec.cpopNatRec_le w)
  simp only [Nat.zero_add, Nat.lt_two_pow_self]

@[pbv_push]
theorem setWidth_clz {o w : Nat} (h : w ≤ o) (a : BitVec w) :
    (a.clz).setWidth o = (a.setWidth o).clz - ((BitVec.ofNat o o) - (maskOfWidth o w).cpop) := by
  have hclz : a.clz.toNat ≤ w := by
    have := BitVec.clz_le (x := a)
    rwa [BitVec.le_def, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt Nat.lt_two_pow_self] at this
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le, toNat_ofNat_sub_cpop_maskOfWidth h, BitVec.toNat_clz_setWidth a h,
    BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.clz.isLt (Nat.pow_le_pow_right (by decide) h))]
  · omega
  · rw [BitVec.le_def, toNat_ofNat_sub_cpop_maskOfWidth h, BitVec.toNat_clz_setWidth a h]
    omega

/-- Reversing the zero-extension puts `a`'s bits at the top, so shift them back down by `o - w`. -/
@[pbv_push]
theorem setWidth_reverse {o w : Nat} (h : w ≤ o) (a : BitVec w) :
    a.reverse.setWidth o =
      (a.setWidth o).reverse >>> ((BitVec.ofNat o o) - (maskOfWidth o w).cpop) := by
  rw [BitVec.ushiftRight_eq', toNat_ofNat_sub_cpop_maskOfWidth h]
  ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getElem_ushiftRight, BitVec.getLsbD_reverse,
    BitVec.getMsbD_setWidth]
  rw [show o - w + i + w - o = i by omega]
  simp

/-- Zero-extension keeps the trailing zeros, except for `0`, where the count is the width `w`. -/
@[pbv_push]
theorem setWidth_ctz {o w : Nat} (h : w ≤ o) (a : BitVec w) :
    a.ctz.setWidth o =
      bif a.setWidth o == 0#o then (maskOfWidth o w).cpop else (a.setWidth o).ctz := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.ctz.isLt (Nat.pow_le_pow_right (by decide) h))]
  by_cases ha : a = 0#w
  · subst ha
    simp only [BitVec.setWidth_zero, beq_self_eq_true, Bool.cond_true, BitVec.toNat_ctz_zero,
      cpop_eq_width_of_maskOfWidth h rfl, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have : o < 2 ^ o := Nat.lt_two_pow_self; omega)]
  · have ha' := BitVec.setWidth_ne_zero_of_le h ha
    simp only [beq_eq_false_iff_ne.mpr ha', Bool.cond_false, BitVec.toNat_ctz_setWidth_of_ne_zero h ha]

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

/-- Bit `i` of `x`, read from the lowest bit of `x >>> i` at width `o`. -/
@[pbv_push_bound]
theorem getLsbD_eq_setWidth_ushiftRight (o : Nat) {w : Nat} (h : w ≤ o) (x : BitVec w) (i : Nat) :
    x.getLsbD i = (((x >>> i).setWidth o &&& 1#o) != 0#o) := by
  rcases Nat.eq_zero_or_pos o with rfl | ho
  · obtain rfl : w = 0 := by omega
    simp [BitVec.of_length_zero]
  · have hb : ∀ y : BitVec o, ((y &&& 1#o) != 0#o) = y.getLsbD 0 := by
      intro y
      rw [Bool.eq_iff_iff, bne_iff_ne, ne_eq, ← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega)), Nat.and_one_is_mod]
      simp only [BitVec.getLsbD, Nat.testBit_zero, BitVec.toNat_ofNat, Nat.zero_mod, decide_eq_true_eq]
      omega
    rw [hb]
    simp [ho]

/-- `x.getMsbD i` is bit `w - 1 - i`: the sign bit of the mask shifted down by `i`. -/
@[pbv_push_bound]
theorem getMsbD_eq_and_signBitOfMask_ne_zero (o : Nat) {w : Nat} (h : w ≤ o)
    (x : BitVec w) (i : Nat) :
    x.getMsbD i = ((x.setWidth o &&& (signBitOfMask (maskOfWidth o w) >>> i)) != 0#o) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [BitVec.getMsbD]
  · rw [signBitOfMask_maskOfWidth_eq_twoPow_of_pos h hw, BitVec.getMsbD_eq_getLsbD]
    by_cases hi : i < w
    · have hs : BitVec.twoPow o (w - 1) >>> i = BitVec.twoPow o (w - 1 - i) := by
        ext j hj
        simp only [BitVec.getElem_ushiftRight, BitVec.getElem_twoPow, BitVec.getLsbD_twoPow]
        grind
      have hlt : w - 1 - i < o := by omega
      rw [hs, BitVec.and_twoPow, BitVec.getLsbD_setWidth]
      cases x.getLsbD (w - 1 - i) <;> simp [hi, hlt, BitVec.twoPow_ne_zero hlt]
    · have hs : BitVec.twoPow o (w - 1) >>> i = 0#o := by
        ext j hj
        simp only [BitVec.getElem_ushiftRight, BitVec.getLsbD_twoPow, BitVec.getElem_zero]
        grind
      simp [hi, hs]

/-! ### Overflow flags

The signed overflows are unfolded into `msb`s, which `msb_eq_and_signBitOfMask_ne_zero` pushes.
Otherwise `bv_decide` would unfold them only after pushing, leaving `msb`s at the parametric width.
-/

attribute [pbv_push] BitVec.saddOverflow_eq BitVec.ssubOverflow_eq

/-- A mask is non-zero exactly when its width is. -/
theorem maskOfWidth_ne_zero_iff {o w : Nat} (h : w ≤ o) : maskOfWidth o w ≠ 0#o ↔ 0 < w := by
  rw [ne_eq, ← BitVec.toNat_inj, toNat_maskOfWidth h, BitVec.toNat_ofNat, Nat.zero_mod]
  have := Nat.one_le_two_pow (n := w)
  constructor
  · intro h0; rcases Nat.eq_zero_or_pos w with rfl | hw
    · simp at h0
    · exact hw
  · intro hw; have := Nat.one_lt_two_pow (n := w) (by omega); omega

/-- Negation overflows iff `x` is `intMin`, for a non-zero width. -/
@[pbv_push_bound]
theorem negOverflow_eq_beq_setWidth (o : Nat) {w : Nat} (h : w ≤ o) (x : BitVec w) :
    x.negOverflow = (maskOfWidth o w != 0#o && x.setWidth o == (BitVec.intMin w).setWidth o) := by
  rw [BitVec.negOverflow_eq, ← beq_setWidth o h]
  congr 1
  have := maskOfWidth_ne_zero_iff h
  by_cases hw : 0 < w <;> simp_all

/-- Signed division overflows iff `x / -1` negates `intMin`. -/
@[pbv_push_bound]
theorem sdivOverflow_eq_negOverflow_and (o : Nat) {w : Nat} (h : w ≤ o) (x y : BitVec w) :
    x.sdivOverflow y = (x.negOverflow && y.setWidth o == maskOfWidth o w) := by
  rw [BitVec.sdivOverflow_eq, BitVec.negOverflow_eq, maskOfWidth_eq_allOnes h]
  have := beq_setWidth o h y (BitVec.allOnes w)
  simp only [BitVec.truncate_eq_setWidth] at *
  rw [← this]
  simp [Bool.and_assoc, Bool.beq_eq_decide_eq]

/-- Unsigned addition overflows iff the wrapped sum is below an operand, compared at width `o`. -/
@[pbv_push_bound]
theorem uaddOverflow_eq_ult_setWidth (o : Nat) {w : Nat} (h : w ≤ o) (a b : BitVec w) :
    a.uaddOverflow b = ((a + b).setWidth o).ult (a.setWidth o) := by
  rw [← ult_setWidth o h]
  have := a.isLt; have := b.isLt
  simp only [BitVec.uaddOverflow, BitVec.ult_eq_decide, BitVec.toNat_add]
  rw [decide_eq_decide]
  by_cases hc : a.toNat + b.toNat < 2 ^ w
  · simp only [Nat.mod_eq_of_lt hc]; omega
  · simp only [Nat.mod_eq_sub_mod (Nat.le_of_not_lt hc), Nat.mod_eq_of_lt (by omega : a.toNat + b.toNat - 2 ^ w < 2 ^ w)]
    omega

/-- Unsigned subtraction overflows iff `a < b`, compared at width `o`. -/
@[pbv_push_bound]
theorem usubOverflow_eq_ult_setWidth (o : Nat) {w : Nat} (h : w ≤ o) (a b : BitVec w) :
    a.usubOverflow b = (a.setWidth o).ult (b.setWidth o) := by
  rw [← ult_setWidth o h, BitVec.usubOverflow_eq, BitVec.ult_eq_decide]
  simp [BitVec.lt_def]

@[pbv_push]
theorem setWidth_twoPow {o w n : Nat} (h : w ≤ o) :
    (BitVec.twoPow w n).setWidth o = (maskOfWidth o n + 1) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp [maskOfWidth, Nat.mod_mod_pow_of_le h, Nat.sub_one_add_one]

@[pbv_push]
theorem setWidth_ofIntMin {o w : Nat} (h : w ≤ o) :
    (BitVec.intMin w).setWidth o = maskOfWidth o w ^^^ (maskOfWidth o w >>> 1) := by
  ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_intMin, maskOfWidth_eq_allOnes h, BitVec.truncate_eq_setWidth,
    BitVec.getElem_xor, BitVec.getLsbD_allOnes, BitVec.getElem_ushiftRight, BitVec.getLsbD_setWidth]
  grind

@[pbv_push]
theorem setWidth_ofIntMax {o w : Nat} (h : w ≤ o) :
    (BitVec.intMax w).setWidth o = (maskOfWidth o w >>> 1) := by
  ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_intMax, maskOfWidth_eq_allOnes h, BitVec.truncate_eq_setWidth,
    BitVec.getElem_ushiftRight, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  grind

@[pbv_push]
theorem setWidth_ofInt {o w : Nat} {i : Int} (h : w ≤ o) :
    (BitVec.ofInt w i).setWidth o = (BitVec.ofInt o i) &&& maskOfWidth o w := by
  refine setWidth_eq_and_maskOfWidth h ?_
  simp only [BitVec.toNat_ofInt]
  have hdvd : ((2 ^ w : Nat) : Int) ∣ ((2 ^ o : Nat) : Int) :=
    Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 h)
  have hw := Nat.two_pow_pos w
  have ho := Nat.two_pow_pos o
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)),
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega)), Int.emod_emod_of_dvd _ hdvd]

@[pbv_push]
theorem setWidth_allOnes {o w : Nat} (h : w ≤ o) :
    (BitVec.allOnes w).setWidth o = maskOfWidth o w := by
  exact Eq.symm (maskOfWidth_eq_allOnes h)

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

@[pbv_push]
theorem ofNat_nat_sub_of_maskOfWidth {o w n : Nat} {m : BitVec o} (h : w ≤ o) (hm : m = maskOfWidth o w) :
    BitVec.ofNat o (w - n) = (m >>> n).cpop := by
  have hshift : m >>> n = maskOfWidth o (w - n) := by
    subst hm
    ext i hi
    simp only [BitVec.getElem_ushiftRight, getLsbD_maskOfWidth, getElem_maskOfWidth]
    grind
  rw [hshift]
  exact (cpop_eq_width_of_maskOfWidth (by omega) rfl).symm

/-- The difference of two width variables is the difference of their masks' popcounts.
This takes priority over `ofNat_nat_sub_of_maskOfWidth`, which would shift by the `Nat` `w`. -/
@[pbv_push high]
theorem ofNat_sub_of_maskOfWidth {o t w : Nat} {mt mw : BitVec o} (ht : t ≤ o) (hw : w ≤ o)
    (hmt : mt = maskOfWidth o t) (hmw : mw = maskOfWidth o w) :
    BitVec.ofNat o (t - w) = bif mw.ule mt then mt.cpop - mw.cpop else 0#o := by
  rw [cpop_eq_width_of_maskOfWidth ht hmt, cpop_eq_width_of_maskOfWidth hw hmw]
  have ho : o < 2 ^ o := Nat.lt_two_pow_self
  have hle : mw.ule mt = decide (w ≤ t) := by
    subst hmt hmw
    rw [BitVec.ule_eq_decide, toNat_maskOfWidth hw, toNat_maskOfWidth ht]
    have := Nat.one_le_two_pow (n := w); have := Nat.one_le_two_pow (n := t)
    simp only [decide_eq_decide]
    rw [Nat.sub_le_sub_iff_right (by omega), Nat.pow_le_pow_iff_right (by decide)]
  rw [hle]
  by_cases h : w ≤ t
  · simp only [h, decide_true, Bool.cond_true]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp [Nat.mod_eq_of_lt (by omega : w < 2 ^ o), Nat.mod_eq_of_lt (by omega : t < 2 ^ o)]; omega)]
    simp [Nat.mod_eq_of_lt (by omega : w < 2 ^ o), Nat.mod_eq_of_lt (by omega : t < 2 ^ o), Nat.mod_eq_of_lt (by omega : t - w < 2 ^ o)]
  · simp only [h, decide_false, Bool.cond_false]
    rw [Nat.sub_eq_zero_of_le (by omega)]

/-- The mask of a difference of two width variables, for widths that have no mask variable of their
own. Like `ofNat_sub_of_maskOfWidth`, it takes priority over the `Nat` shift of
`maskOfWidth_sub_eq_ushiftRight`. -/
@[pbv_push high]
theorem maskOfWidth_sub_eq_ushiftRight_cpop {o t n : Nat} {mt mn : BitVec o} (ht : t ≤ o)
    (hn : n ≤ o) (hmt : mt = maskOfWidth o t) (hmn : mn = maskOfWidth o n) :
    maskOfWidth o (t - n) = mt >>> mn.cpop := by
  rw [BitVec.ushiftRight_eq', cpop_eq_width_of_maskOfWidth hn hmn, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hn Nat.lt_two_pow_self)]
  subst hmt
  ext i hi
  simp only [BitVec.getElem_ushiftRight, getLsbD_maskOfWidth, getElem_maskOfWidth]
  grind

/-- The mask of a width variable minus a literal. -/
@[pbv_push]
theorem maskOfWidth_sub_eq_ushiftRight {o t n : Nat} {mt : BitVec o} (ht : t ≤ o)
    (hmt : mt = maskOfWidth o t) :
    maskOfWidth o (t - n) = mt >>> n := by
  subst hmt
  ext i hi
  simp only [BitVec.getElem_ushiftRight, getLsbD_maskOfWidth, getElem_maskOfWidth]
  grind

/-! ### `Nat` shift amounts

Shifts by a `Nat` become shifts by `BitVec.ofNatClamp o n`; these push the amounts that
mention width variables. The `% w` ones come from `rotateLeft`/`rotateRight`.
-/

/-- A `Nat` shift by a width variable minus a constant. -/
@[pbv_push]
theorem ofNatClamp_nat_sub_of_maskOfWidth {o w n : Nat} {m : BitVec o} (h : w ≤ o)
    (hm : m = maskOfWidth o w) :
    BitVec.ofNatClamp o (w - n) = (m >>> n).cpop := by
  have ho : o < 2 ^ o := Nat.lt_two_pow_self
  rw [BitVec.ofNatClamp_eq_ofNat (by omega)]
  exact ofNat_nat_sub_of_maskOfWidth h hm

/-- A `Nat` shift by the difference of two width variables. -/
@[pbv_push high]
theorem ofNatClamp_sub_of_maskOfWidth {o t w : Nat} {mt mw : BitVec o} (ht : t ≤ o) (hw : w ≤ o)
    (hmt : mt = maskOfWidth o t) (hmw : mw = maskOfWidth o w) :
    BitVec.ofNatClamp o (t - w) = bif mw.ule mt then mt.cpop - mw.cpop else 0#o := by
  have ho : o < 2 ^ o := Nat.lt_two_pow_self
  rw [BitVec.ofNatClamp_eq_ofNat (by omega)]
  exact ofNat_sub_of_maskOfWidth ht hw hmt hmw

/-- `ofNatClamp_ofNat_mod_of_maskOfWidth` for any `n`. Not a push lemma: for a variable `n`,
the width `n + o` is not concrete. -/
theorem ofNatClamp_mod_of_maskOfWidth {o w n : Nat} {m : BitVec o} (h : w ≤ o)
    (hm : m = maskOfWidth o w) :
    BitVec.ofNatClamp o (n % w) =
      bif m == 0#o then BitVec.ofNatClamp o n
      else ((BitVec.ofNat (n + o) n) % (m.cpop.setWidth (n + o))).setWidth o := by
  rw [cpop_eq_width_of_maskOfWidth h hm]
  have ho : o < 2 ^ o := Nat.lt_two_pow_self
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [hm]
  · have hm0 : (m == 0#o) = false := by
      rw [hm]; simpa using (maskOfWidth_ne_zero_iff h).mpr hw
    have hnw : n % w < w := Nat.mod_lt _ hw
    have hn : n < 2 ^ (n + o) := Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by decide) (by omega))
    have hwo : w < 2 ^ (n + o) := Nat.lt_of_lt_of_le (by omega : w < 2 ^ o) (Nat.pow_le_pow_right (by decide) (by omega))
    rw [hm0, Bool.cond_false, BitVec.ofNatClamp_eq_ofNat (by omega)]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_umod, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega : w < 2 ^ o),
      Nat.mod_eq_of_lt hwo, Nat.mod_eq_of_lt (by omega : n % w < 2 ^ o)]

/-- A rotation amount `n % w` for a numeral `n`. The remainder is computed at width `n + o`,
which is concrete and wide enough to hold both `n` and `w`. Restricting `n` to numerals keeps
that width concrete. -/
@[pbv_push]
theorem ofNatClamp_ofNat_mod_of_maskOfWidth {o w n : Nat} {m : BitVec o} (h : w ≤ o)
    (hm : m = maskOfWidth o w) :
    BitVec.ofNatClamp o ((no_index (OfNat.ofNat n : Nat)) % w) =
      bif m == 0#o then BitVec.ofNatClamp o (OfNat.ofNat n)
      else ((BitVec.ofNat (OfNat.ofNat n + o) (OfNat.ofNat n)) %
        (m.cpop.setWidth (OfNat.ofNat n + o))).setWidth o :=
  ofNatClamp_mod_of_maskOfWidth h hm

/-- The complementary rotation amount `w - n % w`. -/
@[pbv_push high]
theorem ofNatClamp_sub_mod_of_maskOfWidth {o w n : Nat} {m : BitVec o} (h : w ≤ o)
    (hm : m = maskOfWidth o w) :
    BitVec.ofNatClamp o (w - n % w) = bif m == 0#o then 0#o else m.cpop - BitVec.ofNatClamp o (n % w) := by
  have ho : o < 2 ^ o := Nat.lt_two_pow_self
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp [hm, BitVec.ofNatClamp_eq_ofNat (by omega : 0 < 2 ^ o)]
  · have hm0 : (m == 0#o) = false := by
      rw [hm]; simpa using (maskOfWidth_ne_zero_iff h).mpr hw
    have hnw : n % w < w := Nat.mod_lt _ hw
    rw [hm0, Bool.cond_false, cpop_eq_width_of_maskOfWidth h hm, BitVec.ofNatClamp_eq_ofNat (by omega),
      BitVec.ofNatClamp_eq_ofNat (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp [Nat.mod_eq_of_lt (by omega : w < 2 ^ o),
      Nat.mod_eq_of_lt (by omega : n % w < 2 ^ o)]; omega)]
    simp [Nat.mod_eq_of_lt (by omega : w < 2 ^ o), Nat.mod_eq_of_lt (by omega : n % w < 2 ^ o),
      Nat.mod_eq_of_lt (by omega : w - n % w < 2 ^ o)]
