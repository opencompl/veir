module

public meta import Veir.Meta.Tactic.BVDecide
public import Veir.Data.LLVM.Int.Bitblast
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Int.Bitblast

open Veir.Data.LLVM

namespace Veir.Data.GMIR

public section

/--
 Like `LLVM.Int.select`, for a condition of any width, which is true when it is nonzero. This is the
 meaning gMIR's `G_SELECT` has on a target whose booleans are zero or one, such as RISC-V: LLVM
 leaves the meaning of a condition wider than `i1` to the target. For an `i1` condition, it is
 `select` (see `selectNonzero_one`).
-/
def selectNonzero {wc w : Nat} (c : Int wc) (x y : Int w) : Int w := Id.run do
  let .val c' := c | .poison
  if c' != 0#wc then x else y

@[veir_bv_normalize, grind =]
theorem isPoison_selectNonzero {wc w : Nat} (x y : Int w) (c : Int wc) :
    (selectNonzero c x y).isPoison =
      if h : c.isPoison = true then true
      else if c.getValue ≠ 0#wc then x.isPoison else y.isPoison := by
  cases c with
  | poison => simp [selectNonzero, Id.run, Int.isPoison]
  | val c' => by_cases hc : c' = 0#wc <;> simp [selectNonzero, Id.run, hc, Int.isPoison]

@[veir_bv_normalize, grind =]
theorem getValue_selectNonzero {wc w : Nat} (x y : Int w) (c : Int wc)
    (h : (selectNonzero c x y).isPoison = false) :
    (selectNonzero c x y).getValue h =
      if _ : c.getValue ≠ 0#wc then x.getValue else y.getValue := by
  cases c with
  | poison => simp [selectNonzero, Id.run, Int.isPoison] at h
  | val c' => by_cases hc : c' = 0#wc <;> simp [selectNonzero, Id.run, hc]

/--
 The amount `z` of a `w`-bit funnel shift or rotate, reduced modulo `w`. In gMIR, the amount (type
 group 1) may be wider or narrower than the shifted values (type group 0), and is read as an
 unsigned integer, as in LLVM's `G_FSHL`, `G_FSHR`, `G_ROTL` and `G_ROTR`.
-/
def funnelShiftAmount {w' : Nat} (w : Nat) : Int w' → Int w
  | .val z => .val (BitVec.ofNat w (z.toNat % w))
  | .poison => .poison

/-- gMIR's `G_ROTL`: the funnel shift left of `x` with itself by `z`. -/
def rotl {w w' : Nat} (x : Int w) (z : Int w') : Int w :=
  Int.fshl x x (funnelShiftAmount w z)

/-- gMIR's `G_ROTR`: the funnel shift right of `x` with itself by `z`. -/
def rotr {w w' : Nat} (x : Int w) (z : Int w') : Int w :=
  Int.fshr x x (funnelShiftAmount w z)

/-- For an `i1` condition, `selectNonzero` is `select`. -/
theorem selectNonzero_one {w : Nat} (c : Int 1) (x y : Int w) :
    selectNonzero c x y = Int.select c x y := by
  cases c with
  | poison => simp [selectNonzero, Int.select, Id.run]
  | val c' =>
    rcases BitVec.eq_zero_or_eq_one c' with rfl | rfl <;>
      simp [selectNonzero, Int.select, Id.run]

/--
Converts a shift amount (type group 1) to the width `w` of the shifted value (type group 0).
An amount that does not fit in `w` bits is out of range, so it is replaced by the all-ones value,
which is also out of range and hence yields the same (poison) result.
-/
def shiftAmount {w' : Nat} (w : Nat) : Data.LLVM.Int w' → Data.LLVM.Int w
  | .val v => .val (if v.toNat < w then BitVec.ofNat w v.toNat else BitVec.allOnes w)
  | .poison => .poison

/-- Converts a bit count to the width `w` of the result (type group 0) of `g_ctlz`/`g_cttz`/`g_ctpop`. -/
def resizeCount {w' : Nat} (w : Nat) : Data.LLVM.Int w' → Data.LLVM.Int w
  | .val v => .val (BitVec.ofNat w v.toNat)
  | .poison => .poison

/--
The `2 * w`-bit value whose low half is `lo` and whose high half is `hi`, as produced by gMIR's
`g_merge_values`. If either half is poison, the result is poison.
-/
-- TODO: A poison half should not make the other half poison, so that a half padded with
-- `g_implicit_def` (as LLVM does when narrowing `g_anyext`) keeps the defined half.
def mergeValues {w : Nat} (lo hi : Data.LLVM.Int w) : Data.LLVM.Int (w + w) :=
  match lo, hi with
  | .val lo, .val hi => .val (hi ++ lo)
  | _, _ => .poison

/--
The low and the high half of the `2 * w`-bit `x`, as produced by gMIR's `g_unmerge_values`.
If `x` is poison, both halves are poison.
-/
def unmergeValues {w : Nat} (x : Data.LLVM.Int (w + w)) :
    Data.LLVM.Int w × Data.LLVM.Int w :=
  match x with
  | .val x => (.val (x.truncate w), .val (x.extractLsb' w w))
  | .poison => (.poison, .poison)

/--
The sum of `x`, `y` and the carry `c`, and the carry out, as produced by gMIR's `g_uadde`. The sum
is taken modulo `2^w`, and the carry out is `1` if it does not fit in `w` bits. If any operand is
poison, both results are poison.
-/
def uaddWithCarry {w : Nat} (x y : Data.LLVM.Int w) (c : Data.LLVM.Int 1) :
    Data.LLVM.Int w × Data.LLVM.Int 1 :=
  match x, y, c with
  | .val x, .val y, .val c =>
    let sum := x + y + c.zeroExtend w
    -- `BitVec.carry w` is the carry out of a `w`-bit add, i.e. whether `x + y + c ≥ 2^w`.
    (.val sum, .val (BitVec.ofBool (BitVec.carry w x y (c.getLsbD 0))))
  | _, _, _ => (.poison, .poison)

/--
The difference of `x`, `y` and the borrow `b`, and the borrow out, as produced by gMIR's `g_usube`.
The difference is taken modulo `2^w`, and the borrow out is `1` if `x < y + b` as unsigned integers.
If any operand is poison, both results are poison.
-/
def usubWithBorrow {w : Nat} (x y : Data.LLVM.Int w) (b : Data.LLVM.Int 1) :
    Data.LLVM.Int w × Data.LLVM.Int 1 :=
  match x, y, b with
  | .val x, .val y, .val b =>
    -- `y + b` is at most `2^w`, so it fits in `w + 1` bits.
    let borrow := (x.zeroExtend (w + 1)).ult (y.zeroExtend (w + 1) + b.zeroExtend (w + 1))
    (.val (x - y - b.zeroExtend w), .val (BitVec.ofBool borrow))
  | _, _, _ => (.poison, .poison)

/--
Reverses the bits within each byte of `x`, as RISC-V's `brev8` (LLVM's `RISCV::G_BREV8`).
Reversing all bits also reverses the byte order, which `bswap` undoes. The verifier only accepts
widths of 8, 16, 32 and 64 bits.
-/
def brev8 {w : Nat} (x : Data.LLVM.Int w) : Data.LLVM.Int w :=
  if w = 8 then Data.LLVM.Int.bitreverse x else Data.LLVM.Int.bitreverse (Data.LLVM.Int.bswap x)

end

end Veir.Data.GMIR
