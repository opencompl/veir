module

public import Veir.Data.LLVM.Int.Basic

namespace Veir.Data.Comb

public section

/-! # CIRCT Comb Dialect Semantics

Value-level semantics for the `comb` dialect, over `LLVM.Int w` so that poison is expressible.
`Veir.Comb.interpretOp'` is the thin layer that reads these out of the IR.

Two conventions run through the file:

- **Poison propagates from any operand.** `comb` has no operation that is defined when one of its
  inputs is not, so every variadic operation returns poison as soon as it sees one, and every
  fixed-arity one matches on its operands first.
- **Width is carried in the type**, so nothing here can be applied at disagreeing widths. The
  operations whose result width differs from their operand width say so in their signatures, and
  the operation interpreter is what checks the IR agrees.
-/

/-- Fold a variadic operation over its operands, returning poison if any operand is poison.

`comb`'s variadic operations are all associative with a unit, which is what makes this shape
work for every one of them. -/
private def variadic {w : Nat} (unit : BitVec w) (f : BitVec w → BitVec w → BitVec w)
    (l : List (LLVM.Int w)) : LLVM.Int w := Id.run do
  let mut acc : BitVec w := unit
  for x in l do
    match x with
    | .poison => return .poison
    | .val x' => acc := f acc x'
  .val acc

/--
Variadic `add` operation returns a poison value only if any of the arguments is poison, otherwise it returns the sum of the arguments.
-/
def add {w : Nat} (l : List (LLVM.Int w)) : LLVM.Int w := variadic 0 (· + ·) l

/-- Variadic `mul`. Poison if any operand is. -/
def mul {w : Nat} (l : List (LLVM.Int w)) : LLVM.Int w := variadic 1 (· * ·) l

/-- Variadic bitwise `and`. The unit is all ones. -/
def and {w : Nat} (l : List (LLVM.Int w)) : LLVM.Int w := variadic (BitVec.allOnes w) (· &&& ·) l

/-- Variadic bitwise `or`. -/
def or {w : Nat} (l : List (LLVM.Int w)) : LLVM.Int w := variadic 0 (· ||| ·) l

/-- Variadic bitwise `xor`.

`comb` has no `not`; complementing against an all-ones constant is CIRCT's idiom for it, so this
is the operation a `~` in a source language usually becomes. -/
def xor {w : Nat} (l : List (LLVM.Int w)) : LLVM.Int w := variadic 0 (· ^^^ ·) l

/-- Binary `sub`. Not variadic, unlike the operations above. -/
def sub {w : Nat} (x y : LLVM.Int w) : LLVM.Int w :=
  match x, y with
  | .val x, .val y => .val (x - y)
  | _, _ => .poison

/-- `comb.shl`. A shift **at or past the operand width is poison**, which is where this differs
from `BitVec.shiftLeft` giving zero, and from what a hardware shifter would do. -/
def shl {w : Nat} (x y : LLVM.Int w) : LLVM.Int w :=
  match x, y with
  | .val x, .val y => if y.toNat ≥ w then .poison else .val (x.shiftLeft y.toNat)
  | _, _ => .poison

/-- `comb.shru`, the logical right shift. Out of range is poison, as for `shl`. -/
def shru {w : Nat} (x y : LLVM.Int w) : LLVM.Int w :=
  match x, y with
  | .val x, .val y => if y.toNat ≥ w then .poison else .val (x.ushiftRight y.toNat)
  | _, _ => .poison

/-- `comb.shrs`, the arithmetic right shift. Out of range is poison, as for `shl`. -/
def shrs {w : Nat} (x y : LLVM.Int w) : LLVM.Int w :=
  match x, y with
  | .val x, .val y => if y.toNat ≥ w then .poison else .val (x.sshiftRight y.toNat)
  | _, _ => .poison

/-- `comb.icmp`, with CIRCT's `ICmpPredicate` as the integer it is printed as.

The numbering is MLIR's and `LLVM.IntPred` already uses it -- 0 is `eq`, 6 is `ult` -- so the
predicate table is shared rather than restated here. -/
def icmp {w : Nat} (p : LLVM.IntPred) (x y : LLVM.Int w) : LLVM.Int 1 :=
  match x, y with
  | .val x, .val y => .val (BitVec.ofBool (p.eval x y))
  | _, _ => .poison

