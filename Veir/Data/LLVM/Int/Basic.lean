module

namespace Veir.Data.LLVM

public section

/--
The `Int` type can have any bitwidth `w`. It is either a two's complement
integer value of width `w` or a poison value indicating delayed undefined
bahavior.
-/
inductive Int (w : Nat) where
/-- A two's complement integer value of width `w`. -/
| val : BitVec w → Int w
/-- A poison value indicating delayed undefined behavior. -/
| poison : Int w
deriving DecidableEq, Inhabited

namespace Int

instance {w : Nat} : ToString (Int w) where
  toString
    | .val v => toString v
    | .poison => "poison"

/--
The ‘add’ instruction returns the sum of its two operands.

If the sum has unsigned overflow, the result returned is the mathematical result
modulo 2^n, where n is the bit width of the result.

Because LLVM integers use a two’s complement representation, this instruction is
appropriate for both signed and unsigned integers.

`nuw` and `nsw` stand for “No Unsigned Wrap” and “No Signed Wrap”, respectively.
If the `nuw` and/or `nsw` arguments are true, the result value of the add is a
poison value if unsigned and/or signed overflow, respectively, occurs.
-/
def add {w : Nat} (x y : Int w) (nsw : Bool := false) (nuw : Bool := false) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if nsw ∧ BitVec.saddOverflow x' y' then
    return poison

  if nuw ∧ BitVec.uaddOverflow x' y' then
    return poison

  val (x' + y')

/--
The `sub` instruction returns the difference of its two operands.

Note that the `sub` instruction is used to represent the `neg` instruction
present in most other intermediate representations.

The value produced is the integer difference of the two operands.

If the difference has unsigned overflow, the result returned is the mathematical
result modulo `2^w`, where `w` is the bit width of the result.

Because LLVM integers use a two’s complement representation, this instruction is
appropriate for both signed and unsigned integers.

`nuw` and `nsw` stand for “No Unsigned Wrap” and “No Signed Wrap”, respectively.
If the `nuw` and/or `nsw` arguments are true, the result value of the sub is a
poison value if unsigned and/or signed overflow, respectively, occurs.
-/
def sub {w : Nat} (x y : Int w) (nsw : Bool := false) (nuw : Bool := false) :
    Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if nsw ∧ BitVec.ssubOverflow x' y' then
    return poison

  if nuw ∧ BitVec.usubOverflow x' y' then
    return poison

  val (x' - y')

/--
The ‘mul’ instruction returns the product of its two operands.

If the result of the multiplication has unsigned overflow, the result returned
is the mathematical result modulo 2^n, where n is the bit width of the result.

Because LLVM integers use a two’s complement representation, and the result is
the same width as the operands, this instruction returns the correct result for
both signed and unsigned integers. If a full product (e.g., i32 * i32 -> i64) is
needed, the operands should be sign-extended or zero-extended as appropriate to
the width of the full product.

`nuw` and `nsw` stand for “No Unsigned Wrap” and “No Signed Wrap”, respectively. If
the `nuw` and/or `nsw` arguments are true, the result value of the mul is a poison
value if unsigned and/or signed overflow, respectively, occurs.
-/
def mul {w : Nat} (x y : Int w) (nsw : Bool := false) (nuw : Bool := false) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if nsw ∧ BitVec.smulOverflow x' y' then
    return poison

  if nuw ∧ BitVec.umulOverflow x' y' then
    return poison

  val (x' * y')

/--
The ‘udiv’ instruction returns the unsigned integer quotient of its two operands.

Note that unsigned integer division and signed integer division are distinct
operations; for signed integer division, use ‘sdiv’.

Division by zero is undefined behavior. For vectors, if any element of the
divisor is zero, the operation has undefined behavior.

If the `exact` argument is true, the result value of the udiv is a poison value
if `x` is not a multiple of `y` (as such, “((a udiv exact b) mul b) == a”).
-/
def udiv {w : Nat} (x y : Int w) (exact : Bool := false) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if exact ∧ x'.umod y' ≠ 0 then
    return poison

  if y' = 0 then
    return poison

  val (x' / y')

/--
The ‘sdiv’ instruction returns the quotient of its two operands.

The value produced is the signed integer quotient of the two operands rounded
towards zero.

Note that signed integer division and unsigned integer division are distinct
operations; for unsigned integer division, use ‘udiv’.

Division by zero is undefined behavior. For vectors, if any element of the
divisor is zero, the operation has undefined behavior. Overflow also leads to
undefined behavior; this is a rare case, but can occur, for example, by doing a
32-bit division of -2147483648 by -1.

If the `exact` argument is true, the result value of the sdiv is a poison value
if the result would be rounded.
-/
def sdiv {w : Nat} (x y : Int w) (exact : Bool := false) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if y' == 0 || (w != 1 && x' == (BitVec.intMin w) && y' == -1) then
    return poison

  if exact ∧ x'.smod y' ≠ 0 then
    return poison

  if y' == 0 then
    return poison

  val (x'.sdiv y')

/--
The ‘urem’ instruction returns the unsigned integer remainder from the
unsigned division of its two arguments. This instruction always performs
an unsigned division to get the remainder.

Note that unsigned integer remainder and signed integer remainder are distinct
operations; for signed integer remainder, use ‘srem’.

Taking the remainder of a division by zero is undefined behavior. For vectors,
if any element of the divisor is zero, the operation has undefined behavior.
-/
def urem {w : Nat} (x y : Int w) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if y' == 0 then
    return poison

  val (x' % y')

/--
The ‘srem’ instruction returns the remainder from the signed division of its two
operands.

This instruction returns the remainder of a division (where the result is either
zero or has the same sign as the dividend, `x`), not the modulo operator (where
the result is either zero or has the same sign as the divisor, `y`) of a value.

Note that signed integer remainder and unsigned integer remainder are distinct
operations; for unsigned integer remainder, use ‘urem’.

Taking the remainder of a division by zero is undefined behavior. For vectors,
if any element of the divisor is zero, the operation has undefined behavior.
Overflow also leads to undefined behavior; this is a rare case, but can occur,
for example, by taking the remainder of a 32-bit division of -2147483648 by -1.
(The remainder doesn’t actually overflow, but this rule lets srem be implemented
using instructions that return both the result of the division and the
remainder.)
-/
def srem {w : Nat} (x y : Int w) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if y' == 0 || (w != 1 && x' == (BitVec.intMin w) && y' == -1) then
    return poison

  val (x'.srem y')

/--
The ‘shl’ instruction returns the first operand shifted to the left by a specified
number of bits.

The value produced is `x` * 2^`y` mod 2^n, where n is the width of the result.
If `y` is (statically or dynamically) equal to or larger than the number of bits
in `x`, this instruction returns a poison value. If the arguments are vectors,
each vector element of `x` is shifted by the corresponding shift amount in `y`.

If the `nuw` keyword is present, then the shift produces a poison value if it
shifts out any non-zero bits. If the `nsw` keyword is present, then the shift
produces a poison value if it shifts out any bits that disagree with the
resultant sign bit.
-/
def shl {w : Nat} (x y : Int w) (nsw : Bool := false) (nuw : Bool := false) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if nsw ∧ (x' <<< y').sshiftRight' y' ≠ x' then
    return poison

  if nuw ∧ (x' <<< y') >>> y' ≠ x' then
    return poison

  if y' ≥ w then
    return poison

  val (x' <<< y')

/--
The ‘lshr’ instruction (logical shift right) returns the first operand shifted
to the right a specified number of bits with zero fill.

This instruction always performs a logical shift right operation. The most
significant bits of the result will be filled with zero bits after the shift. If
`y` is (statically or dynamically) equal to or larger than the number of bits in
`x`, this instruction returns a poison value. If the arguments are vectors, each
vector element of `x` is shifted by the corresponding shift amount in `y`.

If the `exact` argument is true, the result value of the lshr is a poison value
if any of the bits shifted out are non-zero.
-/
def lshr {w : Nat} (x y : Int w) (exact : Bool := false) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if y' ≥ w then
    return poison

  if exact ∧ (x' >>> y') <<< y' ≠ x' then
    return poison

  val (x' >>> y')

/--
The ‘ashr’ instruction (arithmetic shift right) returns the first operand
shifted to the right a specified number of bits with sign extension.

This instruction always performs an arithmetic shift right operation, The most
significant bits of the result will be filled with the sign bit of `x`. If `y`
is (statically or dynamically) equal to or larger than the number of bits in
`x`, this instruction returns a poison value. If the arguments are vectors, each
vector element of `x` is shifted by the corresponding shift amount in `y`.

If the `exact` argument is true, the result value of the ashr is a poison value
if any of the bits shifted out are non-zero.
-/
def ashr {w : Nat} (x y : Int w) (exact : Bool := false) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if y' ≥ w then
    return poison

  if exact ∧ (x' >>> y') <<< y' ≠ x' then
    return poison

  val (x'.sshiftRight' y')

def cast {w₁ w₂ : Nat} (x : Int w₁) (h : w₁ = w₂) : Int w₂ :=
  match x with
  | .val v => .val (v.cast h)
  | .poison => .poison

/--
The ‘and’ instruction returns the bitwise logical and of its two operands.

The truth table used for the ‘and’ instruction is:

   In0 In1 Out
    0   0   0
    0   1   0
    1   0   0
    1   1   1
-/
def and {w : Nat} (x y : Int w) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  val (x' &&& y')


/--
The ‘or’ instruction returns the bitwise logical inclusive or of its two operands.

The truth table used for the ‘or’ instruction is:

   In0 In1 Out
    0   0   0
    0   1   1
    1   0   1
    1   1   1

`disjoint` means that for each bit, that bit is zero in at least one of the
inputs. This allows the Or to be treated as an Add since no carry can occur from
any bit. If the `disjoint` keyword is present, the result value of the or is a
poison value if both inputs have a one in the same bit position. For vectors,
any bit. If the `disjoint` argument is true, the result value of the or is a
poison value if both inputs have a one in the same bit position. For vectors,
-/
def or {w : Nat} (x y : Int w) (disjoint : Bool := false) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if disjoint ∧ (x' &&& y') ≠ 0 then
    return poison

  val (x' ||| y')

/--
The `xor` instruction returns the bitwise logical exclusive or of its two
operands. The xor is used to implement the "one's complement" operation, which
is the "~" operator in C.

The truth table used for the ‘xor’ instruction is:

    In0 In1 Out
      0   0   0
      0   1   1
      1   0   1
      1   1   0
-/
def xor {w : Nat} (x y : Int w) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison
  val (x' ^^^ y')

end Int
end
end Veir.Data.LLVM
