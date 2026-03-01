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

def cast {w₁ w₂ : Nat} (x : Int w₁) (h : w₁ = w₂) : Int w₂ :=
  match x with
  | .val v => .val (v.cast h)
  | .poison => .poison

end Int
end
end Veir.Data.LLVM
