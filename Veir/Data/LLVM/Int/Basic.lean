module

namespace Veir.Data.LLVM

public section

/-- The `Int` type can have any bitwidth `w`. -/
inductive Int (w : Nat) where
/-- A two's complement integer value of width `w`. -/
| val : BitVec w → Int w
/-- A poison value indicating delayed undefined behavior. -/
| poison : Int w
deriving DecidableEq, Inhabited

inductive IntPred where
  | eq
  | ne
  | ugt
  | uge
  | ult
  | ule
  | sgt
  | sge
  | slt
  | sle
deriving DecidableEq, Inhabited, Repr, Hashable

/-- Mapped as in MLIR: https://github.com/llvm/llvm-project/blob/d3417c8bf35852af88f41aa721a719ea756fdd8c/mlir/include/mlir/Dialect/LLVMIR/LLVMEnums.td#L571 -/
def IntPred.fromNat (s : Nat) : Option IntPred :=
  match s with
  | 0 => some .eq
  | 1 => some .ne
  | 2 => some .slt
  | 3 => some .sle
  | 4 => some .sgt
  | 5 => some .sge
  | 6 => some .ult
  | 7 => some .ule
  | 8 => some .ugt
  | 9 => some .uge
  | _ => none

/-- Mapped as in MLIR. See `IntPred.fromNat`. -/
def IntPred.toNat : IntPred → Nat
  | .eq => 0
  | .ne => 1
  | .slt => 2
  | .sle => 3
  | .sgt => 4
  | .sge => 5
  | .ult => 6
  | .ule => 7
  | .ugt => 8
  | .uge => 9

/-- Sanity check: A numeric code parses to a predicate exactly when it is that predicate's MLIR code. -/
theorem IntPred.fromNat_eq_some_iff {n : Nat} {p : IntPred} :
    IntPred.fromNat n = some p ↔ p.toNat = n := by
  cases p <;> simp only [IntPred.fromNat, IntPred.toNat] <;> grind

def IntPred.eval (p : IntPred) (x y : BitVec w) : Bool :=
  match p with
  | .eq => x == y
  | .ne => x != y
  | .ugt => y.ult x
  | .uge => y.ule x
  | .ult => x.ult y
  | .ule => x.ule y
  | .sgt => y.slt x
  | .sge => y.sle x
  | .slt => x.slt y
  | .sle => x.sle y

namespace Int

instance {w : Nat} : ToString (Int w) where
  toString
    | .val v => toString v
    | .poison => "poison"

/-- We define the semantics of a `constant` operation. -/
def constant (w : Nat) (v : _root_.Int) : Int w := val (BitVec.ofInt w v)

/-- The ‘add’ instruction returns the sum of its two operands. -/
def add {w : Nat} (x y : Int w) (nsw : Bool := false) (nuw : Bool := false) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if nsw ∧ BitVec.saddOverflow x' y' then
    return poison

  if nuw ∧ BitVec.uaddOverflow x' y' then
    return poison

  val (x' + y')

/-- The `sub` instruction returns the difference of its two operands. -/
def sub {w : Nat} (x y : Int w) (nsw : Bool := false) (nuw : Bool := false) :
    Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if nsw ∧ BitVec.ssubOverflow x' y' then
    return poison

  if nuw ∧ BitVec.usubOverflow x' y' then
    return poison

  val (x' - y')

/-- The ‘mul’ instruction returns the product of its two operands. -/
def mul {w : Nat} (x y : Int w) (nsw : Bool := false) (nuw : Bool := false) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if nsw ∧ BitVec.smulOverflow x' y' then
    return poison

  if nuw ∧ BitVec.umulOverflow x' y' then
    return poison

  val (x' * y')

/-- The ‘udiv’ instruction returns the unsigned integer quotient of its two operands. -/
def udiv {w : Nat} (x y : Int w) (exact : Bool := false) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if exact ∧ x'.umod y' ≠ 0 then
    return poison

  if y' = 0 then
    return poison

  val (x' / y')

/-- The ‘sdiv’ instruction returns the quotient of its two operands. -/
def sdiv {w : Nat} (x y : Int w) (exact : Bool := false) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if y' == 0 || (x' == (BitVec.intMin w) && y' == -1) then
    return poison

  if exact ∧ x'.smod y' ≠ 0 then
    return poison

  val (x'.sdiv y')

/-- The ‘urem’ instruction returns the unsigned integer remainder from the unsigned division of its two arguments. -/
def urem {w : Nat} (x y : Int w) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if y' == 0 then
    return poison

  val (x' % y')

/-- The ‘srem’ instruction returns the remainder from the signed division of its two operands. -/
def srem {w : Nat} (x y : Int w) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if y' == 0 || (x' == (BitVec.intMin w) && y' == -1) then
    return poison

  val (x'.srem y')

/-- The ‘shl’ instruction returns the first operand shifted to the left by a specified number of bits. -/
def shl {w : Nat} (x y : Int w) (nsw : Bool := false) (nuw : Bool := false) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if y' ≥ w then
    return poison

  if nsw ∧ (x' <<< y').sshiftRight' y' ≠ x' then
    return poison

  if nuw ∧ (x' <<< y') >>> y' ≠ x' then
    return poison

  val (x' <<< y')

/-- The ‘lshr’ instruction (logical shift right) returns the first operand shifted to the right a specified number of bits with zero fill. -/
def lshr {w : Nat} (x y : Int w) (exact : Bool := false) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if y' ≥ w then
    return poison

  if exact ∧ (x' >>> y') <<< y' ≠ x' then
    return poison

  val (x' >>> y')

/-- The ‘ashr’ instruction (arithmetic shift right) returns the first operand shifted to the right a specified number of bits with sign extension. -/
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

@[simp, grind =]
theorem cast_self {w : Nat} (x : Int w) (h : w = w) : cast x h = x := by
  cases x <;> simp [cast]

/-- The ‘and’ instruction returns the bitwise logical and of its two operands. -/
def and {w : Nat} (x y : Int w) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  val (x' &&& y')


/-- The ‘or’ instruction returns the bitwise logical inclusive or of its two operands. -/
def or {w : Nat} (x y : Int w) (disjoint : Bool := false) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison

  if disjoint ∧ (x' &&& y') ≠ 0 then
    return poison

  val (x' ||| y')

/-- The `xor` instruction returns the bitwise logical exclusive or of its two operands. -/
def xor {w : Nat} (x y : Int w) : Int w := Id.run do
  let val x' := x | poison
  let val y' := y | poison
  val (x' ^^^ y')

/-- The `trunc` instruction truncates the high order bits in value and converts the remaining bits to `w₂`. -/
def trunc {w₁ : Nat} (x : Int w₁) (w₂ : Nat) (nsw : Bool := false) (nuw : Bool := false) (_h : w₁ > w₂) : Int w₂ := Id.run do
  let val v := x | poison

  if nsw && (v.truncate w₂).signExtend w₁ ≠ v then
    return poison

  if nuw && (v.truncate w₂).zeroExtend w₁ ≠ v then
    return poison

  val (v.truncate w₂)

/-- The 'zext' instruction zero-extends its operand to the given type. -/
def zext {w₁ : Nat} (x : Int w₁) (w₂ : Nat) (nneg : Bool := false) (_h : w₁ < w₂) : Int w₂ := Id.run do
  let val v := x | poison

  if nneg && v.msb then
    return poison

  val (v.zeroExtend w₂)

/-- The `sext` instruction sign-extends its operand to the given type. -/
def sext {w₁ : Nat} (x : Int w₁) (w₂ : Nat) (_h : w₁ < w₂) : Int w₂ := Id.run do
  let val v := x | poison

  val (v.signExtend w₂)

/-- The `icmp` instruction takes three operands. -/
def icmp {w : Nat} (x y : Int w) (p : IntPred) : Int 1 := Id.run do
  let val x' := x | poison
  let val y' := y | poison
  val (BitVec.ofBool (IntPred.eval p x' y'))

/-- If the condition is an i1 and it evaluates to 1, the instruction returns the first value argument; otherwise, it returns the second value argument. -/
def select {w : Nat} (c : Int 1) (x y : Int w) : Int w := Id.run do
  let val c' := c | poison
  if c' == 1#1 then x else y

end Int
end
end Veir.Data.LLVM
