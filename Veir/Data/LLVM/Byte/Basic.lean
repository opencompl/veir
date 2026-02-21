module

public import Veir.Data.LLVM.Int.Basic

namespace Veir.Data.LLVM

namespace Byte

public section

/--
The `Byte` type can have any bitwidth `w`. It carries a two's complement integer
value of width `w` and a per-bit poison mask modeling bitwise delayed undefined
behavior.
-/
structure Byte (w : Nat) where
  /-- A two's complement integer value of width `w`. -/
  val : BitVec w
  /-- A per-bit poison mask of width `w`. -/
  poison : BitVec w
  /-- Invariant: if a bit is poison, the corresponding bit in `val` is zero. -/
  h : val &&& poison = 0
deriving DecidableEq

def and (x y : Byte w) : Byte w :=
  let poison := x.poison ||| y.poison
  ⟨(x.val &&& y.val) &&& ~~~poison, poison, by simp [BitVec.and_assoc]⟩

instance {w : Nat} : AndOp (Byte w) := ⟨and⟩

def or (x y : Byte w) : Byte w :=
  let poison := x.poison ||| y.poison
  ⟨(x.val ||| y.val) &&& ~~~poison, poison, by simp [BitVec.and_assoc]⟩

instance {w : Nat} : OrOp (Byte w) := ⟨or⟩

def xor (x y : Byte w) : Byte w :=
  let poison := x.poison ||| y.poison
  ⟨(x.val ^^^ y.val) &&& ~~~poison, poison, by simp [BitVec.and_assoc]⟩

instance {w : Nat} : XorOp (Byte w) := ⟨xor⟩

open Int

/-- Convert from `Byte` and `Int`.
  A byte where no bit is poison is equal to an integer value.
  If any bit is poison, the integer type is also poison.
-/
def Byte.toInt {w : Nat} (x : Byte w) : Int w :=
  if x.poison = 0 then
    .val x.val
  else
    .poison

def fromInt {w : Nat} (x : Int w) : Byte w :=
  if let .val x := x then
    ⟨x, 0, by simp⟩
  else
    ⟨0, BitVec.allOnes w, by simp⟩
end

end Byte
