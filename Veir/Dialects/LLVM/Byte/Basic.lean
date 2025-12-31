module

public import Veir.Dialects.LLVM.Int.Basic

namespace Veir.Dialects.LLVM

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

def xor {w : Nat} (x y : Byte w) : Byte w :=
  ⟨x.val ^^^ y.val, x.poison ||| y.poison⟩

def or {w : Nat} (x y : Byte w) : Byte w :=
  ⟨x.val ||| y.val, x.poison ||| y.poison⟩

def and {w : Nat} (x y : Byte w) : Byte w :=
  ⟨x.val &&& y.val, x.poison ||| y.poison⟩

open Int

/-- Convert from `Byte` and `Int`.
  A byte where no bit is poison is equal to an integer value.
  If any bit is poison, the integer type is also poison.
-/
def toInt {w : Nat} (x : Byte w) : Int w :=
  if x.poison = 0 then
    .val x.val
  else
    .poison

def fromInt {w : Nat} (x : Int w) : Byte w :=
  if let .val x := x then
    ⟨x, 0⟩
  else
    ⟨0, BitVec.allOnes w⟩

end

end Byte
