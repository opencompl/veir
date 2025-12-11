module

public import Veir.Dialects.LLVM.Int.Basic

namespace Veir.Dialects.LLVM

namespace Byte

public section

structure Byte (w : Nat) where
  val : BitVec w
  poison : BitVec w
deriving DecidableEq

def xor {w : Nat} (x y : Byte w) : Byte w :=
  ⟨x.val ^^^ y.val, x.poison ||| y.poison⟩

def or {w : Nat} (x y : Byte w) : Byte w :=
  ⟨x.val ||| y.val, x.poison ||| y.poison⟩

def and {w : Nat} (x y : Byte w) : Byte w :=
  ⟨x.val &&& y.val, x.poison ||| y.poison⟩

open Int

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
