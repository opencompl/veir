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

def add {w : Nat} : (x y : Int w) → Int w
| .val x, .val y => .val (x + y)
| _, _ => .poison

instance {w : Nat} : Add (Int w) := ⟨add⟩

def mul {w : Nat} : (x y : Int w) → Int w
| .val x, .val y => .val (x * y)
| _, _ => .poison

instance {w : Nat} : Mul (Int w) := ⟨mul⟩

def cast {w₁ w₂ : Nat} (x : Int w₁) (h : w₁ = w₂) : Int w₂ :=
  match x with
  | .val v => .val (v.cast h)
  | .poison => .poison

end Int
end
end Veir.Data.LLVM
