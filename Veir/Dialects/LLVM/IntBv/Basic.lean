module

namespace Veir.Dialects.LLVM.IntBv

public section

/--
The `IntBv` type is either a two's complement integer value of width `w` or a poison value indicating delayed undefined behavior.
-/
structure IntBv (w : Nat) where
  /-- A two's complement integer value of width `w`. -/
  val : BitVec w
  /-- A poison flag for `w`. -/
  poison : Bool
  /-- Invariant: If this value is poison the `val` is zero. -/
  h : poison → (val = 0) := by simp
deriving DecidableEq

def IntBv.mkPoison (w : Nat) : IntBv w :=
  ⟨0, true, by simp⟩

def IntBv.mkVal {w : Nat} (val : BitVec w): IntBv w :=
  ⟨val, false, by simp⟩

def add {w : Nat} (x y : IntBv w) : IntBv w :=
  if x.poison || y.poison then
    IntBv.mkPoison
  else
    IntBv.mkVal (x.val + y.val)

instance {w : Nat} : Add (IntBv w) := ⟨add⟩

def mul {w : Nat} (x y : IntBv w) : IntBv w :=
  if x.poison || y.poison then
    IntBv.mkPoison
  else
    IntBv.mkVal (x.val * y.val)

instance {w : Nat} : Mul (IntBv w) := ⟨mul⟩

end

end Veir.Dialects.LLVM.IntBv
