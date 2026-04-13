module

namespace Veir.Dialects.LLVM.Int

namespace IntBv

public section

structure IntBv (w : Nat) where
  /-- A two's complement integer value of width `w`. -/
  val : BitVec w
  /-- A poison flag. If true, the value is considered poison. -/
  poison : Bool
  h : poison → val == 0 := by simp
deriving DecidableEq

@[expose, bv_normalize]
def mk_poison {w : Nat} : IntBv w :=
  ⟨0, true, by simp⟩

@[expose, bv_normalize]
def mk_val {w : Nat} (val : BitVec w) : IntBv w :=
  ⟨val, false, by simp⟩

@[expose]
def add (x y : IntBv w) : IntBv w :=
  if x.poison || y.poison then
    mk_poison
  else
    mk_val (x.val + y.val)

instance {w : Nat} : Add (IntBv w) := ⟨add⟩

open Int

end

end IntBv

end Veir.Dialects.LLVM.Int
