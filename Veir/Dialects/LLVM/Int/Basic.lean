module

namespace Veir.Dialects.LLVM.Int

public section

inductive Int (w : Nat) where
| val : BitVec w → Int w
| poison : Int w
deriving DecidableEq

def add {w : Nat} : (x y : Int w) → Int w
| .val x, .val y => .val (x + y)
| _, _ => .poison

instance {w : Nat} : Add (Int w) := ⟨add⟩

def mul {w : Nat} : (x y : Int w) → Int w
| .val x, .val y => .val (x * y)
| _, _ => .poison

instance {w : Nat} : Mul (Int w) := ⟨mul⟩

end

end Veir.Dialects.LLVM.Int
