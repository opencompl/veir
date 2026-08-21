import Veir.Meta.PBVDecide

example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 13
  · bv_decide
  · grind
