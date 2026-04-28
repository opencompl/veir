import Veir.Data.LLVM.Int.Bitblast

namespace Veir.Data.LLVM.Int

example (x y : Int 64) :
    (x.add y) = (y.add x) := by
  simp [llvm_toBitVec]
  bv_decide

example (x : Int 64) :
    x.add (val 0#64) = x := by
  simp [llvm_toBitVec]

example (x y : Int 64) :
    (x.add y) = (y.add x) := by
  simp [llvm_toBitVec]
  bv_decide
