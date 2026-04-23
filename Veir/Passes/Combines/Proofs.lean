import Veir.Data.RISCV.Reg.Basic
import Veir.Data.LLVM.Int.Basic
import Veir.Data.RISCV.Reg.Lemmas

/-!
  In this file we prove the correctness of the RISCV combines.
-/

namespace Veir.Data.RISCV
namespace Veir.Data.LLVM


/--
  Prove the correctness of the `right_identity_zero_add` combine.
-/
theorem right_identity_zero_add:
    (RISCV.add lhs (Data.RISCV.li (BitVec.ofInt 64 0))) = lhs := by
  simp [reg_toBitVec]
