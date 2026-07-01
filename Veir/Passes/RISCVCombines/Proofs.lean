import Veir.Data.RISCV.Reg.Basic
import Veir.Data.RISCV.Reg.Lemmas

import Veir.Meta.BVDecide

/-!
  Correctness proofs for the RISC-V combines in `Combine.lean`.
-/

namespace Veir.Data.RISCV

/--
  Prove the correctness of the `right_identity_zero_add` combine.
-/
theorem right_identity_zero_add:
    (RISCV.add lhs (Data.RISCV.li (BitVec.ofInt 64 0))) = lhs := by
  veir_bv_decide

end Veir.Data.RISCV
