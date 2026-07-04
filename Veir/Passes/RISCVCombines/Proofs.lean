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

/--
  Prove the correctness of the `srl_sra_signbit` combine, phrased directly on the
  already-selected RISC-V register ops the combine rewrites: `riscv.srli 63
  (riscv.srai shamt x) = riscv.srli 63 x`. An arithmetic right shift by any amount
  `shamt` never changes the top bit, so a subsequent logical shift by 63 (which
  keeps only that bit) gives the same result as skipping the `srai` entirely. The
  RISC-V ops are total, so this is an exact equality. Mirrors LLVM's generic
  `DAGCombiner::visitSRL` rule `fold (srl (sra X, Y), 31) -> (srl X, 31)`.
  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L11628-L11633
-/
theorem srl_sra_signbit {x : Reg} {shamt : BitVec 6} :
    RISCV.srli 63 (RISCV.srai shamt x) = RISCV.srli 63 x := by
  veir_bv_decide

/--
  Prove the correctness of the `srlw_sraw_signbit` combine (the `i32` analogue of
  `srl_sra_signbit`, at bit 31): `riscv.srliw 31 (riscv.sraiw shamt x) =
  riscv.srliw 31 x`.
-/
theorem srlw_sraw_signbit {x : Reg} {shamt : BitVec 5} :
    RISCV.srliw 31 (RISCV.sraiw shamt x) = RISCV.srliw 31 x := by
  veir_bv_decide

end Veir.Data.RISCV
