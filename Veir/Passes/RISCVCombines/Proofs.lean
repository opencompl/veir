import Veir.Data.RISCV.Reg.Basic
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Data.LLVM.Int.Basic
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.LLVM.Int.Bitblast
import Veir.Data.Casting
import Veir.Data.Refinement

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
  Prove the correctness of the `srl_sra_signbit` combine, phrased at the LLVM
  level (the combine itself fires on already-selected `riscv.srai`/`riscv.srli`,
  but the fact it relies on is a generic, division-agnostic property of `ashr`
  followed by `lshr`): an arithmetic right shift by any amount `shamt` -- even an
  out-of-range one, where `ashr` itself is poison and the refinement holds
  trivially -- never changes the top bit, so a subsequent logical shift by 63
  (which keeps only that bit) gives the same result as skipping the `ashr`
  entirely. Mirrors LLVM's generic `DAGCombiner::visitSRL` rule
  `fold (srl (sra X, Y), 31) -> (srl X, 31)`.
  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L11628-L11633
-/
theorem srl_sra_signbit_refinement {x shamt : LLVM.Int 64} :
    (Data.LLVM.Int.lshr (Data.LLVM.Int.ashr x shamt) (LLVM.Int.constant 64 63)) ⊒
      (Data.LLVM.Int.lshr x (LLVM.Int.constant 64 63)) := by
  veir_bv_decide

/--
  Prove the correctness of the `srlw_sraw_signbit` combine (the `i32` analogue of
  `srl_sra_signbit_refinement`, at bit 31).
-/
theorem srlw_sraw_signbit_refinement {x shamt : LLVM.Int 32} :
    (Data.LLVM.Int.lshr (Data.LLVM.Int.ashr x shamt) (LLVM.Int.constant 32 31)) ⊒
      (Data.LLVM.Int.lshr x (LLVM.Int.constant 32 31)) := by
  veir_bv_decide

end Veir.Data.RISCV
