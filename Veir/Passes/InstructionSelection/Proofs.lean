module

public import Veir.Data.RISCV.Reg.Basic
public import Veir.Data.LLVM.Int.Basic
public import Veir.Data.LLVM.Ptr.Basic
public import Veir.Data.Casting
public import Veir.Dialects.GMIR.Semantics

meta import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide.Reflect
meta import Veir.Meta.Tactic.PBVDecide

import Veir.ForLean
import all Veir.Data.RISCV.Reg.Basic
import all Veir.Data.RISCV.Reg.Lemmas
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Int.Lemmas
import all Veir.Data.LLVM.Int.Bitblast
import all Veir.Dialects.GMIR.Semantics
import all Veir.Data.Casting

public section

/-!
  The correctness lemmas of the instruction-selection lowerings that the CTree validity proofs
  of `Veir.Passes.InstructionSelection.Proofs.RISCV64` and `Veir.Passes.InstructionSelection.Validity`
  use.
-/

namespace Veir.Data.RISCV

/--
  Prove the correctness of the `constant` lowering pattern at every width `w ≤ 64`: the
  constant is truncated to `w` bits and sign-extended to the 64-bit `li` immediate, whose
  low `w` bits are then exactly the constant.
-/
theorem constant_refinement_le64 {w : Nat} (h : w ≤ 64) {v : Int} :
    (LLVM.Int.constant w v) ⊒
      (RISCV.Reg.toInt (Data.RISCV.li ((BitVec.ofInt w v).signExtend 64)) w) := by
  simp only [LLVM.Int.isRefinedBy, LLVM.Int.constant, RISCV.Reg.toInt, RISCV.li]
  generalize BitVec.ofInt w v = x
  pbv_decide 64

/--
  Prove the correctness of the `trunc` lowering pattern at every pair of widths `w₂ < w₁ ≤ 64`:
  the operand is zero-extended into a register and the low `w₂` bits are read back. The
  `nsw`/`nuw` flags only add poison cases, which any register value refines.
-/
theorem trunc_refinement_le64 {w₁ w₂ : Nat} (hw : w₁ ≤ 64) {x : LLVM.Int w₁} {nsw nuw : Bool}
    {h : w₁ > w₂} :
    (Data.LLVM.Int.trunc x w₂ nsw nuw h) ⊒ (RISCV.Reg.toInt (LLVM.Int.toReg x) w₂) := by
  veir_pbv_decide 64

/--
  Prove the correctness of the `gmirAnyextOfReg` lowering pattern, at every width: the high bits of
  `g_anyext` may be chosen as those of the register, so it is refined by a single cast from it.
-/
theorem anyext_of_reg_refinement (n m : Nat) (h : n < m) (r : Reg) :
    ∃ ext : BitVec (m - n),
      LLVM.Int.ext (RISCV.Reg.toInt r n) m ext h ⊒ RISCV.Reg.toInt r m :=
  ⟨(r.val.zeroExtend m).extractLsb' n (m - n), by
    veir_bv_normalize
    simp [BitVec.eq_of_getElem_eq_iff, BitVec.getElem_append]
    grind⟩

/--
  A `g_load` of `n` bits `v` into an `i64` is refined by any register whose low `n` bits are `v`,
  such as the result of `lbu`, `lh` or `lw` (see `gmirLoad_pattern`).
-/
theorem gmir_load_refinement {n : Nat} (h : n < 64) (v : BitVec n) (r : Reg)
    (hlow : r.val.setWidth n = v) :
    ∃ ext : BitVec (64 - n), LLVM.Int.ext (.val v) 64 ext h ⊒ RISCV.Reg.toInt r 64 := by
  have hv : RISCV.Reg.toInt r n = .val v := by simp [RISCV.Reg.toInt, ← hlow]
  simpa [hv] using anyext_of_reg_refinement n 64 h r
