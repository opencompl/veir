module

public import Veir.Dialects.RISCV.ResultsConform
public import Veir.Interpreter.ResultsConform

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.RISCV.Interpreter

public section

/-!
# The results of a CTree run of a RISC-V operation conform to their types

A RISC-V opcode that is not a load runs its `Interp` semantics in a CTree, so the conformance of
the results its CTree produces follows from `Riscv.interpretOp'_results_conform`.

A load interprets a CTree of its own, which chooses the bits of the loaded value that memory
marks poison, since a register cannot carry poison. Whatever it chooses, the result is a single
register, and `Riscv.regs_results_conform` asks no more than that.
-/

open CTree

namespace Veir

/-- A RISC-V opcode that is not a load runs its `Interp` semantics. -/
private theorem riscv_interpretOp'_ctree_eq_lift {opT : Riscv} (hLoad : opT.isLoad = false)
    (properties : propertiesOf (OpCode.riscv opT)) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (bs : Array BlockPtr) (mem : MemoryState)
    (regions : Array RegionPtr) :
    CTree.interpretOp' (.riscv opT) properties resultTypes operands bs mem regions =
      monadLift (Veir.interpretOp' (.riscv opT) properties resultTypes operands bs mem) := by
  cases opT <;>
    simp_all [CTree.interpretOp', Veir.interpretOp', Riscv.interpretOpCTree,
      Riscv.isLoad_eq]

/-- A RISC-V load returns a single register in CTrees, whatever bits it chooses. -/
private theorem riscvLoadCTree_ok_reg {imm12 : BitVec 12} {operands : Array RuntimeValue}
    {mem : MemoryState} {bytes : Nat} {ext : LoadExtension} {vals : Array RuntimeValue}
    {mem' : MemoryState} {act : Option ControlFlowAction}
    (h : CTree.MayReturn
      (riscvLoadCTree (E := ErrorE ⊕ₑ UBE) imm12 operands mem bytes ext)
      (vals, mem', act)) :
    ∃ r, vals = #[.reg r] := by
  simp only [riscvLoadCTree] at h
  split at h
  · simp only [Bind.bind, CTree.MayReturn.bind_iff,
      CTree.MayReturn.monadLift_iff, CTree.MayReturn.choose_iff,
      CTree.MayReturn.pure_iff, Prod.mk.injEq] at h
    obtain ⟨b, -, bits, -, rfl, -, -⟩ := h
    exact ⟨_, rfl⟩
  · simp only [CTree.MayReturn.fail_iff] at h

/-- The results of a CTree run of every RISC-V opcode conform to their types. -/
theorem OpCode.resultsConform_riscv (opT : Riscv) : OpCode.ResultsConform (.riscv opT) := by
  refine OpCode.resultsConform_def.mpr
    fun ctx op opIn hType hV operands mem _ vals mem' act h => ?_
  have hType! : op.getOpType! ctx.raw = .riscv opT := by
    rw [OperationPtr.getOpType!_eq_getOpType opIn]; exact hType
  rw [OperationPtr.interpretCTree_def!, hType!] at h
  cases hLoad : opT.isLoad
  · rw [riscv_interpretOp'_ctree_eq_lift hLoad,
      CTree.MayReturn.monadLift_iff] at h
    simp only [Veir.interpretOp'] at h
    exact Riscv.interpretOp'_results_conform opT hType! hV h
  · obtain ⟨r, rfl⟩ : ∃ r, vals = #[.reg r] := by
      cases opT <;>
        first
          | exact riscvLoadCTree_ok_reg
              (by simpa only [CTree.interpretOp', Riscv.interpretOpCTree] using h)
          | simp [Riscv.isLoad_eq] at hLoad
    refine Riscv.regs_results_conform opT hType! hV ?_ (by simp)
    rw [Riscv.numResults_of_isLoad hLoad]; simp

instance (op : Riscv) : ResultsConform (.riscv op) := ⟨OpCode.resultsConform_riscv op⟩

end Veir

end
