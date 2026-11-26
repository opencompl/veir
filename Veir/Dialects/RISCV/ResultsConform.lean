module

public import Veir.Interpreter.ResultsConform
import Veir.Dialects.RISCV.VerifierLemmas

import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV.Interpreter

public section

/-!
# The results of RISC-V operations conform to their types

Every result of a RISC-V operation is a register, the verifier makes every result type
`!riscv.reg`, and a store has no result where every other opcode has one.

A load interprets a CTree of its own, which chooses the bits of the loaded value that memory marks
poison, since a register cannot carry poison. Whatever it chooses, the result is a single register.
-/

open CTree

namespace Veir

/--
Registers, as many as the operation has results, conform to the result types of an operation
that `verifyRISCVRegisterTypes` accepts.
-/
theorem OperationPtr.arrayConforms_of_verifyRISCVRegisterTypes {OpInfo : Type} [HasOpInfo OpInfo]
    {op : OperationPtr} {ctx : WfIRContext OpInfo} {opIn : op.InBounds ctx.raw}
    {vals : Array RuntimeValue} (h : op.verifyRISCVRegisterTypes ctx opIn = .ok ())
    (hs : vals.size = op.getNumResults! ctx.raw) (hr : ∀ v ∈ vals, ∃ r, v = .reg r) :
    RuntimeValue.ArrayConforms vals (op.getResultTypes! ctx.raw) := by
  refine .of_getResult hs fun i hi => ?_
  obtain ⟨rt, hT⟩ := verifyRISCVRegisterTypes_eq_ok h i (hs ▸ hi)
  exact hT ▸ RuntimeValue.Conforms.registerType.mpr (hr _ (Array.getElem_mem hi))

/-- The number of results of a RISC-V opcode: none for a store, one otherwise. -/
private def Riscv.numResults : Riscv → Nat
  | .sd | .sw | .sh | .sb => 0
  | _ => 1

/-- A verified RISC-V operation has as many results as its opcode. -/
private theorem Riscv.verifyLocalInvariants_numResults {OpInfo : Type} [HasOpInfo OpInfo]
    [HasDialect OpInfo Riscv] {op : OperationPtr} {ctx : WfIRContext OpInfo}
    {opIn : op.InBounds ctx.raw} {opT : Riscv}
    (h : Riscv.verifyLocalInvariants opT op ctx opIn = .ok ()) :
    op.getNumResults! ctx.raw = opT.numResults := by
  unfold Riscv.verifyLocalInvariants at h
  have h' := Except.ok_of_bind_ok h
  cases opT <;>
    first
      | exact OperationPtr.verifyPlainOpCounts_eq_ok (Except.ok_left_of_bind_ok h')
      | exact OperationPtr.verifyPlainOpCounts_eq_ok
          (Except.ok_left_of_bind_ok (Except.ok_left_of_bind_ok h'))

/-- A RISC-V load returns a single register, whatever bits it chooses. -/
private theorem riscvLoadCTree_mayReturn {EIn : Type} {E : EIn → Type} [ErrorE -< E] [UBE -< E]
    {imm12 : BitVec 12} {operands : Array RuntimeValue} {mem mem' : MemoryState} {bytes : Nat}
    {ext : LoadExtension} {vals : Array RuntimeValue} {act : Option ControlFlowAction}
    (h : CTree.MayReturn (riscvLoadCTree (E := E) imm12 operands mem bytes ext)
      (vals, mem', act)) :
    ∃ r, vals = #[.reg r] := by
  simp only [riscvLoadCTree] at h
  split at h <;> grind

/-- A RISC-V operation returns as many registers as its opcode has results. -/
private theorem Riscv.interpretOpCTree_mayReturn {EIn : Type} {E : EIn → Type} [ErrorE -< E]
    [UBE -< E] {opT : Riscv} {properties : propertiesOf opT} {resultTypes : Array TypeAttr}
    {operands : Array RuntimeValue} {bs : Array BlockPtr} {mem mem' : MemoryState}
    {vals : Array RuntimeValue} {act : Option ControlFlowAction}
    (h : CTree.MayReturn (Riscv.interpretOpCTree (E := E) opT properties resultTypes operands bs
      mem) (vals, mem', act)) :
    vals.size = opT.numResults ∧ ∀ v ∈ vals, ∃ r, v = .reg r := by
  have : (∃ r, vals = #[.reg r]) ∧ opT.numResults = 1 ∨ vals = #[] ∧ opT.numResults = 0 := by
    cases opT <;>
      simp only [Riscv.interpretOpCTree, CTree.MayReturn.monadLift_iff, Riscv.interpretOp']
        at h <;>
      first
        | exact .inl ⟨riscvLoadCTree_mayReturn h, rfl⟩
        | grind [Riscv.numResults]
  rcases this with ⟨⟨r, rfl⟩, hn⟩ | ⟨rfl, hn⟩ <;> simp [hn]

/-- The results of a CTree run of every RISC-V opcode conform to their types. -/
theorem OpCode.resultsConform_riscv (opT : Riscv) : OpCode.ResultsConform (.riscv opT) := by
  refine OpCode.resultsConform_def!.mpr
    fun ctx op opIn hType hV operands mem _ vals mem' act h => ?_
  have hVL : Riscv.verifyLocalInvariants opT op ctx opIn = .ok () :=
    hV.verifyLocalInvariants_eq_ok hType
  have ⟨hs, hr⟩ := Riscv.interpretOpCTree_mayReturn (CTree.interpretOp'_riscv .. ▸ h)
  exact OperationPtr.arrayConforms_of_verifyRISCVRegisterTypes (Except.ok_left_of_bind_ok hVL)
    (hs.trans (Riscv.verifyLocalInvariants_numResults hVL).symm) hr

instance (op : Riscv) : ResultsConform (.riscv op) := ⟨OpCode.resultsConform_riscv op⟩

end Veir

end
