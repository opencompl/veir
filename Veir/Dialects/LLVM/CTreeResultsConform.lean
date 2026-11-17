module

public import Veir.Dialects.LLVM.ResultsConform
public import Veir.Interpreter.ResultsConform

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.LLVM.Interpreter

public section

/-!
# The results of a CTree run of an LLVM operation conform to their types

Every LLVM opcode but `llvm.freeze` runs its `Interp` semantics in a CTree, so the conformance of
the results its CTree produces follows from `Llvm.interpretOp'_results_conform`. `llvm.freeze`
interprets a CTree of its own, which chooses a value where its operand carries poison. Every value
it may choose has the shape of the operand, whose type the verifier matches to the result type, so
each of them conforms.
-/

open CTree

namespace Veir

/-- An LLVM opcode but `freeze` runs its `Interp` semantics in a CTree. -/
private theorem llvm_interpretOp'_ctree_eq_lift {opT : Llvm} (hf : opT ≠ .freeze)
    (properties : propertiesOf (OpCode.llvm opT)) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (bs : Array BlockPtr) (mem : MemoryState)
    (regions : Array RegionPtr) :
    CTree.interpretOp' (.llvm opT) properties resultTypes operands bs mem regions =
      monadLift (Veir.interpretOp' (.llvm opT) properties resultTypes operands bs mem) := by
  cases opT <;> simp_all [CTree.interpretOp', Veir.interpretOp', Llvm.interpretOpCTree]

/-- Every result the CTree of a verified `llvm.freeze` can produce conforms to its result type. -/
private theorem freeze_results_conform {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opIn : op.InBounds ctx.raw} {operands vals : Array RuntimeValue} {mem mem' : MemoryState}
    {act : Option ControlFlowAction} {bs : Array BlockPtr} {regions : Array RegionPtr}
    {properties : propertiesOf (OpCode.llvm Llvm.freeze)}
    (hType : op.getOpType! ctx.raw = .llvm .freeze) (hV : op.Verified ctx opIn)
    (hConf : RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw))
    (h : CTree.MayReturn
      (CTree.interpretOp' (.llvm .freeze) properties (op.getResultTypes! ctx.raw) operands bs mem
        regions) (vals, mem', act)) :
    RuntimeValue.ArrayConforms vals (op.getResultTypes! ctx.raw) := by
  simp only [CTree.interpretOp', Llvm.interpretOpCTree] at h
  split at h
  · next val hOps =>
    obtain ⟨hR, h0⟩ := Llvm.freeze_verified_operand_conforms hType hV hConf hOps
    repeat' split at h
    all_goals try simp only [Bind.bind, CTree.MayReturn.bind_iff,
      CTree.MayReturn.choose_iff, CTree.MayReturn.pure_iff,
      CTree.MayReturn.fail_iff, Prod.mk.injEq, true_and] at h
    all_goals
      first
        | obtain ⟨rfl, -, -⟩ := h
        | obtain ⟨-, rfl, -, -⟩ := h
    all_goals
      first
        | exact results_one hR (int_conforms h0)
        | exact results_one hR (byte_conforms h0)
        | exact results_one hR (addr_conforms h0)
  · simp only [CTree.MayReturn.fail_iff] at h

/-- The results of a CTree run of every LLVM opcode conform to their types. -/
theorem OpCode.resultsConform_llvm (opT : Llvm) : OpCode.ResultsConform (.llvm opT) := by
  refine OpCode.resultsConform_def.mpr
    fun ctx op opIn hType hV operands mem hConf vals mem' act h => ?_
  have hType! : op.getOpType! ctx.raw = .llvm opT := by
    rw [OperationPtr.getOpType!_eq_getOpType opIn]; exact hType
  rw [OperationPtr.interpretCTree_def!, hType!] at h
  by_cases hf : opT = .freeze
  · subst hf
    exact freeze_results_conform hType! hV hConf h
  · rw [llvm_interpretOp'_ctree_eq_lift hf,
      CTree.MayReturn.monadLift_iff] at h
    simp only [Veir.interpretOp'] at h
    exact Llvm.interpretOp'_results_conform opT hType! hV hConf h

/-- The results of a CTree run of an LLVM operation conform to its result types. -/
theorem Llvm.interpretCTree_results_conform {llvmOp : Llvm} {op : OperationPtr}
    {ctx : WfIRContext OpCode} {opIn : op.InBounds ctx.raw}
    (hType : op.getOpType ctx.raw opIn = .llvm llvmOp)
    (opVerif : op.Verified ctx opIn)
    (conforms : RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw))
    (h : CTree.MayReturn (op.interpretCTree opIn operands mem)
      (vals, mem', act)) :
    RuntimeValue.ArrayConforms vals (op.getResultTypes! ctx.raw) :=
  _root_.Veir.interpretCTree_results_conform (hType ▸ OpCode.resultsConform_llvm llvmOp)
    opVerif conforms h

open Lean Elab Command in
/--
Give every LLVM opcode its `ResultsConform` instance, so that instance resolution finds the proof
rather than `OpCode.resultsConform_assumed`. An opcode added to the dialect gets its instance
here, and fails loudly if its CTree neither runs its `Interp` semantics nor returns only values
that conform.
-/
local elab "llvm_results_conform_instances" : command => do
  let info ← getConstInfoInduct ``Llvm
  for ctor in info.ctors do
    elabCommand (← `(command|
      instance : ResultsConform (.llvm $(mkIdent ctor)) := ⟨OpCode.resultsConform_llvm _⟩))

llvm_results_conform_instances

/--
Instance resolution proves, rather than assumes, the conformance of the results of the CTree of
every LLVM opcode. No LLVM opcode is carved out.

The catch-all instance is not in scope here, as the module that declares it imports this one.
`cf_resultsConform_not_assumed` pins that resolution takes such a proof over the assumption.
-/
theorem llvm_resultsConform_not_assumed (op : Llvm) : ResultsConform (.llvm op) := by
  cases op <;> exact inferInstance

/--
info: 'Veir.llvm_resultsConform_not_assumed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms llvm_resultsConform_not_assumed

/--
info: 'Veir.Llvm.interpretCTree_results_conform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Llvm.interpretCTree_results_conform

end Veir

end
