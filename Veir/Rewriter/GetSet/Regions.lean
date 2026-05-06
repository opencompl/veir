module

public import Veir.IR.Basic
public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic

import Veir.Rewriter.LinkedList.GetSet
import Veir.ForLean
import Veir.IR.DeallocLemmas

public section

/-
 - The getters we consider are:
 - * BlockPtr.get! optionally replaced by the following special cases:
 -   * Block.firstUse
 -   * Block.prev
 -   * Block.next
 -   * Block.parent
 -   * Block.firstOp
 -   * Block.lastOp
 - * OperationPtr.get! optionally replaced by the following special cases:
 -   * Operation.prev
 -   * Operation.next
 -   * Operation.parent
 -   * OperationPtr.getOpType!
 -   * Operation.attrs
 - * OperationPtr.getProperties!
 - * OperationPtr.getNumResults!
 - * OpResultPtr.get!
 - * OperationPtr.getNumOperands!
 - * OpOperandPtr.get! optionally replaced by the following special case:
 - * OperationPtr.getOperands!
 - * OperationPtr.getNumSuccessors!
 - * BlockOperandPtr.get!
 - * OperationPtr.getSuccessor!
 - * OperationPtr.getSuccessors!
 - * OperationPtr.getNumRegions!
 - * OperationPtr.getRegion!
 - * BlockOperandPtrPtr.get!
 - * BlockPtr.getNumArguments!
 - * BlockArgumentPtr.get!
 - * RegionPtr.get! with optionally special cases for:
 -   * firstBlock
 -   * lastBlock
 -   * parent
 - * ValuePtr.getFirstUse!
 - * ValuePtr.getType!
 - * OpOperandPtrPtr.get!
 -/

namespace Veir

variable {OpInfo} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}
/-! ## `Rewriter.pushRegion` -/

section Rewriter.pushRegion

variable {op : OperationPtr}

attribute [local grind] Rewriter.pushRegion

@[simp, grind =]
theorem BlockPtr.get!_pushRegion {block : BlockPtr} :
    block.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_pushRegion {operation : OperationPtr} :
    (operation.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_pushRegion {operation : OperationPtr} :
    (operation.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_pushRegion {operation : OperationPtr} :
    (operation.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_pushRegion {operation : OperationPtr} :
    operation.getOpType! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_pushRegion {operation : OperationPtr} :
    (operation.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_pushRegion {operation : OperationPtr} :
    operation.getProperties! (Rewriter.pushRegion ctx op region hop hregion hregionParent) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_pushRegion {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_pushRegion {opResult : OpResultPtr} :
    opResult.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_pushRegion {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_pushRegion {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_pushRegion {operation : OperationPtr} :
    operation.getOperands! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_pushRegion {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_pushRegion {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_pushRegion {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.pushRegion ctx op region hop hregion hregionParent) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_pushRegion {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[grind =]
theorem OperationPtr.getNumRegions!_pushRegion {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    if operation = op then operation.getNumRegions! ctx + 1
    else operation.getNumRegions! ctx := by
  grind

@[grind =]
theorem OperationPtr.getRegion!_pushRegion {operation : OperationPtr} :
    operation.getRegion! (Rewriter.pushRegion ctx op region hop hregion hregionParent) index =
    if operation = op ∧ index = operation.getNumRegions! ctx then region
    else operation.getRegion! ctx index := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_pushRegion {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_pushRegion {block : BlockPtr} :
    block.getNumArguments! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.firstBlock!_pushRegion {r : RegionPtr} :
    (r.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).firstBlock =
    (r.get! ctx).firstBlock := by
  grind

@[simp, grind =]
theorem RegionPtr.lastBlock!_pushRegion {r : RegionPtr} :
    (r.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).lastBlock =
    (r.get! ctx).lastBlock := by
  grind

@[grind =]
theorem RegionPtr.parent!_pushRegion {r : RegionPtr} :
    (r.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).parent =
    if r = region then some op else (r.get! ctx).parent := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_pushRegion {value : ValuePtr} :
    value.getFirstUse! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_pushRegion {value : ValuePtr} :
    value.getType! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_pushRegion {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    opOperandPtr.get! ctx := by
  grind

end Rewriter.pushRegion
/-! ## `Rewriter.initOpRegions` -/

section Rewriter.initOpRegions

variable {op : OperationPtr}

attribute [local grind] Rewriter.initOpRegions

@[simp, grind =>]
theorem BlockPtr.get!_initOpRegions {block : BlockPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    block.get! ctx' = block.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem OperationPtr.prev!_initOpRegions {operation : OperationPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    (operation.get! ctx').prev = (operation.get! ctx).prev := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem OperationPtr.next!_initOpRegions {operation : OperationPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    (operation.get! ctx').next = (operation.get! ctx).next := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem OperationPtr.parent!_initOpRegions {operation : OperationPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    (operation.get! ctx').parent = (operation.get! ctx).parent := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem OperationPtr.getOpType!_initOpRegions {operation : OperationPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getOpType! ctx' = operation.getOpType! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem OperationPtr.attrs!_initOpRegions {operation : OperationPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    (operation.get! ctx').attrs = (operation.get! ctx).attrs := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem OperationPtr.getProperties!_initOpRegions {operation : OperationPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getProperties! ctx' opCode = operation.getProperties! ctx opCode := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem OperationPtr.getNumResults!_initOpRegions {operation : OperationPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getNumResults! ctx' = operation.getNumResults! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem OperationPtr.getNumOperands!_initOpRegions {operation : OperationPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getNumOperands! ctx' = operation.getNumOperands! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem OpResultPtr.get!_initOpRegions {opResult : OpResultPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    opResult.get! ctx' = opResult.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem OpOperandPtr.get!_initOpRegions {opOperand : OpOperandPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    opOperand.get! ctx' = opOperand.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem OperationPtr.getOperands!_initOpRegions {operation : OperationPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getOperands! ctx' = operation.getOperands! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem OperationPtr.getNumSuccessors!_initOpRegions {operation : OperationPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getNumSuccessors! ctx' = operation.getNumSuccessors! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem BlockOperandPtr.get!_initOpRegions {blockOperand : BlockOperandPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    blockOperand.get! ctx' = blockOperand.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem OperationPtr.getSuccessor!_initOpRegions {operation : OperationPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    operation.getSuccessor! ctx' i = operation.getSuccessor! ctx i := by
  fun_induction Rewriter.initOpRegions <;> grind [OperationPtr.getSuccessor!_def]

@[simp, grind =>]
theorem OperationPtr.getSuccessors!_initOpRegions {operation : OperationPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    operation.getSuccessors! ctx' = operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_initOpRegions h,
    OperationPtr.getNumSuccessors!_initOpRegions h]

@[grind =>]
theorem OperationPtr.getNumRegions!_initOpRegions {operation : OperationPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getNumRegions! ctx' =
    if operation = op then op.getNumRegions! ctx + (regions.size - index) else operation.getNumRegions! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem OperationPtr.getRegion!_initOpRegions {operation : OperationPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getRegion! ctx' idx =
    if _ : operation = op ∧ idx ≥ op.getNumRegions! ctx ∧ idx < regions.size then regions[idx]
    else operation.getRegion! ctx idx := by
  fun_induction Rewriter.initOpRegions <;> grind (splits := 15)

@[simp, grind =>]
theorem BlockOperandPtrPtr.get!_initOpRegions {blockOperandPtr : BlockOperandPtrPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    blockOperandPtr.get! ctx' = blockOperandPtr.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem BlockPtr.getNumArguments!_initOpRegions {block : BlockPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    block.getNumArguments! ctx' = block.getNumArguments! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem BlockArgumentPtr.get!_initOpRegions {blockArg : BlockArgumentPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    blockArg.get! ctx' = blockArg.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem RegionPtr.firstBlock!_initOpRegions {region : RegionPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    (region.get! ctx').firstBlock = (region.get! ctx).firstBlock := by
  fun_induction Rewriter.initOpRegions <;> grind (instances := 5000)

@[simp, grind =>]
theorem RegionPtr.lastBlock!_initOpRegions {region : RegionPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    (region.get! ctx').lastBlock = (region.get! ctx).lastBlock := by
  fun_induction Rewriter.initOpRegions <;> grind (instances := 5000)

theorem RegionPtr.parent!_initOpRegions_gen {region : RegionPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    (region.get! ctx').parent =
    if ∃ (i : Nat) (_ : i < regions.size), index ≤ i ∧ regions[i] = region then some op else (region.get! ctx).parent := by
  fun_induction Rewriter.initOpRegions
  · grind (instances := 5000) (gen := 100)
  · simp_all +zetaDelta only
    split <;> split <;> grind (instances := 5000)
  · grind

@[grind =>]
theorem RegionPtr.parent!_initOpRegions {region : RegionPtr}
    (h : Rewriter.initOpRegions ctx op regions 0 h₁ h₂ h₃ h₄ = some ctx') :
    (region.get! ctx').parent =
    if region ∈ regions then some op else (region.get! ctx).parent := by
  rw [parent!_initOpRegions_gen h]
  congr
  grind [Array.mem_iff_getElem]

@[simp, grind =>]
theorem ValuePtr.getFirstUse!_initOpRegions {value : ValuePtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    value.getFirstUse! ctx' = value.getFirstUse! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem ValuePtr.getType!_initOpRegions {value : ValuePtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    value.getType! ctx' = value.getType! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>]
theorem OpOperandPtrPtr.get!_initOpRegions {opOperandPtr : OpOperandPtrPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    opOperandPtr.get! ctx' = opOperandPtr.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

end Rewriter.initOpRegions

end Veir
