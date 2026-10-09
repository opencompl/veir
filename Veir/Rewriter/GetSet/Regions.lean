module

public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import all Veir.IR.Basic
import all Veir.IR.GetSet
import all Veir.Rewriter.LinkedList.GetSet
import Veir.Rewriter.WfRewriter.GetSetTactic


public section

namespace Veir

variable {OpInfo} [HasOpInfo OpInfo]

-- Relate the getters to the fields of the underlying structures.
attribute [local grind _=_]
  OperationPtr.getNextOp!_def OperationPtr.getPrevOp!_def OperationPtr.getParent!_def
  OperationPtr.getAttributes!_def OpOperandPtr.getNextUse!_def OpOperandPtr.getBack!_def
  OpOperandPtr.getOwner!_def OpOperandPtr.getValue!_def BlockOperandPtr.getNextUse!_def
  BlockOperandPtr.getBack!_def BlockOperandPtr.getOwner!_def BlockOperandPtr.getValue!_def
  OpResultPtr.getType!_def OpResultPtr.getFirstUse!_def OpResultPtr.getOwner!_def
  BlockPtr.getParent!_def BlockPtr.getFirstUse!_def BlockPtr.getFirstOp!_def
  BlockPtr.getLastOp!_def BlockPtr.getNextBlock!_def BlockPtr.getPrevBlock!_def
  BlockArgumentPtr.getType!_def BlockArgumentPtr.getFirstUse!_def
  BlockArgumentPtr.getIndex!_def BlockArgumentPtr.getLoc!_def
  BlockArgumentPtr.getOwner!_def RegionPtr.getParent!_def RegionPtr.getFirstBlock!_def
  RegionPtr.getLastBlock!_def OpResultPtr.getIndex!_def
variable {ctx : IRContext OpInfo}
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
variable {opCode : Dialect}
/-! ## `Rewriter.pushRegion` -/

section Rewriter.pushRegion

variable {op : OperationPtr}

attribute [local grind] Rewriter.pushRegion

@[simp, grind =, simp_getset]
private theorem BlockPtr.get!_pushRegion {block : BlockPtr} :
    block.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    block.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_pushRegion {block : BlockPtr} :
    block.getParent! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_pushRegion {block : BlockPtr} :
    block.getFirstUse! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_pushRegion {block : BlockPtr} :
    block.getFirstOp! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_pushRegion {block : BlockPtr} :
    block.getLastOp! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_pushRegion {block : BlockPtr} :
    block.getNextBlock! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_pushRegion {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.prev!_pushRegion {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.next!_pushRegion {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.parent!_pushRegion {operation : OperationPtr} :
    operation.getParent! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getParent! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_pushRegion {operation : OperationPtr} :
    operation.getOpType! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.attrs!_pushRegion {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_pushRegion {operation : OperationPtr} :
    operation.getProperties! (Rewriter.pushRegion ctx op region hop hregion hregionParent) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_pushRegion {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpResultPtr.get!_pushRegion {opResult : OpResultPtr} :
    opResult.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    opResult.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_pushRegion {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_pushRegion {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_pushRegion {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_pushRegion {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_pushRegion {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpOperandPtr.get!_pushRegion {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    opOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_pushRegion {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_pushRegion {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_pushRegion {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_pushRegion {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_pushRegion {operation : OperationPtr} :
    operation.getOperands! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_pushRegion {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getBlockOperands!_pushRegion {operation : OperationPtr} :
    operation.getBlockOperands! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getBlockOperands! ctx := by
  simp only [OperationPtr.getBlockOperands!_def]
  grind

@[simp, grind =, simp_getset]
private theorem BlockOperandPtr.get!_pushRegion {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_pushRegion {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_pushRegion {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_pushRegion {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_pushRegion {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_pushRegion {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.pushRegion ctx op region hop hregion hregionParent) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_pushRegion {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[grind =, simp_getset]
theorem OperationPtr.getNumRegions!_pushRegion {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    if operation = op then operation.getNumRegions! ctx + 1
    else operation.getNumRegions! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getRegion!_pushRegion {operation : OperationPtr} :
    operation.getRegion! (Rewriter.pushRegion ctx op region hop hregion hregionParent) index =
    if operation = op ∧ index = operation.getNumRegions! ctx then region
    else operation.getRegion! ctx index := by
  grind

@[simp, grind =, simp_getset]
private theorem BlockOperandPtrPtr.get!_pushRegion {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_pushRegion {block : BlockPtr} :
    block.getNumArguments! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getBlockArguments!_pushRegion {block : BlockPtr} :
    block.getBlockArguments! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    block.getBlockArguments! ctx := by
  simp only [BlockPtr.getBlockArguments!_def]
  grind

@[simp, grind =, simp_getset]
private theorem BlockArgumentPtr.get!_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockArg.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getLoc!_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.firstBlock!_pushRegion {r : RegionPtr} :
    r.getFirstBlock! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    r.getFirstBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.lastBlock!_pushRegion {r : RegionPtr} :
    r.getLastBlock! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    r.getLastBlock! ctx := by
  grind

@[grind =, simp_getset]
theorem RegionPtr.parent!_pushRegion {r : RegionPtr} :
    r.getParent! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    if r = region then some op else (r.getParent! ctx) := by
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getFirstUse!_pushRegion {value : ValuePtr} :
    value.getFirstUse! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getType!_pushRegion {value : ValuePtr} :
    value.getType! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    value.getType! ctx := by
  grind

@[simp, grind =, simp_getset]
private theorem OpOperandPtrPtr.get!_pushRegion {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    opOperandPtr.get! ctx := by
  grind

end Rewriter.pushRegion
/-! ## `Rewriter.initOpRegions` -/

section Rewriter.initOpRegions

variable {op : OperationPtr}

attribute [local grind] Rewriter.initOpRegions

@[simp, grind =>, simp_getset]
private theorem BlockPtr.get!_initOpRegions {block : BlockPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    block.get! ctx' = block.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getParent!_initOpRegions {block : BlockPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    block.getParent! ctx' =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getFirstUse!_initOpRegions {block : BlockPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    block.getFirstUse! ctx' =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getFirstOp!_initOpRegions {block : BlockPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    block.getFirstOp! ctx' =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getLastOp!_initOpRegions {block : BlockPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    block.getLastOp! ctx' =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getNextBlock!_initOpRegions {block : BlockPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    block.getNextBlock! ctx' =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getPrevBlock!_initOpRegions {block : BlockPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    block.getPrevBlock! ctx' =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.prev!_initOpRegions {operation : OperationPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getPrevOp! ctx' = operation.getPrevOp! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.next!_initOpRegions {operation : OperationPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getNextOp! ctx' = operation.getNextOp! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.parent!_initOpRegions {operation : OperationPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getParent! ctx' = operation.getParent! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getOpType!_initOpRegions {operation : OperationPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getOpType! ctx' = operation.getOpType! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.attrs!_initOpRegions {operation : OperationPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getAttributes! ctx' = operation.getAttributes! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getProperties!_initOpRegions {operation : OperationPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getProperties! ctx' opCode = operation.getProperties! ctx opCode := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumResults!_initOpRegions {operation : OperationPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getNumResults! ctx' = operation.getNumResults! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumOperands!_initOpRegions {operation : OperationPtr} {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getNumOperands! ctx' = operation.getNumOperands! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
private theorem OpResultPtr.get!_initOpRegions {opResult : OpResultPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    opResult.get! ctx' = opResult.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem OpResultPtr.getIndex!_initOpRegions {opResult : OpResultPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    opResult.getIndex! ctx' =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OpResultPtr.getType!_initOpRegions {opResult : OpResultPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    opResult.getType! ctx' =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OpResultPtr.getFirstUse!_initOpRegions {opResult : OpResultPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    opResult.getFirstUse! ctx' =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OpResultPtr.getOwner!_initOpRegions {opResult : OpResultPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    opResult.getOwner! ctx' =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =>, simp_getset]
private theorem OpOperandPtr.get!_initOpRegions {opOperand : OpOperandPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    opOperand.get! ctx' = opOperand.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem OpOperandPtr.getNextUse!_initOpRegions {opOperand : OpOperandPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    opOperand.getNextUse! ctx' =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OpOperandPtr.getBack!_initOpRegions {opOperand : OpOperandPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    opOperand.getBack! ctx' =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OpOperandPtr.getOwner!_initOpRegions {opOperand : OpOperandPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    opOperand.getOwner! ctx' =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OpOperandPtr.getValue!_initOpRegions {opOperand : OpOperandPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    opOperand.getValue! ctx' =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getOperands!_initOpRegions {operation : OperationPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getOperands! ctx' = operation.getOperands! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getNumSuccessors!_initOpRegions {operation : OperationPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getNumSuccessors! ctx' = operation.getNumSuccessors! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getBlockOperands!_initOpRegions {operation : OperationPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getBlockOperands! ctx' =
    operation.getBlockOperands! ctx := by
  simp only [OperationPtr.getBlockOperands!_def]
  grind

@[simp, grind =>, simp_getset]
private theorem BlockOperandPtr.get!_initOpRegions {blockOperand : BlockOperandPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    blockOperand.get! ctx' = blockOperand.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getNextUse!_initOpRegions {blockOperand : BlockOperandPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    blockOperand.getNextUse! ctx' =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getBack!_initOpRegions {blockOperand : BlockOperandPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    blockOperand.getBack! ctx' =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getOwner!_initOpRegions {blockOperand : BlockOperandPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    blockOperand.getOwner! ctx' =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockOperandPtr.getValue!_initOpRegions {blockOperand : BlockOperandPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    blockOperand.getValue! ctx' =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getSuccessor!_initOpRegions {operation : OperationPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    operation.getSuccessor! ctx' i = operation.getSuccessor! ctx i := by
  fun_induction Rewriter.initOpRegions <;> grind [OperationPtr.getSuccessor!_def]

@[simp, grind =>, simp_getset]
theorem OperationPtr.getSuccessors!_initOpRegions {operation : OperationPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    operation.getSuccessors! ctx' = operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_initOpRegions h,
    OperationPtr.getNumSuccessors!_initOpRegions h]

@[grind =>, simp_getset]
theorem OperationPtr.getNumRegions!_initOpRegions {operation : OperationPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getNumRegions! ctx' =
    if operation = op then op.getNumRegions! ctx + (regions.size - index) else operation.getNumRegions! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem OperationPtr.getRegion!_initOpRegions {operation : OperationPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    operation.getRegion! ctx' idx =
    if _ : operation = op ∧ idx ≥ op.getNumRegions! ctx ∧ idx < regions.size then regions[idx]
    else operation.getRegion! ctx idx := by
  fun_induction Rewriter.initOpRegions <;> grind (splits := 15)

@[simp, grind =>, simp_getset]
private theorem BlockOperandPtrPtr.get!_initOpRegions {blockOperandPtr : BlockOperandPtrPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    blockOperandPtr.get! ctx' = blockOperandPtr.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getNumArguments!_initOpRegions {block : BlockPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    block.getNumArguments! ctx' = block.getNumArguments! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem BlockPtr.getBlockArguments!_initOpRegions {block : BlockPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    block.getBlockArguments! ctx' =
    block.getBlockArguments! ctx := by
  simp only [BlockPtr.getBlockArguments!_def]
  grind

@[simp, grind =>, simp_getset]
private theorem BlockArgumentPtr.get!_initOpRegions {blockArg : BlockArgumentPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    blockArg.get! ctx' = blockArg.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem BlockArgumentPtr.getType!_initOpRegions {blockArg : BlockArgumentPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    blockArg.getType! ctx' =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_initOpRegions {blockArg : BlockArgumentPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    blockArg.getFirstUse! ctx' =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =>, simp_getset]
theorem BlockArgumentPtr.getIndex!_initOpRegions {blockArg : BlockArgumentPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    blockArg.getIndex! ctx' =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, simp_getset]
theorem BlockArgumentPtr.getLoc!_initOpRegions {blockArg : BlockArgumentPtr}
    (_h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    blockArg.getLoc! ctx' =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =>, simp_getset]
theorem BlockArgumentPtr.getOwner!_initOpRegions {blockArg : BlockArgumentPtr}
    (h : Rewriter.initOpRegions ctx op regions idx h₁ h₂ h₃ h₄ = some ctx') :
    blockArg.getOwner! ctx' =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =>, simp_getset]
theorem RegionPtr.firstBlock!_initOpRegions {region : RegionPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    region.getFirstBlock! ctx' = region.getFirstBlock! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind (instances := 5000)

@[simp, grind =>, simp_getset]
theorem RegionPtr.lastBlock!_initOpRegions {region : RegionPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    region.getLastBlock! ctx' = region.getLastBlock! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind (instances := 5000)

@[simp_getset]
theorem RegionPtr.parent!_initOpRegions_gen {region : RegionPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    region.getParent! ctx' =
    if ∃ (i : Nat) (_ : i < regions.size), index ≤ i ∧ regions[i] = region then some op else (region.getParent! ctx) := by
  fun_induction Rewriter.initOpRegions
  · grind (instances := 5000) (gen := 100)
  · simp_all +zetaDelta only
    split <;> split <;> grind (instances := 5000)
  · grind

@[grind =>]
theorem RegionPtr.parent!_initOpRegions {region : RegionPtr}
    (h : Rewriter.initOpRegions ctx op regions 0 h₁ h₂ h₃ h₄ = some ctx') :
    region.getParent! ctx' =
    if region ∈ regions then some op else (region.getParent! ctx) := by
  rw [parent!_initOpRegions_gen h]
  congr
  grind [Array.mem_iff_getElem]

@[simp, grind =>, simp_getset]
theorem ValuePtr.getFirstUse!_initOpRegions {value : ValuePtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    value.getFirstUse! ctx' = value.getFirstUse! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
theorem ValuePtr.getType!_initOpRegions {value : ValuePtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    value.getType! ctx' = value.getType! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp, grind =>, simp_getset]
private theorem OpOperandPtrPtr.get!_initOpRegions {opOperandPtr : OpOperandPtrPtr}
    (h : Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx') :
    opOperandPtr.get! ctx' = opOperandPtr.get! ctx := by
  fun_induction Rewriter.initOpRegions <;> grind

@[simp_getset]
theorem Rewriter.initOpRegions_inBounds {ptr : GenericPtr} {ctx' : IRContext OpInfo} :
    initOpRegions ctx op regions index h₁ h₂ h₃ h₄ = some ctx' →
    (ptr.InBounds ctx ↔ ptr.InBounds ctx') := by
  fun_induction Rewriter.initOpRegions <;> grind

grind_pattern Rewriter.initOpRegions_inBounds =>
  Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄, some ctx', ptr.InBounds ctx
grind_pattern Rewriter.initOpRegions_inBounds =>
  Rewriter.initOpRegions ctx op regions index h₁ h₂ h₃ h₄, some ctx', ptr.InBounds ctx'

end Rewriter.initOpRegions

end Veir
