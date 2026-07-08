module

public import Veir.IR.Buffed.RawAccessors
public import Veir.IR.Buffed.Sim
public import Veir.IR.Buffed.SimDefs
import all Veir.IR.Buffed.RawAccessors
import all Veir.IR.Buffed.SimDefs

public section

namespace Veir.Buffed

section range

variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] {bctx : IRBufContext OpInfo}

@[simp, grind =]
theorem ValueImplMPtr.writeType_range :
    (ValueImplMPtr.writeType bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeType]
@[simp, grind =]
theorem ValueImplMPtr.writeType_size :
    (ValueImplMPtr.writeType bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeType]

@[simp, grind =]
theorem ValueImplMPtr.writeFirstUse_range :
    (ValueImplMPtr.writeFirstUse bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeFirstUse]
@[simp, grind =]
theorem ValueImplMPtr.writeFirstUse_size :
    (ValueImplMPtr.writeFirstUse bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeFirstUse]

@[simp, grind =]
theorem OpResultMPtr.writeType_range :
    (OpResultMPtr.writeType bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeType]
@[simp, grind =]
theorem OpResultMPtr.writeType_size :
    (OpResultMPtr.writeType bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeType]

@[simp, grind =]
theorem OpResultMPtr.writeFirstUse_range :
    (OpResultMPtr.writeFirstUse bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeFirstUse]
@[simp, grind =]
theorem OpResultMPtr.writeFirstUse_size :
    (OpResultMPtr.writeFirstUse bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeFirstUse]

@[simp, grind =]
theorem OpResultMPtr.writeIndex_range :
    (OpResultMPtr.writeIndex bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeIndex]
@[simp, grind =]
theorem OpResultMPtr.writeIndex_size :
    (OpResultMPtr.writeIndex bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeIndex]

@[simp, grind =]
theorem OpResultMPtr.writeOwner_range :
    (OpResultMPtr.writeOwner bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeOwner]
@[simp, grind =]
theorem OpResultMPtr.writeOwner_size :
    (OpResultMPtr.writeOwner bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeOwner]

@[simp, grind =]
theorem BlockArgumentMPtr.writeType_range :
    (BlockArgumentMPtr.writeType bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeType]
@[simp, grind =]
theorem BlockArgumentMPtr.writeType_size :
    (BlockArgumentMPtr.writeType bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeType]

@[simp, grind =]
theorem BlockArgumentMPtr.writeFirstUse_range :
    (BlockArgumentMPtr.writeFirstUse bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeFirstUse]
@[simp, grind =]
theorem BlockArgumentMPtr.writeFirstUse_size :
    (BlockArgumentMPtr.writeFirstUse bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeFirstUse]

@[simp, grind =]
theorem BlockArgumentMPtr.writeIndex_range :
    (BlockArgumentMPtr.writeIndex bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeIndex]
@[simp, grind =]
theorem BlockArgumentMPtr.writeIndex_size :
    (BlockArgumentMPtr.writeIndex bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeIndex]

@[simp, grind =]
theorem BlockArgumentMPtr.writeOwner_range :
    (BlockArgumentMPtr.writeOwner bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeOwner]
@[simp, grind =]
theorem BlockArgumentMPtr.writeOwner_size :
    (BlockArgumentMPtr.writeOwner bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeOwner]

@[simp, grind =]
theorem OpOperandMPtr.writeNextUse_range :
    (OpOperandMPtr.writeNextUse bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeNextUse]
@[simp, grind =]
theorem OpOperandMPtr.writeNextUse_size :
    (OpOperandMPtr.writeNextUse bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeNextUse]

@[simp, grind =]
theorem OpOperandMPtr.writeBack_range :
    (OpOperandMPtr.writeBack bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeBack]
@[simp, grind =]
theorem OpOperandMPtr.writeBack_size :
    (OpOperandMPtr.writeBack bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeBack]

@[simp, grind =]
theorem OpOperandMPtr.writeOwner_range :
    (OpOperandMPtr.writeOwner bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeOwner]
@[simp, grind =]
theorem OpOperandMPtr.writeOwner_size :
    (OpOperandMPtr.writeOwner bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeOwner]

@[simp, grind =]
theorem OpOperandMPtr.writeValue_range :
    (OpOperandMPtr.writeValue bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeValue]
@[simp, grind =]
theorem OpOperandMPtr.writeValue_size :
    (OpOperandMPtr.writeValue bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeValue]

@[simp, grind =]
theorem BlockOperandMPtr.writeNextUse_range :
    (BlockOperandMPtr.writeNextUse bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeNextUse]
@[simp, grind =]
theorem BlockOperandMPtr.writeNextUse_size :
    (BlockOperandMPtr.writeNextUse bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeNextUse]

@[simp, grind =]
theorem BlockOperandMPtr.writeBack_range :
    (BlockOperandMPtr.writeBack bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeBack]
@[simp, grind =]
theorem BlockOperandMPtr.writeBack_size :
    (BlockOperandMPtr.writeBack bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeBack]

@[simp, grind =]
theorem BlockOperandMPtr.writeOwner_range :
    (BlockOperandMPtr.writeOwner bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeOwner]
@[simp, grind =]
theorem BlockOperandMPtr.writeOwner_size :
    (BlockOperandMPtr.writeOwner bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeOwner]

@[simp, grind =]
theorem BlockOperandMPtr.writeValue_range :
    (BlockOperandMPtr.writeValue bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeValue]
@[simp, grind =]
theorem BlockOperandMPtr.writeValue_size :
    (BlockOperandMPtr.writeValue bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeValue]

@[simp, grind =]
theorem OperationMPtr.writeNumResults_range :
    (OperationMPtr.writeNumResults bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeNumResults]
@[simp, grind =]
theorem OperationMPtr.writeNumResults_size :
    (OperationMPtr.writeNumResults bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeNumResults]

@[simp, grind =]
theorem OperationMPtr.writePrev_range :
    (OperationMPtr.writePrev bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writePrev]
@[simp, grind =]
theorem OperationMPtr.writePrev_size :
    (OperationMPtr.writePrev bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writePrev]

@[simp, grind =]
theorem OperationMPtr.writeNext_range :
    (OperationMPtr.writeNext bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeNext]
@[simp, grind =]
theorem OperationMPtr.writeNext_size :
    (OperationMPtr.writeNext bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeNext]

@[simp, grind =]
theorem OperationMPtr.writeParent_range :
    (OperationMPtr.writeParent bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeParent]
@[simp, grind =]
theorem OperationMPtr.writeParent_size :
    (OperationMPtr.writeParent bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeParent]

@[simp, grind =]
theorem OperationMPtr.writeOpType_range :
    (OperationMPtr.writeOpType bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeOpType]
@[simp, grind =]
theorem OperationMPtr.writeOpType_size :
    (OperationMPtr.writeOpType bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeOpType]

@[simp, grind =]
theorem OperationMPtr.writeNumBlockOperands_range :
    (OperationMPtr.writeNumBlockOperands bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeNumBlockOperands]
@[simp, grind =]
theorem OperationMPtr.writeNumBlockOperands_size :
    (OperationMPtr.writeNumBlockOperands bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeNumBlockOperands]

@[simp, grind =]
theorem OperationMPtr.writeNumRegions_range :
    (OperationMPtr.writeNumRegions bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeNumRegions]
@[simp, grind =]
theorem OperationMPtr.writeNumRegions_size :
    (OperationMPtr.writeNumRegions bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeNumRegions]

@[simp, grind =]
theorem OperationMPtr.writeNumOperands_range :
    (OperationMPtr.writeNumOperands bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeNumOperands]
@[simp, grind =]
theorem OperationMPtr.writeNumOperands_size :
    (OperationMPtr.writeNumOperands bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeNumOperands]

@[simp, grind =]
theorem OperationMPtr.writeAttrs_range :
    (OperationMPtr.writeAttrs bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeAttrs]
@[simp, grind =]
theorem OperationMPtr.writeAttrs_size :
    (OperationMPtr.writeAttrs bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeAttrs]

@[simp, grind =]
theorem OperationMPtr.writeNthRegion_range :
    (OperationMPtr.writeNthRegion bctx ptr idx val h₁ h₂).mem.range = bctx.mem.range := by
  simp [writeNthRegion]
@[simp, grind =]
theorem OperationMPtr.writeNthRegion_size :
    (OperationMPtr.writeNthRegion bctx ptr idx val h₁ h₂).mem.size = bctx.mem.size := by
  simp [writeNthRegion]

@[simp, grind =]
theorem BlockMPtr.writeFirstUse_range :
    (BlockMPtr.writeFirstUse bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeFirstUse]
@[simp, grind =]
theorem BlockMPtr.writeFirstUse_size :
    (BlockMPtr.writeFirstUse bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeFirstUse]

@[simp, grind =]
theorem BlockMPtr.writePrev_range :
    (BlockMPtr.writePrev bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writePrev]
@[simp, grind =]
theorem BlockMPtr.writePrev_size :
    (BlockMPtr.writePrev bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writePrev]

@[simp, grind =]
theorem BlockMPtr.writeNext_range :
    (BlockMPtr.writeNext bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeNext]
@[simp, grind =]
theorem BlockMPtr.writeNext_size :
    (BlockMPtr.writeNext bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeNext]

@[simp, grind =]
theorem BlockMPtr.writeParent_range :
    (BlockMPtr.writeParent bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeParent]
@[simp, grind =]
theorem BlockMPtr.writeParent_size :
    (BlockMPtr.writeParent bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeParent]

@[simp, grind =]
theorem BlockMPtr.writeFirstOp_range :
    (BlockMPtr.writeFirstOp bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeFirstOp]
@[simp, grind =]
theorem BlockMPtr.writeFirstOp_size :
    (BlockMPtr.writeFirstOp bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeFirstOp]

@[simp, grind =]
theorem BlockMPtr.writeLastOp_range :
    (BlockMPtr.writeLastOp bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeLastOp]
@[simp, grind =]
theorem BlockMPtr.writeLastOp_size :
    (BlockMPtr.writeLastOp bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeLastOp]

@[simp, grind =]
theorem BlockMPtr.writeNumArguments_range :
    (BlockMPtr.writeNumArguments bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeNumArguments]
@[simp, grind =]
theorem BlockMPtr.writeNumArguments_size :
    (BlockMPtr.writeNumArguments bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeNumArguments]

@[simp, grind =]
theorem RegionMPtr.writeFirstBlock_range :
    (RegionMPtr.writeFirstBlock bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeFirstBlock]
@[simp, grind =]
theorem RegionMPtr.writeFirstBlock_size :
    (RegionMPtr.writeFirstBlock bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeFirstBlock]

@[simp, grind =]
theorem RegionMPtr.writeLastBlock_range :
    (RegionMPtr.writeLastBlock bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeLastBlock]
@[simp, grind =]
theorem RegionMPtr.writeLastBlock_size :
    (RegionMPtr.writeLastBlock bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeLastBlock]

@[simp, grind =]
theorem RegionMPtr.writeParent_range :
    (RegionMPtr.writeParent bctx ptr val h).mem.range = bctx.mem.range := by
  simp [writeParent]
@[simp, grind =]
theorem RegionMPtr.writeParent_size :
    (RegionMPtr.writeParent bctx ptr val h).mem.size = bctx.mem.size := by
  simp [writeParent]

@[simp, grind =]
theorem OpOperandPtrMPtr.write_range :
    (OpOperandPtrMPtr.write bctx operandPtr val h).mem.range = bctx.mem.range := by
  simp [write]
@[simp, grind =]
theorem OpOperandPtrMPtr.write_size :
    (OpOperandPtrMPtr.write bctx operandPtr val h).mem.size = bctx.mem.size := by
  simp [write]

@[simp, grind =]
theorem BlockOperandPtrMPtr.write_range :
    (BlockOperandPtrMPtr.write bctx operandPtr val h).mem.range = bctx.mem.range := by
  simp [write]
@[simp, grind =]
theorem BlockOperandPtrMPtr.write_size :
    (BlockOperandPtrMPtr.write bctx operandPtr val h).mem.size = bctx.mem.size := by
  simp [write]

end range
