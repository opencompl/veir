import Mlir.Rewriter.Rewriter
import Mlir.Rewriter.LinkedList.GetSet
import Mlir.ForLean

namespace Mlir

@[grind .]
theorem Rewriter.insertOp?_inBounds_mono (ptr : GenericPtr)
    (heq : insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    ptr.InBounds ctx ↔ ptr.InBounds newCtx := by
  simp only [insertOp?] at heq
  split at heq
  · split at heq <;> grind
  · grind

@[grind .]
theorem Rewriter.insertOp?_fieldsInBounds_mono
    (heq : insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    ctx.FieldsInBounds → newCtx.FieldsInBounds := by
  simp only [insertOp?] at heq
  grind

@[grind .]
theorem OpResultPtr.get?_insertOp? (val : OpResultPtr) (hval : val.InBounds ctx)
    (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    val.get! newCtx = val.get! ctx := by
  simp only [Rewriter.insertOp?] at heq
  grind

@[grind .]
theorem OpResultPtr.get_insertOp? (val : OpResultPtr) (hval : val.InBounds ctx)
    (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    val.get newCtx (by grind) = val.get ctx hval := by
  simp only [Rewriter.insertOp?] at heq
  grind

@[grind .]
theorem ValuePtr.get_insertOp? (val : ValuePtr) (hval : val.InBounds ctx)
    (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    val.getFirstUse newCtx (by grind) = val.getFirstUse ctx hval := by
  simp only [Rewriter.insertOp?] at heq
  grind

@[grind .]
theorem OpOperandPtr.get_insertOp? (opr : OpOperandPtr) (hopr : opr.InBounds ctx)
    (heq : Rewriter.insertOp? ctx newOp ip h₁ h₂ h₃ = some newCtx) :
    opr.get newCtx (by grind) = opr.get ctx hopr := by
  simp only [Rewriter.insertOp?] at heq
  grind

/- replaceUse -/

@[simp, grind .]
theorem BlockOperandPtr.get_replaceUse {bop : BlockOperandPtr} {hbop} :
    bop.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hbop =
    bop.get ctx (by grind) := by
  unfold Rewriter.replaceUse
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp_replaceUse {b : BlockPtr} {hb} :
    (b.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hb).firstOp =
    (b.get ctx (by grind)).firstOp := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockPtr.getLastOp_replaceUse {b : BlockPtr} {hb} :
    (b.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hb).lastOp =
    (b.get ctx (by grind)).lastOp := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockPtr.getNext_replaceUse {b : BlockPtr} {hb} :
    (b.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hb).next =
    (b.get ctx (by grind)).next := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockPtr.getPrev_replaceUse {b : BlockPtr} {hb} :
    (b.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hb).prev =
    (b.get ctx (by grind)).prev := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockPtr.getParent_replaceUse {b : BlockPtr} {hb} :
    (b.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hb).parent =
    (b.get ctx (by grind)).parent := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getParent_replaceUse {op : OperationPtr} {hop} :
    (op.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hop).parent =
    (op.get ctx (by grind)).parent := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getNext_replaceUse {op : OperationPtr} {hop} :
    (op.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hop).next =
    (op.get ctx (by grind)).next := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getPrev_replaceUse {op : OperationPtr} {hop} :
    (op.get (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hop).prev =
    (op.get ctx (by grind)).prev := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getNumOperands_replaceUse :
    OperationPtr.getNumOperands op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hop =
    OperationPtr.getNumOperands op ctx (by grind) := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OpOperandPtr.owner_replaceUse :
    (OpOperandPtr.get opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hop).owner =
    (OpOperandPtr.get opr ctx (by grind)).owner := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_replaceUse :
    OperationPtr.getNumSuccessors! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getNumSuccessors! op ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockOperandPtr.get!_replaceUse :
    BlockOperandPtr.get! bop (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    BlockOperandPtr.get! bop ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getNumResults_replaceUse :
    OperationPtr.getNumResults! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getNumResults! op ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OpResultPtr.owner_replaceUse :
    (OpResultPtr.get opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hopr).owner =
    (OpResultPtr.get opr ctx (by grind)).owner := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OpResultPtr.index_replaceUse :
    (OpResultPtr.get opr (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hopr).index =
    (OpResultPtr.get opr ctx (by grind)).index := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem OperationPtr.getRegions_replaceUse :
    OperationPtr.getRegion! op (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    OperationPtr.getRegion! op ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockPtr.getNumArguments_replaceUse :
    BlockPtr.getNumArguments! block (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) =
    BlockPtr.getNumArguments! block ctx := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockArgumentPtr.owner!_replaceUse :
    (BlockArgumentPtr.get! arg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).owner =
    (BlockArgumentPtr.get! arg ctx).owner := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem BlockArgumentPtr.index!_replaceUse :
    (BlockArgumentPtr.get! arg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn)).index =
    (BlockArgumentPtr.get! arg ctx).index := by
  grind [Rewriter.replaceUse]

@[simp, grind =]
theorem RegionPtr.get_replaceUse :
    RegionPtr.get reg (Rewriter.replaceUse ctx use value' useIn newValueInBounds ctxIn) hreg =
    RegionPtr.get reg ctx (by grind) := by
  grind [Rewriter.replaceUse]

/- replaceValue? -/

@[simp, grind .]
theorem OperationPtr.getNumOperands_iff_replaceValue?
    (hctx' : Rewriter.replaceValue? ctx oldValue newValue oldIn newIn ctxIn depth = some ctx') :
    OperationPtr.getNumOperands op ctx' h_op =
    OperationPtr.getNumOperands op ctx (by grind) := by
  grind [OpOperandPtr.inBounds_if_operand_size_eq]
