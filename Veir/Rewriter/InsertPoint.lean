import Veir.IR
import Veir.IR.WellFormed
import Veir.IR.Grind

namespace Veir

section InsertPoint

/--
- A position in the IR where we can insert an operation.
-/
inductive InsertPoint where
  | before (op: OperationPtr)
  | atEnd (block: BlockPtr)
deriving DecidableEq

@[grind]
def InsertPoint.InBounds (ip : InsertPoint) (ctx : IRContext) : Prop :=
  match ip with
  | before op => op.InBounds ctx
  | atEnd bl => bl.InBounds ctx

@[grind =]
theorem InsertPoint.inBounds_before : (before op).InBounds ctx ↔ op.InBounds ctx := by rfl
@[grind =]
theorem InsertPoint.inBounds_atEnd : (atEnd bl).InBounds ctx ↔ bl.InBounds ctx := by rfl

@[grind]
def InsertPoint.block! (insertionPoint : InsertPoint) (ctx : IRContext) : Option BlockPtr :=
  match insertionPoint with
  | before op => (op.get! ctx).parent
  | atEnd b => b

def InsertPoint.block (insertionPoint : InsertPoint) (ctx : IRContext)
    (hIn : insertionPoint.InBounds ctx := by grind) : Option BlockPtr :=
  match insertionPoint with
  | before op => (op.get ctx (by grind)).parent
  | atEnd b => b

@[grind _=_]
theorem InsertPoint.block!_eq_block (insertionPoint : InsertPoint) (ctx : IRContext)
    (hIn : insertionPoint.InBounds ctx) :
    insertionPoint.block! ctx = insertionPoint.block ctx hIn := by
  cases insertionPoint <;> grind [InsertPoint.block!, InsertPoint.block]

@[grind .]
theorem InsertPoint.block_InBounds {insertionPoint : InsertPoint} {ctx : IRContext}
    (ctxFieldsInBounds : ctx.FieldsInBounds) (hIn : insertionPoint.InBounds ctx) :
    insertionPoint.block ctx hIn = some blockPtr →
    insertionPoint.InBounds ctx →
    blockPtr.InBounds ctx := by
  simp only [InsertPoint.block]
  grind

@[simp, grind =]
theorem InsertPoint.block!_before_eq :
    InsertPoint.block! (before op) ctx =
    (op.get! ctx).parent := by
  grind [InsertPoint.block]

@[simp, grind =]
theorem InsertPoint.block!_atEnd_eq :
    InsertPoint.block! (atEnd blockPtr) ctx =
    blockPtr := by rfl

def InsertPoint.prev (ip : InsertPoint) (ctx : IRContext) (inBounds : ip.InBounds ctx) : Option OperationPtr :=
  match ip with
  | before op => (op.get ctx).prev
  | atEnd block => (block.get ctx).lastOp

def InsertPoint.prev! (ip : InsertPoint) (ctx : IRContext) : Option OperationPtr :=
  match ip with
  | before op => (op.get! ctx).prev
  | atEnd block => (block.get! ctx).lastOp

@[grind _=_]
theorem InsertPoint.prev!_eq_prev {ip : InsertPoint} {ctx : IRContext}
    (hIn : ip.InBounds ctx) :
    ip.prev! ctx = ip.prev ctx hIn := by
  cases ip <;> grind [InsertPoint.prev!, InsertPoint.prev]

@[simp, grind =]
theorem InsertPoint.prev!_before_eq :
    InsertPoint.prev! (before op) ctx =
    (op.get! ctx).prev := by
  grind [InsertPoint.prev!]

@[simp, grind =]
theorem InsertPoint.prev_atEnd_eq :
    InsertPoint.prev! (atEnd blockPtr) ctx =
    (blockPtr.get! ctx).lastOp := by
  grind [InsertPoint.prev!]

@[simp, grind .]
theorem InsertPoint.prev!_inBounds {ipInBounds : InsertPoint.InBounds ip ctx} {ctxInBounds : ctx.FieldsInBounds} :
    ip.prev! ctx = some opPtr →
    opPtr.InBounds ctx := by
  simp_all only [InsertPoint.prev!, InsertPoint.InBounds]
  grind

def InsertPoint.next (ip : InsertPoint) : Option OperationPtr :=
  match ip with
  | before op => op
  | atEnd _ => none

@[grind .]
theorem InsertPoint.next_inBounds {ipInBounds : InsertPoint.InBounds ip ctx} :
    ip.next = some opPtr →
    opPtr.InBounds ctx := by
  simp_all only [InsertPoint.next, InsertPoint.InBounds]
  grind

@[simp, grind =]
theorem InsertPoint.next_before_eq :
    InsertPoint.next (before op) = some op := by rfl

@[simp, grind =]
theorem InsertPoint.next_atEnd_eq :
    InsertPoint.next (atEnd blockPtr) = none := by rfl

@[grind =]
theorem InsertPoint.next_eq_none_iff_eq_atEnd {ip : InsertPoint} :
    ip.next = none ↔ ∃ block, ip = .atEnd block := by
  cases ip <;> grind

@[grind =]
theorem InsertPoint.next_eq_some_iff_eq_before {ip : InsertPoint} :
    ip.next = some nextOp ↔ ip = .before nextOp := by
  cases ip <;> grind

@[simp, grind .]
theorem InsertPoint.block!_eq_of_prev!_eq_some
    (ipInBounds : InsertPoint.InBounds ip ctx) :
    ip.next = some firstOp →
    (firstOp.get! ctx).parent = some blockPtr →
    ip.block! ctx = some blockPtr := by
  intros hPrev
  cases ip <;> grind

theorem InsertPoint.next.maybe₁_parent :
    BlockPtr.OpChain blockPtr ctx array →
    InsertPoint.block! ip ctx = some blockPtr →
    ip.next.maybe₁ (fun op => (op.get! ctx).parent = some blockPtr) := by
  cases ip <;> grind

theorem InsertPoint.prev.maybe₁_parent :
    BlockPtr.OpChain blockPtr ctx array →
    InsertPoint.InBounds ip ctx →
    InsertPoint.block! ip ctx = some blockPtr →
    (ip.prev! ctx).maybe₁ (fun op => (op.get! ctx).parent = some blockPtr) := by
  cases ip <;> grind [Option.maybe₁_def]

/--
 - Get the index of the insertion point in the operation list of the block.
 - The index is where a new operation would be inserted.
 -/
noncomputable def InsertPoint.idxIn
    (insertPoint : InsertPoint) (ctx : IRContext)
    (blockPtr : BlockPtr) (inBounds : insertPoint.InBounds ctx := by grind)
    (blockIsParent : insertPoint.block ctx (by grind) = some blockPtr := by grind)
    (ctxWf : ctx.WellFormed := by grind) : Nat :=
  match insertPoint with
  | before op =>
    let opList := BlockPtr.operationList blockPtr ctx (by grind) (by grind)
    opList.idxOf op
  | atEnd b =>
    (BlockPtr.operationList blockPtr ctx (by grind) (by grind)).size

@[simp, grind =]
theorem InsertPoint.idxIn_before_eq :
    InsertPoint.idxIn (before op) ctx blockPtr inBounds blockIsParent ctxWf =
    (BlockPtr.operationList blockPtr ctx ctxWf (by grind)).idxOf op := by
  simp [InsertPoint.idxIn]

@[simp, grind =]
theorem InsertPoint.idxIn_atEnd_eq :
    InsertPoint.idxIn (atEnd blockPtr) ctx blockPtr inBounds blockIsParent ctxWf =
    (BlockPtr.operationList blockPtr ctx ctxWf (by grind)).size := by
  simp [InsertPoint.idxIn]

@[grind .]
theorem InsertPoint.idxIn.le_size_array :
    BlockPtr.OpChain blockPtr ctx array →
    InsertPoint.idxIn ip ctx blockPtr inBounds blockIsParent ctxWf ≤ array.size := by
  simp only [InsertPoint.idxIn]
  grind

@[grind .]
theorem InsertPoint.idxIn.le_size_operationList :
    InsertPoint.idxIn ip ctx blockPtr inBounds blockIsParent ctxWf ≤ (BlockPtr.operationList blockPtr ctx ctxWf blockInBounds).size := by
  simp only [InsertPoint.idxIn]
  grind

@[grind =]
theorem InsertPoint.idxIn.getElem? :
    (blockPtr.operationList ctx ctxWf blockInBounds)[
      InsertPoint.idxIn ip ctx blockPtr inBounds blockIsParent ctxWf]? = ip.next := by
  simp only [InsertPoint.idxIn]
  cases ip
  case before op =>
    simp only [next_before_eq]
    apply Array.getElem?_idxOf
    suffices _ : op ∈ blockPtr.operationList ctx ctxWf blockInBounds by grind
    have := @BlockPtr.operationListWF ctx blockPtr blockInBounds ctxWf
    have := this.allOpsInChain
    grind
  case atEnd bl =>
    grind

theorem InsertPoint.idxIn_InsertPoint_prev_none:
    (InsertPoint.prev! ip ctx = none ↔
    InsertPoint.idxIn ip ctx blockPtr inBounds blockIsParent ctxWf = 0) := by
  have ⟨array, harray⟩ := ctxWf.opChain blockPtr (by grind)
  grind [BlockPtr.OpChain, cases InsertPoint]


theorem InsertPoint.next_eq_none_iff_idxIn_eq_size_array
    (hCtx : BlockPtr.OpChain blockPtr ctx array) :
    (ip.next = none ↔
    idxIn ip ctx blockPtr inBounds blockIsParent ctxWf = array.size) := by
  have ⟨array, harray⟩ := ctxWf.opChain blockPtr (by grind)
  grind [BlockPtr.OpChain, cases InsertPoint]

theorem InsertPoint.idxIn_eq_iff_getElem?
    (hctx : BlockPtr.OpChain blockPtr ctx array) :
    x < array.size →
    InsertPoint.idxIn ip ctx blockPtr inBounds blockIsParent ctxWf = x →
    array[x]? = ip.next := by
  have harray := @InsertPoint.idxIn.getElem? ip ctx blockPtr inBounds blockIsParent ctxWf (by grind)
  grind

theorem InsertPoint.prev!_eq_none_iff_firstOp!_eq_next
    (hctx : ctx.WellFormed)
    (inBounds : ip.InBounds ctx)
    (hblock : ip.block! ctx = some blockPtr) :
    (InsertPoint.prev! ip ctx = none ↔
    (blockPtr.get! ctx).firstOp = ip.next) := by
  have ⟨array, harray⟩ := hctx.opChain blockPtr (by grind)
  cases ip
  · grind [BlockPtr.OpChain.prev!_eq_none_iff_firstOp!_eq_self]
  · grind [BlockPtr.OpChain.firstOp_eq_none_iff_lastOp_eq_none]

theorem InsertPoint.next_ne_firstOp
    (hWF : ctx.WellFormed) (ipInBounds : ip.InBounds ctx) :
    (BlockPtr.get blockPtr ctx blockInBounds).firstOp = some firstOp →
    InsertPoint.prev! ip ctx ≠ none →
    InsertPoint.next ip ≠ some firstOp := by
  intro hFirst hPrev
  have ⟨array, harray⟩ := hWF.opChain blockPtr blockInBounds
  grind [InsertPoint.prev!_eq_none_iff_firstOp!_eq_next]

theorem InsertPoint.idxIn_eq_size_operationList_iff_eq_atEnd :
    ip.block! ctx = some blockPtr →
    (ip.idxIn ctx blockPtr inBounds blockIsParent ctxWf = (BlockPtr.operationList blockPtr ctx ctxWf blockInBounds).size ↔
      ip = atEnd blockPtr) := by
  intros hblock
  constructor
  · intros hIdx
    cases ip <;> grind [BlockPtr.operationList.mem]
  · grind [BlockPtr.OpChain]

@[grind .]
theorem InsertPoint.idxIn.pred_lt_size :
    BlockPtr.OpChain blockPtr ctx array →
    InsertPoint.idxIn ip ctx blockPtr inBounds blockIsParent ctxWf > 0 →
    InsertPoint.idxIn ip ctx blockPtr inBounds blockIsParent ctxWf - 1 < array.size := by
  intros hChain
  have := @InsertPoint.idxIn.le_size_operationList ip ctx blockPtr (by grind) (by grind) (by grind) (by grind)
  grind

theorem InsertPoint.prev!_eq_GetElem!_idxIn
    (hChain : BlockPtr.OpChain blockPtr ctx array)
    (hIdx : InsertPoint.idxIn ip ctx blockPtr inBounds blockIsParent ctxWf > 0) :
    ip.prev! ctx = some (array[InsertPoint.idxIn ip ctx blockPtr inBounds blockIsParent ctxWf - 1]'(by apply InsertPoint.idxIn.pred_lt_size <;> grind)) := by
  have := @InsertPoint.idxIn.le_size_operationList ip ctx blockPtr (by grind) (by grind) (by grind) (by grind)
  have : array = blockPtr.operationList ctx (by grind) (by grind) := by grind
  by_cases array.size = ip.idxIn ctx blockPtr inBounds blockIsParent ctxWf
  · have : ip = atEnd blockPtr := by grind [InsertPoint.idxIn_eq_size_operationList_iff_eq_atEnd]
    grind [BlockPtr.OpChain]
  · have : ip.idxIn ctx blockPtr (by grind) (by grind) (by grind) < array.size := by grind
    have := hChain.prev _ hIdx (by grind)
    cases ip <;> grind

@[grind .]
theorem InsertPoint.idxIn_Before_lt_size :
    InsertPoint.idxIn (before op) ctx blockPtr inBounds blockIsParent ctxWf <
    (BlockPtr.operationList blockPtr ctx ctxWf blockInBounds).size := by
  grind [BlockPtr.OpChain, BlockPtr.operationListWF]

end InsertPoint

section BlockInsertPoint

/--
- A position in the IR where we can insert an operation.
-/
inductive BlockInsertPoint where
  | before (op: BlockPtr)
  | atEnd (block: RegionPtr)

@[grind]
def BlockInsertPoint.InBounds : BlockInsertPoint → IRContext → Prop
| before op => op.InBounds
| atEnd bl => bl.InBounds
@[grind =]
theorem BlockInsertPoint.inBounds_before : (before op).InBounds ctx ↔ op.InBounds ctx := by rfl
@[grind =]
theorem BlockInsertPoint.inBounds_atEnd : (atEnd bl).InBounds ctx ↔ bl.InBounds ctx := by rfl

@[grind]
def BlockInsertPoint.prev! (ip : BlockInsertPoint) (ctx : IRContext) : Option OperationPtr :=
  match ip with
  | before op => (op.get! ctx).prev
  | atEnd block => (block.get! ctx).lastBlock

@[grind]
def BlockInsertPoint.next (ip : BlockInsertPoint) : Option OperationPtr :=
  match ip with
  | before bl => bl
  | atEnd _ => none

@[grind]
def BlockInsertPoint.region! (ip : BlockInsertPoint) (ctx : IRContext) : Option RegionPtr :=
  match ip with
  | before bl => bl.get! ctx |>.parent
  | atEnd rg => some rg

end BlockInsertPoint

end Veir
