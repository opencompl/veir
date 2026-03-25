module

public import Veir.IR
import Veir.IR.WellFormed
import Veir.IR.Grind

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx' : IRContext OpInfo}

section InsertPoint

/--
- A position in the IR where we can insert an operation.
-/
inductive InsertPoint where
  | before (op: OperationPtr)
  | atEnd (block: BlockPtr)
deriving DecidableEq

@[grind]
def InsertPoint.InBounds (ip : InsertPoint) (ctx : IRContext OpInfo) : Prop :=
  match ip with
  | before op => op.InBounds ctx
  | atEnd bl => bl.InBounds ctx

@[grind =]
theorem InsertPoint.inBounds_before : (before op).InBounds ctx ↔ op.InBounds ctx := by rfl
@[grind =]
theorem InsertPoint.inBounds_atEnd : (atEnd bl).InBounds ctx ↔ bl.InBounds ctx := by rfl

@[grind]
def InsertPoint.block! (insertionPoint : InsertPoint) (ctx : IRContext OpInfo) : Option BlockPtr :=
  match insertionPoint with
  | before op => (op.get! ctx).parent
  | atEnd b => b

def InsertPoint.block (insertionPoint : InsertPoint) (ctx : IRContext OpInfo)
    (hIn : insertionPoint.InBounds ctx := by grind) : Option BlockPtr :=
  match insertionPoint with
  | before op => (op.get ctx (by grind)).parent
  | atEnd b => b

@[grind _=_]
theorem InsertPoint.block!_eq_block (insertionPoint : InsertPoint) (ctx : IRContext OpInfo)
    (hIn : insertionPoint.InBounds ctx) :
    insertionPoint.block! ctx = insertionPoint.block ctx hIn := by
  cases insertionPoint <;> grind [InsertPoint.block!, InsertPoint.block]

@[grind .]
theorem InsertPoint.block_InBounds {insertionPoint : InsertPoint} {ctx : IRContext OpInfo}
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

def InsertPoint.prev (ip : InsertPoint) (ctx : IRContext OpInfo) (inBounds : ip.InBounds ctx) : Option OperationPtr :=
  match ip with
  | before op => (op.get ctx).prev
  | atEnd block => (block.get ctx).lastOp

def InsertPoint.prev! (ip : InsertPoint) (ctx : IRContext OpInfo) : Option OperationPtr :=
  match ip with
  | before op => (op.get! ctx).prev
  | atEnd block => (block.get! ctx).lastOp

@[grind _=_]
theorem InsertPoint.prev!_eq_prev {ip : InsertPoint} {ctx : IRContext OpInfo}
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
    (insertPoint : InsertPoint) (ctx : IRContext OpInfo)
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
theorem InsertPoint.idxIn.le_size_operationList (ip : InsertPoint) (ctx : IRContext OpInfo) (blockPtr : BlockPtr)
  (inBounds : ip.InBounds ctx) (blockIsParent : ip.block ctx inBounds = some blockPtr) (ctxWf : ctx.WellFormed)
  (blockInBounds : blockPtr.InBounds ctx)  :
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
    have := BlockPtr.operationListWF ctx blockPtr blockInBounds ctxWf
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
  have := InsertPoint.idxIn.le_size_operationList ip ctx blockPtr (by grind) (by grind) (by grind) (by grind)
  grind

theorem InsertPoint.prev!_eq_GetElem!_idxIn
    (hChain : BlockPtr.OpChain blockPtr ctx array)
    (hIdx : InsertPoint.idxIn ip ctx blockPtr inBounds blockIsParent ctxWf > 0) :
    ip.prev! ctx = some (array[InsertPoint.idxIn ip ctx blockPtr inBounds blockIsParent ctxWf - 1]'(by apply InsertPoint.idxIn.pred_lt_size <;> grind)) := by
  have := InsertPoint.idxIn.le_size_operationList ip ctx blockPtr (by grind) (by grind) (by grind) (by grind)
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

/--
- A position in the IR where we can insert an operation.
-/
inductive BlockInsertPoint where
  | before (op: BlockPtr)
  | atEnd (block: RegionPtr)

namespace BlockInsertPoint

@[grind]
def InBounds : BlockInsertPoint → IRContext OpInfo → Prop
| before op => op.InBounds
| atEnd bl => bl.InBounds
@[grind =]
theorem inBounds_before : (before op).InBounds ctx ↔ op.InBounds ctx := by rfl
@[grind =]
theorem inBounds_atEnd : (atEnd bl).InBounds ctx ↔ bl.InBounds ctx := by rfl

@[grind]
def prev! (ip : BlockInsertPoint) (ctx : IRContext OpInfo) : Option BlockPtr :=
  match ip with
  | before block => (block.get! ctx).prev
  | atEnd region => (region.get! ctx).lastBlock

def prev (ip : BlockInsertPoint) (ctx : IRContext OpInfo)
    (hIn : ip.InBounds ctx := by grind) : Option BlockPtr :=
  match ip with
  | before block => (block.get ctx (by grind)).prev
  | atEnd region => (region.get ctx (by grind)).lastBlock

@[grind _=_]
theorem prev!_eq_prev {ip : BlockInsertPoint} {ctx : IRContext OpInfo}
    (hIn : ip.InBounds ctx) :
    ip.prev! ctx = ip.prev ctx hIn := by
  cases ip <;> grind [prev!, prev]

theorem prev!_inBounds {ip : BlockInsertPoint}
    {ctxInBounds : ctx.FieldsInBounds} :
    ip.InBounds ctx →
    ip.prev! ctx = some blockPtr →
    blockPtr.InBounds ctx := by
  cases ip <;> simp_all only [prev!, InBounds] <;> grind

grind_pattern prev!_inBounds =>
  ip.InBounds ctx, ip.prev! ctx, some blockPtr

@[grind]
def next (ip : BlockInsertPoint) : Option BlockPtr :=
  match ip with
  | before bl => bl
  | atEnd _ => none

theorem next_inBounds {ip : BlockInsertPoint} :
    ip.InBounds ctx →
    ip.next = some blockPtr →
    blockPtr.InBounds ctx := by
  cases ip <;> simp_all only [next, InBounds] <;> grind

grind_pattern next_inBounds =>
  ip.InBounds ctx, ip.next, some blockPtr

@[grind]
def region! (ip : BlockInsertPoint) (ctx : IRContext OpInfo) : Option RegionPtr :=
  match ip with
  | before bl => bl.get! ctx |>.parent
  | atEnd rg => some rg

def region (ip : BlockInsertPoint) (ctx : IRContext OpInfo)
    (hIn : ip.InBounds ctx := by grind) : Option RegionPtr :=
  match ip with
  | before bl => (bl.get ctx (by grind)).parent
  | atEnd rg => some rg

@[grind _=_]
theorem region!_eq_region (ip : BlockInsertPoint) (ctx : IRContext OpInfo)
    (hIn : ip.InBounds ctx) :
    ip.region! ctx = ip.region ctx hIn := by
  cases ip <;> grind [region!, region]

theorem region_InBounds {ip : BlockInsertPoint} {ctx : IRContext OpInfo}
    (ctxFieldsInBounds : ctx.FieldsInBounds) (hIn : ip.InBounds ctx) :
    ip.region ctx hIn = some regionPtr →
    ip.InBounds ctx →
    regionPtr.InBounds ctx := by
  simp only [region]
  grind

grind_pattern region_InBounds =>
  ip.InBounds ctx, ip.region ctx hIn, some regionPtr, ip.InBounds ctx

/--
Get the index of the insertion point in the block list of the region.
The index is where a new block would be inserted.
-/
noncomputable def idxIn
    (insertPoint : BlockInsertPoint) (ctx : IRContext OpInfo)
    (regionPtr : RegionPtr) (inBounds : insertPoint.InBounds ctx := by grind)
    (regionIsParent : insertPoint.region ctx (by grind) = some regionPtr := by grind)
    (ctxWf : ctx.WellFormed := by grind) : Nat :=
  match insertPoint with
  | before bl =>
    let blList := RegionPtr.blockList regionPtr ctx (by grind) (by grind)
    blList.idxOf bl
  | atEnd r =>
    (RegionPtr.blockList regionPtr ctx (by grind) (by grind)).size

@[simp, grind =]
theorem idxIn_before_eq :
    idxIn (before bl) ctx regionPtr inBounds regionIsParent ctxWf =
    (RegionPtr.blockList regionPtr ctx ctxWf (by grind)).idxOf bl := by
  simp [idxIn]

@[simp, grind =]
theorem idxIn_atEnd_eq :
    idxIn (atEnd regionPtr) ctx regionPtr inBounds regionIsParent ctxWf =
    (RegionPtr.blockList regionPtr ctx ctxWf (by grind)).size := by
  simp [idxIn]

@[grind .]
theorem idxIn.le_size_array :
    RegionPtr.BlockChain regionPtr ctx array →
    idxIn ip ctx regionPtr inBounds regionIsParent ctxWf ≤ array.size := by
  simp only [idxIn]
  grind

@[grind .]
theorem idxIn.le_size_blockList (ip : BlockInsertPoint) (ctx : IRContext OpInfo)
  (regionPtr : RegionPtr) (inBounds : ip.InBounds ctx)
  (regionIsParent : ip.region ctx inBounds = some regionPtr)
  (ctxWf : ctx.WellFormed)
  (regionInBounds : regionPtr.InBounds ctx)  :
    idxIn ip ctx regionPtr inBounds regionIsParent ctxWf ≤ (RegionPtr.blockList regionPtr ctx ctxWf regionInBounds).size := by
  simp only [idxIn]
  grind

@[grind .]
theorem idxIn.getElem? :
    (regionPtr.blockList ctx ctxWf regionInBounds)[
      idxIn ip ctx regionPtr inBounds regionIsParent ctxWf]? = ip.next := by
  simp only [idxIn]
  cases ip
  case before bl =>
    simp only [next]
    apply Array.getElem?_idxOf
    suffices _ : bl ∈ regionPtr.blockList ctx ctxWf regionInBounds by grind
    have := RegionPtr.blockListWF ctx regionPtr regionInBounds ctxWf
    have := this.allBlocksInChain
    grind
  case atEnd r =>
    grind

theorem idxIn_BlockInsertPoint_prev_none:
    prev! ip ctx = none ↔
    idxIn ip ctx regionPtr inBounds regionIsParent ctxWf = 0 := by
  have ⟨array, harray⟩ := ctxWf.blockChain regionPtr (by grind)
  grind [RegionPtr.BlockChain, cases BlockInsertPoint]

grind_pattern idxIn_BlockInsertPoint_prev_none =>
  prev! ip ctx, idxIn ip ctx regionPtr inBounds regionIsParent ctxWf

theorem next_eq_none_iff_idxIn_eq_size_array
    (hCtx : RegionPtr.BlockChain regionPtr ctx array) :
    ip.next = none ↔
    idxIn ip ctx regionPtr inBounds regionIsParent ctxWf = array.size := by
  have ⟨array, harray⟩ := ctxWf.blockChain regionPtr (by grind)
  grind [RegionPtr.BlockChain, cases BlockInsertPoint]

grind_pattern next_eq_none_iff_idxIn_eq_size_array =>
  RegionPtr.BlockChain regionPtr ctx array, ip.next,
  idxIn ip ctx regionPtr inBounds regionIsParent ctxWf

theorem idxIn_eq_iff_getElem?
    (hctx : RegionPtr.BlockChain regionPtr ctx array) :
    idxIn ip ctx regionPtr inBounds regionIsParent ctxWf < array.size →
    array[idxIn ip ctx regionPtr inBounds regionIsParent ctxWf]? = ip.next := by
  grind

theorem idxIn_eq_size_blockList_iff_eq_atEnd
    (hregion : ip.region! ctx = some regionPtr) :
    ip.idxIn ctx regionPtr inBounds regionIsParent ctxWf =
      (RegionPtr.blockList regionPtr ctx ctxWf regionInBounds).size ↔
    ip = atEnd regionPtr := by
  constructor
  · intros hIdx
    cases ip <;> grind [RegionPtr.blockList.mem]
  · grind [RegionPtr.BlockChain]

@[grind .]
theorem idxIn.pred_lt_size :
    RegionPtr.BlockChain regionPtr ctx array →
    idxIn ip ctx regionPtr inBounds regionIsParent ctxWf > 0 →
    idxIn ip ctx regionPtr inBounds regionIsParent ctxWf - 1 < array.size := by
  intros hChain
  have := idxIn.le_size_blockList ip ctx regionPtr (by grind) (by grind) (by grind) (by grind)
  grind

@[grind .]
theorem idxIn_Before_lt_size :
    idxIn (before bl) ctx regionPtr inBounds regionIsParent ctxWf <
    (RegionPtr.blockList regionPtr ctx ctxWf regionInBounds).size := by
  grind [RegionPtr.BlockChain, RegionPtr.blockListWF]

end BlockInsertPoint

end Veir
