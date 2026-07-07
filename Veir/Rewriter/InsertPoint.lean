module

public import ExArray.CompilerExtras
public import Veir.IR
import Veir.IR.WellFormed
import Veir.IR.Grind
public import Veir.IR.Buffed.Basic
public import Veir.IR.Buffed.Sim
public import Veir.IR.Buffed.InBounds

import all Veir.IR.Buffed.Sim

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
deriving DecidableEq, BEq, Hashable

@[grind]
def InsertPoint.InBounds (ip : InsertPoint) (ctx : IRContext OpInfo) : Prop :=
  match ip with
  | before op => op.InBounds ctx
  | atEnd bl => bl.InBounds ctx

@[expose, grind]
def InsertPoint.IsRepr (ip : InsertPoint) : Prop :=
  match ip with
  | before op => op.IsRepr
  | atEnd bl => bl.IsRepr

theorem InsertPoint.inBounds_def :
    ip.InBounds ctx = (match ip with | before op => op.InBounds ctx | atEnd bl => bl.InBounds ctx) :=
  by rfl

instance : Decidable (InsertPoint.InBounds ip (ctx : IRContext OpInfo)) := by
  cases ip <;> simp only [InsertPoint.inBounds_def] <;> infer_instance

@[simp, grind =]
theorem InsertPoint.inBounds_before : (before op).InBounds ctx ↔ op.InBounds ctx := by rfl
@[simp, grind =]
theorem InsertPoint.inBounds_atEnd : (atEnd bl).InBounds ctx ↔ bl.InBounds ctx := by rfl

def InsertPoint.atStart! (block : BlockPtr) (ctx : IRContext OpInfo) : InsertPoint :=
  match (block.get! ctx).firstOp with
  | some firstOp => .before firstOp
  | none => .atEnd block

def InsertPoint.atStart (block : BlockPtr) (ctx : IRContext OpInfo)
    (hIn : block.InBounds ctx := by grind) : InsertPoint :=
  match (block.get ctx (by grind)).firstOp with
  | some firstOp => .before firstOp
  | none => .atEnd block

@[grind =_, eq_bang ←]
theorem InsertPoint.atStart!_eq_atStart (block : BlockPtr) (ctx : IRContext OpInfo)
    (hIn : block.InBounds ctx) :
    InsertPoint.atStart! block ctx = InsertPoint.atStart block ctx hIn := by
  cases (block.get ctx (by grind)).firstOp <;> grind [InsertPoint.atStart!, InsertPoint.atStart]

def InsertPoint.after (op : OperationPtr) (ctx : IRContext OpInfo) (block : BlockPtr)
    (_opHasParent : (op.get! ctx).parent = some block := by grind)
    (opInBounds : op.InBounds ctx := by grind) : InsertPoint :=
  match (op.get ctx).next with
  | some op => .before op
  | none => InsertPoint.atEnd block

def InsertPoint.after? (op : OperationPtr) (ctx : IRContext OpInfo) : Option InsertPoint :=
  match (op.get! ctx).parent with
  | some block =>
    match (op.get! ctx).next with
    | some nextOp => some (.before nextOp)
    | none => some (.atEnd block)
  | none => none

theorem InsertPoint.after?_eq_some_of_after_eq :
    InsertPoint.after op ctx block h₁ h₂ = ip →
    InsertPoint.after? op ctx = some ip := by
  grind [InsertPoint.after, InsertPoint.after?]

theorem InsertPoint.after?_eq_of_after?_eq_some
    (h : InsertPoint.after? op ctx = some ip)
    (hblock : (op.get! ctx).parent = some block)
    (hop : op.InBounds ctx) :
    InsertPoint.after op ctx block (by grind) (by grind) = ip := by
  grind [InsertPoint.after, InsertPoint.after?]

@[grind .]
theorem InsertPoint.after_inBounds (ctxWf : ctx.WellFormed) :
    (InsertPoint.after op ctx blockPtr opHasParent opInBounds).InBounds ctx := by
  grind [InsertPoint.after]

@[grind]
def InsertPoint.block! (insertionPoint : InsertPoint) (ctx : IRContext OpInfo) : Option BlockPtr :=
  match insertionPoint with
  | before op => (op.get! ctx).parent
  | atEnd b => b

buffed
def InsertPoint.blockSim (insertionPoint : InsertPoint) (ctx : Sim.IRContext OpInfo)
    (hIn : insertionPoint.InBounds ctx.spec := by grind)
    (_hRepr : insertionPoint.IsRepr := by grind) : Sim.OptionBlockPtr :=
  match insertionPoint with
  | before op => op.toSim.getParent ctx (by sorry)
  | atEnd b => b.toSim.toO

@[grind _=_]
theorem InsertPoint.block!_eq_block (insertionPoint : InsertPoint) (ctx : Sim.IRContext OpInfo)
    (hIn : insertionPoint.InBounds ctx.spec) hRepr :
    insertionPoint.block! ctx.spec = (insertionPoint.block ctx hIn hRepr).spec := by
  -- cases insertionPoint <;> grind [InsertPoint.block!, InsertPoint.block]
  sorry

@[grind .]
theorem InsertPoint.block_InBounds {insertionPoint : InsertPoint} {ctx : Sim.IRContext OpInfo}
    (ctxFieldsInBounds : ctx.spec.FieldsInBounds) (hIn : insertionPoint.InBounds ctx.spec) hRepr :
    insertionPoint.InBounds ctx.spec →
    (insertionPoint.block ctx hIn hRepr).InBounds ctx := by
  simp only [InsertPoint.block_def, InsertPoint.blockSim]
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

buffed
def InsertPoint.prevSim (ip : InsertPoint) (ctx : Sim.IRContext OpInfo) (inBounds : ip.InBounds ctx.spec) : Sim.OptionOperationPtr :=
  match ip with
  | before op => op.toSim.getPrevOp ctx (by sorry)
  | atEnd block => block.toSim.getLastOp ctx (by sorry)

def InsertPoint.prev! (ip : InsertPoint) (ctx : IRContext OpInfo) : Option OperationPtr :=
  match ip with
  | before op => (op.get! ctx).prev
  | atEnd block => (block.get! ctx).lastOp

@[grind .]
theorem InsertPoint.prev_inBounds {ip : InsertPoint} {ctx : Sim.IRContext OpInfo} h :
    ip.InBounds ctx.spec →
    (ip.prev ctx h).InBounds ctx := by
  cases ip <;> simp_all only [prev_def, prevSim, InBounds] <;> grind

@[grind _=_]
theorem InsertPoint.prev!_eq_prev {ip : InsertPoint} {ctx : Sim.IRContext OpInfo}
    (hIn : ip.InBounds ctx.spec) :
    ip.prev! ctx.spec = (ip.prev ctx hIn).spec := by
  -- cases ip <;> grind [InsertPoint.prev!, InsertPoint.prev]
  sorry

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

buffed
def InsertPoint.nextSim (ip : InsertPoint) : Sim.OptionOperationPtr :=
  match ip with
  | before op => op.toSim.toO
  | atEnd _ => .none

@[grind .]
theorem InsertPoint.next_inBounds {ctx : Sim.IRContext OpInfo} {ipInBounds : InsertPoint.InBounds ip ctx.spec} :
    (ip.next).InBounds ctx := by
  simp_all only [next_def, nextSim, InsertPoint.InBounds]
  split
  · grind
  · split at ipInBounds
    · grind
    · sorry

@[simp, grind =]
theorem InsertPoint.next_before_eq :
    (InsertPoint.next (before op)).spec = some op := by sorry

@[simp, grind =]
theorem InsertPoint.next_atEnd_eq :
    InsertPoint.next (atEnd blockPtr) = .none := by rfl

@[grind =]
theorem InsertPoint.next_eq_none_iff_eq_atEnd {ip : InsertPoint} :
    ip.next.spec = none ↔ ∃ block, ip = .atEnd block := by
  cases ip <;> sorry

@[grind =]
theorem InsertPoint.next_eq_some_iff_eq_before {ip : InsertPoint} :
    ip.next.toOption = some nextOp ↔ ip = .before nextOp.spec := by
  cases ip <;> sorry

@[simp, grind .]
theorem InsertPoint.block!_eq_of_prev!_eq_some
    (ipInBounds : InsertPoint.InBounds ip ctx) :
    ip.next.toOption = some firstOp →
    (firstOp.spec.get! ctx).parent = some blockPtr →
    ip.block! ctx = some blockPtr := by
  intros hPrev
  cases ip <;> grind

theorem InsertPoint.next.maybe₁_parent_of_opChain :
    BlockPtr.OpChain blockPtr ctx array →
    InsertPoint.block! ip ctx = some blockPtr →
    ip.next.spec.maybe₁ (fun op => (op.get! ctx).parent = some blockPtr) := by
  cases ip <;> sorry

theorem InsertPoint.next.maybe₁_parent :
    ctx.WellFormed →
    InsertPoint.block! ip ctx = some blockPtr →
    ip.next.toOption = some nextOp →
    (nextOp.spec.get! ctx).parent = some blockPtr := by
  cases ip <;> grind

grind_pattern InsertPoint.next.maybe₁_parent =>
  ctx.WellFormed, InsertPoint.block! ip ctx, some blockPtr, ip.next, some nextOp,
  (nextOp.spec.get! ctx).parent

theorem InsertPoint.prev.maybe₁_parent_of_opChain :
    BlockPtr.OpChain blockPtr ctx array →
    InsertPoint.InBounds ip ctx →
    InsertPoint.block! ip ctx = some blockPtr →
    (ip.prev! ctx).maybe₁ (fun op => (op.get! ctx).parent = some blockPtr) := by
  cases ip <;> grind [Option.maybe₁_def]

theorem InsertPoint.prev.maybe₁_parent :
    ctx.WellFormed →
    InsertPoint.InBounds ip ctx →
    InsertPoint.block! ip ctx = some blockPtr →
    ip.prev! ctx = some prevOp →
    (prevOp.get! ctx).parent = some blockPtr := by
  intro ctxWf ipInBounds hblock hprev
  have ⟨array, harray⟩ := ctxWf.opChain blockPtr (by sorry)
  have := InsertPoint.prev.maybe₁_parent_of_opChain harray ipInBounds hblock
  grind [Option.maybe₁_def]

grind_pattern InsertPoint.prev.maybe₁_parent =>
  ctx.WellFormed, InsertPoint.InBounds ip ctx, InsertPoint.block! ip ctx, some blockPtr,
  ip.prev! ctx, some prevOp, (prevOp.get! ctx).parent

/--
 - Get the index of the insertion point in the operation list of the block.
 - The index is where a new operation would be inserted.
 -/
noncomputable def InsertPoint.idxIn
    (insertPoint : InsertPoint) (ctx : IRContext OpInfo)
    (blockPtr : BlockPtr) (inBounds : insertPoint.InBounds ctx := by grind) (hRepr : insertPoint.IsRepr := by grind)
    (blockIsParent : insertPoint.block! ctx = some blockPtr := by grind)
    (ctxWf : ctx.WellFormed := by grind) : Nat :=
  match insertPoint with
  | before op =>
    let opList := BlockPtr.operationList blockPtr ctx (by grind) (by grind)
    opList.idxOf op
  | atEnd b =>
    (BlockPtr.operationList blockPtr ctx (by grind) (by grind)).size

@[simp, grind =]
theorem InsertPoint.idxIn_before_eq {ctx : IRContext OpInfo} {blockPtr : BlockPtr} {repr} {inBounds} {blockIsParent} {ctxWf} :
    InsertPoint.idxIn (before op) ctx blockPtr inBounds repr blockIsParent ctxWf =
    (BlockPtr.operationList blockPtr ctx ctxWf (by grind)).idxOf op := by
  simp [InsertPoint.idxIn]

@[simp, grind =]
theorem InsertPoint.idxIn_atEnd_eq {ctx : IRContext OpInfo} {blockPtr : BlockPtr} {repr} {inBounds} {blockIsParent} {ctxWf} :
    InsertPoint.idxIn (atEnd blockPtr) ctx blockPtr inBounds repr blockIsParent ctxWf =
    (BlockPtr.operationList blockPtr ctx ctxWf (by grind)).size := by
  simp [InsertPoint.idxIn]

@[grind .]
theorem InsertPoint.idxIn.le_size_array {ctx : IRContext OpInfo} {repr} {ctxWf} {inBounds} {blockIsParent} :
    BlockPtr.OpChain blockPtr ctx array →
    InsertPoint.idxIn ip ctx blockPtr inBounds repr blockIsParent ctxWf ≤ array.size := by
  simp only [InsertPoint.idxIn]
  grind

@[grind .]
theorem InsertPoint.idxIn.le_size_operationList (ip : InsertPoint) (ctx : IRContext OpInfo) (blockPtr : BlockPtr) {repr}
  {inBounds} {blockIsParent} ctxWf (blockInBounds : blockPtr.InBounds ctx)  :
    InsertPoint.idxIn ip ctx blockPtr inBounds repr blockIsParent ctxWf ≤ (BlockPtr.operationList blockPtr ctx ctxWf blockInBounds).size := by
  simp only [InsertPoint.idxIn]
  grind

@[grind =]
theorem InsertPoint.idxIn.getElem?  {ctx : IRContext OpInfo} {repr} {ctxWf} {inBounds} {blockInBounds} {blockIsParent} :
    (blockPtr.operationList ctx ctxWf blockInBounds)[
      InsertPoint.idxIn ip ctx blockPtr inBounds repr blockIsParent ctxWf]? = ip.next.spec := by
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
    -- grind
    sorry

theorem InsertPoint.idxIn_InsertPoint_prev_none {ctx : IRContext OpInfo} {repr} {ctxWf} {inBounds} {blockIsParent} :
    (InsertPoint.prev! ip ctx = none ↔
    InsertPoint.idxIn ip ctx blockPtr inBounds repr blockIsParent ctxWf = 0) := by
  have ⟨array, harray⟩ := ctxWf.opChain blockPtr (by sorry)
  grind [BlockPtr.OpChain, cases InsertPoint]


theorem InsertPoint.next_eq_none_iff_idxIn_eq_size_array
    {ctx : IRContext OpInfo} {repr} {ctxWf} {inBounds} {blockIsParent}
    (hCtx : BlockPtr.OpChain blockPtr ctx array) :
    ip.next.spec = none ↔ idxIn ip ctx blockPtr inBounds repr blockIsParent ctxWf = array.size := by
  have ⟨array, harray⟩ := ctxWf.opChain blockPtr (by grind)
  grind [BlockPtr.OpChain, cases InsertPoint]

theorem InsertPoint.idxIn_eq_iff_getElem?
    {ctx : IRContext OpInfo} {repr} {ctxWf} {inBounds} {blockIsParent}
    (hctx : BlockPtr.OpChain blockPtr ctx array) :
    x < array.size →
    InsertPoint.idxIn ip ctx blockPtr inBounds repr blockIsParent ctxWf = x →
    array[x]? = ip.next.spec := by
  sorry

theorem InsertPoint.prev!_eq_none_iff_firstOp!_eq_next
    (hctx : ctx.WellFormed)
    (inBounds : ip.InBounds ctx)
    (hblock : ip.block! ctx = some blockPtr) :
    (InsertPoint.prev! ip ctx = none ↔
    (blockPtr.get! ctx).firstOp = ip.next.spec) := by
  have ⟨array, harray⟩ := hctx.opChain blockPtr (by sorry)
  cases ip
  · grind [BlockPtr.OpChain.prev!_eq_none_iff_firstOp!_eq_self]
  · sorry
  -- · grind [BlockPtr.OpChain.firstOp_eq_none_iff_lastOp_eq_none]

theorem InsertPoint.next_ne_firstOp
    (hWF : ctx.WellFormed) (ipInBounds : ip.InBounds ctx) :
    (BlockPtr.get blockPtr ctx blockInBounds).firstOp = some firstOp →
    InsertPoint.prev! ip ctx ≠ none →
    (InsertPoint.next ip).toOption.map (·.spec) ≠ some firstOp := by -- TODO: better statement
  intro hFirst hPrev
  have ⟨array, harray⟩ := hWF.opChain blockPtr blockInBounds
  sorry
  -- grind [InsertPoint.prev!_eq_none_iff_firstOp!_eq_next]

theorem InsertPoint.idxIn_eq_size_operationList_iff_eq_atEnd
    {ctx : IRContext OpInfo} {repr} {ctxWf} {inBounds} {blockInBounds} {blockIsParent} :
    ip.block! ctx = some blockPtr →
    (ip.idxIn ctx blockPtr inBounds repr blockIsParent ctxWf = (BlockPtr.operationList blockPtr ctx ctxWf blockInBounds).size ↔
      ip = atEnd blockPtr) := by
  intros hblock
  constructor
  · intros hIdx
    cases ip <;> grind [BlockPtr.operationList.mem]
  · grind [BlockPtr.OpChain]

@[grind .]
theorem InsertPoint.idxIn.pred_lt_size
    {ctx : IRContext OpInfo} {repr} {ctxWf} {inBounds} {blockIsParent} :
    BlockPtr.OpChain blockPtr ctx array →
    InsertPoint.idxIn ip ctx blockPtr inBounds repr blockIsParent ctxWf > 0 →
    InsertPoint.idxIn ip ctx blockPtr inBounds repr blockIsParent ctxWf - 1 < array.size := by
  intros hChain
  have := InsertPoint.idxIn.le_size_operationList ip ctx blockPtr (by grind) (blockIsParent := by grind) (repr := repr) (inBounds := inBounds)
  grind

theorem InsertPoint.prev!_eq_GetElem!_idxIn
    {ctx : IRContext OpInfo} {repr} {ctxWf} {inBounds} {blockIsParent}
    (hChain : BlockPtr.OpChain blockPtr ctx array)
    (hIdx : InsertPoint.idxIn ip ctx blockPtr inBounds repr blockIsParent ctxWf > 0) :
    ip.prev! ctx = some (array[InsertPoint.idxIn ip ctx blockPtr inBounds repr blockIsParent ctxWf - 1]'(by apply InsertPoint.idxIn.pred_lt_size <;> grind)) := by
  have := InsertPoint.idxIn.le_size_operationList ip ctx blockPtr (by grind) (blockIsParent := by grind) (repr := repr) (inBounds := inBounds)
  have : array = blockPtr.operationList ctx (by grind) (by grind) := by grind
  by_cases array.size = ip.idxIn ctx blockPtr inBounds repr blockIsParent ctxWf
  · have : ip = atEnd blockPtr := by grind [InsertPoint.idxIn_eq_size_operationList_iff_eq_atEnd]
    grind [BlockPtr.OpChain]
  · have : ip.idxIn ctx blockPtr (by grind) (by grind) (by grind) < array.size := by grind
    have := hChain.prev _ hIdx (by grind)
    cases ip <;> grind

@[grind .]
theorem InsertPoint.idxIn_Before_lt_size
    {ctx : IRContext OpInfo} {repr} {ctxWf} {inBounds} {blockInBounds} {blockIsParent} :
    InsertPoint.idxIn (before op) ctx blockPtr inBounds repr blockIsParent ctxWf <
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

theorem inBounds_def :
    BlockInsertPoint.InBounds bip ctx = (match bip with | before op => op.InBounds | atEnd bl => bl.InBounds) ctx :=
  by rfl

instance : Decidable (BlockInsertPoint.InBounds bip (ctx : IRContext OpInfo)) := by
  cases bip <;> simp only [inBounds_def] <;> infer_instance

@[grind =]
theorem inBounds_before : (before op).InBounds ctx ↔ op.InBounds ctx := by rfl
@[grind =]
theorem inBounds_atEnd : (atEnd bl).InBounds ctx ↔ bl.InBounds ctx := by rfl

@[expose, grind]
def IsRepr (ip : BlockInsertPoint) : Prop :=
  match ip with
  | before bl => bl.IsRepr
  | atEnd rg => rg.IsRepr

def prev! (ip : BlockInsertPoint) (ctx : IRContext OpInfo) : Option BlockPtr :=
  match ip with
  | before block => (block.get! ctx).prev
  | atEnd region => (region.get! ctx).lastBlock

buffed
def prevSim (ip : BlockInsertPoint) (ctx : Sim.IRContext OpInfo)
    (hIn : ip.InBounds ctx.spec := by grind) : Sim.OptionBlockPtr :=
  match ip with
  | before block => block.toSim.getPrevBlock ctx (by grind)
  | atEnd region => region.toSim.getLastBlock ctx (by grind)

@[grind _=_]
theorem prev!_eq_prev {ip : BlockInsertPoint} {ctx : Sim.IRContext OpInfo}
    (hIn : ip.InBounds ctx.spec) :
    ip.prev! ctx.spec = (ip.prev ctx hIn).spec := by
  -- cases ip <;> grind [prev!, prev]
  sorry

@[simp, grind =]
theorem prev!_before :
    BlockInsertPoint.prev! (before blockPtr) ctx =
    (blockPtr.get! ctx).prev := by
  grind [prev!]

@[simp, grind =]
theorem prev!_atEnd :
    BlockInsertPoint.prev! (atEnd regionPtr) ctx =
    (regionPtr.get! ctx).lastBlock := by
  grind [prev!]

@[grind .]
theorem prev!_inBounds {ip : BlockInsertPoint}
    {ctxInBounds : ctx.FieldsInBounds} :
    ip.InBounds ctx →
    ip.prev! ctx = some blockPtr →
    blockPtr.InBounds ctx := by
  cases ip <;> simp_all only [prev!, InBounds] <;> grind

@[grind .]
theorem prev_inBounds {ip : BlockInsertPoint} {ctx : Sim.IRContext OpInfo} h :
    ip.InBounds ctx.spec →
    (ip.prev ctx h).InBounds ctx := by
  cases ip <;> simp_all only [prev_def, prevSim, InBounds] <;> grind

buffed
def nextSim (ip : BlockInsertPoint) : Sim.OptionBlockPtr :=
  match ip with
  | before bl => bl.toSim.toO
  | atEnd _ => .none

@[simp, grind =]
theorem next_before :
    (BlockInsertPoint.next (before blockPtr)).spec = some blockPtr := by sorry

@[simp, grind =]
theorem next_atEnd :
    BlockInsertPoint.next (atEnd regionPtr) = .none := by rfl

@[grind .]
theorem next_inBounds {ip : BlockInsertPoint} {ctx : Sim.IRContext OpInfo} :
    ip.InBounds ctx.spec →
    ip.next.InBounds ctx := by
  cases ip <;> simp_all only [next_def, nextSim, InBounds]
  · grind
  · simp [Sim.OptionBlockPtr.none]
    intros
    constructor
    · rfl
    · grind

@[grind]
def region! (ip : BlockInsertPoint) (ctx : IRContext OpInfo) : Option RegionPtr :=
  match ip with
  | before bl => bl.get! ctx |>.parent
  | atEnd rg => some rg

buffed
def regionSim (ip : BlockInsertPoint) (ctx : Sim.IRContext OpInfo)
    (hIn : ip.InBounds ctx.spec := by grind)
    (_hRepr : ip.IsRepr := by grind) : Sim.OptionRegionPtr :=
  match ip with
  | before bl => bl.toSim.getParent ctx (by sorry)
  | atEnd rg => rg.toSim.toO

@[grind _=_]
theorem region!_eq_region (ip : BlockInsertPoint) (ctx : Sim.IRContext OpInfo)
    (hIn : ip.InBounds ctx.spec) hRepr :
    ip.region! ctx.spec = (ip.region ctx hIn hRepr).spec := by
  -- cases ip <;> grind [region!, region]
  sorry

@[simp, grind =]
theorem region!_before :
    BlockInsertPoint.region! (before blockPtr) ctx = (blockPtr.get! ctx).parent := by rfl

@[simp, grind =]
theorem region!_atEnd :
    BlockInsertPoint.region! (atEnd regionPtr) ctx = some regionPtr := by rfl

theorem region_InBounds {ip : BlockInsertPoint} {ctx : Sim.IRContext OpInfo}
    (ctxFieldsInBounds : ctx.spec.FieldsInBounds) (hIn : ip.InBounds ctx.spec) hRepr :
    (ip.region ctx hIn hRepr).toOption = some regionPtr →
    ip.InBounds ctx.spec →
    regionPtr.InBounds ctx := by
  simp only [region_def, regionSim]
  split
  · sorry
  · grind

grind_pattern region_InBounds =>
  ip.InBounds ctx.spec, (ip.region ctx hIn hRepr).spec, some regionPtr, ip.InBounds ctx.spec

@[grind =>]
theorem BlockPtr_parent!_of_next_eq_some {ip : BlockInsertPoint} :
  ip.next.toOption.map (·.spec) = some block →
  (block.get! ctx).parent = ip.region! ctx := by
  -- cases ip <;> grind
  sorry

@[grind =>]
theorem BlockPtr_parent!_of_prev_eq_some {ip : BlockInsertPoint}
    (hctx : ctx.WellFormed missingUses missingSuccessorUses)
    (ipInBounds : ip.InBounds ctx) :
    ip.region! ctx = some regionPtr →
    ip.prev! ctx = some block →
    (block.get! ctx).parent = ip.region! ctx := by
  cases ip <;> grind

theorem exists_parent_of_prev_eq_some {ip : BlockInsertPoint} (ctxWf : ctx.WellFormed)
    (ipInBounds : ip.InBounds ctx) :
    ip.prev! ctx = some prevOp →
    ∃ parentOp, ip.region! ctx = some parentOp := by
  cases ip
  case before block =>
    have := ctxWf.blocks block (by grind)
    cases h : (block.get! ctx).parent <;> grind [BlockPtr.WellFormed]
  case atEnd region =>
    have := ctxWf.regions region (by grind)
    cases h : (region.get! ctx).lastBlock <;> grind [RegionPtr.WellFormed]

grind_pattern exists_parent_of_prev_eq_some =>
  ctx.WellFormed, ip.InBounds ctx, ip.prev! ctx, some prevOp

theorem prev_next {ip : BlockInsertPoint}
    (ipInBounds : ip.InBounds ctx) :
    ip.prev! ctx = some prevOp →
    ip.next.toOption.map (·.spec) = some nextOp →
    (nextOp.get! ctx).prev = some prevOp := by
  -- cases ip <;> grind
  sorry

grind_pattern prev_next =>
  ip.InBounds ctx, ip.prev! ctx, some prevOp, ip.next.toOption.map (·.spec), some nextOp,
  (nextOp.get! ctx).prev

theorem next_prev {ip : BlockInsertPoint} :
  ctx.WellFormed →
  ip.InBounds ctx →
  ip.prev! ctx = some prevOp →
  ip.next.toOption.map (·.spec) = some nextOp →
  (prevOp.get! ctx).next = some nextOp := by
  -- cases ip <;> grind
  sorry

grind_pattern next_prev =>
  ctx.WellFormed, ip.InBounds ctx, ip.prev! ctx, some prevOp, ip.next.toOption.map (·.spec), some nextOp

/--
Get the index of the insertion point in the block list of the region.
The index is where a new block would be inserted.
-/
noncomputable def idxIn
    (insertPoint : BlockInsertPoint) (ctx : IRContext OpInfo)
    (regionPtr : RegionPtr) (inBounds : insertPoint.InBounds ctx := by grind) (hRepr : insertPoint.IsRepr := by grind)
    (regionIsParent : insertPoint.region! ctx = some regionPtr := by grind)
    (ctxWf : ctx.WellFormed := by grind) : Nat :=
  match insertPoint with
  | before bl =>
    let blList := RegionPtr.blockList regionPtr ctx (by grind) (by grind)
    blList.idxOf bl
  | atEnd r =>
    (RegionPtr.blockList regionPtr ctx (by grind) (by grind)).size

@[simp, grind =]
theorem idxIn_before_eq :
    idxIn (before bl) ctx regionPtr inBounds hRepr regionIsParent ctxWf =
    (RegionPtr.blockList regionPtr ctx ctxWf (by grind)).idxOf bl := by
  simp [idxIn]

@[simp, grind =]
theorem idxIn_atEnd_eq :
    idxIn (atEnd regionPtr) ctx regionPtr inBounds hRepr regionIsParent ctxWf =
    (RegionPtr.blockList regionPtr ctx ctxWf (by grind)).size := by
  simp [idxIn]

@[grind .]
theorem idxIn.le_size_array :
    RegionPtr.BlockChain regionPtr ctx array →
    idxIn ip ctx regionPtr inBounds hRepr regionIsParent ctxWf ≤ array.size := by
  simp only [idxIn]
  grind

@[grind .]
theorem idxIn.le_size_blockList (ip : BlockInsertPoint) (ctx : IRContext OpInfo)
  (regionPtr : RegionPtr) {hRepr} (inBounds : ip.InBounds ctx)
  (regionIsParent : ip.region! ctx = some regionPtr)
  (ctxWf : ctx.WellFormed)
  (regionInBounds : regionPtr.InBounds ctx)  :
    idxIn ip ctx regionPtr inBounds hRepr regionIsParent ctxWf ≤ (RegionPtr.blockList regionPtr ctx ctxWf regionInBounds).size := by
  simp only [idxIn]
  grind

@[grind .]
theorem idxIn.getElem? :
    (regionPtr.blockList ctx ctxWf regionInBounds)[
      idxIn ip ctx regionPtr inBounds hRepr regionIsParent ctxWf]? = ip.next.spec := by
  simp only [idxIn]
  cases ip
  case before bl =>
    simp only [next_before]
    apply Array.getElem?_idxOf
    suffices _ : bl ∈ regionPtr.blockList ctx ctxWf regionInBounds by grind
    have := RegionPtr.blockListWF ctx regionPtr regionInBounds ctxWf
    have := this.allBlocksInChain
    grind
  case atEnd r =>
    -- grind
    sorry

theorem idxIn_BlockInsertPoint_prev_none:
    prev! ip ctx = none ↔
    idxIn ip ctx regionPtr inBounds hRepr regionIsParent ctxWf = 0 := by
  have ⟨array, harray⟩ := ctxWf.blockChain regionPtr (by sorry)
  grind [RegionPtr.BlockChain, cases BlockInsertPoint]

grind_pattern idxIn_BlockInsertPoint_prev_none =>
  prev! ip ctx, idxIn ip ctx regionPtr inBounds hRepr regionIsParent ctxWf

theorem next_eq_none_iff_idxIn_eq_size_array
    (hCtx : RegionPtr.BlockChain regionPtr ctx array) :
    ip.next = .none ↔
    idxIn ip ctx regionPtr inBounds hRepr regionIsParent ctxWf = array.size := by
  have ⟨array, harray⟩ := ctxWf.blockChain regionPtr (by sorry)
  -- grind [RegionPtr.BlockChain, cases BlockInsertPoint]
  sorry

grind_pattern next_eq_none_iff_idxIn_eq_size_array =>
  RegionPtr.BlockChain regionPtr ctx array, ip.next,
  idxIn ip ctx regionPtr inBounds hRepr regionIsParent ctxWf

theorem idxIn_eq_iff_getElem?
    (hctx : RegionPtr.BlockChain regionPtr ctx array) :
    idxIn ip ctx regionPtr inBounds hRepr regionIsParent ctxWf < array.size →
    array[idxIn ip ctx regionPtr inBounds hRepr regionIsParent ctxWf]? = ip.next.spec := by
  sorry

theorem idxIn_eq_size_blockList_iff_eq_atEnd
    (hregion : ip.region! ctx = some regionPtr) :
    ip.idxIn ctx regionPtr inBounds hRepr regionIsParent ctxWf =
      (RegionPtr.blockList regionPtr ctx ctxWf regionInBounds).size ↔
    ip = atEnd regionPtr := by
  constructor
  · intros hIdx
    cases ip <;> grind [RegionPtr.blockList.mem]
  · grind [RegionPtr.BlockChain]

@[grind .]
theorem idxIn.pred_lt_size :
    RegionPtr.BlockChain regionPtr ctx array →
    idxIn ip ctx regionPtr inBounds hRepr regionIsParent ctxWf > 0 →
    idxIn ip ctx regionPtr inBounds hRepr regionIsParent ctxWf - 1 < array.size := by
  intros hChain
  have := idxIn.le_size_blockList ip ctx regionPtr (hRepr := by grind) (by grind) (by grind) (by grind) (by grind)
  grind

theorem prev!_eq_getElem!_idxIn
    (hChain : RegionPtr.BlockChain regionPtr ctx array)
    (hIdx : idxIn ip ctx regionPtr inBounds hRepr regionIsParent ctxWf > 0) :
    ip.prev! ctx = some (array[idxIn ip ctx regionPtr inBounds hRepr regionIsParent ctxWf - 1]'(by apply idxIn.pred_lt_size <;> grind)) := by
  have := idxIn.le_size_blockList ip ctx regionPtr (hRepr := by grind) (by grind) (by grind) (by grind) (by grind)
  have : array = regionPtr.blockList ctx (by grind) (by grind) := by grind
  by_cases array.size = ip.idxIn ctx regionPtr inBounds hRepr regionIsParent ctxWf
  · have : ip = atEnd regionPtr := by grind [idxIn_eq_size_blockList_iff_eq_atEnd]
    grind [RegionPtr.BlockChain]
  · have : ip.idxIn ctx regionPtr (by grind) (by grind) (by grind) (by grind) < array.size := by grind
    have := hChain.prev _ hIdx (by grind)
    cases ip <;> grind

@[grind .]
theorem idxIn_Before_lt_size :
    idxIn (before bl) ctx regionPtr inBounds hRepr regionIsParent ctxWf <
    (RegionPtr.blockList regionPtr ctx ctxWf regionInBounds).size := by
  grind [RegionPtr.BlockChain, RegionPtr.blockListWF]

end BlockInsertPoint

end Veir
