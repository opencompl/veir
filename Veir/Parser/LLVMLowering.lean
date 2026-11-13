import Veir.Parser.NameResolutionSketch
import Veir.Parser.DecidableInBounds
import Veir.Rewriter.WfRewriter
import Veir.OpCode
import Veir.Printer
import Veir.Dominance

namespace Veir.LLVMLowering

open LLVMParserProp NameResolutionSketch

abbrev LoweringError := String
abbrev LowerM := StateT (WfIRContext OpCode) (Except LoweringError)

def lowerType : LLType → TypeAttr
  | .int width => TypeAttr.of IntegerType (.signless width)

/-- Create an optionally attached operation, checking the construction helper's pointer preconditions. -/
def emit (opcode : Llvm) (types : Array TypeAttr) (operands : Array ValuePtr)
    (regions : Array RegionPtr) (properties : propertiesOf opcode) (block : BlockPtr) (insert : Bool := true) :
    LowerM OperationPtr := do
  let ip := if insert then some (InsertPoint.atEnd block) else none
  let ctx ← get
  if hoper : ∀ v ∈ operands, v.InBounds ctx.raw then
    if hregions : ∀ r ∈ regions, r.InBounds ctx.raw then
      if hins : ip.maybe InsertPoint.InBounds ctx.raw then
        let some (ctx', op) := WfRewriter.createOp ctx opcode types operands #[] regions
            properties ip hoper (by simp) hregions hins
          | throw "could not create operation"
        set ctx'
        return op
      else throw "invalid insertion block"
    else throw "invalid operation region"
  else throw "invalid operand"

/-- Create a detached function body with one entry block. -/
def createBody (types : Array TypeAttr) : LowerM (RegionPtr × BlockPtr) := do
  let some (ctx, region) := WfRewriter.createRegion (← get)
    | throw "could not create region"
  if hip : (some (BlockInsertPoint.atEnd region)).maybe BlockInsertPoint.InBounds ctx.raw then
    let some (ctx', block) := WfRewriter.createBlock ctx types (some (.atEnd region)) hip
      | throw "could not create entry block"
    set ctx'
    return (region, block)
  else throw "invalid body region"

/-- Resolve a reference through the complete result table, or materialise a literal. -/
def lowerValue (block : BlockPtr) (results : Array ValuePtr) (ty : LLType) :
    ResolvedValue → LowerM ValuePtr
  | .ref (.param i) => do
      let ctx ← get
      if i < block.getNumArguments! ctx.raw then
        return .blockArgument { block, index := i }
      else throw s!"parameter index {i} is out of bounds"
  | .ref (.inst i) =>
      match results[i]? with
      | some value => pure value
      | none => throw s!"instruction index {i} is out of bounds"
  | .intConst value => do
      let .int width := ty
      let op ← emit .mlir__constant #[lowerType ty] #[] #[]
        { value := .integer (IntegerAttr.ofInt value (.signless width)) } block
      return .opResult (op.getResult 0)

/-- Allocate an instruction's result before resolving any operands. -/
def lowerInst (block : BlockPtr) : ResolvedAST → LowerM OperationPtr
  | .bin op ty _ _ =>
      match op with
      | .and => emit .and #[lowerType ty] #[] #[] () block false
      | .or => emit .or #[lowerType ty] #[] #[] { disjoint := false } block false
      | .xor => emit .xor #[lowerType ty] #[] #[] () block false

def pushValue (op : OperationPtr) (v : ValuePtr) : LowerM Unit := do
  let ctx ← get
  if ho : op.InBounds ctx.raw then
    if hv : v.InBounds ctx.raw then set (WfRewriter.pushOperand ctx op v ho hv)
    else throw "invalid operand"
  else throw "invalid instruction"

def attachInst (block : BlockPtr) (op : OperationPtr) : LowerM Unit := do
  let ctx ← get
  if ho : op.InBounds ctx.raw then
    if hb : (InsertPoint.atEnd block).InBounds ctx.raw then
      let some ctx' := WfRewriter.insertOp ctx op (.atEnd block) ho hb
        | throw "could not insert instruction"
      set ctx'
    else throw "invalid insertion block"
  else throw "invalid instruction"

/-- Wire an allocated instruction's operands, then insert it after its constants. -/
def wireInst (block : BlockPtr) (results : Array ValuePtr) : ResolvedAST × OperationPtr → LowerM Unit
  | (.bin _ ty lhs rhs, op) => do
      pushValue op (← lowerValue block results ty lhs)
      pushValue op (← lowerValue block results ty rhs)
      attachInst block op

/-- Allocate all definitions, then wire operands and insert each instruction after its constants. -/
def lowerInsts (block : BlockPtr) (insts : List ResolvedAST) : LowerM (Array ValuePtr) := do
  let ops ← insts.mapM (lowerInst block)
  let results := ops.toArray.map (fun op => ValuePtr.opResult (op.getResult 0))
  (insts.zip ops).forM (wireInst block results)
  return results

def lowerFunction (moduleBlock : BlockPtr) (f : ResolvedFunction) : LowerM OperationPtr := do
  let inputs := f.header.params.toArray.map (lowerType ·.ty)
  let output := lowerType f.header.retType
  let (region, block) ← createBody inputs
  let results ← lowerInsts block f.insts
  let value ← lowerValue block results f.header.retType f.result
  let _ ← emit .return #[] #[value] #[] () block
  emit .func #[] #[] #[region]
    { sym_name := ⟨f.header.name.toUTF8⟩
      function_type := { inputs := inputs.map Subtype.val, outputs := #[output.val] }
      extra := .empty } moduleBlock

def lowerFunctions (block : BlockPtr) (fs : List ResolvedFunction) : LowerM Unit :=
  fs.forM (fun f => do let _ ← lowerFunction block f)

/-- Prototype lowering of the resolved single-block integer fragment.
Supports forward references and rejects undefined references; LLVM validity is checked separately. -/
def lowerModule (m : ResolvedModule) :
    Except LoweringError (WfIRContext OpCode × OperationPtr) := do
  let some (ctx, root) := WfIRContext.create OpCode
    | throw "could not create module"
  let some block := (root.getRegion! ctx.raw 0).getFirstBlock! ctx.raw
    | throw "module has no body block"
  let ((), ctx') ← (lowerFunctions block m.funcs).run ctx
  return (ctx', root)

/-! Declarative specification of the final graph. Each instruction lowers to a tile containing
its operand constants followed by its defining op. Local names and allocation IDs are ignored.
This specifies the single-block representation, not full LLVM verification. -/

section Specification

variable (ctx : WfIRContext OpCode)

/-- Equality of observable operation fields, excluding allocation and use-list links. -/
def MatchesOp (op : OperationPtr)
    {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpCode Dialect]
    (opcode : Dialect) (types : Array TypeAttr) (operands : Array ValuePtr)
    (regions : Array RegionPtr) (properties : propertiesOf opcode) : Prop :=
  op.InBounds ctx.raw ∧ op.getProperties! ctx.raw opcode = properties ∧
  (op.getOpType! ctx.raw, op.getResultTypes! ctx.raw, op.getOperands! ctx.raw,
    op.getRegions! ctx.raw, op.getNumSuccessors! ctx.raw, op.getAttributes! ctx.raw) =
  (ofDialect OpCode opcode, types, operands, regions, 0, DictionaryAttr.empty)

def binOpcode : BinOp → Llvm
  | .and => .and
  | .or => .or
  | .xor => .xor

abbrev ValueMap := ValueId → Option ValuePtr

/-- `OperandTile values ty val v cs`: `val` denotes `v`, and `cs` are the ops materialised
for it: none for a reference, one `mlir.constant` for a literal. -/
def OperandTile (values : ValueMap) : LLType → ResolvedValue → ValuePtr → List OperationPtr → Prop
  | _, .ref id, v, cs => values id = some v ∧ cs = []
  | .int w, .intConst n, v, cs => ∃ c, cs = [c] ∧ v = .opResult (c.getResult 0) ∧
      MatchesOp ctx c Llvm.mlir__constant #[lowerType (.int w)] #[] #[]
        (LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt n (.signless w))))

/-- `LowersInstTile values id inst tile`: `inst`, named `id`, lowers to exactly the ops `tile`:
the constants of its operands, left to right, followed by its defining op. -/
def LowersInstTile (values : ValueMap) (id : ValueId) : ResolvedAST → List OperationPtr → Prop
  | .bin opc ty l r, tile => ∃ vl vr cl cr op, tile = cl ++ cr ++ [op] ∧
      OperandTile ctx values ty l vl cl ∧ OperandTile ctx values ty r vr cr ∧
      values id = some (.opResult (op.getResult 0)) ∧
      MatchesOp ctx op (binOpcode opc) #[lowerType ty] #[vl, vr] #[] default

/-- All references name existing definitions. Each instruction lowers to a tile of ops,
and the body block is exactly the tiles, then
the return value's constants, then the return. This fixes operation order, not dominance. -/
def LowersFunctionTiles (f : ResolvedFunction) (op : OperationPtr) : Prop :=
  ValidResolvedFunction f ∧
  ∃ region block, ∃ tiles : List (List OperationPtr), ∃ cs ret v, ∃ values : ValueMap,
    MatchesOp ctx op Llvm.func #[] #[] #[region]
      (LLVMFuncProperties.mk ⟨f.header.name.toUTF8⟩
        { inputs := f.header.params.toArray.map (fun p => (lowerType p.ty).val)
          outputs := #[(lowerType f.header.retType).val] } .empty) ∧
    region.BlockChain ctx.raw #[block] ∧
    block.getArgumentTypes! ctx.raw = f.header.params.toArray.map (lowerType ·.ty) ∧
    (∀ i, values (.param i) = (block.getArguments! ctx.raw)[i]?) ∧
    ResolvesList (fun (inst, i) => LowersInstTile ctx values (.inst i) inst) f.insts.zipIdx tiles ∧
    OperandTile ctx values f.header.retType f.result v cs ∧
    MatchesOp ctx ret Llvm.return #[] #[v] #[] () ∧
    block.OpChain ctx.raw (tiles.flatten ++ cs ++ [ret]).toArray


/-- Only the module reachable from the root is specified;  We don't require Dominance -/
def LowersModule (m : ResolvedModule) (root : OperationPtr) : Prop :=
  ∃ (region : RegionPtr) (block : BlockPtr) (funcs : List OperationPtr),
    MatchesOp ctx root Builtin.module #[] #[] #[region] default ∧
    region.BlockChain ctx.raw #[block] ∧
    block.OpChain ctx.raw funcs.toArray ∧
    root.getParent! ctx.raw = none ∧
    block.getArgumentTypes! ctx.raw = #[] ∧ ResolvesList (LowersFunctionTiles ctx) m.funcs funcs



end Specification

section Soundness

set_option maxRecDepth 4000
set_option maxHeartbeats 800000

variable {ctx ctx' ctx'' : WfIRContext OpCode} {block : BlockPtr} {changed changed' : List OperationPtr}
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpCode Dialect]
variable {opcode : Dialect} {properties : propertiesOf opcode}

attribute [local simp] StateT.run StateT.bind StateT.get StateT.set StateT.pure StateT.lift
  bind pure get getThe MonadState.get MonadStateOf.get set MonadStateOf.set
  Except.pure Except.bind throw throwThe MonadExceptOf.throw

theorem run_bind {x : LowerM α} {f : α → LowerM β} : (x >>= f).run ctx = .ok p ↔
    ∃ a ctx₁, x.run ctx = .ok (a, ctx₁) ∧ (f a).run ctx₁ = .ok p := by
  cases hx : x ctx <;> simp_all; exact ⟨fun h => ⟨_, _, rfl, h⟩, fun ⟨_, _, he, h⟩ => he ▸ h⟩

theorem run_pure {a : α} : (pure a : LowerM α).run ctx = .ok p ↔ p = (a, ctx) := by simp [eq_comm]

/-! Primitive rewriter steps. -/

theorem createOp_matches
    (h : WfRewriter.createOp ctx opcode types operands #[] regions properties ip
      hoper hsucc hregions hins = some (ctx', op)) :
    MatchesOp ctx' op opcode types operands regions properties := by
  have : op.getRegions! ctx'.raw = regions := by
    apply Array.ext <;> grind
  have := WfRewriter.createOp_new_inBounds op h
  simp only [MatchesOp, Prod.mk.injEq]; simp_getset; grind

theorem MatchesOp.pushOperand (h : MatchesOp ctx op opcode types operands regions properties) :
    MatchesOp (WfRewriter.pushOperand ctx target value ht hv) op opcode types
      (if op = target then operands.push value else operands) regions properties := by
  simp only [MatchesOp, Prod.mk.injEq, WfRewriter.pushOperand] at *; simp_getset; grind

theorem MatchesOp.insertOp (h : MatchesOp ctx op opcode types operands regions properties)
    (hc : WfRewriter.insertOp ctx target ip ht hi = some ctx') :
    MatchesOp ctx' op opcode types operands regions properties := by
  have hr : op.getRegions! ctx'.raw = op.getRegions! ctx.raw := by apply Array.ext <;> grind
  simp only [MatchesOp, Prod.mk.injEq] at *; simp_getset; grind

theorem MatchesOp.createOp (h : MatchesOp ctx op opcode types operands regions properties)
    {newCode : Llvm} {newProps : propertiesOf newCode}
    (hc : WfRewriter.createOp ctx newCode ts vs bs rs newProps ip ho hb hr hi = some (ctx', newOp)) :
    MatchesOp ctx' op opcode types operands regions properties := by
  have hn : op ≠ newOp := by have := WfRewriter.createOp_new_not_inBounds newOp hc; grind [MatchesOp]
  have hr : op.getRegions! ctx'.raw = op.getRegions! ctx.raw := by apply Array.ext <;> grind
  simp only [MatchesOp, Prod.mk.injEq] at *; simp_getset; grind

theorem MatchesOp.createRegion (h : MatchesOp ctx op opcode types operands regions properties)
    (hc : WfRewriter.createRegion ctx = some (ctx', region)) :
    MatchesOp ctx' op opcode types operands regions properties := by
  simp only [WfRewriter.createRegion] at hc
  have hr : op.getRegions! ctx'.raw = op.getRegions! ctx.raw := by apply Array.ext <;> grind
  simp only [MatchesOp, Prod.mk.injEq] at *; try simp_getset
  grind

theorem MatchesOp.createBlock (h : MatchesOp ctx op opcode types operands regions properties)
    (hc : WfRewriter.createBlock ctx ts ip hi = some (ctx', block)) :
    MatchesOp ctx' op opcode types operands regions properties := by
  simp only [MatchesOp, Prod.mk.injEq] at h
  cases ip <;> unfold WfRewriter.createBlock Rewriter.createBlock at hc <;> simp only [Option.bind_eq_bind, Option.bind, pure] at hc
  all_goals have hr : op.getRegions! ctx'.raw = op.getRegions! ctx.raw := by apply Array.ext <;> grind (gen := 20)
  all_goals simp only [MatchesOp, Prod.mk.injEq] at *; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals grind (gen := 20) [OperationPtr.getProperties!, OperationPtr.getAttributes!]

theorem opChain_pushOperand (h : block.OpChain ctx.raw ops) :
    block.OpChain (WfRewriter.pushOperand ctx target value ht hv).raw ops :=
  BlockPtr.opChain_rewriter_pushOperand ctx.raw (by grind) target ht h

theorem opChain_insertOp {ho : op.InBounds ctx.raw} {hi : (InsertPoint.atEnd block).InBounds ctx.raw}
    (h : block.OpChain ctx.raw ops) (hc : WfRewriter.insertOp ctx op (.atEnd block) ho hi = some ctx') :
    block.OpChain ctx'.raw (ops.push op) := by
  have hr : Rewriter.insertOp ctx.raw op (.atEnd block) ho hi (by grind) = some ctx'.raw := by
    unfold WfRewriter.insertOp at hc; split at hc <;> grind
  have hb : block.InBounds ctx'.raw := by grind
  have he := BlockPtr.operationList_rewriter_insertOp (ctx'Wf := ctx'.wellFormed) (blockIn := hb) hr ctx.wellFormed
  have hold := (BlockPtr.operationList_iff_BlockPtr_OpChain (hctx := ctx.wellFormed) (hblock := h.blockInBounds)).mp h
  apply (BlockPtr.operationList_iff_BlockPtr_OpChain (hctx := ctx'.wellFormed) (hblock := hb)).mpr
  simpa [InsertPoint.block!_atEnd_eq, InsertPoint.idxIn_atEnd_eq, hold] using he

theorem opChain_createOp {insert : Bool}
    {hi : (if insert then some (InsertPoint.atEnd block) else none).maybe InsertPoint.InBounds ctx.raw}
    (h : block.OpChain ctx.raw ops)
    (hc : WfRewriter.createOp ctx opcode types operands #[] regions properties
      (if insert then some (.atEnd block) else none) ho hs hr hi = some (ctx', op)) :
    block.OpChain ctx'.raw (if insert then ops.push op else ops) := by
  have he : Rewriter.createOp ctx.raw opcode types operands #[] regions properties
      (if insert then some (.atEnd block) else none) ho hs hr hi (by grind) = some (ctx'.raw, op) := by
    unfold WfRewriter.createOp at hc; split at hc <;> grind
  have hb : block.InBounds ctx'.raw := by grind
  have hl := BlockPtr.operationList_rewriter_createOp (newCtxWf := ctx'.wellFormed) (blockIn := hb) he ctx.wellFormed
  have hold := (BlockPtr.operationList_iff_BlockPtr_OpChain (hctx := ctx.wellFormed) (hblock := h.blockInBounds)).mp h
  apply (BlockPtr.operationList_iff_BlockPtr_OpChain (hctx := ctx'.wellFormed) (hblock := hb)).mpr
  cases insert <;> simpa [InsertPoint.block!_atEnd_eq, InsertPoint.idxIn_atEnd_eq, hold] using hl

theorem blockChain_singleton {r : RegionPtr} {b : BlockPtr} (hr : r.InBounds ctx.raw)
    (hf : r.getFirstBlock! ctx.raw = some b) (hl : r.getLastBlock! ctx.raw = some b) : r.BlockChain ctx.raw #[b] := by
  obtain ⟨bs, hb⟩ := ctx.wellFormed.blockChain r hr
  have hinj := RegionPtr.BlockChain_array_injective hb 0 (bs.size - 1)
  have hs : bs = #[b] := by apply Array.ext <;> grind
  simpa [hs] using hb

/-! Frames: what a lowering step leaves untouched. -/

def definitionMap (ctx : WfIRContext OpCode) (block : BlockPtr) (results : Array ValuePtr) : ValueMap
  | .param i => (block.getArguments! ctx.raw)[i]?
  | .inst i => results[i]?

/-- Preserve old operation fields (except `changed`) and the op chains of blocks other than `block`. -/
structure Frame (ctx ctx' : WfIRContext OpCode) (changed : List OperationPtr) (block : BlockPtr) : Prop where
  bounds : ∀ p : GenericPtr, p.InBounds ctx.raw → p.InBounds ctx'.raw
  ops : ∀ op, op ∉ changed → ∀ {D : Type} [HasOpInfo D] [HasDialect OpCode D]
    (code : D) ts vs rs props, MatchesOp ctx op code ts vs rs props → MatchesOp ctx' op code ts vs rs props
  parents : ∀ op, op.InBounds ctx.raw → op ∉ changed → op.getParent! ctx'.raw = op.getParent! ctx.raw
  args : ∀ b : BlockPtr, b.InBounds ctx.raw → b.getArgumentTypes! ctx'.raw = b.getArgumentTypes! ctx.raw ∧ b.getArguments! ctx'.raw = b.getArguments! ctx.raw
  chains : ∀ b : BlockPtr, b ≠ block → ∀ os, b.OpChain ctx.raw os → b.OpChain ctx'.raw os
  regions : ∀ (r : RegionPtr) (b : BlockPtr), r.BlockChain ctx.raw #[b] → r.BlockChain ctx'.raw #[b]

theorem Frame.refl : Frame ctx ctx [] block :=
  ⟨fun _ h => h, fun _ _ _ _ _ _ _ _ _ _ h => h, fun _ _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ h => h, fun _ _ h => h⟩

theorem Frame.trans (h : Frame ctx ctx' changed block) (h' : Frame ctx' ctx'' changed' block) :
    Frame ctx ctx'' (changed ++ changed') block := by
  refine ⟨fun p hp => h'.bounds p (h.bounds p hp), fun op hn _ _ _ _ _ _ _ _ hm => h'.ops op (by simp_all) _ _ _ _ _ (h.ops op (by simp_all) _ _ _ _ _ hm),
    fun op ho hn => (h'.parents op (h.bounds (.operation op) ho) (by simp_all)).trans (h.parents op ho (by simp_all)),
    fun b hb => ?_, fun b hn os ho => h'.chains b hn os (h.chains b hn os ho), fun r bs hr => h'.regions r bs (h.regions r bs hr)⟩
  exact ⟨(h'.args b (h.bounds (.block b) hb)).1.trans (h.args b hb).1, (h'.args b (h.bounds (.block b) hb)).2.trans (h.args b hb).2⟩

/-- Shrink `changed` to `changed'`, dropping operations fresh in `ctx`; retarget to `other` if `block` is fresh. -/
theorem Frame.mono (h : Frame ctx ctx' changed block) (hs : ∀ op ∈ changed, op ∈ changed' ∨ ¬op.InBounds ctx.raw)
    (hb : block = other ∨ ¬block.InBounds ctx.raw) : Frame ctx ctx' changed' other := by
  refine { h with ops := ?_, parents := fun op ho hn => h.parents op ho fun hp => (hs op hp).elim hn (· ho), chains := ?_ }
  · intro op hn _ _ _ c ts vs rs ps hm; exact h.ops op (fun hp => (hs op hp).elim hn (· hm.1)) _ _ _ _ _ hm
  · rintro b hn os hc; exact h.chains b (by rintro rfl; exact hb.elim hn (· hc.blockInBounds)) os hc

theorem Frame.definitionMap_eq (h : Frame ctx ctx' changed block) (hb : b.InBounds ctx.raw) :
    definitionMap ctx' b results = definitionMap ctx b results := by
  funext id; cases id <;> simp only [definitionMap, (h.args b hb).2]

theorem Frame.numArgs {b : BlockPtr} (hf : Frame ctx ctx' changed block) (hb : b.InBounds ctx.raw) :
    b.getNumArguments! ctx'.raw = b.getNumArguments! ctx.raw := by
  simpa only [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] using congrArg Array.size (hf.args b hb).1

theorem Frame.createOp {code : Llvm} {props : propertiesOf code} {insert : Bool}
    {hi : (if insert then some (InsertPoint.atEnd block) else none).maybe InsertPoint.InBounds ctx.raw}
    (hc : WfRewriter.createOp ctx code ts vs #[] rs props
      (if insert then some (InsertPoint.atEnd block) else none) ho hs hr hi = some (ctx', op)) : Frame ctx ctx' [] block := by
  refine ⟨fun p hp => by grind, fun _ _ _ _ _ _ _ _ _ _ hm => hm.createOp hc, fun p hp _ => ?_, fun b hb => ⟨?_, ?_⟩, ?_, ?_⟩
  · have := WfRewriter.createOp_new_not_inBounds op hc; grind
  · apply Array.ext (by grind); intro i hi hi'; have := ValuePtr.getType!_WfRewriter_createOp (value := .blockArgument (b.getArgument i)) hc; grind
  · simp only [BlockPtr.getArguments!]; congr 1; grind
  · intro b hn os hb; apply BlockPtr.OpChain_unchanged hb <;> grind
  · intro r b hb; apply blockChain_singleton <;> grind

theorem Frame.pushOperand (ho : op.InBounds ctx.raw) (hv : v.InBounds ctx.raw) :
    Frame ctx (WfRewriter.pushOperand ctx op v ho hv) [op] block := by
  refine ⟨fun p hp => by grind [WfRewriter.pushOperand], fun p hn _ _ _ _ _ _ _ _ hm => by simpa [show p ≠ op by simpa using hn] using hm.pushOperand (target := op) (ht := ho) (hv := hv),
    fun p hp hn => by grind [WfRewriter.pushOperand], fun b hb => ⟨?_, ?_⟩, fun _ _ _ h => opChain_pushOperand h,
    fun _ _ h => by apply RegionPtr.blockChain_unchanged h <;> grind [WfRewriter.pushOperand]⟩
  · apply Array.ext <;> grind [WfRewriter.pushOperand]
  · simp only [BlockPtr.getArguments!]; congr 1; grind [WfRewriter.pushOperand]

theorem Frame.insertOp {ho : op.InBounds ctx.raw} {hi : (InsertPoint.atEnd block).InBounds ctx.raw}
    (hp : op.getParent! ctx.raw = none)
    (hc : WfRewriter.insertOp ctx op (.atEnd block) ho hi = some ctx') : Frame ctx ctx' [op] block := by
  refine ⟨fun p hp => by grind, fun _ _ _ _ _ _ _ _ _ _ hm => hm.insertOp hc, fun p hp hn => by grind, fun b hb => ⟨?_, ?_⟩, ?_, ?_⟩
  · apply Array.ext <;> grind [WfRewriter.insertOp]
  · simp only [BlockPtr.getArguments!]; congr 1; grind
  · intro b hn os hb; apply BlockPtr.OpChain_unchanged hb <;> grind
  · intro r b hb; apply blockChain_singleton <;> grind

theorem OperandTile.frame (hf : Frame ctx ctx' changed block)
    (h : OperandTile ctx values ty value v cs) (hn : ∀ c ∈ cs, c ∉ changed) :
    OperandTile ctx' values ty value v cs := by
  rcases value with _ | _; · exact h
  cases ty; obtain ⟨c, rfl, hv, hc⟩ := h; exact ⟨c, rfl, hv, hf.ops c (hn c (by simp)) _ _ _ _ _ hc⟩

theorem LowersInstTile.frame {id : ValueId} (hf : Frame ctx ctx' changed block)
    (h : LowersInstTile ctx values id inst tile) (hn : ∀ c ∈ tile, c ∉ changed) :
    LowersInstTile ctx' values id inst tile := by
  cases inst; obtain ⟨vl, vr, cl, cr, op, rfl, hl, hr, hv, ho⟩ := h
  exact ⟨vl, vr, cl, cr, op, rfl, hl.frame hf (by grind), hr.frame hf (by grind), hv, hf.ops op (by grind) _ _ _ _ _ ho⟩

theorem resolvesList_mono {bs : List β} (h : ResolvesList R as bs) (f : ∀ a, ∀ b ∈ bs, R a b → S a b) :
    ResolvesList S as bs := by
  induction h with
  | nil => exact .nil
  | cons hab h ih => exact .cons (f _ _ (by simp) hab) (ih fun a b hb => f a b (by simp_all))

/-! Monadic steps. -/

theorem emit_spec {opcode : Llvm} {properties : propertiesOf opcode} {insert : Bool}
    (h : (emit opcode types operands regions properties block insert).run ctx = .ok (op, ctx')) :
    Frame ctx ctx' [] block ∧ MatchesOp ctx' op opcode types operands regions properties ∧
      ¬op.InBounds ctx.raw ∧ (insert = false → op.getParent! ctx'.raw = none) ∧
      ∀ os, block.OpChain ctx.raw os → block.OpChain ctx'.raw (if insert then os.push op else os) := by
  simp [emit] at h; split at h <;> try simp at h
  split at h <;> try simp at h
  rename_i ho hr; by_cases hi : (if insert then some (InsertPoint.atEnd block) else none).maybe InsertPoint.InBounds ctx.raw
  · rw [dite_eq_left hi] at h
    rcases hc : WfRewriter.createOp ctx opcode types operands #[] regions properties _ ho (by simp) hr hi with _ | ⟨c, o⟩ <;> simp [hc] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Frame.createOp hc, createOp_matches hc, WfRewriter.createOp_new_not_inBounds _ hc, by grind, fun _ hb => opChain_createOp hb hc⟩
  · rw [dite_eq_right hi] at h; simp at h

theorem lowerValue_spec (hb : block.OpChain ctx.raw os)
    (h : (lowerValue block results ty value).run ctx = .ok (v, ctx')) :
    Frame ctx ctx' [] block ∧ ValidResolvedValue (block.getNumArguments! ctx.raw) results.size value ∧
    ∃ cs, OperandTile ctx' (definitionMap ctx block results) ty value v cs ∧
      block.OpChain ctx'.raw (os ++ cs.toArray) ∧ ∀ c ∈ cs, ¬c.InBounds ctx.raw := by
  rcases value with ⟨i | i⟩ | n
  · simp [lowerValue] at h; split at h <;> simp_all [Frame.refl, OperandTile, definitionMap, ValidResolvedValue, BlockPtr.getArguments!, BlockPtr.getArgument]
  · cases hr : results[i]? <;> simp_all [lowerValue, Frame.refl, OperandTile, definitionMap, ValidResolvedValue] <;> grind
  · cases ty; simp only [lowerValue, run_bind, run_pure, Prod.mk.injEq] at h; obtain ⟨c, c₁, he, rfl, rfl⟩ := h
    obtain ⟨hf, hm, hn, -, hc⟩ := emit_spec he
    exact ⟨hf, trivial, [c], ⟨c, rfl, rfl, hm⟩, by simpa using hc _ hb, by simpa⟩

/-! Instructions are first allocated, detached, then wired. -/

def Allocated (ctx : WfIRContext OpCode) : ResolvedAST → OperationPtr → Prop
  | .bin opc ty _ _, op => MatchesOp ctx op (binOpcode opc) #[lowerType ty] #[] #[] default ∧ op.getParent! ctx.raw = none

theorem Allocated.inBounds (h : Allocated ctx inst op) : op.InBounds ctx.raw := by cases inst; exact h.1.1

theorem Allocated.frame (hf : Frame ctx ctx' changed block) (hn : op ∉ changed)
    (h : Allocated ctx inst op) : Allocated ctx' inst op := by
  cases inst; exact ⟨hf.ops op hn _ _ _ _ _ h.1, (hf.parents op h.1.1 hn).trans h.2⟩

theorem allocate_sound (h : (insts.mapM (lowerInst block)).run ctx = .ok (ops, ctx')) :
    Frame ctx ctx' [] block ∧ ResolvesList (Allocated ctx') insts ops ∧ ops.Nodup ∧
      (∀ op ∈ ops, ¬op.InBounds ctx.raw) ∧ ∀ os, block.OpChain ctx.raw os → block.OpChain ctx'.raw os := by
  induction insts generalizing ctx ops with
  | nil => simp only [List.mapM_nil, run_pure, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨Frame.refl, .nil, .nil, by simp, fun _ h => h⟩
  | cons inst insts ih =>
    simp only [List.mapM_cons, run_bind, run_pure, Prod.mk.injEq] at h; obtain ⟨op, c₁, ho, ops, c₂, hs, rfl, rfl⟩ := h
    obtain ⟨hf, ha, hn, hc⟩ : Frame ctx c₁ [] block ∧ Allocated c₁ inst op ∧ ¬op.InBounds ctx.raw ∧
        ∀ os, block.OpChain ctx.raw os → block.OpChain c₁.raw os := by
      rcases inst with ⟨_ | _ | _, _, _, _⟩ <;> obtain ⟨hf, hm, hn, hp, hc⟩ := emit_spec ho <;> exact ⟨hf, ⟨hm, hp rfl⟩, hn, by simpa using hc⟩
    obtain ⟨hf', ha', hd, hn', hc'⟩ := ih hs
    exact ⟨hf.trans hf', .cons (ha.frame hf' (by simp)) ha', List.nodup_cons.2 ⟨fun hm => hn' _ hm ha.inBounds, hd⟩,
      by simpa [hn] using fun p hp hi => hn' p hp (hf.bounds (.operation p) hi), fun os h => hc' _ (hc _ h)⟩

theorem lowerOperand_sound {code : Llvm} {props : propertiesOf code}
    (hm : MatchesOp ctx op code ts vs rs props) (hb : block.OpChain ctx.raw os)
    (hl : (lowerValue block results ty value).run ctx = .ok (v, ctx₁)) (hp : (pushValue op v).run ctx₁ = .ok ((), ctx')) :
    ∃ cs, OperandTile ctx' (definitionMap ctx block results) ty value v cs ∧
      MatchesOp ctx' op code ts (vs.push v) rs props ∧ op.getParent! ctx'.raw = op.getParent! ctx.raw ∧
      block.OpChain ctx'.raw (os ++ cs.toArray) ∧ Frame ctx ctx' [op] block ∧
      (∀ c ∈ cs, c ∉ [op] ∧ ¬c.InBounds ctx.raw) ∧ ValidResolvedValue (block.getNumArguments! ctx.raw) results.size value := by
  obtain ⟨hf, hv, cs, ht, hc, hn⟩ := lowerValue_spec hb hl
  simp [pushValue] at hp; split at hp <;> try simp at hp
  split at hp <;> try simp at hp
  subst ctx'; rename_i ho hv'
  have hd : ∀ c ∈ cs, c ∉ [op] := fun c hc he => hn c hc (by simp_all [hm.1])
  exact ⟨cs, ht.frame (Frame.pushOperand (block := block) ho hv') hd, by simpa using (hf.ops op (by simp) _ _ _ _ _ hm).pushOperand (target := op) (ht := ho) (hv := hv'),
    by simpa [WfRewriter.pushOperand] using hf.parents op hm.1 (by simp), opChain_pushOperand hc,
    hf.trans (Frame.pushOperand (block := block) ho hv'), fun c h => ⟨hd c h, hn c h⟩, hv⟩

theorem wireInst_sound (ha : Allocated ctx inst op) (hb : block.OpChain ctx.raw os)
    (hid : results[i]? = some (.opResult (op.getResult 0)))
    (h : (wireInst block results (inst, op)).run ctx = .ok ((), ctx')) :
    ∃ tile, LowersInstTile ctx' (definitionMap ctx block results) (.inst i) inst tile ∧
      block.OpChain ctx'.raw (os ++ tile.toArray) ∧ Frame ctx ctx' [op] block ∧
      (∀ c ∈ tile, c = op ∨ ¬c.InBounds ctx.raw) ∧ ValidResolvedInst (block.getNumArguments! ctx.raw) results.size inst := by
  rcases inst with ⟨opc, ty, lhs, rhs⟩; simp only [wireInst, run_bind] at h
  obtain ⟨vl, c₁, hl, _, c₂, hpl, vr, c₃, hr, _, c₄, hpr, hi⟩ := h
  obtain ⟨cl, htl, hml, hpl, hcl, hfl, hnl, hvl⟩ := lowerOperand_sound ha.1 hb hl hpl
  obtain ⟨cr, htr, hmr, hpr, hcr, hfr, hnr, hvr⟩ := lowerOperand_sound hml hcl hr hpr
  simp [attachInst] at hi; split at hi <;> try simp at hi
  split at hi <;> try simp at hi
  rename_i ho hip; rcases hc : WfRewriter.insertOp c₄ op (.atEnd block) ho hip with _ | c <;> simp [hc] at hi; subst hi
  have hfi := Frame.insertOp (hpr.trans (hpl.trans ha.2)) hc
  refine ⟨cl ++ cr ++ [op], ⟨vl, vr, cl, cr, op, rfl, ((htl.frame hfr (by grind)).frame hfi (by grind)), ?_, hid, by simpa using hmr.insertOp hc⟩,
    by simpa [Array.append_assoc] using opChain_insertOp hcr hc, (hfl.trans (hfr.trans hfi)).mono (by simp) (.inl rfl), ?_, ?_⟩
  · simpa [hfl.definitionMap_eq hb.blockInBounds] using htr.frame hfi (by grind)
  · simp only [List.mem_append, List.mem_singleton]; rintro c ((hc | hc) | rfl)
    · exact .inr (hnl c hc).2
    · exact .inr fun h => (hnr c hc).2 (hfl.bounds (.operation c) h)
    · exact .inl rfl
  · simpa [ValidResolvedInst, hfl.numArgs hb.blockInBounds] using And.intro hvl hvr

section Lists
variable {R : α → β → Prop} {as : List α} {bs : List β}

theorem _root_.Veir.NameResolutionSketch.ResolvesList.length (h : ResolvesList R as bs) : as.length = bs.length := by induction h <;> simp_all

theorem _root_.Veir.NameResolutionSketch.ResolvesList.zipIdx (h : ResolvesList R as bs) (pre : List β) :
    ResolvesList (fun e b => R e.1 b ∧ (pre ++ bs)[e.2]? = some b) (as.zipIdx pre.length) bs := by
  induction h generalizing pre with
  | nil => exact .nil
  | @cons _ b _ _ hr _ ih => exact .cons ⟨hr, by simp⟩ (by simpa using ih (pre ++ [b]))

theorem _root_.Veir.NameResolutionSketch.ResolvesList.mem_right (h : ResolvesList R as bs) (hb : b ∈ bs) : ∃ a, R a b := by
  induction h with
  | nil => simp at hb
  | cons hab _ ih => exact (List.mem_cons.mp hb).elim (fun he => ⟨_, he ▸ hab⟩) ih

end Lists

def Ready (ctx : WfIRContext OpCode) (results : Array ValuePtr) (e : ResolvedAST × Nat) (op : OperationPtr) : Prop :=
  Allocated ctx e.1 op ∧ results[e.2]? = some (.opResult (op.getResult 0))

theorem wire_sound (hb : block.OpChain ctx.raw os)
    (ha : ResolvesList (Ready ctx results) entries ops) (hn : ops.Nodup)
    (h : ((entries.map Prod.fst).zip ops |>.forM (wireInst block results)).run ctx = .ok ((), ctx')) :
    Frame ctx ctx' ops block ∧ (∀ inst ∈ entries.map Prod.fst, ValidResolvedInst (block.getNumArguments! ctx.raw) results.size inst) ∧
    ∃ tiles, ResolvesList (fun (inst, i) => LowersInstTile ctx' (definitionMap ctx block results) (.inst i) inst) entries tiles ∧
      block.OpChain ctx'.raw (os ++ tiles.flatten.toArray) := by
  induction entries generalizing ops ctx os with
  | nil => cases ha; simp at h; subst ctx'; exact ⟨Frame.refl, by simp, [], .nil, by simpa using hb⟩
  | cons e entries ih =>
    cases ha with | cons he ha =>
    obtain ⟨hno, hnt⟩ := List.nodup_cons.mp hn
    simp only [List.map_cons, List.zip_cons_cons, List.forM_eq_forM, List.forM_cons, run_bind] at h; obtain ⟨_, c₁, hh, hs⟩ := h
    obtain ⟨tile, ht, hc, hf, hnew, hv⟩ := wireInst_sound he.1 hb he.2 hh
    obtain ⟨hf', hv', tiles, hi, hc'⟩ := ih hc (resolvesList_mono ha fun _ p hp he => ⟨he.1.frame hf (by grind), he.2⟩) hnt hs
    have hm := hf.definitionMap_eq (results := results) hb.blockInBounds
    refine ⟨hf.trans hf', ?_, tile :: tiles, .cons (ht.frame hf' fun c hc hp => ?_) (by simpa only [hm] using hi), by simpa [Array.append_assoc] using hc'⟩
    · simpa [hv, hf.numArgs hb.blockInBounds] using hv'
    · obtain ⟨_, ha⟩ := ha.mem_right hp; rcases hnew c hc with rfl | hc
      · exact hno hp
      · exact hc ha.1.inBounds

theorem lowerInsts_sound (hb : block.OpChain ctx.raw os)
    (h : (lowerInsts block insts).run ctx = .ok (results, ctx')) :
    Frame ctx ctx' [] block ∧ results.size = insts.length ∧
    (∀ inst ∈ insts, ValidResolvedInst (block.getNumArguments! ctx.raw) insts.length inst) ∧
    ∃ tiles, ResolvesList (fun (inst, i) => LowersInstTile ctx' (definitionMap ctx' block results) (.inst i) inst) insts.zipIdx tiles ∧
      block.OpChain ctx'.raw (os ++ tiles.flatten.toArray) := by
  simp only [lowerInsts, run_bind, run_pure, Prod.mk.injEq] at h; obtain ⟨ops, c₁, ha, _, c₂, hw, rfl, rfl⟩ := h
  obtain ⟨hf, hal, hd, hn, hc⟩ := allocate_sound ha
  have hs := hal.length.symm
  obtain ⟨hf', hv, hw⟩ := wire_sound (results := ops.toArray.map fun op => .opResult (op.getResult 0)) (hc os hb) (by exact resolvesList_mono (hal.zipIdx []) fun _ _ _ ⟨h₁, h₂⟩ => ⟨h₁, by simp at h₂; simp [h₂]⟩)
    hd (by simpa only [List.zipIdx_map_fst] using hw)
  refine ⟨(hf.trans hf').mono (fun o h => .inr (hn o (by simpa using h))) (.inl rfl), by simp [hs], by simpa [hf.numArgs hb.blockInBounds, hs] using hv, ?_⟩
  simpa only [hf'.definitionMap_eq (hf.bounds (.block block) hb.blockInBounds), List.length_nil] using hw

/-! Functions and modules. -/

theorem createBlock_raw (h : WfRewriter.createBlock ctx ts ip hi = some (ctx', body)) :
    Rewriter.createBlock ctx.raw ts ip (by grind) hi = some (ctx'.raw, body) := by
  unfold WfRewriter.createBlock at h; split at h <;> grind

theorem createBlock_spec
    (hb : WfRewriter.createBlock ctx ts (some (.atEnd region)) hi = some (ctx', body))
    (_ : region.getFirstBlock! ctx.raw = none) (hl : region.getLastBlock! ctx.raw = none) :
    ¬body.InBounds ctx.raw ∧ region.BlockChain ctx'.raw #[body] ∧ body.OpChain ctx'.raw #[] ∧
      body.getArgumentTypes! ctx'.raw = ts ∧ ∀ op : OperationPtr, op.getParent! ctx'.raw = op.getParent! ctx.raw := by
  have hbr := createBlock_raw hb; have hc := BlockPtr.opChain_rewriter_createBlock_new hbr
  unfold Rewriter.createBlock at hbr; simp only [Option.bind_eq_bind, Option.bind] at hbr
  split at hbr <;> try contradiction
  split at hbr <;> try contradiction
  simp only [Option.some.injEq, Prod.mk.injEq] at hbr; rcases hbr with ⟨rfl, rfl⟩
  refine ⟨by grind, blockChain_singleton (by grind) (by grind (gen := 20)) (by grind (gen := 20)), hc, Array.ext (by grind (gen := 20)) (by grind (gen := 20)), fun op => ?_⟩
  simp_getset; grind

theorem createBody_spec (h : (createBody ts).run ctx = .ok ((region, body), ctx')) :
    Frame ctx ctx' [] block ∧ ¬body.InBounds ctx.raw ∧ region.BlockChain ctx'.raw #[body] ∧
      body.OpChain ctx'.raw #[] ∧ body.getArgumentTypes! ctx'.raw = ts := by
  rcases hr : WfRewriter.createRegion ctx with _ | ⟨ctx₁, r⟩; · simp [createBody, hr] at h
  rcases (Classical.em ((some (BlockInsertPoint.atEnd r)).maybe BlockInsertPoint.InBounds ctx₁.raw)).symm with hi | hi; · simp [createBody, hr, hi] at h
  rcases hb : WfRewriter.createBlock ctx₁ ts (some (.atEnd r)) hi with _ | ⟨c₂, b⟩ <;> simp [createBody, hr, hi, hb] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  have hrr : Rewriter.createRegion ctx.raw = some (ctx₁.raw, r) := by unfold WfRewriter.createRegion at hr; split at hr <;> grind
  obtain ⟨hn, hblocks, hchain, ht, -⟩ := createBlock_spec hb (by grind) (by grind)
  refine ⟨?_, fun hi => hn (by grind), hblocks, hchain, ht⟩; clear hn hblocks hchain ht; have hbr := createBlock_raw hb
  refine ⟨fun p hp => by grind, fun _ _ _ _ _ _ _ _ _ _ hm => (hm.createRegion hr).createBlock hb, ?_, ?_, ?_, ?_⟩
  all_goals (unfold Rewriter.createBlock at hbr; simp only [Option.bind_eq_bind, Option.bind] at hbr; split at hbr <;> try contradiction)
  all_goals (split at hbr <;> try contradiction); all_goals simp only [Option.some.injEq, Prod.mk.injEq] at hbr; all_goals rcases hbr with ⟨rfl, rfl⟩
  · intro op ho hn; grind (gen := 20)
  · intro b hb; constructor <;> first | (apply Array.ext <;> grind (gen := 20)) | (simp only [BlockPtr.getArguments!]; congr 1; grind (gen := 20))
  · intro b hn os hc; exact BlockPtr.opChain_rewriter_createBlock (BlockPtr.opChain_rewriter_createRegion hc hrr) (createBlock_raw hb)
  · intro r b hc; have hf₀ : r.getFirstBlock! ctx.raw = some b := (by simpa using hc.first); have hl₀ : r.getLastBlock! ctx.raw = some b := (by simpa using hc.last)
    have hfirst := RegionPtr.getFirstBlock!_BlockPtr_allocEmpty (region := r) (show BlockPtr.allocEmpty ctx₁.raw = some (_, _) by assumption); have hlast := RegionPtr.getLastBlock!_BlockPtr_allocEmpty (region := r) (show BlockPtr.allocEmpty ctx₁.raw = some (_, _) by assumption); apply blockChain_singleton <;> (try simp_getset) <;> grind (gen := 20)

/-- A function lowering that survives any later frame of the module block. -/
def SafeFunction (ctx : WfIRContext OpCode) (block : BlockPtr) (f : ResolvedFunction) (op : OperationPtr) : Prop :=
  ∀ ctx', Frame ctx ctx' [] block → LowersFunctionTiles ctx' f op

theorem lowerFunction_sound (hb : moduleBlock.OpChain ctx.raw os)
    (h : (lowerFunction moduleBlock f).run ctx = .ok (op, ctx')) :
    Frame ctx ctx' [] moduleBlock ∧ SafeFunction ctx' moduleBlock f op ∧ moduleBlock.OpChain ctx'.raw (os.push op) := by
  simp only [lowerFunction, run_bind] at h; obtain ⟨⟨region, body⟩, c₁, hc, results, c₂, hi, v, c₃, hv, ret, c₄, hr, hf⟩ := h
  obtain ⟨hF₁, hnew, hblocks, hchain, htypes⟩ := createBody_spec (block := body) hc
  obtain ⟨hF₂, hsize, hvi, tiles, hti, hci⟩ := lowerInsts_sound hchain hi
  obtain ⟨hF₃, hvv, cs, htv, hcv, -⟩ := lowerValue_spec hci hv
  obtain ⟨hF₄, hmr, -, -, hcr⟩ := emit_spec hr; obtain ⟨hF₅, hmf, -, -, hcf⟩ := emit_spec hf
  have hB := hF₁.trans (hF₂.trans (hF₃.trans hF₄)); have hbin : body.InBounds c₁.raw := hblocks.arrayInBounds (by simp)
  have hne : moduleBlock ≠ body := by rintro rfl; exact hnew hb.blockInBounds
  refine ⟨(hB.mono (changed' := []) (by simp) (.inr hnew)).trans hF₅, fun c'' hG' => ?_, by simpa using hcf _ (hB.chains _ hne _ hb)⟩
  have hG := hF₅.trans hG'; have hB' := hF₃.trans hF₄; have hbin₂ := hF₂.bounds (.block body) hbin
  have ht := (hG.args body ((hF₂.trans hB').bounds (.block body) hbin)).1.trans ((hF₂.trans hB').args body hbin).1
  have heq : (f.header.params.toArray.map (lowerType ·.ty)).map Subtype.val = f.header.params.toArray.map (fun p => (lowerType p.ty).val) := Array.map_map (β := TypeAttr)
  have hn : body.getNumArguments! c₁.raw = f.header.params.length := by simpa [← BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] using congrArg Array.size htypes
  refine ⟨⟨by simpa [hn] using hvi, by simpa [hsize, hF₂.numArgs hbin, hn] using hvv⟩, region, body, tiles, cs, ret, v, definitionMap c₂ body results,
    by simpa only [heq] using hG'.ops op (by simp) _ _ _ _ _ hmf, hG.regions _ _ ((hF₂.trans hB').regions _ _ hblocks), ht.trans htypes, fun i => ?_,
    resolvesList_mono hti fun _ _ _ h => (h.frame hB' (by simp)).frame hG (by simp), (htv.frame hF₄ (by simp)).frame hG (by simp),
    hG.ops ret (by simp) _ _ _ _ _ hmr, by simpa using hG.chains body hne.symm _ (hcr _ hcv)⟩
  simp only [definitionMap, (hG.args body (hB'.bounds _ hbin₂)).2, (hB'.args body hbin₂).2]

theorem lowerFunctions_sound (hb : block.OpChain ctx.raw os)
    (h : (lowerFunctions block fs).run ctx = .ok ((), ctx')) :
    Frame ctx ctx' [] block ∧ ∃ ops, ResolvesList (SafeFunction ctx' block) fs ops ∧ block.OpChain ctx'.raw (os ++ ops.toArray) := by
  induction fs generalizing ctx os with
  | nil => simp [lowerFunctions] at h; subst ctx'; exact ⟨Frame.refl, [], .nil, by simpa using hb⟩
  | cons f fs ih =>
    simp only [lowerFunctions, List.forM_eq_forM, List.forM_cons, run_bind, run_pure, Prod.mk.injEq] at h ih
    obtain ⟨_, c₁, ⟨op, c₀, hh, -, rfl⟩, hs⟩ := h
    obtain ⟨hf, hs', hc⟩ := lowerFunction_sound hb hh; obtain ⟨hf', ops, hr, hc'⟩ := ih hc hs
    exact ⟨hf.trans hf', op :: ops, .cons (fun c hG => hs' c (hf'.trans hG)) hr, by simpa using hc'⟩

theorem createOp_of_raw {code : Dialect} {props : propertiesOf code}
    (h : Rewriter.createOp ctx.raw code ts vs bs rs props ip ho hb hr hi (by grind) = some (ctx'.raw, op)) :
    WfRewriter.createOp ctx code ts vs bs rs props ip ho hb hr hi = some (ctx', op) := by
  unfold WfRewriter.createOp; split <;> simp_all

theorem createBlock_of_raw (h : Rewriter.createBlock ctx.raw ts ip (by grind) hi = some (ctx'.raw, body)) :
    WfRewriter.createBlock ctx ts ip hi = some (ctx', body) := by
  unfold WfRewriter.createBlock; split <;> simp_all

theorem createModule_sound (h : WfIRContext.create OpCode = some (ctx, root)) :
    ∃ region block, MatchesOp ctx root Builtin.module #[] #[] #[region] default ∧
      region.BlockChain ctx.raw #[block] ∧ block.OpChain ctx.raw #[] ∧
      root.getParent! ctx.raw = none ∧ block.getArgumentTypes! ctx.raw = #[] := by
  unfold WfIRContext.create at h; split at h <;> try contradiction
  rename_i raw root₀ hc; simp at h; rcases h with ⟨rfl, rfl⟩; unfold IRContext.create at hc; simp only [pure] at hc
  split at hc <;> try contradiction
  rename_i raw₁ region hreg; split at hc <;> try contradiction
  rename_i raw₂ root hroot; split at hc <;> try contradiction
  rename_i raw₃ block hblock; simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
  have hw₁ := IRContext.wellFormed_Rewriter_createRegion IRContext.empty_wellFormed hreg; have hw₂ := Rewriter.createOp_WellFormed hw₁ hroot
  have hro := createOp_of_raw (ctx := ⟨raw₁, hw₁⟩) (ctx' := ⟨raw₂, hw₂⟩) hroot
  have hb := createBlock_of_raw (ctx := ⟨raw₂, hw₂⟩) (ctx' := ⟨raw₃, by grind [Rewriter.createBlock_WellFormed]⟩) hblock
  obtain ⟨_, hblocks, hchain, htypes, hp⟩ := createBlock_spec hb (by grind (gen := 20)) (by grind (gen := 20))
  exact ⟨region, block, (createOp_matches hro).createBlock hb, hblocks, hchain, (hp root).trans (by simpa using OperationPtr.getParent!_WfRewriter_createOp (operation := root) hro), htypes⟩

theorem lowerModule_sound : lowerModule m = .ok (ctx, root) → LowersModule ctx m root := by
  intro h; rcases hc : WfIRContext.create OpCode with _ | ⟨ctx₀, root₀⟩ <;> simp [lowerModule, hc] at h
  rcases hb : (root₀.getRegion! ctx₀.raw 0).getFirstBlock! ctx₀.raw with _ | block <;> simp [hb] at h
  rcases hf : lowerFunctions block m.funcs ctx₀ with _ | ⟨_, c⟩ <;> simp [hf] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨region, b, hm, hr, ho, hp, ha⟩ := createModule_sound hc
  obtain rfl : b = block := by rw [← OperationPtr.getRegions!.getElem!_eq_getRegion!, show root₀.getRegions! _ = #[region] by grind [MatchesOp]] at hb; simpa [hr.first] using hb
  obtain ⟨hs, ops, hfs, hchain⟩ := lowerFunctions_sound ho hf
  exact ⟨region, b, ops, hs.ops root₀ (by simp) _ _ _ _ _ hm, hs.regions _ _ hr, by simpa using hchain,
    (hs.parents root₀ hm.1 (by simp)).trans hp, (hs.args b ho.blockInBounds).1.trans ha, resolvesList_mono hfs fun _ _ _ h => h _ Frame.refl⟩

end Soundness


/--
info: "builtin.module"() ({
  ^2():
    "llvm.func"() <{"function_type" = !llvm.func<i32 (i32, i32)>, "sym_name" = "demorgan_or"}> ({
      ^4(%arg4_0 : i32, %arg4_1 : i32):
        %9 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %5 = "llvm.xor"(%arg4_0, %9) : (i32, i32) -> i32
        %10 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %6 = "llvm.xor"(%arg4_1, %10) : (i32, i32) -> i32
        %7 = "llvm.and"(%5, %6) : (i32, i32) -> i32
        %11 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %8 = "llvm.xor"(%7, %11) : (i32, i32) -> i32
        "llvm.return"(%8) : (i32) -> ()
    }) : () -> ()
    "llvm.func"() <{"function_type" = !llvm.func<i32 (i32, i32)>, "sym_name" = "demorgan_and"}> ({
      ^15(%arg15_0 : i32, %arg15_1 : i32):
        %20 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %16 = "llvm.xor"(%arg15_0, %20) : (i32, i32) -> i32
        %21 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %17 = "llvm.xor"(%arg15_1, %21) : (i32, i32) -> i32
        %18 = "llvm.or"(%16, %17) : (i32, i32) -> i32
        %22 = "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
        %19 = "llvm.xor"(%18, %22) : (i32, i32) -> i32
        "llvm.return"(%19) : (i32) -> ()
    }) : () -> ()
}) : () -> ()
-/
#guard_msgs in
#eval show IO Unit from do
  match lowerModule resolvedDeMorganModule with
  | .error error => throw (IO.userError error)
  | .ok (ctx, root) => Printer.printModule ctx.raw root

#eval (lowerModule resolvedDeMorganModule).map (·.1.raw)

/-- Decode the signless integer types supported by the source fragment. -/
def reverseType (ty : Attribute) : Except String LLType :=
  match ty with
  | .integerType ⟨width, .signless⟩ => pure (.int width)
  | _ => throw "expected a signless integer type"

/-- Read a block's operations, bounding traversal by the context's allocation count. -/
def reverseOps (ctx : WfIRContext OpCode) (block : BlockPtr) :
    Except String (List OperationPtr) :=
  let rec collect : Nat → Option OperationPtr → Except String (List OperationPtr)
    | _, none => pure []
    | 0, some _ => throw "cyclic operation chain"
    | n + 1, some op => do
        if !op.InBounds ctx.raw then throw "invalid operation"
        return op :: (← collect n (op.getNextOp! ctx.raw))
  collect (ctx.raw.operations.size + 1) (block.getFirstOp! ctx.raw)

/-- Extract the sole block of an operation's sole region. -/
def reverseBody (ctx : WfIRContext OpCode) (op : OperationPtr) : Except String BlockPtr := do
  let #[region] := op.getRegions! ctx.raw | throw "expected one region"
  let some block := region.getFirstBlock! ctx.raw | throw "expected a body block"
  if (block.getNextBlock! ctx.raw).isSome then throw "expected one block"
  return block

/-- References use the complete definition table, so forward references are preserved. -/
def reverseValue (ctx : WfIRContext OpCode) (values : List (ValuePtr × ValueId))
    (v : ValuePtr) : Except String ResolvedValue := do
  if let some id := values.lookup v then return .ref id
  let .opResult result := v | throw "unknown block argument"
  if result.index != 0 || toDialect? Llvm (result.op.getOpType! ctx.raw) != some .mlir__constant then
    throw "unknown instruction result"
  let .integer attr := (result.op.getProperties! ctx.raw Llvm.mlir__constant).value
    | throw "expected an integer constant"
  return .intConst attr.value

/-- Recover a single-block function, giving parameters and the block canonical names.
Constants become literals; binary operations retain their block order. -/
def reverseFunction (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Except String ResolvedFunction := do
  if toDialect? Llvm (op.getOpType! ctx.raw) != some .func then throw "expected llvm.func"
  let props := op.getProperties! ctx.raw Llvm.func
  let #[output] := props.function_type.outputs | throw "expected one return type"
  let retType ← reverseType output
  let block ← reverseBody ctx op
  let ops ← reverseOps ctx block
  let some ret := ops.getLast? | throw "expected a return"
  if toDialect? Llvm (ret.getOpType! ctx.raw) != some .return then throw "expected llvm.return"
  let #[result] := ret.getOperands! ctx.raw | throw "expected one return operand"
  let defs := ops.dropLast.filter fun inst =>
    toDialect? Llvm (inst.getOpType! ctx.raw) != some .mlir__constant
  let values := (block.getArguments! ctx.raw).toList.zipIdx.map (fun (v, i) => (v, .param i)) ++
    defs.zipIdx.map (fun (inst, i) => (.opResult (inst.getResult 0), .inst i))
  let insts ← defs.mapM fun inst => do
    let opc ← match toDialect? Llvm (inst.getOpType! ctx.raw) with
      | some .and => pure BinOp.and
      | some .or => pure BinOp.or
      | some .xor => pure BinOp.xor
      | _ => throw "unsupported instruction"
    let #[ty] := inst.getResultTypes! ctx.raw | throw "expected one instruction result"
    let #[lhs, rhs] := inst.getOperands! ctx.raw | throw "expected two operands"
    return ResolvedAST.bin opc (← reverseType ty.val)
      (← reverseValue ctx values lhs) (← reverseValue ctx values rhs)
  let params ← (block.getArgumentTypes! ctx.raw).toList.zipIdx.mapM fun (ty, i) => do
    return Param.mk (← reverseType ty.val) s!"arg{i}"
  return ⟨⟨retType, String.fromUTF8! props.sym_name.value, params⟩,
    "entry", insts, ← reverseValue ctx values result⟩

/-- Decode the supported MLIR fragment. This is not a verifier of `LowersModule`:
round-trip guarantees apply to graphs satisfying that specification. -/
def reverseModule (ctx : WfIRContext OpCode) (root : OperationPtr) :
    Except String ResolvedModule := do
  if root.getOpType! ctx.raw != ofDialect OpCode Builtin.module then throw "expected builtin.module"
  let block ← reverseBody ctx root
  return ⟨← (← reverseOps ctx block).mapM (reverseFunction ctx)⟩

def equivalent_modulo_renaming_rearranging (ctx1 : WfIRContext OpCode) (root1 : OperationPtr)
    (ctx2 : WfIRContext OpCode) (root2 : OperationPtr) : Prop :=
  sorry

theorem lowerModule_complete : LowersModule ctx m root  → ∃ ctx2 root2, lowerModule m = .ok (ctx2, root2) ∧
  equivalent_modulo_renaming_rearranging ctx root ctx2 root2 := sorry

/-- MLIR → LLVM → MLIR recovers the specified rooted graph up to renaming. -/
theorem lower_reverseModule : LowersModule ctx m root →
    ∃ m' ctx' root', reverseModule ctx root = .ok m' ∧
      lowerModule m' = .ok (ctx', root') ∧
      equivalent_modulo_renaming_rearranging ctx root ctx' root' := sorry

/--
info: define i32 @demorgan_or (i32 %arg0, i32 %arg1) {
entry:
  %0 = xor i32 %arg0, -1
  %1 = xor i32 %arg1, -1
  %2 = and i32 %0, %1
  %3 = xor i32 %2, -1
  ret i32 %3
}

define i32 @demorgan_and (i32 %arg0, i32 %arg1) {
entry:
  %0 = xor i32 %arg0, -1
  %1 = xor i32 %arg1, -1
  %2 = or i32 %0, %1
  %3 = xor i32 %2, -1
  ret i32 %3
}
-/
#guard_msgs in
#eval show IO Unit from do
  let decoded := do
    let (ctx, root) ← lowerModule resolvedDeMorganModule
    reverseModule ctx root
  match decoded with
  | .error error => throw (IO.userError error)
  | .ok m => IO.println (String.intercalate "\n\n" (m.funcs.map toString))

end Veir.LLVMLowering
