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

/-- Allocate all definitions, then wire operands and insert each instruction after its constants. -/
def lowerInsts (block : BlockPtr) (insts : List ResolvedAST) : LowerM (Array ValuePtr) := do
  let ops ← insts.toArray.mapM (lowerInst block)
  let results := ops.map (fun op => ValuePtr.opResult (op.getResult 0))
  for (inst, op) in insts.zip ops.toList do
    let .bin _ ty lhs rhs := inst
    for operand in [lhs, rhs] do
      let v ← lowerValue block results ty operand
      let ctx ← get
      if ho : op.InBounds ctx.raw then
        if hv : v.InBounds ctx.raw then
          set (WfRewriter.pushOperand ctx op v ho hv)
        else throw "invalid operand"
      else throw "invalid instruction"
    let ctx ← get
    if ho : op.InBounds ctx.raw then
      if hb : (InsertPoint.atEnd block).InBounds ctx.raw then
        let some ctx' := WfRewriter.insertOp ctx op (.atEnd block) ho hb
          | throw "could not insert instruction"
        set ctx'
      else throw "invalid insertion block"
    else throw "invalid instruction"
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

/-- Prototype lowering of the resolved single-block integer fragment.
Supports forward references and rejects undefined references; LLVM validity is checked separately. -/
def lowerModule (m : ResolvedModule) :
    Except LoweringError (WfIRContext OpCode × OperationPtr) := do
  let some (ctx, root) := WfIRContext.create OpCode
    | throw "could not create module"
  let some block := (root.getRegion! ctx.raw 0).getFirstBlock! ctx.raw
    | throw "module has no body block"
  let ((), ctx') ← (m.funcs.forM (fun f => do
    let _ ← lowerFunction block f)).run ctx
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

variable {ctx ctx' : WfIRContext OpCode}
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpCode Dialect]
variable {opcode : Dialect} {properties : propertiesOf opcode}
theorem createOp_regions
    (h : WfRewriter.createOp ctx opcode types operands successors regions properties ip
      hoper hsucc hregions hins = some (ctx', op)) : op.getRegions! ctx'.raw = regions := by
  apply Array.ext
  · grind
  · intro i hi hi'; rw [OperationPtr.getRegions!.getElem_eq_getRegion!]; grind
theorem createOp_matches
    (h : WfRewriter.createOp ctx opcode types operands #[] regions properties ip
      hoper hsucc hregions hins = some (ctx', op)) :
    MatchesOp ctx' op opcode types operands regions properties := by
  have := createOp_regions h
  have := WfRewriter.createOp_new_inBounds op h
  simp only [MatchesOp, Prod.mk.injEq]
  simp_getset
  grind

attribute [local simp] StateT.run StateT.bind StateT.get StateT.set StateT.pure StateT.lift
  bind pure get getThe MonadState.get MonadStateOf.get set MonadStateOf.set
  Except.pure Except.bind throw throwThe MonadExceptOf.throw
theorem emit_createOp {opcode : Llvm} {properties : propertiesOf opcode} {insert : Bool}
    (h : (emit opcode types operands regions properties block insert).run ctx = .ok (op, ctx')) :
    ∃ ho hr hi, WfRewriter.createOp ctx opcode types operands #[] regions properties
      (if insert then some (InsertPoint.atEnd block) else none) ho (by simp) hr hi = some (ctx', op) := by
  simp [emit] at h
  by_cases ho : ∀ v ∈ operands, v.InBounds ctx.raw
  · rw [dite_eq_left ho] at h; by_cases hr : ∀ r ∈ regions, r.InBounds ctx.raw
    · rw [dite_eq_left hr] at h; by_cases hi : (if insert then some (InsertPoint.atEnd block) else none).maybe InsertPoint.InBounds ctx.raw
      · rw [dite_eq_left hi] at h; cases hc : WfRewriter.createOp ctx opcode types operands #[] regions properties (if insert then some (InsertPoint.atEnd block) else none) ho (by simp) hr hi with
        | none => simp [hc] at h
        | some pair => rcases pair with ⟨ctx2, op2⟩; simp [hc] at h; rcases h with ⟨rfl, rfl⟩; exact ⟨ho, hr, hi, hc⟩
      · rw [dite_eq_right hi] at h; simp at h
    · rw [dite_eq_right hr] at h; simp at h
  · rw [dite_eq_right ho] at h; simp at h

theorem emit_matches {opcode : Llvm} {properties : propertiesOf opcode} {insert : Bool}
    (h : (emit opcode types operands regions properties block insert).run ctx = .ok (op, ctx')) :
    MatchesOp ctx' op opcode types operands regions properties := by
  obtain ⟨_, _, _, hc⟩ := emit_createOp h
  exact createOp_matches hc
theorem lowerInst_matches
    (h : (lowerInst block (.bin opc ty lhs rhs)).run ctx = .ok (op, ctx')) :
    MatchesOp ctx' op (binOpcode opc) #[lowerType ty] #[] #[] default := by
  cases opc <;> exact emit_matches h

theorem MatchesOp.pushOperand (h : MatchesOp ctx op opcode types operands regions properties)
    (hne : op ≠ target) :
    MatchesOp (WfRewriter.pushOperand ctx target value ht hv) op opcode types operands regions properties := by
  simp only [MatchesOp, Prod.mk.injEq, WfRewriter.pushOperand] at *
  simp_getset
  grind

theorem MatchesOp.insertOp (h : MatchesOp ctx op opcode types operands regions properties)
    (hc : WfRewriter.insertOp ctx target ip ht hi = some ctx') :
    MatchesOp ctx' op opcode types operands regions properties := by
  have hr : op.getRegions! ctx'.raw = op.getRegions! ctx.raw := by apply Array.ext <;> grind
  simp only [MatchesOp, Prod.mk.injEq] at *
  simp_getset
  grind
theorem MatchesOp.createOp (h : MatchesOp ctx op opcode types operands regions properties)
    {newCode : Llvm} {newProps : propertiesOf newCode}
    (hc : WfRewriter.createOp ctx newCode ts vs bs rs newProps ip ho hb hr hi = some (ctx', newOp)) :
    MatchesOp ctx' op opcode types operands regions properties := by
  have hn : op ≠ newOp := by have := WfRewriter.createOp_new_not_inBounds newOp hc; grind [MatchesOp]
  have hr : op.getRegions! ctx'.raw = op.getRegions! ctx.raw := by apply Array.ext <;> grind
  simp only [MatchesOp, Prod.mk.injEq] at *
  simp_getset
  grind

theorem MatchesOp.createRegion (h : MatchesOp ctx op opcode types operands regions properties)
    (hc : WfRewriter.createRegion ctx = some (ctx', region)) :
    MatchesOp ctx' op opcode types operands regions properties := by
  simp only [WfRewriter.createRegion] at hc
  have hr : op.getRegions! ctx'.raw = op.getRegions! ctx.raw := by apply Array.ext <;> grind
  simp only [MatchesOp, Prod.mk.injEq] at *
  try simp_getset
  grind
theorem MatchesOp.createBlock (h : MatchesOp ctx op opcode types operands regions properties)
    (hc : WfRewriter.createBlock ctx ts ip hi = some (ctx', block)) :
    MatchesOp ctx' op opcode types operands regions properties := by
  simp only [MatchesOp, Prod.mk.injEq] at h
  cases ip <;> unfold WfRewriter.createBlock at hc <;> unfold Rewriter.createBlock at hc
  all_goals simp only [Option.bind_eq_bind, Option.bind, pure] at hc
  all_goals have hr : op.getRegions! ctx'.raw = op.getRegions! ctx.raw := by apply Array.ext <;> grind (gen := 20)
  all_goals simp only [MatchesOp, Prod.mk.injEq] at *
  all_goals refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals grind (gen := 20) [OperationPtr.getProperties!, OperationPtr.getAttributes!]
theorem MatchesOp.pushOperand_self (h : MatchesOp ctx op opcode types operands regions properties) :
    MatchesOp (WfRewriter.pushOperand ctx op value ht hv) op opcode types (operands.push value) regions properties := by
  simp only [MatchesOp, Prod.mk.injEq, WfRewriter.pushOperand] at *
  simp_getset
  grind


def definitionMap (ctx : WfIRContext OpCode) (block : BlockPtr) (results : Array ValuePtr) : ValueMap
  | .param i => (block.getArguments! ctx.raw)[i]?
  | .inst i => results[i]?
theorem lowerValue_param
    (h : (lowerValue block results ty (.ref (.param i))).run ctx = .ok (v, ctx')) :
    ctx' = ctx ∧ i < block.getNumArguments! ctx.raw ∧
      (block.getArguments! ctx.raw)[i]? = some v := by
  simp [lowerValue] at h
  split at h <;> simp_all [BlockPtr.getArguments!, BlockPtr.getArgument]
theorem lowerValue_inst
    (h : (lowerValue block results ty (.ref (.inst i))).run ctx = .ok (v, ctx')) :
    ctx' = ctx ∧ results[i]? = some v := by
  cases hr : results[i]? <;> simp_all [lowerValue]
theorem lowerValue_const_emit
    (h : (lowerValue block results (.int w) (.intConst n)).run ctx = .ok (v, ctx')) :
    ∃ c, v = .opResult (c.getResult 0) ∧
      (emit .mlir__constant #[lowerType (.int w)] #[] #[]
        (LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt n (.signless w)))) block).run ctx = .ok (c, ctx') := by
  simp only [lowerValue, StateT.run, bind, StateT.bind] at h
  cases hc : (emit .mlir__constant #[lowerType (.int w)] #[] #[]
    (LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt n (.signless w)))) block).run ctx with
  | error e => simp_all [StateT.run]
  | ok pair =>
    rcases pair with ⟨c, ctx2⟩; simp [StateT.run] at hc; simp [hc] at h
    rcases h with ⟨rfl, rfl⟩; exact ⟨c, rfl, rfl⟩

theorem lowerValue_const
    (h : (lowerValue block results (.int w) (.intConst n)).run ctx = .ok (v, ctx')) :
    ∃ c, v = .opResult (c.getResult 0) ∧ MatchesOp ctx' c Llvm.mlir__constant
      #[lowerType (.int w)] #[] #[] (LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt n (.signless w)))) := by
  obtain ⟨c, hv, hc⟩ := lowerValue_const_emit h
  exact ⟨c, hv, emit_matches hc⟩

theorem lowerValue_valid
    (h : (lowerValue block results ty value).run ctx = .ok (v, ctx')) :
    ValidResolvedValue (block.getNumArguments! ctx.raw) results.size value := by
  cases value with
  | ref id =>
    cases id with
    | param i => exact (lowerValue_param h).2.1
    | inst i => have := (lowerValue_inst h).2; grind [ValidResolvedValue]
  | intConst n => trivial
theorem lowerValue_tile
    (h : (lowerValue block results ty value).run ctx = .ok (v, ctx')) :
    ∃ cs, OperandTile ctx' (definitionMap ctx block results) ty value v cs := by
  cases value with
  | ref id =>
    refine ⟨[], ?_⟩; cases id with
    | param i => simpa [OperandTile, definitionMap] using (lowerValue_param h).2.2
    | inst i => simpa [OperandTile, definitionMap] using (lowerValue_inst h).2
  | intConst n =>
    cases ty; obtain ⟨c, hv, hc⟩ := lowerValue_const h
    exact ⟨[c], c, rfl, hv, hc⟩
theorem opChain_pushOperand {block : BlockPtr} (h : block.OpChain ctx.raw ops) :
    block.OpChain (WfRewriter.pushOperand ctx target value ht hv).raw ops :=
  BlockPtr.opChain_rewriter_pushOperand ctx.raw (by grind) target ht h

theorem blockChain_pushOperand {region : RegionPtr} (h : region.BlockChain ctx.raw blocks) :
    region.BlockChain (WfRewriter.pushOperand ctx target value ht hv).raw blocks := by
  apply RegionPtr.blockChain_unchanged h <;> grind [WfRewriter.pushOperand]
theorem opChain_insertOp {block : BlockPtr} {op : OperationPtr}
    {ho : op.InBounds ctx.raw} {hi : (InsertPoint.atEnd block).InBounds ctx.raw}
    (h : block.OpChain ctx.raw ops)
    (hc : WfRewriter.insertOp ctx op (.atEnd block) ho hi = some ctx') :
    block.OpChain ctx'.raw (ops.push op) := by
  have hr : Rewriter.insertOp ctx.raw op (.atEnd block) ho hi (by grind) = some ctx'.raw := by
    unfold WfRewriter.insertOp at hc; split at hc <;> grind
  have hb : block.InBounds ctx'.raw := by grind
  have he := BlockPtr.operationList_rewriter_insertOp (block := block) (ctx'Wf := ctx'.wellFormed) (blockIn := hb) hr ctx.wellFormed
  have hold := (BlockPtr.operationList_iff_BlockPtr_OpChain (hctx := ctx.wellFormed) (hblock := h.blockInBounds)).mp h
  apply (BlockPtr.operationList_iff_BlockPtr_OpChain (hctx := ctx'.wellFormed) (hblock := hb)).mpr
  simpa [InsertPoint.block!_atEnd_eq, InsertPoint.idxIn_atEnd_eq, hold] using he

theorem opChain_createOp {block : BlockPtr} {insert : Bool}
    {hi : (if insert then some (InsertPoint.atEnd block) else none).maybe InsertPoint.InBounds ctx.raw}
    (h : block.OpChain ctx.raw ops)
    (hc : WfRewriter.createOp ctx opcode types operands #[] regions properties
      (if insert then some (.atEnd block) else none) ho hs hr hi = some (ctx', op)) :
    block.OpChain ctx'.raw (if insert then ops.push op else ops) := by
  have he : Rewriter.createOp ctx.raw opcode types operands #[] regions properties
      (if insert then some (.atEnd block) else none) ho hs hr hi (by grind) = some (ctx'.raw, op) := by
    unfold WfRewriter.createOp at hc; split at hc <;> grind
  have hb : block.InBounds ctx'.raw := by grind
  have hl := BlockPtr.operationList_rewriter_createOp (block := block) (newCtxWf := ctx'.wellFormed)
    (blockIn := hb) he ctx.wellFormed
  have hold := (BlockPtr.operationList_iff_BlockPtr_OpChain (hctx := ctx.wellFormed) (hblock := h.blockInBounds)).mp h
  apply (BlockPtr.operationList_iff_BlockPtr_OpChain (hctx := ctx'.wellFormed) (hblock := hb)).mpr
  cases insert <;> simpa [InsertPoint.block!_atEnd_eq, InsertPoint.idxIn_atEnd_eq, hold] using hl

theorem opChain_emit {opcode : Llvm} {properties : propertiesOf opcode} {insert : Bool}
    {block : BlockPtr} (hb : block.OpChain ctx.raw ops)
    (h : (emit opcode types operands regions properties block insert).run ctx = .ok (op, ctx')) :
    block.OpChain ctx'.raw (if insert then ops.push op else ops) := by
  obtain ⟨_, _, _, hc⟩ := emit_createOp h
  exact opChain_createOp hb hc

theorem lowerValue_chain {block : BlockPtr} (hb : block.OpChain ctx.raw ops)
    (h : (lowerValue block results ty value).run ctx = .ok (v, ctx')) :
    ∃ cs, OperandTile ctx' (definitionMap ctx block results) ty value v cs ∧
      block.OpChain ctx'.raw (ops ++ cs.toArray) := by
  cases value with
  | ref id =>
    obtain ⟨cs, ht⟩ := lowerValue_tile h
    have hc : ctx' = ctx := by cases id <;> first | exact (lowerValue_param h).1 | exact (lowerValue_inst h).1
    have hs : cs = [] := by cases ty; exact ht.2
    exact ⟨cs, ht, by simpa [hc, hs] using hb⟩
  | intConst n =>
    cases ty; obtain ⟨c, hv, he⟩ := lowerValue_const_emit h
    exact ⟨[c], ⟨c, rfl, hv, emit_matches he⟩, by simpa using opChain_emit hb he⟩

/-- Preserve the observable fields used by LLVM tiles. -/
def PreservesMatches (ctx ctx' : WfIRContext OpCode) : Prop :=
  ∀ op (code : Llvm) ts vs rs props,
    MatchesOp ctx op code ts vs rs props → MatchesOp ctx' op code ts vs rs props
theorem emit_preservesMatches {opcode : Llvm} {properties : propertiesOf opcode} {insert : Bool}
    (h : (emit opcode types operands regions properties block insert).run ctx = .ok (op, ctx')) :
    PreservesMatches ctx ctx' := by
  obtain ⟨_, _, _, hc⟩ := emit_createOp h
  exact fun _ _ _ _ _ _ hm => hm.createOp hc

theorem OperandTile.mono (hm : PreservesMatches ctx ctx')
    (h : OperandTile ctx values ty value v cs) : OperandTile ctx' values ty value v cs := by
  cases value with
  | ref id => exact h
  | intConst n =>
    cases ty; obtain ⟨c, hcs, hv, hc⟩ := h
    exact ⟨c, hcs, hv, hm _ _ _ _ _ _ hc⟩
theorem LowersInstTile.mono {id : ValueId} (hm : PreservesMatches ctx ctx')
    (h : LowersInstTile ctx values id inst tile) : LowersInstTile ctx' values id inst tile := by
  cases inst
  obtain ⟨vl, vr, cl, cr, op, ht, hl, hr, hv, ho⟩ := h
  exact ⟨vl, vr, cl, cr, op, ht, hl.mono hm, hr.mono hm, hv, hm _ _ _ _ _ _ ho⟩
theorem resolvesList_mono (hm : ∀ a b, R a b → S a b) (h : ResolvesList R as bs) :
    ResolvesList S as bs := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons (hm _ _ h) ih

theorem LowersFunctionTiles.mono (hm : PreservesMatches ctx ctx')
    (hr : ∀ (r : RegionPtr) bs, r.BlockChain ctx.raw bs → r.BlockChain ctx'.raw bs)
    (hb : ∀ (b : BlockPtr) ops, b.OpChain ctx.raw ops → b.OpChain ctx'.raw ops)
    (ha : ∀ b : BlockPtr, b.InBounds ctx.raw → b.getArgumentTypes! ctx'.raw = b.getArgumentTypes! ctx.raw ∧
      b.getArguments! ctx'.raw = b.getArguments! ctx.raw)
    (h : LowersFunctionTiles ctx f op) : LowersFunctionTiles ctx' f op := by
  rcases h with ⟨hf, r, b, tiles, cs, ret, v, values, hop, hreg, hty, hparam, hi, hv, hret, hchain⟩
  obtain ⟨htypes, hargs⟩ := ha b hchain.blockInBounds
  exact ⟨hf, r, b, tiles, cs, ret, v, values, hm _ _ _ _ _ _ hop, hr _ _ hreg,
    htypes.trans hty, fun i => (hparam i).trans (congrArg (·[i]?) hargs).symm,
    resolvesList_mono (fun _ _ h => LowersInstTile.mono hm h) hi, hv.mono hm, hm _ _ _ _ _ _ hret, hb _ _ hchain⟩


set_option maxRecDepth 4000
set_option maxHeartbeats 800000

theorem blockChain_singleton {ctx : WfIRContext OpCode} {r : RegionPtr} {b : BlockPtr} (hr : r.InBounds ctx.raw)
    (hf : r.getFirstBlock! ctx.raw = some b) (hl : r.getLastBlock! ctx.raw = some b) : r.BlockChain ctx.raw #[b] := by
  obtain ⟨bs, hb⟩ := ctx.wellFormed.blockChain r hr
  have hinj := RegionPtr.BlockChain_array_injective hb 0 (bs.size - 1)
  have hs : bs = #[b] := by apply Array.ext <;> grind
  simpa [hs] using hb

/-- Preserve old operation fields and other blocks while wiring the listed operations. -/
structure Frame (ctx ctx' : WfIRContext OpCode) (changed : List OperationPtr) (block : BlockPtr) : Prop where
  bounds : ∀ p : GenericPtr, p.InBounds ctx.raw → p.InBounds ctx'.raw
  ops : ∀ op, op ∉ changed → ∀ {D : Type} [HasOpInfo D] [HasDialect OpCode D]
    (code : D) ts vs rs props, MatchesOp ctx op code ts vs rs props → MatchesOp ctx' op code ts vs rs props
  parents : ∀ op, op.InBounds ctx.raw → op ∉ changed → op.getParent! ctx'.raw = op.getParent! ctx.raw
  blocks : ∀ b : BlockPtr, b.InBounds ctx.raw → b.getParent! ctx'.raw = b.getParent! ctx.raw
  args : ∀ b : BlockPtr, b.InBounds ctx.raw → b.getArgumentTypes! ctx'.raw = b.getArgumentTypes! ctx.raw ∧ b.getArguments! ctx'.raw = b.getArguments! ctx.raw
  chains : ∀ b : BlockPtr, b ≠ block → ∀ os, b.OpChain ctx.raw os → b.OpChain ctx'.raw os
  regions : ∀ (r : RegionPtr) (b : BlockPtr), r.BlockChain ctx.raw #[b] → r.BlockChain ctx'.raw #[b]

variable {ctx ctx' ctx'' : WfIRContext OpCode} {changed changed' : List OperationPtr} {block : BlockPtr}

theorem Frame.refl : Frame ctx ctx [] block :=
  ⟨fun _ h => h, fun _ _ _ _ _ _ _ _ _ _ h => h, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ h => h, fun _ _ h => h⟩

theorem Frame.trans (h : Frame ctx ctx' changed block) (h' : Frame ctx' ctx'' changed' block) :
    Frame ctx ctx'' (changed ++ changed') block := by
  refine ⟨fun p hp => h'.bounds p (h.bounds p hp), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro op hn D _ _ code ts vs rs props hm; exact h'.ops op (by simp_all) _ _ _ _ _ (h.ops op (by simp_all) _ _ _ _ _ hm)
  · intro op ho hn; exact (h'.parents op (h.bounds (.operation op) ho) (by simp_all)).trans (h.parents op ho (by simp_all))
  · intro b hb; exact (h'.blocks b (h.bounds (.block b) hb)).trans (h.blocks b hb)
  · intro b hb; obtain ⟨ht, ha⟩ := h.args b hb; obtain ⟨ht', ha'⟩ := h'.args b (h.bounds (.block b) hb); exact ⟨ht'.trans ht, ha'.trans ha⟩
  · exact fun b hn os ho => h'.chains b hn os (h.chains b hn os ho)
  · exact fun r bs hr => h'.regions r bs (h.regions r bs hr)

theorem Frame.weaken (h : Frame ctx ctx' changed block) (hs : changed ⊆ changed') : Frame ctx ctx' changed' block :=
  { h with ops := fun op hn => h.ops op (fun hp => hn (hs hp)), parents := fun op ho hn => h.parents op ho (fun hp => hn (hs hp)) }

theorem Frame.forget (h : Frame ctx ctx' changed block) (hf : ∀ op ∈ changed, ¬op.InBounds ctx.raw) :
    Frame ctx ctx' [] block := by
  refine { h with ops := ?_, parents := ?_ }
  · intro op _ D _ _ code ts vs rs props hm; exact h.ops op (fun hp => hf op hp hm.1) _ _ _ _ _ hm
  · exact fun op ho _ => h.parents op ho (fun hp => hf op hp ho)

theorem Frame.definitionMap_eq (h : Frame ctx ctx' changed block) (hb : b.InBounds ctx.raw) :
    definitionMap ctx' b results = definitionMap ctx b results := by
  funext id; cases id <;> simp only [definitionMap, (h.args b hb).2]

theorem Frame.createOp {code : Llvm} {props : propertiesOf code} {insert : Bool}
    {hi : (if insert then some (InsertPoint.atEnd block) else none).maybe InsertPoint.InBounds ctx.raw}
    (hc : WfRewriter.createOp ctx code ts vs #[] rs props
      (if insert then some (InsertPoint.atEnd block) else none) ho hs hr hi = some (ctx', op)) : Frame ctx ctx' [] block := by
  refine ⟨fun p hp => by grind, fun _ _ _ _ _ _ _ _ _ _ hm => hm.createOp hc, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp _; have : p ≠ op := by have := WfRewriter.createOp_new_not_inBounds op hc; grind
    grind
  · intro b hb; grind
  · intro b hb; constructor
    · apply Array.ext (by grind); intro i hi hi'; have := ValuePtr.getType!_WfRewriter_createOp (value := .blockArgument (b.getArgument i)) hc; grind
    · simp only [BlockPtr.getArguments!]; congr 1; grind
  · intro b hn os hb; apply BlockPtr.OpChain_unchanged hb <;> grind
  · intro r b hb; apply blockChain_singleton <;> grind

theorem Frame.emit {code : Llvm} {props : propertiesOf code} {insert : Bool}
    (h : (emit code ts vs rs props block insert).run ctx = .ok (op, ctx')) : Frame ctx ctx' [] block := by
  obtain ⟨_, _, _, hc⟩ := emit_createOp h; exact Frame.createOp hc

theorem Frame.pushOperand (ho : op.InBounds ctx.raw) (hv : v.InBounds ctx.raw) :
    Frame ctx (WfRewriter.pushOperand ctx op v ho hv) [op] block := by
  refine ⟨fun p hp => by grind [WfRewriter.pushOperand], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hn D _ _ code ts vs rs props hm; exact hm.pushOperand (by simpa using hn)
  · intro p hp hn; grind [WfRewriter.pushOperand]
  · intro b hb; grind [WfRewriter.pushOperand]
  · intro b hb; constructor <;> (first | (apply Array.ext <;> grind [WfRewriter.pushOperand]) | (simp only [BlockPtr.getArguments!]; congr 1; grind [WfRewriter.pushOperand]))
  · exact fun _ _ _ h => opChain_pushOperand h
  · exact fun _ _ h => blockChain_pushOperand h

theorem Frame.insertOp {ho : op.InBounds ctx.raw} {hi : (InsertPoint.atEnd block).InBounds ctx.raw}
    (hp : op.getParent! ctx.raw = none)
    (hc : WfRewriter.insertOp ctx op (.atEnd block) ho hi = some ctx') : Frame ctx ctx' [op] block := by
  refine ⟨fun p hp => by grind, fun _ _ _ _ _ _ _ _ _ _ hm => hm.insertOp hc, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp hn; grind
  · intro b hb; grind
  · intro b hb; constructor <;> (first | (apply Array.ext <;> grind [WfRewriter.insertOp]) | (simp only [BlockPtr.getArguments!]; congr 1; grind))
  · intro b hn os hb; apply BlockPtr.OpChain_unchanged hb <;> grind
  · intro r b hb; apply blockChain_singleton <;> grind

attribute [local simp] StateT.run StateT.bind StateT.get StateT.set StateT.pure StateT.lift
  bind pure get getThe MonadState.get MonadStateOf.get set MonadStateOf.set
  Except.pure Except.bind throw throwThe MonadExceptOf.throw

theorem bind_ok {x : LowerM α} {f : α → LowerM β}
    (h : (x >>= f).run ctx = .ok (b, ctx')) :
    ∃ a ctx₁, x.run ctx = .ok (a, ctx₁) ∧ (f a).run ctx₁ = .ok (b, ctx') := by
  cases hx : x ctx with
  | error e => simp_all [StateT.run, StateT.bind]
  | ok pair => exact ⟨pair.1, pair.2, hx, by simpa [StateT.run, StateT.bind, hx] using h⟩

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

def wireInst (block : BlockPtr) (results : Array ValuePtr) : ResolvedAST × OperationPtr → LowerM Unit
  | (.bin _ ty lhs rhs, op) => do
      pushValue op (← lowerValue block results ty lhs)
      pushValue op (← lowerValue block results ty rhs)
      attachInst block op

theorem forIn_unit (xs : List α) (f : α → LowerM Unit) :
    forIn xs () (fun a _ => do f a; pure (.yield ())) = xs.forM f := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.forIn_cons, List.forM_eq_forM, List.forM_cons, bind_assoc, pure_bind]; cases u : () <;> simpa only [List.forM_eq_forM] using congrArg (fun k => f a >>= fun _ => k) ih

theorem lowerInsts_eq (block : BlockPtr) (insts : List ResolvedAST) :
    lowerInsts block insts = (do
      let ops ← insts.mapM (lowerInst block)
      let results := ops.toArray.map (fun op => ValuePtr.opResult (op.getResult 0))
      (insts.zip ops).forM (wireInst block results)
      pure results) := by
  simp only [lowerInsts, List.mapM_toArray, bind_map_left]
  congr 1; funext ops; rw [← forIn_unit]; congr 2; funext pair u; rcases pair with ⟨⟨opc, ty, lhs, rhs⟩, op⟩
  simp only [wireInst, pushValue, attachInst, List.forIn_cons, List.forIn_nil, bind_assoc]; apply StateT.ext; intro c
  cases hl : lowerValue block ((ops.map (fun op => ValuePtr.opResult (op.getResult 0))).toArray) ty lhs c
  · simp [hl]
  · rename_i pair; rcases pair with ⟨v, c₁⟩; by_cases ho : op.InBounds c₁.raw <;> simp [hl, ho]; by_cases hv : v.InBounds c₁.raw <;> simp [hv]
    cases hr : lowerValue block ((ops.map (fun op => ValuePtr.opResult (op.getResult 0))).toArray) ty rhs (WfRewriter.pushOperand c₁ op v ho hv)
    · simp
    · rename_i pair; rcases pair with ⟨v₂, c₂⟩; by_cases ho₂ : op.InBounds c₂.raw <;> simp [ho₂]; by_cases hv₂ : v₂.InBounds c₂.raw <;> simp [hv₂]
      by_cases ho₃ : op.InBounds (WfRewriter.pushOperand c₂ op v₂ ho₂ hv₂).raw <;> simp [ho₃]; by_cases hb : block.InBounds (WfRewriter.pushOperand c₂ op v₂ ho₂ hv₂).raw <;> simp [hb]; cases hc : WfRewriter.insertOp (WfRewriter.pushOperand c₂ op v₂ ho₂ hv₂) op (.atEnd block) ho₃ hb <;> simp


theorem Frame.lowerValue (h : (lowerValue block results ty value).run ctx = .ok (v, ctx')) :
    Frame ctx ctx' [] block := by
  cases value with
  | ref id => have he : ctx' = ctx := by cases id <;> first | exact (lowerValue_param h).1 | exact (lowerValue_inst h).1
              subst ctx'; exact Frame.refl
  | intConst n => cases ty; obtain ⟨c, _, hc⟩ := lowerValue_const_emit h; exact Frame.emit hc

theorem lowerValue_fresh
    (h : (lowerValue block results ty value).run ctx = .ok (v, ctx'))
    (ht : OperandTile ctx' values ty value v cs) : ∀ c ∈ cs, ¬c.InBounds ctx.raw := by
  cases value with
  | ref id => intro c hc; simp_all [OperandTile]
  | intConst n =>
    cases ty; obtain ⟨c, hv, he⟩ := lowerValue_const_emit h; obtain ⟨c', rfl, hv', _⟩ := ht
    have : c' = c := by simpa [OperationPtr.getResult] using hv'.symm.trans hv
    subst c'; obtain ⟨_, _, _, hc⟩ := emit_createOp he; simpa using WfRewriter.createOp_new_not_inBounds c hc

theorem OperandTile.frame (hf : Frame ctx ctx' changed block)
    (h : OperandTile ctx values ty value v cs) (hn : ∀ c ∈ cs, c ∉ changed) :
    OperandTile ctx' values ty value v cs := by
  cases value with
  | ref id => exact h
  | intConst n => cases ty; obtain ⟨c, rfl, hv, hc⟩ := h; exact ⟨c, rfl, hv, hf.ops c (hn c (by simp)) _ _ _ _ _ hc⟩

theorem LowersInstTile.frame {id : ValueId} (hf : Frame ctx ctx' changed block)
    (h : LowersInstTile ctx values id inst tile) (hn : ∀ c ∈ tile, c ∉ changed) :
    LowersInstTile ctx' values id inst tile := by
  cases inst; obtain ⟨vl, vr, cl, cr, op, rfl, hl, hr, hv, ho⟩ := h
  exact ⟨vl, vr, cl, cr, op, rfl, hl.frame hf (by intro c hc; exact hn c (by simp_all)),
    hr.frame hf (by intro c hc; exact hn c (by simp_all)), hv, hf.ops op (hn op (by simp)) _ _ _ _ _ ho⟩

theorem pushValue_ok (h : (pushValue op v).run ctx = .ok ((), ctx')) :
    ∃ ho hv, ctx' = WfRewriter.pushOperand ctx op v ho hv := by
  simp [pushValue] at h; split at h <;> simp_all; split at h <;> simp_all

theorem attachInst_ok (h : (attachInst block op).run ctx = .ok ((), ctx')) :
    ∃ ho hi, WfRewriter.insertOp ctx op (.atEnd block) ho hi = some ctx' := by
  simp [attachInst] at h; split at h <;> simp_all; split at h <;> simp_all
  cases hc : WfRewriter.insertOp ctx op (.atEnd block) ‹_› ‹_› <;> simp_all

def Allocated (ctx : WfIRContext OpCode) : ResolvedAST → OperationPtr → Prop
  | .bin opc ty _ _, op => MatchesOp ctx op (binOpcode opc) #[lowerType ty] #[] #[] default ∧ op.getParent! ctx.raw = none

theorem Allocated.inBounds (h : Allocated ctx inst op) : op.InBounds ctx.raw := by cases inst; exact h.1.1

theorem Allocated.frame (hf : Frame ctx ctx' changed block) (hn : op ∉ changed)
    (h : Allocated ctx inst op) : Allocated ctx' inst op := by
  cases inst; exact ⟨hf.ops op hn _ _ _ _ _ h.1, (hf.parents op h.1.1 hn).trans h.2⟩

theorem lowerInst_spec (h : (lowerInst block inst).run ctx = .ok (op, ctx')) :
    Frame ctx ctx' [] block ∧ Allocated ctx' inst op ∧ ¬op.InBounds ctx.raw ∧
      ∀ os, block.OpChain ctx.raw os → block.OpChain ctx'.raw os := by
  cases inst with | bin opc ty lhs rhs =>
    have hm := lowerInst_matches h
    cases opc <;> obtain ⟨_, _, _, hc⟩ := emit_createOp h
    all_goals exact ⟨Frame.createOp hc, ⟨hm, by grind⟩, WfRewriter.createOp_new_not_inBounds op hc,
      fun os hb => by simpa using (opChain_createOp hb hc)⟩

/-- The allocation pass produces fresh, distinct, detached instruction definitions. -/
structure Allocation (block : BlockPtr) (insts : List ResolvedAST) (ops : List OperationPtr)
    (ctx ctx' : WfIRContext OpCode) : Prop where
  frame : Frame ctx ctx' [] block
  allocated : ResolvesList (Allocated ctx') insts ops
  nodup : ops.Pairwise (· ≠ ·)
  fresh : ∀ op ∈ ops, ¬op.InBounds ctx.raw
  chain : ∀ os, block.OpChain ctx.raw os → block.OpChain ctx'.raw os

theorem Allocation.cons (h : Frame ctx ctx' [] block) (ha : Allocated ctx' inst op)
    (hn : ¬op.InBounds ctx.raw) (hb : ∀ os, block.OpChain ctx.raw os → block.OpChain ctx'.raw os)
    (ht : Allocation block insts ops ctx' ctx'') : Allocation block (inst :: insts) (op :: ops) ctx ctx'' := by
  refine ⟨by simpa using h.trans ht.frame, .cons (ha.frame ht.frame (by simp)) ht.allocated, ?_, ?_, fun os hc => ht.chain os (hb os hc)⟩
  · exact List.Pairwise.cons (fun p hp he => ht.fresh p hp (he ▸ ha.inBounds)) ht.nodup
  · intro p hp; rcases List.mem_cons.mp hp with rfl | hp; exact hn; exact fun hi => ht.fresh p hp (h.bounds (.operation p) hi)

theorem mapM_cons_ok {f : α → LowerM β}
    (h : ((a :: as).mapM f).run ctx = .ok (bs, ctx')) :
    ∃ b bs' ctx₁, bs = b :: bs' ∧ (f a).run ctx = .ok (b, ctx₁) ∧ (as.mapM f).run ctx₁ = .ok (bs', ctx') := by
  obtain ⟨b, ctx₁, hb, ht⟩ := bind_ok (by simpa only [List.mapM_cons, map_eq_pure_bind] using h)
  obtain ⟨bs', ctx₂, hs, he⟩ := bind_ok ht
  simp at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨b, bs', ctx₁, rfl, hb, hs⟩

theorem allocate_sound (h : (insts.mapM (lowerInst block)).run ctx = .ok (ops, ctx')) :
    Allocation block insts ops ctx ctx' := by
  induction insts generalizing ctx ops with
  | nil => simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨Frame.refl, .nil, .nil, by simp, fun _ h => h⟩
  | cons inst insts ih =>
    obtain ⟨op, ops, ctx₁, rfl, ho, hs⟩ := mapM_cons_ok h
    obtain ⟨hf, ha, hn, hb⟩ := lowerInst_spec ho
    exact Allocation.cons hf ha hn hb (ih hs)

theorem fresh_avoids {cs : List OperationPtr} {op : OperationPtr} (hn : ∀ c ∈ cs, ¬c.InBounds ctx.raw) (ho : op.InBounds ctx.raw) :
    ∀ c ∈ cs, c ∉ [op] := by
  intro c hc he; have he := List.mem_singleton.mp he; subst c; exact hn op hc ho

theorem lowerOperand_sound {code : Llvm} {props : propertiesOf code}
    (hm : MatchesOp ctx op code ts vs rs props) (hb : block.OpChain ctx.raw os)
    (h : (do pushValue op (← lowerValue block results ty value)).run ctx = .ok ((), ctx')) :
    ∃ v cs, OperandTile ctx' (definitionMap ctx block results) ty value v cs ∧
      MatchesOp ctx' op code ts (vs.push v) rs props ∧
      op.getParent! ctx'.raw = op.getParent! ctx.raw ∧
      block.OpChain ctx'.raw (os ++ cs.toArray) ∧ Frame ctx ctx' [op] block ∧
      (∀ c ∈ cs, ¬c.InBounds ctx.raw) ∧ ValidResolvedValue (block.getNumArguments! ctx.raw) results.size value := by
  obtain ⟨v, ctx₁, hl, hp⟩ := bind_ok h
  obtain ⟨cs, ht, hc⟩ := lowerValue_chain hb hl
  have hf := Frame.lowerValue hl; have hn := lowerValue_fresh hl ht
  obtain ⟨ho, hv, rfl⟩ := pushValue_ok hp
  have hd : ∀ c ∈ cs, c ∉ [op] := fresh_avoids hn hm.1
  exact ⟨v, cs, ht.frame (Frame.pushOperand (block := block) ho hv) hd,
    (hf.ops op (by simp) _ _ _ _ _ hm).pushOperand_self, by simpa [WfRewriter.pushOperand] using hf.parents op hm.1 (by simp),
    opChain_pushOperand hc, hf.trans (Frame.pushOperand (block := block) ho hv), hn, lowerValue_valid hl⟩

theorem wireInst_split
    (h : (wireInst block results (.bin opc ty lhs rhs, op)).run ctx = .ok ((), ctx')) :
    ∃ ctx₁ ctx₂,
      (do pushValue op (← lowerValue block results ty lhs)).run ctx = .ok ((), ctx₁) ∧
      (do pushValue op (← lowerValue block results ty rhs)).run ctx₁ = .ok ((), ctx₂) ∧
      (attachInst block op).run ctx₂ = .ok ((), ctx') := by
  have h' : ((do pushValue op (← lowerValue block results ty lhs)) >>= fun _ =>
    (do pushValue op (← lowerValue block results ty rhs)) >>= fun _ => attachInst block op).run ctx = .ok ((), ctx') := by simpa only [wireInst, bind_assoc] using h
  obtain ⟨⟨⟩, ctx₁, hl, ht⟩ := bind_ok h'; obtain ⟨⟨⟩, ctx₂, hr, ha⟩ := bind_ok ht
  exact ⟨ctx₁, ctx₂, hl, hr, ha⟩

theorem wireInst_sound {id : ValueId}
    (ha : Allocated ctx inst op) (hb : block.OpChain ctx.raw os)
    (hid : definitionMap ctx block results id = some (.opResult (op.getResult 0)))
    (h : (wireInst block results (inst, op)).run ctx = .ok ((), ctx')) :
    ∃ tile, LowersInstTile ctx' (definitionMap ctx block results) id inst tile ∧
      block.OpChain ctx'.raw (os ++ tile.toArray) ∧ Frame ctx ctx' [op] block ∧
      (∀ c ∈ tile, c = op ∨ ¬c.InBounds ctx.raw) ∧
      ValidResolvedInst (block.getNumArguments! ctx.raw) results.size inst := by
  rcases inst with ⟨opc, ty, lhs, rhs⟩; obtain ⟨ctx₁, ctx₂, hl, hr, hi⟩ := wireInst_split h
  obtain ⟨vl, cl, htl, hml, hpl, hcl, hfl, hnl, hvl⟩ := lowerOperand_sound ha.1 hb hl; obtain ⟨vr, cr, htr, hmr, hpr, hcr, hfr, hnr, hvr⟩ := lowerOperand_sound hml hcl hr
  obtain ⟨ho, hip, hi⟩ := attachInst_ok hi; have hfi := Frame.insertOp (hpr.trans (hpl.trans ha.2)) hi; have hni := fresh_avoids hnl ha.1.1; have hnr' := fresh_avoids hnr hml.1
  refine ⟨cl ++ cr ++ [op], ⟨vl, vr, cl, cr, op, rfl, (htl.frame hfr hni).frame hfi hni, ?_, hid, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simpa [hfl.definitionMap_eq hb.blockInBounds] using htr.frame hfi hnr'
  · simpa using hmr.insertOp hi
  · simpa [Array.append_assoc] using opChain_insertOp hcr hi
  · exact ((hfl.trans hfr).trans hfi).weaken (by simp)
  · intro c hc; simp only [List.mem_append, List.mem_singleton] at hc; rcases hc with (hc | hc) | rfl; exact .inr (hnl c hc); exact .inr (fun hin => hnr c hc (hfl.bounds (.operation c) hin)); exact .inl rfl
  · simpa [ValidResolvedInst, ← BlockPtr.getArgumentTypes!.size_eq_getNumArguments!, (hfl.args block hb.blockInBounds).1] using And.intro hvl hvr

section Indexed
variable {α β : Type} {R : α → β → Prop} {as : List α} {bs : List β} {a : α} {b : β} {i : Nat}

theorem _root_.Veir.NameResolutionSketch.ResolvesList.length (h : ResolvesList R as bs) : as.length = bs.length := by
  induction h <;> simp_all

theorem _root_.Veir.NameResolutionSketch.ResolvesList.getElem? (h : ResolvesList R as bs) (ha : as[i]? = some a) (hb : bs[i]? = some b) : R a b := by
  induction h generalizing i <;> cases i <;> simp_all <;> grind

theorem resolvesList_of_getElem? (hl : as.length = bs.length)
    (h : ∀ (i : Nat) a b, as[i]? = some a → bs[i]? = some b → R a b) : ResolvesList R as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [ResolvesList.nil]
  | cons a as ih =>
    cases bs with
    | nil => simp at hl
    | cons b bs => exact .cons (h 0 a b rfl rfl) (ih (by simpa using hl) (fun i a b ha hb => h (i+1) a b ha hb))

end Indexed

theorem allocation_indexed (ha : ResolvesList (Allocated ctx) insts ops) :
    ResolvesList (fun (inst, i) op => Allocated ctx inst op ∧
      definitionMap ctx block (ops.toArray.map (fun op => ValuePtr.opResult (op.getResult 0))) (.inst i) = some (.opResult (op.getResult 0))) insts.zipIdx ops := by
  apply resolvesList_of_getElem? (by simpa using ha.length)
  intro i e op he ho
  simp only [List.getElem?_zipIdx, Nat.zero_add, Option.map_eq_some_iff] at he
  obtain ⟨inst, hi, rfl⟩ := he
  exact ⟨ha.getElem? hi ho, by simp [definitionMap, ho]⟩

def Ready (ctx : WfIRContext OpCode) (block : BlockPtr) (results : Array ValuePtr)
    (entry : ResolvedAST × Nat) (op : OperationPtr) : Prop :=
  Allocated ctx entry.1 op ∧ definitionMap ctx block results (.inst entry.2) = some (.opResult (op.getResult 0))

theorem Ready.frame (hf : Frame ctx ctx' changed block) (hb : block.InBounds ctx.raw)
    (hn : op ∉ changed) (h : Ready ctx block results entry op) : Ready ctx' block results entry op :=
  ⟨h.1.frame hf hn, by simpa [Ready, hf.definitionMap_eq hb] using h.2⟩

theorem resolvesList_mem_right {R : α → β → Prop} {as : List α} {bs : List β} {b : β} (h : ResolvesList R as bs) (hb : b ∈ bs) : ∃ a, R a b := by
  induction h with
  | nil => simp at hb
  | cons hab _ ih => rcases List.mem_cons.mp hb with rfl | hb; exact ⟨_, hab⟩; exact ih hb

theorem forM_cons_ok {f : α → LowerM Unit}
    (h : ((a :: as).forM f).run ctx = .ok ((), ctx')) :
    ∃ ctx₁, (f a).run ctx = .ok ((), ctx₁) ∧ (as.forM f).run ctx₁ = .ok ((), ctx') := by
  obtain ⟨⟨⟩, ctx₁, ha, ht⟩ := bind_ok (by simpa only [List.forM_eq_forM, List.forM_cons] using h)
  exact ⟨ctx₁, ha, ht⟩

theorem tile_avoids {tile ops : List OperationPtr} {op : OperationPtr} (hf : ∀ c ∈ tile, c = op ∨ ¬c.InBounds ctx.raw)
    (hn : ∀ p ∈ ops, op ≠ p) (ha : ResolvesList (Ready ctx block results) entries ops) :
    ∀ c ∈ tile, c ∉ ops := by
  intro c hc hp; obtain ⟨entry, he⟩ := resolvesList_mem_right ha hp
  rcases hf c hc with rfl | hf; exact hn c hp rfl; exact hf he.1.inBounds

/-- The wiring pass produces tiles using the complete definition table. -/
structure Wiring (block : BlockPtr) (results : Array ValuePtr) (entries : List (ResolvedAST × Nat))
    (ops : List OperationPtr) (os : Array OperationPtr) (ctx ctx' : WfIRContext OpCode) : Prop where
  frame : Frame ctx ctx' ops block
  tiles : ∃ tiles, ResolvesList (fun (inst, i) => LowersInstTile ctx' (definitionMap ctx block results) (.inst i) inst) entries tiles ∧
    block.OpChain ctx'.raw (os ++ tiles.flatten.toArray)
  valid : ∀ e ∈ entries, ValidResolvedInst (block.getNumArguments! ctx.raw) results.size e.1

theorem Frame.numArgs {b : BlockPtr} (hf : Frame ctx ctx' changed block) (hb : b.InBounds ctx.raw) :
    b.getNumArguments! ctx'.raw = b.getNumArguments! ctx.raw := by
  simpa only [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] using congrArg Array.size (hf.args b hb).1

theorem Wiring.cons (hb : block.InBounds ctx.raw)
    (hf : Frame ctx ctx' [op] block)
    (ht : LowersInstTile ctx' (definitionMap ctx block results) (.inst e.2) e.1 tile)
    (hn : ∀ c ∈ tile, c ∉ ops) (hv : ValidResolvedInst (block.getNumArguments! ctx.raw) results.size e.1)
    (hs : Wiring block results entries ops (os ++ tile.toArray) ctx' ctx'') :
    Wiring block results (e :: entries) (op :: ops) os ctx ctx'' := by
  obtain ⟨tiles, hi, hc⟩ := hs.tiles
  refine ⟨hf.trans hs.frame, ⟨tile :: tiles, .cons (ht.frame hs.frame hn) ?_, ?_⟩, ?_⟩
  · simpa only [hf.definitionMap_eq hb] using hi
  · simpa [Array.append_assoc] using hc
  · intro a ha; rcases List.mem_cons.mp ha with rfl | ha; exact hv
    simpa only [hf.numArgs hb] using hs.valid a ha

theorem resolvesList_mono_mem_right {R S : α → β → Prop} {as : List α} {bs : List β}
    (h : ResolvesList R as bs) (f : ∀ b ∈ bs, ∀ a, R a b → S a b) : ResolvesList S as bs := by
  induction h with
  | nil => exact .nil
  | cons hab h ih => exact .cons (f _ (by simp) _ hab) (ih fun b hb => f b (by simp_all))

theorem wire_sound (hb : block.OpChain ctx.raw os)
    (ha : ResolvesList (Ready ctx block results) entries ops) (hn : ops.Pairwise (· ≠ ·))
    (h : ((entries.map Prod.fst).zip ops |>.forM (wireInst block results)).run ctx = .ok ((), ctx')) :
    Wiring block results entries ops os ctx ctx' := by
  induction entries generalizing ops ctx os with
  | nil => cases ha; simp at h; subst ctx'; exact ⟨Frame.refl, ⟨[], .nil, by simpa using hb⟩, by simp⟩
  | cons e entries ih =>
    cases ha with | cons he ha =>
      obtain ⟨hno, hnt⟩ := List.pairwise_cons.mp hn
      obtain ⟨ctx₁, hh, hs⟩ := forM_cons_ok h
      obtain ⟨tile, ht, hc, hf, hnew, hv⟩ := wireInst_sound he.1 hb he.2 hh
      have hr := resolvesList_mono_mem_right ha (fun p hp e he => he.frame hf hb.blockInBounds (by simpa [ne_comm] using hno p hp))
      exact Wiring.cons hb.blockInBounds hf ht (tile_avoids hnew hno ha) hv (ih hc hr hnt hs)

theorem lowerInsts_split (h : (lowerInsts block insts).run ctx = .ok (results, ctx')) :
    ∃ ops ctx₁, (insts.mapM (lowerInst block)).run ctx = .ok (ops, ctx₁) ∧
      ((insts.zip ops).forM (wireInst block (ops.toArray.map (fun op => ValuePtr.opResult (op.getResult 0))))).run ctx₁ = .ok ((), ctx') ∧
      results = ops.toArray.map (fun op => ValuePtr.opResult (op.getResult 0)) := by
  rw [lowerInsts_eq] at h; obtain ⟨ops, ctx₁, ha, ht⟩ := bind_ok h
  obtain ⟨⟨⟩, ctx₂, hw, he⟩ := bind_ok ht
  simp at he; obtain ⟨rfl, rfl⟩ := he; exact ⟨ops, ctx₁, ha, hw, by simp⟩

structure InstsResult (block : BlockPtr) (insts : List ResolvedAST) (results : Array ValuePtr)
    (os : Array OperationPtr) (ctx ctx' : WfIRContext OpCode) : Prop where
  frame : Frame ctx ctx' [] block
  size : results.size = insts.length
  tiles : ∃ tiles, ResolvesList (fun (inst, i) => LowersInstTile ctx' (definitionMap ctx' block results) (.inst i) inst) insts.zipIdx tiles ∧
    block.OpChain ctx'.raw (os ++ tiles.flatten.toArray)
  valid : ∀ inst ∈ insts, ValidResolvedInst (block.getNumArguments! ctx.raw) insts.length inst

theorem instsResult_of_wiring (hb : block.InBounds ctx.raw) (ha : Allocation block insts ops ctx ctx₁)
    (hw : Wiring block (ops.toArray.map (fun op => ValuePtr.opResult (op.getResult 0))) insts.zipIdx ops os ctx₁ ctx') :
    InstsResult block insts (ops.toArray.map (fun op => ValuePtr.opResult (op.getResult 0))) os ctx ctx' := by
  refine ⟨(ha.frame.trans hw.frame).forget ha.fresh, by simpa using ha.allocated.length.symm, ?_, ?_⟩
  · simpa only [hw.frame.definitionMap_eq (ha.frame.bounds (.block block) hb)] using hw.tiles
  · intro inst hi
    obtain ⟨i, he⟩ := List.mem_iff_getElem?.mp hi
    have hv := hw.valid (inst, i) (by simpa [List.getElem?_zipIdx] using List.mem_iff_getElem?.mpr ⟨i, by simp [he]⟩)
    simpa [ha.frame.numArgs hb, ← ha.allocated.length] using hv

theorem lowerInsts_sound (hb : block.OpChain ctx.raw os)
    (h : (lowerInsts block insts).run ctx = .ok (results, ctx')) : InstsResult block insts results os ctx ctx' := by
  obtain ⟨ops, ctx₁, ha, hw, rfl⟩ := lowerInsts_split h
  have ha := allocate_sound ha
  have hw := wire_sound (ha.chain os hb) (allocation_indexed ha.allocated) ha.nodup (by simpa only [List.zipIdx_map_fst] using hw)
  exact instsResult_of_wiring hb.blockInBounds ha hw

theorem createBody_split (h : (createBody ts).run ctx = .ok ((region, body), ctx')) :
    ∃ ctx₁ hi, WfRewriter.createRegion ctx = some (ctx₁, region) ∧
      WfRewriter.createBlock ctx₁ ts (some (.atEnd region)) hi = some (ctx', body) := by
  cases hr : WfRewriter.createRegion ctx with
  | none => simp [createBody, hr] at h
  | some pair =>
    rcases pair with ⟨ctx₁, r⟩
    by_cases hi : (some (BlockInsertPoint.atEnd r)).maybe BlockInsertPoint.InBounds ctx₁.raw
    · cases hb : WfRewriter.createBlock ctx₁ ts (some (.atEnd r)) hi with
      | none => simp [createBody, hr, hi, hb] at h
      | some pair => rcases pair with ⟨ctx₂, b⟩; simp [createBody, hr, hi, hb] at h; rcases h with ⟨⟨rfl, rfl⟩, rfl⟩; exact ⟨ctx₁, hi, rfl, hb⟩
    · simp [createBody, hr, hi] at h

theorem createBlock_raw
    (h : WfRewriter.createBlock ctx ts ip hi = some (ctx', body)) :
    Rewriter.createBlock ctx.raw ts ip (by grind) hi = some (ctx'.raw, body) := by
  unfold WfRewriter.createBlock at h; split at h <;> grind

theorem createRegion_raw (h : WfRewriter.createRegion ctx = some (ctx', region)) :
    Rewriter.createRegion ctx.raw = some (ctx'.raw, region) := by
  unfold WfRewriter.createRegion at h; split at h <;> grind

theorem createBody_frame
    (hr : WfRewriter.createRegion ctx = some (ctx₁, region))
    (hb : WfRewriter.createBlock ctx₁ ts (some (.atEnd region)) hi = some (ctx', body)) : Frame ctx ctx' [] block := by
  have hrr := createRegion_raw hr; have hbr := createBlock_raw hb
  refine ⟨fun p hp => by grind, fun _ _ _ _ _ _ _ _ _ _ hm => (hm.createRegion hr).createBlock hb, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (unfold Rewriter.createBlock at hbr; simp only [Option.bind_eq_bind, Option.bind] at hbr; split at hbr <;> try contradiction)
  all_goals (split at hbr <;> try contradiction); all_goals simp only [Option.some.injEq, Prod.mk.injEq] at hbr; all_goals rcases hbr with ⟨rfl, rfl⟩
  · intro op ho hn; grind (gen := 20)
  · intro b hb; grind (gen := 20)
  · intro b hb; constructor <;> first | (apply Array.ext <;> grind (gen := 20)) | (simp only [BlockPtr.getArguments!]; congr 1; grind (gen := 20))
  · intro b hn os hc; exact BlockPtr.opChain_rewriter_createBlock (BlockPtr.opChain_rewriter_createRegion hc hrr) (createBlock_raw hb)
  · intro r b hc; have hf₀ : r.getFirstBlock! ctx.raw = some b := (by simpa using hc.first); have hl₀ : r.getLastBlock! ctx.raw = some b := (by simpa using hc.last)
    have hfirst := RegionPtr.getFirstBlock!_BlockPtr_allocEmpty (region := r) (show BlockPtr.allocEmpty ctx₁.raw = some (_, _) by assumption); have hlast := RegionPtr.getLastBlock!_BlockPtr_allocEmpty (region := r) (show BlockPtr.allocEmpty ctx₁.raw = some (_, _) by assumption); apply blockChain_singleton <;> (try simp_getset) <;> grind (gen := 20)

theorem createBlock_properties
    (hb : WfRewriter.createBlock ctx ts (some (.atEnd region)) hi = some (ctx', body))
    (_ : region.getFirstBlock! ctx.raw = none) (hl : region.getLastBlock! ctx.raw = none) :
    ¬body.InBounds ctx.raw ∧ region.BlockChain ctx'.raw #[body] ∧
      body.OpChain ctx'.raw #[] ∧ body.getArgumentTypes! ctx'.raw = ts := by
  have hbr := createBlock_raw hb; have hc := BlockPtr.opChain_rewriter_createBlock_new hbr
  unfold Rewriter.createBlock at hbr
  simp only [Option.bind_eq_bind, Option.bind] at hbr
  split at hbr <;> try contradiction
  split at hbr <;> try contradiction
  simp only [Option.some.injEq, Prod.mk.injEq] at hbr
  rcases hbr with ⟨rfl, rfl⟩
  refine ⟨by grind, blockChain_singleton (by grind) (by grind (gen := 20)) (by grind (gen := 20)), hc, ?_⟩
  apply Array.ext <;> grind (gen := 20)

theorem createBody_properties
    (hr : WfRewriter.createRegion ctx = some (ctx₁, region))
    (hb : WfRewriter.createBlock ctx₁ ts (some (.atEnd region)) hi = some (ctx', body)) :
    ¬body.InBounds ctx.raw ∧ ¬region.InBounds ctx.raw ∧ region.BlockChain ctx'.raw #[body] ∧
      body.OpChain ctx'.raw #[] ∧ body.getArgumentTypes! ctx'.raw = ts := by
  have hrr := createRegion_raw hr
  obtain ⟨hn, hblocks, hchain, ht⟩ := createBlock_properties hb (by grind) (by grind)
  exact ⟨fun hi => hn (by grind), by grind, hblocks, hchain, ht⟩

theorem Frame.retarget (hf : Frame ctx ctx' changed block) (hn : ¬block.InBounds ctx.raw) : Frame ctx ctx' changed other :=
  { hf with chains := fun b _ os hc => hf.chains b (fun he => hn (he ▸ hc.blockInBounds)) os hc }

theorem Frame.preservesMatches (hf : Frame ctx ctx' [] block) : PreservesMatches ctx ctx' :=
  fun op code ts vs rs props hm => hf.ops op (by simp) code ts vs rs props hm

structure FunctionBody (ctx : WfIRContext OpCode) (f : ResolvedFunction) (region : RegionPtr) (body : BlockPtr) : Prop where
  valid : ValidResolvedFunction f
  blocks : region.BlockChain ctx.raw #[body]
  args : body.getArgumentTypes! ctx.raw = f.header.params.toArray.map (lowerType ·.ty)
  content : ∃ tiles cs ret v, ∃ values : ValueMap,
    (∀ i, values (.param i) = (body.getArguments! ctx.raw)[i]?) ∧
    ResolvesList (fun (inst, i) => LowersInstTile ctx values (.inst i) inst) f.insts.zipIdx tiles ∧
    OperandTile ctx values f.header.retType f.result v cs ∧ MatchesOp ctx ret Llvm.return #[] #[v] #[] () ∧
    body.OpChain ctx.raw (tiles.flatten ++ cs ++ [ret]).toArray

theorem FunctionBody.frame (hf : Frame ctx ctx' [] block) (hn : body ≠ block)
    (h : FunctionBody ctx f region body) : FunctionBody ctx' f region body := by
  obtain ⟨tiles, cs, ret, v, values, hp, hi, hv, hr, hc⟩ := h.content
  obtain ⟨htypes, hargs⟩ := hf.args body hc.blockInBounds
  exact ⟨h.valid, hf.regions _ _ h.blocks, htypes.trans h.args,
    tiles, cs, ret, v, values, fun i => (hp i).trans (congrArg (·[i]?) hargs).symm,
    resolvesList_mono (fun _ _ h => h.mono hf.preservesMatches) hi,
    hv.mono hf.preservesMatches, hf.preservesMatches _ _ _ _ _ _ hr, hf.chains _ hn _ hc⟩

theorem FunctionBody.to_function (h : FunctionBody ctx f region body)
    (hm : MatchesOp ctx op Llvm.func #[] #[] #[region]
      (LLVMFuncProperties.mk ⟨f.header.name.toUTF8⟩
        { inputs := f.header.params.toArray.map (fun p => (lowerType p.ty).val)
          outputs := #[(lowerType f.header.retType).val] } .empty)) : LowersFunctionTiles ctx f op := by
  obtain ⟨tiles, cs, ret, v, values, hp, hi, hv, hr, hc⟩ := h.content
  exact ⟨h.valid, region, body, tiles, cs, ret, v, values, hm, h.blocks, h.args, hp, hi, hv, hr, hc⟩

theorem lowerFunction_split
    (h : (lowerFunction moduleBlock f).run ctx = .ok (op, ctx')) :
    ∃ region body results value ret ctx₁ ctx₂ ctx₃ ctx₄,
      (createBody (f.header.params.toArray.map (lowerType ·.ty))).run ctx = .ok ((region, body), ctx₁) ∧
      (lowerInsts body f.insts).run ctx₁ = .ok (results, ctx₂) ∧
      (lowerValue body results f.header.retType f.result).run ctx₂ = .ok (value, ctx₃) ∧
      (emit .return #[] #[value] #[] () body).run ctx₃ = .ok (ret, ctx₄) ∧
      (emit .func #[] #[] #[region]
        { sym_name := ⟨f.header.name.toUTF8⟩
          function_type := { inputs := (f.header.params.toArray.map (lowerType ·.ty)).map Subtype.val, outputs := #[(lowerType f.header.retType).val] }
          extra := .empty } moduleBlock).run ctx₄ = .ok (op, ctx') := by
  obtain ⟨⟨region, body⟩, ctx₁, hb, hi⟩ := bind_ok (show (lowerFunction moduleBlock f).run ctx = _ from h)
  obtain ⟨results, ctx₂, hi, hv⟩ := bind_ok hi
  obtain ⟨value, ctx₃, hv, hr⟩ := bind_ok hv
  obtain ⟨ret, ctx₄, hr, hf⟩ := bind_ok hr
  exact ⟨region, body, results, value, ret, ctx₁, ctx₂, ctx₃, ctx₄, hb, hi, hv, hr, hf⟩

theorem functionBody_valid (hb : body.InBounds ctx.raw) (ht : body.getArgumentTypes! ctx.raw = f.header.params.toArray.map (lowerType ·.ty))
    (hi : InstsResult body f.insts results #[] ctx ctx₁)
    (hv : ValidResolvedValue (body.getNumArguments! ctx₁.raw) results.size f.result) : ValidResolvedFunction f := by
  have hnum : body.getNumArguments! ctx.raw = f.header.params.length := by
    simpa only [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!, Array.size_map, List.size_toArray] using congrArg Array.size ht
  exact ⟨by simpa only [hnum] using hi.valid, by simpa only [hi.size, hi.frame.numArgs hb, hnum] using hv⟩

theorem finishBody_sound {f : ResolvedFunction} {region : RegionPtr} {body : BlockPtr} (hb : region.BlockChain ctx.raw #[body])
    (ht : body.getArgumentTypes! ctx.raw = f.header.params.toArray.map (lowerType ·.ty))
    (hi : InstsResult body f.insts results #[] ctx ctx₁)
    (hv : (lowerValue body results f.header.retType f.result).run ctx₁ = .ok (v, ctx₂))
    (hr : (emit .return #[] #[v] #[] () body).run ctx₂ = .ok (ret, ctx')) :
    FunctionBody ctx' f region body ∧ Frame ctx ctx' [] body := by
  obtain ⟨tiles, hinst, hchain⟩ := hi.tiles; have hbin : body.InBounds ctx.raw := hb.arrayInBounds (by simp)
  have hb₁ := hi.frame.bounds (.block body) hbin; obtain ⟨cs, hvalue, hchain⟩ := lowerValue_chain hchain hv
  have hfv := Frame.lowerValue hv; have hfr := Frame.emit hr; have hf : Frame ctx₁ ctx' [] body := hfv.trans hfr
  refine ⟨⟨functionBody_valid hbin ht hi (lowerValue_valid hv), (hi.frame.trans hf).regions _ _ hb,
    ((hi.frame.trans hf).args body hbin).1.trans ht, tiles, cs, ret, v, definitionMap ctx₁ body results,
    ?_, resolvesList_mono (fun _ _ h => h.mono hf.preservesMatches) hinst,
    hvalue.mono hfr.preservesMatches, emit_matches hr, ?_⟩, hi.frame.trans hf⟩
  · intro i; simp only [definitionMap, (hf.args body hb₁).2]
  · simpa [Array.append_assoc] using opChain_emit hchain hr

theorem MatchesOp.regions_eq
    {D : Type} [HasOpInfo D] [HasDialect OpCode D] {code : D} {props : propertiesOf code}
    (h : MatchesOp ctx op code ts vs rs props) : op.getRegions! ctx.raw = rs := by grind [MatchesOp]

theorem LowersFunctionTiles.body (h : LowersFunctionTiles ctx f op) :
    ∃ region body, MatchesOp ctx op Llvm.func #[] #[] #[region]
      (LLVMFuncProperties.mk ⟨f.header.name.toUTF8⟩
        { inputs := f.header.params.toArray.map (fun p => (lowerType p.ty).val)
          outputs := #[(lowerType f.header.retType).val] } .empty) ∧ FunctionBody ctx f region body := by
  obtain ⟨hf, r, b, tiles, cs, ret, v, values, hm, hr, ht, hp, hi, hv, hret, hc⟩ := h
  exact ⟨r, b, hm, hf, hr, ht, tiles, cs, ret, v, values, hp, hi, hv, hret, hc⟩

/-- A function body is separate from the enclosing module block. -/
def SafeFunction (ctx : WfIRContext OpCode) (block : BlockPtr) (f : ResolvedFunction) (op : OperationPtr) : Prop :=
  LowersFunctionTiles ctx f op ∧ ∃ region, op.getRegions! ctx.raw = #[region] ∧ block.getParent! ctx.raw ≠ some region

theorem SafeFunction.frame (hf : Frame ctx ctx' [] block) (hb : block.InBounds ctx.raw)
    (h : SafeFunction ctx block f op) : SafeFunction ctx' block f op := by
  obtain ⟨hfun, region, hreg, hne⟩ := h
  obtain ⟨r, body, hm, hbody⟩ := hfun.body
  have he : region = r := by have := hm.regions_eq; grind
  subst region
  have hn : body ≠ block := by intro he; subst body; exact hne (hbody.blocks.opParent (by simp))
  have hm' := hf.ops op (by simp) _ _ _ _ _ hm
  exact ⟨(hbody.frame hf hn).to_function hm', r, hm'.regions_eq, by simpa only [hf.blocks block hb] using hne⟩

theorem lowerFunction_sound (hb : moduleBlock.OpChain ctx.raw os)
    (h : (lowerFunction moduleBlock f).run ctx = .ok (op, ctx')) :
    Frame ctx ctx' [] moduleBlock ∧ SafeFunction ctx' moduleBlock f op ∧ moduleBlock.OpChain ctx'.raw (os.push op) := by
  obtain ⟨region, body, results, value, ret, ctx₁, ctx₂, ctx₃, ctx₄, hc, hi, hv, hr, hf⟩ := lowerFunction_split h
  obtain ⟨ctxr, hip, hreg, hblock⟩ := createBody_split hc; obtain ⟨hnew, hnewr, hblocks, hchain, htypes⟩ := createBody_properties hreg hblock
  obtain ⟨hbody, hrest⟩ := finishBody_sound hblocks htypes (lowerInsts_sound hchain hi) hv hr
  have hbodyframe : Frame ctx ctx₄ [] body := (createBody_frame hreg hblock).trans hrest
  have hne : body ≠ moduleBlock := fun he => hnew (he ▸ hb.blockInBounds); have hemit := Frame.emit hf
  have hframe : Frame ctx ctx' [] moduleBlock := (hbodyframe.retarget hnew).trans hemit; have hm := emit_matches hf
  have heq : (f.header.params.toArray.map (lowerType ·.ty)).map Subtype.val = f.header.params.toArray.map (fun p => (lowerType p.ty).val) := Array.map_map (β := TypeAttr)
  refine ⟨hframe, ⟨(hbody.frame hemit hne).to_function (by simpa only [heq] using hm), region, hm.regions_eq, ?_⟩, ?_⟩
  · rw [hframe.blocks moduleBlock hb.blockInBounds]; intro hp; exact hnewr (by grind)
  · simpa using opChain_emit (hbodyframe.chains moduleBlock hne.symm _ hb) hf

def lowerFunctions (block : BlockPtr) (fs : List ResolvedFunction) : LowerM Unit :=
  fs.forM (fun f => do let _ ← lowerFunction block f)

theorem discard_lowerFunction_ok
    (h : (do let _ ← lowerFunction block f).run ctx = .ok ((), ctx')) :
    ∃ op, (lowerFunction block f).run ctx = .ok (op, ctx') := by
  obtain ⟨op, ctx₁, hf, he⟩ := bind_ok h
  simp at he; obtain rfl := he; exact ⟨op, hf⟩

structure FunctionsResult (block : BlockPtr) (fs : List ResolvedFunction) (os : Array OperationPtr)
    (ctx ctx' : WfIRContext OpCode) : Prop where
  frame : Frame ctx ctx' [] block
  functions : ∃ ops, ResolvesList (SafeFunction ctx' block) fs ops ∧ block.OpChain ctx'.raw (os ++ ops.toArray)

theorem FunctionsResult.cons (hb : block.InBounds ctx.raw) (hf : Frame ctx ctx' [] block)
    (hs : SafeFunction ctx' block f op) (ht : FunctionsResult block fs (os.push op) ctx' ctx'') :
    FunctionsResult block (f :: fs) os ctx ctx'' := by
  obtain ⟨ops, hm, hc⟩ := ht.functions
  exact ⟨hf.trans ht.frame, op :: ops, .cons (hs.frame ht.frame (hf.bounds (.block block) hb)) hm, by simpa using hc⟩

theorem lowerFunctions_sound (hb : block.OpChain ctx.raw os)
    (h : (lowerFunctions block fs).run ctx = .ok ((), ctx')) : FunctionsResult block fs os ctx ctx' := by
  induction fs generalizing ctx os with
  | nil => simp [lowerFunctions] at h; subst ctx'; exact ⟨Frame.refl, [], .nil, by simpa using hb⟩
  | cons f fs ih =>
    obtain ⟨ctx₁, hh, ht⟩ := forM_cons_ok h
    obtain ⟨op, hh⟩ := discard_lowerFunction_ok hh
    obtain ⟨hf, hs, hc⟩ := lowerFunction_sound hb hh
    exact FunctionsResult.cons hb.blockInBounds hf hs (ih hc ht)

theorem createOp_raw
    {D : Type} [HasOpInfo D] [HasDialect OpCode D] {code : D} {props : propertiesOf code}
    (h : Rewriter.createOp ctx.raw code ts vs bs rs props ip ho hb hr hi (by grind) = some (ctx'.raw, op)) :
    WfRewriter.createOp ctx code ts vs bs rs props ip ho hb hr hi = some (ctx', op) := by
  unfold WfRewriter.createOp; split
  · rename_i he; rw [h] at he; contradiction
  · rename_i raw ptr he
    have hp := Prod.mk.inj (Option.some.inj (h.symm.trans he))
    rcases hp with ⟨rfl, rfl⟩; rfl

theorem createBlock_parent {op : OperationPtr} (hb : WfRewriter.createBlock ctx ts (some (.atEnd region)) hi = some (ctx', body)) :
    op.getParent! ctx'.raw = op.getParent! ctx.raw := by
  have hbr := createBlock_raw hb
  unfold Rewriter.createBlock at hbr
  simp only [Option.bind_eq_bind, Option.bind] at hbr
  split at hbr <;> try contradiction
  split at hbr <;> try contradiction
  simp only [Option.some.injEq, Prod.mk.injEq] at hbr
  rcases hbr with ⟨rfl, rfl⟩; simp_getset; grind

theorem createBlock_of_raw
    (h : Rewriter.createBlock ctx.raw ts ip (by grind) hi = some (ctx'.raw, body)) :
    WfRewriter.createBlock ctx ts ip hi = some (ctx', body) := by
  unfold WfRewriter.createBlock; split
  · rename_i he; rw [h] at he; contradiction
  · rename_i raw ptr he; have hp := Prod.mk.inj (Option.some.inj (h.symm.trans he)); rcases hp with ⟨rfl, rfl⟩; rfl

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
  have hro := createOp_raw (ctx := ⟨raw₁, hw₁⟩) (ctx' := ⟨raw₂, hw₂⟩) hroot; have hm := createOp_matches hro; have hp : root.getParent! raw₂ = none := (by have := OperationPtr.getParent!_WfRewriter_createOp (operation := root) hro; simpa using this)
  have hb := createBlock_of_raw (ctx := ⟨raw₂, hw₂⟩) (ctx' := ⟨raw₃, by grind [Rewriter.createBlock_WellFormed]⟩) hblock; obtain ⟨_, hblocks, hchain, htypes⟩ := createBlock_properties hb (by grind (gen := 20)) (by grind (gen := 20))
  exact ⟨region, block, hm.createBlock hb, hblocks, hchain, (createBlock_parent hb).trans hp, htypes⟩

theorem lowerModule_split (h : lowerModule m = .ok (ctx, root)) :
    ∃ ctx₀ block, WfIRContext.create OpCode = some (ctx₀, root) ∧
      (root.getRegion! ctx₀.raw 0).getFirstBlock! ctx₀.raw = some block ∧
      (lowerFunctions block m.funcs).run ctx₀ = .ok ((), ctx) := by
  cases hc : WfIRContext.create OpCode
  · simp [lowerModule, hc] at h
  · rename_i pair; rcases pair with ⟨ctx₀, root₀⟩
    cases hb : (root₀.getRegion! ctx₀.raw 0).getFirstBlock! ctx₀.raw
    · simp [lowerModule, hc, hb] at h
    · rename_i block; simp only [lowerModule, hc, hb] at h
      change (do let ((), ctx₁) ← (lowerFunctions block m.funcs).run ctx₀; pure (ctx₁, root₀)) = .ok (ctx, root) at h
      cases hf : lowerFunctions block m.funcs ctx₀
      · simp [hf] at h
      · rename_i pair; rcases pair with ⟨⟨⟩, ctx₁⟩; simp [hf] at h; rcases h with ⟨rfl, rfl⟩; exact ⟨ctx₀, block, rfl, hb, hf⟩


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
theorem lowerModule_sound : lowerModule m = .ok (ctx, root) → LowersModule ctx m root := by
  intro h; obtain ⟨ctx₀, block, hc, hb, hf⟩ := lowerModule_split h
  obtain ⟨region, b, hm, hr, ho, hp, ha⟩ := createModule_sound hc
  have hg : root.getRegion! ctx₀.raw 0 = region := (by rw [← OperationPtr.getRegions!.getElem!_eq_getRegion!, hm.regions_eq]; rfl)
  have he : b = block := (by rw [hg, hr.first] at hb; simpa using hb); subst b
  have hs := lowerFunctions_sound ho hf; obtain ⟨ops, hfs, hchain⟩ := hs.functions
  exact ⟨region, block, ops, hs.frame.ops root (by simp) _ _ _ _ _ hm, hs.frame.regions _ _ hr,
    by simpa using hchain, (hs.frame.parents root hm.1 (by simp)).trans hp,
    (hs.frame.args block ho.blockInBounds).1.trans ha, resolvesList_mono (fun _ _ h => h.1) hfs⟩

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
