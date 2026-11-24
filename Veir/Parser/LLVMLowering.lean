import Veir.IR.RootedIso
import Veir.Parser.LoweringInitial
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

/-- The `llvm.func` properties beyond name and type that `mlir-translate` gives a function whose
source names no calling convention, linkage, `unnamed_addr` or visibility. -/
def defaultFuncExtra : DictionaryAttr where
  entries := #[("CConv".toUTF8, .cconvAttr ⟨"ccc"⟩), ("linkage".toUTF8, .linkageAttr ⟨"external"⟩),
    ("unnamed_addr".toUTF8, .integerAttr { value := 0, type := .signless 64 }),
    ("visibility_".toUTF8, .integerAttr { value := 0, type := .signless 64 })]

/-- The module attributes `mlir-translate` gives a module with no `target datalayout`,
`target triple` or `module asm`. The layout is MLIR's default data layout. -/
def defaultModuleAttrs : DictionaryAttr where
  entries := #[("dlti.dl_spec".toUTF8, .dlSpecAttr ⟨"!llvm.ptr = dense<64> : vector<4xi64>, \
i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, \
i32 = dense<32> : vector<2xi64>, i64 = dense<[32, 64]> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, \
f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, \"dlti.endianness\" = \"little\""⟩),
    ("llvm.module_asm".toUTF8, .arrayAttr ⟨#[]⟩), ("llvm.target_triple".toUTF8, .stringAttr ⟨"".toUTF8⟩)]

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
      extra := defaultFuncExtra } moduleBlock

def lowerFunctions (block : BlockPtr) (fs : List ResolvedFunction) : LowerM Unit :=
  fs.forM (fun f => do let _ ← lowerFunction block f)

/-- An empty module carrying `defaultModuleAttrs`. -/
def createModule : Option (WfIRContext OpCode × OperationPtr) :=
  (WfIRContext.create OpCode).bind fun (ctx, root) =>
    if h : root.InBounds ctx.raw then some (WfRewriter.setAttributes ctx root defaultModuleAttrs h, root) else none

/-- Prototype lowering of the resolved single-block integer fragment.
Supports forward references and rejects undefined references; LLVM validity is checked separately. -/
def lowerModule (m : ResolvedModule) :
    Except LoweringError (WfIRContext OpCode × OperationPtr) := do
  let some (ctx, root) := createModule
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
    (regions : Array RegionPtr) (properties : propertiesOf opcode) (attrs : DictionaryAttr := .empty) : Prop :=
  op.InBounds ctx.raw ∧ op.getProperties! ctx.raw opcode = properties ∧
  (op.getOpType! ctx.raw, op.getResultTypes! ctx.raw, op.getOperands! ctx.raw,
    op.getRegions! ctx.raw, op.getNumSuccessors! ctx.raw, op.getAttributes! ctx.raw) =
  (ofDialect OpCode opcode, types, operands, regions, 0, attrs)

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
          outputs := #[(lowerType f.header.retType).val] } defaultFuncExtra) ∧
    region.BlockChain ctx.raw #[block] ∧
    block.getArgumentTypes! ctx.raw = f.header.params.toArray.map (lowerType ·.ty) ∧
    (∀ i, values (.param i) = (block.getArguments! ctx.raw)[i]?) ∧
    ResolvesList (fun (inst, i) => LowersInstTile ctx values (.inst i) inst) f.insts.zipIdx tiles ∧
    OperandTile ctx values f.header.retType f.result v cs ∧
    MatchesOp ctx ret Llvm.return #[] #[v] #[] () ∧
    block.OpChain ctx.raw (tiles.flatten ++ cs ++ [ret]).toArray

#check BlockPtr.getArguments!

/-- Only the module reachable from the root is specified;  We don't require Dominance -/
def LowersModule (m : ResolvedModule) (root : OperationPtr) : Prop :=
  ∃ (region : RegionPtr) (block : BlockPtr) (funcs : List OperationPtr),
    MatchesOp ctx root Builtin.module #[] #[] #[region] default defaultModuleAttrs ∧
    region.BlockChain ctx.raw #[block] ∧
    block.OpChain ctx.raw funcs.toArray ∧
    block.getArgumentTypes! ctx.raw = #[] ∧ ResolvesList (LowersFunctionTiles ctx) m.funcs funcs



end Specification

section Soundness

set_option maxRecDepth 4000
set_option maxHeartbeats 800000

variable {ctx ctx' ctx'' : WfIRContext OpCode} {block : BlockPtr} {changed changed' : List OperationPtr}
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpCode Dialect]
variable {opcode : Dialect} {properties : propertiesOf opcode} {attrs : DictionaryAttr}

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

theorem MatchesOp.pushOperand (h : MatchesOp ctx op opcode types operands regions properties attrs) :
    MatchesOp (WfRewriter.pushOperand ctx target value ht hv) op opcode types
      (if op = target then operands.push value else operands) regions properties attrs := by
  simp only [MatchesOp, Prod.mk.injEq, WfRewriter.pushOperand] at *; simp_getset; grind

theorem MatchesOp.insertOp (h : MatchesOp ctx op opcode types operands regions properties attrs)
    (hc : WfRewriter.insertOp ctx target ip ht hi = some ctx') :
    MatchesOp ctx' op opcode types operands regions properties attrs := by
  have hr : op.getRegions! ctx'.raw = op.getRegions! ctx.raw := by apply Array.ext <;> grind
  simp only [MatchesOp, Prod.mk.injEq] at *; simp_getset; grind

theorem MatchesOp.createOp (h : MatchesOp ctx op opcode types operands regions properties attrs)
    {newCode : Llvm} {newProps : propertiesOf newCode}
    (hc : WfRewriter.createOp ctx newCode ts vs bs rs newProps ip ho hb hr hi = some (ctx', newOp)) :
    MatchesOp ctx' op opcode types operands regions properties attrs := by
  have hn : op ≠ newOp := by have := WfRewriter.createOp_new_not_inBounds newOp hc; grind [MatchesOp]
  have hr : op.getRegions! ctx'.raw = op.getRegions! ctx.raw := by apply Array.ext <;> grind
  simp only [MatchesOp, Prod.mk.injEq] at *; simp_getset; grind

theorem MatchesOp.createRegion (h : MatchesOp ctx op opcode types operands regions properties attrs)
    (hc : WfRewriter.createRegion ctx = some (ctx', region)) :
    MatchesOp ctx' op opcode types operands regions properties attrs := by
  simp only [WfRewriter.createRegion] at hc
  have hr : op.getRegions! ctx'.raw = op.getRegions! ctx.raw := by apply Array.ext <;> grind
  simp only [MatchesOp, Prod.mk.injEq] at *; try simp_getset
  grind

theorem MatchesOp.createBlock (h : MatchesOp ctx op opcode types operands regions properties attrs)
    (hc : WfRewriter.createBlock ctx ts ip hi = some (ctx', block)) :
    MatchesOp ctx' op opcode types operands regions properties attrs := by
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
    (code : D) ts vs rs props {attrs}, MatchesOp ctx op code ts vs rs props attrs → MatchesOp ctx' op code ts vs rs props attrs
  parents : ∀ op, op.InBounds ctx.raw → op ∉ changed → op.getParent! ctx'.raw = op.getParent! ctx.raw
  args : ∀ b : BlockPtr, b.InBounds ctx.raw → b.getArgumentTypes! ctx'.raw = b.getArgumentTypes! ctx.raw ∧ b.getArguments! ctx'.raw = b.getArguments! ctx.raw
  chains : ∀ b : BlockPtr, b ≠ block → ∀ os, b.OpChain ctx.raw os → b.OpChain ctx'.raw os
  regions : ∀ (r : RegionPtr) (b : BlockPtr), r.BlockChain ctx.raw #[b] → r.BlockChain ctx'.raw #[b]

theorem Frame.refl : Frame ctx ctx [] block :=
  ⟨fun _ h => h, fun _ _ _ _ _ _ _ _ _ _ _ h => h, fun _ _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩, fun _ _ _ h => h, fun _ _ h => h⟩

theorem Frame.trans (h : Frame ctx ctx' changed block) (h' : Frame ctx' ctx'' changed' block) :
    Frame ctx ctx'' (changed ++ changed') block := by
  refine ⟨fun p hp => h'.bounds p (h.bounds p hp), fun op hn _ _ _ _ _ _ _ _ _ hm => h'.ops op (by simp_all) _ _ _ _ _ (h.ops op (by simp_all) _ _ _ _ _ hm),
    fun op ho hn => (h'.parents op (h.bounds (.operation op) ho) (by simp_all)).trans (h.parents op ho (by simp_all)),
    fun b hb => ?_, fun b hn os ho => h'.chains b hn os (h.chains b hn os ho), fun r bs hr => h'.regions r bs (h.regions r bs hr)⟩
  exact ⟨(h'.args b (h.bounds (.block b) hb)).1.trans (h.args b hb).1, (h'.args b (h.bounds (.block b) hb)).2.trans (h.args b hb).2⟩

/-- Shrink `changed` to `changed'`, dropping operations fresh in `ctx`; retarget to `other` if `block` is fresh. -/
theorem Frame.mono (h : Frame ctx ctx' changed block) (hs : ∀ op ∈ changed, op ∈ changed' ∨ ¬op.InBounds ctx.raw)
    (hb : block = other ∨ ¬block.InBounds ctx.raw) : Frame ctx ctx' changed' other := by
  refine { h with ops := ?_, parents := fun op ho hn => h.parents op ho fun hp => (hs op hp).elim hn (· ho), chains := ?_ }
  · intro op hn _ _ _ c ts vs rs ps _ hm; exact h.ops op (fun hp => (hs op hp).elim hn (· hm.1)) _ _ _ _ _ hm
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
  refine ⟨fun p hp => by grind, fun _ _ _ _ _ _ _ _ _ _ _ hm => hm.createOp hc, fun p hp _ => ?_, fun b hb => ⟨?_, ?_⟩, ?_, ?_⟩
  · have := WfRewriter.createOp_new_not_inBounds op hc; grind
  · apply Array.ext (by grind); intro i hi hi'; have := ValuePtr.getType!_WfRewriter_createOp (value := .blockArgument (b.getArgument i)) hc; grind
  · simp only [BlockPtr.getArguments!]; congr 1; grind
  · intro b hn os hb; apply BlockPtr.OpChain_unchanged hb <;> grind
  · intro r b hb; apply blockChain_singleton <;> grind

theorem Frame.pushOperand (ho : op.InBounds ctx.raw) (hv : v.InBounds ctx.raw) :
    Frame ctx (WfRewriter.pushOperand ctx op v ho hv) [op] block := by
  refine ⟨fun p hp => by grind [WfRewriter.pushOperand], fun p hn _ _ _ _ _ _ _ _ _ hm => by simpa [show p ≠ op by simpa using hn] using hm.pushOperand (target := op) (ht := ho) (hv := hv),
    fun p hp hn => by grind [WfRewriter.pushOperand], fun b hb => ⟨?_, ?_⟩, fun _ _ _ h => opChain_pushOperand h,
    fun _ _ h => by apply RegionPtr.blockChain_unchanged h <;> grind [WfRewriter.pushOperand]⟩
  · apply Array.ext <;> grind [WfRewriter.pushOperand]
  · simp only [BlockPtr.getArguments!]; congr 1; grind [WfRewriter.pushOperand]

theorem Frame.insertOp {ho : op.InBounds ctx.raw} {hi : (InsertPoint.atEnd block).InBounds ctx.raw}
    (hp : op.getParent! ctx.raw = none)
    (hc : WfRewriter.insertOp ctx op (.atEnd block) ho hi = some ctx') : Frame ctx ctx' [op] block := by
  refine ⟨fun p hp => by grind, fun _ _ _ _ _ _ _ _ _ _ _ hm => hm.insertOp hc, fun p hp hn => by grind, fun b hb => ⟨?_, ?_⟩, ?_, ?_⟩
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
  refine ⟨fun p hp => by grind, fun _ _ _ _ _ _ _ _ _ _ _ hm => (hm.createRegion hr).createBlock hb, ?_, ?_, ?_, ?_⟩
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

theorem createRawModule_sound (h : WfIRContext.create OpCode = some (ctx, root)) :
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

theorem setAttributes_inBounds (p : GenericPtr) :
    p.InBounds (WfRewriter.setAttributes ctx op a ho).raw ↔ p.InBounds ctx.raw :=
  Rewriter.setAttributes_inBounds (opIn := ho) p

theorem setAttributes_opInBounds (o : OperationPtr) :
    o.InBounds (WfRewriter.setAttributes ctx op a ho).raw ↔ o.InBounds ctx.raw := setAttributes_inBounds (.operation o)

theorem MatchesOp.setAttributes (h : MatchesOp ctx op opcode types operands regions properties attrs)
    (ho : op.InBounds ctx.raw) :
    MatchesOp (WfRewriter.setAttributes ctx op a ho) op opcode types operands regions properties a := by
  simp only [MatchesOp, Prod.mk.injEq] at *; exact ⟨(setAttributes_opInBounds op).mpr ho, by grind⟩

theorem createModule_sound (h : createModule = some (ctx, root)) :
    ∃ region block, MatchesOp ctx root Builtin.module #[] #[] #[region] default defaultModuleAttrs ∧
      region.BlockChain ctx.raw #[block] ∧ block.OpChain ctx.raw #[] ∧
      root.getParent! ctx.raw = none ∧ block.getArgumentTypes! ctx.raw = #[] := by
  rcases hc : WfIRContext.create OpCode with _ | ⟨c, r⟩; · simp [createModule, hc] at h
  simp only [createModule, hc, Option.bind] at h; split at h <;> cases h; rename_i hr
  obtain ⟨region, block, hm, hb, ho, hp, ha⟩ := createRawModule_sound hc
  refine ⟨region, block, hm.setAttributes hr, ?_, ?_, ?_, ?_⟩
  · apply RegionPtr.blockChain_unchanged hb <;> grind [setAttributes_inBounds]
  · apply BlockPtr.OpChain_unchanged ho <;> grind [setAttributes_inBounds]
  all_goals grind

theorem lowerModule_sound : lowerModule m = .ok (ctx, root) → LowersModule ctx m root := by
  intro h; rcases hc : createModule with _ | ⟨ctx₀, root₀⟩ <;> simp [lowerModule, hc] at h
  rcases hb : (root₀.getRegion! ctx₀.raw 0).getFirstBlock! ctx₀.raw with _ | block <;> simp [hb] at h
  rcases hf : lowerFunctions block m.funcs ctx₀ with _ | ⟨_, c⟩ <;> simp [hf] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨region, b, hm, hr, ho, hp, ha⟩ := createModule_sound hc
  obtain rfl : b = block := by rw [← OperationPtr.getRegions!.getElem!_eq_getRegion!, show root₀.getRegions! _ = #[region] by grind [MatchesOp]] at hb; simpa [hr.first] using hb
  obtain ⟨hs, ops, hfs, hchain⟩ := lowerFunctions_sound ho hf
  exact ⟨region, b, ops, hs.ops root₀ (by simp) _ _ _ _ _ hm, hs.regions _ _ hr, by simpa using hchain,
    (hs.args b ho.blockInBounds).1.trans ha, resolvesList_mono hfs fun _ _ _ h => h _ Frame.refl⟩

end Soundness


/--
info: "builtin.module"() ({
  ^2():
    "llvm.func"() <{"CConv" = #llvm.cconv<ccc>, "function_type" = !llvm.func<i32 (i32, i32)>, "linkage" = #llvm.linkage<external>, "sym_name" = "demorgan_or", "unnamed_addr" = 0 : i64, "visibility_" = 0 : i64}> ({
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
    "llvm.func"() <{"CConv" = #llvm.cconv<ccc>, "function_type" = !llvm.func<i32 (i32, i32)>, "linkage" = #llvm.linkage<external>, "sym_name" = "demorgan_and", "unnamed_addr" = 0 : i64, "visibility_" = 0 : i64}> ({
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
}) {"dlti.dl_spec" = #dlti.dl_spec<!llvm.ptr = dense<64> : vector<4xi64>, i1 = dense<8> : vector<2xi64>, i8 = dense<8> : vector<2xi64>, i16 = dense<16> : vector<2xi64>, i32 = dense<32> : vector<2xi64>, i64 = dense<[32, 64]> : vector<2xi64>, f16 = dense<16> : vector<2xi64>, f64 = dense<64> : vector<2xi64>, f128 = dense<128> : vector<2xi64>, "dlti.endianness" = "little">, "llvm.module_asm" = [], "llvm.target_triple" = ""} : () -> ()
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
  let [region] := (op.getRegions! ctx.raw).toList | throw "expected one region"
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

/-- Operations other than literal constants define instructions. -/
def isDefinition (ctx : WfIRContext OpCode) (op : OperationPtr) : Bool :=
  toDialect? Llvm (op.getOpType! ctx.raw) != some .mlir__constant

/-- Number the block's arguments as parameters and the definitions as instructions. -/
def valueTable (ctx : WfIRContext OpCode) (block : BlockPtr) (defs : List OperationPtr) :
    List (ValuePtr × ValueId) :=
  (block.getArguments! ctx.raw).toList.zipIdx.map (fun (v, i) => (v, .param i)) ++
    defs.zipIdx.map (fun (inst, i) => (.opResult (inst.getResult 0), .inst i))

def reverseInst (ctx : WfIRContext OpCode) (values : List (ValuePtr × ValueId))
    (inst : OperationPtr) : Except String ResolvedAST := do
  let opc ← match toDialect? Llvm (inst.getOpType! ctx.raw) with
    | some .and => pure BinOp.and
    | some .or => pure BinOp.or
    | some .xor => pure BinOp.xor
    | _ => throw "unsupported instruction"
  let [ty] := (inst.getResultTypes! ctx.raw).toList | throw "expected one instruction result"
  let [lhs, rhs] := (inst.getOperands! ctx.raw).toList | throw "expected two operands"
  return .bin opc (← reverseType ty.val) (← reverseValue ctx values lhs) (← reverseValue ctx values rhs)

def reverseParam : TypeAttr × Nat → Except String Param
  | (ty, i) => return ⟨← reverseType ty.val, s!"arg{i}"⟩

/-- Recover a single-block function, giving parameters and the block canonical names.
Constants become literals; binary operations retain their block order. -/
def reverseFunction (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Except String ResolvedFunction := do
  if toDialect? Llvm (op.getOpType! ctx.raw) != some .func then throw "expected llvm.func"
  let props := op.getProperties! ctx.raw Llvm.func
  let [output] := props.function_type.outputs.toList | throw "expected one return type"
  let retType ← reverseType output
  let block ← reverseBody ctx op
  let ops ← reverseOps ctx block
  let some ret := ops.getLast? | throw "expected a return"
  if toDialect? Llvm (ret.getOpType! ctx.raw) != some .return then throw "expected llvm.return"
  let [result] := (ret.getOperands! ctx.raw).toList | throw "expected one return operand"
  let values := valueTable ctx block (ops.dropLast.filter (isDefinition ctx))
  let insts ← (ops.dropLast.filter (isDefinition ctx)).mapM (reverseInst ctx values)
  let params ← (block.getArgumentTypes! ctx.raw).toList.zipIdx.mapM reverseParam
  return ⟨⟨retType, String.fromUTF8! props.sym_name.value, params⟩,
    "entry", insts, ← reverseValue ctx values result⟩

/-- Decode the supported MLIR fragment. This is not a verifier of `LowersModule`:
round-trip guarantees apply to graphs satisfying that specification. -/
def reverseModule (ctx : WfIRContext OpCode) (root : OperationPtr) :
    Except String ResolvedModule := do
  if root.getOpType! ctx.raw != ofDialect OpCode Builtin.module then throw "expected builtin.module"
  let block ← reverseBody ctx root
  return ⟨← (← reverseOps ctx block).mapM (reverseFunction ctx)⟩

def equivalent_modulo_renaming (ctx1 : WfIRContext OpCode) (root1 : OperationPtr)
    (ctx2 : WfIRContext OpCode) (root2 : OperationPtr) : Prop :=
  RootedIso ctx1 root1 ctx2 root2

/-! Totality follows from reference bounds and freshness of allocated identifiers. -/

section Completeness

set_option maxRecDepth 4000
set_option maxHeartbeats 800000

variable {ctx ctx' ctx'' : WfIRContext OpCode} {block : BlockPtr}

attribute [local simp] StateT.run StateT.bind StateT.get StateT.set StateT.pure StateT.lift
  bind pure get getThe MonadState.get MonadStateOf.get set MonadStateOf.set
  Except.pure Except.bind throw throwThe MonadExceptOf.throw

theorem emit_total (hs : AllocationSafe ctx.raw) (hb : block.InBounds ctx.raw)
    {code : Llvm} {props : propertiesOf code} (insert : Bool)
    (hv : ∀ v ∈ vs, v.InBounds ctx.raw) (hr : ∀ r ∈ rs, r.InBounds ctx.raw)
    (hp : ∀ r ∈ rs, r.getParent! ctx.raw = none) (hn : rs.size ≤ 1) :
    ∃ op ctx', (emit code ts vs rs props block insert).run ctx = .ok (op, ctx') ∧
      AllocationSafe ctx'.raw ∧ ∀ r, r ∉ rs → r.getParent! ctx'.raw = r.getParent! ctx.raw := by
  obtain ⟨raw, op, hc, hs⟩ := hs.createOp_total (ts := ts) (insert := insert) ctx.wellFormed.inBounds code props (fun _ => hb) hv hr hp hn
  let ctx' : WfIRContext OpCode := ⟨raw, by grind [Rewriter.createOp_WellFormed]⟩
  have he := createOp_of_raw (ctx' := ctx') hc
  refine ⟨op, ctx', ?_, hs, by grind⟩
  simp [emit]; simp [ show (if insert then some (InsertPoint.atEnd block) else none).maybe InsertPoint.InBounds ctx.raw by cases insert <;> grind, he]
  rw [ite_eq_left hv, ite_eq_left hr]; rfl

theorem MatchesOp.result_inBounds {code : Llvm} {props : propertiesOf code}
    (h : MatchesOp ctx op code #[ty] vs rs props) : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
  simp only [MatchesOp, Prod.mk.injEq] at h
  have hn : op.getNumResults! ctx.raw = 1 := by simpa [OperationPtr.getResultTypes!.size_eq_getNumResults!] using congrArg Array.size h.2.2.2.1
  grind [OperationPtr.getResult, OpResultPtr.inBounds_def]

theorem lowerValue_total (hs : AllocationSafe ctx.raw) (hb : block.InBounds ctx.raw)
    (hv : ∀ v ∈ results, v.InBounds ctx.raw)
    (hvalid : ValidResolvedValue (block.getNumArguments! ctx.raw) results.size value) :
    ∃ v ctx', (lowerValue block results ty value).run ctx = .ok (v, ctx') ∧
      AllocationSafe ctx'.raw ∧ v.InBounds ctx'.raw ∧ ∀ r : RegionPtr, r.getParent! ctx'.raw = r.getParent! ctx.raw := by
  rcases value with ⟨i | i⟩ | n
  · refine ⟨.blockArgument (block.getArgument i), ctx, ?_, hs, by grind [ValidResolvedValue], fun _ => rfl⟩
    change i < block.getNumArguments! ctx.raw at hvalid
    simp [lowerValue]; rw [ite_eq_left hvalid]; rfl
  · have hi : i < results.size := hvalid; exact ⟨results[i], ctx, by simp [lowerValue, hi], hs, hv _ (by simp), fun _ => rfl⟩
  · cases ty with | int w =>
    obtain ⟨op, c, he, hs, hr⟩ := emit_total (ctx := ctx) (code := .mlir__constant) (vs := #[]) (rs := #[]) (ts := #[lowerType (.int w)])
      (props := { value := .integer (IntegerAttr.ofInt n (.signless w)) }) hs hb true (by simp) (by simp) (by simp) (by simp)
    refine ⟨.opResult (op.getResult 0), c, ?_, hs, (emit_spec he).2.1.result_inBounds, fun r => hr r (by simp)⟩
    simp only [lowerValue, run_bind, run_pure]; exact ⟨op, c, he, rfl⟩

theorem lowerInst_total (hs : AllocationSafe ctx.raw) (hb : block.InBounds ctx.raw) :
    ∃ op ctx', (lowerInst block inst).run ctx = .ok (op, ctx') ∧
      AllocationSafe ctx'.raw ∧ Frame ctx ctx' [] block ∧ ∀ r : RegionPtr, r.getParent! ctx'.raw = r.getParent! ctx.raw := by
  rcases inst with ⟨opc, ty, l, r⟩
  obtain ⟨op, c, he, hs, hr⟩ := emit_total (ctx := ctx) (code := binOpcode opc) (props := default)
    (ts := #[lowerType ty]) (vs := #[]) (rs := #[]) hs hb false (by simp) (by simp) (by simp) (by simp)
  refine ⟨op, c, ?_, hs, (emit_spec he).1, fun r => hr r (by simp)⟩; cases opc <;> exact he

theorem allocate_total {insts : List ResolvedAST} (hs : AllocationSafe ctx.raw) (hb : block.InBounds ctx.raw) :
    ∃ ops ctx', (insts.mapM (lowerInst block)).run ctx = .ok (ops, ctx') ∧
      AllocationSafe ctx'.raw ∧ ∀ r : RegionPtr, r.getParent! ctx'.raw = r.getParent! ctx.raw := by
  induction insts generalizing ctx with
  | nil => exact ⟨[], ctx, by simp, hs, fun _ => rfl⟩
  | cons inst insts ih =>
    obtain ⟨op, c, he, hs, hf, hr⟩ := lowerInst_total (inst := inst) hs hb
    obtain ⟨ops, c', he', hs', hr'⟩ := ih hs (hf.bounds (.block block) hb)
    refine ⟨op :: ops, c', ?_, hs', fun r => (hr' r).trans (hr r)⟩
    simp only [List.mapM_cons, run_bind, run_pure]; exact ⟨op, c, he, ops, c', he', rfl⟩

theorem pushValue_total (hs : AllocationSafe ctx.raw) (ho : op.InBounds ctx.raw) (hv : v.InBounds ctx.raw) :
    ∃ ctx', (pushValue op v).run ctx = .ok ((), ctx') ∧ AllocationSafe ctx'.raw ∧
      ∀ r : RegionPtr, r.getParent! ctx'.raw = r.getParent! ctx.raw := by
  refine ⟨WfRewriter.pushOperand ctx op v ho hv, ?_, hs.pushOperand, ?_⟩
  · simp [pushValue]; rw [dite_eq_left ho, dite_eq_left hv]; rfl
  · intro r; grind [WfRewriter.pushOperand]

theorem insertOp_of_raw (h : Rewriter.insertOp ctx.raw op ip ho hi (by grind) = some ctx'.raw) :
    WfRewriter.insertOp ctx op ip ho hi = some ctx' := by
  unfold WfRewriter.insertOp; split <;> simp_all

theorem attachInst_total (hs : AllocationSafe ctx.raw) (ho : op.InBounds ctx.raw)
    (hb : block.InBounds ctx.raw) (hp : op.getParent! ctx.raw = none) :
    ∃ ctx', (attachInst block op).run ctx = .ok ((), ctx') ∧ AllocationSafe ctx'.raw ∧
      ∀ r : RegionPtr, r.getParent! ctx'.raw = r.getParent! ctx.raw := by
  obtain ⟨raw, hi⟩ := insertOp_total ctx.wellFormed.inBounds ho hb hp
  let c : WfIRContext OpCode := ⟨raw, by grind [Rewriter.insertOp_WellFormed]⟩
  have he := insertOp_of_raw (ctx' := c) hi
  refine ⟨c, ?_, hs.insertOp hi, by grind⟩
  simp [attachInst]; rw [dite_eq_left ho, dite_eq_left hb]; simp [he]

theorem lowerOperand_total {code : Llvm} {props : propertiesOf code}
    (hs : AllocationSafe ctx.raw) (hm : MatchesOp ctx op code ts vs rs props)
    (hb : block.OpChain ctx.raw os) (hv : ∀ v ∈ results, v.InBounds ctx.raw)
    (hvalid : ValidResolvedValue (block.getNumArguments! ctx.raw) results.size value) :
    ∃ v c₁ c₂, (lowerValue block results ty value).run ctx = .ok (v, c₁) ∧
      (pushValue op v).run c₁ = .ok ((), c₂) ∧ AllocationSafe c₂.raw ∧ Frame ctx c₂ [op] block ∧
      MatchesOp c₂ op code ts (vs.push v) rs props ∧ op.getParent! c₂.raw = op.getParent! ctx.raw ∧
      ∃ os', block.OpChain c₂.raw os' ∧ ∀ r : RegionPtr, r.getParent! c₂.raw = r.getParent! ctx.raw := by
  obtain ⟨v, c₁, hl, hs₁, hv₁, hr₁⟩ := lowerValue_total (ty := ty) hs hb.blockInBounds hv hvalid
  have hf := (lowerValue_spec hb hl).1
  obtain ⟨c₂, hp, hs₂, hr₂⟩ := pushValue_total hs₁ (hf.bounds (.operation op) hm.1) hv₁
  obtain ⟨cs, -, hm', hparent, hchain, hf', -⟩ := lowerOperand_sound hm hb hl hp
  exact ⟨v, c₁, c₂, hl, hp, hs₂, hf', hm', hparent, _, hchain, fun r => (hr₂ r).trans (hr₁ r)⟩

theorem wireInst_total (hs : AllocationSafe ctx.raw) (ha : Allocated ctx inst op)
    (hb : block.OpChain ctx.raw os) (hv : ∀ v ∈ results, v.InBounds ctx.raw)
    (hvalid : ValidResolvedInst (block.getNumArguments! ctx.raw) results.size inst) :
    ∃ ctx', (wireInst block results (inst, op)).run ctx = .ok ((), ctx') ∧ AllocationSafe ctx'.raw ∧
      ∀ r : RegionPtr, r.getParent! ctx'.raw = r.getParent! ctx.raw := by
  rcases inst with ⟨opc, ty, lhs, rhs⟩
  obtain ⟨vl, c₁, c₂, hl, hpl, hs₂, hf₂, hm₂, hp₂, os₂, hb₂, hr₂⟩ := lowerOperand_total (ty := ty) hs ha.1 hb hv hvalid.1
  obtain ⟨vr, c₃, c₄, hr, hpr, hs₄, hf₄, hm₄, hp₄, os₄, hb₄, hr₄⟩ := lowerOperand_total (ty := ty) hs₂ hm₂ hb₂
    (fun v hv' => hf₂.bounds (.value v) (hv v hv')) (by simpa [hf₂.numArgs hb.blockInBounds] using hvalid.2)
  obtain ⟨c₅, hi, hs₅, hr₅⟩ := attachInst_total hs₄ hm₄.1 hb₄.blockInBounds (hp₄.trans (hp₂.trans ha.2))
  refine ⟨c₅, ?_, hs₅, fun r => (hr₅ r).trans ((hr₄ r).trans (hr₂ r))⟩
  simp only [wireInst, run_bind]; exact ⟨vl, c₁, hl, (), c₂, hpl, vr, c₃, hr, (), c₄, hpr, hi⟩

theorem wire_total (hs : AllocationSafe ctx.raw) (hb : block.OpChain ctx.raw os)
    (ha : ResolvesList (Ready ctx results) entries ops) (hn : ops.Nodup)
    (hv : ∀ v ∈ results, v.InBounds ctx.raw)
    (hvalid : ∀ e ∈ entries, ValidResolvedInst (block.getNumArguments! ctx.raw) results.size e.1) :
    ∃ ctx', ((entries.map Prod.fst).zip ops |>.forM (wireInst block results)).run ctx = .ok ((), ctx') ∧
      AllocationSafe ctx'.raw ∧ ∀ r : RegionPtr, r.getParent! ctx'.raw = r.getParent! ctx.raw := by
  induction entries generalizing ctx ops os with
  | nil => cases ha; exact ⟨ctx, by simp, hs, fun _ => rfl⟩
  | cons e entries ih =>
    cases ha with | cons he ha =>
    obtain ⟨hno, hnt⟩ := List.nodup_cons.mp hn; obtain ⟨c, hw, hs', hr⟩ := wireInst_total hs he.1 hb hv (hvalid e (by simp))
    obtain ⟨tile, -, hc, hf, -⟩ := wireInst_sound he.1 hb he.2 hw
    obtain ⟨c', hw', hs'', hr'⟩ := ih hs' hc
      (resolvesList_mono ha fun _ p hp he => ⟨he.1.frame hf (by grind), he.2⟩) hnt
      (fun v hv' => hf.bounds (.value v) (hv v hv')) (fun e he => by simpa [hf.numArgs hb.blockInBounds] using hvalid e (by simp [he]))
    refine ⟨c', ?_, hs'', fun r => (hr' r).trans (hr r)⟩; simp only [List.map_cons, List.zip_cons_cons, List.forM_eq_forM, List.forM_cons, run_bind]; exact ⟨(), c, hw, hw'⟩

theorem allocated_result_inBounds (ha : Allocated ctx inst op) :
    (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
  cases inst; exact ha.1.result_inBounds

theorem allocated_results_inBounds (ha : ResolvesList (Allocated ctx) insts ops) :
    ∀ v ∈ ops.toArray.map (fun op => ValuePtr.opResult (op.getResult 0)), v.InBounds ctx.raw := by
  intro v hv; obtain ⟨op, hop, rfl⟩ := Array.mem_map.mp hv
  obtain ⟨_, h⟩ := ha.mem_right (by simpa using hop); exact allocated_result_inBounds h

theorem lowerInsts_total (hs : AllocationSafe ctx.raw) (hb : block.OpChain ctx.raw os)
    (hvalid : ∀ inst ∈ insts, ValidResolvedInst (block.getNumArguments! ctx.raw) insts.length inst) :
    ∃ results ctx', (lowerInsts block insts).run ctx = .ok (results, ctx') ∧ AllocationSafe ctx'.raw ∧
      (∀ v ∈ results, v.InBounds ctx'.raw) ∧ ∀ r : RegionPtr, r.getParent! ctx'.raw = r.getParent! ctx.raw := by
  obtain ⟨ops, c₁, ha, hs₁, hr₁⟩ := allocate_total (insts := insts) hs hb.blockInBounds; obtain ⟨hf, hal, hd, hn, hc⟩ := allocate_sound ha
  let results := ops.toArray.map fun op => ValuePtr.opResult (op.getResult 0)
  have hv : ∀ v ∈ results, v.InBounds c₁.raw := allocated_results_inBounds hal
  have hready : ResolvesList (Ready c₁ results) insts.zipIdx ops := resolvesList_mono (hal.zipIdx []) fun _ _ _ ⟨h₁, h₂⟩ => ⟨h₁, by simp at h₂; simp [results, h₂]⟩
  obtain ⟨c₂, hw, hs₂, hr₂⟩ := wire_total hs₁ (hc os hb)
    hready hd hv
    (by simpa [results, hal.length, hf.numArgs hb.blockInBounds] using fun e (he : e ∈ insts.zipIdx) => hvalid e.1 (by simpa only [List.zipIdx_map_fst] using List.mem_map_of_mem (f := Prod.fst) he))
  have hw' : ((insts.zip ops).forM (wireInst block results)).run c₁ = .ok ((), c₂) := by simpa only [List.zipIdx_map_fst] using hw
  obtain ⟨hf', -, -, hc'⟩ := wire_sound (hc os hb) hready hd hw
  refine ⟨results, c₂, ?_, hs₂, fun v hv' => hf'.bounds (.value v) (hv v hv'), fun r => (hr₂ r).trans (hr₁ r)⟩; simp only [lowerInsts, run_bind, run_pure]; exact ⟨ops, c₁, ha, (), c₂, hw', rfl⟩

theorem createRegion_of_raw (h : Rewriter.createRegion ctx.raw = some (ctx'.raw, r)) :
    WfRewriter.createRegion ctx = some (ctx', r) := by
  unfold WfRewriter.createRegion; split <;> simp_all

theorem regionParent_insertBlock {raw raw' : IRContext OpCode} {r : RegionPtr}
    {b : BlockPtr} {ip : BlockInsertPoint} {hb : b.InBounds raw} {hi : ip.InBounds raw} {hx : raw.FieldsInBounds}
    (h : Rewriter.insertBlock raw b ip hb hi hx = some raw') :
    r.getParent! raw' = r.getParent! raw := by
  unfold Rewriter.insertBlock at h; split at h <;> grind

theorem regionParent_createBlock {raw raw' : IRContext OpCode} {r : RegionPtr}
    {b : BlockPtr} {ip : Option BlockInsertPoint} {ts : Array TypeAttr} {hx : raw.FieldsInBounds} {hi : ip.maybe BlockInsertPoint.InBounds raw}
    (h : Rewriter.createBlock raw ts ip hx hi = some (raw', b)) :
    r.getParent! raw' = r.getParent! raw := by
  unfold Rewriter.createBlock at h
  simp only [Option.bind_eq_bind, Option.bind] at h
  split at h <;> try contradiction
  split at h
  · split at h <;> try contradiction
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩
    grind [regionParent_insertBlock]
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩; grind

theorem createBody_total (hs : AllocationSafe ctx.raw) :
    ∃ region body ctx', (createBody ts).run ctx = .ok ((region, body), ctx') ∧ AllocationSafe ctx'.raw ∧
      region.getParent! ctx'.raw = none := by
  obtain ⟨raw₁, r, hr, hs₁⟩ := hs.allocateRegion
  let c₁ : WfIRContext OpCode := ⟨raw₁, by grind [IRContext.wellFormed_Rewriter_createRegion]⟩
  obtain ⟨raw₂, b, hb, hs₂⟩ := hs₁.createBlock_total (ts := ts) (by grind) (show r.InBounds raw₁ by grind)
  let c₂ : WfIRContext OpCode := ⟨raw₂, by have := c₁.wellFormed; grind [Rewriter.createBlock_WellFormed]⟩
  have hr' := createRegion_of_raw (ctx' := c₁) hr
  have hb' := createBlock_of_raw (ctx := c₁) (ctx' := c₂) hb
  refine ⟨r, b, c₂, ?_, hs₂, (regionParent_createBlock hb).trans (by grind)⟩
  simp [createBody, hr']; rw [dite_eq_left (show (BlockInsertPoint.atEnd r).InBounds c₁.raw by grind)]; simp [hb']

theorem lowerFunction_total (hs : AllocationSafe ctx.raw) (hb : moduleBlock.OpChain ctx.raw os)
    (hvalid : ValidResolvedFunction f) :
    ∃ op ctx', (lowerFunction moduleBlock f).run ctx = .ok (op, ctx') ∧ AllocationSafe ctx'.raw := by
  obtain ⟨region, body, c₁, hcreate, hs₁, hparent⟩ := createBody_total (ts := f.header.params.toArray.map (lowerType ·.ty)) hs
  obtain ⟨hF₁, -, hblocks, hchain, htypes⟩ := createBody_spec (block := body) hcreate; have hbin : body.InBounds c₁.raw := hchain.blockInBounds
  have hnum : body.getNumArguments! c₁.raw = f.header.params.length := by simpa [← BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] using congrArg Array.size htypes
  obtain ⟨results, c₂, hi, hs₂, hv, hr₂⟩ := lowerInsts_total hs₁ hchain (by simpa [hnum] using hvalid.1); obtain ⟨hF₂, hsize, -, tiles, -, hci⟩ := lowerInsts_sound hchain hi
  obtain ⟨v, c₃, hval, hs₃, hvin, hr₃⟩ := lowerValue_total (ty := f.header.retType) hs₂ hci.blockInBounds hv (by simpa [hsize, hF₂.numArgs hbin, hnum] using hvalid.2)
  have hF₃ := (lowerValue_spec hci hval).1; obtain ⟨ret, c₄, hret, hs₄, hr₄⟩ := emit_total (code := .return) (props := ()) (ts := #[]) (vs := #[v]) (rs := #[]) hs₃ (hF₃.bounds (.block body) hci.blockInBounds) true (by simpa) (by simp) (by simp) (by simp)
  have hF₄ := (emit_spec hret).1; have hF := hF₁.trans (hF₂.trans (hF₃.trans hF₄)); have hdet : region.getParent! c₄.raw = none := (hr₄ region (by simp)).trans ((hr₃ region).trans ((hr₂ region).trans hparent))
  obtain ⟨op, c₅, hfunc, hs₅, -⟩ := emit_total (code := .func) (ts := #[]) (vs := #[]) (rs := #[region]) (props := { sym_name := ⟨f.header.name.toUTF8⟩, function_type := { inputs := (f.header.params.toArray.map (lowerType ·.ty)).map Subtype.val, outputs := #[(lowerType f.header.retType).val] }, extra := defaultFuncExtra })
    hs₄ (hF.bounds (.block moduleBlock) hb.blockInBounds) true (by simp) (by simpa using (hF₂.trans (hF₃.trans hF₄)).bounds (.region region) hblocks.inBounds) (by simpa using hdet) (by simp)
  refine ⟨op, c₅, ?_, hs₅⟩; simp only [lowerFunction, run_bind]; exact ⟨(region, body), c₁, hcreate, results, c₂, hi, v, c₃, hval, ret, c₄, hret, hfunc⟩

theorem lowerFunctions_total (hs : AllocationSafe ctx.raw) (hb : block.OpChain ctx.raw os)
    (hvalid : ∀ f ∈ fs, ValidResolvedFunction f) :
    ∃ ctx', (lowerFunctions block fs).run ctx = .ok ((), ctx') ∧ AllocationSafe ctx'.raw := by
  induction fs generalizing ctx os with
  | nil => exact ⟨ctx, by simp [lowerFunctions], hs⟩
  | cons f fs ih =>
    obtain ⟨op, c, he, hs'⟩ := lowerFunction_total hs hb (hvalid f (by simp))
    obtain ⟨-, -, hc⟩ := lowerFunction_sound hb he
    obtain ⟨c', he', hs''⟩ := ih hs' hc (by simp_all)
    refine ⟨c', ?_, hs''⟩
    simp only [lowerFunctions, List.forM_eq_forM, List.forM_cons, run_bind, run_pure]
    exact ⟨(), c, ⟨op, c, he, rfl⟩, he'⟩

theorem resolvesList_mem_left {R : α → β → Prop} {as : List α} {bs : List β}
    (h : ResolvesList R as bs) (ha : a ∈ as) : ∃ b, R a b := by
  induction h with
  | nil => simp at ha
  | cons hab _ ih => exact (List.mem_cons.mp ha).elim (fun he => ⟨_, he ▸ hab⟩) ih

theorem LowersModule.valid (h : LowersModule ctx m root) : ∀ f ∈ m.funcs, ValidResolvedFunction f := by
  obtain ⟨_, _, _, _, _, _, _, hfs⟩ := h
  intro f hf; obtain ⟨_, hfun⟩ := resolvesList_mem_left hfs hf; exact hfun.1

theorem createModule_allocationSafe : ∃ ctx root, createModule = some (ctx, root) ∧ AllocationSafe ctx.raw := by
  obtain ⟨ctx, root, hc, hs⟩ := createModule_total
  obtain ⟨_, _, hm, -⟩ := createRawModule_sound hc
  refine ⟨WfRewriter.setAttributes ctx root defaultModuleAttrs hm.1, root, by simp [createModule, hc, hm.1], ?_⟩
  exact ⟨fun p hp => hs.operations p ((setAttributes_inBounds (.operation p)).mp hp),
    fun p hp => hs.blocks p ((setAttributes_inBounds (.block p)).mp hp), fun p hp => hs.regions p ((setAttributes_inBounds (.region p)).mp hp)⟩

theorem lowerModule_total (hvalid : ∀ f ∈ m.funcs, ValidResolvedFunction f) :
    ∃ ctx root, lowerModule m = .ok (ctx, root) := by
  obtain ⟨ctx, root, hcreate, hs⟩ := createModule_allocationSafe
  obtain ⟨region, b, hm, hr, hb, -, -⟩ := createModule_sound hcreate
  have hfirst : (root.getRegion! ctx.raw 0).getFirstBlock! ctx.raw = some b := by
    rw [← OperationPtr.getRegions!.getElem!_eq_getRegion!, show root.getRegions! ctx.raw = #[region] by grind [MatchesOp]]
    simpa using hr.first
  obtain ⟨ctx', hfs, -⟩ := lowerFunctions_total hs hb hvalid
  exact ⟨ctx', root, by simp [lowerModule, hcreate, hfirst, show lowerFunctions b m.funcs ctx = .ok ((), ctx') from hfs]⟩

end Completeness

/-! Two witnesses of the same module specify the same rooted graph, up to pointer renaming. -/

section CompletenessIsomorphism

set_option maxRecDepth 4000
set_option maxHeartbeats 800000
variable {ctx₁ ctx₂ : WfIRContext OpCode}
variable {D : Type} [HasOpInfo D] [HasDialect OpCode D]
variable {code : D} {props : propertiesOf code}

theorem MatchesOp.properties_eq (h₁ : MatchesOp ctx₁ o₁ code ts₁ vs₁ rs₁ props as₁)
    (h₂ : MatchesOp ctx₂ o₂ code ts₂ vs₂ rs₂ props as₂) :
    ∀ c : OpCode, o₂.getProperties! ctx₂.raw c = o₁.getProperties! ctx₁.raw c := by
  simp only [MatchesOp, Prod.mk.injEq] at *
  intro c
  unfold OperationPtr.getOpType! at h₁ h₂
  unfold OperationPtr.getProperties! at *
  grind [HasDialect.ofDialectProperties_toDialectProperties]

/-- The observable fields of a pair of corresponding operations. -/
def SameFields (ctx₁ ctx₂ : WfIRContext OpCode) (φ : OperationPtr → OperationPtr)
    (β : BlockPtr → BlockPtr) (o₁ o₂ : OperationPtr) : Prop :=
  (∀ c : OpCode, o₂.getProperties! ctx₂.raw c = o₁.getProperties! ctx₁.raw c) ∧
  (o₂.getOpType! ctx₂.raw, o₂.getResultTypes! ctx₂.raw, o₂.getSuccessors! ctx₂.raw,
    o₂.getAttributes! ctx₂.raw, o₂.getOperands! ctx₂.raw, (o₂.getRegions! ctx₂.raw).size) =
  (o₁.getOpType! ctx₁.raw, o₁.getResultTypes! ctx₁.raw, (o₁.getSuccessors! ctx₁.raw).map β,
    o₁.getAttributes! ctx₁.raw, (o₁.getOperands! ctx₁.raw).map (renameValue φ β), (o₁.getRegions! ctx₁.raw).size)

theorem MatchesOp.fields (h₁ : MatchesOp ctx₁ o₁ code ts vs₁ rs₁ props attrs)
    (h₂ : MatchesOp ctx₂ o₂ code ts vs₂ rs₂ props attrs)
    (hv : vs₂ = vs₁.map (renameValue φ β)) (hr : rs₂.size = rs₁.size) :
    SameFields ctx₁ ctx₂ φ β o₁ o₂ := by
  refine ⟨h₁.properties_eq h₂, ?_⟩
  have hs (ctx : WfIRContext OpCode) (o : OperationPtr)
      (h : o.getNumSuccessors! ctx.raw = 0) : o.getSuccessors! ctx.raw = #[] :=
    Array.eq_empty_iff_size_eq_zero.mpr ((OperationPtr.getSuccessors!.size_eq_getNumSuccessors!).trans h)
  simp only [MatchesOp, Prod.mk.injEq] at *
  simp only [hs ctx₁ o₁ (by grind), hs ctx₂ o₂ (by grind), Array.map_empty]
  grind

def literalCount : ResolvedValue → Nat
  | .ref _ => 0
  | .intConst _ => 1

def instructionSize : ResolvedAST → Nat
  | .bin _ _ lhs rhs => literalCount lhs + literalCount rhs + 1

theorem OperandTile.length (h : OperandTile ctx values ty value v cs) : cs.length = literalCount value := by
  cases value with
  | ref => simp_all [OperandTile, literalCount]
  | intConst => cases ty; obtain ⟨c, rfl, -⟩ := h; rfl

theorem LowersInstTile.length {id : ValueId} (h : LowersInstTile ctx values id inst tile) : tile.length = instructionSize inst := by
  cases inst; obtain ⟨_, _, _, _, _, rfl, hl, hr, -⟩ := h
  simp [instructionSize, hl.length, hr.length, Nat.add_assoc]

theorem LowersInstTile.definition_map {id : ValueId} (h₁ : LowersInstTile ctx₁ values₁ id inst tile₁)
    (h₂ : LowersInstTile ctx₂ values₂ id inst tile₂) (hm : tile₁.map φ = tile₂)
    (hv₁ : values₁ id = some v₁) (hv₂ : values₂ id = some v₂) : renameValue φ β v₁ = v₂ := by
  cases inst; obtain ⟨vl₁, vr₁, cl₁, cr₁, o₁, rfl, hl₁, hr₁, hd₁, -⟩ := h₁
  obtain ⟨vl₂, vr₂, cl₂, cr₂, o₂, rfl, hl₂, hr₂, hd₂, -⟩ := h₂
  have hh := (List.append_inj' (s₁ := cl₁.map φ ++ cr₁.map φ) (s₂ := cl₂ ++ cr₂)
    (t₁ := [φ o₁]) (t₂ := [o₂]) (by simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc] using hm) rfl).2
  have ho : φ o₁ = o₂ := by simpa using hh
  obtain rfl : v₁ = .opResult (o₁.getResult 0) := Option.some.inj (hv₁.symm.trans hd₁)
  obtain rfl : v₂ = .opResult (o₂.getResult 0) := Option.some.inj (hv₂.symm.trans hd₂)
  simp [renameValue, OperationPtr.getResult, ho]

theorem instTiles_map {entries : List (ResolvedAST × Nat)}
    (h₁ : ResolvesList (fun (inst, i) => LowersInstTile ctx₁ values₁ (.inst i) inst) entries tiles₁)
    (h₂ : ResolvesList (fun (inst, i) => LowersInstTile ctx₂ values₂ (.inst i) inst) entries tiles₂)
    (hm : tiles₁.flatten.map φ = tiles₂.flatten) : tiles₁.map (List.map φ) = tiles₂ := by
  induction h₁ generalizing tiles₂ with
  | nil => cases h₂; rfl
  | cons hh ht ih =>
    cases h₂ with | cons hh' ht' =>
    obtain ⟨he, ht⟩ := List.append_inj (by simpa [List.map_append] using hm) (by simp [hh.length, hh'.length])
    simp [he, ih ht' (by simpa only [List.map_flatten] using ht)]

theorem resolvesList_and_map {R : α → β → Prop} {S : α → γ → Prop} {f : β → γ}
    (h₁ : ResolvesList R as bs) (h₂ : ResolvesList S as (bs.map f)) :
    ResolvesList (fun a b => R a b ∧ S a (f b)) as bs := by
  induction h₁ with
  | nil => exact .nil
  | cons hr ht ih => cases h₂ with | cons hs ht' => exact .cons ⟨hr, hs⟩ (ih ht')

noncomputable def pairRename [Inhabited γ] (pairs : List (α × γ)) (a : α) : γ :=
  Classical.epsilon (fun b => (a, b) ∈ pairs)

theorem pair_left_unique {pairs : List (α × γ)} (hn : (pairs.map Prod.fst).Nodup)
    (h₁ : (a, b) ∈ pairs) (h₂ : (a, b') ∈ pairs) : b = b' := by
  induction pairs generalizing a b b' with
  | nil => simp at h₁
  | cons p ps ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at h₁ h₂
    rcases h₁ with rfl | h₁ <;> rcases h₂ with he | h₂ <;> grind

theorem pairRename_eq [Inhabited γ] {pairs : List (α × γ)}
    (hn : (pairs.map Prod.fst).Nodup) (h : (a, b) ∈ pairs) : pairRename pairs a = b := by
  exact pair_left_unique hn (Classical.epsilon_spec (show ∃ b, (a, b) ∈ pairs from ⟨b, h⟩)) h

theorem OperandTile.correspond
    (h₁ : OperandTile ctx₁ values₁ ty value v₁ cs₁) (h₂ : OperandTile ctx₂ values₂ ty value v₂ cs₂)
    (hm : cs₁.map φ = cs₂) (hvalid : ValidResolvedValue np ni value)
    (hvalues : ∀ id v₁ v₂, ValidResolvedValue np ni (.ref id) →
      values₁ id = some v₁ → values₂ id = some v₂ → renameValue φ β v₁ = v₂) :
    renameValue φ β v₁ = v₂ ∧ ∀ c ∈ cs₁, SameFields ctx₁ ctx₂ φ β c (φ c) := by
  cases value with
  | ref id => obtain ⟨hv₁, rfl⟩ := h₁; obtain ⟨hv₂, rfl⟩ := h₂; exact ⟨hvalues id _ _ hvalid hv₁ hv₂, by simp⟩
  | intConst => cases ty; obtain ⟨c₁, rfl, rfl, hc₁⟩ := h₁; obtain ⟨c₂, rfl, rfl, hc₂⟩ := h₂
                obtain rfl : c₂ = φ c₁ := by simpa using hm.symm
                exact ⟨by simp [renameValue, OperationPtr.getResult], by simpa using hc₁.fields (φ := φ) (β := β) hc₂ (by simp) rfl⟩

theorem LowersInstTile.correspond {id : ValueId}
    (h₁ : LowersInstTile ctx₁ values₁ id inst tile₁) (h₂ : LowersInstTile ctx₂ values₂ id inst tile₂)
    (hm : tile₁.map φ = tile₂) (hvalid : ValidResolvedInst np ni inst)
    (hvalues : ∀ id v₁ v₂, ValidResolvedValue np ni (.ref id) →
      values₁ id = some v₁ → values₂ id = some v₂ → renameValue φ β v₁ = v₂) :
    ∀ o ∈ tile₁, SameFields ctx₁ ctx₂ φ β o (φ o) := by
  rcases inst with ⟨opc, ty, lhs, rhs⟩; obtain ⟨vl₁, vr₁, cl₁, cr₁, o₁, rfl, hl₁, hr₁, -, ho₁⟩ := h₁
  obtain ⟨vl₂, vr₂, cl₂, cr₂, o₂, rfl, hl₂, hr₂, -, ho₂⟩ := h₂
  obtain ⟨hm', ho⟩ := List.append_inj' (s₁ := cl₁.map φ ++ cr₁.map φ) (s₂ := cl₂ ++ cr₂)
    (t₁ := [φ o₁]) (t₂ := [o₂]) (by simpa only [List.map_append, List.map_cons, List.map_nil, List.append_assoc] using hm) rfl
  obtain ⟨hcl, hcr⟩ := List.append_inj hm' (by simp [hl₁.length, hl₂.length])
  obtain ⟨hvl, hfl⟩ := hl₁.correspond hl₂ hcl hvalid.1 hvalues; obtain ⟨hvr, hfr⟩ := hr₁.correspond hr₂ hcr hvalid.2 hvalues
  have hop : φ o₁ = o₂ := by simpa using ho
  have hfo := ho₁.fields (φ := φ) (β := β) ho₂ (by simp [hvl, hvr]) rfl
  intro o ho; simp only [List.mem_append, List.mem_singleton] at ho
  rcases ho with (ho | ho) | rfl <;> first | exact hfl _ ho | exact hfr _ ho | simpa only [hop] using hfo

theorem OperandTile.regions (h : OperandTile ctx values ty value v cs) (hc : c ∈ cs) : c.getRegions! ctx.raw = #[] := by
  cases value with
  | ref => simp_all [OperandTile]
  | intConst =>
    cases ty; obtain ⟨op, rfl, -, hm⟩ := h
    have he : c = op := by simpa using hc
    subst c; grind [MatchesOp]

theorem LowersInstTile.regions {id : ValueId} (h : LowersInstTile ctx values id inst tile) (ho : o ∈ tile) :
    o.getRegions! ctx.raw = #[] := by
  cases inst; obtain ⟨vl, vr, cl, cr, op, rfl, hl, hr, -, hm⟩ := h
  simp only [List.mem_append, List.mem_singleton] at ho
  rcases ho with (ho | ho) | rfl
  · exact hl.regions ho
  · exact hr.regions ho
  · grind [MatchesOp]

theorem MatchesOp.region_parent (h : MatchesOp ctx o code ts vs rs props attrs) (hr : r ∈ rs) :
    r.getParent! ctx.raw = some o := by
  have hm : r ∈ o.getRegions! ctx.raw := by grind [MatchesOp]
  have hi := OperationPtr.getRegions!.mem_iff_exists_index.mp hm
  exact ((ctx.wellFormed.operations o h.1).region_parent r (by have := h.1; grind)).mp hi

/-- Data witnessing the existential layout in `LowersFunctionTiles`. -/
structure FunctionWitness (ctx : WfIRContext OpCode) (f : ResolvedFunction) (op : OperationPtr) where
  region : RegionPtr
  block : BlockPtr
  tiles : List (List OperationPtr)
  constants : List OperationPtr
  ret : OperationPtr
  result : ValuePtr
  values : ValueMap
  valid : ValidResolvedFunction f
  func : MatchesOp ctx op Llvm.func #[] #[] #[region]
    (LLVMFuncProperties.mk ⟨f.header.name.toUTF8⟩
      { inputs := f.header.params.toArray.map (fun p => (lowerType p.ty).val)
        outputs := #[(lowerType f.header.retType).val] } defaultFuncExtra)
  blocks : region.BlockChain ctx.raw #[block]
  args : block.getArgumentTypes! ctx.raw = f.header.params.toArray.map (lowerType ·.ty)
  params : ∀ i, values (.param i) = (block.getArguments! ctx.raw)[i]?
  insts : ResolvesList (fun (inst, i) => LowersInstTile ctx values (.inst i) inst) f.insts.zipIdx tiles
  resultTile : OperandTile ctx values f.header.retType f.result result constants
  returnOp : MatchesOp ctx ret Llvm.return #[] #[result] #[] ()
  chain : block.OpChain ctx.raw (tiles.flatten ++ constants ++ [ret]).toArray

def FunctionWitness.operations (w : FunctionWitness ctx f op) : List OperationPtr :=
  w.tiles.flatten ++ w.constants ++ [w.ret]

theorem LowersFunctionTiles.witness (h : LowersFunctionTiles ctx f op) : Nonempty (FunctionWitness ctx f op) := by
  obtain ⟨hv, r, b, tiles, cs, ret, v, values, hf, hb, ha, hp, hi, hval, hret, hc⟩ := h
  exact ⟨⟨r, b, tiles, cs, ret, v, values, hv, hf, hb, ha, hp, hi, hval, hret, hc⟩⟩

theorem instTiles_length {entries : List (ResolvedAST × Nat)}
    (h₁ : ResolvesList (fun (inst, i) => LowersInstTile ctx₁ values₁ (.inst i) inst) entries tiles₁)
    (h₂ : ResolvesList (fun (inst, i) => LowersInstTile ctx₂ values₂ (.inst i) inst) entries tiles₂) :
    tiles₁.flatten.length = tiles₂.flatten.length := by
  induction h₁ generalizing tiles₂ with
  | nil => cases h₂; rfl
  | cons hh ht ih => cases h₂ with | cons hh' ht' => simpa [hh.length, hh'.length] using ih ht'

theorem FunctionWitness.length_eq (w₁ : FunctionWitness ctx₁ f op₁) (w₂ : FunctionWitness ctx₂ f op₂) :
    w₁.operations.length = w₂.operations.length := by
  simp only [operations, List.length_append, List.length_singleton]
  rw [instTiles_length w₁.insts w₂.insts, w₁.resultTile.length, w₂.resultTile.length]

theorem FunctionWitness.numArgs (w : FunctionWitness ctx f op) : w.block.getNumArguments! ctx.raw = f.header.params.length := by
  simpa [← BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] using congrArg Array.size w.args

theorem FunctionWitness.params_correspond (w₁ : FunctionWitness ctx₁ f op₁) (w₂ : FunctionWitness ctx₂ f op₂)
    (hb : β w₁.block = w₂.block) (hvalid : i < f.header.params.length)
    (h₁ : w₁.values (.param i) = some v₁) (h₂ : w₂.values (.param i) = some v₂) : renameValue φ β v₁ = v₂ := by
  have hi₁ : i < w₁.block.getNumArguments! ctx₁.raw := by simpa [w₁.numArgs] using hvalid
  have hi₂ : i < w₂.block.getNumArguments! ctx₂.raw := by simpa [w₂.numArgs] using hvalid
  rw [w₁.params] at h₁; rw [w₂.params] at h₂
  simp [BlockPtr.getArguments!, hi₁, hi₂] at h₁ h₂
  subst v₁; subst v₂; simp [renameValue, BlockPtr.getArgument, hb]

theorem FunctionWitness.values_correspond {id : ValueId} (w₁ : FunctionWitness ctx₁ f op₁) (w₂ : FunctionWitness ctx₂ f op₂)
    (hm : w₁.tiles.flatten.map φ = w₂.tiles.flatten) (hb : β w₁.block = w₂.block)
    (hvalid : ValidResolvedValue f.header.params.length f.insts.length (.ref id))
    (h₁ : w₁.values id = some v₁) (h₂ : w₂.values id = some v₂) : renameValue φ β v₁ = v₂ := by
  cases id with
  | param i => exact w₁.params_correspond w₂ hb hvalid h₁ h₂
  | inst i =>
    have hi : i < f.insts.length := hvalid
    have ht := instTiles_map w₁.insts w₂.insts hm
    have hboth := resolvesList_and_map w₁.insts (show ResolvesList _ _ (w₁.tiles.map (List.map φ)) from ht.symm ▸ w₂.insts)
    obtain ⟨tile, htile₁, htile₂⟩ := resolvesList_mem_left hboth (show (f.insts[i], i) ∈ f.insts.zipIdx by simp [List.mk_mem_zipIdx_iff_getElem?, hi])
    exact htile₁.definition_map htile₂ rfl h₁ h₂

theorem resolvesList_mem_right {R : α → γ → Prop} {as : List α} {bs : List γ}
    (h : ResolvesList R as bs) (hb : b ∈ bs) : ∃ a, a ∈ as ∧ R a b := by
  induction h with
  | nil => simp at hb
  | cons hab ht ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, by simp, hab⟩
    · obtain ⟨a, ha, hr⟩ := ih hb; exact ⟨a, by simp [ha], hr⟩

theorem FunctionWitness.instruction_fields (w₁ : FunctionWitness ctx₁ f op₁) (w₂ : FunctionWitness ctx₂ f op₂)
    (hm : w₁.tiles.flatten.map φ = w₂.tiles.flatten) (hb : β w₁.block = w₂.block) :
    ∀ o ∈ w₁.tiles.flatten, SameFields ctx₁ ctx₂ φ β o (φ o) := by
  have ht := instTiles_map w₁.insts w₂.insts hm
  have hboth := resolvesList_and_map w₁.insts (show ResolvesList _ _ (w₁.tiles.map (List.map φ)) from ht.symm ▸ w₂.insts)
  intro o ho; obtain ⟨tile, htile, ho⟩ := List.mem_flatten.mp ho
  obtain ⟨e, he, ht₁, ht₂⟩ := resolvesList_mem_right hboth htile
  exact ht₁.correspond ht₂ rfl (w₁.valid.1 e.1 (by simpa only [List.zipIdx_map_fst] using List.mem_map_of_mem (f := Prod.fst) he))
    (fun _ _ _ hv h₁ h₂ => w₁.values_correspond w₂ hm hb hv h₁ h₂) o ho

theorem FunctionWitness.fields (w₁ : FunctionWitness ctx₁ f op₁) (w₂ : FunctionWitness ctx₂ f op₂)
    (hm : w₁.operations.map φ = w₂.operations) (hb : β w₁.block = w₂.block) :
    ∀ o ∈ w₁.operations, SameFields ctx₁ ctx₂ φ β o (φ o) := by
  obtain ⟨hflat, htail⟩ := List.append_inj (s₁ := w₁.tiles.flatten.map φ) (s₂ := w₂.tiles.flatten)
    (t₁ := w₁.constants.map φ ++ [φ w₁.ret]) (t₂ := w₂.constants ++ [w₂.ret]) (by simpa only [operations, List.map_append, List.map_cons, List.map_nil, List.append_assoc] using hm)
    (by simpa only [List.length_map] using instTiles_length w₁.insts w₂.insts)
  obtain ⟨hcs, hret⟩ := List.append_inj htail (by simp [w₁.resultTile.length, w₂.resultTile.length])
  obtain ⟨hv, hconstants⟩ := w₁.resultTile.correspond w₂.resultTile hcs w₁.valid.2
    (fun _ _ _ hv h₁ h₂ => w₁.values_correspond w₂ hflat hb hv h₁ h₂)
  have hr : φ w₁.ret = w₂.ret := by simpa using hret
  intro o ho; simp only [operations, List.mem_append, List.mem_singleton] at ho
  rcases ho with (ho | ho) | rfl <;> first | exact w₁.instruction_fields w₂ hflat hb _ ho | exact hconstants _ ho | simpa only [hr] using w₁.returnOp.fields (φ := φ) (β := β) w₂.returnOp (by simp [hv]) rfl

theorem FunctionWitness.leaf (w : FunctionWitness ctx f op) (ho : o ∈ w.operations) : o.getRegions! ctx.raw = #[] := by
  simp only [operations, List.mem_append, List.mem_singleton] at ho
  rcases ho with (ho | ho) | rfl
  · obtain ⟨tile, ht, ho⟩ := List.mem_flatten.mp ho
    obtain ⟨e, -, htile⟩ := resolvesList_mem_right w.insts ht; exact htile.regions ho
  · exact w.resultTile.regions ho
  · have := w.returnOp; grind [MatchesOp]

/-- A value is defined in a function's operation list or its entry block. -/
def ValueSupported (ops : List OperationPtr) (block : BlockPtr) : ValuePtr → Prop
  | .opResult r => r.op ∈ ops
  | .blockArgument a => a.block = block

theorem LowersInstTile.definition_mem {id : ValueId} (h : LowersInstTile ctx values id inst tile)
    (hv : values id = some v) : ∃ o ∈ tile, v = .opResult (o.getResult 0) := by
  cases inst; obtain ⟨_, _, _, _, o, rfl, _, _, hd, _⟩ := h
  exact ⟨o, by simp, Option.some.inj (hv.symm.trans hd)⟩

theorem resolvesList_mem_left_mem {R : α → γ → Prop} {as : List α} {bs : List γ}
    (h : ResolvesList R as bs) (ha : a ∈ as) : ∃ b ∈ bs, R a b := by
  induction h with
  | nil => simp at ha
  | cons hab ht ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, by simp, hab⟩
    · obtain ⟨b, hb, hr⟩ := ih ha; exact ⟨b, by simp [hb], hr⟩

theorem FunctionWitness.value_supported {id : ValueId} (w : FunctionWitness ctx f op)
    (hv : ValidResolvedValue f.header.params.length f.insts.length (.ref id))
    (he : w.values id = some v) : ValueSupported w.operations w.block v := by
  cases id with
  | param i =>
    rw [w.params] at he; have hi : i < w.block.getNumArguments! ctx.raw := by simpa [w.numArgs, ValidResolvedValue] using hv
    simp [BlockPtr.getArguments!, hi] at he; subst v; rfl
  | inst i =>
    change i < f.insts.length at hv
    obtain ⟨tile, ht, hh⟩ := resolvesList_mem_left_mem w.insts (show (f.insts[i], i) ∈ f.insts.zipIdx by simp [List.mk_mem_zipIdx_iff_getElem?, hv])
    obtain ⟨o, ho, rfl⟩ := hh.definition_mem he
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatten.mpr ⟨tile, ht, ho⟩))

theorem OperandTile.supported (h : OperandTile ctx values ty value v cs)
    (hc : ∀ c ∈ cs, c ∈ ops)
    (hv : ∀ id v, value = .ref id → values id = some v → ValueSupported ops block v) :
    ValueSupported ops block v := by
  cases value with
  | ref id => exact hv id v rfl h.1
  | intConst => cases ty; obtain ⟨c, rfl, rfl, _⟩ := h; exact hc c (by simp)

theorem OperandTile.empty_operands (h : OperandTile ctx values ty value v cs) (hc : c ∈ cs) :
    c.getOperands! ctx.raw = #[] ∧ c.getSuccessors! ctx.raw = #[] := by
  cases value with
  | ref => simp_all [OperandTile]
  | intConst =>
    cases ty; obtain ⟨o, rfl, _, hm⟩ := h; obtain rfl : c = o := by simpa using hc
    have hs : c.getNumSuccessors! ctx.raw = 0 := by grind [MatchesOp]
    exact ⟨by grind [MatchesOp], Array.eq_empty_iff_size_eq_zero.mpr (by simpa using hs)⟩

theorem LowersInstTile.supported_operands {id : ValueId} (h : LowersInstTile ctx values id inst tile)
    (ht : ∀ o ∈ tile, o ∈ ops) (hv : ValidResolvedInst np ni inst)
    (hvalues : ∀ id v, ValidResolvedValue np ni (.ref id) → values id = some v → ValueSupported ops block v)
    (ho : o ∈ tile) : ∀ v ∈ o.getOperands! ctx.raw, ValueSupported ops block v := by
  cases inst; obtain ⟨vl, vr, cl, cr, inst, rfl, hl, hr, _, hm⟩ := h
  have hvl := hl.supported (fun c hc => ht c (by simp [hc])) (fun id v he hh => hvalues id v (he ▸ hv.1) hh)
  have hvr := hr.supported (fun c hc => ht c (by simp [hc])) (fun id v he hh => hvalues id v (he ▸ hv.2) hh)
  simp only [List.mem_append, List.mem_singleton] at ho
  rcases ho with (ho | ho) | rfl
  · simp [(hl.empty_operands ho).1]
  · simp [(hr.empty_operands ho).1]
  · have he : o.getOperands! ctx.raw = #[vl, vr] := by grind [MatchesOp]
    intro v hv; have hv' : v = vl ∨ v = vr := by simpa [he] using hv
    exact hv'.elim (fun h => h ▸ hvl) (fun h => h ▸ hvr)

theorem FunctionWitness.supported_operands (w : FunctionWitness ctx f op) (ho : o ∈ w.operations) :
    ∀ v ∈ o.getOperands! ctx.raw, ValueSupported w.operations w.block v := by
  simp only [operations, List.mem_append, List.mem_singleton] at ho
  rcases ho with (ho | ho) | rfl
  · obtain ⟨tile, ht, ho⟩ := List.mem_flatten.mp ho; obtain ⟨⟨inst, i⟩, hi, hh⟩ := resolvesList_mem_right w.insts ht
    exact hh.supported_operands (fun o ho => by simp only [operations, List.mem_append]; exact .inl (.inl (List.mem_flatten.mpr ⟨tile, ht, ho⟩)))
      (w.valid.1 inst (List.fst_mem_of_mem_zipIdx hi)) (fun _ _ hv he => w.value_supported hv he) ho
  · simp [(w.resultTile.empty_operands ho).1]
  · have hv := w.resultTile.supported (fun c hc => by simp [operations, hc]) (fun id v he hh => w.value_supported (he ▸ w.valid.2) hh)
    have he : w.ret.getOperands! ctx.raw = #[w.result] := by have := w.returnOp; grind [MatchesOp]
    simpa only [he, Array.mem_singleton, forall_eq] using hv

theorem LowersInstTile.empty_successors {id : ValueId} (h : LowersInstTile ctx values id inst tile)
    (ho : o ∈ tile) : o.getSuccessors! ctx.raw = #[] := by
  cases inst; obtain ⟨_, _, _, _, _, rfl, hl, hr, _, hm⟩ := h
  simp only [List.mem_append, List.mem_singleton] at ho
  rcases ho with (ho | ho) | rfl
  · exact (hl.empty_operands ho).2
  · exact (hr.empty_operands ho).2
  · have hs : o.getNumSuccessors! ctx.raw = 0 := by grind [MatchesOp]
    exact Array.eq_empty_iff_size_eq_zero.mpr (by simpa using hs)

theorem FunctionWitness.empty_successors (w : FunctionWitness ctx f op) (ho : o ∈ w.operations) :
    o.getSuccessors! ctx.raw = #[] := by
  simp only [operations, List.mem_append, List.mem_singleton] at ho
  rcases ho with (ho | ho) | rfl
  · obtain ⟨tile, ht, ho⟩ := List.mem_flatten.mp ho
    obtain ⟨_, _, hh⟩ := resolvesList_mem_right w.insts ht; exact hh.empty_successors ho
  · exact (w.resultTile.empty_operands ho).2
  · have hs : w.ret.getNumSuccessors! ctx.raw = 0 := by have := w.returnOp; grind [MatchesOp]
    exact Array.eq_empty_iff_size_eq_zero.mpr (by simpa using hs)

def blockOwner (ctx : WfIRContext OpCode) (b : BlockPtr) : Option OperationPtr :=
  (b.getParent! ctx.raw).bind (fun r => r.getParent! ctx.raw)

/-- The ordered, single-block shape of a specified function. -/
structure FunctionShape (ctx : WfIRContext OpCode) where
  op : OperationPtr
  region : RegionPtr
  block : BlockPtr
  operations : List OperationPtr
  inBounds : op.InBounds ctx.raw
  operands : op.getOperands! ctx.raw = #[]
  successors : op.getSuccessors! ctx.raw = #[]
  supported : ∀ o ∈ operations, ∀ v ∈ o.getOperands! ctx.raw, ValueSupported operations block v
  noSuccessors : ∀ o ∈ operations, o.getSuccessors! ctx.raw = #[]
  opcode : op.getOpType! ctx.raw = ofDialect OpCode Llvm.func
  regions : op.getRegions! ctx.raw = #[region]
  parent : region.getParent! ctx.raw = some op
  blocks : region.BlockChain ctx.raw #[block]
  chain : block.OpChain ctx.raw operations.toArray
  leaves : ∀ o ∈ operations, o.getRegions! ctx.raw = #[]

def FunctionShape.ofWitness {op : OperationPtr} (w : FunctionWitness ctx f op) : FunctionShape ctx where
  op := op
  region := w.region
  block := w.block
  operations := w.operations
  inBounds := w.func.1
  operands := by have := w.func; grind [MatchesOp]
  successors := by
    have hs : op.getNumSuccessors! ctx.raw = 0 := by have := w.func; grind [MatchesOp]
    exact Array.eq_empty_iff_size_eq_zero.mpr (by simpa using hs)
  supported := fun _ h => w.supported_operands h
  noSuccessors := fun _ h => w.empty_successors h
  opcode := by have := w.func; grind [MatchesOp]
  regions := by have := w.func; grind [MatchesOp]
  parent := w.func.region_parent (by simp)
  blocks := w.blocks
  chain := w.chain
  leaves := fun _ h => w.leaf h

theorem FunctionShape.owner (g : FunctionShape ctx) (ho : o ∈ g.operations) : o.getParentOp! ctx.raw = some g.op := by
  apply OperationPtr.getParentOp!_eq_some_iff.mpr
  exact ⟨g.block, g.region, g.chain.opParent (by simpa using ho), g.blocks.opParent (by simp), g.parent⟩

theorem FunctionShape.block_owner (g : FunctionShape ctx) : blockOwner ctx g.block = some g.op := by
  have hb : g.block.getParent! ctx.raw = some g.region := g.blocks.opParent (by simp)
  simp [blockOwner, hb, g.parent]

theorem FunctionShape.nodup (g : FunctionShape ctx) : g.operations.Nodup := by
  simpa using BlockPtr.OpChain_array_toList_Nodup g.chain

structure FunctionPair (ctx₁ ctx₂ : WfIRContext OpCode) where
  left : FunctionShape ctx₁
  right : FunctionShape ctx₂
  length : left.operations.length = right.operations.length
  args : right.block.getArgumentTypes! ctx₂.raw = left.block.getArgumentTypes! ctx₁.raw
  fields : ∀ φ β, SameFields ctx₁ ctx₂ φ β left.op right.op
  body : ∀ φ β, left.operations.map φ = right.operations → β left.block = right.block →
    ∀ o ∈ left.operations, SameFields ctx₁ ctx₂ φ β o (φ o)

theorem functionPair_of_specs (h₁ : LowersFunctionTiles ctx₁ f op₁) (h₂ : LowersFunctionTiles ctx₂ f op₂) :
    ∃ p : FunctionPair ctx₁ ctx₂, p.left.op = op₁ ∧ p.right.op = op₂ := by
  obtain ⟨w₁⟩ := h₁.witness; obtain ⟨w₂⟩ := h₂.witness
  exact ⟨⟨.ofWitness w₁, .ofWitness w₂, w₁.length_eq w₂, w₂.args.trans w₁.args.symm,
    fun φ β => w₁.func.fields w₂.func (by simp) rfl, fun _ _ hm hb => w₁.fields w₂ hm hb⟩, rfl, rfl⟩

theorem functionPairs_of_specs (h₁ : ResolvesList (LowersFunctionTiles ctx₁) fs ops₁)
    (h₂ : ResolvesList (LowersFunctionTiles ctx₂) fs ops₂) :
    ∃ ps : List (FunctionPair ctx₁ ctx₂), ps.map (·.left.op) = ops₁ ∧ ps.map (·.right.op) = ops₂ := by
  induction h₁ generalizing ops₂ with
  | nil => cases h₂; exact ⟨[], rfl, rfl⟩
  | cons hf ht ih =>
    cases h₂ with | cons hf' ht' =>
    obtain ⟨p, hp₁, hp₂⟩ := functionPair_of_specs hf hf'; obtain ⟨ps, hs₁, hs₂⟩ := ih ht'
    exact ⟨p :: ps, by simp [hp₁, hs₁], by simp [hp₂, hs₂]⟩

theorem pair_right_unique {pairs : List (α × γ)} (hn : (pairs.map Prod.snd).Nodup)
    (h₁ : (a, b) ∈ pairs) (h₂ : (a', b) ∈ pairs) : a = a' := by
  induction pairs generalizing a a' b with
  | nil => simp at h₁
  | cons p ps ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.mem_cons] at h₁ h₂
    rcases h₁ with rfl | h₁ <;> rcases h₂ with he | h₂ <;> grind

theorem map_eq_of_zip {as : List α} {bs : List γ} {f : α → γ}
    (hlen : as.length = bs.length) (h : ∀ p ∈ as.zip bs, f p.1 = p.2) : as.map f = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all
  | cons a as ih => cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have ht : ∀ p ∈ as.zip bs, f p.1 = p.2 := fun p hp => h p (by simp only [List.zip_cons_cons, List.mem_cons]; exact .inr hp)
      have hh := h (a, b) (by simp)
      simp only [List.map_cons]; rw [hh, ih (by simpa using hlen) ht]

theorem grouped_nodup {gs : List γ} {root : α} {head : γ → α} {tail : γ → List α}
    {owner : α → Option α} (hr : ∀ g ∈ gs, head g ≠ root ∧ root ∉ tail g)
    (hh : ∀ g ∈ gs, owner (head g) = some root) (ht : ∀ g ∈ gs, ∀ x ∈ tail g, owner x = some (head g))
    (hn : (gs.map head).Nodup) (hd : ∀ g ∈ gs, (tail g).Nodup) :
    (root :: gs.flatMap (fun g => head g :: tail g)).Nodup := by
  have hnr : ∀ g ∈ gs, head g ≠ root := fun g hg => (hr g hg).1
  refine List.nodup_cons.mpr ⟨?_, ?_⟩
  · simp only [List.mem_flatMap, List.mem_cons]; rintro ⟨g, hg, he | he⟩ <;> grind
  · apply List.pairwise_flatMap.mpr; refine ⟨?_, ?_⟩
    · intro g hg; apply List.nodup_cons.mpr; exact ⟨by intro he; have := ht g hg _ he; have := hh g hg; grind, hd g hg⟩
    · apply List.Pairwise.imp_of_mem (R := fun g g' => head g ≠ head g') _ (List.pairwise_map.mp hn)
      intro g g' hg hg' hne x hx y hy; simp only [List.mem_cons] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy <;> grind

structure ModulePair (ctx₁ ctx₂ : WfIRContext OpCode) (root₁ root₂ : OperationPtr) where
  region₁ : RegionPtr
  region₂ : RegionPtr
  block₁ : BlockPtr
  block₂ : BlockPtr
  functions : List (FunctionPair ctx₁ ctx₂)
  module₁ : MatchesOp ctx₁ root₁ Builtin.module #[] #[] #[region₁] default defaultModuleAttrs
  module₂ : MatchesOp ctx₂ root₂ Builtin.module #[] #[] #[region₂] default defaultModuleAttrs
  blocks₁ : region₁.BlockChain ctx₁.raw #[block₁]
  blocks₂ : region₂.BlockChain ctx₂.raw #[block₂]
  chain₁ : block₁.OpChain ctx₁.raw (functions.map (·.left.op)).toArray
  chain₂ : block₂.OpChain ctx₂.raw (functions.map (·.right.op)).toArray
  args₁ : block₁.getArgumentTypes! ctx₁.raw = #[]
  args₂ : block₂.getArgumentTypes! ctx₂.raw = #[]

theorem modulePair_of_specs (h₁ : LowersModule ctx₁ m root₁) (h₂ : LowersModule ctx₂ m root₂) :
    Nonempty (ModulePair ctx₁ ctx₂ root₁ root₂) := by
  obtain ⟨r₁, b₁, fs₁, hm₁, hb₁, hc₁, ha₁, hf₁⟩ := h₁
  obtain ⟨r₂, b₂, fs₂, hm₂, hb₂, hc₂, ha₂, hf₂⟩ := h₂
  obtain ⟨ps, hps₁, hps₂⟩ := functionPairs_of_specs hf₁ hf₂
  exact ⟨⟨r₁, r₂, b₁, b₂, ps, hm₁, hm₂, hb₁, hb₂, by simpa only [hps₁] using hc₁,
    by simpa only [hps₂] using hc₂, ha₁, ha₂⟩⟩

def FunctionPair.operationPairs (p : FunctionPair ctx₁ ctx₂) : List (OperationPtr × OperationPtr) :=
  (p.left.op, p.right.op) :: p.left.operations.zip p.right.operations

def ModulePair.operationPairs (g : ModulePair ctx₁ ctx₂ root₁ root₂) : List (OperationPtr × OperationPtr) :=
  (root₁, root₂) :: g.functions.flatMap (·.operationPairs)

def ModulePair.blockPairs (g : ModulePair ctx₁ ctx₂ root₁ root₂) : List (BlockPtr × BlockPtr) :=
  (g.block₁, g.block₂) :: g.functions.map (fun p => (p.left.block, p.right.block))

theorem FunctionPair.operationPairs_left (p : FunctionPair ctx₁ ctx₂) :
    p.operationPairs.map Prod.fst = p.left.op :: p.left.operations := by
  simp only [operationPairs, List.map_cons, List.map_fst_zip (Nat.le_of_eq p.length)]

theorem FunctionPair.operationPairs_right (p : FunctionPair ctx₁ ctx₂) :
    p.operationPairs.map Prod.snd = p.right.op :: p.right.operations := by
  simp only [operationPairs, List.map_cons, List.map_snd_zip (Nat.le_of_eq p.length.symm)]

theorem ModulePair.operations_left (g : ModulePair ctx₁ ctx₂ root₁ root₂) :
    g.operationPairs.map Prod.fst = root₁ :: g.functions.flatMap (fun p => p.left.op :: p.left.operations) := by
  simp [operationPairs, List.map_flatMap, FunctionPair.operationPairs_left]

theorem ModulePair.operations_right (g : ModulePair ctx₁ ctx₂ root₁ root₂) :
    g.operationPairs.map Prod.snd = root₂ :: g.functions.flatMap (fun p => p.right.op :: p.right.operations) := by
  simp [operationPairs, List.map_flatMap, FunctionPair.operationPairs_right]

theorem ModulePair.function_owner₁ (g : ModulePair ctx₁ ctx₂ root₁ root₂) (hp : p ∈ g.functions) :
    p.left.op.getParentOp! ctx₁.raw = some root₁ := by
  apply OperationPtr.getParentOp!_eq_some_iff.mpr
  exact ⟨g.block₁, g.region₁, g.chain₁.opParent (by simpa using List.mem_map_of_mem (f := fun p => p.left.op) hp),
    g.blocks₁.opParent (by simp), g.module₁.region_parent (by simp)⟩

theorem ModulePair.function_owner₂ (g : ModulePair ctx₁ ctx₂ root₁ root₂) (hp : p ∈ g.functions) :
    p.right.op.getParentOp! ctx₂.raw = some root₂ := by
  apply OperationPtr.getParentOp!_eq_some_iff.mpr
  exact ⟨g.block₂, g.region₂, g.chain₂.opParent (by simpa using List.mem_map_of_mem (f := fun p => p.right.op) hp),
    g.blocks₂.opParent (by simp), g.module₂.region_parent (by simp)⟩

theorem FunctionShape.distinct_module (g : FunctionShape ctx) (hm : MatchesOp ctx root Builtin.module #[] #[] #[r] default defaultModuleAttrs) :
    g.op ≠ root ∧ root ∉ g.operations := by
  have hn : g.op ≠ root := by have := g.opcode; simp only [MatchesOp, Prod.mk.injEq] at hm; intro h; subst root; cases hm.2.2.1.symm.trans this
  exact ⟨hn, fun h => by have := g.leaves root h; grind [MatchesOp]⟩

theorem ModulePair.operations_left_nodup (g : ModulePair ctx₁ ctx₂ root₁ root₂) : (g.operationPairs.map Prod.fst).Nodup := by
  rw [g.operations_left]
  exact grouped_nodup (fun p _ => p.left.distinct_module g.module₁) (fun p hp => g.function_owner₁ hp) (fun p _ _ ho => p.left.owner ho)
    (by simpa using BlockPtr.OpChain_array_toList_Nodup g.chain₁) (fun p _ => p.left.nodup)

theorem ModulePair.operations_right_nodup (g : ModulePair ctx₁ ctx₂ root₁ root₂) : (g.operationPairs.map Prod.snd).Nodup := by
  rw [g.operations_right]
  exact grouped_nodup (fun p _ => p.right.distinct_module g.module₂) (fun p hp => g.function_owner₂ hp) (fun p _ _ ho => p.right.owner ho)
    (by simpa using BlockPtr.OpChain_array_toList_Nodup g.chain₂) (fun p _ => p.right.nodup)

theorem nodup_map_of {as : List α} {f : α → γ} {g : α → δ} (hn : (as.map f).Nodup)
    (h : ∀ a ∈ as, ∀ b ∈ as, g a = g b → f a = f b) : (as.map g).Nodup := by
  apply List.pairwise_map.mpr
  apply (List.pairwise_map.mp hn).imp_of_mem
  intro a b ha hb hne he; exact hne (h a ha b hb he)

theorem ModulePair.blocks_left_nodup (g : ModulePair ctx₁ ctx₂ root₁ root₂) : (g.blockPairs.map Prod.fst).Nodup := by
  have hn : (g.functions.map (·.left.op)).Nodup := by simpa using BlockPtr.OpChain_array_toList_Nodup g.chain₁
  have hbn := nodup_map_of (g := fun p => p.left.block) hn (fun p _ q _ he => by have := p.left.block_owner; have := q.left.block_owner; grind)
  simp only [blockPairs, List.map_cons, List.map_map]; apply List.nodup_cons.mpr; refine ⟨?_, hbn⟩
  rintro he; obtain ⟨p, hp, he⟩ := List.mem_map.mp he
  have hb : blockOwner ctx₁ g.block₁ = some root₁ := by
    have hb : g.block₁.getParent! ctx₁.raw = some g.region₁ := g.blocks₁.opParent (by simp)
    have hr : g.region₁.getParent! ctx₁.raw = some root₁ := g.module₁.region_parent (by simp)
    simp [blockOwner, hb, hr]
  have := p.left.block_owner; have := (p.left.distinct_module g.module₁).1; grind

theorem list_mapM_some {f : α → Option β} {g : α → β} {xs : List α}
    (h : ∀ x ∈ xs, f x = some (g x)) : xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp_all [List.mapM_cons]

theorem array_mapM_some {f : α → Option β} {g : α → β} {xs : Array α}
    (h : ∀ x ∈ xs, f x = some (g x)) : xs.mapM f = some (xs.map g) := by
  rw [Array.mapM_eq_mapM_toList, list_mapM_some (by simpa using h)]
  simp [← List.map_toArray]

theorem lookup_mem [BEq α] [LawfulBEq α] {ps : List (α × β)}
    (h : ps.lookup a = some b) : (a, b) ∈ ps := by
  obtain ⟨l₁, l₂, rfl, _⟩ := List.lookup_eq_some_iff.mp h
  simp

theorem lookup_of_mem [BEq α] [LawfulBEq α] {ps : List (α × β)}
    (hn : (ps.map Prod.fst).Nodup) (h : (a, b) ∈ ps) : ps.lookup a = some b := by
  induction ps with
  | nil => simp at h
  | cons p ps ih =>
    rcases p with ⟨x, y⟩; simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with he | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he; simp
    · have hn' : a ≠ x := by intro he; exact hn.1 (he ▸ List.mem_map_of_mem (f := Prod.fst) h)
      simp only [List.lookup_cons]; cases he : a == x with
      | false => exact ih hn.2 h
      | true => exact False.elim (hn' (eq_of_beq he))

noncomputable def ModulePair.opRename (g : ModulePair ctx₁ ctx₂ root₁ root₂) : OperationPtr → OperationPtr :=
  pairRename g.operationPairs

noncomputable def ModulePair.blockRename (g : ModulePair ctx₁ ctx₂ root₁ root₂) : BlockPtr → BlockPtr :=
  pairRename g.blockPairs

theorem ModulePair.rename_root (g : ModulePair ctx₁ ctx₂ root₁ root₂) : g.opRename root₁ = root₂ :=
  pairRename_eq g.operations_left_nodup (by simp [operationPairs])

theorem ModulePair.rename_function (g : ModulePair ctx₁ ctx₂ root₁ root₂) (hp : p ∈ g.functions) :
    g.opRename p.left.op = p.right.op := by
  apply pairRename_eq g.operations_left_nodup
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨p, hp, List.mem_cons_self⟩)

theorem ModulePair.rename_body (g : ModulePair ctx₁ ctx₂ root₁ root₂) (hp : p ∈ g.functions) :
    p.left.operations.map g.opRename = p.right.operations := by
  apply map_eq_of_zip p.length; intro pair hpair
  apply pairRename_eq g.operations_left_nodup
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨p, hp, List.mem_cons_of_mem _ hpair⟩)

theorem ModulePair.rename_moduleBlock (g : ModulePair ctx₁ ctx₂ root₁ root₂) : g.blockRename g.block₁ = g.block₂ :=
  pairRename_eq g.blocks_left_nodup (by simp [blockPairs])

theorem ModulePair.rename_block (g : ModulePair ctx₁ ctx₂ root₁ root₂) (hp : p ∈ g.functions) :
    g.blockRename p.left.block = p.right.block := by
  apply pairRename_eq g.blocks_left_nodup
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, hp, rfl⟩)

theorem ModulePair.rename_functions (g : ModulePair ctx₁ ctx₂ root₁ root₂) :
    (g.functions.map (·.left.op)).map g.opRename = g.functions.map (·.right.op) := by
  simp only [List.map_map]; apply List.map_congr_left; intro p hp; exact g.rename_function hp

theorem MatchesOp.regions_eq (h : MatchesOp ctx o code ts vs rs props attrs) : o.getRegions! ctx.raw = rs := by grind [MatchesOp]

def ModulePair.regionPairs (g : ModulePair ctx₁ ctx₂ root₁ root₂) : List (RegionPtr × RegionPtr) :=
  (g.region₁, g.region₂) :: g.functions.map (fun p => (p.left.region, p.right.region))

theorem ModulePair.blocks_right_nodup (g : ModulePair ctx₁ ctx₂ root₁ root₂) : (g.blockPairs.map Prod.snd).Nodup := by
  have hn : (g.functions.map (·.right.op)).Nodup := by simpa using BlockPtr.OpChain_array_toList_Nodup g.chain₂
  have hbn := nodup_map_of (g := fun p => p.right.block) hn (fun p _ q _ he => by have := p.right.block_owner; have := q.right.block_owner; grind)
  simp only [blockPairs, List.map_cons, List.map_map]; apply List.nodup_cons.mpr; refine ⟨?_, hbn⟩
  rintro he; obtain ⟨p, hp, he⟩ := List.mem_map.mp he
  have hb : blockOwner ctx₂ g.block₂ = some root₂ := by
    have hb : g.block₂.getParent! ctx₂.raw = some g.region₂ := g.blocks₂.opParent (by simp)
    have hr : g.region₂.getParent! ctx₂.raw = some root₂ := g.module₂.region_parent (by simp)
    simp [blockOwner, hb, hr]
  have := p.right.block_owner; have := (p.right.distinct_module g.module₂).1; grind

theorem ModulePair.regions_left_nodup (g : ModulePair ctx₁ ctx₂ root₁ root₂) : (g.regionPairs.map Prod.fst).Nodup := by
  have hn : (g.functions.map (·.left.op)).Nodup := by simpa using BlockPtr.OpChain_array_toList_Nodup g.chain₁
  have hbn := nodup_map_of (g := fun p => p.left.region) hn (fun p _ q _ he => by have := p.left.parent; have := q.left.parent; grind)
  simp only [regionPairs, List.map_cons, List.map_map]; apply List.nodup_cons.mpr; refine ⟨?_, hbn⟩
  rintro he; obtain ⟨p, hp, he⟩ := List.mem_map.mp he
  have := g.module₁.region_parent (show g.region₁ ∈ #[g.region₁] by simp)
  have := p.left.parent; have := (p.left.distinct_module g.module₁).1; grind

theorem ModulePair.regions_right_nodup (g : ModulePair ctx₁ ctx₂ root₁ root₂) : (g.regionPairs.map Prod.snd).Nodup := by
  have hn : (g.functions.map (·.right.op)).Nodup := by simpa using BlockPtr.OpChain_array_toList_Nodup g.chain₂
  have hbn := nodup_map_of (g := fun p => p.right.region) hn (fun p _ q _ he => by have := p.right.parent; have := q.right.parent; grind)
  simp only [regionPairs, List.map_cons, List.map_map]; apply List.nodup_cons.mpr; refine ⟨?_, hbn⟩
  rintro he; obtain ⟨p, hp, he⟩ := List.mem_map.mp he
  have := g.module₂.region_parent (show g.region₂ ∈ #[g.region₂] by simp)
  have := p.right.parent; have := (p.right.distinct_module g.module₂).1; grind

theorem lookup_partialInjective [BEq α] [LawfulBEq α] {ps : List (α × γ)}
    (hn : (ps.map Prod.snd).Nodup) : PartialInjective (fun a => ps.lookup a) :=
  fun _ _ _ h h' => pair_right_unique hn (lookup_mem h) (lookup_mem h')

theorem lookup_pairRename [BEq α] [LawfulBEq α] [Inhabited γ] {ps : List (α × γ)}
    (hn : (ps.map Prod.fst).Nodup) (ha : a ∈ ps.map Prod.fst) :
    ps.lookup a = some (pairRename ps a) := by
  obtain ⟨⟨a, b⟩, hp, rfl⟩ := List.mem_map.mp ha
  rw [pairRename_eq hn hp]; exact lookup_of_mem hn hp

def ModulePair.opMap (g : ModulePair ctx₁ ctx₂ root₁ root₂) : OperationPtr → Option OperationPtr :=
  fun o => g.operationPairs.lookup o

def ModulePair.regionMap (g : ModulePair ctx₁ ctx₂ root₁ root₂) : RegionPtr → Option RegionPtr :=
  fun r => g.regionPairs.lookup r

def ModulePair.blockMap (g : ModulePair ctx₁ ctx₂ root₁ root₂) : BlockPtr → Option BlockPtr :=
  fun b => g.blockPairs.lookup b

theorem ModulePair.opMap_total (g : ModulePair ctx₁ ctx₂ root₁ root₂) (ho : o ∈ g.operationPairs.map Prod.fst) :
    g.opMap o = some (g.opRename o) := lookup_pairRename g.operations_left_nodup ho

theorem ModulePair.blockMap_total (g : ModulePair ctx₁ ctx₂ root₁ root₂) (hb : b ∈ g.blockPairs.map Prod.fst) :
    g.blockMap b = some (g.blockRename b) := lookup_pairRename g.blocks_left_nodup hb

theorem ModulePair.map_root (g : ModulePair ctx₁ ctx₂ root₁ root₂) : g.opMap root₁ = some root₂ :=
  lookup_of_mem g.operations_left_nodup (by simp [operationPairs])

theorem ModulePair.map_function (g : ModulePair ctx₁ ctx₂ root₁ root₂) (hp : p ∈ g.functions) :
    g.opMap p.left.op = some p.right.op := by
  rw [g.opMap_total (by rw [g.operations_left]; exact .tail _ (List.mem_flatMap.mpr ⟨p, hp, List.mem_cons_self⟩)), g.rename_function hp]

theorem ModulePair.map_body (g : ModulePair ctx₁ ctx₂ root₁ root₂) (hp : p ∈ g.functions) :
    g.blockMap p.left.block = some p.right.block :=
  lookup_of_mem g.blocks_left_nodup (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, hp, rfl⟩))

theorem ModulePair.map_moduleBlock (g : ModulePair ctx₁ ctx₂ root₁ root₂) : g.blockMap g.block₁ = some g.block₂ :=
  lookup_of_mem g.blocks_left_nodup (by simp [blockPairs])

theorem ModulePair.map_moduleRegion (g : ModulePair ctx₁ ctx₂ root₁ root₂) : g.regionMap g.region₁ = some g.region₂ :=
  lookup_of_mem g.regions_left_nodup (by simp [regionPairs])

theorem ModulePair.map_functionRegion (g : ModulePair ctx₁ ctx₂ root₁ root₂) (hp : p ∈ g.functions) :
    g.regionMap p.left.region = some p.right.region :=
  lookup_of_mem g.regions_left_nodup (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p, hp, rfl⟩))

theorem ModulePair.map_value (g : ModulePair ctx₁ ctx₂ root₁ root₂) (hp : p ∈ g.functions)
    (hv : ValueSupported p.left.operations p.left.block v) :
    renameValue? g.opMap g.blockMap v = some (renameValue g.opRename g.blockRename v) := by
  cases v with
  | opResult r =>
    have hm := g.opMap_total (o := r.op) (by rw [g.operations_left]; simp only [List.mem_cons, List.mem_flatMap]; exact .inr ⟨p, hp, .inr hv⟩)
    simp [renameValue?, renameValue, hm]
  | blockArgument a =>
    have hm := g.blockMap_total (b := a.block) (by simp only [blockPairs, List.map_cons, List.map_map, List.mem_cons, List.mem_map]; exact .inr ⟨p, hp, hv.symm⟩)
    simp [renameValue?, renameValue, hm]

theorem OperationAgrees.of_fields {φ : OperationPtr → Option OperationPtr} {ρ : RegionPtr → Option RegionPtr}
    {β : BlockPtr → Option BlockPtr} (hf : SameFields ctx₁ ctx₂ f g o o')
    (hi : o.InBounds ctx₁.raw) (hi' : o'.InBounds ctx₂.raw)
    (hv : (o.getOperands! ctx₁.raw).mapM (renameValue? φ β) = some ((o.getOperands! ctx₁.raw).map (renameValue f g)))
    (hs : o.getSuccessors! ctx₁.raw = #[])
    (hr : (o.getRegions! ctx₁.raw).mapM ρ = some (o'.getRegions! ctx₂.raw))
    (hp : o ≠ root → (o.getParent! ctx₁.raw).mapM β = some (o'.getParent! ctx₂.raw)) :
    OperationAgrees ctx₁ ctx₂ root φ ρ β o o' := by
  simp only [SameFields, Prod.mk.injEq] at hf
  rcases hf with ⟨hprops, ht, hts, hsucc, hattrs, hoper, _⟩
  exact ⟨hi, hi', fun c => (hprops c).symm, by grind, by simpa only [hoper] using hv,
    by simp [hs, hsucc], hr, hp⟩

theorem MatchesOp.successors_eq (h : MatchesOp ctx o code ts vs rs props attrs) : o.getSuccessors! ctx.raw = #[] := by
  have hs : o.getNumSuccessors! ctx.raw = 0 := by grind [MatchesOp]
  exact Array.eq_empty_iff_size_eq_zero.mpr (by simpa using hs)

theorem region_agrees_of_chains {φ : OperationPtr → Option OperationPtr} {β : BlockPtr → Option BlockPtr}
    (h₁ : r.BlockChain ctx₁.raw bs) (h₂ : r'.BlockChain ctx₂.raw bs')
    (hp : (r.getParent! ctx₁.raw).mapM φ = some (r'.getParent! ctx₂.raw))
    (hm : bs.mapM β = some bs') : RegionAgrees ctx₁ ctx₂ φ β r r' := by
  refine ⟨h₁.inBounds, h₂.inBounds, hp, ?_⟩
  intro xs hx; obtain rfl := RegionPtr.BlockChain_unique hx h₁; exact ⟨bs', hm, h₂⟩

theorem block_agrees_of_chains {φ : OperationPtr → Option OperationPtr} {ρ : RegionPtr → Option RegionPtr}
    (h₁ : b.OpChain ctx₁.raw os) (h₂ : b'.OpChain ctx₂.raw os')
    (ha : b.getArgumentTypes! ctx₁.raw = b'.getArgumentTypes! ctx₂.raw)
    (hp : (b.getParent! ctx₁.raw).mapM ρ = some (b'.getParent! ctx₂.raw))
    (hm : os.mapM φ = some os') : BlockAgrees ctx₁ ctx₂ φ ρ b b' := by
  refine ⟨h₁.blockInBounds, h₂.blockInBounds, ha, hp, ?_⟩
  intro xs hx; obtain rfl := BlockPtr.OpChain_unique hx h₁; exact ⟨os', hm, h₂⟩

theorem ModulePair.map_function_ops (g : ModulePair ctx₁ ctx₂ root₁ root₂) (hp : p ∈ g.functions) :
    p.left.operations.toArray.mapM g.opMap = some p.right.operations.toArray := by
  have hm := array_mapM_some (xs := p.left.operations.toArray) (g := g.opRename) (fun o ho => g.opMap_total (by
    rw [g.operations_left]; exact .tail _ (List.mem_flatMap.mpr ⟨p, hp, List.mem_cons_of_mem _ (by simpa using ho)⟩)))
  simpa only [List.map_toArray, g.rename_body hp] using hm

theorem ModulePair.map_functions (g : ModulePair ctx₁ ctx₂ root₁ root₂) :
    (g.functions.map (·.left.op)).toArray.mapM g.opMap = some (g.functions.map (·.right.op)).toArray := by
  have hm := array_mapM_some (xs := (g.functions.map (·.left.op)).toArray) (g := g.opRename) (fun o ho => g.opMap_total (by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp ho)
    rw [g.operations_left]; exact .tail _ (List.mem_flatMap.mpr ⟨p, hp, List.mem_cons_self⟩)))
  simpa only [List.map_toArray, g.rename_functions] using hm

theorem ModulePair.regions_agree (g : ModulePair ctx₁ ctx₂ root₁ root₂) (hm : g.regionMap r = some r') :
    RegionAgrees ctx₁ ctx₂ g.opMap g.blockMap r r' := by
  rcases List.mem_cons.mp (lookup_mem hm) with he | he
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    apply region_agrees_of_chains g.blocks₁ g.blocks₂
    · simp [show g.region₁.getParent! ctx₁.raw = some root₁ from g.module₁.region_parent (by simp),
      show g.region₂.getParent! ctx₂.raw = some root₂ from g.module₂.region_parent (by simp), g.map_root]
    · simp [Array.mapM_eq_mapM_toList, g.map_moduleBlock]
  · obtain ⟨p, hp, he⟩ := List.mem_map.mp he; obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    apply region_agrees_of_chains p.left.blocks p.right.blocks
    · simp [p.left.parent, p.right.parent, g.map_function hp]
    · simp [Array.mapM_eq_mapM_toList, g.map_body hp]

theorem ModulePair.blocks_agree (g : ModulePair ctx₁ ctx₂ root₁ root₂) (hm : g.blockMap b = some b') :
    BlockAgrees ctx₁ ctx₂ g.opMap g.regionMap b b' := by
  rcases List.mem_cons.mp (lookup_mem hm) with he | he
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    apply block_agrees_of_chains g.chain₁ g.chain₂ (g.args₁.trans g.args₂.symm) _ g.map_functions
    simp [show g.block₁.getParent! ctx₁.raw = some g.region₁ from g.blocks₁.opParent (by simp),
      show g.block₂.getParent! ctx₂.raw = some g.region₂ from g.blocks₂.opParent (by simp), g.map_moduleRegion]
  · obtain ⟨p, hp, he⟩ := List.mem_map.mp he; obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    apply block_agrees_of_chains p.left.chain p.right.chain p.args.symm _ (g.map_function_ops hp)
    simp [show p.left.block.getParent! ctx₁.raw = some p.left.region from p.left.blocks.opParent (by simp),
      show p.right.block.getParent! ctx₂.raw = some p.right.region from p.right.blocks.opParent (by simp), g.map_functionRegion hp]

theorem ModulePair.root_agrees (g : ModulePair ctx₁ ctx₂ root₁ root₂) :
    OperationAgrees ctx₁ ctx₂ root₁ g.opMap g.regionMap g.blockMap root₁ root₂ := by
  apply OperationAgrees.of_fields (g.module₁.fields (φ := g.opRename) (β := g.blockRename) g.module₂ (by simp) (by simp)) g.module₁.1 g.module₂.1
  · have hv : root₁.getOperands! ctx₁.raw = #[] := by have := g.module₁; grind [MatchesOp]
    simp [hv]
  · exact g.module₁.successors_eq
  · simp [g.module₁.regions_eq, g.module₂.regions_eq, Array.mapM_eq_mapM_toList, g.map_moduleRegion]
  · simp

theorem ModulePair.function_agrees (g : ModulePair ctx₁ ctx₂ root₁ root₂) (hp : p ∈ g.functions) :
    OperationAgrees ctx₁ ctx₂ root₁ g.opMap g.regionMap g.blockMap p.left.op p.right.op := by
  apply OperationAgrees.of_fields (p.fields g.opRename g.blockRename) p.left.inBounds p.right.inBounds
  · simp [p.left.operands]
  · exact p.left.successors
  · simp [p.left.regions, p.right.regions, Array.mapM_eq_mapM_toList, g.map_functionRegion hp]
  · intro _
    simp [g.chain₁.opParent (by simpa using List.mem_map_of_mem (f := fun p => p.left.op) hp),
      g.chain₂.opParent (by simpa using List.mem_map_of_mem (f := fun p => p.right.op) hp), g.map_moduleBlock]

theorem ModulePair.leaf_agrees (g : ModulePair ctx₁ ctx₂ root₁ root₂) (hp : p ∈ g.functions)
    (ho : o ∈ p.left.operations) :
    OperationAgrees ctx₁ ctx₂ root₁ g.opMap g.regionMap g.blockMap o (g.opRename o) := by
  have ho' : g.opRename o ∈ p.right.operations := by rw [← g.rename_body hp]; exact List.mem_map_of_mem ho
  apply OperationAgrees.of_fields (p.body _ _ (g.rename_body hp) (g.rename_block hp) o ho)
    (p.left.chain.arrayInBounds (by simpa using ho)) (p.right.chain.arrayInBounds (by simpa using ho'))
  · exact array_mapM_some (fun v hv => g.map_value hp (p.left.supported o ho v hv))
  · exact p.left.noSuccessors o ho
  · simp [p.left.leaves o ho, p.right.leaves _ ho']
  · intro _
    simp [p.left.chain.opParent (by simpa using ho), p.right.chain.opParent (by simpa using ho'), g.map_body hp]

theorem ModulePair.operations_agree (g : ModulePair ctx₁ ctx₂ root₁ root₂) (hm : g.opMap o = some o') :
    OperationAgrees ctx₁ ctx₂ root₁ g.opMap g.regionMap g.blockMap o o' := by
  have ho : o ∈ g.operationPairs.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) (lookup_mem hm)
  obtain rfl : o' = g.opRename o := Option.some.inj (hm.symm.trans (g.opMap_total ho))
  rw [g.operations_left] at ho; simp only [List.mem_cons, List.mem_flatMap] at ho
  rcases ho with rfl | ⟨p, hp, rfl | ho⟩
  · simpa only [g.rename_root] using g.root_agrees
  · simpa only [g.rename_function hp] using g.function_agrees hp
  · exact g.leaf_agrees hp ho

theorem ModulePair.iso (g : ModulePair ctx₁ ctx₂ root₁ root₂) : RootedIso ctx₁ root₁ ctx₂ root₂ :=
  ⟨g.opMap, g.regionMap, g.blockMap, lookup_partialInjective g.operations_right_nodup,
    lookup_partialInjective g.regions_right_nodup, lookup_partialInjective g.blocks_right_nodup,
    g.map_root, fun _ _ h => g.operations_agree h, fun _ _ h => g.regions_agree h,
    fun _ _ h => g.blocks_agree h⟩

theorem LowersModule.iso (h₁ : LowersModule ctx₁ m root₁) (h₂ : LowersModule ctx₂ m root₂) :
    RootedIso ctx₁ root₁ ctx₂ root₂ := by
  obtain ⟨g⟩ := modulePair_of_specs h₁ h₂; exact g.iso

end CompletenessIsomorphism

theorem lowerModule_complete : LowersModule ctx m root  → ∃ ctx2 root2, lowerModule m = .ok (ctx2, root2) ∧
  equivalent_modulo_renaming ctx root ctx2 root2 := by
  intro h; obtain ⟨ctx2, root2, he⟩ := lowerModule_total h.valid
  exact ⟨ctx2, root2, he, h.iso (lowerModule_sound he)⟩

section IsomorphismTransport


variable {ctx₁ ctx₂ : WfIRContext OpCode}
variable {D : Type} [HasOpInfo D] [HasDialect OpCode D] {code : D} {props : propertiesOf code}

def totalMap [Inhabited β] (f : α → Option β) (a : α) : β := (f a).getD default

theorem list_mapM_map {f : α → Option β} {g : α → β} {xs : List α} {ys : List β}
    (hf : ∀ a b, f a = some b → g a = b) (h : xs.mapM f = some ys) : xs.map g = ys := by
  induction xs generalizing ys with
  | nil => simpa using h
  | cons a xs ih =>
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hs : xs.mapM f with
      | none => simp [ha, hs] at h
      | some bs => obtain rfl : ys = b :: bs := (by simpa [ha, hs] using h.symm); simp [hf _ _ ha, ih hs]

theorem array_mapM_map {f : α → Option β} {g : α → β} {xs : Array α} {ys : Array β}
    (hf : ∀ a b, f a = some b → g a = b) (h : xs.mapM f = some ys) : xs.map g = ys := by
  apply Array.toList_inj.mp
  simpa using list_mapM_map hf (show xs.toList.mapM f = some ys.toList by simp [← Array.toList_mapM, h])

theorem renameValue_total {φ : OperationPtr → Option OperationPtr} {β : BlockPtr → Option BlockPtr}
    (h : renameValue? φ β v = some v') : renameValue (totalMap φ) (totalMap β) v = v' := by
  cases v with
  | opResult r =>
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [renameValue, totalMap, ho]
  | blockArgument a =>
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [renameValue, totalMap, hb]

theorem properties_eq_of_global {o o' : OperationPtr}
    (ht : o.getOpType! ctx₁.raw = o'.getOpType! ctx₂.raw)
    (hp : ∀ c : OpCode, o.getProperties! ctx₁.raw c = o'.getProperties! ctx₂.raw c) :
    o.getProperties! ctx₁.raw code = o'.getProperties! ctx₂.raw code := by
  have hc := hp (ofDialect OpCode code)
  unfold OperationPtr.getOpType! at ht
  unfold OperationPtr.getProperties! at *
  grind [HasDialect.toDialectProperties_ofDialectProperties, HasDialect.ofDialectProperties_toDialectProperties]

theorem list_mapM_defined [Inhabited β] {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) (ha : a ∈ xs) : f a = some (totalMap f a) := by
  induction xs generalizing ys with
  | nil => simp at ha
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [hx] at h
    | some b =>
      cases hs : xs.mapM f with
      | none => simp [hx, hs] at h
      | some bs => rcases List.mem_cons.mp ha with rfl | ha; simp [totalMap, hx]; exact ih hs ha

theorem array_mapM_defined [Inhabited β] {f : α → Option β} {xs : Array α} {ys : Array β}
    (h : xs.mapM f = some ys) (ha : a ∈ xs) : f a = some (totalMap f a) :=
  list_mapM_defined (xs := xs.toList) (ys := ys.toList) (by simp [← Array.toList_mapM, h]) (by simpa using ha)

theorem mapM_singleton [Inhabited β] {f : α → Option β} {ys : Array β}
    (h : #[a].mapM f = some ys) : f a = some (totalMap f a) ∧ ys = #[totalMap f a] := by
  cases he : f a <;> simp_all [Array.mapM_eq_mapM_toList, totalMap]

theorem MatchesOp.map {φ : OperationPtr → Option OperationPtr} {ρ : RegionPtr → Option RegionPtr}
    {β : BlockPtr → Option BlockPtr} (h : MatchesOp ctx₁ o code ts vs rs props attrs)
    (he : OperationAgrees ctx₁ ctx₂ root φ ρ β o o') :
    MatchesOp ctx₂ o' code ts (vs.map (renameValue (totalMap φ) (totalMap β))) (rs.map (totalMap ρ)) props attrs := by
  rcases he with ⟨hi, hi', hprops, hlabels, hvs, hss, hrs, _⟩
  have hv := array_mapM_map (fun _ _ => renameValue_total) hvs
  have hr := array_mapM_map (g := totalMap ρ) (fun a b h => by simp [totalMap, h]) hrs
  have hs := array_mapM_map (g := totalMap β) (fun a b h => by simp [totalMap, h]) hss
  have hp := properties_eq_of_global (code := code) (congrArg Prod.fst hlabels) hprops
  simp only [MatchesOp, Prod.mk.injEq] at *
  have hsize := congrArg Array.size hs
  grind [Array.size_map, OperationPtr.getSuccessors!.size_eq_getNumSuccessors!]

section Map

variable {φ : OperationPtr → Option OperationPtr} {ρ : RegionPtr → Option RegionPtr} {β : BlockPtr → Option BlockPtr}
variable {root : OperationPtr}
variable (hop : ∀ o o', φ o = some o' → OperationAgrees ctx₁ ctx₂ root φ ρ β o o')
variable (hreg : ∀ r r', ρ r = some r' → RegionAgrees ctx₁ ctx₂ φ β r r')
variable (hblock : ∀ b b', β b = some b' → BlockAgrees ctx₁ ctx₂ φ ρ b b')

def mappedValues (φ : OperationPtr → Option OperationPtr) (β : BlockPtr → Option BlockPtr) (values : ValueMap) : ValueMap :=
  fun id => (values id).map (renameValue (totalMap φ) (totalMap β))

include hop in
theorem OperandTile.map (h : OperandTile ctx₁ values ty value v cs)
    (hdefs : ∀ o ∈ cs, φ o = some (totalMap φ o)) :
    OperandTile ctx₂ (mappedValues φ β values) ty value (renameValue (totalMap φ) (totalMap β) v) (cs.map (totalMap φ)) := by
  cases value with
  | ref id => obtain ⟨hv, rfl⟩ := h; exact ⟨by simp [mappedValues, hv], rfl⟩
  | intConst n =>
    cases ty; obtain ⟨c, rfl, rfl, hc⟩ := h
    refine ⟨totalMap φ c, rfl, by simp [renameValue, OperationPtr.getResult], ?_⟩
    simpa using hc.map (hop _ _ (hdefs c (by simp)))

include hop in
theorem LowersInstTile.map {id : ValueId} (h : LowersInstTile ctx₁ values id inst tile)
    (hdefs : ∀ o ∈ tile, φ o = some (totalMap φ o)) :
    LowersInstTile ctx₂ (mappedValues φ β values) id inst (tile.map (totalMap φ)) := by
  cases inst; obtain ⟨vl, vr, cl, cr, o, rfl, hl, hr, hd, ho⟩ := h
  refine ⟨renameValue (totalMap φ) (totalMap β) vl, renameValue (totalMap φ) (totalMap β) vr,
    cl.map (totalMap φ), cr.map (totalMap φ), totalMap φ o, by simp,
    hl.map hop (fun c hc => hdefs c (by simp [hc])), hr.map hop (fun c hc => hdefs c (by simp [hc])), ?_, ?_⟩
  · simp [mappedValues, hd, renameValue, OperationPtr.getResult]
  · simpa using ho.map (hop _ _ (hdefs o (by simp)))

theorem resolvesList_map_right {R : α → γ → Prop} {S : α → δ → Prop} {f : γ → δ}
    (h : ResolvesList R as bs) (hf : ∀ a b, b ∈ bs → R a b → S a (f b)) : ResolvesList S as (bs.map f) := by
  induction h with
  | nil => exact .nil
  | cons hr ht ih => exact .cons (hf _ _ (by simp) hr) (ih (fun a b hb => hf a b (by simp [hb])))

include hop hreg hblock in
theorem map_single_body {ops : List OperationPtr} (hf : MatchesOp ctx₁ o code ts vs #[r] props attrs)
    (hb : r.BlockChain ctx₁.raw #[b]) (hc : b.OpChain ctx₁.raw ops.toArray) (hm : φ o = some o') :
    ρ r = some (totalMap ρ r) ∧ β b = some (totalMap β b) ∧
    (totalMap ρ r).BlockChain ctx₂.raw #[totalMap β b] ∧
    (totalMap β b).getArgumentTypes! ctx₂.raw = b.getArgumentTypes! ctx₁.raw ∧
    (totalMap β b).OpChain ctx₂.raw (ops.map (totalMap φ)).toArray ∧
    (∀ o ∈ ops, φ o = some (totalMap φ o)) := by
  have he := hop _ _ hm
  have hr := mapM_singleton (show #[r].mapM ρ = some (o'.getRegions! ctx₂.raw) by simpa only [hf.regions_eq] using he.2.2.2.2.2.2.1)
  obtain ⟨bs, hbs, hb'⟩ := (hreg _ _ hr.1).2.2.2 _ hb
  obtain ⟨hd, rfl⟩ := mapM_singleton hbs
  have heblock := hblock _ _ hd
  obtain ⟨os, hos, hc'⟩ := heblock.2.2.2.2 _ hc
  have htotal := array_mapM_map (g := totalMap φ) (fun a b h => by simp [totalMap, h]) hos
  exact ⟨hr.1, hd, hb', heblock.2.2.1.symm, by simpa only [← List.map_toArray, htotal] using hc',
    fun o ho => array_mapM_defined hos (by simpa using ho)⟩

theorem mapped_params (hp : ∀ i, values (.param i) = (b.getArguments! ctx₁.raw)[i]?)
    (ha : (totalMap β b).getArgumentTypes! ctx₂.raw = b.getArgumentTypes! ctx₁.raw) :
    ∀ i, mappedValues φ β values (.param i) = ((totalMap β b).getArguments! ctx₂.raw)[i]? := by
  have hn := congrArg Array.size ha
  simp only [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] at hn
  intro i; simp [mappedValues, hp, BlockPtr.getArguments!, renameValue, BlockPtr.getArgument, hn, Function.comp_def]

include hop hreg hblock in
theorem LowersFunctionTiles.map (h : LowersFunctionTiles ctx₁ f o) (hm : φ o = some o') :
    LowersFunctionTiles ctx₂ f o' := by
  obtain ⟨w⟩ := h.witness
  obtain ⟨hr, hb, hbs, ha, hc, hd⟩ := map_single_body hop hreg hblock w.func w.blocks w.chain hm
  refine ⟨w.valid, totalMap ρ w.region, totalMap β w.block, w.tiles.map (List.map (totalMap φ)),
    w.constants.map (totalMap φ), totalMap φ w.ret, renameValue (totalMap φ) (totalMap β) w.result,
    mappedValues φ β w.values, by simpa using w.func.map (hop _ _ hm), hbs, ha.trans w.args,
    mapped_params w.params ha, ?_, ?_, ?_, ?_⟩
  · exact resolvesList_map_right w.insts (fun _ tile ht hh => hh.map hop (fun o ho => hd o (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatten.mpr ⟨tile, ht, ho⟩)))))
  · exact w.resultTile.map hop (fun o ho => hd o (by simp [ho]))
  · simpa using w.returnOp.map (hop _ _ (hd w.ret (by simp)))
  · simpa [FunctionWitness.operations, List.map_append, List.map_flatten] using hc

include hop hreg hblock in
theorem LowersModule.map (h : LowersModule ctx₁ m o) (hm : φ o = some o') : LowersModule ctx₂ m o' := by
  obtain ⟨r, b, fs, hf, hb, hc, ha, hfs⟩ := h
  obtain ⟨hr, hd, hbs, hargs, hchain, hdefs⟩ := map_single_body hop hreg hblock hf hb hc hm
  exact ⟨totalMap ρ r, totalMap β b, fs.map (totalMap φ), by simpa using hf.map (hop _ _ hm),
    hbs, hchain, hargs.trans ha, resolvesList_map_right hfs (fun _ op hop' hh => hh.map hop hreg hblock (hdefs op hop'))⟩

end Map

theorem LowersModule.of_iso (h : LowersModule ctx₁ m root₁) (he : RootedIso ctx₁ root₁ ctx₂ root₂) :
    LowersModule ctx₂ m root₂ := by
  obtain ⟨φ, ρ, β, _, _, _, hr, ho, hreg, hblock⟩ := he
  exact h.map ho hreg hblock hr

theorem lowerModule_correct : LowersModule ctx m root ↔
    ∃ ctx₂ root₂, lowerModule m = .ok (ctx₂, root₂) ∧ equivalent_modulo_renaming ctx root ctx₂ root₂ := by
  refine ⟨lowerModule_complete, ?_⟩
  rintro ⟨ctx₂, root₂, he, hi⟩
  exact (lowerModule_sound he).of_iso hi.symm


end IsomorphismTransport

section RoundTrip

variable {ctx : WfIRContext OpCode} {block : BlockPtr}

theorem collect_chain {arr : Array OperationPtr} (h : block.OpChain ctx.raw arr) (hn : arr.size - i < n) :
    reverseOps.collect ctx n arr[i]? = .ok (arr.toList.drop i) := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    by_cases hi : i < arr.size
    · simp [reverseOps.collect, hi, h.arrayInBounds, h.next hi, ih (i := i + 1) (by omega), Functor.map, Except.map, List.drop_eq_getElem_cons (show i < arr.toList.length by simpa using hi)]
    · simp [reverseOps.collect, hi, List.drop_of_length_le (show arr.toList.length ≤ i by simpa using Nat.le_of_not_lt hi), pure, Except.pure]

theorem reverseOps_chain {arr : Array OperationPtr} (h : block.OpChain ctx.raw arr) :
    reverseOps ctx block = .ok arr.toList := by
  have hs : arr.toList.length ≤ ctx.raw.operations.size := Std.HashMap.length_keys (m := ctx.raw.operations) ▸
    (BlockPtr.OpChain_array_toList_Nodup h).length_le_of_subset fun o ho => Std.HashMap.mem_keys.mpr (h.arrayInBounds (by simpa using ho))
  simpa [reverseOps, h.first] using collect_chain (i := 0) h (by simp at hs; omega)

theorem reverseBody_chain (hr : op.getRegions! ctx.raw = #[r]) (hb : r.BlockChain ctx.raw #[b]) :
    reverseBody ctx op = .ok b := by
  have h₁ := hb.first; have h₂ := hb.next (i := 0) (by simp)
  simp_all [reverseBody, pure, Except.pure]

theorem fromUTF8!_toByteArray (s : String) : String.fromUTF8! s.toByteArray = s := by
  simp [String.fromUTF8!, s.isValidUTF8]; rfl

theorem reverseType_lowerType (ty : LLType) : reverseType (lowerType ty).val = .ok ty := by
  cases ty; rfl

theorem ofInt_normalizeValue {w : Nat} {n : Int} : BitVec.ofInt w (IntegerAttr.normalizeValue (.signless w) n) = BitVec.ofInt w n := by
  unfold IntegerAttr.normalizeValue IntegerType.signless
  split <;> simp only [BitVec.ofInt_toInt, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem OperandTile.reverse {vals : List (ValuePtr × ValueId)} (h : OperandTile ctx values ty x v cs)
    (hx : ValidResolvedValue np ni x)
    (href : ∀ id v, ValidResolvedValue np ni (.ref id) → values id = some v → vals.lookup v = some id)
    (hc : ∀ c : OperationPtr, c.getOpType! ctx.raw = ofDialect OpCode Llvm.mlir__constant →
      vals.lookup (.opResult (c.getResult 0)) = none) :
    ∃ x', reverseValue ctx vals v = .ok x' ∧ ValueEquiv ty x' x := by
  cases x with
  | ref id => obtain ⟨hv, rfl⟩ := h; exact ⟨_, by simp [reverseValue, href id v hx hv, pure, Except.pure], .refl⟩
  | intConst n =>
    cases ty; obtain ⟨c, rfl, rfl, hm⟩ := h
    have ht : c.getOpType! ctx.raw = ofDialect OpCode Llvm.mlir__constant := by grind [MatchesOp]
    have hp := hm.2.1
    refine ⟨.intConst (IntegerAttr.normalizeValue (.signless _) n), ?_, ofInt_normalizeValue⟩
    have hl := hc c ht; simp only [OperationPtr.getResult] at hl
    simp [reverseValue, hl, ht, hp, OperationPtr.getResult, IntegerAttr.ofInt, pure, Except.pure]

section Lists

theorem resolvesList_filter {R : α → List β → Prop} {as : List α} {p : β → Bool} {tiles : List (List β)} (h : ResolvesList R as tiles)
    (ht : ∀ a t, R a t → ∃ d, t.getLast? = some d ∧ t.filter p = [d]) :
    ResolvesList (fun a d => ∃ t, R a t ∧ t.getLast? = some d) as (tiles.flatten.filter p) := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih => obtain ⟨d, hl, hf⟩ := ht _ _ hr; rw [List.flatten_cons, List.filter_append, hf]; exact .cons ⟨_, hr, hl⟩ ih

theorem resolvesList_mapM {S : γ → α → Prop} {as : List α} {bs : List β} {f : β → Except ε γ} (h : ResolvesList (fun a b => ∃ c, f b = .ok c ∧ S c a) as bs) :
    ∃ cs, bs.mapM f = .ok cs ∧ ResolvesList S cs as := by
  induction h with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons hr _ ih =>
    obtain ⟨c, hc, hs⟩ := hr; obtain ⟨cs, hcs, ht⟩ := ih
    exact ⟨c :: cs, by simp [List.mapM_cons, hc, hcs, bind, Except.bind, pure, Except.pure], .cons hs ht⟩

theorem resolvesList_of_zipIdx {S : γ → α → Prop} {as : List α} {cs : List γ} (h : ResolvesList (fun c e => S c e.1) cs (as.zipIdx k)) :
    ResolvesList S cs as := by
  induction as generalizing k cs with
  | nil => cases h; exact .nil
  | cons a as ih => cases h with | cons hr ht => exact .cons hr (ih ht)

theorem resolvesList_zipIdx_mem {R : α × Nat → β → Prop} {as : List α} {bs : List β} (h : ResolvesList R (as.zipIdx k) bs) (ha : (a, i) ∈ as.zipIdx k) :
    ∃ b, (b, i) ∈ bs.zipIdx k ∧ R (a, i) b := by
  induction as generalizing k bs with
  | nil => simp at ha
  | cons a' as ih =>
    cases h with | cons hr ht =>
    rcases List.mem_cons.mp ha with he | ha
    · cases he; exact ⟨_, by simp, hr⟩
    · obtain ⟨b, hb, hr⟩ := ih ht ha; exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

end Lists

theorem OperandTile.filter (h : OperandTile ctx values ty x v cs) : cs.filter (isDefinition ctx) = [] := by
  cases x with
  | ref => simp [h.2]
  | intConst => cases ty; obtain ⟨c, rfl, -, hm⟩ := h; have := hm.2.2; simp_all [isDefinition, HasDialect.toDialect?_ofDialect]

theorem LowersInstTile.filter {id : ValueId} (h : LowersInstTile ctx values id inst tile) :
    ∃ d, tile.getLast? = some d ∧ tile.filter (isDefinition ctx) = [d] := by
  cases inst with | bin opc =>
  obtain ⟨_, _, _, _, op, rfl, hl, hr, -, hm⟩ := h
  have := hm.2.2; cases opc <;> simp_all [List.filter_append, hl.filter, hr.filter, isDefinition, binOpcode]

theorem map_zipIdx_fst (f : α → β) (l : List α) : l.zipIdx.map (fun x => f x.1) = l.map f := by
  show List.map (f ∘ Prod.fst) _ = _; rw [← List.map_map, List.zipIdx_map_fst]

theorem valueTable_keys (hd : defs.Nodup) : ((valueTable ctx block defs).map Prod.fst).Nodup := by
  simp only [valueTable, List.map_append, List.map_map, Function.comp_def, map_zipIdx_fst (fun v => v), List.map_id']
  refine List.nodup_append.mpr ⟨?_, (map_zipIdx_fst (fun d => ValuePtr.opResult (d.getResult 0)) defs) ▸ hd.map _ fun _ _ hne h => hne (by simpa [OperationPtr.getResult] using h), ?_⟩
  · simp only [BlockPtr.getArguments!, Array.toList_map, Array.toList_range]
    exact List.nodup_range.map _ fun _ _ hne h => hne (by simpa [BlockPtr.getArgument] using h)
  · intro a ha b hb; simp [BlockPtr.getArguments!] at ha; simp at hb; grind

theorem valueTable_const (hd : ∀ d ∈ defs, isDefinition ctx d) (hc : isDefinition ctx c = false) :
    (valueTable ctx block defs).lookup (.opResult (c.getResult 0)) = none := by
  simp only [valueTable, List.lookup_eq_none_iff, List.mem_append, List.mem_map]
  rintro _ (⟨⟨_, _⟩, hm, rfl⟩ | ⟨⟨d, _⟩, hm, rfl⟩) <;> have hm := List.fst_mem_of_mem_zipIdx hm
  · simp only [BlockPtr.getArguments!, Array.toList_map, List.mem_map] at hm; grind
  · have := hd d hm; simp only [OperationPtr.getResult, bne_iff_ne, ne_eq, ValuePtr.opResult.injEq, OpResultPtr.mk.injEq, and_true]
    rintro rfl; simp_all

theorem LowersInstTile.reverse {id : ValueId} {vals : List (ValuePtr × ValueId)}
    (h : LowersInstTile ctx values id inst tile) (hl : tile.getLast? = some d) (hv : ValidResolvedInst np ni inst)
    (href : ∀ id v, ValidResolvedValue np ni (.ref id) → values id = some v → vals.lookup v = some id)
    (hc : ∀ c : OperationPtr, c.getOpType! ctx.raw = ofDialect OpCode Llvm.mlir__constant →
      vals.lookup (.opResult (c.getResult 0)) = none) :
    ∃ i, reverseInst ctx vals d = .ok i ∧ InstEquiv i inst := by
  cases inst with | bin opc ty =>
  obtain ⟨_, _, _, _, op, rfl, hlt, hrt, -, hm⟩ := h
  obtain rfl : op = d := by simpa using hl
  obtain ⟨l, hl, hle⟩ := hlt.reverse hv.1 href hc; obtain ⟨r, hr, hre⟩ := hrt.reverse hv.2 href hc
  have := hm.2.2
  refine ⟨.bin opc ty l r, ?_, rfl, rfl, hle, hre⟩
  cases opc <;> simp_all [reverseInst, binOpcode, reverseType_lowerType, bind, Except.bind, pure, Except.pure]

theorem resolvesList_imp {R S : α → β → Prop} {as : List α} {bs : List β} (h : ResolvesList R as bs)
    (f : ∀ a ∈ as, ∀ b, R a b → S a b) : ResolvesList S as bs := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih => exact .cons (f _ (by simp) _ hr) (ih fun a ha => f a (by simp [ha]))

theorem LowersInstTile.value {id : ValueId} (h : LowersInstTile ctx values id inst tile) (hl : tile.getLast? = some d) :
    values id = some (.opResult (d.getResult 0)) := by
  cases inst; obtain ⟨_, _, _, _, op, rfl, -, -, hv, -⟩ := h; obtain rfl : op = d := by simpa using hl
  exact hv

/-- The definitions `reverseFunction` numbers: the last op of each instruction tile. -/
def FunctionWitness.defs (w : FunctionWitness ctx f op) : List OperationPtr :=
  w.tiles.flatten.filter (isDefinition ctx)

theorem FunctionWitness.defs_spec (w : FunctionWitness ctx f op) :
    ResolvesList (fun e d => ∃ t, LowersInstTile ctx w.values (.inst e.2) e.1 t ∧ t.getLast? = some d)
      f.insts.zipIdx w.defs :=
  resolvesList_filter w.insts fun _ _ ht => ht.filter

theorem FunctionWitness.defs_nodup (w : FunctionWitness ctx f op) : w.defs.Nodup :=
  (FunctionShape.ofWitness w).nodup.sublist ((List.filter_sublist).trans (by simp [FunctionShape.ofWitness, operations, List.append_assoc]))

theorem FunctionWitness.lookup {id : ValueId} (w : FunctionWitness ctx f op) (hv : ValidResolvedValue f.header.params.length f.insts.length (.ref id))
    (he : w.values id = some v) : (valueTable ctx w.block w.defs).lookup v = some id := by
  refine lookup_of_mem (valueTable_keys w.defs_nodup) ?_
  cases id with
  | param i => rw [w.params] at he; exact List.mem_append_left _ (List.mem_map.mpr ⟨(v, i), by simpa [List.mk_mem_zipIdx_iff_getElem?] using he, rfl⟩)
  | inst i =>
    obtain ⟨d, hd, t, ht, hl⟩ := resolvesList_zipIdx_mem w.defs_spec (show (f.insts[i]'hv, i) ∈ f.insts.zipIdx by simpa [List.mk_mem_zipIdx_iff_getElem?] using List.getElem?_eq_getElem hv)
    obtain rfl := Option.some.inj (he.symm.trans (ht.value hl))
    exact List.mem_append_right _ (List.mem_map.mpr ⟨(d, i), hd, rfl⟩)

theorem FunctionWitness.lookup_const {c : OperationPtr} (w : FunctionWitness ctx f op) (hc : c.getOpType! ctx.raw = ofDialect OpCode Llvm.mlir__constant) :
    (valueTable ctx w.block w.defs).lookup (.opResult (c.getResult 0)) = none :=
  valueTable_const (fun _ hd => (List.mem_filter.mp hd).2) (by simp [isDefinition, hc, HasDialect.toDialect?_ofDialect])

theorem FunctionWitness.reverseInsts (w : FunctionWitness ctx f op) :
    ∃ insts, w.defs.mapM (reverseInst ctx (valueTable ctx w.block w.defs)) = .ok insts ∧ ResolvesList InstEquiv insts f.insts := by
  obtain ⟨insts, h, hr⟩ := resolvesList_mapM (S := fun i e => InstEquiv i e.1) (resolvesList_imp w.defs_spec fun e he _ ⟨_, ht, hl⟩ =>
    ht.reverse hl (w.valid.1 _ (List.fst_mem_of_mem_zipIdx he)) (fun _ _ => w.lookup) (fun _ => w.lookup_const))
  exact ⟨insts, h, resolvesList_of_zipIdx hr⟩

theorem list_mapM_map_ok {f : β → Except ε γ} {h : α → β} {g : α → γ} {xs : List α}
    (hf : ∀ x ∈ xs, f (h x) = .ok (g x)) : (xs.map h).mapM f = .ok (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp_all [List.mapM_cons, bind, Except.bind, pure, Except.pure]

theorem FunctionWitness.reverseParams (w : FunctionWitness ctx f op) :
    (w.block.getArgumentTypes! ctx.raw).toList.zipIdx.mapM reverseParam =
      .ok (f.header.params.zipIdx.map fun (p, i) => ⟨p.ty, s!"arg{i}"⟩) := by
  rw [w.args, Array.toList_map, List.zipIdx_map]
  exact list_mapM_map_ok fun _ _ => by simp [reverseParam, reverseType_lowerType, bind, Except.bind, pure, Except.pure]

theorem FunctionWitness.reverse_last (w : FunctionWitness ctx f op) : w.operations.getLast? = some w.ret := by
  simp [operations]

theorem FunctionWitness.reverse_defs (w : FunctionWitness ctx f op) :
    w.operations.dropLast.filter (isDefinition ctx) = w.defs := by
  simp [operations, defs, List.filter_append, w.resultTile.filter]

theorem LowersFunctionTiles.reverse (h : LowersFunctionTiles ctx f op) :
    ∃ g, reverseFunction ctx op = .ok g ∧ g.Equiv f := by
  obtain ⟨w⟩ := h.witness
  obtain ⟨insts, hi, hie⟩ := w.reverseInsts
  obtain ⟨r, hr, hre⟩ := w.resultTile.reverse w.valid.2 (fun _ _ => w.lookup) (fun _ => w.lookup_const)
  have hf := w.func; have hret := w.returnOp
  refine ⟨⟨⟨f.header.retType, f.header.name, f.header.params.zipIdx.map fun (p, i) => ⟨p.ty, s!"arg{i}"⟩⟩, "entry", insts, r⟩, ?_, rfl, rfl, ?_, hie, hre⟩
  · have hops : reverseOps ctx w.block = .ok w.operations := by simpa [FunctionWitness.operations] using reverseOps_chain w.chain
    have hp := hf.2.1; have hft := hf.2.2; have hrt := hret.2.2; simp only [Prod.mk.injEq] at hft hrt
    simp [reverseFunction, reverseBody_chain hf.regions_eq w.blocks, hops, w.reverse_last, w.reverse_defs, hi, hr, hp, hft, hrt,
      w.reverseParams, reverseType_lowerType, fromUTF8!_toByteArray, HasDialect.toDialect?_ofDialect, bind, Except.bind, pure, Except.pure]
  · simp [List.map_map, Function.comp_def, map_zipIdx_fst (fun p : Param => p.ty)]

theorem LowersModule.reverse (h : LowersModule ctx m root) : ∃ m', reverseModule ctx root = .ok m' ∧ m'.Equiv m := by
  obtain ⟨r, b, fs, hm, hb, hc, -, hfs⟩ := h
  obtain ⟨gs, hg, hrel⟩ := resolvesList_mapM (S := ResolvedFunction.Equiv) (resolvesList_imp hfs fun _ _ _ hf => hf.reverse)
  have ht := hm.2.2; simp only [Prod.mk.injEq] at ht
  exact ⟨⟨gs⟩, by simp [reverseModule, ht, reverseBody_chain hm.regions_eq hb, reverseOps_chain hc, hg, bind, Except.bind, pure, Except.pure], hrel⟩

/-- LLVM → MLIR → LLVM recovers the module up to local names and the spelling of literals. -/
theorem reverseModule_lowerModule (h : ∀ f ∈ m.funcs, ValidResolvedFunction f) :
    ∃ m', (lowerModule m >>= reverseModule.uncurry) = .ok m' ∧ m'.Equiv m := by
  obtain ⟨ctx, root, hl⟩ := lowerModule_total h
  obtain ⟨m', hr, he⟩ := (lowerModule_sound hl).reverse
  exact ⟨m', by simp [hl, hr, bind, Except.bind, Function.uncurry], he⟩

end RoundTrip

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
