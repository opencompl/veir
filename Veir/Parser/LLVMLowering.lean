import Veir.IR.RootedIso
import Veir.Parser.NameResolutionSketch
import Veir.Parser.DecidableInBounds
import Veir.Rewriter.WfRewriter
import Veir.OpCode

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

abbrev LookupValue := ValueId → LowerM ValuePtr

/-- Look up a reference or materialise a literal at its use. -/
def lowerOperand (lookup : LookupValue) (block : BlockPtr) (ty : LLType) :
    ResolvedValue → LowerM ValuePtr
  | .ref id => lookup id
  | .intConst value => do
      let .int width := ty
      let op ← emit .mlir__constant #[lowerType ty] #[] #[]
        { value := .integer (IntegerAttr.ofInt value (.signless width)) } block
      return .opResult (op.getResult 0)

/-- Allocate an instruction's result before resolving any operands. -/
def lowerInst (block : BlockPtr) : ResolvedBinary → LowerM OperationPtr
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
def wireBinary (lookup : LookupValue) (block : BlockPtr) : ResolvedBinary × OperationPtr → LowerM Unit
  | (.bin _ ty lhs rhs, op) => do
      pushValue op (← lowerOperand lookup block ty lhs)
      pushValue op (← lowerOperand lookup block ty rhs)
      attachInst block op

structure BlockLoweringPlan (α : Type) where
  block : BlockPtr
  insts : List ResolvedBinary
  terminator : α

/-- Allocate function-wide results first, then wire each block and lower its terminator. -/
def lowerBlocks (plans : List (BlockLoweringPlan α))
    (lookup : List (List OperationPtr) → LookupValue)
    (terminate : LookupValue → BlockLoweringPlan α → LowerM Unit) : LowerM Unit := do
  let groups ← plans.mapM fun p => p.insts.mapM (lowerInst p.block)
  let values := lookup groups
  for (p, ops) in plans.zip groups do
    (p.insts.zip ops).forM (wireBinary values p.block)
    terminate values p

def lowerReturn (lookup : LookupValue) (block : BlockPtr) (ty : LLType) (value : ResolvedValue) :
    LowerM OperationPtr := do
  let value ← lowerOperand lookup block ty value
  emit .return #[] #[value] #[] () block

/-- An empty module carrying `defaultModuleAttrs`. -/
def createModule : Option (WfIRContext OpCode × OperationPtr) :=
  (WfIRContext.create OpCode).bind fun (ctx, root) =>
    if h : root.InBounds ctx.raw then some (WfRewriter.setAttributes ctx root defaultModuleAttrs h, root) else none

/-! The lowering specification describes the rooted graph, including instruction tiles and
branch operands. -/

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
def LowersInstTile (values : ValueMap) (id : ValueId) : ResolvedBinary → List OperationPtr → Prop
  | .bin opc ty l r, tile => ∃ vl vr cl cr op, tile = cl ++ cr ++ [op] ∧
      OperandTile ctx values ty l vl cl ∧ OperandTile ctx values ty r vr cr ∧
      values id = some (.opResult (op.getResult 0)) ∧
      MatchesOp ctx op (binOpcode opc) #[lowerType ty] #[vl, vr] #[] default

end Specification

/-! ## Control-flow lowering -/

abbrev BlockMap := BlockId → Option BlockPtr

/-- Repeated phi entries for the same predecessor carry one resolved value. -/
def PhiInputsAgree (incoming : List (BlockId × ResolvedValue)) : Prop :=
  ∀ v ∈ incoming, ∀ w ∈ incoming, v.1 = w.1 → v.2 = w.2

instance : DecidablePred PhiInputsAgree := fun _ => inferInstanceAs (Decidable (∀ _ ∈ _, ∀ _ ∈ _, _))

theorem PhiInputsAgree.lookup_eq_some_iff (h : PhiInputsAgree incoming) :
    incoming.lookup src = some value ↔ (src, value) ∈ incoming := by
  have mem_of_lookup : ∀ {v}, incoming.lookup src = some v → (src, v) ∈ incoming := by
    intro v hv; obtain ⟨_, _, rfl, _⟩ := List.lookup_eq_some_iff.mp hv; simp
  refine ⟨mem_of_lookup, fun hv => ?_⟩
  cases hl : incoming.lookup src with
  | none => simpa using (List.lookup_eq_none_iff.mp hl) (src, value) hv
  | some found => exact congrArg some (h (src, found) (mem_of_lookup hl) (src, value) hv rfl)

def checkPhi (preds : List BlockId) : List ResolvedInst → Except LoweringError Unit
  | [] => .ok ()
  | .bin .. :: rest =>
    if rest.any (·.phiType.isSome) then .error "phi follows a non-phi instruction" else .ok ()
  | .phi _ incoming :: rest =>
    if (incoming.map Prod.fst).mergeSort = preds.mergeSort then
      if PhiInputsAgree incoming then checkPhi preds rest
      else .error "phi has different values for edges from the same predecessor"
    else .error "phi incoming blocks do not match the predecessor edges"

theorem mergeSort_nat_eq_iff_perm {a b : List BlockId} : a.mergeSort = b.mergeSort ↔ a.Perm b := by
  have ha := List.mergeSort_perm a (· ≤ ·)
  have hb := List.mergeSort_perm b (· ≤ ·)
  refine ⟨fun h => ha.symm.trans (h ▸ hb), fun h => ?_⟩
  have sorted (xs : List Nat) : xs.mergeSort.Pairwise (· ≤ ·) := by
    simpa using List.pairwise_mergeSort (le := fun x y : Nat => decide (x ≤ y))
      (by simpa using fun _ _ _ => Nat.le_trans) (by simpa using Nat.le_total) xs
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ => Nat.le_antisymm)
    (sorted a) (sorted b) (ha.trans (h.trans hb.symm))

theorem checkPhi_iff (preds : List BlockId) (insts : List ResolvedInst) :
    checkPhi preds insts = .ok () ↔
      insts.Pairwise (fun earlier later => later.phiType ≠ none → earlier.phiType ≠ none) ∧
      ∀ ty incoming, ResolvedInst.phi ty incoming ∈ insts →
        PhiInputsAgree incoming ∧ (incoming.map Prod.fst).Perm preds := by
  induction insts with
  | nil => simp [checkPhi]
  | cons inst rest ih =>
    cases inst with
    | bin =>
      have hn : rest.any (·.phiType.isSome) = false ↔ ∀ i ∈ rest, i.phiType = none := by
        simp [List.any_eq_false]
      rw [checkPhi.eq_2]
      split <;> grind [ResolvedInst.phiType, List.pairwise_cons, List.pairwise_iff_getElem]
    | phi ty incoming =>
      simp only [checkPhi.eq_3, mergeSort_nat_eq_iff_perm]
      by_cases hp : (incoming.map Prod.fst).Perm preds <;> by_cases ha : PhiInputsAgree incoming <;>
        simp [hp, ha, ih, List.pairwise_cons, ResolvedInst.phiType, or_imp, forall_and, and_assoc, and_comm]

def checkBlocks (f : ResolvedFunction) : Except LoweringError Unit := do
  let some entry := f.blocks[0]? | throw "function has no entry block"
  if entry.insts.any (·.phiType.isSome) then throw "phi in entry block"
  let mut preds := f.blocks.map fun _ => ([] : List BlockId)
  for (block, src) in f.blocks.toList.zipIdx do
    for dst in block.terminator.successors do
      if dst == 0 then throw "branch to the entry block"
      let some prev := preds[dst]? | throw "invalid branch destination"
      preds := preds.set! dst (src :: prev)
  for (block, id) in f.blocks.toList.zipIdx do
    checkPhi preds[id]! block.insts

def createBlock (region : RegionPtr) (types : Array TypeAttr) : LowerM BlockPtr := do
  let ctx ← get
  if hip : (some (BlockInsertPoint.atEnd region)).maybe BlockInsertPoint.InBounds ctx.raw then
    let some (ctx', block) := WfRewriter.createBlock ctx types (some (.atEnd region)) hip
      | throw "could not create block"
    set ctx'
    return block
  else throw "invalid body region"

def emitBranch (code : Llvm) (operands : Array ValuePtr) (successors : Array BlockPtr)
    (props : propertiesOf code) (block : BlockPtr) : LowerM Unit := do
  let ctx ← get
  let ip := some (InsertPoint.atEnd block)
  if hv : ∀ v ∈ operands, v.InBounds ctx.raw then
    if hb : ∀ b ∈ successors, b.InBounds ctx.raw then
      if hi : ip.maybe InsertPoint.InBounds ctx.raw then
        let some (ctx', _) := WfRewriter.createOp ctx code #[] operands successors #[] props ip
            hv hb (by simp) hi | throw "could not create branch"
        set ctx'
      else throw "invalid insertion block"
    else throw "invalid branch destination"
  else throw "invalid branch operand"

/-- List the block's results in instruction order. -/
def blockDefinitions (block : BlockPtr) (arg : Nat) :
    List ResolvedInst → List OperationPtr → List ValuePtr
  | [], _ => []
  | .phi .. :: rest, ops =>
    .blockArgument { block, index := arg } :: blockDefinitions block (arg + 1) rest ops
  | .bin _ :: rest, op :: ops =>
    .opResult (op.getResult 0) :: blockDefinitions block arg rest ops
  | .bin .. :: _, [] => []

def lookupValue (values : ValueMap) : LookupValue := fun id => do
  let some value := values id | throw "undefined value"
  return value

/-- Select operands in destination phi order, using the first incoming entry for the source block. -/
def selectPhiInputs (src : BlockId) : List ResolvedInst → Option (List (LLType × ResolvedValue))
  | [] => some []
  | .bin .. :: rest => selectPhiInputs src rest
  | .phi ty incoming :: rest => do
    let value ← incoming.lookup src
    return (ty, value) :: (← selectPhiInputs src rest)

def lowerEdge (f : ResolvedFunction) (blocks : Array BlockPtr) (lookup : LookupValue)
    (block : BlockPtr) (src dst : BlockId) : LowerM (BlockPtr × Array ValuePtr) := do
  let some target := f.blocks[dst]? | throw "invalid branch destination"
  let some ptr := blocks[dst]? | throw "missing branch destination block"
  let some inputs := selectPhiInputs src target.insts | throw "missing phi incoming value"
  let args ← inputs.mapM fun (ty, input) => do
    let arg ← lowerOperand lookup block ty input
    let ctx ← get
    unless arg.getType! ctx.raw == lowerType ty do throw "phi incoming value has the wrong type"
    return arg
  return (ptr, args.toArray)

def lowerTerminator (f : ResolvedFunction) (blocks : Array BlockPtr) (lookup : LookupValue)
    (block : BlockPtr) (src : BlockId) : ResolvedTerminator → LowerM Unit
  | .ret value => do
    let _ ← lowerReturn lookup block f.header.retType value
  | .br dst => do
    let (b, args) ← lowerEdge f blocks lookup block src dst
    emitBranch .br args #[b] { loop_annotation := none } block
  | .condBr c yes no => do
    let x ← lowerOperand lookup block (.int 1) c
    let ctx ← get
    unless x.getType! ctx.raw == lowerType (.int 1) do throw "branch condition must be i1"
    let (y, ys) ← lowerEdge f blocks lookup block src yes
    let (n, ns) ← lowerEdge f blocks lookup block src no
    emitBranch .cond_br (#[x] ++ ys ++ ns) #[y, n]
      { branch_weights := ⟨.signless 32, #[]⟩
        loop_annotation := none
        operandSegmentSizes := ⟨.signless 32, #[1, Int.ofNat ys.size, Int.ofNat ns.size]⟩ } block

def lowerFunction (parent : BlockPtr) (f : ResolvedFunction) : LowerM OperationPtr := do
  StateT.lift (checkBlocks f)
  let inputs := f.header.params.toArray.map (lowerType ·.ty)
  let (region, entry) ← createBody inputs
  let tail ← f.blocks.toList.drop 1 |>.mapM fun b =>
    createBlock region (b.insts.filterMap (fun i => i.phiType.map lowerType)).toArray
  let blocks := (entry :: tail).toArray
  let body := f.blocks.toList.zip blocks.toList
  let plans := body.zipIdx.map fun ((b, block), id) =>
    ⟨block, b.insts.filterMap ResolvedInst.binary, (id, b.terminator)⟩
  let lookup groups :=
    let defs := ((body.zip groups).flatMap fun ((b, block), ops) =>
      blockDefinitions block 0 b.insts ops).toArray
    let values : ValueMap
      | .param i =>
        if i < f.header.params.length then some (.blockArgument { block := entry, index := i }) else none
      | .inst i => defs[i]?
    lookupValue values
  lowerBlocks plans lookup fun values p =>
    lowerTerminator f blocks values p.block p.terminator.1 p.terminator.2
  emit .func #[] #[] #[region]
    { sym_name := ⟨f.header.name.toUTF8⟩
      function_type := { inputs := inputs.map Subtype.val, outputs := #[(lowerType f.header.retType).val] }
      extra := defaultFuncExtra } parent

def lowerModule (m : ResolvedModule) : Except LoweringError (WfIRContext OpCode × OperationPtr) := do
  let some (ctx, root) := createModule | throw "could not create module"
  let some block := (root.getRegion! ctx.raw 0).getFirstBlock! ctx.raw | throw "module has no body block"
  let (_, ctx') ← (m.funcs.forM fun f => do let _ ← lowerFunction block f).run ctx
  return (ctx', root)

abbrev ArgTile := ValuePtr × List OperationPtr

def argPtrs (args : List ArgTile) : Array ValuePtr := (args.map Prod.fst).toArray

def argOps (args : List ArgTile) : List OperationPtr := args.flatMap Prod.snd

def typeOf (ctx : IRContext OpCode) (arg : ValuePtr) : TypeAttr := arg.getType! ctx

def MatchesTermOp (ctx : WfIRContext OpCode) (op : OperationPtr) (code : Llvm)
    (args : Array ValuePtr) (successors : Array BlockPtr) (props : propertiesOf code) : Prop :=
  op.InBounds ctx.raw ∧ op.getProperties! ctx.raw code = props ∧
  (op.getOpType! ctx.raw, op.getResultTypes! ctx.raw, op.getOperands! ctx.raw,
    op.getRegions! ctx.raw, op.getSuccessors! ctx.raw, op.getAttributes! ctx.raw) =
    (ofDialect OpCode code, #[], args, #[], successors, .empty)

def LowersResolvedInstTile (ctx : WfIRContext OpCode) (values : ValueMap) :
    ResolvedInst × Nat → List OperationPtr → Prop
  | (.bin inst, i), tile => LowersInstTile ctx values (.inst i) inst tile
  | (.phi .., _), tile => tile = []

inductive FilterRel {α β : Type} (rel : α → β → Prop) :
    List α → List β → Prop where
  | nil : FilterRel rel [] []
  | keep :
      rel x y →
      FilterRel rel xs ys →
      FilterRel rel (x :: xs) (y :: ys)
  | drop :
      (¬ ∃ y, rel x y) →
      FilterRel rel xs ys →
      FilterRel rel (x :: xs) ys

def PhiPassesArg (ctx : WfIRContext OpCode) (values : ValueMap)
    (src : BlockId) : ResolvedInst → ArgTile → Prop
  | .phi ty incoming, (v, cs) =>
      ∃ input, (src, input) ∈ incoming ∧ OperandTile ctx values ty input v cs
  | _, _ => False

def LowersEdge (ctx : WfIRContext OpCode) (f : ResolvedFunction)
    (blocks : BlockMap) (values : ValueMap) (src dst : BlockId)
    (b : BlockPtr) (args : List ArgTile) : Prop :=
  dst ≠ 0 ∧ blocks dst = some b ∧ ∃ block phis, f.blocks[dst]? = some block ∧
    FilterRel (fun inst phi => inst = phi ∧ inst.phiType ≠ none) block.insts phis ∧
    ResolvesList (fun phi arg => PhiPassesArg ctx values src phi arg ∧
      phi.phiType.map lowerType = some (typeOf ctx.raw arg.1)) phis args

def LowersTerminatorTile (ctx : WfIRContext OpCode) (f : ResolvedFunction)
    (blocks : BlockMap) (values : ValueMap) (src : BlockId) :
    ResolvedTerminator → List OperationPtr → Prop
  | .ret v, tile => ∃ x cs op,
      OperandTile ctx values f.header.retType v x cs ∧
      MatchesTermOp ctx op .return #[x] #[] () ∧ tile = cs ++ [op]
  | .br dst, tile => ∃ b args op,
      LowersEdge ctx f blocks values src dst b args ∧
      MatchesTermOp ctx op .br (argPtrs args) #[b] { loop_annotation := none } ∧
      tile = argOps args ++ [op]
  | .condBr c yes no, tile => ∃ x cs y n ys ns op,
      OperandTile ctx values (.int 1) c x cs ∧
      typeOf ctx.raw x = lowerType (.int 1) ∧
      LowersEdge ctx f blocks values src yes y ys ∧
      LowersEdge ctx f blocks values src no n ns ∧
      MatchesTermOp ctx op .cond_br (#[x] ++ argPtrs ys ++ argPtrs ns) #[y, n]
        { branch_weights := ⟨.signless 32, #[]⟩
          loop_annotation := none
          operandSegmentSizes := ⟨.signless 32, #[1, Int.ofNat ys.length, Int.ofNat ns.length]⟩ } ∧
      tile = cs ++ argOps ys ++ argOps ns ++ [op]

def LowersBlockArgs (ctx : IRContext OpCode) (values : ValueMap)
    (f : ResolvedFunction) (id : BlockId) (insts : List (ResolvedInst × Nat)) (dst : BlockPtr) : Prop :=
  ∃ phis, FilterRel (fun inst phi => inst = phi ∧ inst.1.phiType ≠ none) insts phis ∧
    ResolvesList (fun (inst, i) arg => ∃ ty incoming, inst = .phi ty incoming ∧
      typeOf ctx arg = lowerType ty ∧ values (.inst i) = some arg ∧
      PhiInputsAgree incoming ∧
      ∀ src, incoming.countP (fun pair => pair.1 = src) =
        ((f.blocks[src]?.map (·.terminator.successors)).getD []).count id)
      phis (dst.getArguments! ctx).toList

theorem FilterRel.mem_of_matches (h : FilterRel R xs ys) (hx : x ∈ xs)
    (hm : ∃ y, R x y) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => simp at hx
  | keep hr _ ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨y, hy, hr⟩ := ih hx; exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩
  | drop hn _ ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (hn hm).elim
    · exact ih hx

theorem resolvesList_mem_left (h : ResolvesList R xs ys) (hx : x ∈ xs) :
    ∃ y, R x y := by
  induction h with
  | nil => simp at hx
  | cons hr _ ih => rcases List.mem_cons.mp hx with rfl | hx <;> first | exact ⟨_, hr⟩ | exact ih hx

theorem LowersBlockArgs.phiIncoming {id : BlockId} (h : LowersBlockArgs ctx values f id insts dst)
    (hi : (.phi ty incoming, i) ∈ insts) :
    PhiInputsAgree incoming ∧ ∀ src, incoming.countP (fun pair => pair.1 = src) =
      ((f.blocks[src]?.map (·.terminator.successors)).getD []).count id := by
  obtain ⟨_, hf, hr⟩ := h
  obtain ⟨phi, hp, rfl, _⟩ := hf.mem_of_matches hi ⟨_, rfl, by simp [ResolvedInst.phiType]⟩
  obtain ⟨_, _, _, he, _, _, ha, hc⟩ := resolvesList_mem_left hr hp
  cases he; exact ⟨ha, hc⟩

theorem LowersBlockArgs.checkPhi {id : BlockId}
    (h : LowersBlockArgs ctx values f id (insts.zipIdx offset) dst)
    (ho : insts.Pairwise (fun earlier later => later.phiType ≠ none → earlier.phiType ≠ none))
    (hp : ∀ src, preds.count src = ((f.blocks[src]?.map (·.terminator.successors)).getD []).count id) :
    checkPhi preds insts = .ok () := by
  refine (checkPhi_iff _ _).mpr ⟨ho, fun ty incoming hi => ?_⟩
  obtain ⟨⟨inst, i⟩, hm, rfl⟩ := List.mem_map.mp (by simpa using hi :
    .phi ty incoming ∈ (insts.zipIdx offset).map Prod.fst)
  obtain ⟨ha, hc⟩ := h.phiIncoming hm
  refine ⟨ha, List.perm_iff_count.mpr fun src => ?_⟩
  simpa [List.count_eq_countP, Function.comp_def, Bool.beq_eq_decide_eq] using (hc src).trans (hp src).symm

def LowersBlock (ctx : WfIRContext OpCode) (f : ResolvedFunction)
    (blocks : BlockMap) (values : ValueMap)
    (id : BlockId) (dst : BlockPtr) : Prop :=
  let offset := ((f.blocks.toList.take id).map (·.insts.length)).sum
  ∃ src instTiles termTile,
    f.blocks[id]? = some src ∧
    blocks id = some dst ∧
    src.insts.Pairwise (fun earlier later => later.phiType ≠ none → earlier.phiType ≠ none) ∧
    LowersBlockArgs ctx.raw values f id (src.insts.zipIdx offset) dst ∧
    ResolvesList (LowersResolvedInstTile ctx values) (src.insts.zipIdx offset) instTiles ∧
    LowersTerminatorTile ctx f blocks values id src.terminator termTile ∧
    dst.OpChain ctx.raw (instTiles.flatten ++ termTile).toArray

/-- Entry arguments come from the function signature. All other block arguments come from phis. -/
def LowersEntry (ctx : WfIRContext OpCode) (f : ResolvedFunction)
    (blocks : BlockMap) (values : ValueMap) (dst : BlockPtr) : Prop :=
  ∃ src instTiles termTile,
    f.blocks[0]? = some src ∧ blocks 0 = some dst ∧
    dst.getArgumentTypes! ctx.raw = f.header.params.toArray.map (lowerType ·.ty) ∧
    (∀ i, values (.param i) = (dst.getArguments! ctx.raw)[i]?) ∧
    (∀ inst ∈ src.insts, inst.phiType = none) ∧
    ResolvesList (LowersResolvedInstTile ctx values) src.insts.zipIdx instTiles ∧
    LowersTerminatorTile ctx f blocks values 0 src.terminator termTile ∧
    dst.OpChain ctx.raw (instTiles.flatten ++ termTile).toArray

def LowersFunction (ctx : WfIRContext OpCode) (f : ResolvedFunction) (op : OperationPtr) : Prop :=
  ValidResolvedFunction f ∧
  ∃ (region : RegionPtr) (body : Array BlockPtr) (entry : BlockPtr) (values : ValueMap),
    MatchesOp ctx op Llvm.func #[] #[] #[region]
      (LLVMFuncProperties.mk ⟨f.header.name.toUTF8⟩
        { inputs := f.header.params.toArray.map (fun p => (lowerType p.ty).val)
          outputs := #[(lowerType f.header.retType).val] } defaultFuncExtra) ∧
    region.BlockChain ctx.raw body ∧ body.size = f.blocks.size ∧
    body[0]? = some entry ∧ LowersEntry ctx f (fun i => body[i]?) values entry ∧
    ∀ i dst, i ≠ 0 → body[i]? = some dst → LowersBlock ctx f (fun j => body[j]?) values i dst

/-- The rooted VeIR module contains the lowering of each resolved LLVM function. -/
def LowersModule (ctx : WfIRContext OpCode) (m : ResolvedModule) (root : OperationPtr) : Prop :=
  ∃ (region : RegionPtr) (block : BlockPtr) (funcs : List OperationPtr),
    MatchesOp ctx root Builtin.module #[] #[] #[region] default defaultModuleAttrs ∧
    region.BlockChain ctx.raw #[block] ∧ block.OpChain ctx.raw funcs.toArray ∧
    block.getArgumentTypes! ctx.raw = #[] ∧ ResolvesList (LowersFunction ctx) m.funcs funcs

abbrev equivalent_modulo_renaming := RootedIso

section ModuleCreation

variable {ctx ctx' : WfIRContext OpCode}
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpCode Dialect]
variable {opcode : Dialect} {properties : propertiesOf opcode}

attribute [local simp] StateT.run StateT.bind StateT.get StateT.set StateT.pure StateT.lift
  bind pure get getThe MonadState.get MonadStateOf.get set MonadStateOf.set
  Except.pure Except.bind throw throwThe MonadExceptOf.throw

theorem opChain_createOp_atEnd
    (h : block.OpChain ctx.raw ops)
    (hc : WfRewriter.createOp ctx opcode types operands successors regions properties
      (some (.atEnd block)) ho hs hr hi = some (ctx', op)) :
    block.OpChain ctx'.raw (ops.push op) := by
  have he : Rewriter.createOp ctx.raw opcode types operands successors regions properties
      (some (.atEnd block)) ho hs hr hi (by grind) = some (ctx'.raw, op) := by
    unfold WfRewriter.createOp at hc; split at hc <;> grind
  have hb : block.InBounds ctx'.raw := by grind
  have hl := BlockPtr.operationList_rewriter_createOp (newCtxWf := ctx'.wellFormed) (blockIn := hb) he ctx.wellFormed
  have hold := (BlockPtr.operationList_iff_BlockPtr_OpChain (hctx := ctx.wellFormed) (hblock := h.blockInBounds)).mp h
  apply (BlockPtr.operationList_iff_BlockPtr_OpChain (hctx := ctx'.wellFormed) (hblock := hb)).mpr
  simpa [InsertPoint.block!_atEnd_eq, InsertPoint.idxIn_atEnd_eq, hold] using hl

theorem emitBranch_sound {code : Llvm} {props : propertiesOf code}
    (h : (emitBranch code operands successors props block).run ctx = .ok ((), ctx'))
    (hb : block.OpChain ctx.raw ops) :
    ∃ op, MatchesTermOp ctx' op code operands successors props ∧
      block.OpChain ctx'.raw (ops.push op) := by
  simp [emitBranch] at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  rename_i ho hs hi
  rcases hc : WfRewriter.createOp ctx code #[] operands successors #[] props (some (.atEnd block))
    ho hs (by simp) (by simpa using hi) with _ | ⟨c, op⟩ <;> simp [hc] at h
  obtain rfl : c = ctx' := h
  refine ⟨op, ?_, opChain_createOp_atEnd hb hc⟩
  have hr : op.getRegions! c.raw = #[] := by apply Array.ext <;> grind
  simp only [MatchesTermOp, Prod.mk.injEq]; simp_getset; grind

theorem createOp_matches
    (h : WfRewriter.createOp ctx opcode types operands #[] regions properties ip
      hoper hsucc hregions hins = some (ctx', op)) :
    MatchesOp ctx' op opcode types operands regions properties := by
  have : op.getRegions! ctx'.raw = regions := by
    apply Array.ext <;> grind
  have := WfRewriter.createOp_new_inBounds op h
  simp only [MatchesOp, Prod.mk.injEq]; simp_getset; grind

theorem MatchesOp.createBlock (h : MatchesOp ctx op opcode types operands regions properties attrs)
    (hc : WfRewriter.createBlock ctx ts ip hi = some (ctx', block)) :
    MatchesOp ctx' op opcode types operands regions properties attrs := by
  simp only [MatchesOp, Prod.mk.injEq] at h
  cases ip <;> unfold WfRewriter.createBlock Rewriter.createBlock at hc <;> simp only [Option.bind_eq_bind, Option.bind, pure] at hc
  all_goals have hr : op.getRegions! ctx'.raw = op.getRegions! ctx.raw := by apply Array.ext <;> grind (gen := 20)
  all_goals simp only [MatchesOp, Prod.mk.injEq] at *; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals grind (gen := 20) [OperationPtr.getProperties!, OperationPtr.getAttributes!]

theorem blockChain_singleton {r : RegionPtr} {b : BlockPtr} (hr : r.InBounds ctx.raw)
    (hf : r.getFirstBlock! ctx.raw = some b) (hl : r.getLastBlock! ctx.raw = some b) : r.BlockChain ctx.raw #[b] := by
  obtain ⟨bs, hb⟩ := ctx.wellFormed.blockChain r hr
  have hinj := RegionPtr.BlockChain_array_injective hb 0 (bs.size - 1)
  have hs : bs = #[b] := by apply Array.ext <;> grind
  simpa [hs] using hb

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

end ModuleCreation

theorem lowerModule_empty_sound (h : lowerModule ⟨[]⟩ = .ok (ctx, root)) :
    LowersModule ctx ⟨[]⟩ root := by
  rcases hc : createModule with _ | ⟨c, r⟩
  · simp [lowerModule, hc] at h
  obtain ⟨region, b, hm, hb, ho, _, ha⟩ := createModule_sound hc
  have hb' : (r.getRegion! c.raw 0).getFirstBlock! c.raw = some b := by
    rw [← OperationPtr.getRegions!.getElem!_eq_getRegion!]
    simpa [show r.getRegions! c.raw = #[region] by grind [MatchesOp]] using hb.first
  have he : c = ctx ∧ r = root := by
    simpa [lowerModule, hc, hb', List.forM, StateT.run, pure, StateT.pure, Except.map, bind,
      Except.bind, Except.pure] using h
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨region, b, [], hm, hb, ho, ha, .nil⟩

theorem lowerModule_correct : LowersModule ctx m root ↔
    ∃ ctx₂ root₂, lowerModule m = .ok (ctx₂, root₂) ∧
      equivalent_modulo_renaming ctx root ctx₂ root₂ := by
  sorry

/-- Placeholder for recovering a resolved module, including branches and phis. -/
def reverseModule (_ : WfIRContext OpCode) (_ : OperationPtr) :
    Except LoweringError ResolvedModule := by
  sorry

theorem reverseModule_lowerModule {m : ResolvedModule}
    (_ : ∀ f ∈ m.funcs, ValidResolvedFunction f) :
    ∃ m', (lowerModule m >>= reverseModule.uncurry) = .ok m' ∧ m'.Equiv m := by
  sorry

def IncomingPhiArg (src : BlockId) : ResolvedInst → LLType × ResolvedValue → Prop
  | .phi ty incoming, (t, value) => ty = t ∧ (src, value) ∈ incoming
  | _, _ => False

theorem selectPhiInputs_sound (h : selectPhiInputs src insts = some inputs) :
    ∃ phis, FilterRel (fun inst phi => inst = phi ∧ inst.phiType ≠ none) insts phis ∧
      ResolvesList (IncomingPhiArg src) phis inputs := by
  induction insts generalizing inputs with
  | nil => cases h; exact ⟨[], .nil, .nil⟩
  | cons inst rest ih =>
    cases inst with
    | bin => obtain ⟨phis, hf, hr⟩ := ih h; exact ⟨phis, .drop (by simp [ResolvedInst.phiType]) hf, hr⟩
    | phi ty incoming =>
      obtain ⟨v, hv, tail, ht, rfl⟩ := by simpa [selectPhiInputs, Option.bind_eq_some_iff] using h
      obtain ⟨phis, hf, hr⟩ := ih ht
      obtain ⟨_, _, rfl, _⟩ := List.lookup_eq_some_iff.mp hv
      exact ⟨_, .keep ⟨rfl, by simp [ResolvedInst.phiType]⟩ hf, .cons ⟨rfl, by simp⟩ hr⟩

theorem selectPhiInputs_complete
    (h : FilterRel (fun inst phi => inst = phi ∧ inst.phiType ≠ none) insts phis)
    (hm : ResolvesList (IncomingPhiArg src) phis inputs)
    (ha : ∀ ty incoming, .phi ty incoming ∈ insts → PhiInputsAgree incoming) :
    selectPhiInputs src insts = some inputs := by
  induction h generalizing inputs with
  | nil => cases hm; rfl
  | @keep x y xs ys hxy _ ih =>
    obtain ⟨rfl, hx⟩ := hxy
    cases x with
    | bin => exact (hx rfl).elim
    | phi ty incoming =>
      cases hm with
      | @cons _ input _ _ hi ht =>
        rcases input with ⟨_, _⟩
        obtain ⟨rfl, hv⟩ := hi
        simp [selectPhiInputs, (ha ty incoming List.mem_cons_self).lookup_eq_some_iff.mpr hv,
          ih ht (fun ty incoming hmem => ha ty incoming (List.mem_cons_of_mem _ hmem))]
  | @drop x xs ys hn _ ih =>
    cases x with
    | bin => exact ih hm (fun ty incoming hmem => ha ty incoming (List.mem_cons_of_mem _ hmem))
    | phi => exact (hn ⟨_, rfl, by simp [ResolvedInst.phiType]⟩).elim

theorem IncomingPhiArg.passes {inst : ResolvedInst} {input : LLType × ResolvedValue}
    {arg : ArgTile} (h : IncomingPhiArg src inst input)
    (hv : OperandTile ctx values input.1 input.2 arg.1 arg.2) :
    PhiPassesArg ctx values src inst arg := by
  rcases input with ⟨ty, value⟩; rcases arg with ⟨ptr, cs⟩
  cases inst with
  | bin => exact False.elim h
  | phi => obtain ⟨rfl, hm⟩ := h; exact ⟨value, hm, hv⟩

theorem phiPassesArg_list {ctx : WfIRContext OpCode} {values : ValueMap}
    (h : ResolvesList (IncomingPhiArg src) phis inputs)
    (ht : ResolvesList (fun input arg => OperandTile ctx values input.1 input.2 arg.1 arg.2 ∧
      lowerType input.1 = typeOf ctx.raw arg.1) inputs args) :
    ResolvesList (fun phi arg => PhiPassesArg ctx values src phi arg ∧
      phi.phiType.map lowerType = some (typeOf ctx.raw arg.1)) phis args := by
  induction h generalizing args with
  | nil => cases ht; exact .nil
  | cons h _ ih =>
    cases ht with
    | cons hv ht =>
      refine .cons ⟨h.passes hv.1, ?_⟩ (ih ht)
      cases ‹ResolvedInst› <;> simp_all [IncomingPhiArg, ResolvedInst.phiType]

end Veir.LLVMLowering
