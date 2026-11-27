import Veir.IR.RootedIso
import Veir.Parser.NameResolutionSketch
import Veir.Parser.DecidableInBounds
import Veir.Parser.LoweringInitial
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

def functionValues (f : ResolvedFunction) (entry : BlockPtr)
    (blocks : List (ResolvedBlock × BlockPtr)) (groups : List (List OperationPtr)) : ValueMap :=
  let defs := ((blocks.zip groups).flatMap fun ((b, block), ops) =>
    blockDefinitions block 0 b.insts ops).toArray
  fun
    | .param i => if i < f.header.params.length then some (.blockArgument ⟨entry, i⟩) else none
    | .inst i => defs[i]?

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
  let lookup groups := lookupValue (functionValues f entry body groups)
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

def instructionType : ResolvedInst → LLType
  | .bin (.bin _ ty _ _) | .phi ty _ => ty

def binaryType : ResolvedBinary → LLType
  | .bin _ ty _ _ => ty

def allocatedResult (op : OperationPtr) : ValuePtr := .opResult (op.getResult 0)

theorem blockDefinitions_map_typeOf {raw : IRContext OpCode} {block : BlockPtr}
    {insts : List ResolvedInst} {ops : List OperationPtr} {arg : Nat}
    (hops : ops.map (fun op => typeOf raw (allocatedResult op)) =
      (insts.filterMap ResolvedInst.binary).map (lowerType ∘ binaryType))
    (hargs : ∀ j (ty : LLType), (insts.filterMap ResolvedInst.phiType)[j]? = some ty →
      typeOf raw (.blockArgument ⟨block, arg + j⟩) = lowerType ty) :
    (blockDefinitions block arg insts ops).map (typeOf raw) =
      insts.map (lowerType ∘ instructionType) := by
  induction insts generalizing ops arg with
  | nil => rfl
  | cons inst rest ih =>
    cases inst with
    | bin bin =>
      cases ops with
      | nil => simp [ResolvedInst.binary] at hops
      | cons op tail =>
        obtain ⟨ht, hs⟩ := by simpa [ResolvedInst.binary] using hops
        change _ = List.map _ _ at hs
        have htail := ih (arg := arg) hs (by simpa [List.filterMap_cons, ResolvedInst.phiType] using hargs)
        cases bin
        simpa [blockDefinitions, instructionType, binaryType, allocatedResult, htail] using ht
    | phi ty incoming =>
      have h0 := hargs 0 ty rfl
      have htail := ih (arg := arg + 1) (by simpa [List.filterMap_cons, ResolvedInst.binary] using hops)
        (fun j t hj => by simpa [Nat.add_assoc, Nat.add_comm j 1] using hargs (j + 1) t hj)
      simpa [blockDefinitions, instructionType, htail] using h0

theorem blockDefinitions_inBounds {raw : IRContext OpCode} {block : BlockPtr}
    {insts : List ResolvedInst} {ops : List OperationPtr} {arg : Nat}
    (hops : ∀ op ∈ ops, (allocatedResult op).InBounds raw)
    (hargs : ∀ j, j < (insts.filterMap ResolvedInst.phiType).length →
      (ValuePtr.blockArgument ⟨block, arg + j⟩).InBounds raw) :
    ∀ v ∈ blockDefinitions block arg insts ops, v.InBounds raw := by
  induction insts generalizing ops arg with
  | nil => simp [blockDefinitions]
  | cons inst rest ih =>
    cases inst with
    | bin =>
      cases ops with
      | nil => simp [blockDefinitions]
      | cons op tail =>
        simp only [blockDefinitions, List.forall_mem_cons]
        exact ⟨hops _ List.mem_cons_self, ih (fun o h => hops o (List.mem_cons_of_mem _ h))
          (by simpa [List.filterMap_cons, ResolvedInst.phiType] using hargs)⟩
    | phi =>
      simp only [blockDefinitions, List.forall_mem_cons]
      refine ⟨by simpa using hargs 0 (by simp [ResolvedInst.phiType]), ih hops (fun j hj => ?_)⟩
      simpa [Nat.add_assoc, Nat.add_comm j 1] using hargs (j + 1) (by simpa [ResolvedInst.phiType] using hj)

theorem functionValues_param {ctx : IRContext OpCode}
    (ht : entry.getArgumentTypes! ctx = f.header.params.toArray.map (lowerType ·.ty)) :
    functionValues f entry blocks groups (.param i) = (entry.getArguments! ctx)[i]? := by
  by_cases hi : i < f.header.params.length <;>
    simp [functionValues, BlockPtr.getArguments!, BlockPtr.getArgument,
      ← BlockPtr.getArgumentTypes!.size_eq_getNumArguments!, ht, hi]


theorem blockDefinitions_typeOf_zip {ctx : IRContext OpCode}
    {blocks : List (ResolvedBlock × BlockPtr)} {groups : List (List OperationPtr)}
    (h : ResolvesList (fun (b, block) ops =>
      (blockDefinitions block 0 b.insts ops).map (typeOf ctx) =
        b.insts.map (lowerType ∘ instructionType)) blocks groups) :
    ((blocks.zip groups).flatMap fun ((b, block), ops) =>
      blockDefinitions block 0 b.insts ops).map (typeOf ctx) =
      (blocks.flatMap (·.1.insts)).map (lowerType ∘ instructionType) := by
  induction h with
  | nil => rfl
  | @cons x ops xs groups h _ ih =>
    rcases x with ⟨b, block⟩
    simp [h, ih]

theorem functionValues_inst_type {ctx : IRContext OpCode}
    {blocks : List (ResolvedBlock × BlockPtr)} {groups : List (List OperationPtr)}
    (hf : blocks.map Prod.fst = f.blocks.toList)
    (h : ResolvesList (fun (b, block) ops =>
      (blockDefinitions block 0 b.insts ops).map (typeOf ctx) =
        b.insts.map (lowerType ∘ instructionType)) blocks groups) :
    (functionValues f entry blocks groups (.inst i)).map (typeOf ctx) =
      (f.valueType (.inst i)).map lowerType := by
  have ht := blockDefinitions_typeOf_zip h
  have hblocks : blocks.flatMap (·.1.insts) = f.blocks.toList.flatMap (·.insts) := by
    rw [← hf, List.flatMap_map]
  rw [hblocks] at ht
  have ht' := congrArg (fun ts : List TypeAttr => ts[i]?) ht
  have he : (f.valueType (.inst i)) = ((f.blocks.toList.flatMap (·.insts))[i]?).map instructionType := rfl
  simpa [functionValues, he, Function.comp_def] using ht'

theorem functionValues_param_type {ctx : IRContext OpCode}
    (ht : entry.getArgumentTypes! ctx = f.header.params.toArray.map (lowerType ·.ty)) :
    (functionValues f entry blocks groups (.param i)).map (typeOf ctx) =
      (f.valueType (.param i)).map lowerType := by
  rw [functionValues_param ht]
  have hs : entry.getNumArguments! ctx = f.header.params.length := by
    simp [← BlockPtr.getArgumentTypes!.size_eq_getNumArguments!, ht]
  by_cases hi : i < f.header.params.length
  · have he : i < entry.getNumArguments! ctx := by simpa [hs] using hi
    have hg := congrArg (fun a : Array TypeAttr => a[i]!) ht
    rw [BlockPtr.getArgumentTypes!.getElem!_eq_getArgument he] at hg
    simpa [BlockPtr.getArguments!, hs, hi, ResolvedFunction.valueType, typeOf] using hg
  · simp [BlockPtr.getArguments!, hs, hi, ResolvedFunction.valueType]

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

section ControlFlowValidation

def addPredecessor (src dst : BlockId) (preds : Array (List BlockId)) :
    Except LoweringError (Array (List BlockId)) := do
  if dst == 0 then throw "branch to the entry block"
  let some prev := preds[dst]? | throw "invalid branch destination"
  return preds.set! dst (src :: prev)

def collectBlockPredecessors (blocks : List (ResolvedBlock × BlockId)) (initial : Array (List BlockId)) :
    Except LoweringError (Array (List BlockId)) :=
  blocks.foldlM (fun preds (block, src) => block.terminator.successors.foldlM (fun p dst =>
    addPredecessor src dst p) preds) initial

theorem forIn_foldlM_yield (xs : List α) (a : β) (f : β → α → Except LoweringError β) :
    forIn xs a (fun x b => ForInStep.yield <$> f b x) = xs.foldlM f a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => cases h : f a x <;> simp [h] <;> exact ih _

theorem liftPredecessor_yield (p : Array (List BlockId)) (src dst : BlockId) :
    (do
      if dst == 0 then throw "branch to the entry block"
      let some prev := p[dst]? | do
        throw "invalid branch destination"
        return ForInStep.yield p
      return ForInStep.yield (p.set! dst (src :: prev))) =
      ForInStep.yield <$> addPredecessor src dst p := by
  by_cases hd : dst = 0 <;> cases hp : p[dst]? <;>
    simp [addPredecessor, hd, hp, Except.bind, Except.pure, pure, throw, throwThe, MonadExceptOf.throw, bind] <;> rfl

theorem collectBlockPredecessors_eq (xs : List (ResolvedBlock × BlockId)) (p : Array (List BlockId)) :
    (do
      let mut preds := p
      for (block, src) in xs do
        for dst in block.terminator.successors do
          if dst == 0 then throw "branch to the entry block"
          let some prev := preds[dst]? | throw "invalid branch destination"
          preds := preds.set! dst (src :: prev)
      pure preds) = collectBlockPredecessors xs p := by
  unfold collectBlockPredecessors
  rw [← forIn_foldlM_yield]
  simp only [bind_pure]
  congr 1
  funext x q; rcases x with ⟨block, src⟩
  rw [← forIn_foldlM_yield, map_eq_pure_bind]
  apply congrArg (fun m : Except LoweringError (Array (List BlockId)) => m >>= fun r => pure (ForInStep.yield r))
  exact congrArg (forIn block.terminator.successors q) (funext fun dst => funext fun p => liftPredecessor_yield p src dst)

theorem checkPhi_forM_eq (xs : List (ResolvedBlock × BlockId)) (p : Array (List BlockId)) :
    (do
      for (block, id) in xs do
        checkPhi p[id]! block.insts : Except LoweringError Unit) =
      xs.forM (fun (block, id) => checkPhi p[id]! block.insts) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨block, id⟩
    cases h : checkPhi p[id]! block.insts <;> simp [List.forM, Except.bind, Except.pure, pure, bind, h]
    exact ih

theorem checkBlocks_eq (f : ResolvedFunction) :
    checkBlocks f = (do
      let some entry := f.blocks[0]? | throw "function has no entry block"
      if entry.insts.any (·.phiType.isSome) then throw "phi in entry block"
      let preds ← collectBlockPredecessors f.blocks.toList.zipIdx (f.blocks.map fun _ => [])
      f.blocks.toList.zipIdx.forM fun (block, id) => checkPhi preds[id]! block.insts) := by
  unfold checkBlocks
  cases h : f.blocks[0]? with
  | none => rfl
  | some entry =>
    by_cases he : (entry.insts.any (·.phiType.isSome)) = true
    · simp [he]; rfl
    simp only [he, ← collectBlockPredecessors_eq, bind_assoc, pure_bind]
    exact bind_congr (fun preds => checkPhi_forM_eq _ preds)


theorem addPredecessor_ok {src dst : BlockId} {p q : Array (List BlockId)} :
    addPredecessor src dst p = .ok q ↔
      dst ≠ 0 ∧ dst < p.size ∧ q = p.set! dst (src :: p[dst]!) := by
  by_cases hd : dst = 0 <;> by_cases hi : dst < p.size <;>
    simp [addPredecessor, hd, hi, throw, throwThe, MonadExceptOf.throw,
      Except.pure, Except.bind, pure, bind] <;> grind

theorem addPredecessor_count {src dst : BlockId} {p q : Array (List BlockId)}
    (h : addPredecessor src dst p = .ok q) (i s : BlockId) :
    q[i]!.count s = p[i]!.count s + if dst = i ∧ src = s then 1 else 0 := by
  obtain ⟨_, hi, rfl⟩ := addPredecessor_ok.mp h
  by_cases hd : dst = i
  · subst i
    rw [Array.getElem!_set!_self _ _ _ hi]
    by_cases hs : src = s <;> simp [hs]
  · rw [Array.getElem!_set!_ne _ _ _ _ hd]
    simp [hd]

theorem addPredecessor_size {src dst : BlockId} {p q : Array (List BlockId)}
    (h : addPredecessor src dst p = .ok q) : q.size = p.size :=
  (addPredecessor_ok.mp h).2.2 ▸ Array.size_set! _ _ _

theorem foldSuccessors_ok (ds : List BlockId) (p : Array (List BlockId)) (src : BlockId) :
    (∃ q, ds.foldlM (fun q dst => addPredecessor src dst q) p = .ok q) ↔
    ∀ dst ∈ ds, dst ≠ 0 ∧ dst < p.size := by
  induction ds generalizing p with
  | nil => simp [List.foldlM, Except.pure, pure]
  | cons dst ds ih =>
    simp only [List.foldlM_cons, Except.bind_eq_ok, List.forall_mem_cons]
    constructor
    · rintro ⟨q, r, hr, hq⟩
      exact ⟨⟨(addPredecessor_ok.mp hr).1, (addPredecessor_ok.mp hr).2.1⟩,
        addPredecessor_size hr ▸ (ih r).mp ⟨q, hq⟩⟩
    · rintro ⟨⟨hn, hi⟩, ht⟩
      have hr := (addPredecessor_ok (src := src)).mpr ⟨hn, hi, rfl⟩
      obtain ⟨q, hq⟩ := (ih (p.set! dst (src :: p[dst]!))).mpr (by simpa using ht)
      exact ⟨q, _, hr, hq⟩

theorem foldSuccessors_shape {ds : List BlockId} {p q : Array (List BlockId)} {src : BlockId}
    (h : ds.foldlM (fun r dst => addPredecessor src dst r) p = .ok q) (i s : BlockId) :
    q.size = p.size ∧ q[i]!.count s = p[i]!.count s + if src = s then ds.count i else 0 := by
  induction ds generalizing p with
  | nil => simp_all [List.foldlM, Except.pure, pure]
  | cons dst ds ih =>
    obtain ⟨r, hr, hq⟩ := Except.bind_eq_ok.mp h
    obtain ⟨hs, hc⟩ := ih hq
    refine ⟨hs.trans (addPredecessor_size hr), ?_⟩
    rw [hc, addPredecessor_count hr]
    by_cases ht : src = s <;> by_cases hd : dst = i <;>
      simp [ht, hd, Nat.add_assoc, Nat.add_comm]


theorem collectBlockPredecessors_shape {xs : List (ResolvedBlock × BlockId)}
    {p q : Array (List BlockId)} (h : collectBlockPredecessors xs p = .ok q) (i s : BlockId) :
    q.size = p.size ∧ q[i]!.count s = p[i]!.count s +
      (xs.map fun (block, src) => if src = s then block.terminator.successors.count i else 0).sum := by
  induction xs generalizing p with
  | nil => simp_all [collectBlockPredecessors, Except.pure, pure]
  | cons x xs ih =>
    obtain ⟨r, hr, hq⟩ := Except.bind_eq_ok.mp h
    obtain ⟨hs, hc⟩ := ih hq
    obtain ⟨hs', hc'⟩ := foldSuccessors_shape (src := x.2) hr i s
    exact ⟨hs.trans hs', by simp [hc, hc', Nat.add_assoc]⟩

theorem collectBlockPredecessors_ok (xs : List (ResolvedBlock × BlockId)) (p : Array (List BlockId)) :
    (∃ q, collectBlockPredecessors xs p = .ok q) ↔
      ∀ x ∈ xs, ∀ dst ∈ x.1.terminator.successors, dst ≠ 0 ∧ dst < p.size := by
  induction xs generalizing p with
  | nil => simp [collectBlockPredecessors, Except.pure, pure]
  | cons x xs ih =>
    simp only [collectBlockPredecessors, List.foldlM_cons, Except.bind_eq_ok, List.forall_mem_cons]
    constructor
    · rintro ⟨q, r, hr, hq⟩
      exact ⟨(foldSuccessors_ok _ _ _).mp ⟨r, hr⟩,
        (foldSuccessors_shape hr 0 0).1 ▸ (ih r).mp ⟨q, hq⟩⟩
    · rintro ⟨hh, ht⟩
      obtain ⟨r, hr⟩ := (foldSuccessors_ok _ _ _).mpr hh
      obtain ⟨q, hq⟩ := (ih r).mpr (by rw [(foldSuccessors_shape hr 0 0).1]; exact ht)
      exact ⟨q, r, hr, hq⟩

theorem sum_zipIdx_eq_getElem {xs : List α} (g : α → Nat) (k s : Nat) :
    (xs.zipIdx k |>.map fun (a, idx) => if idx = s then g a else 0).sum =
      if k ≤ s then (xs[s - k]?.map g).getD 0 else 0 := by
  induction xs generalizing k with
  | nil => simp
  | cons x xs ih =>
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, ih]
    rcases Nat.lt_trichotomy s k with h | rfl | h
    · simp [Nat.not_le_of_gt h, show ¬ k + 1 ≤ s by omega, show k ≠ s by omega]
    · simp [show ¬ s + 1 ≤ s by omega]
    · obtain ⟨n, hn⟩ : ∃ n, s - k = n + 1 := ⟨s - (k + 1), by omega⟩
      simp [Nat.ne_of_lt h, show k + 1 ≤ s by omega, show k ≤ s by omega, hn,
        show s - (k + 1) = n by omega]

theorem collectBlockPredecessors_count {f : ResolvedFunction} {p : Array (List BlockId)}
    (h : collectBlockPredecessors f.blocks.toList.zipIdx (f.blocks.map fun _ => []) = .ok p)
    (i s : BlockId) :
    p[i]!.count s = ((f.blocks[s]?.map (·.terminator.successors)).getD []).count i := by
  have hc := (collectBlockPredecessors_shape h i s).2
  rw [sum_zipIdx_eq_getElem (xs := f.blocks.toList) (fun b => b.terminator.successors.count i) 0 s] at hc
  have hz : (f.blocks.map fun _ => ([] : List BlockId))[i]! = [] := by
    by_cases hi : i < f.blocks.size <;> simp [hi] <;> rfl
  cases hs : f.blocks[s]? <;> simpa [hz, hs] using hc


theorem forM_except_ok (xs : List α) (k : α → Except ε Unit) :
    xs.forM k = .ok () ↔ ∀ x ∈ xs, k x = .ok () := by
  induction xs with
  | nil => simp [List.forM, Except.pure, pure]
  | cons x xs ih => cases h : k x <;> simp [List.forM, h, Except.bind, bind] <;> exact ih

theorem checkBlocks_accepts {f : ResolvedFunction} {entry : ResolvedBlock}
    (he : f.blocks[0]? = some entry) (hentry : ∀ i ∈ entry.insts, i.phiType = none)
    (hd : ∀ b ∈ f.blocks.toList, ∀ dst ∈ b.terminator.successors, dst ≠ 0 ∧ dst < f.blocks.size)
    (hp : ∀ b id, (b, id) ∈ f.blocks.toList.zipIdx →
      b.insts.Pairwise (fun earlier later => later.phiType ≠ none → earlier.phiType ≠ none) ∧
      ∀ ty incoming, ResolvedInst.phi ty incoming ∈ b.insts →
        PhiInputsAgree incoming ∧ HasPredEdges f id (incoming.map Prod.fst)) :
    checkBlocks f = .ok () := by
  have hno : entry.insts.any (·.phiType.isSome) = false := by simpa [List.any_eq_false] using hentry
  have hdst x (hx : x ∈ f.blocks.toList.zipIdx) := hd _ (List.fst_mem_of_mem_zipIdx hx)
  obtain ⟨p, hq⟩ := (collectBlockPredecessors_ok f.blocks.toList.zipIdx (f.blocks.map fun _ => [])).mpr (by simpa using hdst)
  simp [checkBlocks_eq, he, hno, hq, Except.bind, bind]
  apply (forM_except_ok _ _).mpr
  rintro ⟨b, id⟩ hb
  obtain ⟨ho, hp⟩ := hp b id hb
  refine (checkPhi_iff _ _).mpr ⟨ho, fun ty incoming hi => ?_⟩
  obtain ⟨ha, hc⟩ := hp ty incoming hi
  exact ⟨ha, List.perm_iff_count.mpr fun src => (hc src).trans (by cases hs : f.blocks[src]? <;> simp [hs, collectBlockPredecessors_count hq id src])⟩


theorem LowersEdge.validDestination (h : LowersEdge ctx f blocks values src dst b args) :
    dst ≠ 0 ∧ dst < f.blocks.size := by
  obtain ⟨hn, _, block, _, hb, _, _⟩ := h
  exact ⟨hn, (Array.getElem?_eq_some_iff.mp hb).choose⟩

theorem LowersTerminatorTile.validDestinations {t : ResolvedTerminator}
    (h : LowersTerminatorTile ctx f blocks values src t tile) :
    ∀ dst ∈ t.successors, dst ≠ 0 ∧ dst < f.blocks.size := by
  cases t with
  | ret => simp [ResolvedTerminator.successors]
  | br =>
    obtain ⟨_, _, _, he, _, _⟩ := h
    simpa [ResolvedTerminator.successors] using he.validDestination
  | condBr =>
    obtain ⟨_, _, _, _, _, _, _, _, _, hy, hn, _, _⟩ := h
    simpa [ResolvedTerminator.successors] using ⟨hy.validDestination, hn.validDestination⟩

theorem LowersBlockArgs.phiPredEdges {insts : List ResolvedInst} {id offset : Nat}
    (h : LowersBlockArgs ctx values f id (insts.zipIdx offset) dst)
    (hi : ResolvedInst.phi ty incoming ∈ insts) :
    PhiInputsAgree incoming ∧ HasPredEdges f id (incoming.map Prod.fst) := by
  obtain ⟨⟨inst, i⟩, hm, rfl⟩ := List.mem_map.mp (by simpa using hi :
    .phi ty incoming ∈ (insts.zipIdx offset).map Prod.fst)
  obtain ⟨ha, hc⟩ := h.phiIncoming hm
  refine ⟨ha, fun src => ?_⟩
  cases hs : f.blocks[src]? <;>
    simpa [hs, List.count_eq_countP, Function.comp_def, Bool.beq_eq_decide_eq] using hc src

theorem LowersFunction.checkBlocks (h : LowersFunction ctx f op) : checkBlocks f = .ok () := by
  obtain ⟨_, _, body, _, values, _, _, hs, _, hl, ht⟩ := h
  obtain ⟨block, _, _, hb, _, _, _, hnone, _, hterm, _⟩ := hl
  have blockSpec (b : ResolvedBlock) (id : Nat) (hm : (b, id) ∈ f.blocks.toList.zipIdx) (hn : id ≠ 0) :
      ∃ dst, LowersBlock ctx f (fun j => body[j]?) values id dst := by
    have hin : id < body.size := by simpa [hs] using (List.mem_zipIdx' hm).1
    exact ⟨body[id], ht _ _ hn (Array.getElem?_eq_getElem hin)⟩
  refine checkBlocks_accepts hb hnone ?_ ?_
  · intro b hm
    obtain ⟨⟨b', id⟩, hz, h⟩ := List.mem_map.mp (by simpa using hm : b ∈ f.blocks.toList.zipIdx.map Prod.fst)
    change b' = b at h; subst b'
    have hget : f.blocks[id]? = some b := by simpa using List.mk_mem_zipIdx_iff_getElem?.mp hz
    rcases Nat.eq_zero_or_pos id with rfl | hn
    · obtain rfl := Option.some.inj (hget.symm.trans hb); exact hterm.validDestinations
    obtain ⟨_, b', _, _, hb', _, _, _, _, hterm, _⟩ := blockSpec b id hz (Nat.ne_of_gt hn)
    obtain rfl := Option.some.inj (hget.symm.trans hb'); exact hterm.validDestinations
  · intro b id hm
    have hget : f.blocks[id]? = some b := by simpa using List.mk_mem_zipIdx_iff_getElem?.mp hm
    rcases Nat.eq_zero_or_pos id with rfl | hn
    · obtain rfl := Option.some.inj (hget.symm.trans hb)
      exact ⟨List.pairwise_iff_getElem.mpr fun _ _ _ hj _ h => (h (hnone _ (List.getElem_mem hj))).elim,
        fun ty incoming hi => ((hnone _ hi).symm ▸ (by simp : (some ty : Option LLType) ≠ none)) rfl |>.elim⟩
    obtain ⟨_, b', _, _, hb', _, ho, ha, _, _, _⟩ := blockSpec b id hm (Nat.ne_of_gt hn)
    obtain rfl := Option.some.inj (hget.symm.trans hb')
    exact ⟨ho, fun _ _ hi => ha.phiPredEdges hi⟩


theorem checkBlocks_accepts_iff {f : ResolvedFunction} :
    checkBlocks f = .ok () ↔
    (∃ entry, f.blocks[0]? = some entry ∧ ∀ i ∈ entry.insts, i.phiType = none) ∧
    (∀ b ∈ f.blocks.toList, ∀ dst ∈ b.terminator.successors, dst ≠ 0 ∧ dst < f.blocks.size) ∧
    ∀ b id, (b, id) ∈ f.blocks.toList.zipIdx →
      b.insts.Pairwise (fun earlier later => later.phiType ≠ none → earlier.phiType ≠ none) ∧
      ∀ ty incoming, ResolvedInst.phi ty incoming ∈ b.insts →
        PhiInputsAgree incoming ∧ HasPredEdges f id (incoming.map Prod.fst) := by
  refine ⟨?_, fun ⟨⟨entry, he, hn⟩, hd, hp⟩ => checkBlocks_accepts he hn hd hp⟩
  rw [checkBlocks_eq]
  cases he : f.blocks[0]? with
  | none => simp [throw, throwThe, MonadExceptOf.throw]
  | some e =>
    by_cases hn : e.insts.any (·.phiType.isSome)
    · simp [hn, throw, throwThe, MonadExceptOf.throw, Except.bind, bind]
    simp only [hn, Bool.false_eq_true, ite_false, Except.bind_eq_ok]
    rintro ⟨p, hq, hf⟩
    have hdst := (collectBlockPredecessors_ok _ _).mp ⟨p, hq⟩
    refine ⟨⟨e, rfl, by simpa [List.any_eq_false] using hn⟩, ?_, ?_⟩
    · intro b hb
      obtain ⟨⟨b', id⟩, hm, hr⟩ := List.mem_map.mp (by simpa using hb : b ∈ f.blocks.toList.zipIdx.map Prod.fst)
      change b' = b at hr; subst b'
      simpa using hdst (b, id) hm
    · intro b id hb
      obtain ⟨ho, hp⟩ := (checkPhi_iff _ _).mp ((forM_except_ok _ _).mp hf (b, id) hb)
      refine ⟨ho, fun ty incoming hi => ?_⟩
      obtain ⟨ha, hc⟩ := hp ty incoming hi
      exact ⟨ha, fun src => (List.perm_iff_count.mp hc src).trans (by cases hs : f.blocks[src]? <;> simp [hs, collectBlockPredecessors_count hq id src])⟩

end ControlFlowValidation

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

section IsomorphismTransport
variable {ctx₁ ctx₂ : WfIRContext OpCode}
variable {D : Type} [HasOpInfo D] [HasDialect OpCode D] {code : D} {props : propertiesOf code}

def totalMap [Inhabited β] (f : α → Option β) (a : α) : β := (f a).getD default

theorem array_mapM_map {f : α → Option β} {g : α → β} {xs : Array α} {ys : Array β}
    (hf : ∀ a b, f a = some b → g a = b) (h : xs.mapM f = some ys) : xs.map g = ys := by
  have hs := Array.size_eq_of_mapM_eq_some h
  apply Array.ext (by simpa using hs)
  intro i hi hj
  simpa using hf _ _ (Array.mapM_option_eq_some_implies h i hj)

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

theorem array_mapM_defined [Inhabited β] {f : α → Option β} {xs : Array α} {ys : Array β}
    (h : xs.mapM f = some ys) (ha : a ∈ xs) : f a = some (totalMap f a) := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp ha
  have hj := (Array.size_eq_of_mapM_eq_some h) ▸ hi
  simp [totalMap, Array.mapM_option_eq_some_implies h i hj]

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
def mappedValues (φ : OperationPtr → Option OperationPtr) (β : BlockPtr → Option BlockPtr) (values : ValueMap) : ValueMap :=
  fun id => (values id).map (renameValue (totalMap φ) (totalMap β))

theorem OperandTile.map
    (hop : ∀ o o', φ o = some o' → OperationAgrees ctx₁ ctx₂ root φ ρ β o o')
    (h : OperandTile ctx₁ values ty value v cs)
    (hdefs : ∀ o ∈ cs, φ o = some (totalMap φ o)) :
    OperandTile ctx₂ (mappedValues φ β values) ty value (renameValue (totalMap φ) (totalMap β) v) (cs.map (totalMap φ)) := by
  cases value with
  | ref id => obtain ⟨hv, rfl⟩ := h; exact ⟨by simp [mappedValues, hv], rfl⟩
  | intConst n =>
    cases ty; obtain ⟨c, rfl, rfl, hc⟩ := h
    refine ⟨totalMap φ c, rfl, by simp [renameValue, OperationPtr.getResult], ?_⟩
    simpa using hc.map (hop _ _ (hdefs c (by simp)))

theorem LowersInstTile.map {id : ValueId}
    (hop : ∀ o o', φ o = some o' → OperationAgrees ctx₁ ctx₂ root φ ρ β o o')
    (h : LowersInstTile ctx₁ values id inst tile)
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

theorem MatchesTermOp.map {code : Llvm} {props : propertiesOf code} (h : MatchesTermOp ctx₁ o code vs bs props)
    (he : OperationAgrees ctx₁ ctx₂ root φ ρ β o o') :
    MatchesTermOp ctx₂ o' code (vs.map (renameValue (totalMap φ) (totalMap β)))
      (bs.map (totalMap β)) props := by
  rcases he with ⟨_, hi, hp, hl, hv, hb, hr, _⟩
  have hvs := array_mapM_map (fun _ _ => renameValue_total) hv
  have hbs := array_mapM_map (g := totalMap β) (fun a b h => by simp [totalMap, h]) hb
  have hrs := array_mapM_map (g := totalMap ρ) (fun a b h => by simp [totalMap, h]) hr
  have hprops := properties_eq_of_global (code := code) (congrArg Prod.fst hl) hp
  simp only [MatchesTermOp, Prod.mk.injEq] at *
  grind

theorem mappedBlockArguments (ha : b'.getArgumentTypes! ctx₂.raw = b.getArgumentTypes! ctx₁.raw)
    (hb : β b = some b') :
    (b.getArguments! ctx₁.raw).map (renameValue (totalMap φ) (totalMap β)) =
      b'.getArguments! ctx₂.raw := by
  have hn := congrArg Array.size ha
  simp only [BlockPtr.getArgumentTypes!.size_eq_getNumArguments!] at hn
  simp [BlockPtr.getArguments!, BlockPtr.getArgument, totalMap, hb, hn, renameValue, Function.comp_def]

theorem mappedBodyLookup {body body' : Array BlockPtr} {i : Nat} (hb : body.mapM β = some body') :
    body'[i]? = (body[i]?).map (totalMap β) := by
  rw [← array_mapM_map (g := totalMap β) (fun a b h => by simp [totalMap, h]) hb]
  simp

theorem typeOf_rename
    (hop : ∀ o o', φ o = some o' → OperationAgrees ctx₁ ctx₂ root φ ρ β o o')
    (hblock : ∀ b b', β b = some b' → BlockAgrees ctx₁ ctx₂ φ ρ b b')
    (hv : renameValue? φ β v = some v') (hin : v.InBounds ctx₁.raw) :
    typeOf ctx₂.raw v' = typeOf ctx₁.raw v := by
  cases v with
  | opResult r =>
    rcases r with ⟨op, i⟩
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp hv
    have ht := congrArg (fun a => a.2.1) (hop _ _ ho).2.2.2.1
    change op.getResultTypes! ctx₁.raw = o.getResultTypes! ctx₂.raw at ht
    have hs := congrArg Array.size ht
    have hi : i < op.getNumResults! ctx₁.raw := OpResultPtr.inBounds_OperationPtr_getNumResults! ⟨op, i⟩ _ (by simpa using hin)
    have hi' : i < o.getNumResults! ctx₂.raw := by grind
    change (o.getResult i).getType! ctx₂.raw = (op.getResult i).getType! ctx₁.raw
    rw [← OperationPtr.getResultTypes!.getElem!_eq hi', ← OperationPtr.getResultTypes!.getElem!_eq hi, ht]
  | blockArgument a =>
    rcases a with ⟨block, i⟩
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hv
    have ht := (hblock _ _ hb).2.2.1
    change block.getArgumentTypes! ctx₁.raw = b.getArgumentTypes! ctx₂.raw at ht
    have hs := congrArg Array.size ht
    have hi : i < block.getNumArguments! ctx₁.raw := by
      obtain ⟨hb, hi⟩ := BlockArgumentPtr.inBounds_def.mp (by simpa using hin : (BlockArgumentPtr.mk block i).InBounds ctx₁.raw)
      simpa [BlockPtr.getNumArguments!_eq_getNumArguments hb] using hi
    have hi' : i < b.getNumArguments! ctx₂.raw := by grind
    change (b.getArgument i).getType! ctx₂.raw = (block.getArgument i).getType! ctx₁.raw
    rw [← BlockPtr.getArgumentTypes!.getElem!_eq_getArgument hi', ← BlockPtr.getArgumentTypes!.getElem!_eq_getArgument hi, ht]


theorem renameValue?_some (h : ∃ v', renameValue? φ β v = some v') :
    renameValue? φ β v = some (renameValue (totalMap φ) (totalMap β) v) := by
  obtain ⟨_, he⟩ := h
  rw [renameValue_total he, he]

theorem array_mapM_exists_of_mem [Inhabited γ] {f : α → Option γ} {xs : Array α}
    (h : xs.mapM f = some ys) (hx : x ∈ xs) : ∃ y, f x = some y :=
  ⟨_, array_mapM_defined h hx⟩


def renameArgTile (φ : OperationPtr → Option OperationPtr) (β : BlockPtr → Option BlockPtr)
    (arg : ArgTile) : ArgTile :=
  (renameValue (totalMap φ) (totalMap β) arg.1, arg.2.map (totalMap φ))

@[simp]
theorem argPtrs_map {args : List ArgTile} :
    argPtrs (args.map (renameArgTile φ β)) =
      (argPtrs args).map (renameValue (totalMap φ) (totalMap β)) := by
  simp [argPtrs, renameArgTile, Function.comp_def]

@[simp]
theorem argOps_map {args : List ArgTile} :
    argOps (args.map (renameArgTile φ β)) = (argOps args).map (totalMap φ) := by
  simp [argOps, renameArgTile, List.map_flatMap, List.flatMap_map]

theorem typeOf_operand_map
    (hop : ∀ o o', φ o = some o' → OperationAgrees ctx₁ ctx₂ root φ ρ β o o')
    (hblock : ∀ b b', β b = some b' → BlockAgrees ctx₁ ctx₂ φ ρ b b')
    (h : OperationAgrees ctx₁ ctx₂ root φ ρ β o o')
    (hv : v ∈ o.getOperands! ctx₁.raw) :
    typeOf ctx₂.raw (renameValue (totalMap φ) (totalMap β) v) = typeOf ctx₁.raw v :=
  typeOf_rename hop hblock (renameValue?_some (array_mapM_exists_of_mem h.2.2.2.2.1 hv))
    (OperationPtr.getOperands!_inBounds ctx₁.wellFormed.inBounds h.1 hv)

theorem LowersEdge.map {blocks : BlockMap}
    (h : LowersEdge ctx₁ f blocks values src dst b args)
    (hop : ∀ o o', φ o = some o' → OperationAgrees ctx₁ ctx₂ root φ ρ β o o')
    (hd : ∀ o ∈ argOps args, φ o = some (totalMap φ o))
    (ht : ∀ a ∈ args, typeOf ctx₂.raw (renameArgTile φ β a).1 = typeOf ctx₁.raw a.1) :
    LowersEdge ctx₂ f (fun i => (blocks i).map (totalMap β)) (mappedValues φ β values)
      src dst (totalMap β b) (args.map (renameArgTile φ β)) := by
  obtain ⟨hn, hb, block, phis, he, hf, hl⟩ := h
  refine ⟨hn, by simp [hb], block, phis, he, hf, resolvesList_map_right hl ?_⟩
  intro inst arg ha hp
  rcases inst with _ | ⟨ty, incoming⟩
  · exact False.elim hp.1
  · obtain ⟨input, hi, hv⟩ := hp.1
    exact ⟨⟨input, hi, hv.map hop (fun o ho => hd o (List.mem_flatMap.mpr ⟨arg, ha, ho⟩))⟩,
      (ht _ ha).symm ▸ hp.2⟩

theorem LowersTerminatorTile.map {blocks : BlockMap} {term : ResolvedTerminator}
    (h : LowersTerminatorTile ctx₁ f blocks values src term tile)
    (hop : ∀ o o', φ o = some o' → OperationAgrees ctx₁ ctx₂ root φ ρ β o o')
    (hblock : ∀ b b', β b = some b' → BlockAgrees ctx₁ ctx₂ φ ρ b b')
    (hd : ∀ o ∈ tile, φ o = some (totalMap φ o)) :
    LowersTerminatorTile ctx₂ f (fun i => (blocks i).map (totalMap β)) (mappedValues φ β values)
      src term (tile.map (totalMap φ)) := by
  cases term with
  | ret =>
    obtain ⟨x, cs, op, hx, ho, rfl⟩ := h
    exact ⟨_, _, _, hx.map hop (fun o hm => hd o (by simp [hm])), by simpa using ho.map (hop _ _ (hd op (by simp))), by simp⟩
  | br =>
    obtain ⟨b, args, op, he, ho, rfl⟩ := h
    have ha := hop _ _ (hd op (by simp))
    have ht : op.getOperands! ctx₁.raw = argPtrs args := by grind [MatchesTermOp]
    refine ⟨_, _, totalMap φ op, he.map hop (fun o hm => hd o (by simp [hm])) (fun a hm => typeOf_operand_map hop hblock ha ?_), ?_, by simp⟩
    · simp [ht, argPtrs, List.mem_map_of_mem hm]
    · simpa using ho.map ha
  | condBr =>
    obtain ⟨x, cs, y, n, ys, ns, op, hx, ht, hy, hn, ho, rfl⟩ := h
    have ha := hop _ _ (hd op (by simp))
    have hv : op.getOperands! ctx₁.raw = #[x] ++ argPtrs ys ++ argPtrs ns := by grind [MatchesTermOp]
    refine ⟨_, _, totalMap β y, totalMap β n, ys.map (renameArgTile φ β), ns.map (renameArgTile φ β), totalMap φ op, hx.map hop (fun o hm => hd o (by simp [hm])), (typeOf_operand_map hop hblock ha (by simp [hv])).trans ht, ?_, ?_, ?_, by simp [List.map_append]⟩
    · exact hy.map hop (fun o hm => hd o (by simp [hm])) (fun a hm => typeOf_operand_map hop hblock ha (by simp [hv, argPtrs, List.mem_map_of_mem hm]))
    · exact hn.map hop (fun o hm => hd o (by simp [hm])) (fun a hm => typeOf_operand_map hop hblock ha (by simp [hv, argPtrs, List.mem_map_of_mem hm]))
    · simpa using ho.map ha


theorem LowersBlockArgs.map {id : BlockId} {insts : List (ResolvedInst × Nat)}
    (h : LowersBlockArgs ctx₁.raw values f id insts b)
    (hop : ∀ o o', φ o = some o' → OperationAgrees ctx₁ ctx₂ root φ ρ β o o')
    (hblock : ∀ b b', β b = some b' → BlockAgrees ctx₁ ctx₂ φ ρ b b')
    (hb : β b = some b') :
    LowersBlockArgs ctx₂.raw (mappedValues φ β values) f id insts b' := by
  obtain ⟨phis, hphis, hargs⟩ := h
  have htypes := (hblock _ _ hb).2.2.1
  unfold LowersBlockArgs
  rw [← mappedBlockArguments (φ := φ) htypes.symm hb, Array.toList_map]
  refine ⟨phis, hphis, resolvesList_map_right hargs ?_⟩
  rintro ⟨inst, i⟩ arg ha ⟨ty, incoming, rfl, ht, hv, hagree, hc⟩
  obtain ⟨a, rfl⟩ := BlockArgumentPtr.exists_blockArgument_of_mem_getArguments! (by simpa using ha)
  have hin := BlockPtr.getArguments!_inBounds ctx₁.wellFormed.inBounds (hblock _ _ hb).1 (by simpa using ha)
  have hab := (BlockArgumentPtr.block_of_mem_getArguments! (by simpa using hin)).mpr (by simpa using ha)
  have hr := typeOf_rename hop hblock (renameValue?_some ⟨.blockArgument ⟨b', a.index⟩, by simp [renameValue?, hab, hb]⟩) hin
  exact ⟨ty, incoming, rfl, hr.trans ht, by simp [mappedValues, hv], hagree, hc⟩

theorem mapOpChain {ops : List OperationPtr}
    (ha : BlockAgrees ctx₁ ctx₂ φ ρ b b') (hc : b.OpChain ctx₁.raw ops.toArray) :
    b'.OpChain ctx₂.raw (ops.map (totalMap φ)).toArray ∧
    ∀ o ∈ ops, φ o = some (totalMap φ o) := by
  obtain ⟨os, hos, hc'⟩ := ha.2.2.2.2 _ hc
  have he := array_mapM_map (g := totalMap φ) (fun a b h => by simp [totalMap, h]) hos
  exact ⟨by simpa only [← List.map_toArray, he] using hc', fun o ho => array_mapM_defined hos (by simpa using ho)⟩

theorem mapInstTiles {insts : List (ResolvedInst × Nat)}
    (h : ResolvesList (LowersResolvedInstTile ctx₁ values) insts tiles)
    (hop : ∀ o o', φ o = some o' → OperationAgrees ctx₁ ctx₂ root φ ρ β o o')
    (hd : ∀ o ∈ tiles.flatten, φ o = some (totalMap φ o)) :
    ResolvesList (LowersResolvedInstTile ctx₂ (mappedValues φ β values)) insts
      (tiles.map (List.map (totalMap φ))) := by
  refine resolvesList_map_right h ?_
  rintro ⟨inst, i⟩ tile hm hi
  cases inst with
  | bin => exact LowersInstTile.map hop hi (fun o ho => hd o (List.mem_flatten.mpr ⟨tile, hm, ho⟩))
  | phi => simpa [LowersResolvedInstTile] using congrArg (List.map (totalMap φ)) (show tile = [] from hi)

theorem LowersBlock.map {id : BlockId} {blocks : BlockMap}
    (h : LowersBlock ctx₁ f blocks values id b)
    (hop : ∀ o o', φ o = some o' → OperationAgrees ctx₁ ctx₂ root φ ρ β o o')
    (hblock : ∀ b b', β b = some b' → BlockAgrees ctx₁ ctx₂ φ ρ b b') (hb : β b = some b') :
    LowersBlock ctx₂ f (fun i => (blocks i).map (totalMap β)) (mappedValues φ β values) id b' := by
  obtain ⟨src, tiles, term, hs, he, ho, ha, hi, ht, hc⟩ := h
  obtain ⟨hc', hd⟩ := mapOpChain (hblock _ _ hb) hc
  refine ⟨src, tiles.map (List.map (totalMap φ)), term.map (totalMap φ), hs, by simp [he, totalMap, hb],
    ho, ha.map hop hblock hb, mapInstTiles hi hop (fun o hm => hd o (by simp [hm])),
    ht.map hop hblock (fun o hm => hd o (by simp [hm])), ?_⟩
  simpa [List.map_flatten, List.map_append] using hc'

theorem LowersEntry.map {blocks : BlockMap}
    (h : LowersEntry ctx₁ f blocks values b)
    (hop : ∀ o o', φ o = some o' → OperationAgrees ctx₁ ctx₂ root φ ρ β o o')
    (hblock : ∀ b b', β b = some b' → BlockAgrees ctx₁ ctx₂ φ ρ b b') (hb : β b = some b') :
    LowersEntry ctx₂ f (fun i => (blocks i).map (totalMap β)) (mappedValues φ β values) b' := by
  obtain ⟨src, tiles, term, hs, he, ha, hp, ho, hi, ht, hc⟩ := h
  obtain ⟨hc', hd⟩ := mapOpChain (hblock _ _ hb) hc
  have htypes := (hblock _ _ hb).2.2.1.symm
  refine ⟨src, tiles.map (List.map (totalMap φ)), term.map (totalMap φ), hs, by simp [he, totalMap, hb],
    htypes.trans ha, fun i => ?_, ho, mapInstTiles hi hop (fun o hm => hd o (by simp [hm])),
    ht.map hop hblock (fun o hm => hd o (by simp [hm])), by simpa [List.map_flatten, List.map_append] using hc'⟩
  simp [mappedValues, hp, ← mappedBlockArguments (φ := φ) htypes hb]


theorem MatchesOp.regions_eq (h : MatchesOp ctx₁ o code ts vs rs props attrs) :
    o.getRegions! ctx₁.raw = rs := by grind [MatchesOp]

theorem LowersFunction.map (h : LowersFunction ctx₁ f o)
    (hop : ∀ o o', φ o = some o' → OperationAgrees ctx₁ ctx₂ root φ ρ β o o')
    (hreg : ∀ r r', ρ r = some r' → RegionAgrees ctx₁ ctx₂ φ β r r')
    (hblock : ∀ b b', β b = some b' → BlockAgrees ctx₁ ctx₂ φ ρ b b') (hm : φ o = some o') :
    LowersFunction ctx₂ f o' := by
  obtain ⟨hv, r, bs, entry, values, hf, hc, hs, he, hl, ht⟩ := h
  have ha := hop _ _ hm
  have hr := (mapM_singleton (show #[r].mapM ρ = some (o'.getRegions! ctx₂.raw) by simpa only [hf.regions_eq] using ha.2.2.2.2.2.2.1)).1
  obtain ⟨bs', hm', hc'⟩ := (hreg _ _ hr).2.2.2 _ hc
  have hlookup : ∀ i : Nat, bs'[i]? = (bs[i]?).map (totalMap β) := fun _ => mappedBodyLookup hm'
  have he' := array_mapM_defined hm' (Array.mem_of_getElem? he)
  refine ⟨hv, totalMap ρ r, bs', totalMap β entry, mappedValues φ β values, by simpa using hf.map ha, hc', ?_, by simp [hlookup, he], ?_, ?_⟩
  · exact (Array.size_eq_of_mapM_eq_some hm').symm.trans hs
  · simpa only [hlookup] using hl.map hop hblock he'
  · intro i dst hi hd; obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp ((hlookup i).symm.trans hd)
    simpa only [hlookup] using (ht i b hi hb).map hop hblock (array_mapM_defined hm' (Array.mem_of_getElem? hb))

theorem LowersModule.of_iso (h : LowersModule ctx₁ m root) (his : RootedIso ctx₁ root ctx₂ root') :
    LowersModule ctx₂ m root' := by
  obtain ⟨φ, ρ, β, _, _, _, hm, hop, hreg, hblock⟩ := his
  obtain ⟨r, b, fs, hf, hb, hc, ha, hfs⟩ := h
  have he := hop _ _ hm
  have hr := (mapM_singleton (show #[r].mapM ρ = some (root'.getRegions! ctx₂.raw) by simpa only [hf.regions_eq] using he.2.2.2.2.2.2.1)).1
  obtain ⟨bs, hbs, hc'⟩ := (hreg _ _ hr).2.2.2 _ hb
  obtain ⟨hd, rfl⟩ := mapM_singleton hbs
  obtain ⟨hc'', hdefs⟩ := mapOpChain (hblock _ _ hd) hc
  exact ⟨totalMap ρ r, totalMap β b, fs.map (totalMap φ), by simpa using hf.map he, hc', hc'',
    (hblock _ _ hd).2.2.1.symm.trans ha, resolvesList_map_right hfs (fun _ op hm' hh => hh.map hop hreg hblock (hdefs op hm'))⟩


end Map

theorem MatchesOp.properties_eq (h₁ : MatchesOp ctx₁ o₁ code ts₁ vs₁ rs₁ props as₁)
    (h₂ : MatchesOp ctx₂ o₂ code ts₂ vs₂ rs₂ props as₂) (c : OpCode) :
    o₁.getProperties! ctx₁.raw c = o₂.getProperties! ctx₂.raw c := by
  simp only [MatchesOp, Prod.mk.injEq] at h₁ h₂
  unfold OperationPtr.getOpType! at h₁ h₂
  unfold OperationPtr.getProperties! at *
  grind [HasDialect.ofDialectProperties_toDialectProperties]

theorem MatchesOp.singletonRegion_parent (hm : MatchesOp ctx₁ op code ts vs #[r] props attrs)
    (hr : r.InBounds ctx₁.raw) : r.getParent! ctx₁.raw = some op := by
  apply ((ctx₁.wellFormed.operations op hm.1).region_parent r hr).mp
  refine ⟨0, ?_, ?_⟩
  · simp [← OperationPtr.getRegions!.size_eq_getNumRegions!, hm.regions_eq]
  · rw [← OperationPtr.getRegions!.getElem!_eq_getRegion!, hm.regions_eq]
    rfl

theorem lowersModule_empty_iso
    (h₁ : LowersModule ctx₁ ⟨[]⟩ root₁) (h₂ : LowersModule ctx₂ ⟨[]⟩ root₂) :
    RootedIso ctx₁ root₁ ctx₂ root₂ := by
  obtain ⟨r, b, _, hm, hr, hb, ha, hf⟩ := h₁
  obtain ⟨r', b', _, hm', hr', hb', ha', hf'⟩ := h₂
  cases hf
  cases hf'
  let φ := fun o => if o = root₁ then some root₂ else none
  let ρ := fun s => if s = r then some r' else none
  let β := fun z => if z = b then some b' else none
  refine ⟨φ, ρ, β, ?_, ?_, ?_, by simp [φ], ?_, ?_, ?_⟩
  · simp [PartialInjective, φ]
  · simp [PartialInjective, ρ]
  · simp [PartialInjective, β]
  · intro o o' ho
    have h : o = root₁ ∧ o' = root₂ := by grind
    obtain ⟨he, he'⟩ := h
    subst o o'
    have hs : root₁.getSuccessors! ctx₁.raw = #[] ∧ root₂.getSuccessors! ctx₂.raw = #[] := by
      simp only [MatchesOp, Prod.mk.injEq] at hm hm'
      exact ⟨Array.eq_empty_of_size_eq_zero (by grind), Array.eq_empty_of_size_eq_zero (by grind)⟩
    have hp := hm.properties_eq hm'
    simp only [MatchesOp, Prod.mk.injEq] at hm hm'
    refine ⟨hm.1, hm'.1, hp, by grind, ?_, ?_, ?_, by simp⟩
    · simp [show root₁.getOperands! ctx₁.raw = #[] by grind, show root₂.getOperands! ctx₂.raw = #[] by grind]
    · simp [hs.1, hs.2]
    · simp [show root₁.getRegions! ctx₁.raw = #[r] by grind, show root₂.getRegions! ctx₂.raw = #[r'] by grind, ρ, Array.mapM_eq_mapM_toList]
  · intro s s' hs
    have h : s = r ∧ s' = r' := by grind
    obtain ⟨he, he'⟩ := h
    subst s s'
    have hp := hm.singletonRegion_parent hr.inBounds
    have hp' := hm'.singletonRegion_parent hr'.inBounds
    refine ⟨hr.inBounds, hr'.inBounds, by simp [hp, hp', φ], fun bs hbs => ?_⟩
    obtain rfl := RegionPtr.BlockChain_unique hbs hr
    exact ⟨#[b'], by simp [β, Array.mapM_eq_mapM_toList], hr'⟩
  · intro z z' hz
    have h : z = b ∧ z' = b' := by grind
    obtain ⟨he, he'⟩ := h
    subst z z'
    have hp : b.getParent! ctx₁.raw = some r := hr.opParent (by simp)
    have hp' : b'.getParent! ctx₂.raw = some r' := hr'.opParent (by simp)
    refine ⟨hb.blockInBounds, hb'.blockInBounds, ha.trans ha'.symm, by simp [hp, hp', ρ], fun os hos => ?_⟩
    obtain rfl := BlockPtr.OpChain_unique hos hb
    exact ⟨#[], by simp, hb'⟩

end IsomorphismTransport

theorem lowerModule_empty_total : ∃ ctx root, lowerModule ⟨[]⟩ = .ok (ctx, root) := by
  obtain ⟨ctx, root, hc, _⟩ := createModule_total
  obtain ⟨region, block, hmodule, hblocks, _, _, _⟩ := createRawModule_sound hc
  have hi := hmodule.1
  have he : createModule = some (WfRewriter.setAttributes ctx root defaultModuleAttrs hi, root) := by
    simp [createModule, hc, hi]
  have hbody : (root.getRegion! ctx.raw 0).getFirstBlock! ctx.raw = some block := by
    rw [← OperationPtr.getRegions!.getElem!_eq_getRegion!, hmodule.regions_eq]
    simpa using hblocks.first
  exact ⟨WfRewriter.setAttributes ctx root defaultModuleAttrs hi, root, by simp [lowerModule, he, hbody, List.forM, StateT.run, pure, StateT.pure,
    bind, Except.bind, Except.pure]⟩

theorem lowerModule_empty_correct : LowersModule ctx ⟨[]⟩ root ↔
    ∃ ctx₂ root₂, lowerModule ⟨[]⟩ = .ok (ctx₂, root₂) ∧
      equivalent_modulo_renaming ctx root ctx₂ root₂ := by
  constructor
  · intro h
    obtain ⟨ctx₂, root₂, he⟩ := lowerModule_empty_total
    exact ⟨ctx₂, root₂, he, lowersModule_empty_iso h (lowerModule_empty_sound he)⟩
  · rintro ⟨_, _, he, hi⟩
    exact (lowerModule_empty_sound he).of_iso hi.symm

/-- Follow a linked list with a bound from the owning context. -/
def collectLoweredChain (next : α → Option α) (fuel : Nat) (first : Option α) :
    Except LoweringError (List α) :=
  loop fuel first []
where
  loop : Nat → Option α → List α → Except LoweringError (List α)
    | _, none, acc => .ok acc.reverse
    | 0, some _, _ => .error "invalid lowered IR chain"
    | fuel + 1, some ptr, acc => loop fuel (next ptr) (ptr :: acc)

def reverseRegion (ctx : IRContext OpCode) (op : OperationPtr) : Except LoweringError (List BlockPtr) :=
  match (op.getRegions! ctx).toList with
  | [region] => collectLoweredChain (·.getNextBlock! ctx) ctx.blocks.size (region.getFirstBlock! ctx)
  | _ => .error "expected a single region"

def reverseBlockOps (ctx : IRContext OpCode) (block : BlockPtr) : Except LoweringError (List OperationPtr) :=
  collectLoweredChain (·.getNextOp! ctx) ctx.operations.size (block.getFirstOp! ctx)

def reverseIntType : Attribute → Except LoweringError LLType
  | .integerType ⟨width, .signless⟩ => .ok (.int width)
  | _ => .error "expected a signless integer type"

def reverseBinOp : OpCode → Option BinOp
  | .llvm .and => some .and
  | .llvm .or => some .or
  | .llvm .xor => some .xor
  | _ => none

/-- Assign IDs before decoding any operands, including references around loops. -/
def reverseValueIds (ctx : IRContext OpCode) (entry : BlockPtr)
    (blocks : List (BlockPtr × List OperationPtr)) : Std.HashMap ValuePtr ValueId :=
  let params := (entry.getArguments! ctx).toList.zipIdx
  let defs := blocks.flatMap fun (block, ops) =>
    (if block = entry then [] else (block.getArguments! ctx).toList) ++
      (ops.filterMap fun op => (reverseBinOp (op.getOpType! ctx)).map fun _ => .opResult (op.getResult 0))
  Std.HashMap.ofList (params.map (fun (ptr, i) => (ptr, .param i)) ++
    defs.zipIdx.map (fun (ptr, i) => (ptr, .inst i)))

def reverseOperand (ctx : IRContext OpCode) (ids : Std.HashMap ValuePtr ValueId)
    (ptr : ValuePtr) : Except LoweringError ResolvedValue := do
  if let some id := ids[ptr]? then return .ref id
  let .opResult result := ptr | throw "unknown lowered operand"
  unless result.index == 0 && result.op.getOpType! ctx == .llvm .mlir__constant do
    throw "unknown lowered result"
  let .integer attr := (result.op.getProperties! ctx Llvm.mlir__constant).value
    | throw "expected an integer constant"
  return .intConst attr.value

def reverseBinary (ctx : IRContext OpCode) (val : ValuePtr → Except LoweringError ResolvedValue)
    (op : OperationPtr) (bin : BinOp) : Except LoweringError ResolvedInst := do
  let [ty] := (op.getResultTypes! ctx).toList | throw "expected one binary result"
  let [lhs, rhs] := (op.getOperands! ctx).toList | throw "expected two binary operands"
  if bin == .or && (op.getProperties! ctx Llvm.or).disjoint then
    throw "unsupported disjoint flag"
  return .bin (.bin bin (← reverseIntType ty.val) (← val lhs) (← val rhs))

/-- A decoded edge carries the destination and one incoming value per destination phi. -/
abbrev ReverseEdge := BlockId × Array ResolvedValue

def reverseEdge (ctx : IRContext OpCode) (blockIds : Std.HashMap BlockPtr BlockId)
    (val : ValuePtr → Except LoweringError ResolvedValue) (dst : BlockPtr) (args : List ValuePtr) :
    Except LoweringError ReverseEdge := do
  let some id := blockIds[dst]? | throw "branch to a block outside the function"
  if id == 0 then throw "branch to the entry block"
  unless args.length == (dst.getArguments! ctx).size do throw "wrong number of phi inputs"
  return (id, (← args.mapM val).toArray)

def reverseTerminator (ctx : IRContext OpCode) (blockIds : Std.HashMap BlockPtr BlockId)
    (val : ValuePtr → Except LoweringError ResolvedValue) (op : OperationPtr) :
    Except LoweringError (ResolvedTerminator × List ReverseEdge) := do
  let operands := (op.getOperands! ctx).toList
  let successors := (op.getSuccessors! ctx).toList
  match op.getOpType! ctx, operands, successors with
  | .llvm .return, [v], [] => return (.ret (← val v), [])
  | .llvm .br, args, [dst] =>
    let e ← reverseEdge ctx blockIds val dst args
    return (.br e.1, [e])
  | .llvm .cond_br, cond :: args, [yes, no] =>
    let yesCount := (yes.getArguments! ctx).size
    let sizes := (op.getProperties! ctx Llvm.cond_br).operandSegmentSizes.values
    unless sizes == #[1, Int.ofNat yesCount, Int.ofNat ((no.getArguments! ctx).size)] do
      throw "invalid conditional branch operand segments"
    let yesEdge ← reverseEdge ctx blockIds val yes (args.take yesCount)
    let noEdge ← reverseEdge ctx blockIds val no (args.drop yesCount)
    return (.condBr (← val cond) yesEdge.1 noEdge.1, [yesEdge, noEdge])
  | _, _, _ => throw "unsupported or malformed terminator"

/-- Decode one non-terminator op: binary ops are instructions, constants live in their operands. -/
def reverseInst (ctx : IRContext OpCode) (val : ValuePtr → Except LoweringError ResolvedValue)
    (op : OperationPtr) : Except LoweringError (Option ResolvedInst) :=
  match reverseBinOp (op.getOpType! ctx) with
  | some bin => some <$> reverseBinary ctx val op bin
  | none => if op.getOpType! ctx == .llvm .mlir__constant then pure none
            else throw "unsupported instruction in lowered block"

def reverseBlock (ctx : IRContext OpCode) (blockIds : Std.HashMap BlockPtr BlockId)
    (val : ValuePtr → Except LoweringError ResolvedValue) (ops : List OperationPtr) :
    Except LoweringError (List ResolvedInst × ResolvedTerminator × List ReverseEdge) := do
  let term :: reversedInsts := ops.reverse | throw "block has no terminator"
  let insts ← reversedInsts.reverse.filterMapM (reverseInst ctx val)
  let (terminator, edges) ← reverseTerminator ctx blockIds val term
  return (insts, terminator, edges)

/-- The edges into `dst`, in source block order. -/
def incomingEdges (edges : List (List ReverseEdge)) (dst : BlockId) : List (BlockId × Array ResolvedValue) :=
  edges.zipIdx.flatMap fun (es, src) => (es.filter (·.1 == dst)).map fun (_, values) => (src, values)

/-- The input a decoded edge passes to the destination's `i`th phi. -/
def reversePhiInput (i : Nat) (edge : BlockId × Array ResolvedValue) :
    Except LoweringError (BlockId × ResolvedValue) := do
  let some v := edge.2[i]? | throw "missing phi input"
  return (edge.1, v)

/-- One phi per block argument, taking its input from each incoming edge. -/
def reversePhis (ctx : IRContext OpCode) (block : BlockPtr) (preds : List (BlockId × Array ResolvedValue)) :
    Except LoweringError (List ResolvedInst) :=
  (block.getArgumentTypes! ctx).toList.zipIdx.mapM fun (ty, i) => do
    let inputs ← preds.mapM (reversePhiInput i)
    return ResolvedInst.phi (← reverseIntType ty.val) inputs

def reverseFunction (ctx : IRContext OpCode) (op : OperationPtr) : Except LoweringError ResolvedFunction := do
  unless op.getOpType! ctx == .llvm .func do throw "expected an LLVM function"
  let props := op.getProperties! ctx Llvm.func
  let some name := String.fromUTF8? props.sym_name.value | throw "invalid LLVM function name"
  let [result] := props.function_type.outputs.toList | throw "expected one function result"
  let retType ← reverseIntType result
  let paramTypes ← props.function_type.inputs.toList.mapM reverseIntType
  let params := paramTypes.zipIdx.map fun (ty, i) => Param.mk ty (ValueId.sourceName (.param i))
  let blocks ← reverseRegion ctx op
  let entry :: _ := blocks | throw "function has no entry block"
  unless (entry.getArgumentTypes! ctx).toList.map Subtype.val == props.function_type.inputs.toList do
    throw "entry block arguments do not match the function type"
  let blockIds := Std.HashMap.ofList blocks.zipIdx
  let body ← blocks.mapM fun block => do return (block, ← reverseBlockOps ctx block)
  let val := reverseOperand ctx (reverseValueIds ctx entry body)
  let decoded ← body.mapM fun (_, ops) => reverseBlock ctx blockIds val ops
  let edges := decoded.map (·.2.2)
  let resultBlocks ← (blocks.zip decoded).zipIdx.mapM fun ((block, insts, terminator, _), dst) => do
    let phis ← if dst == 0 then pure [] else reversePhis ctx block (incomingEdges edges dst)
    return ResolvedBlock.mk (phis ++ insts) terminator
  return ⟨⟨retType, name, params⟩, resultBlocks.toArray⟩

/-- Recover the integer LLVM fragment, listing phi inputs in predecessor block and edge order. -/
def reverseModule (ctx : WfIRContext OpCode) (root : OperationPtr) : Except LoweringError ResolvedModule := do
  let raw := ctx.raw
  unless raw.operations.contains root do throw "invalid module root"
  unless root.getOpType! raw == .builtin .module do throw "expected a builtin module"
  let [body] ← reverseRegion raw root | throw "expected a single module body block"
  let funcs ← reverseBlockOps raw body
  return ⟨← funcs.mapM (reverseFunction raw)⟩

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
        simp [selectPhiInputs, (PhiInputsAgree.lookup_eq_some_iff (ha ty incoming List.mem_cons_self)).mpr hv,
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

section LoweringConstruction

variable {ctx ctx' ctx'' : WfIRContext OpCode}

theorem getRegions_createOp_eq {code : Llvm} {props : propertiesOf code}
    (h : WfRewriter.createOp ctx code ts vs bs rs props ip ho hb hr hi = some (ctx', fresh))
    (hn : op ≠ fresh) : op.getRegions! ctx'.raw = op.getRegions! ctx.raw := by
  apply Array.ext <;> grind

theorem MatchesOp.createOp {D : Type} [HasOpInfo D] [HasDialect OpCode D]
    {opcode : D} {properties : propertiesOf opcode} {code : Llvm} {props : propertiesOf code}
    (hm : MatchesOp ctx op opcode types operands regions properties attrs)
    (hc : WfRewriter.createOp ctx code ts vs bs rs props ip ho hb hr hi = some (ctx', fresh)) :
    MatchesOp ctx' op opcode types operands regions properties attrs := by
  have hn : op ≠ fresh := fun he => WfRewriter.createOp_new_not_inBounds fresh hc (he ▸ hm.1)
  have hregions := getRegions_createOp_eq hc hn
  simp only [MatchesOp, Prod.mk.injEq] at *; simp_getset; grind

theorem MatchesTermOp.createOp {code newCode : Llvm}
    {props : propertiesOf code} {newProps : propertiesOf newCode}
    (hm : MatchesTermOp ctx op code args succs props)
    (hc : WfRewriter.createOp ctx newCode ts vs bs rs newProps ip ho hb hr hi = some (ctx', fresh)) :
    MatchesTermOp ctx' op code args succs props := by
  have hn : op ≠ fresh := fun he => WfRewriter.createOp_new_not_inBounds fresh hc (he ▸ hm.1)
  have hregions := getRegions_createOp_eq hc hn
  simp only [MatchesTermOp, Prod.mk.injEq] at *; simp_getset; grind

/-- Observations that survive a sequence of lowering mutations. -/
structure LoweringFrame (ctx ctx' : WfIRContext OpCode)
    (writes : List OperationPtr) (inserts : List BlockPtr) (extended : List RegionPtr) : Prop where
  bounds : ∀ p : GenericPtr, p.InBounds ctx.raw → p.InBounds ctx'.raw
  valueTypes : ∀ v : ValuePtr, v.InBounds ctx.raw → v.getType! ctx'.raw = v.getType! ctx.raw
  arguments : ∀ b : BlockPtr, b.InBounds ctx.raw → b.getArgumentTypes! ctx'.raw = b.getArgumentTypes! ctx.raw
  fields : ∀ {D : Type} [HasOpInfo D] [HasDialect OpCode D] {code : D} {props : propertiesOf code}
    {op : OperationPtr} {ts : Array TypeAttr} {vs : Array ValuePtr} {rs : Array RegionPtr} {attrs : DictionaryAttr},
    op ∉ writes → MatchesOp ctx op code ts vs rs props attrs → MatchesOp ctx' op code ts vs rs props attrs
  terminators : ∀ {code : Llvm} {props : propertiesOf code}
    {op : OperationPtr} {vs : Array ValuePtr} {bs : Array BlockPtr},
    op ∉ writes → MatchesTermOp ctx op code vs bs props → MatchesTermOp ctx' op code vs bs props
  parents : ∀ o : OperationPtr, o.InBounds ctx.raw → o ∉ writes → o.getParent! ctx'.raw = o.getParent! ctx.raw
  opChains : ∀ {b : BlockPtr} {os : Array OperationPtr}, b ∉ inserts → b.OpChain ctx.raw os → b.OpChain ctx'.raw os
  blockChains : ∀ {r : RegionPtr} {bs : Array BlockPtr}, r ∉ extended → r.BlockChain ctx.raw bs → r.BlockChain ctx'.raw bs

theorem LoweringFrame.refl : LoweringFrame ctx ctx [] [] [] :=
  ⟨fun _ h => h, fun _ _ => rfl, fun _ _ => rfl, fun _ h => h, fun _ h => h,
    fun _ _ _ => rfl, fun _ h => h, fun _ h => h⟩

theorem LoweringFrame.trans
    (h : LoweringFrame ctx ctx' ws ins ex) (h' : LoweringFrame ctx' ctx'' ws' ins' ex') :
    LoweringFrame ctx ctx'' (ws ++ ws') (ins ++ ins') (ex ++ ex') := by
  refine ⟨fun p hp => h'.bounds p (h.bounds p hp), fun v hv => ?_, fun b hb => ?_,
    fun hw hm => h'.fields (by simp_all) (h.fields (by simp_all) hm),
    fun hw hm => h'.terminators (by simp_all) (h.terminators (by simp_all) hm), ?_,
    fun hi hb => h'.opChains (by simp_all) (h.opChains (by simp_all) hb),
    fun he hr => h'.blockChains (by simp_all) (h.blockChains (by simp_all) hr)⟩
  · exact (h'.valueTypes v (h.bounds (.value v) hv)).trans (h.valueTypes v hv)
  · exact (h'.arguments b (h.bounds (.block b) hb)).trans (h.arguments b hb)
  · intro op ho hw
    exact (h'.parents op (h.bounds (.operation op) ho) (by simp_all)).trans (h.parents op ho (by simp_all))

theorem LoweringFrame.mono (h : LoweringFrame ctx ctx' ws ins ex)
    (hw : ∀ o ∈ ws, o ∈ ws' ∨ ¬o.InBounds ctx.raw)
    (hi : ∀ b ∈ ins, b ∈ ins' ∨ ¬b.InBounds ctx.raw)
    (he : ∀ r ∈ ex, r ∈ ex' ∨ ¬r.InBounds ctx.raw) :
    LoweringFrame ctx ctx' ws' ins' ex' := by
  refine { h with fields := ?_, terminators := ?_, parents := ?_, opChains := ?_, blockChains := ?_ }
  · intro _ _ _ _ _ op _ _ _ _ hn hm; exact h.fields (fun hmem => (hw op hmem).elim hn (· hm.1)) hm
  · intro _ _ op _ _ hn hm; exact h.terminators (fun hmem => (hw op hmem).elim hn (· hm.1)) hm
  · intro o ho hn; exact h.parents o ho (fun hmem => (hw o hmem).elim hn (· ho))
  · intro b _ hn hb; exact h.opChains (fun hmem => (hi b hmem).elim hn (· hb.blockInBounds)) hb
  · intro r _ hn hr; exact h.blockChains (fun hmem => (he r hmem).elim hn (· hr.inBounds)) hr

theorem LoweringFrame.createOp {code : Llvm} {props : propertiesOf code} {insert : Bool}
    {hi : (if insert then some (InsertPoint.atEnd block) else none).maybe InsertPoint.InBounds ctx.raw}
    (h : WfRewriter.createOp ctx code ts vs bs rs props
      (if insert then some (.atEnd block) else none) ho hb hr hi = some (ctx', fresh)) :
    LoweringFrame ctx ctx' [] (if insert then [block] else []) [] := by
  have hn := WfRewriter.createOp_new_not_inBounds fresh h
  have hargs (b : BlockPtr) (_ : b.InBounds ctx.raw) : b.getArgumentTypes! ctx'.raw = b.getArgumentTypes! ctx.raw := by
    apply Array.ext (by grind); intro i hi hi'
    have := ValuePtr.getType!_WfRewriter_createOp (value := .blockArgument (b.getArgument i)) h
    grind
  refine ⟨fun p hp => by grind, fun v hv => ?_, hargs, fun _ hm => hm.createOp h,
    fun _ hm => hm.createOp h, fun o hoo _ => by grind, ?_, ?_⟩
  · cases v <;> grind
  · intro b os hb hc
    apply BlockPtr.OpChain_unchanged hc <;> cases insert <;> simp_all <;> grind
  · intro r arr _ hc
    have hraw : Rewriter.createOp ctx.raw code ts vs bs rs props
        (if insert then some (.atEnd block) else none) ho hb hr hi (by grind) = some (ctx'.raw, fresh) := by
      unfold WfRewriter.createOp at h; split at h <;> grind
    apply RegionPtr.blockChain_unchanged hc <;> grind


section Emit

attribute [local simp] StateT.run StateT.bind StateT.get StateT.set StateT.pure StateT.lift
  bind pure get getThe MonadState.get MonadStateOf.get set MonadStateOf.set
  Except.pure Except.bind throw throwThe MonadExceptOf.throw

theorem lowerM_bind_ok {x : LowerM α} {k : α → LowerM β} : (x >>= k).run ctx = .ok p ↔
    ∃ a ctx₁, x.run ctx = .ok (a, ctx₁) ∧ (k a).run ctx₁ = .ok p := by
  cases hx : x ctx <;> simp_all
  exact ⟨fun h => ⟨_, _, rfl, h⟩, fun ⟨_, _, he, h⟩ => he ▸ h⟩

theorem lowerM_pure_ok {a : α} : (pure a : LowerM α).run ctx = .ok p ↔ p = (a, ctx) := by simp [eq_comm]

theorem emit_total {code : Llvm} {props : propertiesOf code} {insert : Bool}
    (hs : AllocationSafe ctx.raw) (hb : insert = true → block.InBounds ctx.raw)
    (hv : ∀ v ∈ vs, v.InBounds ctx.raw) (hr : ∀ r ∈ rs, r.InBounds ctx.raw)
    (hp : ∀ r ∈ rs, r.getParent! ctx.raw = none) (hn : rs.size ≤ 1) :
    ∃ ctx' op, (emit code tys vs rs props block insert).run ctx = .ok (op, ctx') ∧ AllocationSafe ctx'.raw := by
  obtain ⟨raw, op, hc, hs'⟩ := hs.createOp_total (ts := tys) (insert := insert) (block := block)
    ctx.wellFormed.inBounds code props hb hv hr hp hn
  let c : WfIRContext OpCode := ⟨raw, by grind [Rewriter.createOp_WellFormed]⟩
  have he := createOp_of_raw (ctx' := c) hc
  have hi : (if insert then some (InsertPoint.atEnd block) else none).maybe InsertPoint.InBounds ctx.raw := by
    cases insert <;> grind
  refine ⟨c, op, ?_, hs'⟩
  simp [emit]
  rw [dite_eq_left hv, dite_eq_left hr, dite_eq_left hi, he]
  rfl

theorem emitBranch_total {code : Llvm} {props : propertiesOf code}
    (hs : AllocationSafe ctx.raw) (hb : block.InBounds ctx.raw)
    (hv : ∀ v ∈ vs, v.InBounds ctx.raw) (ht : ∀ b ∈ bs, b.InBounds ctx.raw) :
    ∃ ctx', (emitBranch code vs bs props block).run ctx = .ok ((), ctx') ∧ AllocationSafe ctx'.raw := by
  obtain ⟨raw, op, hc, hs'⟩ := hs.createOp_total (ts := #[]) (rs := #[]) (insert := true)
    ctx.wellFormed.inBounds code props (fun _ => hb) hv (by simp) (by simp) (by simp) bs ht
  let c : WfIRContext OpCode := ⟨raw, by grind [Rewriter.createOp_WellFormed]⟩
  have he := createOp_of_raw (ctx' := c) hc
  have hi : (some (InsertPoint.atEnd block)).maybe InsertPoint.InBounds ctx.raw := by grind
  refine ⟨c, ?_, hs'⟩
  have he' : WfRewriter.createOp ctx code #[] vs bs #[] props (some (.atEnd block)) hv ht (by simp) hi = some (c, op) := by
    simpa only [ite_true] using he
  simp [emitBranch]
  rw [dite_eq_left hv, dite_eq_left ht, dite_eq_left hb, he']
  rfl

theorem emit_spec {code : Llvm} {props : propertiesOf code} {insert : Bool}
    (h : (emit code types operands regions props block insert).run ctx = .ok (op, ctx')) :
    LoweringFrame ctx ctx' [] (if insert then [block] else []) [] ∧
      MatchesOp ctx' op code types operands regions props ∧ ¬op.InBounds ctx.raw ∧
      (insert = false → op.getParent! ctx'.raw = none) ∧
      ∀ os, block.OpChain ctx.raw os → block.OpChain ctx'.raw (if insert then os.push op else os) := by
  simp [emit] at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  rename_i ho hr
  by_cases hi : (if insert then some (InsertPoint.atEnd block) else none).maybe InsertPoint.InBounds ctx.raw
  · rw [dite_eq_left hi] at h
    rcases hc : WfRewriter.createOp ctx code types operands #[] regions props _ ho (by simp) hr hi with _ | ⟨c, o⟩ <;> simp [hc] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨LoweringFrame.createOp hc, createOp_matches hc, WfRewriter.createOp_new_not_inBounds _ hc, by grind, ?_⟩
    intro os hchain; cases insert
    · exact (LoweringFrame.createOp hc).opChains (by simp) hchain
    · exact opChain_createOp_atEnd hchain hc
  · simp [hi] at h

theorem emitBranch_frame {code : Llvm} {props : propertiesOf code}
    (h : (emitBranch code operands successors props block).run ctx = .ok ((), ctx')) :
    LoweringFrame ctx ctx' [] [block] [] := by
  simp [emitBranch] at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  rename_i ho hs hi
  rcases hc : WfRewriter.createOp ctx code #[] operands successors #[] props (some (.atEnd block))
    ho hs (by simp) (by simpa using hi) with _ | ⟨c, op⟩ <;> simp [hc] at h
  obtain rfl : c = ctx' := h
  exact LoweringFrame.createOp (insert := true) hc

end Emit

theorem LoweringFrame.trans_block
    (h : LoweringFrame ctx ctx' [] [block] []) (h' : LoweringFrame ctx' ctx'' [] [block] []) :
    LoweringFrame ctx ctx'' [] [block] [] := by
  apply (h.trans h').mono <;> simp

theorem OperandTile.frame (h : OperandTile ctx values ty val v cs)
    (hf : LoweringFrame ctx ctx' [] ins ex) : OperandTile ctx' values ty val v cs := by
  cases val with
  | ref => exact h
  | intConst =>
    cases ty
    obtain ⟨c, rfl, rfl, hm⟩ := h
    exact ⟨c, rfl, rfl, hf.fields (by simp) hm⟩

theorem MatchesOp.result_inBounds {code : Llvm} {props : propertiesOf code}
    (h : MatchesOp ctx op code ts vs rs props attrs) {i : Nat} (hi : i < ts.size) :
    (ValuePtr.opResult (op.getResult i)).InBounds ctx.raw := by
  have ht : op.getResultTypes! ctx.raw = ts := by grind [MatchesOp]
  have hn : i < op.getNumResults! ctx.raw := by rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, ht]; exact hi
  rw [ValuePtr.inBounds_opResult]
  exact OpResultPtr.inBounds_of (result := op.getResult i) h.1 hn

section OperandLowering

attribute [local simp] StateT.run StateT.bind StateT.get StateT.set StateT.pure StateT.lift
  bind pure get getThe MonadState.get MonadStateOf.get set MonadStateOf.set
  Except.pure Except.bind throw throwThe MonadExceptOf.throw

theorem lookupValue_ok {values : ValueMap} {id : ValueId} :
    (lookupValue values id).run ctx = .ok (v, ctx') ↔ values id = some v ∧ ctx = ctx' := by
  cases hv : values id <;> simp [lookupValue, hv]

theorem lowerOperand_spec {value : ResolvedValue}
    (h : (lowerOperand (lookupValue values) block ty value).run ctx = .ok (v, ctx'))
    (hc : block.OpChain ctx.raw os) (hv : ∀ id x, values id = some x → x.InBounds ctx.raw) :
    LoweringFrame ctx ctx' [] [block] [] ∧ v.InBounds ctx'.raw ∧
    ∃ cs, OperandTile ctx' values ty value v cs ∧ block.OpChain ctx'.raw (os ++ cs.toArray) := by
  cases value with
  | ref id =>
    obtain ⟨hm, rfl⟩ := lookupValue_ok.mp h
    refine ⟨LoweringFrame.refl.mono (by simp) (by simp) (by simp), hv id v hm, [], ⟨hm, rfl⟩, ?_⟩
    simpa using hc
  | intConst n =>
    cases ty
    simp only [lowerOperand, lowerM_bind_ok, lowerM_pure_ok, Prod.mk.injEq] at h
    obtain ⟨c, c₁, he, rfl, rfl⟩ := h
    obtain ⟨hf, hm, _, _, hc'⟩ := emit_spec he
    exact ⟨hf, hm.result_inBounds (by simp), [c], ⟨c, rfl, rfl, hm⟩, by simpa using hc' _ hc⟩

theorem lowerOperand_total {value : ResolvedValue}
    (hs : AllocationSafe ctx.raw) (hb : block.InBounds ctx.raw)
    (hv : ∀ id, value = .ref id → (values id).isSome) :
    ∃ ctx' v, (lowerOperand (lookupValue values) block ty value).run ctx = .ok (v, ctx') ∧
      AllocationSafe ctx'.raw := by
  cases value with
  | ref id =>
    obtain ⟨v, he⟩ := Option.isSome_iff_exists.mp (hv id rfl)
    exact ⟨ctx, v, lookupValue_ok.mpr ⟨he, rfl⟩, hs⟩
  | intConst n =>
    cases ty with
    | int w =>
      obtain ⟨c, o, he, hs'⟩ := emit_total (code := .mlir__constant) (props := {value := .integer (IntegerAttr.ofInt n (.signless w))})
        (tys := #[lowerType (.int w)]) (vs := #[]) (rs := #[]) (insert := true) (block := block)
        hs (fun _ => hb) (by simp) (by simp) (by simp) (by simp)
      exact ⟨c, .opResult (o.getResult 0), lowerM_bind_ok.mpr ⟨o, c, he, rfl⟩, hs'⟩

end OperandLowering

section EdgeLowering

attribute [local simp] StateT.run StateT.bind StateT.get StateT.set StateT.pure StateT.lift
  bind pure get getThe MonadState.get MonadStateOf.get set MonadStateOf.set
  Except.pure Except.bind throw throwThe MonadExceptOf.throw

theorem OperandTile.constant_type {w : Nat}
    (h : OperandTile ctx values (.int w) (.intConst n) v cs) :
    typeOf ctx.raw v = lowerType (.int w) := by
  obtain ⟨c, _, rfl, hm⟩ := h
  have hts : c.getResultTypes! ctx.raw = #[lowerType (.int w)] := by grind [MatchesOp]
  have hi : 0 < c.getNumResults! ctx.raw := by rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hts]; simp
  simpa [typeOf, OperationPtr.getResultTypes!.getElem!_eq hi] using congrArg (·[0]!) hts

def lowerTypedOperand (lookup : LookupValue) (block : BlockPtr) (err : LoweringError)
    (ty : LLType) (value : ResolvedValue) : LowerM ValuePtr := do
  let arg ← lowerOperand lookup block ty value
  let ctx ← get
  unless arg.getType! ctx.raw == lowerType ty do throw err
  return arg

theorem lowerTypedOperand_ok {ty : LLType} {value : ResolvedValue} :
    (lowerTypedOperand lookup block err ty value).run ctx = .ok (v, ctx') ↔
      (lowerOperand lookup block ty value).run ctx = .ok (v, ctx') ∧ typeOf ctx'.raw v = lowerType ty := by
  unfold lowerTypedOperand
  rw [lowerM_bind_ok]
  constructor
  · rintro ⟨x, c, h, ht⟩
    by_cases he : x.getType! c.raw = lowerType ty
    · obtain ⟨rfl, rfl⟩ : x = v ∧ c = ctx' := by simpa [he] using ht
      exact ⟨h, he⟩
    · simp [he] at ht
  · rintro ⟨h, ht⟩; exact ⟨v, ctx', h, by simp [typeOf] at ht; simp [ht]⟩

theorem lowerTypedOperand_total {ty : LLType} {value : ResolvedValue}
    (hs : AllocationSafe ctx.raw) (hc : block.OpChain ctx.raw os)
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw)
    (ht : ∀ id, value = .ref id → ∃ v, values id = some v ∧ typeOf ctx.raw v = lowerType ty) :
    ∃ ctx' v, (lowerTypedOperand (lookupValue values) block err ty value).run ctx = .ok (v, ctx') ∧
      AllocationSafe ctx'.raw := by
  cases value with
  | ref id =>
    obtain ⟨v, h, htype⟩ := ht id rfl
    exact ⟨ctx, v, lowerTypedOperand_ok.mpr ⟨lookupValue_ok.mpr ⟨h, rfl⟩, htype⟩, hs⟩
  | intConst n =>
    obtain ⟨c, v, h, ha⟩ := lowerOperand_total (values := values) (ty := ty) (value := .intConst n) hs hc.blockInBounds (by simp)
    obtain ⟨_, _, cs, hop, _⟩ := lowerOperand_spec h hc hv
    cases ty
    exact ⟨c, v, lowerTypedOperand_ok.mpr ⟨h, hop.constant_type⟩, ha⟩

theorem lowerTypedOperands_spec {inputs : List (LLType × ResolvedValue)}
    {xs : List ValuePtr}
    (h : (inputs.mapM fun (ty, input) => lowerTypedOperand (lookupValue values) block err ty input).run ctx = .ok (xs, ctx'))
    (hc : block.OpChain ctx.raw os) (hv : ∀ id v, values id = some v → v.InBounds ctx.raw) :
    LoweringFrame ctx ctx' [] [block] [] ∧ ∃ args : List ArgTile,
      args.map Prod.fst = xs ∧ (∀ v ∈ xs, v.InBounds ctx'.raw) ∧
      ResolvesList (fun input arg => OperandTile ctx' values input.1 input.2 arg.1 arg.2 ∧
        lowerType input.1 = typeOf ctx'.raw arg.1) inputs args ∧
      block.OpChain ctx'.raw (os ++ (argOps args).toArray) := by
  induction inputs generalizing ctx xs os with
  | nil =>
    cases h
    exact ⟨LoweringFrame.refl.mono (by simp) (by simp) (by simp), [], rfl, by simp, .nil, by simpa [argOps] using hc⟩
  | cons input inputs ih =>
    rcases input with ⟨ty, val⟩
    rw [List.mapM_cons, lowerM_bind_ok] at h
    obtain ⟨v, c, hv, h⟩ := h
    rw [lowerM_bind_ok] at h
    obtain ⟨vs, d, hd, h⟩ := h
    obtain ⟨rfl, rfl⟩ : v :: vs = xs ∧ d = ctx' := by simpa using h
    obtain ⟨hval, ht⟩ := lowerTypedOperand_ok.mp hv
    obtain ⟨hf, hi, cs, hm, hchain⟩ := lowerOperand_spec hval hc ‹∀ id v, values id = some v → v.InBounds ctx.raw›
    obtain ⟨hf', args, ha, hin, hargs, hchain'⟩ := ih hd hchain
      (fun id v h => hf.bounds (.value v) (‹∀ id v, values id = some v → v.InBounds ctx.raw› id v h))
    refine ⟨hf.trans_block hf', (v, cs) :: args, by simp [ha], ?_,
      .cons ⟨hm.frame hf', ((hf'.valueTypes v hi).trans ht).symm⟩ hargs, ?_⟩
    · exact List.forall_mem_cons.mpr ⟨hf'.bounds (.value v) hi, hin⟩
    · simpa [argOps, Array.append_assoc] using hchain'


theorem lowerTypedOperands_total {inputs : List (LLType × ResolvedValue)}
    (hs : AllocationSafe ctx.raw) (hc : block.OpChain ctx.raw os)
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw)
    (ht : ∀ ty id, (ty, .ref id) ∈ inputs →
      ∃ v, values id = some v ∧ typeOf ctx.raw v = lowerType ty) :
    ∃ ctx' vs, (inputs.mapM fun (ty, input) => lowerTypedOperand (lookupValue values) block err ty input).run ctx = .ok (vs, ctx') ∧
      AllocationSafe ctx'.raw := by
  induction inputs generalizing ctx os with
  | nil => exact ⟨ctx, [], rfl, hs⟩
  | cons input inputs ih =>
    rcases input with ⟨ty, input⟩
    obtain ⟨c, v, hv', hs'⟩ := lowerTypedOperand_total (err := err) (ty := ty) (value := input) hs hc hv (fun id h => ht ty id (h ▸ List.mem_cons_self))
    obtain ⟨hf, _, _, _, hc'⟩ := lowerOperand_spec (lowerTypedOperand_ok.mp hv').1 hc hv
    have hv'' id v hm := hf.bounds (.value v) (hv id v hm)
    obtain ⟨d, vs, hd, ha⟩ := ih hs' hc' hv'' (fun ty id hm => by
      obtain ⟨v, he, hty⟩ := ht ty id (List.mem_cons_of_mem _ hm)
      exact ⟨v, he, (hf.valueTypes v (hv id v he)).trans hty⟩)
    exact ⟨d, v :: vs, by rw [List.mapM_cons]; exact lowerM_bind_ok.mpr ⟨v, c, hv', lowerM_bind_ok.mpr ⟨vs, d, hd, rfl⟩⟩, ha⟩

theorem lowerEdge_eq {f : ResolvedFunction} {blocks : Array BlockPtr} :
    lowerEdge f blocks lookup block src dst = (do
      let some target := f.blocks[dst]? | throw "invalid branch destination"
      let some ptr := blocks[dst]? | throw "missing branch destination block"
      let some inputs := selectPhiInputs src target.insts | throw "missing phi incoming value"
      let args ← inputs.mapM fun (ty, val) => lowerTypedOperand lookup block
        "phi incoming value has the wrong type" ty val
      return (ptr, args.toArray)) := rfl

theorem lowerEdge_spec {f : ResolvedFunction} {blocks : Array BlockPtr}
    (h : (lowerEdge f blocks (lookupValue values) block src dst).run ctx = .ok ((b, vs), ctx'))
    (hd : dst ≠ 0) (hc : block.OpChain ctx.raw os)
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw) :
    LoweringFrame ctx ctx' [] [block] [] ∧ ∃ args,
      LowersEdge ctx' f (fun i => blocks[i]?) values src dst b args ∧ argPtrs args = vs ∧
      (∀ v ∈ vs, v.InBounds ctx'.raw) ∧ block.OpChain ctx'.raw (os ++ (argOps args).toArray) := by
  rw [lowerEdge_eq] at h
  cases ht : f.blocks[dst]? <;> try simp [ht] at h
  rename_i target
  cases hp : blocks[dst]? <;> try simp [hp] at h
  rename_i ptr
  cases hi : selectPhiInputs src target.insts <;> try simp [hi] at h
  rename_i inputs
  cases he : (inputs.mapM fun p => lowerTypedOperand (lookupValue values) block
      "phi incoming value has the wrong type" p.1 p.2) ctx <;> simp [he] at h
  rename_i pair
  obtain ⟨xs, c⟩ := pair
  obtain ⟨⟨rfl, hvs⟩, hctx⟩ := h
  change xs.toArray = vs at hvs
  change c = ctx' at hctx
  subst vs ctx'
  obtain ⟨hf, args, ha, hin, hargs, hc'⟩ := lowerTypedOperands_spec he hc hv
  obtain ⟨phis, hphis, hinput⟩ := selectPhiInputs_sound hi
  exact ⟨hf, args, ⟨hd, hp, target, phis, ht, hphis, phiPassesArg_list hinput hargs⟩,
    by simp [argPtrs, ha], by simpa, hc'⟩


theorem lowerEdge_total {f : ResolvedFunction} {blocks : Array BlockPtr}
    (hs : AllocationSafe ctx.raw) (hc : block.OpChain ctx.raw os)
    (ht : f.blocks[dst]? = some target) (hb : blocks[dst]? = some b)
    (hi : selectPhiInputs src target.insts = some inputs)
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw)
    (hty : ∀ ty id, (ty, .ref id) ∈ inputs →
      ∃ v, values id = some v ∧ typeOf ctx.raw v = lowerType ty) :
    ∃ ctx' vs, (lowerEdge f blocks (lookupValue values) block src dst).run ctx = .ok ((b, vs), ctx') ∧
      AllocationSafe ctx'.raw := by
  obtain ⟨c, vs, he, hsafe⟩ := lowerTypedOperands_total (err := "phi incoming value has the wrong type") hs hc hv hty
  refine ⟨c, vs.toArray, ?_, hsafe⟩
  simp only [lowerEdge_eq, ht, hb, hi]
  exact lowerM_bind_ok.mpr ⟨vs, c, he, rfl⟩

theorem selectPhiInputs_exists {insts : List ResolvedInst}
    (h : ∀ ty incoming, ResolvedInst.phi ty incoming ∈ insts → ∃ v, (src, v) ∈ incoming) :
    ∃ inputs, selectPhiInputs src insts = some inputs := by
  induction insts with
  | nil => exact ⟨[], rfl⟩
  | cons inst rest ih =>
    obtain ⟨inputs, hi⟩ := ih (fun ty incoming hm => h ty incoming (List.mem_cons_of_mem _ hm))
    cases inst with
    | bin => exact ⟨inputs, hi⟩
    | phi ty incoming =>
      obtain ⟨v, hv⟩ := h ty incoming List.mem_cons_self
      cases hl : incoming.lookup src with
      | none => simpa using (List.lookup_eq_none_iff.mp hl) (src, v) hv
      | some arg => exact ⟨(ty, arg) :: inputs, by simp [selectPhiInputs, hl, hi]⟩

theorem HasPredEdges.phiInput {f : ResolvedFunction} {target : ResolvedBlock}
    {src dst : BlockId} {incoming : List (BlockId × ResolvedValue)}
    (h : HasPredEdges f dst (incoming.map Prod.fst))
    (hb : f.blocks[src]? = some target) (hd : dst ∈ target.terminator.successors) :
    ∃ v, (src, v) ∈ incoming := by
  have hc := h src
  rw [hb] at hc
  change (incoming.map Prod.fst).count src = target.terminator.successors.count dst at hc
  have hm := List.count_pos_iff.mpr hd
  rw [← hc] at hm
  obtain ⟨⟨s, v⟩, hv, rfl⟩ := List.mem_map.mp (List.count_pos_iff.mp hm)
  exact ⟨v, hv⟩


theorem PhiPassesArg.frame {phi : ResolvedInst} {arg : ArgTile}
    (h : PhiPassesArg ctx values src phi arg)
    (hf : LoweringFrame ctx ctx' [] ins ex) : PhiPassesArg ctx' values src phi arg := by
  cases phi with
  | bin => exact h
  | phi =>
    rcases arg with ⟨v, cs⟩
    obtain ⟨input, hi, ho⟩ := h
    exact ⟨input, hi, ho.frame hf⟩

theorem LowersEdge.frame {blocks : BlockMap}
    (h : LowersEdge ctx f blocks values src dst b args)
    (hf : LoweringFrame ctx ctx' [] ins ex)
    (hv : ∀ v ∈ argPtrs args, v.InBounds ctx.raw) :
    LowersEdge ctx' f blocks values src dst b args := by
  obtain ⟨hn, hb, block, phis, he, hp, ha⟩ := h
  refine ⟨hn, hb, block, phis, he, hp, ?_⟩
  have hom := resolvesList_map_right (f := id) ha (S := fun phi arg =>
    PhiPassesArg ctx' values src phi arg ∧ phi.phiType.map lowerType = some (typeOf ctx'.raw arg.1)) (fun phi arg hm h => ?_)
  · simpa using hom
  · refine ⟨h.1.frame hf, ?_⟩
    have hin := hv arg.1 (by simpa [argPtrs] using List.mem_map_of_mem (f := Prod.fst) hm)
    simpa [typeOf, hf.valueTypes arg.1 hin] using h.2

theorem MatchesOp.return_matchesTerm
    (h : MatchesOp ctx op Llvm.return #[] vs #[] ()) :
    MatchesTermOp ctx op .return vs #[] () := by
  have hs : op.getSuccessors! ctx.raw = #[] := Array.eq_empty_iff_size_eq_zero.mpr (by grind [MatchesOp])
  grind [MatchesOp, MatchesTermOp]

theorem lowerReturn_spec {ty : LLType} {val : ResolvedValue}
    (h : (lowerReturn (lookupValue values) block ty val).run ctx = .ok (op, ctx'))
    (hc : block.OpChain ctx.raw os) (hv : ∀ id v, values id = some v → v.InBounds ctx.raw) :
    LoweringFrame ctx ctx' [] [block] [] ∧ ∃ x cs,
      OperandTile ctx' values ty val x cs ∧ MatchesTermOp ctx' op .return #[x] #[] () ∧
      block.OpChain ctx'.raw (os ++ (cs ++ [op]).toArray) := by
  obtain ⟨x, c, hv', he⟩ := lowerM_bind_ok.mp h
  obtain ⟨hf, _, cs, ht, hchain⟩ := lowerOperand_spec hv' hc hv
  obtain ⟨hg, hm, _, _, hchain'⟩ := emit_spec he
  exact ⟨hf.trans_block hg, x, cs, ht.frame hg, hm.return_matchesTerm,
    by simpa only [List.append_toArray, Array.push_eq_append, Array.append_assoc, ite_true] using hchain' _ hchain⟩

theorem lowerTerminator_ret_spec {f : ResolvedFunction} {blocks : Array BlockPtr}
    (h : (lowerTerminator f blocks (lookupValue values) block src (.ret val)).run ctx = .ok ((), ctx'))
    (hc : block.OpChain ctx.raw os) (hv : ∀ id v, values id = some v → v.InBounds ctx.raw) :
    LoweringFrame ctx ctx' [] [block] [] ∧ ∃ tile,
      LowersTerminatorTile ctx' f (fun i => blocks[i]?) values src (.ret val) tile ∧
      block.OpChain ctx'.raw (os ++ tile.toArray) := by
  obtain ⟨op, c, hr, hp⟩ := lowerM_bind_ok.mp h
  have hc' : c = ctx' := by simpa using hp
  subst c
  obtain ⟨hf, x, cs, ht, hm, hc⟩ := lowerReturn_spec hr hc hv
  exact ⟨hf, cs ++ [op], ⟨x, cs, op, ht, hm, rfl⟩, hc⟩

theorem lowerTerminator_br_spec {f : ResolvedFunction} {blocks : Array BlockPtr} {dst : BlockId}
    (h : (lowerTerminator f blocks (lookupValue values) block src (.br dst)).run ctx = .ok ((), ctx'))
    (hd : dst ≠ 0) (hc : block.OpChain ctx.raw os)
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw) :
    LoweringFrame ctx ctx' [] [block] [] ∧ ∃ tile,
      LowersTerminatorTile ctx' f (fun i => blocks[i]?) values src (.br dst) tile ∧
      block.OpChain ctx'.raw (os ++ tile.toArray) := by
  obtain ⟨⟨b, vs⟩, c, he, ho⟩ := lowerM_bind_ok.mp h
  obtain ⟨hf, args, ha, rfl, hin, hchain⟩ := lowerEdge_spec he hd hc hv
  have hg := emitBranch_frame ho
  obtain ⟨op, hm, hchain'⟩ := emitBranch_sound ho hchain
  exact ⟨hf.trans_block hg, argOps args ++ [op], ⟨b, args, op, ha.frame hg hin, hm, rfl⟩,
    by simpa only [List.append_toArray, Array.push_eq_append, Array.append_assoc] using hchain'⟩


theorem lowerTerminator_condBr_eq {f : ResolvedFunction} {blocks : Array BlockPtr} {yes no : BlockId}
    {cond : ResolvedValue} :
    lowerTerminator f blocks lookup block src (.condBr cond yes no) = (do
      let x ← lowerTypedOperand lookup block "branch condition must be i1" (.int 1) cond
      let (y, ys) ← lowerEdge f blocks lookup block src yes
      let (n, ns) ← lowerEdge f blocks lookup block src no
      emitBranch .cond_br (#[x] ++ ys ++ ns) #[y, n]
        { branch_weights := ⟨.signless 32, #[]⟩
          loop_annotation := none
          operandSegmentSizes := ⟨.signless 32, #[1, Int.ofNat ys.size, Int.ofNat ns.size]⟩ } block) := by
  funext c
  cases he : lowerOperand lookup block (.int 1) cond c with
  | error => simp [lowerTerminator, lowerTypedOperand, he]
  | ok p =>
    rcases p with ⟨v, d⟩
    by_cases ht : v.getType! d.raw = lowerType (.int 1) <;>
      simp [lowerTerminator, lowerTypedOperand, he, ht]

theorem lowerTerminator_condBr_spec {cond : ResolvedValue} {f : ResolvedFunction} {blocks : Array BlockPtr} {yes no : BlockId}
    (h : (lowerTerminator f blocks (lookupValue values) block src (.condBr cond yes no)).run ctx = .ok ((), ctx'))
    (hy : yes ≠ 0) (hn : no ≠ 0) (hc : block.OpChain ctx.raw os)
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw) :
    LoweringFrame ctx ctx' [] [block] [] ∧ ∃ tile,
      LowersTerminatorTile ctx' f (fun i => blocks[i]?) values src (.condBr cond yes no) tile ∧
      block.OpChain ctx'.raw (os ++ tile.toArray) := by
  rw [lowerTerminator_condBr_eq, lowerM_bind_ok] at h
  obtain ⟨x, c, hx, h⟩ := h
  obtain ⟨⟨y, yvs⟩, d, hy', h⟩ := lowerM_bind_ok.mp h
  obtain ⟨⟨n, nvs⟩, e, hn', h⟩ := lowerM_bind_ok.mp h
  obtain ⟨hcond, ht⟩ := lowerTypedOperand_ok.mp hx
  obtain ⟨hf, hix, cs, hval, hchain⟩ := lowerOperand_spec hcond hc hv
  have hvc id v h := hf.bounds (.value v) (hv id v h)
  obtain ⟨hg, ys, hs, rfl, hyin, hchain⟩ := lowerEdge_spec hy' hy hchain hvc
  have hvd id v h := hg.bounds (.value v) (hvc id v h)
  obtain ⟨hh, ns, hs', rfl, hnin, hchain⟩ := lowerEdge_spec hn' hn hchain hvd
  have hi := emitBranch_frame h
  obtain ⟨op, hm, hchain⟩ := emitBranch_sound h hchain
  have hrest := hg.trans_block (hh.trans_block hi)
  refine ⟨hf.trans_block hrest, cs ++ argOps ys ++ argOps ns ++ [op], ⟨x, cs, y, n, ys, ns, op,
    hval.frame hrest, (hrest.valueTypes x hix).trans ht, hs.frame (hh.trans_block hi) hyin,
    hs'.frame hi hnin, by simpa [argPtrs] using hm, rfl⟩, ?_⟩
  simpa only [List.append_toArray, Array.push_eq_append, Array.append_assoc] using hchain

theorem lowerTerminator_spec {f : ResolvedFunction} {blocks : Array BlockPtr} {term : ResolvedTerminator}
    (h : (lowerTerminator f blocks (lookupValue values) block src term).run ctx = .ok ((), ctx'))
    (hd : ∀ dst ∈ term.successors, dst ≠ 0)
    (hc : block.OpChain ctx.raw os) (hv : ∀ id v, values id = some v → v.InBounds ctx.raw) :
    LoweringFrame ctx ctx' [] [block] [] ∧ ∃ tile,
      LowersTerminatorTile ctx' f (fun i => blocks[i]?) values src term tile ∧
      block.OpChain ctx'.raw (os ++ tile.toArray) := by
  cases term with
  | ret => exact lowerTerminator_ret_spec h hc hv
  | br dst => exact lowerTerminator_br_spec h (hd dst (by simp [ResolvedTerminator.successors])) hc hv
  | condBr _ yes no =>
    exact lowerTerminator_condBr_spec h
      (hd yes (by simp [ResolvedTerminator.successors])) (hd no (by simp [ResolvedTerminator.successors])) hc hv


structure EdgeReady (ctx : WfIRContext OpCode) (f : ResolvedFunction) (blocks : Array BlockPtr)
    (values : ValueMap) (src dst : BlockId) : Prop where
  target : ∃ target ptr inputs, f.blocks[dst]? = some target ∧ blocks[dst]? = some ptr ∧
    ptr.InBounds ctx.raw ∧ selectPhiInputs src target.insts = some inputs ∧
    ∀ ty id, (ty, .ref id) ∈ inputs → ∃ v, values id = some v ∧ typeOf ctx.raw v = lowerType ty

theorem EdgeReady.frame {blocks : Array BlockPtr}
    (hr : EdgeReady ctx f blocks values src dst)
    (hf : LoweringFrame ctx ctx' ws ins ex)
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw) :
    EdgeReady ctx' f blocks values src dst := by
  obtain ⟨target, ptr, inputs, ht, hp, hi, hs, hty⟩ := hr.target
  refine ⟨⟨target, ptr, inputs, ht, hp, hf.bounds (.block ptr) hi, hs, fun ty id hm => ?_⟩⟩
  obtain ⟨v, he, h⟩ := hty ty id hm
  exact ⟨v, he, (hf.valueTypes v (hv id v he)).trans h⟩

theorem EdgeReady.lower {blocks : Array BlockPtr}
    (hr : EdgeReady ctx f blocks values src dst)
    (hs : AllocationSafe ctx.raw) (hc : block.OpChain ctx.raw os)
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw) :
    ∃ ctx' ptr vs, (lowerEdge f blocks (lookupValue values) block src dst).run ctx = .ok ((ptr, vs), ctx') ∧
      AllocationSafe ctx'.raw ∧ ptr.InBounds ctx.raw := by
  obtain ⟨_, ptr, _, ht, hp, hin, hi, hty⟩ := hr.target
  obtain ⟨c, vs, he, hsafe⟩ := lowerEdge_total hs hc ht hp hi hv hty
  exact ⟨c, ptr, vs, he, hsafe, hin⟩

theorem lowerReturn_total {ty : LLType} {value : ResolvedValue}
    (hs : AllocationSafe ctx.raw) (hc : block.OpChain ctx.raw os)
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw)
    (hr : ∀ id, value = .ref id → (values id).isSome) :
    ∃ ctx' op, (lowerReturn (lookupValue values) block ty value).run ctx = .ok (op, ctx') ∧ AllocationSafe ctx'.raw := by
  obtain ⟨c, v, he, hsafe⟩ := lowerOperand_total (ty := ty) hs hc.blockInBounds hr
  obtain ⟨_, hin, _, _, hchain⟩ := lowerOperand_spec he hc hv
  obtain ⟨d, op, hp, hsafe⟩ := emit_total (code := .return) (props := ()) (tys := #[]) (vs := #[v])
    (rs := #[]) (block := block) (insert := true) hsafe (fun _ => hchain.blockInBounds)
    (by simpa using hin) (by simp) (by simp) (by simp)
  exact ⟨d, op, lowerM_bind_ok.mpr ⟨v, c, he, hp⟩, hsafe⟩

theorem lowerTerminator_br_total {f : ResolvedFunction} {blocks : Array BlockPtr} {dst : BlockId}
    (hs : AllocationSafe ctx.raw) (hc : block.OpChain ctx.raw os)
    (hr : EdgeReady ctx f blocks values src dst) (hd : dst ≠ 0)
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw) :
    ∃ ctx', (lowerTerminator f blocks (lookupValue values) block src (.br dst)).run ctx = .ok ((), ctx') ∧
      AllocationSafe ctx'.raw := by
  obtain ⟨c, ptr, vs, h, ha, hin⟩ := hr.lower hs hc hv
  obtain ⟨hf, _, _, _, hv', hchain⟩ := lowerEdge_spec h hd hc hv
  obtain ⟨d, he, hs'⟩ := emitBranch_total (code := .br) (props := {loop_annotation := none})
    (bs := #[ptr]) ha hchain.blockInBounds hv' (by simpa using hf.bounds (.block ptr) hin)
  exact ⟨d, lowerM_bind_ok.mpr ⟨(ptr, vs), c, h, he⟩, hs'⟩

theorem lowerTerminator_condBr_total {f : ResolvedFunction} {blocks : Array BlockPtr}
    {yes no : BlockId} {cond : ResolvedValue}
    (hs : AllocationSafe ctx.raw) (hc : block.OpChain ctx.raw os)
    (hy : EdgeReady ctx f blocks values src yes) (hn : EdgeReady ctx f blocks values src no)
    (hdy : yes ≠ 0) (hdn : no ≠ 0)
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw)
    (ht : ∀ id, cond = .ref id → ∃ v, values id = some v ∧ typeOf ctx.raw v = lowerType (.int 1)) :
    ∃ ctx', (lowerTerminator f blocks (lookupValue values) block src (.condBr cond yes no)).run ctx = .ok ((), ctx') ∧
      AllocationSafe ctx'.raw := by
  obtain ⟨c, x, hx, hs⟩ := lowerTypedOperand_total (err := "branch condition must be i1") hs hc hv ht
  obtain ⟨hf, hix, _, _, hchain⟩ := lowerOperand_spec (lowerTypedOperand_ok.mp hx).1 hc hv
  have hvc id v h := hf.bounds (.value v) (hv id v h)
  obtain ⟨d, y, ys, hy', hs, hiy⟩ := (hy.frame hf hv).lower hs hchain hvc
  obtain ⟨hg, _, _, _, hys, hchain⟩ := lowerEdge_spec hy' hdy hchain hvc
  have hvd id v h := hg.bounds (.value v) (hvc id v h)
  obtain ⟨e, n, ns, hn', hs, hin⟩ := (hn.frame (hf.trans_block hg) hv).lower hs hchain hvd
  obtain ⟨hh, _, _, _, hns, hchain⟩ := lowerEdge_spec hn' hdn hchain hvd
  have hargs : ∀ v ∈ #[x] ++ ys ++ ns, v.InBounds e.raw := by
    simp only [Array.mem_append, Array.mem_singleton]
    rintro v ((he | h) | h)
    · subst v; exact (hg.trans_block hh).bounds (.value x) hix
    · exact hh.bounds (.value v) (hys v h)
    · exact hns v h
  have hdest : ∀ b ∈ #[y, n], b.InBounds e.raw := by
    simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (he | he)
    · subst b; exact (hg.trans_block hh).bounds (.block y) hiy
    · subst b; exact hh.bounds (.block n) hin
  let props : propertiesOf Llvm.cond_br :=
    { branch_weights := ⟨.signless 32, #[]⟩
      loop_annotation := none
      operandSegmentSizes := ⟨.signless 32, #[1, Int.ofNat ys.size, Int.ofNat ns.size]⟩ }
  obtain ⟨g, he, hsafe⟩ := emitBranch_total (code := .cond_br) (props := props)
    hs hchain.blockInBounds hargs hdest
  exact ⟨g, by rw [lowerTerminator_condBr_eq]; exact lowerM_bind_ok.mpr ⟨x, c, hx,
    lowerM_bind_ok.mpr ⟨(y, ys), d, hy', lowerM_bind_ok.mpr ⟨(n, ns), e, hn', he⟩⟩⟩, hsafe⟩

end EdgeLowering

section BinaryLowering

attribute [local simp] StateT.run StateT.bind StateT.get StateT.set StateT.pure StateT.lift
  bind pure get getThe MonadState.get MonadStateOf.get set MonadStateOf.set
  Except.pure Except.bind throw throwThe MonadExceptOf.throw

theorem MatchesOp.pushOperand {D : Type} [HasOpInfo D] [HasDialect OpCode D]
    {code : D} {props : propertiesOf code}
    (h : MatchesOp ctx op code types operands regions props attrs)
    (ho : target.InBounds ctx.raw) (hv : value.InBounds ctx.raw) :
    MatchesOp (WfRewriter.pushOperand ctx target value ho hv) op code types
      (if op = target then operands.push value else operands) regions props attrs := by
  simp only [MatchesOp, Prod.mk.injEq, WfRewriter.pushOperand] at *; simp_getset; grind

theorem LoweringFrame.pushOperand (ho : op.InBounds ctx.raw) (hv : v.InBounds ctx.raw) :
    LoweringFrame ctx (WfRewriter.pushOperand ctx op v ho hv) [op] [] [] := by
  refine ⟨fun _ _ => by grind [WfRewriter.pushOperand], fun _ _ => by grind [WfRewriter.pushOperand],
    fun _ _ => ?_, fun hn hm => ?_, fun hn hm => ?_, fun _ _ _ => by grind [WfRewriter.pushOperand], ?_, ?_⟩
  · apply Array.ext <;> grind [WfRewriter.pushOperand]
  · simpa [show _ ≠ op by simpa using hn] using hm.pushOperand ho hv
  · simp only [MatchesTermOp, Prod.mk.injEq, WfRewriter.pushOperand] at *
    simp_getset; grind
  · intro _ _ _ hc; exact BlockPtr.opChain_rewriter_pushOperand ctx.raw (by grind) op ho hc
  · intro _ _ _ hc; apply RegionPtr.blockChain_unchanged hc <;> grind [WfRewriter.pushOperand]

theorem WfRewriter_insertOp_raw
    (h : WfRewriter.insertOp ctx op ip ho hi = some ctx') :
    Rewriter.insertOp ctx.raw op ip ho hi (by grind) = some ctx'.raw := by
  unfold WfRewriter.insertOp at h
  split at h <;> grind

theorem LoweringFrame.insertOp {ho : op.InBounds ctx.raw} {hi : (InsertPoint.atEnd block).InBounds ctx.raw}
    (h : WfRewriter.insertOp ctx op (.atEnd block) ho hi = some ctx')
    (hp : op.getParent! ctx.raw = none) :
    LoweringFrame ctx ctx' [op] [block] [] := by
  have hr := WfRewriter_insertOp_raw h
  refine ⟨fun p hp => by grind, fun v hv => by grind, fun b hb => ?_, ?_,
    ?_, fun p hp hn => by grind, ?_, ?_⟩
  · apply Array.ext <;> grind
  · intro _ _ _ _ _ o _ _ _ _ hn hm
    have hreg : o.getRegions! ctx'.raw = o.getRegions! ctx.raw := by apply Array.ext <;> grind
    simp only [MatchesOp, Prod.mk.injEq] at *; simp_getset; grind
  · intro _ _ o _ _ hn hm
    have hreg : o.getRegions! ctx'.raw = o.getRegions! ctx.raw := by apply Array.ext <;> grind
    simp only [MatchesTermOp, Prod.mk.injEq] at *; simp_getset; grind
  · intro b os hn hc; apply BlockPtr.OpChain_unchanged hc <;> grind
  · intro r bs _ hc; apply RegionPtr.blockChain_unchanged hc <;> grind


def BinaryAllocated (ctx : WfIRContext OpCode) : ResolvedBinary → OperationPtr → Prop
  | .bin opc ty _ _, op => MatchesOp ctx op (binOpcode opc) #[lowerType ty] #[] #[] default ∧
    op.getParent! ctx.raw = none

theorem BinaryAllocated.inBounds (h : BinaryAllocated ctx inst op) : op.InBounds ctx.raw := by
  cases inst
  exact h.1.1

theorem BinaryAllocated.frame (h : BinaryAllocated ctx inst op)
    (hf : LoweringFrame ctx ctx' ws ins ex) (hn : op ∉ ws) : BinaryAllocated ctx' inst op := by
  cases inst
  exact ⟨hf.fields hn h.1, (hf.parents op h.1.1 hn).trans h.2⟩

theorem lowerInst_spec
    (h : (lowerInst block inst).run ctx = .ok (op, ctx')) :
    LoweringFrame ctx ctx' [] [] [] ∧ BinaryAllocated ctx' inst op ∧ ¬op.InBounds ctx.raw := by
  rcases inst with ⟨opc, ty, lhs, rhs⟩
  cases opc <;> obtain ⟨hf, hm, hn, hp, _⟩ := emit_spec h <;>
    exact ⟨hf, ⟨hm, hp rfl⟩, hn⟩

theorem lowerInst_total (hs : AllocationSafe ctx.raw) :
    ∃ ctx' op, (lowerInst block inst).run ctx = .ok (op, ctx') ∧ AllocationSafe ctx'.raw := by
  rcases inst with ⟨opc, ty, lhs, rhs⟩
  cases opc <;> exact emit_total (insert := false) (block := block) hs (by simp)
    (by simp) (by simp) (by simp) (by simp)

theorem pushValue_ok (h : (pushValue op v).run ctx = .ok ((), ctx')) :
    ∃ (ho : op.InBounds ctx.raw) (hv : v.InBounds ctx.raw), ctx' = WfRewriter.pushOperand ctx op v ho hv := by
  simp [pushValue] at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  rename_i ho hv
  exact ⟨ho, hv, h.symm⟩

theorem attachInst_ok (h : (attachInst block op).run ctx = .ok ((), ctx')) :
    ∃ (ho : op.InBounds ctx.raw) (hi : (InsertPoint.atEnd block).InBounds ctx.raw),
      WfRewriter.insertOp ctx op (.atEnd block) ho hi = some ctx' := by
  simp [attachInst] at h
  split at h <;> try simp at h
  split at h <;> try simp at h
  rename_i ho hb
  cases hi : WfRewriter.insertOp ctx op (.atEnd block) ho hb <;> simp [hi] at h
  exact ⟨ho, hb, h ▸ hi⟩

theorem OperandTile.frame_avoiding (h : OperandTile ctx values ty val v cs)
    (hf : LoweringFrame ctx ctx' ws ins ex) (hw : ∀ c ∈ cs, c ∉ ws) :
    OperandTile ctx' values ty val v cs := by
  cases val with
  | ref => exact h
  | intConst =>
    cases ty
    obtain ⟨c, rfl, rfl, hm⟩ := h
    exact ⟨c, rfl, rfl, hf.fields (hw c List.mem_cons_self) hm⟩

theorem not_mem_ops_of_detached {block : BlockPtr} (hc : block.OpChain ctx.raw os)
    (hn : op.getParent! ctx.raw = none) : op ∉ os := by
  intro hm
  rw [hc.opParent hm] at hn
  contradiction

theorem lowerOperand_push_spec {D : Type} [HasOpInfo D] [HasDialect OpCode D]
    {code : D} {props : propertiesOf code}
    (hm : MatchesOp ctx op code ts vs rs props attrs) (hc : block.OpChain ctx.raw os)
    (hd : op.getParent! ctx.raw = none)
    (he : (lowerOperand (lookupValue values) block ty val).run ctx = .ok (v, ctx₁))
    (hp : (pushValue op v).run ctx₁ = .ok ((), ctx'))
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw) :
    LoweringFrame ctx ctx' [op] [block] [] ∧ MatchesOp ctx' op code ts (vs.push v) rs props attrs ∧
    op.getParent! ctx'.raw = none ∧ ∃ cs,
    OperandTile ctx' values ty val v cs ∧ block.OpChain ctx'.raw (os ++ cs.toArray) := by
  obtain ⟨hf, _, cs, ht, hchain⟩ := lowerOperand_spec he hc hv
  obtain ⟨ho, hv', rfl⟩ := pushValue_ok hp
  have hg := LoweringFrame.pushOperand ho hv'
  have hd' := (hf.parents op hm.1 (by simp)).trans hd
  have hn : ∀ c ∈ cs, c ∉ [op] := by
    intro c h hc'
    have he : c = op := by simpa using hc'
    exact not_mem_ops_of_detached hchain hd' (by simp [← he, h])
  refine ⟨hf.trans hg, by simpa using (hf.fields (by simp) hm).pushOperand ho hv',
    by simpa [WfRewriter.pushOperand] using hd', cs, ht.frame_avoiding hg hn, hg.opChains (by simp) hchain⟩


theorem opChain_insertOp_atEnd {ho : op.InBounds ctx.raw} {hi : (InsertPoint.atEnd block).InBounds ctx.raw}
    (hc : block.OpChain ctx.raw os) (h : WfRewriter.insertOp ctx op (.atEnd block) ho hi = some ctx') :
    block.OpChain ctx'.raw (os.push op) := by
  have hr := WfRewriter_insertOp_raw h
  have hb : block.InBounds ctx'.raw := by grind
  have he := BlockPtr.operationList_rewriter_insertOp (ctx'Wf := ctx'.wellFormed) (blockIn := hb) hr ctx.wellFormed
  have hold := (BlockPtr.operationList_iff_BlockPtr_OpChain (hctx := ctx.wellFormed) (hblock := hc.blockInBounds)).mp hc
  apply (BlockPtr.operationList_iff_BlockPtr_OpChain (hctx := ctx'.wellFormed) (hblock := hb)).mpr
  simpa [InsertPoint.block!_atEnd_eq, InsertPoint.idxIn_atEnd_eq, hold] using he

theorem MatchesOp.insertOp {D : Type} [HasOpInfo D] [HasDialect OpCode D]
    {code : D} {props : propertiesOf code}
    (hm : MatchesOp ctx op code types operands regions props attrs)
    (h : WfRewriter.insertOp ctx other ip ho hi = some ctx') :
    MatchesOp ctx' op code types operands regions props attrs := by
  have hreg : op.getRegions! ctx'.raw = op.getRegions! ctx.raw := by apply Array.ext <;> grind
  simp only [MatchesOp, Prod.mk.injEq] at *; simp_getset; grind

theorem avoids_detached {block : BlockPtr} {op : OperationPtr} {cs : List OperationPtr}
    (hc : block.OpChain ctx.raw os) (hd : op.getParent! ctx.raw = none)
    (hs : ∀ p ∈ cs, p ∈ os) : ∀ p ∈ cs, p ∉ [op] := by
  intro p hm he
  have he' : p = op := by simpa using he
  exact not_mem_ops_of_detached hc hd (he' ▸ hs p hm)

theorem wireBinary_finish {code : Llvm} {props : propertiesOf code}
    (hm : MatchesOp ctx op code ts #[vl, vr] #[] props)
    (hl : OperandTile ctx values ty lhs vl cl) (hr : OperandTile ctx values ty rhs vr cr)
    (hc : block.OpChain ctx.raw (os ++ cl.toArray ++ cr.toArray))
    (hd : op.getParent! ctx.raw = none)
    (h : (attachInst block op).run ctx = .ok ((), ctx')) :
    LoweringFrame ctx ctx' [op] [block] [] ∧ MatchesOp ctx' op code ts #[vl, vr] #[] props ∧
    OperandTile ctx' values ty lhs vl cl ∧ OperandTile ctx' values ty rhs vr cr ∧
    block.OpChain ctx'.raw (os ++ (cl ++ cr ++ [op]).toArray) := by
  obtain ⟨_, _, hi⟩ := attachInst_ok h
  have hf := LoweringFrame.insertOp hi hd
  exact ⟨hf, hm.insertOp hi, hl.frame_avoiding hf (avoids_detached hc hd (by simp_all)),
    hr.frame_avoiding hf (avoids_detached hc hd (by simp_all)),
    by simpa only [List.append_toArray, Array.push_eq_append, Array.append_assoc] using opChain_insertOp_atEnd hc hi⟩

theorem wireBinary_spec {inst : ResolvedBinary} {id : ValueId}
    (h : (wireBinary (lookupValue values) block (inst, op)).run ctx = .ok ((), ctx'))
    (ha : BinaryAllocated ctx inst op) (hc : block.OpChain ctx.raw os)
    (hid : values id = some (.opResult (op.getResult 0)))
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw) :
    LoweringFrame ctx ctx' [op] [block] [] ∧ ∃ tile, LowersInstTile ctx' values id inst tile ∧
      block.OpChain ctx'.raw (os ++ tile.toArray) := by
  rcases inst with ⟨opc, ty, lhs, rhs⟩
  simp only [wireBinary, lowerM_bind_ok] at h
  obtain ⟨vl, c, hl, _, d, hp, vr, e, hr, _, g, hq, hi⟩ := h
  obtain ⟨hf, hml, hd, cl, htl, hchain⟩ := lowerOperand_push_spec ha.1 hc ha.2 hl hp hv
  obtain ⟨hg, hmr, hd', cr, htr, hchain'⟩ := lowerOperand_push_spec hml hchain hd hr hq
    (fun i v h => hf.bounds (.value v) (hv i v h))
  have htl' := htl.frame_avoiding hg (avoids_detached hchain hd (by simp_all))
  obtain ⟨hh, hm, htl, htr, hchain⟩ := wireBinary_finish hmr htl' htr hchain' hd' hi
  exact ⟨(hf.trans (hg.trans hh)).mono (by simp) (by simp) (by simp), cl ++ cr ++ [op],
    ⟨vl, vr, cl, cr, op, rfl, htl, htr, hid, hm⟩, hchain⟩


theorem allocateBinaryList_spec {insts : List ResolvedBinary}
    (h : (insts.mapM (lowerInst block)).run ctx = .ok (ops, ctx')) :
    LoweringFrame ctx ctx' [] [] [] ∧ ResolvesList (BinaryAllocated ctx') insts ops ∧ ops.Nodup ∧
      ∀ op ∈ ops, ¬op.InBounds ctx.raw := by
  induction insts generalizing ctx ops with
  | nil => cases h; exact ⟨LoweringFrame.refl, .nil, List.nodup_nil, by simp⟩
  | cons inst insts ih =>
    simp only [List.mapM_cons, lowerM_bind_ok, lowerM_pure_ok, Prod.mk.injEq] at h
    obtain ⟨o, c, ho, tail, d, hd, rfl, rfl⟩ := h
    obtain ⟨hf, ha, hn⟩ := lowerInst_spec ho
    obtain ⟨hg, hs, hnodup, hnew⟩ := ih hd
    exact ⟨hf.trans hg, .cons (ha.frame hg (by simp)) hs,
      List.nodup_cons.mpr ⟨fun hm => hnew o hm ha.inBounds, hnodup⟩,
      List.forall_mem_cons.mpr ⟨hn, fun p hp hi => hnew p hp (hf.bounds (.operation p) hi)⟩⟩

theorem allocateBinaryList_total {insts : List ResolvedBinary} (hs : AllocationSafe ctx.raw) :
    ∃ ctx' ops, (insts.mapM (lowerInst block)).run ctx = .ok (ops, ctx') ∧ AllocationSafe ctx'.raw := by
  induction insts generalizing ctx with
  | nil => exact ⟨ctx, [], rfl, hs⟩
  | cons inst insts ih =>
    obtain ⟨c, op, ho, hsafe⟩ := lowerInst_total (inst := inst) (block := block) hs
    obtain ⟨d, ops, ht, hsafe⟩ := ih hsafe
    exact ⟨d, op :: ops, by rw [List.mapM_cons]; exact lowerM_bind_ok.mpr ⟨op, c, ho,
      lowerM_bind_ok.mpr ⟨ops, d, ht, rfl⟩⟩, hsafe⟩

theorem LowersInstTile.frame_avoiding {id : ValueId}
    (h : LowersInstTile ctx values id inst tile)
    (hf : LoweringFrame ctx ctx' ws ins ex) (hw : ∀ o ∈ tile, o ∉ ws) :
    LowersInstTile ctx' values id inst tile := by
  cases inst
  obtain ⟨vl, vr, cl, cr, op, rfl, hl, hr, hv, ho⟩ := h
  exact ⟨vl, vr, cl, cr, op, rfl, hl.frame_avoiding hf (by grind), hr.frame_avoiding hf (by grind),
    hv, hf.fields (by grind) ho⟩

theorem resolvesList_right_member (h : ResolvesList R xs ys) (hm : y ∈ ys) : ∃ x, R x y := by
  induction h with
  | nil => simp at hm
  | cons hr _ ih => exact (List.mem_cons.mp hm).elim (fun he => ⟨_, he ▸ hr⟩) ih

theorem resolvesList_transfer (h : ResolvesList R xs ys)
    (ht : ∀ x y, y ∈ ys → R x y → S x y) : ResolvesList S xs ys := by
  induction h with
  | nil => exact .nil
  | cons hr _ ih =>
    exact .cons (ht _ _ List.mem_cons_self hr) (ih fun x y hm => ht x y (List.mem_cons_of_mem _ hm))

theorem wireBinaryList_spec {entries : List (ResolvedBinary × κ)} (keyOf : κ → ValueId)
    (h : (((entries.map Prod.fst).zip ops).forM (wireBinary (lookupValue values) block)).run ctx = .ok ((), ctx'))
    (ha : ResolvesList (fun (inst, id) op => BinaryAllocated ctx inst op ∧
      values (keyOf id) = some (.opResult (op.getResult 0))) entries ops)
    (hn : ops.Nodup) (hc : block.OpChain ctx.raw os)
    (hv : ∀ id v, values id = some v → v.InBounds ctx.raw) :
    LoweringFrame ctx ctx' ops [block] [] ∧ ∃ tiles,
      ResolvesList (fun (inst, id) tile => LowersInstTile ctx' values (keyOf id) inst tile) entries tiles ∧
      block.OpChain ctx'.raw (os ++ tiles.flatten.toArray) := by
  induction entries generalizing ops ctx os with
  | nil =>
    cases ha
    cases h
    exact ⟨LoweringFrame.refl.mono (by simp) (by simp) (by simp), [], .nil, by simpa using hc⟩
  | cons entry entries ih =>
    cases ha
    rename_i op ops hfirst htail
    rcases entry with ⟨inst, key⟩
    simp only [List.map_cons, List.zip_cons_cons, List.forM_eq_forM, List.forM_cons, lowerM_bind_ok] at h
    obtain ⟨_, c, hwire, hrest⟩ := h
    obtain ⟨hf, tile, ht, hchain⟩ := wireBinary_spec hwire hfirst.1 hc hfirst.2 hv
    obtain ⟨hne, hnd⟩ := List.nodup_cons.mp hn
    have htail' := resolvesList_transfer htail (S := fun e o => BinaryAllocated c e.1 o ∧ values (keyOf e.2) = some (.opResult (o.getResult 0)))
      (fun e o hm ho => ⟨ho.1.frame hf (fun he => hne (List.mem_singleton.mp he ▸ hm)), ho.2⟩)
    obtain ⟨hg, tiles, htiles, hchain'⟩ := ih hrest htail' hnd hchain (fun i v h => hf.bounds (.value v) (hv i v h))
    have htile := ht.frame_avoiding hg (fun o ho hm => by
      obtain ⟨e, he⟩ := resolvesList_right_member htail' hm
      exact not_mem_ops_of_detached hchain (by cases e with | mk i _ => cases i; exact he.1.2)
        (by simp [ho]))
    exact ⟨(hf.trans hg).mono (fun _ h => .inl h) (by simp) (by simp), tile :: tiles, .cons htile htiles,
      by simpa [Array.append_assoc] using hchain'⟩

end BinaryLowering

end LoweringConstruction

theorem lowerFunction_checkBlocks {f : ResolvedFunction}
    (h : (lowerFunction block f).run ctx = .ok (op, ctx')) : checkBlocks f = .ok () := by
  simp only [lowerFunction, lowerM_bind_ok] at h
  obtain ⟨_, c, hcheck, _⟩ := h
  cases he : checkBlocks f <;> simp [StateT.run, StateT.lift, he, Functor.map, Except.map] at hcheck
  rfl

theorem lowerM_forM_of_mem {xs : List α} {act : α → LowerM Unit}
    (h : (xs.forM act).run ctx = .ok ((), ctx')) (hm : x ∈ xs) :
    ∃ c d, (act x).run c = .ok ((), d) := by
  induction xs generalizing ctx with
  | nil => simp at hm
  | cons a xs ih =>
    simp only [List.forM_eq_forM, List.forM_cons, lowerM_bind_ok] at h
    obtain ⟨_, c, h1, h2⟩ := h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨ctx, c, h1⟩
    · exact ih h2 hm

theorem lowerModule_checkBlocks (h : lowerModule m = .ok (ctx, root)) :
    ∀ f ∈ m.funcs, checkBlocks f = .ok () := by
  intro f hm
  unfold lowerModule at h
  rcases hc : createModule with _ | ⟨c, r⟩
  · simp [hc, throw, throwThe, MonadExceptOf.throw] at h
  cases hb : (r.getRegion! c.raw 0).getFirstBlock! c.raw
  · simp [hc, hb, throw, throwThe, MonadExceptOf.throw] at h
  rename_i block
  simp only [hc, hb, Except.bind_eq_ok] at h
  obtain ⟨⟨_, d⟩, h, _⟩ := h
  obtain ⟨c', d', h⟩ := lowerM_forM_of_mem h hm
  obtain ⟨op, d'', hl, _⟩ := lowerM_bind_ok.mp h
  exact lowerFunction_checkBlocks hl

theorem LowersModule.checkBlocks (h : LowersModule ctx m root) :
    ∀ f ∈ m.funcs, checkBlocks f = .ok () := by
  obtain ⟨_, _, _, _, _, _, _, hf⟩ := h
  intro f hm
  obtain ⟨op, ho⟩ := resolvesList_mem_left hf hm
  exact ho.checkBlocks

end Veir.LLVMLowering
