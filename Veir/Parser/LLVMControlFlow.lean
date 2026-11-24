import Veir.Parser.LLVMLowering

/-! Resolution and lowering of the LLVM integer fragment with control flow. -/

namespace Veir.LLVMLowering.ControlFlow

open LLVMParserProp
open NameResolutionSketch (NameEnv ResolvedValue ValueId resolveValue resolveBinInst bindings)

abbrev BlockId := Nat
abbrev BlockMap := BlockId → Option BlockPtr

inductive ResolvedInst where
  | bin (result : ValueId) (op : BinOp) (ty : LLType) (lhs rhs : ResolvedValue)
  | phi (result : ValueId) (ty : LLType) (incoming : List (BlockId × ResolvedValue))
  deriving Repr, DecidableEq

inductive ResolvedTerminator where
  | ret (value : ResolvedValue)
  | br (dst : BlockId)
  | condBr (condition : ResolvedValue) (yes no : BlockId)
  deriving Repr, DecidableEq

structure ResolvedBlock where
  insts : List ResolvedInst
  terminator : ResolvedTerminator
  deriving Repr, DecidableEq

structure ResolvedFunction where
  header : FuncHeader
  blocks : Array ResolvedBlock
  deriving Repr, DecidableEq

structure ResolvedModule where
  funcs : List ResolvedFunction
  deriving Repr, DecidableEq

abbrev LabelEnv := String → Option BlockId

def resolveInst (labels : LabelEnv) (values : NameEnv) (inst : Instruction) :
    Option ResolvedInst := do
  let result ← values inst.name
  match inst.inst with
  | .bin bin =>
    let .bin op ty lhs rhs ← resolveBinInst values bin
    return .bin result op ty lhs rhs
  | .phi ty first rest =>
    let incoming ← (first :: rest).mapM fun input => do
      return (← labels input.predecessor, ← resolveValue values input.value)
    return .phi result ty incoming

def resolveTerminator (labels : LabelEnv) (values : NameEnv) (retType : LLType) :
    Terminator → Option ResolvedTerminator
  | .ret tv => do
    guard (tv.ty == retType)
    return .ret (← resolveValue values tv.val)
  | .br dst => return .br (← labels dst)
  | .condBr c yes no => return .condBr (← resolveValue values c) (← labels yes) (← labels no)

def resolveFunction (f : FuncDef) : Option ResolvedFunction := do
  let labelEntries := f.blocks.zipIdx.map fun (b, id) => (b.label, id)
  let valueEntries := bindings f.header (f.blocks.flatMap (·.insts))
  guard (((labelEntries.map Prod.fst) ++ (valueEntries.map Prod.fst)).Nodup)
  let labels : LabelEnv := (labelEntries.lookup ·)
  let values : NameEnv := (valueEntries.lookup ·)
  let blocks ← f.blocks.mapM fun b => do
    return ⟨← b.insts.mapM (resolveInst labels values),
      ← resolveTerminator labels values f.header.retType b.term⟩
  return ⟨f.header, blocks.toArray⟩

def resolveModule (m : Module) : Option ResolvedModule :=
  ResolvedModule.mk <$> m.funcs.mapM resolveFunction

def ResolvedTerminator.successors : ResolvedTerminator → List BlockId
  | .ret _ => []
  | .br dst => [dst]
  | .condBr _ yes no => [yes, no]

def ResolvedInst.phiType : ResolvedInst → Option LLType
  | .bin .. => none
  | .phi _ ty _ => some ty

def normalizeIncoming (ty : LLType) (incoming : BlockId × ResolvedValue) :
    BlockId × ResolvedValue :=
  match ty, incoming with
  | .int w, (src, .intConst n) => (src, .intConst (BitVec.ofInt w n).toInt)
  | _, (src, .ref id) => (src, .ref id)

def checkPhi (preds : List BlockId) : List ResolvedInst → Except LoweringError Unit
  | [] => pure ()
  | .bin .. :: rest =>
    if rest.any (·.phiType.isSome) then throw "phi follows a non-phi instruction" else pure ()
  | .phi _ ty incoming :: rest => do
    unless !incoming.isEmpty && (incoming.map Prod.fst).mergeSort == preds.mergeSort do
      throw "phi incoming blocks do not match the predecessor edges"
    let incoming := incoming.map (normalizeIncoming ty)
    for (pred, value) in incoming do
      unless incoming.lookup pred == some value do
        throw "phi has different values for edges from the same predecessor"
    checkPhi preds rest

def checkBlocks (f : ResolvedFunction) : Except LoweringError Unit := do
  if f.blocks.isEmpty then throw "function has no entry block"
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

/-- Allocate definitions throughout the function before wiring any operands. -/
def allocateDefs (f : ResolvedFunction) (blocks : Array BlockPtr) :
    LowerM (List (ValueId × ValuePtr)) := do
  let mut defs := []
  for (src, block) in f.blocks.toList.zip blocks.toList do
    let mut arg := 0
    for inst in src.insts do
      match inst with
      | .phi result _ _ =>
        defs := (result, .blockArgument { block, index := arg }) :: defs
        arg := arg + 1
      | .bin result op ty lhs rhs =>
        let ptr ← lowerInst block (.bin op ty lhs rhs)
        defs := (result, .opResult (ptr.getResult 0)) :: defs
  return defs

def lowerOperand (block : BlockPtr) (values : ValueMap) (ty : LLType) :
    ResolvedValue → LowerM ValuePtr
  | .ref id => do
    let some value := values id | throw "undefined value"
    return value
  | .intConst n => lowerValue block #[] ty (.intConst n)

def lowerBlockInst (block : BlockPtr) (values : ValueMap) : ResolvedInst → LowerM Unit
  | .phi .. => pure ()
  | .bin result _ ty lhs rhs => do
    let some (.opResult ptr) := values result | throw "missing instruction result"
    let op := ptr.op
    pushValue op (← lowerOperand block values ty lhs)
    pushValue op (← lowerOperand block values ty rhs)
    attachInst block op

/-- Select operands in destination phi order, independently of the order of predecessor entries. -/
def selectPhiInputs (src : BlockId) : List ResolvedInst → Option (List (LLType × ResolvedValue))
  | [] => some []
  | .bin .. :: rest => selectPhiInputs src rest
  | .phi _ ty incoming :: rest => do
    let value ← incoming.lookup src
    return (ty, value) :: (← selectPhiInputs src rest)

def lowerEdge (f : ResolvedFunction) (blocks : Array BlockPtr) (values : ValueMap)
    (block : BlockPtr) (src dst : BlockId) : LowerM (BlockPtr × Array ValuePtr) := do
  let some target := f.blocks[dst]? | throw "invalid branch destination"
  let some ptr := blocks[dst]? | throw "missing branch destination block"
  let some inputs := selectPhiInputs src target.insts | throw "missing phi incoming value"
  let args ← inputs.mapM fun (ty, input) => do
    let arg ← lowerOperand block values ty input
    let ctx ← get
    unless arg.getType! ctx.raw == lowerType ty do throw "phi incoming value has the wrong type"
    return arg
  return (ptr, args.toArray)

def lowerTerminator (f : ResolvedFunction) (blocks : Array BlockPtr) (values : ValueMap)
    (block : BlockPtr) (src : BlockId) : ResolvedTerminator → LowerM Unit
  | .ret value => do
    let v ← lowerOperand block values f.header.retType value
    let _ ← emit .return #[] #[v] #[] () block
  | .br dst => do
    let (b, args) ← lowerEdge f blocks values block src dst
    emitBranch .br args #[b] { loop_annotation := none } block
  | .condBr c yes no => do
    let x ← lowerOperand block values (.int 1) c
    let ctx ← get
    unless x.getType! ctx.raw == lowerType (.int 1) do throw "branch condition must be i1"
    let (y, ys) ← lowerEdge f blocks values block src yes
    let (n, ns) ← lowerEdge f blocks values block src no
    emitBranch .cond_br (#[x] ++ ys ++ ns) #[y, n]
      { branch_weights := ⟨.signless 32, #[]⟩
        loop_annotation := none
        operandSegmentSizes := ⟨.signless 32, #[1, Int.ofNat ys.size, Int.ofNat ns.size]⟩ } block

def lowerFunction (parent : BlockPtr) (f : ResolvedFunction) : LowerM OperationPtr := do
  StateT.lift (checkBlocks f)
  let inputs := f.header.params.toArray.map (lowerType ·.ty)
  let (region, entry) ← createBody inputs
  let blocks ← f.blocks.toList.drop 1 |>.mapM fun b =>
    createBlock region (b.insts.filterMap (fun i => i.phiType.map lowerType)).toArray
  let blocks := (entry :: blocks).toArray
  let defs ← allocateDefs f blocks
  let values : ValueMap
    | .param i => if i < inputs.size then some (.blockArgument { block := entry, index := i }) else none
    | id => defs.lookup id
  for ((b, block), id) in (f.blocks.toList.zip blocks.toList).zipIdx do
    b.insts.forM (lowerBlockInst block values)
    lowerTerminator f blocks values block id b.terminator
  emit .func #[] #[] #[region]
    { sym_name := ⟨f.header.name.toUTF8⟩
      function_type := { inputs := inputs.map Subtype.val, outputs := #[(lowerType f.header.retType).val] }
      extra := defaultFuncExtra } parent

def lowerModule (m : ResolvedModule) : Except LoweringError (WfIRContext OpCode × OperationPtr) := do
  let some (ctx, root) := createModule | throw "could not create module"
  let some block := (root.getRegion! ctx.raw 0).getFirstBlock! ctx.raw
    | throw "module has no body block"
  let (_, ctx) ← (m.funcs.forM fun f => do let _ ← lowerFunction block f).run ctx
  return (ctx, root)

/-- Parse textual LLVM IR, resolve function-local names, and lower to the MLIR LLVM dialect. -/
def parseAndLower (src : String) : Except LoweringError (WfIRContext OpCode × OperationPtr) := do
  let m ← (parse src).mapError (fun err => s!"parse: {reprStr err}")
  let some resolved := resolveModule m | throw "resolveModule failed"
  lowerModule resolved

/-- Use the parser's existing pointwise list relation for the lowering specification. -/
abbrev List.Forall₂ := @NameResolutionSketch.ResolvesList

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

def LowersInstTile (ctx : WfIRContext OpCode) (values : ValueMap) :
    ResolvedInst → List OperationPtr → Prop
  | .bin result op ty lhs rhs, tile =>
    LLVMLowering.LowersInstTile ctx values result (.bin op ty lhs rhs) tile
  | .phi .., tile => tile = []

inductive PhiBindsArg (ctx : IRContext OpCode) (values : ValueMap) :
    ResolvedInst → ValuePtr → Prop where
  | phi : typeOf ctx arg = lowerType ty → values result = some arg →
      PhiBindsArg ctx values (.phi result ty incoming) arg

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

def LowersPhiArgs (ctx : IRContext OpCode) (values : ValueMap) :
    List ResolvedInst → List ValuePtr → Prop :=
  FilterRel (PhiBindsArg ctx values)

def LowersBlockArgs ctx values insts (blockptr : BlockPtr) :=
  LowersPhiArgs ctx values insts (blockptr.getArguments! ctx).toList

def PhiPassesArg (ctx : WfIRContext OpCode) (values : ValueMap)
    (src : BlockId) : ResolvedInst → ArgTile → Prop
  | .phi _ ty incoming, (v, cs) =>
      ∃ input, (src, input) ∈ incoming ∧ OperandTile ctx values ty input v cs
  | _, _ => False

def LowersEdge (ctx : WfIRContext OpCode) (f : ResolvedFunction)
    (blocks : BlockMap) (values : ValueMap) (src dst : BlockId)
    (b : BlockPtr) (args : List ArgTile) : Prop :=
  blocks dst = some b ∧ ∃ block, f.blocks[dst]? = some block ∧
    FilterRel (PhiPassesArg ctx values src) block.insts args

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
      LowersEdge ctx f blocks values src yes y ys ∧
      LowersEdge ctx f blocks values src no n ns ∧
      MatchesTermOp ctx op .cond_br (#[x] ++ argPtrs ys ++ argPtrs ns) #[y, n]
        { branch_weights := ⟨.signless 32, #[]⟩
          loop_annotation := none
          operandSegmentSizes := ⟨.signless 32, #[1, Int.ofNat ys.length, Int.ofNat ns.length]⟩ } ∧
      tile = cs ++ argOps ys ++ argOps ns ++ [op]

def LowersBlock (ctx : WfIRContext OpCode) (f : ResolvedFunction)
    (blocks : BlockMap) (values : ValueMap)
    (id : BlockId) (dst : BlockPtr) : Prop :=
  ∃ src instTiles termTile,
    f.blocks[id]? = some src ∧
    blocks id = some dst ∧
    LowersBlockArgs ctx.raw values src.insts dst ∧
    List.Forall₂ (LowersInstTile ctx values) src.insts instTiles ∧
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
    List.Forall₂ (LowersInstTile ctx values) src.insts instTiles ∧
    LowersTerminatorTile ctx f blocks values 0 src.terminator termTile ∧
    dst.OpChain ctx.raw (instTiles.flatten ++ termTile).toArray

def LowersFunction (ctx : WfIRContext OpCode) (f : ResolvedFunction) (op : OperationPtr) : Prop :=
  ∃ (region : RegionPtr) (body : Array BlockPtr) (entry : BlockPtr) (values : ValueMap),
    MatchesOp ctx op Llvm.func #[] #[] #[region]
      (LLVMFuncProperties.mk ⟨f.header.name.toUTF8⟩
        { inputs := f.header.params.toArray.map (fun p => (lowerType p.ty).val)
          outputs := #[(lowerType f.header.retType).val] } defaultFuncExtra) ∧
    region.BlockChain ctx.raw body ∧ body.size = f.blocks.size ∧
    body[0]? = some entry ∧ LowersEntry ctx f (fun i => body[i]?) values entry ∧
    ∀ i dst, i ≠ 0 → body[i]? = some dst → LowersBlock ctx f (fun j => body[j]?) values i dst

def LowersModule (ctx : WfIRContext OpCode) (m : ResolvedModule) (root : OperationPtr) : Prop :=
  ∃ (region : RegionPtr) (block : BlockPtr) (funcs : List OperationPtr),
    MatchesOp ctx root Builtin.module #[] #[] #[region] default defaultModuleAttrs ∧
    region.BlockChain ctx.raw #[block] ∧ block.OpChain ctx.raw funcs.toArray ∧
    block.getArgumentTypes! ctx.raw = #[] ∧ List.Forall₂ (LowersFunction ctx) m.funcs funcs

def IncomingPhiArg (src : BlockId) : ResolvedInst → LLType × ResolvedValue → Prop
  | .phi _ ty incoming, (t, value) => ty = t ∧ (src, value) ∈ incoming
  | _, _ => False

theorem selectPhiInputs_sound (h : selectPhiInputs src insts = some inputs) :
    FilterRel (IncomingPhiArg src) insts inputs := by
  induction insts generalizing inputs with
  | nil => cases h; exact .nil
  | cons inst rest ih =>
    cases inst with
    | bin => exact .drop (by simp [IncomingPhiArg]) (ih h)
    | phi result ty incoming =>
      simp [selectPhiInputs, Option.bind_eq_some_iff] at h
      obtain ⟨v, hv, tail, ht, rfl⟩ := h
      obtain ⟨_, _, rfl, _⟩ := List.lookup_eq_some_iff.mp hv
      exact .keep ⟨rfl, by simp⟩ (ih ht)

theorem IncomingPhiArg.passes {inst : ResolvedInst} {input : LLType × ResolvedValue}
    {arg : ArgTile} (h : IncomingPhiArg src inst input)
    (hv : OperandTile ctx values input.1 input.2 arg.1 arg.2) :
    PhiPassesArg ctx values src inst arg := by
  rcases input with ⟨ty, value⟩; rcases arg with ⟨ptr, cs⟩
  cases inst with
  | bin => exact False.elim h
  | phi => obtain ⟨rfl, hm⟩ := h; exact ⟨value, hm, hv⟩

theorem PhiPassesArg.hasInput {inst : ResolvedInst} {arg : ArgTile}
    (h : PhiPassesArg ctx values src inst arg) : ∃ input, IncomingPhiArg src inst input := by
  rcases arg with ⟨ptr, cs⟩
  cases inst with
  | bin => exact False.elim h
  | phi _ ty _ => obtain ⟨v, hv, _⟩ := h; exact ⟨(ty, v), rfl, hv⟩

theorem FilterRel.phiPassesArg {ctx : WfIRContext OpCode} {values : ValueMap}
    (h : FilterRel (IncomingPhiArg src) insts inputs)
    (ht : List.Forall₂ (fun input arg => OperandTile ctx values input.1 input.2 arg.1 arg.2)
      inputs args) : FilterRel (PhiPassesArg ctx values src) insts args := by
  induction h generalizing args with
  | nil => cases ht; exact .nil
  | keep h _ ih => cases ht with | cons hv ht => exact .keep (h.passes hv) (ih ht)
  | drop h _ ih => exact .drop (fun ⟨_, hp⟩ => h (PhiPassesArg.hasInput hp)) (ih ht)

end Veir.LLVMLowering.ControlFlow
