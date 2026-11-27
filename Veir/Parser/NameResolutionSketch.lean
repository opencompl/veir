import Veir.Parser.LLVMAST
import Std.Data.String.ToNat

/-! Resolved LLVM functions and declarative name resolution for the integer fragment. -/

namespace Veir.NameResolutionSketch

open LLVMParserProp

/-- Function-local identities distinguish parameters from instruction results. -/
inductive ValueId where
  | param (index : Nat)
  | inst (index : Nat)
  deriving Repr, DecidableEq

/-- Operands refer to definitions rather than containing their expressions. -/
inductive ResolvedValue where
  | ref (id : ValueId)
  | intConst (value : Int)
  deriving Repr, DecidableEq

/-- Instructions are stored once; their operands preserve sharing through IDs. -/
inductive ResolvedBinary where
  | bin (op : BinOp) (ty : LLType) (lhs rhs : ResolvedValue)
  deriving Repr, DecidableEq

/-- Names identify definitions; literals are represented directly in operands. -/
abbrev NameEnv := String → Option ValueId

/-- Definition positions determine identities, independently of their expressions. -/
def bindings (header : FuncHeader) (insts : List Instruction) : List (String × ValueId) :=
  header.params.zipIdx.map (fun (p, i) => (p.name, .param i)) ++
    insts.zipIdx.map (fun (inst, i) => (inst.name, .inst i))

/-- Undefined names have no derivation. -/
inductive ResolvesValue (values : NameEnv) :
    Value → ResolvedValue → Prop where
  | local : values name = some valueId →
      ResolvesValue values (.localIdent name) (.ref valueId)
  | intConst : ResolvesValue values (.intConst value) (.intConst value)
  | boolConst : ResolvesValue values (.boolConst b) (.intConst (if b then 1 else 0))

inductive ResolvesBinInst (values : NameEnv) :
    BinInst → ResolvedBinary → Prop where
  | bin : ResolvesValue values lhs lhs' →
      ResolvesValue values rhs rhs' →
      ResolvesBinInst values ⟨op, ty, lhs, rhs⟩ (.bin op ty lhs' rhs')

/-- Pointwise resolution of equally long lists. -/
inductive ResolvesList (R : α → β → Prop) : List α → List β → Prop where
  | nil : ResolvesList R [] []
  | cons : R a b → ResolvesList R as bs → ResolvesList R (a :: as) (b :: bs)

abbrev BlockId := Nat

/-- An instruction's result ID is its position in the function's flattened instruction list. -/
inductive ResolvedInst where
  | bin (instruction : ResolvedBinary)
  | phi (ty : LLType) (incoming : List (BlockId × ResolvedValue))
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

def ResolvedInst.binary : ResolvedInst → Option ResolvedBinary
  | .bin inst => some inst
  | .phi .. => none

def ValidResolvedValue (numParams numInsts : Nat) : ResolvedValue → Prop
  | .ref (.param i) => i < numParams
  | .ref (.inst i) => i < numInsts
  | .intConst _ => True

def ValidResolvedInst (numParams numInsts numBlocks : Nat) : ResolvedInst → Prop
  | .bin (.bin _ _ lhs rhs) =>
      ValidResolvedValue numParams numInsts lhs ∧ ValidResolvedValue numParams numInsts rhs
  | .phi _ incoming =>
      ∀ edge ∈ incoming, edge.1 < numBlocks ∧ ValidResolvedValue numParams numInsts edge.2

def ValidResolvedTerminator (numParams numInsts numBlocks : Nat) : ResolvedTerminator → Prop
  | .ret value => ValidResolvedValue numParams numInsts value
  | .br dst => dst < numBlocks
  | .condBr value yes no =>
      ValidResolvedValue numParams numInsts value ∧ yes < numBlocks ∧ no < numBlocks

/-- Value and block references are in bounds. -/
def ValidResolvedFunction (f : ResolvedFunction) : Prop :=
  let numParams := f.header.params.length
  let insts := f.blocks.toList.flatMap (·.insts)
  ∀ b ∈ f.blocks.toList,
    (∀ inst ∈ b.insts, ValidResolvedInst numParams insts.length f.blocks.size inst) ∧
    ValidResolvedTerminator numParams insts.length f.blocks.size b.terminator

/-- Resolve a local reference by lookup, preserving integer literals. -/
def resolveValue (env : NameEnv) : Value → Option ResolvedValue
  | .localIdent name => (env name).map .ref
  | .intConst value => some (.intConst value)
  | .boolConst b => some (.intConst (if b then 1 else 0))

def resolveBinInst (env : NameEnv) (inst : BinInst) : Option ResolvedBinary := do
  let lhs ← resolveValue env inst.lhs
  let rhs ← resolveValue env inst.rhs
  return .bin inst.op inst.ty lhs rhs

theorem resolveValue_sound (env : NameEnv) (v : Value) (r : ResolvedValue) :
    resolveValue env v = some r → ResolvesValue env v r := by
  cases v <;> simp [resolveValue, Option.map_eq_some_iff] <;>
    grind [ResolvesValue]

theorem resolveBinInst_sound (env : NameEnv) (inst : BinInst) (r : ResolvedBinary) :
    resolveBinInst env inst = some r → ResolvesBinInst env inst r := by
  cases inst
  simp [resolveBinInst, Option.bind_eq_some_iff]
  grind [resolveValue_sound, ResolvesBinInst]

theorem resolveValue_complete (env : NameEnv) (v : Value) (r : ResolvedValue) :
    ResolvesValue env v r → resolveValue env v = some r := by
  intro h; cases h <;> simp [resolveValue, *]

theorem resolveBinInst_complete (env : NameEnv) (inst : BinInst) (r : ResolvedBinary) :
    ResolvesBinInst env inst r → resolveBinInst env inst = some r := by
  rintro ⟨hl, hr⟩
  simp [resolveBinInst, resolveValue_complete _ _ _ hl, resolveValue_complete _ _ _ hr]

theorem resolvesList_mapM_iff (f : α → Option β) (R : α → β → Prop)
    (h : ∀ a b, f a = some b ↔ R a b) (xs : List α) (ys : List β) :
    xs.mapM f = some ys ↔ ResolvesList R xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [ResolvesList.nil]; grind [ResolvesList]
  | cons x xs ih =>
    cases ys <;> simp [List.mapM_cons, Option.bind_eq_some_iff]
    all_goals grind [ResolvesList]

abbrev LabelEnv := String → Option BlockId

def ResolvedValue.normalize (ty : LLType) : ResolvedValue → ResolvedValue
  | .ref id => .ref id
  | .intConst n => match ty with
    | .int w => .intConst (BitVec.ofInt w n).toInt

def resolveIncoming (labels : LabelEnv) (values : NameEnv) (ty : LLType) (input : PhiIncoming) :
    Option (BlockId × ResolvedValue) := do
  return (← labels input.predecessor, (← resolveValue values input.value).normalize ty)

def resolveInst (labels : LabelEnv) (values : NameEnv) : Inst → Option ResolvedInst
  | .bin bin => ResolvedInst.bin <$> resolveBinInst values bin
  | .phi ty incoming => ResolvedInst.phi ty <$> incoming.mapM (resolveIncoming labels values ty)

def resolveTerminator (labels : LabelEnv) (values : NameEnv) (retType : LLType) :
    Terminator → Option ResolvedTerminator
  | .ret tv => do
    guard (tv.ty == retType)
    return .ret (← resolveValue values tv.val)
  | .br dst => return .br (← labels dst)
  | .condBr c yes no => return .condBr (← resolveValue values c) (← labels yes) (← labels no)

def resolveBlock (labels : LabelEnv) (values : NameEnv) (retType : LLType) (b : BasicBlock) :
    Option ResolvedBlock := do
  return ⟨← b.insts.mapM (fun i => resolveInst labels values i.inst),
    ← resolveTerminator labels values retType b.term⟩

def labelBindings (f : FuncDef) : List (String × BlockId) :=
  f.blocks.zipIdx.map fun (b, id) => (b.label, id)

def valueBindings (f : FuncDef) : List (String × ValueId) :=
  bindings f.header (f.blocks.flatMap (·.insts))

def resolveFunction (f : FuncDef) : Option ResolvedFunction := do
  let labelEntries := labelBindings f
  let valueEntries := valueBindings f
  guard (((labelEntries.map Prod.fst) ++ (valueEntries.map Prod.fst)).Nodup)
  let labels : LabelEnv := (labelEntries.lookup ·)
  let values : NameEnv := (valueEntries.lookup ·)
  let blocks ← f.blocks.mapM (resolveBlock labels values f.header.retType)
  return ⟨f.header, blocks.toArray⟩

def resolveModule (m : Module) : Option ResolvedModule :=
  ResolvedModule.mk <$> m.funcs.mapM resolveFunction

def ResolvesIncoming (labels : LabelEnv) (values : NameEnv) (ty : LLType) (input : PhiIncoming)
    (r : BlockId × ResolvedValue) : Prop :=
  labels input.predecessor = some r.1 ∧ ∃ v, ResolvesValue values input.value v ∧ v.normalize ty = r.2

inductive ResolvesInst (labels : LabelEnv) (values : NameEnv) : Inst → ResolvedInst → Prop
  | bin : ResolvesBinInst values inst bin →
      ResolvesInst labels values (.bin inst) (.bin bin)
  | phi : ResolvesList (ResolvesIncoming labels values ty) inputs incoming →
      ResolvesInst labels values (.phi ty inputs) (.phi ty incoming)

inductive ResolvesTerminator (labels : LabelEnv) (values : NameEnv) (retType : LLType) :
    Terminator → ResolvedTerminator → Prop
  | ret : tv.ty = retType → ResolvesValue values tv.val r →
      ResolvesTerminator labels values retType (.ret tv) (.ret r)
  | br : labels dst = some target → ResolvesTerminator labels values retType (.br dst) (.br target)
  | condBr : ResolvesValue values c r → labels yes = some y → labels no = some n →
      ResolvesTerminator labels values retType (.condBr c yes no) (.condBr r y n)

def ResolvesBlock (labels : LabelEnv) (values : NameEnv) (retType : LLType) (b : BasicBlock)
    (r : ResolvedBlock) : Prop :=
  ResolvesList (fun i => ResolvesInst labels values i.inst) b.insts r.insts ∧
    ResolvesTerminator labels values retType b.term r.terminator

def ResolvesFunction (f : FuncDef) (r : ResolvedFunction) : Prop :=
  let labels := labelBindings f
  let values := valueBindings f
  ((labels.map Prod.fst) ++ (values.map Prod.fst)).Nodup ∧ r.header = f.header ∧
    ResolvesList (ResolvesBlock (labels.lookup ·) (values.lookup ·) f.header.retType)
      f.blocks r.blocks.toList

def ResolvesModule (m : Module) (r : ResolvedModule) : Prop :=
  ResolvesList ResolvesFunction m.funcs r.funcs

theorem resolveValue_iff (values : NameEnv) (v : Value) (r : ResolvedValue) :
    resolveValue values v = some r ↔ ResolvesValue values v r :=
  ⟨resolveValue_sound _ _ _, resolveValue_complete _ _ _⟩

theorem resolveIncoming_iff (labels : LabelEnv) (values : NameEnv) (ty : LLType) (input : PhiIncoming)
    (r : BlockId × ResolvedValue) :
    resolveIncoming labels values ty input = some r ↔ ResolvesIncoming labels values ty input r := by
  cases r
  simp [resolveIncoming, ResolvesIncoming, Option.bind_eq_some_iff, resolveValue_iff]
  grind

theorem resolveInst_iff (labels : LabelEnv) (values : NameEnv) (i : Inst) (r : ResolvedInst) :
    resolveInst labels values i = some r ↔ ResolvesInst labels values i r := by
  cases i <;>
    simp only [resolveInst, Functor.map, Option.map_eq_some_iff,
      resolvesList_mapM_iff _ _ (resolveIncoming_iff labels values _)] <;>
    grind [ResolvesInst, resolveBinInst_sound, resolveBinInst_complete]

theorem resolveTerminator_iff (labels : LabelEnv) (values : NameEnv) (retType : LLType)
    (t : Terminator) (r : ResolvedTerminator) :
    resolveTerminator labels values retType t = some r ↔ ResolvesTerminator labels values retType t r := by
  cases t <;> cases r <;>
    simp [resolveTerminator, guard, Option.bind_eq_some_iff, resolveValue_iff,
      iff_iff_implies_and_implies] <;> grind [ResolvesTerminator]

theorem resolveBlock_iff (labels : LabelEnv) (values : NameEnv) (retType : LLType)
    (b : BasicBlock) (r : ResolvedBlock) :
    resolveBlock labels values retType b = some r ↔ ResolvesBlock labels values retType b r := by
  cases r
  simp [resolveBlock, ResolvesBlock, Option.bind_eq_some_iff, resolveTerminator_iff,
    resolvesList_mapM_iff _ _ (fun (i : Instruction) => resolveInst_iff labels values i.inst)] <;> grind

theorem resolveFunction_iff (f : FuncDef) (r : ResolvedFunction) :
    resolveFunction f = some r ↔ ResolvesFunction f r := by
  cases r
  simp [resolveFunction, ResolvesFunction, guard, Option.bind_eq_some_iff,
    resolvesList_mapM_iff _ _ (resolveBlock_iff _ _ _), eq_comm (a := f.header),
    ← Array.toList_inj, and_left_comm]

theorem resolveModule_iff (m : Module) (r : ResolvedModule) :
    resolveModule m = some r ↔ ResolvesModule m r := by
  cases r
  simp [resolveModule, ResolvesModule, Option.map_eq_some_iff,
    resolvesList_mapM_iff _ _ resolveFunction_iff]

def ResolvedTerminator.successors : ResolvedTerminator → List BlockId
  | .ret _ => []
  | .br dst => [dst]
  | .condBr _ yes no => [yes, no]


-- inductive BlockHasEdge : ResolvedFunction → BlockId → BlockId → Prop
--   | br : f.blocks[src]? = some b ∧ b.terminator = (ResolvedTerminator.br dst) → BlockHasEdge f src dst
--   | condT : f.blocks[src]? = some b ∧ b.terminator = (.condBr _ dst _) → BlockHasEdge f src dst
--   | condF : f.blocks[src]? = some b ∧ b.terminator = (.condBr _ _ dst) → BlockHasEdge f src dst

-- inductive BlockPreds : List ResolvedBlock → BlockId → List BlockId → Prop
--   | empty : BlockPreds [] b []
--   | br : BlockPreds xs b ys → b1.terminator = (.br dst) → BlockPreds (b1 :: xs) b (dst :: ys)
--   | condTrue : BlockPreds xs b ys → d1 ≠ dst →  b1.terminator = (.condBr _ dst d1) → BlockPreds (b1 :: xs) b (dst :: ys)
--   | condFalse : BlockPreds xs b ys → d1 ≠ dst →  b1.terminator = (.condBr _ d1 dst) → BlockPreds (b1 :: xs) b (dst :: ys)
--   | condBoth : BlockPreds xs b ys → b1.terminator = (.condBr _ dst dst) → BlockPreds (b1 :: xs) b (dst :: dst :: ys)

def ResolvedInst.phiType : ResolvedInst → Option LLType
  | .bin .. => none
  | .phi ty _ => some ty

/-- Each source occurs once in `preds` for each of its edges to `dst`. -/
def HasPredEdges (f : ResolvedFunction) (dst : BlockId) (preds : List BlockId) : Prop :=
  ∀ src : BlockId,
    preds.count src =
      match f.blocks[src]? with
      | none => 0
      | some b => b.terminator.successors.count dst

/-- Repeated phi entries for the same predecessor carry one resolved value. -/
def PhiInputsAgree (incoming : List (BlockId × ResolvedValue)) : Prop :=
  ∀ v ∈ incoming, ∀ w ∈ incoming, v.1 = w.1 → v.2 = w.2

instance : DecidablePred PhiInputsAgree := fun _ => inferInstanceAs (Decidable (∀ _ ∈ _, ∀ _ ∈ _, _))

def ResolvedFunction.valueType (f : ResolvedFunction) : ValueId → Option LLType
  | .param i => f.header.params[i]?.map (·.ty)
  | .inst i => ((f.blocks.toList.flatMap (·.insts))[i]?).map fun
    | .bin (.bin _ ty _ _) => ty
    | .phi ty _ => ty

def ResolvedFunction.HasType (f : ResolvedFunction) (ty : LLType) : ResolvedValue → Prop
  | .intConst _ => True
  | .ref id => f.valueType id = some ty

def WellFormedResolvedInst (f : ResolvedFunction) (dst : BlockId) : ResolvedInst → Prop
  | .bin (.bin _ ty lhs rhs) => f.HasType ty lhs ∧ f.HasType ty rhs
  | .phi ty incoming =>
      HasPredEdges f dst (incoming.map Prod.fst) ∧ PhiInputsAgree incoming ∧
      ∀ edge ∈ incoming, f.HasType ty edge.2

def WellFormedResolvedTerminator (f : ResolvedFunction) : ResolvedTerminator → Prop
  | .ret v => f.HasType f.header.retType v
  | .br dst => dst ≠ 0
  | .condBr c yes no => f.HasType (.int 1) c ∧ yes ≠ 0 ∧ no ≠ 0

def WellFormedResolvedFunction (f : ResolvedFunction) : Prop :=
  ValidResolvedFunction f ∧ 0 < f.blocks.size ∧
  ∀ b dst, (b, dst) ∈ f.blocks.toList.zipIdx →
    (dst = 0 → ∀ i ∈ b.insts, i.phiType = none) ∧
    b.insts.Pairwise (fun earlier later => later.phiType ≠ none → earlier.phiType ≠ none) ∧
    (∀ i ∈ b.insts, WellFormedResolvedInst f dst i) ∧
    WellFormedResolvedTerminator f b.terminator

def ValidResolvedModule (m : ResolvedModule) : Prop :=
  ∀ f ∈ m.funcs, WellFormedResolvedFunction f

def ResolvedFunction.eraseLocalNames (f : ResolvedFunction) : ResolvedFunction :=
  { f with header := { f.header with params := f.header.params.map fun p => { p with name := "" } } }

def ResolvedInst.normalizeLiterals : ResolvedInst → ResolvedInst
  | .bin (.bin op ty lhs rhs) => .bin (.bin op ty (lhs.normalize ty) (rhs.normalize ty))
  | .phi ty incoming => .phi ty (incoming.map fun (src, v) => (src, v.normalize ty))

def ResolvedTerminator.normalizeLiterals (retType : LLType) : ResolvedTerminator → ResolvedTerminator
  | .ret v => .ret (v.normalize retType)
  | .br dst => .br dst
  | .condBr v yes no => .condBr (v.normalize (.int 1)) yes no

def ResolvedFunction.normalizeLiterals (f : ResolvedFunction) : ResolvedFunction :=
  { f with blocks := f.blocks.map fun b =>
    { b with insts := b.insts.map ResolvedInst.normalizeLiterals
             terminator := b.terminator.normalizeLiterals f.header.retType } }

/-- Compare resolved functions up to local names and bit patterns of integer literals. -/
def EqModuloRenaming (f g : ResolvedFunction) : Prop :=
  f.normalizeLiterals.eraseLocalNames = g.normalizeLiterals.eraseLocalNames

/-- Compare resolved modules up to local names and the spelling of integer literals. -/
def ResolvedModule.Equiv (m m' : ResolvedModule) : Prop :=
  ResolvesList EqModuloRenaming m.funcs m'.funcs

def ValueId.sourceName : ValueId → String
  | .param i => "arg" ++ toString i
  | .inst i => "v" ++ toString i

def blockName (id : BlockId) : String := "bb" ++ toString id

def unresolveValue : ResolvedValue → Value
  | .ref id => .localIdent id.sourceName
  | .intConst n => .intConst n

def unresolveInst : ResolvedInst → Inst
  | .bin (.bin op ty lhs rhs) => .bin ⟨op, ty, unresolveValue lhs, unresolveValue rhs⟩
  | .phi ty incoming =>
    .phi ty (incoming.map fun (pred, value) => ⟨unresolveValue value, blockName pred⟩)

def unresolveTerminator (retType : LLType) : ResolvedTerminator → Terminator
  | .ret v => .ret ⟨retType, unresolveValue v⟩
  | .br dst => .br (blockName dst)
  | .condBr v yes no => .condBr (unresolveValue v) (blockName yes) (blockName no)

def unresolveBlocks (retType : LLType) (nextInst : Nat) :
    List (ResolvedBlock × BlockId) → List BasicBlock
  | [] => []
  | (block, id) :: rest =>
    let insts := (block.insts.zipIdx nextInst).map fun (inst, i) =>
      ⟨(ValueId.inst i).sourceName, unresolveInst inst⟩
    ⟨blockName id, insts, unresolveTerminator retType block.terminator⟩ ::
      unresolveBlocks retType (nextInst + block.insts.length) rest

/-- Reconstruct the source AST with distinct names for parameters, results, and blocks. -/
def unresolveFunction (f : ResolvedFunction) : FuncDef :=
  let params := f.header.params.mapIdx fun i p => { p with name := (ValueId.param i).sourceName }
  ⟨{ f.header with params }, unresolveBlocks f.header.retType 0 f.blocks.toList.zipIdx⟩

/-- Reconstruct the source AST for each function in module order. -/
def unresolveModule (m : ResolvedModule) : Module :=
  ⟨m.funcs.map unresolveFunction⟩

theorem generatedName_injective (stem : String) :
    ∀ {i j : Nat}, stem ++ toString i = stem ++ toString j → i = j :=
  fun h => Nat.repr_inj.mp ((String.append_right_inj stem).mp h)

theorem generatedName_ne {p q : String} {c d : Char}
    (hp : p.toList.head? = some c) (hq : q.toList.head? = some d)
    (h : c ≠ d) (i j : Nat) : p ++ toString i ≠ q ++ toString j := by
  intro he
  apply h
  simpa [String.toList_append, List.head?_append, hp, hq] using
    congrArg (fun s : String => s.toList.head?) he

theorem unresolveBlocks_labels (retType : LLType) (blocks : List ResolvedBlock) (i j : Nat) :
    (unresolveBlocks retType i (blocks.zipIdx j)).map BasicBlock.label =
      (blocks.zipIdx j).map (fun b => blockName b.2) := by
  induction blocks generalizing i j with
  | nil => rfl
  | cons b bs ih => simp [unresolveBlocks, ih]

theorem unresolveBlocks_insts (retType : LLType) (blocks : List ResolvedBlock) (i j : Nat) :
    (unresolveBlocks retType i (blocks.zipIdx j)).flatMap BasicBlock.insts =
      ((blocks.flatMap ResolvedBlock.insts).zipIdx i).map
        (fun (inst, k) => ⟨(ValueId.inst k).sourceName, unresolveInst inst⟩) := by
  induction blocks generalizing i j with
  | nil => rfl
  | cons b bs ih => simp [unresolveBlocks, List.zipIdx_append, ih]

theorem generatedBindings_zipIdx (xs : List α) (name : Nat → String) (id : Nat → β) :
    (xs.mapIdx (fun i _ => name i)).zipIdx.map (fun (s, i) => (s, id i)) =
      (List.range xs.length).map (fun i => (name i, id i)) := by
  simp only [List.mapIdx_eq_zipIdx_map]
  rw [List.range_eq_range']
  apply List.ext_getElem?
  simp [List.getElem?_zipIdx, Function.comp_def]
  intro i
  by_cases h : i < xs.length <;> simp [h]

theorem bindings_zipIdx_map (xs : List α) (name : α → String) (id : Nat → β) :
    (xs.map name).zipIdx.map (fun (s, i) => (s, id i)) =
      xs.zipIdx.map (fun (x, i) => (name x, id i)) := by
  simp [List.zipIdx_map, List.map_map, Function.comp_def]

theorem labelBindings_unresolve (f : ResolvedFunction) :
    labelBindings (unresolveFunction f) =
      (List.range f.blocks.size).map (fun i => (blockName i, i)) := by
  unfold labelBindings unresolveFunction
  rw [← bindings_zipIdx_map _ BasicBlock.label (fun i => i), unresolveBlocks_labels]
  simpa [List.mapIdx_eq_zipIdx_map] using
    generatedBindings_zipIdx f.blocks.toList blockName (fun i => i)

theorem valueBindings_unresolve (f : ResolvedFunction) :
    valueBindings (unresolveFunction f) =
      (List.range f.header.params.length).map (fun i => ((ValueId.param i).sourceName, .param i)) ++
      (List.range (f.blocks.toList.flatMap ResolvedBlock.insts).length).map
        (fun i => ((ValueId.inst i).sourceName, .inst i)) := by
  unfold valueBindings unresolveFunction bindings
  dsimp only
  rw [unresolveBlocks_insts]
  congr 1
  · rw [← bindings_zipIdx_map _ Param.name]
    simpa [List.mapIdx_eq_zipIdx_map, List.map_map, Function.comp_def] using
      generatedBindings_zipIdx f.header.params (fun i => (ValueId.param i).sourceName) ValueId.param
  · rw [← bindings_zipIdx_map _ Instruction.name]
    simpa [List.mapIdx_eq_zipIdx_map, List.map_map, Function.comp_def] using
      generatedBindings_zipIdx (f.blocks.toList.flatMap ResolvedBlock.insts)
        (fun i => (ValueId.inst i).sourceName) ValueId.inst

theorem nodup_generated (name : Nat → String) (n : Nat)
    (h : ∀ {i j}, name i = name j → i = j) : ((List.range n).map name).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  exact List.nodup_range.imp (fun hne he => hne (h he))

theorem unresolve_names_nodup (f : ResolvedFunction) :
    (((labelBindings (unresolveFunction f)).map Prod.fst) ++
      ((valueBindings (unresolveFunction f)).map Prod.fst)).Nodup := by
  rw [labelBindings_unresolve, valueBindings_unresolve]
  simp only [List.map_append, List.map_map, Function.comp_def, List.nodup_append, List.mem_map, List.mem_append]
  refine ⟨nodup_generated _ _ (generatedName_injective "bb"),
    ⟨nodup_generated _ _ (generatedName_injective "arg"),
     nodup_generated _ _ (generatedName_injective "v"), ?_⟩, ?_⟩
  · rintro _ ⟨i, _, rfl⟩ _ ⟨j, _, rfl⟩
    exact generatedName_ne (p := "arg") (q := "v") rfl rfl (by decide) i j
  · rintro _ ⟨i, _, rfl⟩ _ (⟨j, _, rfl⟩ | ⟨j, _, rfl⟩)
    · exact generatedName_ne (p := "bb") (q := "arg") rfl rfl (by decide) i j
    · exact generatedName_ne (p := "bb") (q := "v") rfl rfl (by decide) i j

theorem lookup_of_nodup_keys [BEq α] [LawfulBEq α] {es : List (α × β)}
    (hn : (es.map Prod.fst).Nodup) (h : (key, value) ∈ es) :
    es.lookup key = some value := by
  induction es with
  | nil => contradiction
  | cons e es ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact List.lookup_cons_self
    · have hk : key ∈ es.map Prod.fst := List.mem_map.mpr ⟨_, h, rfl⟩
      have hne := (List.nodup_cons.mp hn).1
      have hkey : key ≠ e.1 := fun he => hne (he ▸ hk)
      rw [List.lookup_cons, beq_eq_false_iff_ne.mpr hkey]
      exact ih (List.nodup_cons.mp hn).2 h

theorem unresolve_lookup_block (f : ResolvedFunction) {i : BlockId} (h : i < f.blocks.size) :
    (labelBindings (unresolveFunction f)).lookup (blockName i) = some i := by
  apply lookup_of_nodup_keys (List.nodup_append.mp (unresolve_names_nodup f)).1
  rw [labelBindings_unresolve]
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr h, rfl⟩

theorem unresolve_lookup_value (f : ResolvedFunction) (id : ValueId)
    (h : ValidResolvedValue f.header.params.length
      (f.blocks.toList.flatMap ResolvedBlock.insts).length (.ref id)) :
    (valueBindings (unresolveFunction f)).lookup id.sourceName = some id := by
  apply lookup_of_nodup_keys (List.nodup_append.mp (unresolve_names_nodup f)).2.1
  rw [valueBindings_unresolve]
  cases id with
  | param i => exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr h, rfl⟩)
  | inst i => exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr h, rfl⟩)

theorem ResolvesList.map_of_mem {xs : List α} {F : α → β} {G : α → γ}
    (h : ∀ x ∈ xs, R (F x) (G x)) : ResolvesList R (xs.map F) (xs.map G) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

def ResolvedInst.normalizePhiLiterals : ResolvedInst → ResolvedInst
  | .phi ty incoming => .phi ty (incoming.map fun (src, v) => (src, v.normalize ty))
  | inst => inst

theorem ResolvedValue.normalize_idem (v : ResolvedValue) (ty : LLType) :
    (v.normalize ty).normalize ty = v.normalize ty := by
  cases ty
  cases v <;> simp only [ResolvedValue.normalize, BitVec.ofInt_toInt]

theorem ResolvedInst.normalizePhiLiterals_normalizeLiterals (inst : ResolvedInst) :
    inst.normalizePhiLiterals.normalizeLiterals = inst.normalizeLiterals := by
  cases inst <;> simp [ResolvedInst.normalizePhiLiterals, ResolvedInst.normalizeLiterals,
    List.map_map, Function.comp_def, ResolvedValue.normalize_idem]

theorem unresolve_resolves_value (f : ResolvedFunction) (v : ResolvedValue)
    (h : ValidResolvedValue f.header.params.length
      (f.blocks.toList.flatMap ResolvedBlock.insts).length v) :
    ResolvesValue ((valueBindings (unresolveFunction f)).lookup ·) (unresolveValue v) v :=
  match v with
  | .ref id => .local (unresolve_lookup_value f id h)
  | .intConst _ => .intConst

theorem unresolve_resolves_inst (f : ResolvedFunction) (inst : ResolvedInst)
    (h : ValidResolvedInst f.header.params.length
      (f.blocks.toList.flatMap ResolvedBlock.insts).length f.blocks.size inst) :
    ResolvesInst ((labelBindings (unresolveFunction f)).lookup ·)
      ((valueBindings (unresolveFunction f)).lookup ·) (unresolveInst inst) inst.normalizePhiLiterals := by
  cases inst with
  | bin inst =>
    cases inst
    exact .bin (.bin (unresolve_resolves_value _ _ h.1) (unresolve_resolves_value _ _ h.2))
  | phi ty incoming =>
    apply ResolvesInst.phi
    apply ResolvesList.map_of_mem
    rintro ⟨pred, v⟩ hi
    exact ⟨unresolve_lookup_block f (h _ hi).1, v, unresolve_resolves_value f v (h _ hi).2, rfl⟩

theorem unresolve_resolves_terminator (f : ResolvedFunction) (term : ResolvedTerminator)
    (h : ValidResolvedTerminator f.header.params.length
      (f.blocks.toList.flatMap ResolvedBlock.insts).length f.blocks.size term) :
    ResolvesTerminator ((labelBindings (unresolveFunction f)).lookup ·)
      ((valueBindings (unresolveFunction f)).lookup ·) f.header.retType
      (unresolveTerminator f.header.retType term) term :=
  match term with
  | .ret v => .ret rfl (unresolve_resolves_value f v h)
  | .br _ => .br (unresolve_lookup_block f h)
  | .condBr v _ _ => .condBr (unresolve_resolves_value f v h.1)
      (unresolve_lookup_block f h.2.1) (unresolve_lookup_block f h.2.2)

theorem unresolve_resolves_insts (f : ResolvedFunction) (insts : List ResolvedInst) (i : Nat)
    (h : ∀ inst ∈ insts, ValidResolvedInst f.header.params.length
      (f.blocks.toList.flatMap ResolvedBlock.insts).length f.blocks.size inst) :
    ResolvesList (fun a : Instruction =>
      ResolvesInst ((labelBindings (unresolveFunction f)).lookup ·)
        ((valueBindings (unresolveFunction f)).lookup ·) a.inst)
      ((insts.zipIdx i).map fun (inst, k) => ⟨(ValueId.inst k).sourceName, unresolveInst inst⟩)
      (insts.map ResolvedInst.normalizePhiLiterals) := by
  induction insts generalizing i with
  | nil => exact .nil
  | cons inst rest ih =>
    exact .cons (unresolve_resolves_inst f inst (h inst (by simp)))
      (ih (i + 1) fun x hx => h x (by simp [hx]))

theorem unresolve_resolves_blocks (f : ResolvedFunction) (hf : ValidResolvedFunction f)
    (bs : List ResolvedBlock) (h : ∀ b ∈ bs, b ∈ f.blocks.toList) (i j : Nat) :
    ResolvesList (ResolvesBlock ((labelBindings (unresolveFunction f)).lookup ·)
      ((valueBindings (unresolveFunction f)).lookup ·) f.header.retType)
      (unresolveBlocks f.header.retType i (bs.zipIdx j))
      (bs.map fun b => { b with insts := b.insts.map ResolvedInst.normalizePhiLiterals }) := by
  induction bs generalizing i j with
  | nil => exact .nil
  | cons b bs ih =>
    have hb := hf b (h b (by simp))
    exact .cons ⟨unresolve_resolves_insts f b.insts i hb.1, unresolve_resolves_terminator f _ hb.2⟩
      (ih (fun x hx => h x (by simp [hx])) _ _)

theorem resolveFunction_round_trip (f : ResolvedFunction) : ValidResolvedFunction f →
    ∃ g, resolveFunction (unresolveFunction f) = some g ∧ EqModuloRenaming g f := by
  intro hf
  let g : ResolvedFunction := ⟨(unresolveFunction f).header,
    f.blocks.map fun b => { b with insts := b.insts.map ResolvedInst.normalizePhiLiterals }⟩
  refine ⟨g, (resolveFunction_iff _ _).mpr ⟨unresolve_names_nodup f, rfl, ?_⟩, ?_⟩
  · simpa [g, unresolveFunction] using unresolve_resolves_blocks f hf f.blocks.toList (fun _ h => h) 0 0
  · simp [g, EqModuloRenaming, ResolvedFunction.normalizeLiterals, ResolvedFunction.eraseLocalNames,
      unresolveFunction, List.mapIdx_eq_zipIdx_map, List.map_map, Function.comp_def,
      ResolvedInst.normalizePhiLiterals_normalizeLiterals]
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map fun p : Param => { p with name := "" })
        (List.zipIdx_map_fst 0 f.header.params)

theorem resolve_round_trip (m : ResolvedModule) : ValidResolvedModule m →
    ∃ m', resolveModule (unresolveModule m) = some m' ∧ m'.Equiv m := by
  obtain ⟨fs⟩ := m
  simp only [ValidResolvedModule, unresolveModule, resolveModule_iff, ResolvesModule, ResolvedModule.Equiv]
  induction fs with
  | nil => exact fun _ => ⟨⟨[]⟩, .nil, .nil⟩
  | cons f fs ih =>
    intro h
    obtain ⟨g, hg, he⟩ := resolveFunction_round_trip f (h f (by simp)).1
    obtain ⟨m', hr, hm⟩ := ih (fun x hx => h x (by simp [hx]))
    exact ⟨⟨g :: m'.funcs⟩, .cons ((resolveFunction_iff _ _).mp hg) hr, .cons he hm⟩

end Veir.NameResolutionSketch
