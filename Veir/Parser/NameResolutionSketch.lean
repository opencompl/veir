import Veir.Parser.LLVMAST

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
  label : String
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
  return ⟨b.label, ← b.insts.mapM (fun i => resolveInst labels values i.inst),
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
  b.label = r.label ∧ ResolvesList (fun i => ResolvesInst labels values i.inst) b.insts r.insts ∧
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

def ResolvedFunction.eraseLocalNames (f : ResolvedFunction) : ResolvedFunction :=
  { header := { f.header with params := f.header.params.map fun p => { p with name := "" } }
    blocks := f.blocks.map fun b => { b with label := "" } }

def EqModuloRenaming (f g : ResolvedFunction) : Prop :=
  f.eraseLocalNames = g.eraseLocalNames

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

/-- Compare resolved modules up to local names and the spelling of integer literals. -/
def ResolvedModule.Equiv (m m' : ResolvedModule) : Prop :=
  ResolvesList (fun f g => EqModuloRenaming f.normalizeLiterals g.normalizeLiterals) m.funcs m'.funcs

/-- Placeholder for reconstructing a source AST from all resolved blocks. -/
noncomputable def unresolveFunction (_ : ResolvedFunction) : FuncDef := by
  sorry

theorem resolve_round_trip (f : ResolvedFunction) :
    ValidResolvedFunction f →
      ∃ g, resolveFunction (unresolveFunction f) = some g ∧ EqModuloRenaming g f := by
  sorry

end Veir.NameResolutionSketch
