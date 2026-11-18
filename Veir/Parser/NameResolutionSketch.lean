import Veir.Parser.LLVMAST
import Init.Data.Nat.ToString

/-! A minimal resolution relation for the complete De Morgan example. -/

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
inductive ResolvedAST where
  | bin (op : BinOp) (ty : LLType) (lhs rhs : ResolvedValue)
  deriving Repr, DecidableEq

/-- Names identify definitions; literals are represented directly in operands. -/
abbrev NameEnv := String → Option ValueId




/-- Definition positions determine identities, independently of their expressions. -/
def bindings (header : FuncHeader) (insts : List Instruction) : List (String × ValueId) :=
  header.params.zipIdx.map (fun (p, i) => (p.name, .param i)) ++
    insts.zipIdx.map (fun (inst, i) => (inst.name, .inst i))

def environment (header : FuncHeader) (insts : List Instruction) : NameEnv :=
  (List.lookup · $ bindings header insts)

theorem environment_mem (header : FuncHeader) (insts : List Instruction)
    (name : String) (id : ValueId) :
    environment header insts name = some id → (name, id) ∈ bindings header insts := by
  grind [environment, List.lookup_eq_some_iff]

/-- Undefined names have no derivation. -/
inductive ResolvesValue (values : NameEnv) :
    Value → ResolvedValue → Prop where
  | local : values name = some valueId →
      ResolvesValue values (.localIdent name) (.ref valueId)
  | intConst : ResolvesValue values (.intConst value) (.intConst value)

inductive ResolvesBinInst (values : NameEnv) :
    BinInst → ResolvedAST → Prop where
  | bin : ResolvesValue values lhs lhs' →
      ResolvesValue values rhs rhs' →
      ResolvesBinInst values ⟨op, ty, lhs, rhs⟩ (.bin op ty lhs' rhs')

inductive HasEnv3 (n : NameEnv) (header : FuncHeader) (insts : List Instruction) : Prop where
    | mk : (∀ pj  ∈ header.params.zipIdx, n pj.1.name = some (.param pj.2)) →
    (∀ ij  ∈ insts.zipIdx, n ij.1.name = some (.inst ij.2)) →
    (∀ name id, n name = some id → (name, id) ∈ bindings header insts) →
      HasEnv3 n header insts


theorem HasEnv3.binding (h : HasEnv3 n header insts) :
    ∀ p ∈ bindings header insts, n p.1 = some p.2 := by
  cases h; grind [bindings]

theorem HasEnv3.environment_eq (h : HasEnv3 n header insts) :
    n = environment header insts := by
  funext name
  have hb := h.binding
  rcases h with ⟨_, _, hc⟩
  cases hn : n name <;> cases he : environment header insts name <;>
    grind [environment_mem, environment, List.lookup_eq_none_iff]

/-- Pointwise resolution of equally long lists. -/
inductive ResolvesList (R : α → β → Prop) : List α → List β → Prop where
  | nil : ResolvesList R [] []
  | cons : R a b → ResolvesList R as bs → ResolvesList R (a :: as) (b :: bs)

/-- A resolved single-block function, retaining its source header and block label. -/
structure ResolvedFunction where
  header : FuncHeader
  label : String
  insts : List ResolvedAST
  result : ResolvedValue
  deriving DecidableEq

/-- A module retains function order; local identities are scoped to each function. -/
structure ResolvedModule where
  funcs : List ResolvedFunction
  deriving DecidableEq

/-- References must point to existing parameters or instructions. -/
def ValidResolvedValue (numParams numInsts : Nat) : ResolvedValue → Prop
  | .ref (.param i) => i < numParams
  | .ref (.inst i) => i < numInsts
  | .intConst _ => True

def ValidResolvedInst (numParams numInsts : Nat) : ResolvedAST → Prop
  | .bin _ _ lhs rhs =>
      ValidResolvedValue numParams numInsts lhs ∧ ValidResolvedValue numParams numInsts rhs

def ValidResolvedFunction (f : ResolvedFunction) : Prop :=
  (∀ inst ∈ f.insts, ValidResolvedInst f.header.params.length f.insts.length inst) ∧
  ValidResolvedValue f.header.params.length f.insts.length f.result

/-- Discard parameter names while retaining their types and positions. -/
def eraseParamNames (f : ResolvedFunction) : ResolvedFunction :=
  { f with header := { f.header with
      params := f.header.params.map fun p => { p with name := "" } } }

def EqModuloRenaming (f g : ResolvedFunction) : Prop :=
  eraseParamNames f = eraseParamNames g

/-- Reintroduce the canonical local names used by the resolved-function printer. -/
def unresolveValue : ResolvedValue → Value
  | .ref (.param i) => .localIdent s!"arg{i}"
  | .ref (.inst i) => .localIdent s!"{i}"
  | .intConst value => .intConst value

def unresolveInst : ResolvedAST → BinInst
  | .bin op ty lhs rhs => ⟨op, ty, unresolveValue lhs, unresolveValue rhs⟩

/-- Reconstruct a single-block AST with canonical names, since source instruction
names are discarded by resolution. Reference indices are preserved without validation. -/
def unresolveFunction (f : ResolvedFunction) : FuncDef :=
  let header := { f.header with
    params := f.header.params.zipIdx.map fun (p, i) => { p with name := s!"arg{i}" } }
  let insts : List Instruction := f.insts.zipIdx.map fun (inst, i) => ⟨s!"{i}", unresolveInst inst⟩
  ⟨header, [⟨f.label, insts, .ret ⟨header.retType, unresolveValue f.result⟩⟩]⟩

def formatType : LLType → String
  | .int width => s!"i{width}"

def formatValue : ResolvedValue → String
  | .ref (.param i) => s!"%arg{i}"
  | .ref (.inst i) => s!"%{i}"
  | .intConst value => toString value

def formatInst : ResolvedAST → String
  | .bin op ty lhs rhs =>
      let name := match op with | .xor => "xor" | .and => "and" | .or => "or"
      s!"{name} {formatType ty} {formatValue lhs}, {formatValue rhs}"

instance : ToString ResolvedFunction where
  toString f :=
    let params := f.header.params.zipIdx.map fun (p, i) => s!"{formatType p.ty} %arg{i}"
    let insts := f.insts.zipIdx.map fun (inst, i) => s!"  %{i} = {formatInst inst}\n"
    s!"define {formatType f.header.retType} @{f.header.name} ({String.intercalate ", " params})" ++ " {\n" ++
      s!"{f.label}:\n" ++ String.join insts ++
      s!"  ret {formatType f.header.retType} {formatValue f.result}\n" ++ "}"

instance : Repr ResolvedFunction where
  reprPrec f _ := .text (toString f)

/-- Resolution uses all definitions; dominance and typing are separate checks. -/
inductive ResolvesFunction : FuncDef → ResolvedFunction → Prop where
  | mk (env) :  HasEnv3 env header insts →
      ResolvesList (fun inst => ResolvesBinInst env inst.inst) insts resolved →
      ResolvesValue env result value →
      ResolvesFunction ⟨header, [⟨label, insts, .ret ⟨header.retType, result⟩⟩]⟩
        ⟨header, label, resolved, value⟩

/-- Resolve a local reference by lookup, preserving integer literals. -/
def resolveValue (env : NameEnv) : Value → Option ResolvedValue
  | .localIdent name => (env name).map .ref
  | .intConst value => some (.intConst value)

def resolveBinInst (env : NameEnv) (inst : BinInst) : Option ResolvedAST := do
  let lhs ← resolveValue env inst.lhs
  let rhs ← resolveValue env inst.rhs
  return .bin inst.op inst.ty lhs rhs

def resolveInsts (env : NameEnv) : List Instruction → Option (List ResolvedAST)
  | [] => some []
  | inst :: insts => do
      let resolved ← resolveBinInst env inst.inst
      let rest ← resolveInsts env insts
      return resolved :: rest

/-- Check every definition against the lookup table, rejecting conflicting names. -/
def validEnvironment (header : FuncHeader) (insts : List Instruction) : Prop :=
  (∀ pj ∈ header.params.zipIdx, environment header insts pj.1.name = some (.param pj.2)) ∧
  (∀ ij ∈ insts.zipIdx, environment header insts ij.1.name = some (.inst ij.2))

instance : DecidablePred (validEnvironment header) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _))

/-- Resolve the single-block fragment specified by `ResolvesFunction`.
All definitions are available to operands, including forward references. -/
def resolveFunction (f : FuncDef) : Option ResolvedFunction :=
  match f.blocks with
  | [⟨label, insts, .ret ⟨ty, result⟩⟩] =>
      if ty = f.header.retType ∧ validEnvironment f.header insts then do
        let resolved ← resolveInsts (environment f.header insts) insts
        let value ← resolveValue (environment f.header insts) result
        return ⟨f.header, label, resolved, value⟩
      else none
  | _ => none

theorem resolveValue_sound (env : NameEnv) (v : Value) (r : ResolvedValue) :
    resolveValue env v = some r → ResolvesValue env v r := by
  cases v <;> simp [resolveValue, Option.map_eq_some_iff] <;>
    grind [ResolvesValue]

theorem resolveBinInst_sound (env : NameEnv) (inst : BinInst) (r : ResolvedAST) :
    resolveBinInst env inst = some r → ResolvesBinInst env inst r := by
  cases inst
  simp [resolveBinInst, Option.bind_eq_some_iff]
  grind [resolveValue_sound, ResolvesBinInst]

theorem resolveInsts_sound (env : NameEnv) (insts : List Instruction) (rs : List ResolvedAST) :
    resolveInsts env insts = some rs → ResolvesList (fun i => ResolvesBinInst env i.inst) insts rs := by
  induction insts generalizing rs <;>
    simp [resolveInsts, Option.bind_eq_some_iff] <;> grind [resolveBinInst_sound, ResolvesList]

theorem resolveFunction_sound (f : FuncDef) (r : ResolvedFunction) :
    resolveFunction f = some r → ResolvesFunction f r := by
  rcases f with ⟨header, blocks⟩; unfold resolveFunction
  split <;> try (intro h; contradiction)
  rename_i label insts ty result heq
  change blocks = _ at heq; subst blocks
  split <;> simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq, false_implies]
  rename_i h; change ty = header.retType ∧ validEnvironment header insts at h
  rcases h with ⟨rfl, hp, hi⟩
  rintro ⟨rs, hs, value, hv, rfl⟩
  exact .mk _ (.mk hp hi (environment_mem _ _)) (resolveInsts_sound _ _ _ hs) (resolveValue_sound _ _ _ hv)

theorem resolveValue_complete (env : NameEnv) (v : Value) (r : ResolvedValue) :
    ResolvesValue env v r → resolveValue env v = some r := by
  intro h; cases h <;> simp [resolveValue, *]

theorem resolveBinInst_complete (env : NameEnv) (inst : BinInst) (r : ResolvedAST) :
    ResolvesBinInst env inst r → resolveBinInst env inst = some r := by
  rintro ⟨hl, hr⟩
  simp [resolveBinInst, resolveValue_complete _ _ _ hl, resolveValue_complete _ _ _ hr]

theorem resolveInsts_complete (env : NameEnv) (insts : List Instruction) (rs : List ResolvedAST) :
    ResolvesList (fun i => ResolvesBinInst env i.inst) insts rs → resolveInsts env insts = some rs := by
  intro h; induction h with
  | nil => rfl
  | cons hi _ ih => simp [resolveInsts, resolveBinInst_complete _ _ _ hi, ih]

theorem resolveFunction_complete (f : FuncDef) (r : ResolvedFunction) :
    ResolvesFunction f r → resolveFunction f = some r := by
  rintro ⟨env, he, hi, hv⟩
  obtain rfl := he.environment_eq
  rcases he with ⟨hp, hi', _⟩
  simp [resolveFunction, show validEnvironment _ _ from ⟨hp, hi'⟩,
    resolveInsts_complete _ _ _ hi, resolveValue_complete _ _ _ hv]

theorem resolveFunction_iff (f : FuncDef) (r : ResolvedFunction) :
    resolveFunction f = some r ↔ ResolvesFunction f r :=
  ⟨resolveFunction_sound f r, resolveFunction_complete f r⟩


/-- Resolve every function independently, failing if any function fails. -/
def resolveModule (m : Module) : Option ResolvedModule :=
  (m.funcs.mapM resolveFunction).map ResolvedModule.mk

def ResolvesModule (m : Module) (r : ResolvedModule) : Prop :=
  ResolvesList ResolvesFunction m.funcs r.funcs

theorem resolvesList_mapM_iff (f : α → Option β) (R : α → β → Prop)
    (h : ∀ a b, f a = some b ↔ R a b) (xs : List α) (ys : List β) :
    xs.mapM f = some ys ↔ ResolvesList R xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [ResolvesList.nil]; grind [ResolvesList]
  | cons x xs ih =>
    cases ys <;> simp [List.mapM_cons, Option.bind_eq_some_iff]
    all_goals grind [ResolvesList]

theorem resolveModule_iff (m : Module) (r : ResolvedModule) :
    resolveModule m = some r ↔ ResolvesModule m r := by
  cases r
  simpa [resolveModule, ResolvesModule, Option.map_eq_some_iff] using
    resolvesList_mapM_iff resolveFunction ResolvesFunction resolveFunction_iff m.funcs _

theorem resolveModule_sound (m : Module) (r : ResolvedModule) :
    resolveModule m = some r → ResolvesModule m r :=
  (resolveModule_iff m r).mp

theorem resolveModule_complete (m : Module) (r : ResolvedModule) :
    ResolvesModule m r → resolveModule m = some r :=
  (resolveModule_iff m r).mpr


theorem nat_toString_injective : Function.Injective (toString : Nat → String) := by
  intro i j h
  simpa [Nat.toString_eq_ofList_toDigits, Nat.ofDigitChars_ten_toDigits] using
    congrArg (fun s : String => Nat.ofDigitChars 10 s.toList 0) h

theorem paramName_ne_instName (i j : Nat) : s!"arg{i}" ≠ s!"{j}" := by
  intro h
  have hm : 'a' ∈ (toString j).toList := by
    rw [← h]; simp only [String.toList_append, List.mem_append]; exact .inl (by decide)
  rw [Nat.toString_eq_ofList_toDigits, String.toList_ofList] at hm
  have := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) hm
  contradiction

def valueIdName : ValueId → String
  | .param i => s!"arg{i}"
  | .inst i => s!"{i}"

theorem valueIdName_injective : Function.Injective valueIdName := by
  intro a b h
  cases a <;> cases b <;>
    simp_all only [valueIdName, String.append_right_inj, nat_toString_injective.eq_iff] <;>
    grind [paramName_ne_instName]

theorem unresolve_bindings (f : ResolvedFunction) :
    bindings (unresolveFunction f).header
      (f.insts.zipIdx.map fun (inst, i) => ⟨s!"{i}", unresolveInst inst⟩) =
    (List.range f.header.params.length).map (fun i => (valueIdName (.param i), .param i)) ++
    (List.range f.insts.length).map (fun i => (valueIdName (.inst i), .inst i)) := by
  unfold bindings
  congr 1 <;> apply List.ext_getElem <;> simp [unresolveFunction, valueIdName]

theorem lookup_valueIdName (ids : List ValueId) (id : ValueId) (h : id ∈ ids) :
    (ids.map fun id => (valueIdName id, id)).lookup (valueIdName id) = some id := by
  induction ids <;> simp_all [List.lookup_cons] <;>
    split <;> grind [valueIdName_injective]

theorem unresolve_lookup (f : ResolvedFunction) (id : ValueId)
    (h : ValidResolvedValue f.header.params.length f.insts.length (.ref id)) :
    environment (unresolveFunction f).header
      (f.insts.zipIdx.map fun (inst, i) => ⟨s!"{i}", unresolveInst inst⟩)
      (valueIdName id) = some id := by
  rw [environment, unresolve_bindings]
  have hm : id ∈ (List.range f.header.params.length).map ValueId.param ++
      (List.range f.insts.length).map ValueId.inst := by cases id <;> simp_all [ValidResolvedValue]
  simpa [List.map_append, List.map_map, Function.comp_def] using lookup_valueIdName _ id hm

theorem unresolve_param_name (f : ResolvedFunction)
    (h : pj ∈ (unresolveFunction f).header.params.zipIdx) :
    pj.1.name = valueIdName (.param pj.2) := by
  simpa [unresolveFunction, valueIdName] using congrArg Param.name (List.fst_eq_of_mem_zipIdx h)

theorem unresolve_inst_name (insts : List ResolvedAST)
    (h : ij ∈ (insts.zipIdx.map fun (inst, i) =>
      (⟨s!"{i}", unresolveInst inst⟩ : Instruction)).zipIdx) :
    ij.1.name = valueIdName (.inst ij.2) := by
  simpa [valueIdName] using congrArg Instruction.name (List.fst_eq_of_mem_zipIdx h)

theorem unresolve_validEnvironment (f : ResolvedFunction) :
    validEnvironment (unresolveFunction f).header
      (f.insts.zipIdx.map fun (inst, i) => ⟨s!"{i}", unresolveInst inst⟩) := by
  constructor
  · intro pj hp; rw [unresolve_param_name f hp]; apply unresolve_lookup
    simpa [unresolveFunction, ValidResolvedValue] using List.snd_lt_of_mem_zipIdx hp
  · intro ij hi; rw [unresolve_inst_name f.insts hi]; apply unresolve_lookup
    simpa [ValidResolvedValue] using List.snd_lt_of_mem_zipIdx hi

theorem unresolve_resolvesValue (f : ResolvedFunction) (v : ResolvedValue)
    (h : ValidResolvedValue f.header.params.length f.insts.length v) :
    ResolvesValue (environment (unresolveFunction f).header
      (f.insts.zipIdx.map fun (inst, i) => ⟨s!"{i}", unresolveInst inst⟩)) (unresolveValue v) v := by
  rcases v with (_ | _) | _ <;> first | exact .local (unresolve_lookup _ _ h) | exact .intConst

theorem unresolve_resolvesInst (f : ResolvedFunction) (inst : ResolvedAST)
    (h : ValidResolvedInst f.header.params.length f.insts.length inst) :
    ResolvesBinInst (environment (unresolveFunction f).header
      (f.insts.zipIdx.map fun (inst, i) => ⟨s!"{i}", unresolveInst inst⟩)) (unresolveInst inst) inst := by
  cases inst; exact .bin (unresolve_resolvesValue _ _ h.1) (unresolve_resolvesValue _ _ h.2)

theorem resolvesList_maps (xs : List α) (g : α → β) (k : α → γ)
    (h : ∀ x ∈ xs, R (g x) (k x)) : ResolvesList R (xs.map g) (xs.map k) := by
  induction xs <;> simp_all [List.mem_cons, ResolvesList.nil, ResolvesList.cons]

theorem unresolve_resolvesInsts (f : ResolvedFunction)
    (h : ∀ inst ∈ f.insts, ValidResolvedInst f.header.params.length f.insts.length inst) :
    ResolvesList (fun (i : Instruction) => ResolvesBinInst (environment (unresolveFunction f).header
      (f.insts.zipIdx.map fun (inst, i) => ⟨s!"{i}", unresolveInst inst⟩)) i.inst)
      (f.insts.zipIdx.map fun (inst, i) => ⟨s!"{i}", unresolveInst inst⟩) f.insts := by
  simpa only [List.zipIdx_map_fst] using resolvesList_maps f.insts.zipIdx
    (fun (inst, i) => (⟨s!"{i}", unresolveInst inst⟩ : Instruction)) Prod.fst
    (R := fun (i : Instruction) inst => ResolvesBinInst _ i.inst inst)
    (fun p hp => unresolve_resolvesInst f p.1 (h p.1 (List.fst_mem_of_mem_zipIdx hp)))

theorem resolve_round_trip (f : ResolvedFunction) :
    ValidResolvedFunction f →
      ∃ g, resolveFunction (unresolveFunction f) = some g ∧ EqModuloRenaming g f := by
  rintro ⟨hi, hv⟩
  refine ⟨⟨(unresolveFunction f).header, f.label, f.insts, f.result⟩, resolveFunction_complete _ _ ?_, ?_⟩
  · obtain ⟨hp, hj⟩ := unresolve_validEnvironment f
    exact .mk _ (.mk hp hj (environment_mem _ _))
      (unresolve_resolvesInsts f hi) (unresolve_resolvesValue f f.result hv)
  · simp [EqModuloRenaming, eraseParamNames, unresolveFunction, List.map_map]
    apply List.ext_getElem <;> simp

/-- The two bodies differ in their middle operation and its result name. -/
def deMorganFunction (name middle : String) (op : BinOp) : FuncDef :=
  ⟨⟨.int 32, name, [⟨.int 32, "p"⟩, ⟨.int 32, "q"⟩]⟩,
    [⟨"entry", [
      ⟨"not_p", ⟨.xor, .int 32, .localIdent "p", .intConst (-1)⟩⟩,
      ⟨"not_q", ⟨.xor, .int 32, .localIdent "q", .intConst (-1)⟩⟩,
      ⟨middle, ⟨op, .int 32, .localIdent "not_p", .localIdent "not_q"⟩⟩,
      ⟨"result", ⟨.xor, .int 32, .localIdent middle, .intConst (-1)⟩⟩],
      .ret ⟨.int 32, .localIdent "result"⟩⟩]⟩

def deMorganModule : Module :=
  ⟨[deMorganFunction "demorgan_or" "both_not" .and,
    deMorganFunction "demorgan_and" "either_not" .or]⟩

-- This AST covers the entire source string, including both functions.
example : parse deMorganExample = .ok deMorganModule := by native_decide

def deMorganNot (paramIndex : Nat) : ResolvedAST :=
  .bin .xor (.int 32) (.ref (.param paramIndex)) (.intConst (-1))

def deMorganCombined (op : BinOp) : ResolvedAST :=
  .bin op (.int 32) (.ref (.inst 0)) (.ref (.inst 1))

def deMorganResult : ResolvedAST :=
  .bin .xor (.int 32) (.ref (.inst 2)) (.intConst (-1))

def resolvedDeMorganFunction (name : String) (op : BinOp) : ResolvedFunction :=
  ⟨⟨.int 32, name, [⟨.int 32, "p"⟩, ⟨.int 32, "q"⟩]⟩, "entry",
    [deMorganNot 0, deMorganNot 1, deMorganCombined op, deMorganResult], .ref (.inst 3)⟩

def resolvedDeMorganModule : ResolvedModule :=
  ⟨[resolvedDeMorganFunction "demorgan_or" .and,
    resolvedDeMorganFunction "demorgan_and" .or]⟩

example : resolveModule deMorganModule = some resolvedDeMorganModule := by native_decide

example : ResolvesModule deMorganModule resolvedDeMorganModule :=
  resolveModule_sound _ _ (by native_decide)

example : resolveFunction (deMorganFunction "demorgan_or" "both_not" .and) =
    some (resolvedDeMorganFunction "demorgan_or" .and) := by native_decide

example : resolveFunction (deMorganFunction "demorgan_and" "either_not" .or) =
    some (resolvedDeMorganFunction "demorgan_and" .or) := by native_decide

#eval resolveFunction (deMorganFunction "demorgan_and" "either_not" .or)
-- A parameter and an instruction cannot share a name in a valid environment.
example : resolveFunction (deMorganFunction "collision" "p" .and) = none := by native_decide

-- Parameter references and all four named results resolve separately in each function.
theorem deMorgan_resolves (name middle : String) (op : BinOp)
    (hp : middle ≠ "p") (hq : middle ≠ "q")
    (hnp : middle ≠ "not_p") (hnq : middle ≠ "not_q") (hr : middle ≠ "result") :
    ResolvesFunction (deMorganFunction name middle op) (resolvedDeMorganFunction name op) := by
  apply resolveFunction_sound
  simp [resolveFunction, deMorganFunction, resolvedDeMorganFunction, validEnvironment,
    environment, bindings, List.lookup, resolveInsts, resolveBinInst, resolveValue,
    deMorganNot, deMorganCombined, deMorganResult, beq_false_of_ne hp,
    beq_false_of_ne hq, beq_false_of_ne hnp, beq_false_of_ne hnq, beq_false_of_ne (Ne.symm hr)]

/-- Both functions resolve, with repeated local names scoped to their own function. -/
example : ResolvesList ResolvesFunction deMorganModule.funcs
    [resolvedDeMorganFunction "demorgan_or" .and,
     resolvedDeMorganFunction "demorgan_and" .or] :=
  .cons (deMorgan_resolves _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (.cons (deMorgan_resolves _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)) .nil)

#eval resolvedDeMorganFunction "demorgan_or" .and

-- Two uses of %x retain the same result ID rather than duplicating its definition.
example : ResolvesBinInst (fun name => if name = "x" then some (.inst 0) else none)
    ⟨.and, .int 32, .localIdent "x", .localIdent "x"⟩
    (.bin .and (.int 32) (.ref (.inst 0)) (.ref (.inst 0))) :=
  .bin (.local rfl) (.local rfl)

end Veir.NameResolutionSketch
