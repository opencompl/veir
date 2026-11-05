import Veir.Parser.LLVMAST

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
  fun name => (bindings header insts).lookup name

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
      HasEnv3 n header insts


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
  cases v <;> simp only [resolveValue, Option.map_eq_some_iff, Option.some.injEq]
  · rintro ⟨id, h, rfl⟩; exact .local h
  · rintro rfl; exact .intConst

theorem resolveBinInst_sound (env : NameEnv) (inst : BinInst) (r : ResolvedAST) :
    resolveBinInst env inst = some r → ResolvesBinInst env inst r := by
  cases inst
  simp only [resolveBinInst, bind, pure, Option.bind_eq_some_iff, Option.some.injEq]
  rintro ⟨lhs, hl, rhs, hr, rfl⟩
  exact .bin (resolveValue_sound _ _ _ hl) (resolveValue_sound _ _ _ hr)

theorem resolveInsts_sound (env : NameEnv) (insts : List Instruction) (rs : List ResolvedAST) :
    resolveInsts env insts = some rs → ResolvesList (fun i => ResolvesBinInst env i.inst) insts rs := by
  induction insts generalizing rs with
  | nil => simp only [resolveInsts, Option.some.injEq]; rintro rfl; exact .nil
  | cons inst insts ih =>
      simp only [resolveInsts, bind, pure, Option.bind_eq_some_iff, Option.some.injEq]
      rintro ⟨r, hr, rest, ht, rfl⟩
      exact .cons (resolveBinInst_sound _ _ _ hr) (ih _ ht)

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
  exact .mk _ (.mk hp hi) (resolveInsts_sound _ _ _ hs) (resolveValue_sound _ _ _ hv)

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

example : resolveFunction (deMorganFunction "demorgan_or" "both_not" .and) =
    some (resolvedDeMorganFunction "demorgan_or" .and) := by native_decide

example : resolveFunction (deMorganFunction "demorgan_and" "either_not" .or) =
    some (resolvedDeMorganFunction "demorgan_and" .or) := by native_decide

-- A parameter and an instruction cannot share a name in a valid environment.
example : resolveFunction (deMorganFunction "collision" "p" .and) = none := by native_decide

-- Parameter references and all four named results resolve separately in each function.
theorem deMorgan_resolves (name middle : String) (op : BinOp)
    (hp : middle ≠ "p") (hq : middle ≠ "q")
    (hnp : middle ≠ "not_p") (hnq : middle ≠ "not_q") (hr : middle ≠ "result") :
    ResolvesFunction (deMorganFunction name middle op) (resolvedDeMorganFunction name op) := by
  let f := deMorganFunction name middle op
  apply ResolvesFunction.mk (environment f.header (f.blocks[0]'(by simp [f, deMorganFunction])).insts)
  · constructor <;> simp [f, deMorganFunction, environment, bindings, List.lookup,
        beq_false_of_ne hp, beq_false_of_ne hq, beq_false_of_ne hnp,
        beq_false_of_ne hnq, beq_false_of_ne (Ne.symm hr)]
  · refine .cons (.bin (.local rfl) .intConst) (.cons (.bin (.local rfl) .intConst)
      (.cons (.bin (.local rfl) (.local rfl)) (.cons (.bin (.local ?_) .intConst) .nil)))
    simp [f, deMorganFunction, environment, bindings, List.lookup,
      beq_false_of_ne hp, beq_false_of_ne hq, beq_false_of_ne hnp, beq_false_of_ne hnq]
  · exact .local (by simp [f, deMorganFunction, environment, bindings, List.lookup, beq_false_of_ne (Ne.symm hr)])

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
