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
  deriving Repr, DecidableEq

/-- Resolution uses all definitions; dominance and typing are separate checks. -/
inductive ResolvesFunction : FuncDef → ResolvedFunction → Prop where
  | mk : (bindings header insts).map Prod.fst |>.Nodup →
      ResolvesList (fun i => ResolvesBinInst (environment header insts) i.inst)
        insts resolved →
      ResolvesValue (environment header insts) result value →
      ResolvesFunction ⟨header, [⟨label, insts, .ret ⟨header.retType, result⟩⟩]⟩
        ⟨header, label, resolved, value⟩

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

-- Parameter references and all four named results resolve separately in each function.
theorem deMorgan_resolves (name middle : String) (op : BinOp)
    (hp : middle ≠ "p") (hq : middle ≠ "q")
    (hnp : middle ≠ "not_p") (hnq : middle ≠ "not_q") (hr : middle ≠ "result") :
    ResolvesFunction (deMorganFunction name middle op) (resolvedDeMorganFunction name op) := by
  apply ResolvesFunction.mk
  · simp [bindings, Ne.symm hp, Ne.symm hq, Ne.symm hnp, Ne.symm hnq, hr]
  · refine .cons (.bin (.local rfl) .intConst)
      (.cons (.bin (.local rfl) .intConst)
      (.cons (.bin (.local rfl) (.local rfl))
      (.cons (.bin (.local ?_) .intConst) .nil)))
    simp [environment, bindings, List.lookup, beq_false_of_ne hp, beq_false_of_ne hq,
      beq_false_of_ne hnp, beq_false_of_ne hnq]
  · exact .local (by simp [environment, bindings, List.lookup, beq_false_of_ne (Ne.symm hr)])

/-- Both functions resolve, with repeated local names scoped to their own function. -/
example : ResolvesList ResolvesFunction deMorganModule.funcs
    [resolvedDeMorganFunction "demorgan_or" .and,
     resolvedDeMorganFunction "demorgan_and" .or] :=
  .cons (deMorgan_resolves _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (.cons (deMorgan_resolves _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)) .nil)

-- Two uses of %x retain the same result ID rather than duplicating its definition.
example : ResolvesBinInst (fun name => if name = "x" then some (.inst 0) else none)
    ⟨.and, .int 32, .localIdent "x", .localIdent "x"⟩
    (.bin .and (.int 32) (.ref (.inst 0)) (.ref (.inst 0))) :=
  .bin (.local rfl) (.local rfl)

end Veir.NameResolutionSketch
