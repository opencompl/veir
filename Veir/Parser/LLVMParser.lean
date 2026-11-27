import Veir.Parser.LoweringIso

/-! The text-to-VeIR pipeline for the LLVM integer fragment with control flow. -/

namespace Veir.LLVMParser

open LLVMParserProp
open LLVMLowering NameResolutionSketch

/-- Lex and parse LLVM IR, resolve local names, and lower to a VeIR module. -/
def parseAndLower (src : String) : Except LoweringError (WfIRContext OpCode × OperationPtr) := do
  let m ← (parse src).mapError (fun err => s!"parse: {reprStr err}")
  let some resolved := resolveModule m | .error "resolveModule failed"
  lowerModule resolved

/-- A source spells an AST whose resolved form describes the rooted VeIR module. -/
def ParsesModule (src : String) (ctx : WfIRContext OpCode) (root : OperationPtr) : Prop :=
  ∃ m r, ParsesTo src.toList m ∧ ResolvesModule m r ∧ LowersModule ctx r root

/-- The importer realizes the lexing, parsing, and resolution relations followed by lowering. -/
theorem parseAndLower_eq_ok_iff :
    parseAndLower src = .ok (ctx, root) ↔
      ∃ m r, ParsesTo src.toList m ∧ ResolvesModule m r ∧ lowerModule r = .ok (ctx, root) := by
  simp only [parseAndLower, Except.bind_eq_ok, ← parse_correct, ← resolveModule_iff]
  constructor
  · rintro ⟨m, hp, hl⟩
    cases hr : resolveModule m with
    | none => simp [hr] at hl
    | some r => exact ⟨m, r, Except.eq_ok_of_mapError_eq_ok hp, hr, by simpa [hr] using hl⟩
  · rintro ⟨m, r, hp, hr, hl⟩
    exact ⟨m, by simp [hp, Except.mapError], by simpa [hr] using hl⟩

/-- Lift a correctness theorem for control-flow lowering to the text importer. -/
theorem parseAndLower_correct_of_lowerModule_correct
    (lowerCorrect : ∀ r ctx root, LowersModule ctx r root ↔
      ∃ ctx' root', lowerModule r = .ok (ctx', root') ∧
        RootedIso ctx root ctx' root') :
    ParsesModule src ctx root ↔
    ∃ ctx' root', parseAndLower src = .ok (ctx', root') ∧
      RootedIso ctx root ctx' root' := by
  constructor
  · rintro ⟨m, r, hp, hr, hl⟩
    obtain ⟨ctx', root', he, hi⟩ := (lowerCorrect _ _ _).mp hl
    exact ⟨ctx', root', parseAndLower_eq_ok_iff.mpr ⟨m, r, hp, hr, he⟩, hi⟩
  · rintro ⟨ctx', root', he, hi⟩
    obtain ⟨m, r, hp, hr, hl⟩ := parseAndLower_eq_ok_iff.mp he
    exact ⟨m, r, hp, hr, (lowerCorrect _ _ _).mpr ⟨ctx', root', hl, hi⟩⟩


theorem parseAndLower_correct :
    ParsesModule src ctx root ↔
    ∃ ctx' root', parseAndLower src = .ok (ctx', root') ∧
      RootedIso ctx root ctx' root' :=
  parseAndLower_correct_of_lowerModule_correct fun _ _ _ => LLVMLowering.lowerModule_correct



def printLLVM (ctx : WfIRContext OpCode) (root : OperationPtr) :
    Except LoweringError String :=
  (reverseModule ctx root).map fun m => (unresolveModule m).print

def FunctionLayout (ctx : WfIRContext OpCode) (op : OperationPtr) : Prop :=
  ∃ (name : String) (ret : TypeAttr) (region : RegionPtr),
    bareName name ∧
    MatchesOp ctx op Llvm.func #[] #[] #[region]
      (LLVMFuncProperties.mk ⟨name.toUTF8⟩
        { inputs := #[] ,
          outputs := #[ret.val] } defaultFuncExtra)

def Module.isValid (ctx : WfIRContext OpCode) (root : OperationPtr) : Prop :=
  ∃ (region : RegionPtr) (body : BlockPtr) (funcs : List OperationPtr),
    MatchesOp ctx root Builtin.module #[] #[] #[region] default defaultModuleAttrs ∧
    region.BlockChain ctx.raw #[body] ∧
    body.OpChain ctx.raw funcs.toArray ∧
    body.getArgumentTypes! ctx.raw = #[] ∧
    ∀ op ∈ funcs, FunctionLayout ctx op

theorem parseAndLower_printLLVM_round_trip
    (ctx : WfIRContext OpCode) (root : OperationPtr)  : Module.isValid  ctx root →
    ∃ (ctx' : WfIRContext OpCode) (root' : OperationPtr),
      ((printLLVM ctx root) >>= parseAndLower = .ok (ctx', root')) ∧
      RootedIso ctx root ctx' root' := sorry


end Veir.LLVMParser
