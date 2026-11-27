import Veir.Parser.LLVMLowering

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
      RootedIso ctx root ctx' root' := by
  sorry

end Veir.LLVMParser
