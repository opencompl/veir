module
public meta import Veir.OpCode
import all Veir.OpCode
import all Veir.GlobalOpInfo
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.Builtin.OpInfo

import all Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RISCV64CTreeSemantics
import all Veir.PatternRewriter.Puddle.CTreeValidity
import all Veir.PatternRewriter.Puddle.Builders
import all Veir.PatternRewriter.Puddle.Definitions
import all Veir.PatternRewriter.Puddle.Validity
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Dialects.LLVM.OpInfo
import all Veir.IR.Attribute
import all Init.Data.Array.Basic
import Veir.Passes.InstructionSelection.Proofs
import all Veir.Data.Casting
import all Veir.Data.Refinement
import all Veir.Data.LLVM.Int.Basic
public meta import Veir.PatternRewriter.Puddle.Definitions
public meta import Veir.PatternRewriter.Puddle.Validity

open Veir Veir.Puddle Veir.Puddle.CTree

namespace Veir.InstructionSelection.CTreeProofs
section

@[simp]
private theorem CanInterpretTo.ctlz_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__ctlz)) (x : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__ctlz) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.ctlz x property.is_zero_poison)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

@[simp]
private theorem CanInterpretTo.cttz_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__cttz)) (x : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__cttz) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.cttz x property.is_zero_poison)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

@[simp]
private theorem CanInterpretTo.ctpop_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__ctpop)) (x : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__ctpop) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.ctpop x)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

private theorem ctlz64_valid : Veir.Puddle.CTree.Pattern.Valid ctlz64_pattern := by
  conv => arg 1; cbv
  constructor
  · simp [Pattern.Supported, CreateProg.Supported, MatchProg.Supported,
      MatchDecl.Supported, CreateDecl.Supported, SupportedOpCode,
      get_effects, is_terminator]
  · cbv
  · decide
  simpPuddleSemantics
  rintro _ ty rfl hty value hvalue property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hvalue
    obtain ⟨x, rfl⟩ := hvalue
    cases x <;> simp [CanInterpretTo.ctlz_int (⟨64, hint⟩)]
    · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, LLVM.Int.toReg] using
        (Data.RISCV.ctlz_refinement (x := .val _) (is_zero_poison := property.is_zero_poison))
    · intro bits
      simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.ctlz, isRefinedBy, Id.run]

private theorem ctlz32_valid : Veir.Puddle.CTree.Pattern.Valid ctlz32_pattern := by
  conv => arg 1; cbv
  constructor
  · simp [Pattern.Supported, CreateProg.Supported, MatchProg.Supported,
      MatchDecl.Supported, CreateDecl.Supported, SupportedOpCode,
      get_effects, is_terminator]
  · cbv
  · decide
  simpPuddleSemantics
  rintro _ ty rfl hty value hvalue property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hvalue
    obtain ⟨x, rfl⟩ := hvalue
    cases x <;> simp [CanInterpretTo.ctlz_int (⟨32, hint⟩)]
    · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, LLVM.Int.toReg] using
        (Data.RISCV.ctlz_refinement_32 (x := .val _) (is_zero_poison := property.is_zero_poison))
    · intro bits
      simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.ctlz, isRefinedBy, Id.run]
private theorem cttz64_valid : Veir.Puddle.CTree.Pattern.Valid cttz64_pattern := by
  conv => arg 1; cbv
  constructor
  · simp [Pattern.Supported, CreateProg.Supported, MatchProg.Supported,
      MatchDecl.Supported, CreateDecl.Supported, SupportedOpCode,
      get_effects, is_terminator]
  · cbv
  · decide
  simpPuddleSemantics
  rintro _ ty rfl hty value hvalue property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hvalue
    obtain ⟨x, rfl⟩ := hvalue
    cases x <;> simp [CanInterpretTo.cttz_int (⟨64, hint⟩)]
    · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, LLVM.Int.toReg] using
        (Data.RISCV.cttz_refinement (x := .val _) (is_zero_poison := property.is_zero_poison))
    · intro bits
      simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.cttz, isRefinedBy, Id.run]
private theorem cttz32_valid : Veir.Puddle.CTree.Pattern.Valid cttz32_pattern := by
  conv => arg 1; cbv
  constructor
  · simp [Pattern.Supported, CreateProg.Supported, MatchProg.Supported,
      MatchDecl.Supported, CreateDecl.Supported, SupportedOpCode,
      get_effects, is_terminator]
  · cbv
  · decide
  simpPuddleSemantics
  rintro _ ty rfl hty value hvalue property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hvalue
    obtain ⟨x, rfl⟩ := hvalue
    cases x <;> simp [CanInterpretTo.cttz_int (⟨32, hint⟩)]
    · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, LLVM.Int.toReg] using
        (Data.RISCV.cttz_refinement_32 (x := .val _) (is_zero_poison := property.is_zero_poison))
    · intro bits
      simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.cttz, isRefinedBy, Id.run]
private theorem ctpop64_valid : Veir.Puddle.CTree.Pattern.Valid ctpop64_pattern := by
  conv => arg 1; cbv
  constructor
  · simp [Pattern.Supported, CreateProg.Supported, MatchProg.Supported,
      MatchDecl.Supported, CreateDecl.Supported, SupportedOpCode,
      get_effects, is_terminator]
  · cbv
  · decide
  simpPuddleSemantics
  rintro _ ty rfl hty value hvalue property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hvalue
    obtain ⟨x, rfl⟩ := hvalue
    cases x <;> simp [CanInterpretTo.ctpop_int (⟨64, hint⟩)]
    · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, LLVM.Int.toReg] using
        (Data.RISCV.ctpop_refinement (x := .val _))
    · intro bits
      simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.ctpop, isRefinedBy, Id.run]
private theorem ctpop32_valid : Veir.Puddle.CTree.Pattern.Valid ctpop32_pattern := by
  conv => arg 1; cbv
  constructor
  · simp [Pattern.Supported, CreateProg.Supported, MatchProg.Supported,
      MatchDecl.Supported, CreateDecl.Supported, SupportedOpCode,
      get_effects, is_terminator]
  · cbv
  · decide
  simpPuddleSemantics
  rintro _ ty rfl hty value hvalue property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hvalue
    obtain ⟨x, rfl⟩ := hvalue
    cases x <;> simp [CanInterpretTo.ctpop_int (⟨32, hint⟩)]
    · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, LLVM.Int.toReg] using
        (Data.RISCV.ctpop_refinement_32 (x := .val _))
    · intro bits
      simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.ctpop, isRefinedBy, Id.run]

end
end Veir.InstructionSelection.CTreeProofs
