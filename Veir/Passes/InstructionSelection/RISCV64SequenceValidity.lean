module
import Veir.PatternRewriter.Puddle.CTreeSymbolicValidity
public meta import Veir.OpCode
public meta import Veir.PatternRewriter.Puddle.Definitions
public meta import Veir.PatternRewriter.Puddle.Validity
import all Init.Data.Array.Basic
import all Veir.PatternRewriter.Puddle.Builders
import all Veir.PatternRewriter.Puddle.Definitions
import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.Passes.InstructionSelection.RISCV64ProofPatterns
import all Veir.PatternRewriter.Puddle.CTreeValidity
import Veir.Passes.InstructionSelection.Proofs
import all Veir.Dialects.RISCV.OpInfo
import all Veir.GlobalOpInfo
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.Builtin.OpInfo
import all Veir.Dialects.RISCV.Properties
import all Veir.Interpreter.Basic
import all Veir.Interpreter.CTree
import Veir.Passes.InstructionSelection.RISCV64CTreeSemantics
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.RISCV.Reg.Basic
import all Veir.Data.Casting
import all Veir.Data.Refinement
import all Veir.PatternRewriter.Puddle.Validity

namespace Veir
attribute [local simp] Llvm.getEffects Llvm.isTerminator
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
open Puddle Puddle.CTree

@[simp]
theorem CanInterpretTo.abs_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__abs)) (x : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__abs) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.abs x property.is_int_min_poison)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp']
  cases results <;> simp [monadLift, MonadLift.monadLift]

@[simp]
theorem CanInterpretTo.neg_reg (ty : RegisterType) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .neg) () #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.neg x)] := by
  exact CanInterpretTo.riscv_pure .neg () #[TypeAttr.of RegisterType ty] #[.reg x] _ (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.max_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .max) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.max y x)] := by
  exact CanInterpretTo.riscv_pure .max () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.saddSat_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__sadd__sat)) (x y : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__sadd__sat) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.saddSat x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp']
  cases results <;> simp [monadLift, MonadLift.monadLift]

@[simp]
theorem CanInterpretTo.ssubSat_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__ssub__sat)) (x y : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__ssub__sat) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.ssubSat x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp']
  cases results <;> simp [monadLift, MonadLift.monadLift]

@[simp]
theorem CanInterpretTo.uaddSat_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__uadd__sat)) (x y : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__uadd__sat) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.uaddSat x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp']
  cases results <;> simp [monadLift, MonadLift.monadLift]

@[simp]
theorem CanInterpretTo.usubSat_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__usub__sat)) (x y : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__usub__sat) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.usubSat x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp']
  cases results <;> simp [monadLift, MonadLift.monadLift]

@[simp]
theorem CanInterpretTo.sshlSat_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__sshl__sat)) (x y : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__sshl__sat) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.sshlSat x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp']
  cases results <;> simp [monadLift, MonadLift.monadLift]

@[simp]
theorem CanInterpretTo.ushlSat_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__ushl__sat)) (x y : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__ushl__sat) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.ushlSat x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp']
  cases results <;> simp [monadLift, MonadLift.monadLift]

@[simp]
theorem CanInterpretTo.rev8_reg (ty : RegisterType) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .rev8) () #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.rev8 x)] := by
  exact CanInterpretTo.riscv_pure .rev8 () #[TypeAttr.of RegisterType ty] #[.reg x] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.maxu_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .maxu) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.maxu y x)] := by
  exact CanInterpretTo.riscv_pure .maxu () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.minu_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .minu) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.minu y x)] := by
  exact CanInterpretTo.riscv_pure .minu () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.add_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .add) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.add y x)] := by
  exact CanInterpretTo.riscv_pure .add () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.sub_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .sub) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.sub y x)] := by
  exact CanInterpretTo.riscv_pure .sub () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.sll_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .sll) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.sll y x)] := by
  exact CanInterpretTo.riscv_pure .sll () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.srl_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .srl) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.srl y x)] := by
  exact CanInterpretTo.riscv_pure .srl () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.sra_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .sra) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.sra y x)] := by
  exact CanInterpretTo.riscv_pure .sra () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.xor_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .xor) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.xor y x)] := by
  exact CanInterpretTo.riscv_pure .xor () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.or_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .or) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.or y x)] := by
  exact CanInterpretTo.riscv_pure .or () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.and_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .and) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.and y x)] := by
  exact CanInterpretTo.riscv_pure .and () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.slt_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .slt) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.slt y x)] := by
  exact CanInterpretTo.riscv_pure .slt () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.czeroeqz_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .czeroeqz) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.czeroeqz y x)] := by
  exact CanInterpretTo.riscv_pure .czeroeqz () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.czeronez_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .czeronez) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.czeronez y x)] := by
  exact CanInterpretTo.riscv_pure .czeronez () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.li_reg (ty : RegisterType) (props : RISCVImmediateProperties)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .li) props #[TypeAttr.of RegisterType ty] #[] results ↔
      results = .ok #[.reg (Data.RISCV.li props.value)] := by
  exact CanInterpretTo.riscv_pure .li props #[TypeAttr.of RegisterType ty] #[] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.xori_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .xori) props #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.xori (props.immField 12) x)] := by
  exact CanInterpretTo.riscv_pure .xori props #[TypeAttr.of RegisterType ty] #[.reg x] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.slli_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .slli) props #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.slli (props.immField 6) x)] := by
  exact CanInterpretTo.riscv_pure .slli props #[TypeAttr.of RegisterType ty] #[.reg x] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.srli_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .srli) props #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.srli (props.immField 6) x)] := by
  exact CanInterpretTo.riscv_pure .srli props #[TypeAttr.of RegisterType ty] #[.reg x] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.srai_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .srai) props #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.srai (props.immField 6) x)] := by
  exact CanInterpretTo.riscv_pure .srai props #[TypeAttr.of RegisterType ty] #[.reg x] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.sltiu_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .sltiu) props #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.sltiu (props.immField 12) x)] := by
  exact CanInterpretTo.riscv_pure .sltiu props #[TypeAttr.of RegisterType ty] #[.reg x] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.addi_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .addi) props #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.addi (props.immField 12) x)] := by
  exact CanInterpretTo.riscv_pure .addi props #[TypeAttr.of RegisterType ty] #[.reg x] _
    (by intro memory; rfl) results

@[simp]
theorem CanInterpretTo.bswap_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__bswap)) (x : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__bswap) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.bswap x)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp']
  cases results <;> simp [monadLift, MonadLift.monadLift]

@[simp]
theorem CanInterpretTo.bitreverse_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__bitreverse)) (x : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__bitreverse) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.bitreverse x)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp']
  cases results <;> simp [monadLift, MonadLift.monadLift]

attribute [local simp] monadLift MonadLift.monadLift interpretOpCTree Llvm.interpretOpCTree Llvm.interpretOp'
  Tree.refines_pure OperationResult.isRefinedBy ControlFlowAction.optionIsRefinedBy_refl
  RuntimeValue.arrayIsRefinedBy_cons

 theorem abs_pattern_valid : Puddle.CTree.Pattern.Valid Veir.InstructionSelection.ProofPatterns.abs_pattern := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty value hvalue property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hvalue
      obtain ⟨x, rfl⟩ := hvalue
      simpRiscvTrees
      cases x <;> simp [interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp',
        monadLift, MonadLift.monadLift, Tree.refines_pure,
        OperationResult.isRefinedBy, ControlFlowAction.optionIsRefinedBy_refl,
        RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.isRefinedBy]
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField] using
          (Data.RISCV.abs_refinement (x := .val _) (is_int_min_poison := property.is_int_min_poison))
      · intro bits
        simp [
          RuntimeValue.isRefinedBy, Data.LLVM.Int.abs, isRefinedBy, Id.run]

private theorem usubSat_pattern_valid : Puddle.CTree.Pattern.Valid Veir.InstructionSelection.ProofPatterns.usubSat_pattern := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty lhs hleft rhs hright property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hleft hright
      obtain ⟨x, rfl⟩ := hleft
      obtain ⟨y, rfl⟩ := hright
      simpRiscvTrees
      cases x <;> cases y <;> simp [CanInterpretTo.usubSat_int (⟨64, hint⟩)]
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField] using
          (Data.RISCV.usubSat_refinement (x := .val _) (y := .val _))
      all_goals first
        | rintro outcome firstBits secondBits thirdBits rfl
        | rintro outcome firstBits secondBits rfl
        | intro bits
        | skip
      all_goals simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.usubSat, isRefinedBy, Id.run]

private theorem uaddSat_pattern_valid : Puddle.CTree.Pattern.Valid Veir.InstructionSelection.ProofPatterns.uaddSat_pattern := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty lhs hleft rhs hright property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hleft hright
      obtain ⟨x, rfl⟩ := hleft
      obtain ⟨y, rfl⟩ := hright
      simpRiscvTrees
      cases x <;> cases y <;> simp [CanInterpretTo.uaddSat_int (⟨64, hint⟩)]
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField] using
          (Data.RISCV.uaddSat_refinement (x := .val _) (y := .val _))
      all_goals first
        | rintro outcome firstBits secondBits thirdBits rfl
        | rintro outcome firstBits secondBits rfl
        | intro bits
        | skip
      all_goals simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.uaddSat, isRefinedBy, Id.run]

private theorem saddSat_pattern_valid : Puddle.CTree.Pattern.Valid Veir.InstructionSelection.ProofPatterns.saddSat_pattern := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty lhs hleft rhs hright property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hleft hright
      obtain ⟨x, rfl⟩ := hleft
      obtain ⟨y, rfl⟩ := hright
      simpRiscvTrees
      cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CanInterpretTo.saddSat_int (⟨64, hint⟩)]
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField] using
          (Data.RISCV.saddSat_refinement (x := .val _) (y := .val _))
      all_goals first
        | rintro outcome firstBits secondBits thirdBits rfl
        | rintro outcome firstBits secondBits rfl
        | intro bits
        | skip
      all_goals simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.saddSat, isRefinedBy, Id.run]

private theorem ssubSat_pattern_valid : Puddle.CTree.Pattern.Valid Veir.InstructionSelection.ProofPatterns.ssubSat_pattern := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty lhs hleft rhs hright property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hleft hright
      obtain ⟨x, rfl⟩ := hleft
      obtain ⟨y, rfl⟩ := hright
      simpRiscvTrees
      cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CanInterpretTo.ssubSat_int (⟨64, hint⟩)]
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField] using
          (Data.RISCV.ssubSat_refinement (x := .val _) (y := .val _))
      all_goals first
        | rintro outcome firstBits secondBits thirdBits rfl
        | rintro outcome firstBits secondBits rfl
        | intro bits
        | skip
      all_goals simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.ssubSat, isRefinedBy, Id.run]

private theorem sshlSat_pattern_valid : Puddle.CTree.Pattern.Valid Veir.InstructionSelection.ProofPatterns.sshlSat_pattern := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty lhs hleft rhs hright property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hleft hright
      obtain ⟨x, rfl⟩ := hleft
      obtain ⟨y, rfl⟩ := hright
      simpRiscvTrees
      cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CanInterpretTo.sshlSat_int (⟨64, hint⟩)]
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField] using
          (Data.RISCV.sshlSat_refinement (x := .val _) (y := .val _))
      all_goals first
        | rintro outcome firstBits secondBits thirdBits rfl
        | rintro outcome firstBits secondBits rfl
        | intro bits
        | skip
      all_goals simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.sshlSat, isRefinedBy, Id.run]

private theorem ushlSat_pattern_valid : Puddle.CTree.Pattern.Valid Veir.InstructionSelection.ProofPatterns.ushlSat_pattern := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty lhs hleft rhs hright property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hleft hright
      obtain ⟨x, rfl⟩ := hleft
      obtain ⟨y, rfl⟩ := hright
      simpRiscvTrees
      cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CanInterpretTo.ushlSat_int (⟨64, hint⟩)]
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField] using
          (Data.RISCV.ushlSat_refinement (x := .val _) (y := .val _))
      all_goals first
        | rintro outcome firstBits secondBits thirdBits rfl
        | rintro outcome firstBits secondBits rfl
        | intro bits
        | skip
      all_goals simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.ushlSat, isRefinedBy, Id.run]

 theorem bswap64_pattern_valid : Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.bswap_pattern 64) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty value hvalue property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hvalue
      obtain ⟨x, rfl⟩ := hvalue
      simpRiscvTrees
      cases x <;> simp [
        CanInterpretTo.bswap_int (⟨64, hint⟩)]
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField] using
          (Data.RISCV.bswap_refinement (x := .val _))
      · intro bits
        simp [
          RuntimeValue.isRefinedBy, Data.LLVM.Int.bswap, isRefinedBy, Id.run]


 theorem bswap32_pattern_valid : Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.bswap_pattern 32) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty value hvalue property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hvalue
      obtain ⟨x, rfl⟩ := hvalue
      simpRiscvTrees
      cases x <;> simp [
        CanInterpretTo.bswap_int (⟨32, hint⟩)]
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField] using
          (Data.RISCV.bswap_refinement_32 (x := .val _))
      · intro bits
        simp [
          RuntimeValue.isRefinedBy, Data.LLVM.Int.bswap, isRefinedBy, Id.run]


@[simp] theorem CanInterpretTo.fshl_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__fshl)) (x y z : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__fshl) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y, .int ty.bitwidth z] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.fshl x y z)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp']
  cases results <;> simp [monadLift, MonadLift.monadLift]

@[simp] theorem CanInterpretTo.fshr_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__fshr)) (x y z : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__fshr) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y, .int ty.bitwidth z] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.fshr x y z)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp']
  cases results <;> simp [monadLift, MonadLift.monadLift]

@[simp] theorem CanInterpretTo.sllw_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .sllw) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.sllw y x)] :=
  CanInterpretTo.riscv_pure .sllw () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results


@[simp] theorem CanInterpretTo.srlw_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .srlw) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.srlw y x)] :=
  CanInterpretTo.riscv_pure .srlw () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results


@[simp] theorem CanInterpretTo.slliw_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .slliw) props #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.slliw (props.immField 5) x)] :=
  CanInterpretTo.riscv_pure .slliw props #[TypeAttr.of RegisterType ty] #[.reg x] _
    (by intro memory; rfl) results


@[simp] theorem CanInterpretTo.srliw_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .srliw) props #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.srliw (props.immField 5) x)] :=
  CanInterpretTo.riscv_pure .srliw props #[TypeAttr.of RegisterType ty] #[.reg x] _
    (by intro memory; rfl) results


@[simp] theorem CanInterpretTo.select_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .select)) (c : Data.LLVM.Int 1) (x y : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .select) property #[TypeAttr.of IntegerType ty]
      #[.int 1 c, .int ty.bitwidth x, .int ty.bitwidth y] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.select c x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, Llvm.interpretOp']
  cases results <;> simp [monadLift, MonadLift.monadLift]

private theorem reg_and_comm (x y : Data.RISCV.Reg) : Data.RISCV.and x y = Data.RISCV.and y x := by
  simp [Data.RISCV.and, BitVec.and_comm]

private theorem reg_or_comm (x y : Data.RISCV.Reg) : Data.RISCV.or x y = Data.RISCV.or y x := by
  simp [Data.RISCV.or, BitVec.or_comm]

set_option maxHeartbeats 5000000 in
 theorem bitreverse64_pattern_valid : Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.bitreverse_pattern 64) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty value hvalue property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hvalue
      obtain ⟨x, rfl⟩ := hvalue
      simpRiscvTrees
      cases x <;> simp
      all_goals try simp [CanInterpretTo.bitreverse_int (⟨64, hint⟩)]
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField, reg_and_comm, reg_or_comm] using
          (Data.RISCV.bitreverse_refinement (x := .val _))
      · intro bits
        simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.bitreverse, isRefinedBy, Id.run]



set_option maxHeartbeats 5000000 in
 theorem bitreverse32_pattern_valid : Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.bitreverse_pattern 32) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty value hvalue property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hvalue
      obtain ⟨x, rfl⟩ := hvalue
      simpRiscvTrees
      cases x <;> simp
      all_goals try simp [CanInterpretTo.bitreverse_int (⟨32, hint⟩)]
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField, reg_and_comm, reg_or_comm] using
          (Data.RISCV.bitreverse_refinement_32 (x := .val _))
      · intro bits
        simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.bitreverse, isRefinedBy, Id.run]



set_option maxHeartbeats 5000000 in
 theorem fshl64General_pattern_valid : Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.lowerFunnelShift true 64) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty lhs hleft rhs hright amt hamt property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hleft hright hamt
      obtain ⟨x, rfl⟩ := hleft
      obtain ⟨y, rfl⟩ := hright
      obtain ⟨z, rfl⟩ := hamt
      simpRiscvTrees
      cases x <;> cases y <;> cases z <;> simp
      all_goals try simp [CanInterpretTo.fshl_int (⟨64, hint⟩)]
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField, reg_or_comm] using
          (Data.RISCV.fshlGeneral_refinement (a := .val _) (b := .val _) (c := .val _))
      all_goals first
        | rintro outcome firstBits secondBits thirdBits rfl
        | rintro outcome firstBits secondBits rfl
        | intro bits
        | skip
      all_goals simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.fshl, isRefinedBy, Id.run]

set_option maxHeartbeats 5000000 in
 theorem fshl32General_pattern_valid : Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.lowerFunnelShift true 32) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty lhs hleft rhs hright amt hamt property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hleft hright hamt
      obtain ⟨x, rfl⟩ := hleft
      obtain ⟨y, rfl⟩ := hright
      obtain ⟨z, rfl⟩ := hamt
      simpRiscvTrees
      cases x <;> cases y <;> cases z <;> simp
      all_goals try simp [CanInterpretTo.fshl_int (⟨32, hint⟩)]
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField, reg_or_comm] using
          (Data.RISCV.fshlGeneralw_refinement (a := .val _) (b := .val _) (c := .val _))
      all_goals first
        | rintro outcome firstBits secondBits thirdBits rfl
        | rintro outcome firstBits secondBits rfl
        | intro bits
        | skip
      all_goals simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.fshl, isRefinedBy, Id.run]

set_option maxHeartbeats 5000000 in
 theorem fshr64General_pattern_valid : Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.lowerFunnelShift false 64) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty lhs hleft rhs hright amt hamt property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hleft hright hamt
      obtain ⟨x, rfl⟩ := hleft
      obtain ⟨y, rfl⟩ := hright
      obtain ⟨z, rfl⟩ := hamt
      simpRiscvTrees
      cases x <;> cases y <;> cases z <;> simp
      all_goals try simp [CanInterpretTo.fshr_int (⟨64, hint⟩)]
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField, reg_or_comm] using
          (Data.RISCV.fshrGeneral_refinement (a := .val _) (b := .val _) (c := .val _))
      all_goals first
        | rintro outcome firstBits secondBits thirdBits rfl
        | rintro outcome firstBits secondBits rfl
        | intro bits
        | skip
      all_goals simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.fshr, isRefinedBy, Id.run]

set_option maxHeartbeats 5000000 in
 theorem fshr32General_pattern_valid : Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.lowerFunnelShift false 32) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty lhs hleft rhs hright amt hamt property
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      simp only [RuntimeValue.Conforms.integerType] at hleft hright hamt
      obtain ⟨x, rfl⟩ := hleft
      obtain ⟨y, rfl⟩ := hright
      obtain ⟨z, rfl⟩ := hamt
      simpRiscvTrees
      cases x <;> cases y <;> cases z <;> simp
      all_goals try simp [CanInterpretTo.fshr_int (⟨32, hint⟩)]
      · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField, reg_or_comm] using
          (Data.RISCV.fshrGeneralw_refinement (a := .val _) (b := .val _) (c := .val _))
      all_goals first
        | rintro outcome firstBits secondBits thirdBits rfl
        | rintro outcome firstBits secondBits rfl
        | intro bits
        | skip
      all_goals simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.fshr, isRefinedBy, Id.run]

set_option maxHeartbeats 5000000 in
 theorem selectGeneral_pattern_valid : Puddle.CTree.Pattern.Valid (Veir.InstructionSelection.ProofPatterns.select_pattern false false) := by
  conv => arg 1; cbv
  provePuddleValid program sym =>
    rintro _ ty rfl hty _ cty rfl hcty cond hcond lhs hleft rhs hright property
    cases cty with
    | mk cbw chint =>
      dsimp [IntegerType.bitwidth] at hcty
      subst cbw
      simp only [RuntimeValue.Conforms.integerType] at hcond hleft hright
      obtain ⟨c, rfl⟩ := hcond
      obtain ⟨t, rfl⟩ := hleft
      obtain ⟨f, rfl⟩ := hright
      cases ty with
      | mk bw hint =>
        dsimp [IntegerType.bitwidth] at hty
        rcases hty with hty | hty | hty <;> subst bw
        all_goals
          simpRiscvTrees
          cases c with
          | val cbits =>
            rcases BitVec.eq_zero_or_eq_one cbits with rfl | rfl
            <;> cases t <;> cases f <;> simp
            all_goals first
              | rintro outcome firstBits secondBits thirdBits rfl
              | rintro outcome firstBits secondBits rfl
              | intro bits
              | skip
            all_goals try simp [CanInterpretTo.select_int (⟨64, hint⟩),
              CanInterpretTo.select_int (⟨32, hint⟩), CanInterpretTo.select_int (⟨1, hint⟩), Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
              RuntimeValue.isRefinedBy, Data.LLVM.Int.select, isRefinedBy, Id.run,
              Data.RISCV.czeroeqz, Data.RISCV.czeronez, Data.RISCV.or, RISCV.Reg.toInt]
          | poison =>
            cases t <;> cases f <;> simp
            all_goals first
              | rintro outcome firstBits secondBits thirdBits rfl
              | rintro outcome firstBits secondBits rfl
              | intro bits
              | skip
            all_goals try simp [CanInterpretTo.select_int (⟨64, hint⟩),
              CanInterpretTo.select_int (⟨32, hint⟩), CanInterpretTo.select_int (⟨1, hint⟩), Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
              RuntimeValue.isRefinedBy, Data.LLVM.Int.select, isRefinedBy, Id.run]


end Veir
