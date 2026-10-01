module
import Veir.PatternRewriter.Puddle.CTreeSymbolicValidity
public meta import Veir.OpCode
import all Veir.OpCode
import all Veir.GlobalOpInfo
import all Veir.Interpreter.Basic
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV.Properties
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
import all Veir.Data.RISCV.Reg.Basic
public meta import Veir.PatternRewriter.Puddle.Definitions
public meta import Veir.PatternRewriter.Puddle.Validity

open Veir Veir.Puddle Veir.Puddle.CTree

namespace Veir.InstructionSelection.CTreeProofs
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
section

@[simp]
private theorem CanInterpretTo.icmp_int (ty : IntegerType) (resTy : IntegerType)
    (property : propertiesOf (OpCode.llvm .icmp)) (x y : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .icmp) property #[TypeAttr.of IntegerType resTy]
      #[.int ty.bitwidth x, .int ty.bitwidth y] results ↔
      results = .ok #[.int 1 (Data.LLVM.Int.icmp x y property.predicate)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

@[simp]
private theorem CanInterpretTo.xor_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .xor) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.xor y x)] := by
  exact CanInterpretTo.riscv_pure .xor () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
private theorem CanInterpretTo.slt_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .slt) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.slt y x)] := by
  exact CanInterpretTo.riscv_pure .slt () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
private theorem CanInterpretTo.li_reg (ty : RegisterType) (props : RISCVImmediateProperties)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .li) props #[TypeAttr.of RegisterType ty] #[] results ↔
      results = .ok #[.reg (Data.RISCV.li props.value)] := by
  exact CanInterpretTo.riscv_pure .li props #[TypeAttr.of RegisterType ty] #[] _
    (by intro memory; rfl) results

@[simp]
private theorem CanInterpretTo.xori_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .xori) props #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.xori (props.immField 12) x)] := by
  exact CanInterpretTo.riscv_pure .xori props #[TypeAttr.of RegisterType ty] #[.reg x] _
    (by intro memory; rfl) results

@[simp]
private theorem CanInterpretTo.sltiu_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .sltiu) props #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.sltiu (props.immField 12) x)] := by
  exact CanInterpretTo.riscv_pure .sltiu props #[TypeAttr.of RegisterType ty] #[.reg x] _
    (by intro memory; rfl) results

@[simp]
private theorem CanInterpretTo.sltu_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .sltu) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.sltu y x)] := by
  exact CanInterpretTo.riscv_pure .sltu () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp]
private theorem CanInterpretTo.sextb_reg (ty : RegisterType) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .sextb) () #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.sextb x)] := by
  exact CanInterpretTo.riscv_pure .sextb () #[TypeAttr.of RegisterType ty] #[.reg x] _
    (by intro memory; rfl) results

@[simp]
private theorem CanInterpretTo.sextw_reg (ty : RegisterType) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .sextw) () #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.sextw x)] := by
  exact CanInterpretTo.riscv_pure .sextw () #[TypeAttr.of RegisterType ty] #[.reg x] _
    (by intro memory; rfl) results

private theorem choose_eq_pure {α : Type} (values : α) (p : Interp α → Prop)
    (h : ∀ outcome, p outcome ↔ outcome = .ok values) :
    CreationM.choose p = CreationM.pure values := by
  apply CreationM.ext
  · rfl
  · intro outcome
    exact h outcome

@[simp] private theorem choose_cast_int_val (w : Nat) (bits : BitVec w) :
    CreationM.choose (CanInterpretTo (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of RegisterType {}] #[.int w (.val bits)]) =
    CreationM.pure #[.reg ⟨bits.zeroExtend 64⟩] :=
  choose_eq_pure _ _ (CanInterpretTo.cast_int_val w bits)

@[simp] private theorem choose_cast_reg_int (ty : IntegerType) (reg : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of IntegerType ty] #[.reg reg]) =
    CreationM.pure #[.int ty.bitwidth (RISCV.Reg.toInt reg ty.bitwidth)] :=
  choose_eq_pure _ _ (CanInterpretTo.cast_reg_int ty reg)

@[simp] private theorem models_bind_cast_poison (w : Nat)
    (next : Array RuntimeValue → CreationM α) (post : Interp α → Prop) :
    ((CreationM.choose (CanInterpretTo (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of RegisterType {}] #[.int w .poison])).bind next).Models post ↔
    ∀ bits : BitVec 64, (next #[.reg ⟨bits⟩]).Models post := by
  rw [CreationM.models_bind]
  simp [CreationM.Models, CreationM.choose]

@[simp] private theorem bind_return (value : α) (next : α → CreationM β) :
    (⟨True, fun outcome => outcome = .ok value⟩ : CreationM α).bind next = next value :=
  CreationM.pure_bind value next

@[simp] private theorem models_return (value : α) (post : Interp α → Prop) :
    (⟨True, fun outcome => outcome = .ok value⟩ : CreationM α).Models post ↔ post (.ok value) :=
  CreationM.models_pure value post

@[simp] private theorem models_eta (m : CreationM α) (post : Interp α → Prop) :
    (⟨m.safe, m.outcomes⟩ : CreationM α).Models post ↔ m.Models post := Iff.rfl

@[simp] private theorem choose_xor_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .xor) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) = CreationM.pure #[.reg (Data.RISCV.xor y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.xor_reg ty x y)

@[simp] private theorem choose_slt_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .slt) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) = CreationM.pure #[.reg (Data.RISCV.slt y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.slt_reg ty x y)

@[simp] private theorem choose_li_reg (ty : RegisterType) (props : RISCVImmediateProperties) :
    CreationM.choose (CanInterpretTo (.riscv .li) props #[TypeAttr.of RegisterType ty] #[]) = CreationM.pure #[.reg (Data.RISCV.li props.value)] :=
  choose_eq_pure _ _ (CanInterpretTo.li_reg ty props)

@[simp] private theorem choose_xori_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .xori) props #[TypeAttr.of RegisterType ty] #[.reg x]) = CreationM.pure #[.reg (Data.RISCV.xori (props.immField 12) x)] :=
  choose_eq_pure _ _ (CanInterpretTo.xori_reg ty props x)

@[simp] private theorem choose_sltiu_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .sltiu) props #[TypeAttr.of RegisterType ty] #[.reg x]) = CreationM.pure #[.reg (Data.RISCV.sltiu (props.immField 12) x)] :=
  choose_eq_pure _ _ (CanInterpretTo.sltiu_reg ty props x)

@[simp] private theorem choose_sltu_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .sltu) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) = CreationM.pure #[.reg (Data.RISCV.sltu y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.sltu_reg ty x y)

@[simp] private theorem choose_sextb_reg (ty : RegisterType) (x : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .sextb) () #[TypeAttr.of RegisterType ty] #[.reg x]) = CreationM.pure #[.reg (Data.RISCV.sextb x)] :=
  choose_eq_pure _ _ (CanInterpretTo.sextb_reg ty x)

@[simp] private theorem choose_sextw_reg (ty : RegisterType) (x : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .sextw) () #[TypeAttr.of RegisterType ty] #[.reg x]) = CreationM.pure #[.reg (Data.RISCV.sextw x)] :=
  choose_eq_pure _ _ (CanInterpretTo.sextw_reg ty x)

private theorem icmp64_eq_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 64 .eq) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨64, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_eq (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_ne_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 64 .ne) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨64, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ne (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_slt_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 64 .slt) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨64, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_slt (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_sle_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 64 .sle) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨64, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sle (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_sgt_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 64 .sgt) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨64, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sgt (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_sge_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 64 .sge) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨64, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sge (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_ult_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 64 .ult) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨64, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ult (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_ule_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 64 .ule) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨64, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ule (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_ugt_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 64 .ugt) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨64, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ugt (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp64_uge_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 64 .uge) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨64, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_uge (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_eq_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 32 .eq) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨32, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_eq_32 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_ne_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 32 .ne) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨32, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ne_32 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_slt_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 32 .slt) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨32, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_slt_32 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_sle_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 32 .sle) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨32, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sle_32 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_sgt_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 32 .sgt) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨32, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sgt_32 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_sge_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 32 .sge) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨32, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sge_32 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_ult_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 32 .ult) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨32, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ult_32 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_ule_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 32 .ule) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨32, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ule_32 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_ugt_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 32 .ugt) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨32, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ugt_32 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp32_uge_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 32 .uge) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨32, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_uge_32 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_eq_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 8 .eq) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨8, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_eq_8 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_ne_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 8 .ne) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨8, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ne_8 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_slt_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 8 .slt) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨8, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_slt_8 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_sle_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 8 .sle) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨8, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sle_8 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_sgt_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 8 .sgt) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨8, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sgt_8 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_sge_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 8 .sge) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨8, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_sge_8 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_ult_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 8 .ult) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨8, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ult_8 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_ule_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 8 .ule) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨8, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ule_8 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_ugt_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 8 .ugt) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨8, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_ugt_8 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

private theorem icmp8_uge_valid : Veir.Puddle.CTree.Pattern.Valid (icmp_pattern 8 .uge) := by
  conv => arg 1; cbv
  provePuddleValid sym =>
    rintro _ ty rfl hty _ resTy rfl hres lhs hleft rhs hright property hprop
    cases ty with
    | mk bw hint =>
      dsimp [IntegerType.bitwidth] at hty
      subst bw
      cases resTy with
      | mk resBw resHint =>
        dsimp [IntegerType.bitwidth] at hres
        subst resBw
        simp only [RuntimeValue.Conforms.integerType] at hleft hright
        obtain ⟨x, rfl⟩ := hleft
        obtain ⟨y, rfl⟩ := hright
        cases x <;> cases y <;> simp (config := { maxSteps := 1000000 }) [CreationM.pure, CreationM.checked, CreationM.invalid, SemanticAssignment.bind, CanInterpretTo.icmp_int (⟨8, hint⟩) (⟨1, resHint⟩), hprop]
        · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField,
            Data.RISCV.xor, BitVec.xor_comm] using
            (Data.RISCV.icmp_refinement_uge_8 (x := .val _) (y := .val _))
        all_goals
          intros
          try (rename_i outcome bits₁ bits₂ htarget; rw [htarget])
          simp [hprop, Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
          RuntimeValue.isRefinedBy, Data.LLVM.Int.icmp, isRefinedBy, Id.run]

end
end Veir.InstructionSelection.CTreeProofs
