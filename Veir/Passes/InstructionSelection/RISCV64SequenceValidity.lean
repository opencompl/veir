module
public meta import Veir.OpCode
public meta import Veir.PatternRewriter.Puddle.Definitions
public meta import Veir.PatternRewriter.Puddle.Validity
import all Init.Data.Array.Basic
import all Veir.PatternRewriter.Puddle.Builders
import all Veir.PatternRewriter.Puddle.Definitions
import all Veir.Passes.InstructionSelection.RISCV64
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
open Puddle Puddle.CTree

@[simp]
theorem CanInterpretTo.abs_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__abs)) (x : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__abs) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.abs x property.is_int_min_poison)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

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
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

@[simp]
theorem CanInterpretTo.ssubSat_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__ssub__sat)) (x y : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__ssub__sat) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.ssubSat x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

@[simp]
theorem CanInterpretTo.uaddSat_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__uadd__sat)) (x y : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__uadd__sat) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.uaddSat x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

@[simp]
theorem CanInterpretTo.usubSat_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__usub__sat)) (x y : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__usub__sat) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.usubSat x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

@[simp]
theorem CanInterpretTo.sshlSat_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__sshl__sat)) (x y : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__sshl__sat) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.sshlSat x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

@[simp]
theorem CanInterpretTo.ushlSat_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__ushl__sat)) (x y : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__ushl__sat) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.ushlSat x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

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
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

@[simp]
theorem CanInterpretTo.bitreverse_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__bitreverse)) (x : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__bitreverse) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.bitreverse x)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

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

@[simp] private theorem choose_neg_reg (ty : RegisterType) (x : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .neg) () #[TypeAttr.of RegisterType ty] #[.reg x]) =
    CreationM.pure #[.reg (Data.RISCV.neg x)] :=
  choose_eq_pure _ _ (CanInterpretTo.neg_reg ty x)

@[simp] private theorem choose_max_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .max) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) =
    CreationM.pure #[.reg (Data.RISCV.max y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.max_reg ty x y)

@[simp] private theorem choose_rev8_reg (ty : RegisterType) (x : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .rev8) () #[TypeAttr.of RegisterType ty] #[.reg x]) =
    CreationM.pure #[.reg (Data.RISCV.rev8 x)] :=
  choose_eq_pure _ _ (CanInterpretTo.rev8_reg ty x)

@[simp] private theorem choose_maxu_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .maxu) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) =
    CreationM.pure #[.reg (Data.RISCV.maxu y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.maxu_reg ty x y)

@[simp] private theorem choose_minu_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .minu) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) =
    CreationM.pure #[.reg (Data.RISCV.minu y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.minu_reg ty x y)

@[simp] private theorem choose_add_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .add) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) =
    CreationM.pure #[.reg (Data.RISCV.add y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.add_reg ty x y)

@[simp] private theorem choose_sub_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .sub) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) =
    CreationM.pure #[.reg (Data.RISCV.sub y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.sub_reg ty x y)

@[simp] private theorem choose_sll_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .sll) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) =
    CreationM.pure #[.reg (Data.RISCV.sll y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.sll_reg ty x y)

@[simp] private theorem choose_srl_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .srl) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) =
    CreationM.pure #[.reg (Data.RISCV.srl y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.srl_reg ty x y)

@[simp] private theorem choose_sra_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .sra) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) =
    CreationM.pure #[.reg (Data.RISCV.sra y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.sra_reg ty x y)

@[simp] private theorem choose_xor_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .xor) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) =
    CreationM.pure #[.reg (Data.RISCV.xor y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.xor_reg ty x y)

@[simp] private theorem choose_or_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .or) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) =
    CreationM.pure #[.reg (Data.RISCV.or y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.or_reg ty x y)

@[simp] private theorem choose_and_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .and) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) =
    CreationM.pure #[.reg (Data.RISCV.and y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.and_reg ty x y)

@[simp] private theorem choose_slt_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .slt) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) =
    CreationM.pure #[.reg (Data.RISCV.slt y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.slt_reg ty x y)

@[simp] private theorem choose_czeroeqz_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .czeroeqz) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) =
    CreationM.pure #[.reg (Data.RISCV.czeroeqz y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.czeroeqz_reg ty x y)

@[simp] private theorem choose_czeronez_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .czeronez) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) =
    CreationM.pure #[.reg (Data.RISCV.czeronez y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.czeronez_reg ty x y)

@[simp] private theorem choose_li_reg (ty : RegisterType) (props : RISCVImmediateProperties) :
    CreationM.choose (CanInterpretTo (.riscv .li) props #[TypeAttr.of RegisterType ty] #[]) =
    CreationM.pure #[.reg (Data.RISCV.li props.value)] :=
  choose_eq_pure _ _ (CanInterpretTo.li_reg ty props)

@[simp] private theorem choose_xori_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .xori) props #[TypeAttr.of RegisterType ty] #[.reg x]) =
    CreationM.pure #[.reg (Data.RISCV.xori (props.immField 12) x)] :=
  choose_eq_pure _ _ (CanInterpretTo.xori_reg ty props x)

@[simp] private theorem choose_slli_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .slli) props #[TypeAttr.of RegisterType ty] #[.reg x]) =
    CreationM.pure #[.reg (Data.RISCV.slli (props.immField 6) x)] :=
  choose_eq_pure _ _ (CanInterpretTo.slli_reg ty props x)

@[simp] private theorem choose_srli_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .srli) props #[TypeAttr.of RegisterType ty] #[.reg x]) =
    CreationM.pure #[.reg (Data.RISCV.srli (props.immField 6) x)] :=
  choose_eq_pure _ _ (CanInterpretTo.srli_reg ty props x)

@[simp] private theorem choose_srai_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .srai) props #[TypeAttr.of RegisterType ty] #[.reg x]) =
    CreationM.pure #[.reg (Data.RISCV.srai (props.immField 6) x)] :=
  choose_eq_pure _ _ (CanInterpretTo.srai_reg ty props x)

@[simp] private theorem choose_sltiu_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .sltiu) props #[TypeAttr.of RegisterType ty] #[.reg x]) =
    CreationM.pure #[.reg (Data.RISCV.sltiu (props.immField 12) x)] :=
  choose_eq_pure _ _ (CanInterpretTo.sltiu_reg ty props x)

@[simp] private theorem choose_addi_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .addi) props #[TypeAttr.of RegisterType ty] #[.reg x]) =
    CreationM.pure #[.reg (Data.RISCV.addi (props.immField 12) x)] :=
  choose_eq_pure _ _ (CanInterpretTo.addi_reg ty props x)

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

@[simp] private theorem checked_true (a : α) : CreationM.checked True a = CreationM.pure a := rfl

macro "simpSequenceCreation" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 }) [Puddle.CTree.Pattern.PreservesSemantics, Puddle.CTree.MatchProg.Models,
    MatchProg.bindingDecls, List.partition_eq_filter_filter, List.range_succ, List.reverse_cons,
    Puddle.CTree.MatchProg.modelsDecls, Puddle.CTree.MatchDecl.Models,
    Puddle.CTree.CreateProg.interpretReplacement, Puddle.CTree.CreateProg.interpret, Puddle.CTree.CreateProg.interpretDecls,
    ↓CreationM.bind_assoc, ↓CreationM.pure_bind, ↓CreationM.bind_pure,
    ↓CreationM.invalid_bind,
    Puddle.CTree.CreateDecl.interpret, bind, pure,
    Interp.ok.injEq, Interp.ub.injEq, Interp.fail.injEq,
    SemanticAssignment.getValues, SemanticAssignment.getTypes,
    SemanticAssignment.getValue, SemanticAssignment.getType,
    SemanticAssignment.getProperty,
    SemanticAssignment.bindProperty, SemanticAssignment.bindType,
    SemanticAssignment.bindValue, SemanticAssignment.bind,
    SemanticAssignment.ForallValues, Puddle.CTree.SemanticAssignment.bindValues.go,
    MetadataTuple.resolveSemantic, MetadataTuple.Shape.resolveSemantic,
    MetadataTuple.Atom.resolveSemantic, MetadataTuple.bindSemantic,
    MetadataTuple.Shape.bindSemantic, MetadataTuple.Atom.bindSemantic,
    Puddle.CTree.MatchProg.RootCanInterpretTo,
    SemanticAssignment.bind_of_ne_eq,
    /- TypeAttr cast normalization -/
    IsTypeAttr.cast?_eq_some_iff,
    /- Native metadata tuples -/
    IsMetadataTuple.shape_unit, IsMetadataTuple.shape_type, IsMetadataTuple.shape_property,
    IsMetadataTuple.shape_type_cons, IsMetadataTuple.shape_property_cons,
    /- Concrete lists, arrays, options -/
    List.filter_cons_of_pos, List.filter_cons_of_neg, List.filter_nil, Function.comp_apply,
    List.reverse_nil, List.nil_append, List.cons_append, List.append_nil,
    Array.toList_map, Array.toList_range, List.range_zero, List.map_cons, List.map_nil,
    List.length_cons, List.length_nil,
    Array.size_map, Array.size_range,
    List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
    Option.bind_fun_some, Nat.add_zero, Nat.reduceAdd, Nat.zero_ne_one, Nat.reduceEqDiff,
    Option.map_some, Option.map_eq_some_iff, Option.getD_eq_iff,
    /- Propositional normalization -/
    Bool.not_true, Bool.not_false, Bool.not_eq_true, Bool.not_eq_true', Bool.false_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_false, or_false,
    not_false_eq_true, ne_eq, reduceCtorEq, ↓reduceIte, ↓reduceDIte, forall_const,
    and_true, and_imp, not_imp, Classical.not_forall, not_exists, not_and, exists_and_left,
    exists_false, false_or, exists_eq_left, exists_eq_right,
    forall_exists_index, forall_apply_eq_imp_iff, forall_eq_apply_imp_iff, true_and,
    /- Elementwise array refinement -/
    RuntimeValue.arrayIsRefinedBy_cons, RuntimeValue.arrayIsRefinedBy_refl,
    /- Handle equality injectivity -/
    Handle.mk.injEq])


 theorem abs_pattern_valid : Puddle.CTree.Pattern.Valid abs_pattern := by
  conv => arg 1; cbv
  provePuddleValid
  rintro _ ty rfl hty value hvalue property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hvalue
    obtain ⟨x, rfl⟩ := hvalue
    cases x <;> simp [CanInterpretTo.neg_reg, CanInterpretTo.max_reg,
      CanInterpretTo.abs_int (⟨64, hint⟩)]
    · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField] using
        (Data.RISCV.abs_refinement (x := .val _) (is_int_min_poison := property.is_int_min_poison))
    · intro bits
      simp [
        RuntimeValue.isRefinedBy, Data.LLVM.Int.abs, isRefinedBy, Id.run]

private theorem usubSat_pattern_valid : Puddle.CTree.Pattern.Valid usubSat_pattern := by
  conv => arg 1; cbv
  provePuddleValid
  rintro _ ty rfl hty lhs hleft rhs hright property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hleft hright
    obtain ⟨x, rfl⟩ := hleft
    obtain ⟨y, rfl⟩ := hright
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

private theorem uaddSat_pattern_valid : Puddle.CTree.Pattern.Valid uaddSat_pattern := by
  conv => arg 1; cbv
  provePuddleValid
  rintro _ ty rfl hty lhs hleft rhs hright property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hleft hright
    obtain ⟨x, rfl⟩ := hleft
    obtain ⟨y, rfl⟩ := hright
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

private theorem saddSat_pattern_valid : Puddle.CTree.Pattern.Valid saddSat_pattern := by
  conv => arg 1; cbv
  provePuddleValid
  rintro _ ty rfl hty lhs hleft rhs hright property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hleft hright
    obtain ⟨x, rfl⟩ := hleft
    obtain ⟨y, rfl⟩ := hright
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

private theorem ssubSat_pattern_valid : Puddle.CTree.Pattern.Valid ssubSat_pattern := by
  conv => arg 1; cbv
  provePuddleValid
  rintro _ ty rfl hty lhs hleft rhs hright property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hleft hright
    obtain ⟨x, rfl⟩ := hleft
    obtain ⟨y, rfl⟩ := hright
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

private theorem sshlSat_pattern_valid : Puddle.CTree.Pattern.Valid sshlSat_pattern := by
  conv => arg 1; cbv
  provePuddleValid
  rintro _ ty rfl hty lhs hleft rhs hright property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hleft hright
    obtain ⟨x, rfl⟩ := hleft
    obtain ⟨y, rfl⟩ := hright
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

private theorem ushlSat_pattern_valid : Puddle.CTree.Pattern.Valid ushlSat_pattern := by
  conv => arg 1; cbv
  provePuddleValid
  rintro _ ty rfl hty lhs hleft rhs hright property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hleft hright
    obtain ⟨x, rfl⟩ := hleft
    obtain ⟨y, rfl⟩ := hright
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

 theorem bswap64_pattern_valid : Puddle.CTree.Pattern.Valid (bswap_pattern 64) := by
  conv => arg 1; cbv
  provePuddleValid
  rintro _ ty rfl hty value hvalue property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hvalue
    obtain ⟨x, rfl⟩ := hvalue
    cases x <;> simp [
      CanInterpretTo.bswap_int (⟨64, hint⟩)]
    · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField] using
        (Data.RISCV.bswap_refinement (x := .val _))
    · intro bits
      simp [
        RuntimeValue.isRefinedBy, Data.LLVM.Int.bswap, isRefinedBy, Id.run]


 theorem bswap32_pattern_valid : Puddle.CTree.Pattern.Valid (bswap_pattern 32) := by
  conv => arg 1; cbv
  provePuddleValid
  rintro _ ty rfl hty value hvalue property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hvalue
    obtain ⟨x, rfl⟩ := hvalue
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
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

@[simp] theorem CanInterpretTo.fshr_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .intr__fshr)) (x y z : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .intr__fshr) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y, .int ty.bitwidth z] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.fshr x y z)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

@[simp] theorem CanInterpretTo.sllw_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .sllw) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.sllw y x)] :=
  CanInterpretTo.riscv_pure .sllw () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp] private theorem choose_sllw_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .sllw) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) =
    CreationM.pure #[.reg (Data.RISCV.sllw y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.sllw_reg ty x y)

@[simp] theorem CanInterpretTo.srlw_reg (ty : RegisterType) (x y : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .srlw) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] results ↔
      results = .ok #[.reg (Data.RISCV.srlw y x)] :=
  CanInterpretTo.riscv_pure .srlw () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y] _
    (by intro memory; rfl) results

@[simp] private theorem choose_srlw_reg (ty : RegisterType) (x y : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .srlw) () #[TypeAttr.of RegisterType ty] #[.reg x, .reg y]) =
    CreationM.pure #[.reg (Data.RISCV.srlw y x)] :=
  choose_eq_pure _ _ (CanInterpretTo.srlw_reg ty x y)

@[simp] theorem CanInterpretTo.slliw_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .slliw) props #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.slliw (props.immField 5) x)] :=
  CanInterpretTo.riscv_pure .slliw props #[TypeAttr.of RegisterType ty] #[.reg x] _
    (by intro memory; rfl) results

@[simp] private theorem choose_slliw_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .slliw) props #[TypeAttr.of RegisterType ty] #[.reg x]) =
    CreationM.pure #[.reg (Data.RISCV.slliw (props.immField 5) x)] :=
  choose_eq_pure _ _ (CanInterpretTo.slliw_reg ty props x)

@[simp] theorem CanInterpretTo.srliw_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .srliw) props #[TypeAttr.of RegisterType ty] #[.reg x] results ↔
      results = .ok #[.reg (Data.RISCV.srliw (props.immField 5) x)] :=
  CanInterpretTo.riscv_pure .srliw props #[TypeAttr.of RegisterType ty] #[.reg x] _
    (by intro memory; rfl) results

@[simp] private theorem choose_srliw_reg (ty : RegisterType) (props : RISCVImmediateProperties) (x : Data.RISCV.Reg) :
    CreationM.choose (CanInterpretTo (.riscv .srliw) props #[TypeAttr.of RegisterType ty] #[.reg x]) =
    CreationM.pure #[.reg (Data.RISCV.srliw (props.immField 5) x)] :=
  choose_eq_pure _ _ (CanInterpretTo.srliw_reg ty props x)

@[simp] theorem CanInterpretTo.select_int (ty : IntegerType)
    (property : propertiesOf (OpCode.llvm .select)) (c : Data.LLVM.Int 1) (x y : Data.LLVM.Int ty.bitwidth)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .select) property #[TypeAttr.of IntegerType ty]
      #[.int 1 c, .int ty.bitwidth x, .int ty.bitwidth y] results ↔
      results = .ok #[.int ty.bitwidth (Data.LLVM.Int.select c x y)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

private theorem reg_and_comm (x y : Data.RISCV.Reg) : Data.RISCV.and x y = Data.RISCV.and y x := by
  simp [Data.RISCV.and, BitVec.and_comm]

private theorem reg_or_comm (x y : Data.RISCV.Reg) : Data.RISCV.or x y = Data.RISCV.or y x := by
  simp [Data.RISCV.or, BitVec.or_comm]

set_option maxHeartbeats 5000000 in
 theorem bitreverse64_pattern_valid : Puddle.CTree.Pattern.Valid (bitreverse_pattern 64) := by
  conv => arg 1; cbv
  provePuddleValid
  rintro _ ty rfl hty value hvalue property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hvalue
    obtain ⟨x, rfl⟩ := hvalue
    cases x <;> simpSequenceCreation
    all_goals simp [CanInterpretTo.bitreverse_int (⟨64, hint⟩)]
    · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField, reg_and_comm, reg_or_comm] using
        (Data.RISCV.bitreverse_refinement (x := .val _))
    · intro bits
      simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.bitreverse, isRefinedBy, Id.run]



set_option maxHeartbeats 5000000 in
 theorem bitreverse32_pattern_valid : Puddle.CTree.Pattern.Valid (bitreverse_pattern 32) := by
  conv => arg 1; cbv
  provePuddleValid
  rintro _ ty rfl hty value hvalue property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hvalue
    obtain ⟨x, rfl⟩ := hvalue
    cases x <;> simpSequenceCreation
    all_goals simp [CanInterpretTo.bitreverse_int (⟨32, hint⟩)]
    · simpa [Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
        RuntimeValue.isRefinedBy, LLVM.Int.toReg, RISCVImmediateProperties.immField, reg_and_comm, reg_or_comm] using
        (Data.RISCV.bitreverse_refinement_32 (x := .val _))
    · intro bits
      simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.bitreverse, isRefinedBy, Id.run]



set_option maxHeartbeats 5000000 in
 theorem fshl64General_pattern_valid : Puddle.CTree.Pattern.Valid (lowerFunnelShift true 64) := by
  conv => arg 1; cbv
  provePuddleValid
  rintro _ ty rfl hty lhs hleft rhs hright amt hamt property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hleft hright hamt
    obtain ⟨x, rfl⟩ := hleft
    obtain ⟨y, rfl⟩ := hright
    obtain ⟨z, rfl⟩ := hamt
    cases x <;> cases y <;> cases z <;> simpSequenceCreation
    all_goals simp [CanInterpretTo.fshl_int (⟨64, hint⟩)]
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
 theorem fshl32General_pattern_valid : Puddle.CTree.Pattern.Valid (lowerFunnelShift true 32) := by
  conv => arg 1; cbv
  provePuddleValid
  rintro _ ty rfl hty lhs hleft rhs hright amt hamt property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hleft hright hamt
    obtain ⟨x, rfl⟩ := hleft
    obtain ⟨y, rfl⟩ := hright
    obtain ⟨z, rfl⟩ := hamt
    cases x <;> cases y <;> cases z <;> simpSequenceCreation
    all_goals simp [CanInterpretTo.fshl_int (⟨32, hint⟩)]
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
 theorem fshr64General_pattern_valid : Puddle.CTree.Pattern.Valid (lowerFunnelShift false 64) := by
  conv => arg 1; cbv
  provePuddleValid
  rintro _ ty rfl hty lhs hleft rhs hright amt hamt property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hleft hright hamt
    obtain ⟨x, rfl⟩ := hleft
    obtain ⟨y, rfl⟩ := hright
    obtain ⟨z, rfl⟩ := hamt
    cases x <;> cases y <;> cases z <;> simpSequenceCreation
    all_goals simp [CanInterpretTo.fshr_int (⟨64, hint⟩)]
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
 theorem fshr32General_pattern_valid : Puddle.CTree.Pattern.Valid (lowerFunnelShift false 32) := by
  conv => arg 1; cbv
  provePuddleValid
  rintro _ ty rfl hty lhs hleft rhs hright amt hamt property
  cases ty with
  | mk bw hint =>
    dsimp [IntegerType.bitwidth] at hty
    subst bw
    simp only [RuntimeValue.Conforms.integerType] at hleft hright hamt
    obtain ⟨x, rfl⟩ := hleft
    obtain ⟨y, rfl⟩ := hright
    obtain ⟨z, rfl⟩ := hamt
    cases x <;> cases y <;> cases z <;> simpSequenceCreation
    all_goals simp [CanInterpretTo.fshr_int (⟨32, hint⟩)]
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
 theorem selectGeneral_pattern_valid : Puddle.CTree.Pattern.Valid (select_pattern false false) := by
  conv => arg 1; cbv
  provePuddleValid
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
        cases c with
        | val cbits =>
          rcases BitVec.eq_zero_or_eq_one cbits with rfl | rfl
          <;> cases t <;> cases f <;> simpSequenceCreation
          all_goals first
            | rintro outcome firstBits secondBits thirdBits rfl
            | rintro outcome firstBits secondBits rfl
            | intro bits
            | skip
          all_goals simp [CanInterpretTo.select_int (⟨64, hint⟩),
            CanInterpretTo.select_int (⟨32, hint⟩), CanInterpretTo.select_int (⟨1, hint⟩), Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, Data.LLVM.Int.select, isRefinedBy, Id.run,
            Data.RISCV.czeroeqz, Data.RISCV.czeronez, Data.RISCV.or, RISCV.Reg.toInt]
        | poison =>
          cases t <;> cases f <;> simpSequenceCreation
          all_goals first
            | rintro outcome firstBits secondBits thirdBits rfl
            | rintro outcome firstBits secondBits rfl
            | intro bits
            | skip
          all_goals simp [CanInterpretTo.select_int (⟨64, hint⟩),
            CanInterpretTo.select_int (⟨32, hint⟩), CanInterpretTo.select_int (⟨1, hint⟩), Interp.isRefinedBy, RuntimeValue.arrayIsRefinedBy_cons,
            RuntimeValue.isRefinedBy, Data.LLVM.Int.select, isRefinedBy, Id.run]


end Veir
