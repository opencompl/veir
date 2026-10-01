module

public import Veir.PatternRewriter.Puddle.CTreeValidity
import all Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.Pass
public import Veir.Data.Casting
import all Veir.Data.Casting
import all Veir.IR.Attribute
import all Veir.Interpreter.CTree
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Interpreter.Basic

namespace Veir.Puddle.CTree
public section

/-- Casting a concrete integer into a register zero-extends its bits. -/
@[simp]
theorem CanInterpretTo.cast_int_val (w : Nat) (value : BitVec w)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of RegisterType (RegisterType.mk none)] #[.int w (.val value)] results ↔
      results = .ok #[.reg ⟨value.zeroExtend 64⟩] := by
  unfold CanInterpretTo
  change (∀ memory, PureOrErr.CanInterpretTo
    (pure (#[.reg ⟨value.zeroExtend 64⟩], memory, none))
    (results.map (·, memory, none))) ↔ _
  cases results <;> simp

/-- Casting integer poison into a register may choose any concrete register value. -/
@[simp]
theorem CanInterpretTo.cast_int_poison (w : Nat) (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of RegisterType (RegisterType.mk none)] #[.int w .poison] results ↔
      ∃ bits : BitVec 64, results = .ok #[.reg ⟨bits⟩] := by
  unfold CanInterpretTo
  change (∀ memory, PureOrErr.CanInterpretTo
    (CTree.bind (CTree.CTree.choose (E := ErrorE ⊕ₑ UBE) (C := FreezeC) (SubC := FreezeC) (FreezeCIn.mk 64))
      (fun bits => pure (#[.reg ⟨bits⟩], memory, none)))
    (results.map (·, memory, none))) ↔ _
  cases results <;> simp [PureOrErr.CanInterpretTo.bind_iff]

/-- Casting a register back into an integer deterministically truncates/extends its bits. -/
@[simp]
theorem CanInterpretTo.cast_reg_int (ty : IntegerType) (value : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of IntegerType ty] #[.reg value] results ↔
      results = .ok #[.int ty.bitwidth (_root_.RISCV.Reg.toInt value ty.bitwidth)] := by
  unfold CanInterpretTo
  change (∀ memory, PureOrErr.CanInterpretTo
    (pure (#[.int ty.bitwidth (RISCV.Reg.toInt value ty.bitwidth)], memory, none))
    (results.map (·, memory, none))) ↔ _
  cases results <;> simp

/-- A deterministic RISC-V instruction returning unchanged memory has exactly its computed result. -/
theorem CanInterpretTo.riscv_pure (op : Riscv) (props : propertiesOf (.riscv op : OpCode))
    (types : Array TypeAttr) (args values : Array RuntimeValue)
    (h : ∀ memory, Veir.interpretOp' (.riscv op) props types args #[] memory =
      .ok (values, memory, none)) (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv op) props types args results ↔ results = .ok values := by
  simp only [CanInterpretTo, interpretOpCTree, h]
  cases results <;> simp [monadLift, MonadLift.monadLift]

@[simp]
theorem CanInterpretTo.clz_reg (value : Data.RISCV.Reg) (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .clz) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg value] results ↔ results = .ok #[.reg (Data.RISCV.clz value)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp]
theorem CanInterpretTo.clzw_reg (value : Data.RISCV.Reg) (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .clzw) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg value] results ↔ results = .ok #[.reg (Data.RISCV.clzw value)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp]
theorem CanInterpretTo.ctz_reg (value : Data.RISCV.Reg) (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .ctz) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg value] results ↔ results = .ok #[.reg (Data.RISCV.ctz value)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp]
theorem CanInterpretTo.ctzw_reg (value : Data.RISCV.Reg) (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .ctzw) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg value] results ↔ results = .ok #[.reg (Data.RISCV.ctzw value)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp]
theorem CanInterpretTo.cpop_reg (value : Data.RISCV.Reg) (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .cpop) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg value] results ↔ results = .ok #[.reg (Data.RISCV.cpop value)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp]
theorem CanInterpretTo.cpopw_reg (value : Data.RISCV.Reg) (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .cpopw) () #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.reg value] results ↔ results = .ok #[.reg (Data.RISCV.cpopw value)] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

end
end Veir.Puddle.CTree
