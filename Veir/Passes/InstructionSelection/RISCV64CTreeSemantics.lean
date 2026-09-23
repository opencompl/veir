module

public import Veir.PatternRewriter.Puddle.CTreeValidity
import all Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.Pass
public import Veir.Data.Casting
import all Veir.Data.Casting
import all Veir.IR.Attribute
import all Veir.Interpreter.CTree
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.Builtin.Interpreter
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Interpreter.Basic
import all Veir.Dialects.LLVM.Interpreter

namespace Veir.Puddle.CTree
public section

/-- Direct stateful semantics for a concrete integer-to-register cast. -/
@[simp]
theorem interpretOpCTree_cast_int_val (w : Nat) (value : BitVec w) (memory : MemoryState) :
    Veir.CTree.interpretOp' (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of RegisterType (RegisterType.mk none)] #[.int w (.val value)] #[] memory =
      pure (#[.reg ⟨value.zeroExtend 64⟩], memory, none) := by
  rfl

/-- Poison casts choose register bits while retaining the current memory. -/
@[simp]
theorem interpretOpCTree_cast_int_poison (w : Nat) (memory : MemoryState) :
    Veir.CTree.interpretOp' (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of RegisterType (RegisterType.mk none)] #[.int w .poison] #[] memory =
      CTree.bind (CTree.CTree.choose (E := ErrorE ⊕ₑ CTree.UBE) (C := FreezeC)
        (SubC := FreezeC) (FreezeCIn.mk 64))
        (fun bits => pure (#[.reg ⟨bits⟩], memory, none)) := by
  rfl

/-- Register-to-integer casts preserve memory and produce a concrete integer. -/
@[simp]
theorem interpretOpCTree_cast_reg_int (ty : IntegerType) (value : Data.RISCV.Reg)
    (memory : MemoryState) :
    Veir.CTree.interpretOp' (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of IntegerType ty] #[.reg value] #[] memory =
      pure (#[.int ty.bitwidth (RISCV.Reg.toInt value ty.bitwidth)], memory, none) := by
  rfl

/-- Peel a target cast without unfolding the source or its continuation. -/
@[simp]
theorem Tree.sim_target_bind_cast_int {α β : Type} {relation : β → α → Prop}
    (w : Nat) (value : Data.LLVM.Int w) (memory : MemoryState) (source : Tree α)
    (next : (Array RuntimeValue × MemoryState × Option ControlFlowAction) → Tree β) :
    CTree.Sim relation
      (CTree.bind (Veir.CTree.interpretOp' (.builtin .unrealized_conversion_cast) ()
        #[TypeAttr.of RegisterType (RegisterType.mk none)] #[.int w value] #[] memory) next) source ↔
      ∀ bits : BitVec 64, CTree.Sim relation
        (next (#[.reg ⟨match value with
          | .val value => value.zeroExtend 64
          | .poison => bits⟩], memory, none)) source := by
  cases value <;>
    simp [CTree.CTree.choose_def, CTree.CTree.tau_def]

/-- Every choice of the poison bits of a target byte cast must refine the source. -/
@[simp]
theorem Tree.sim_target_bind_cast_byte {α β : Type} {relation : β → α → Prop}
    (w : Nat) (value : Data.LLVM.Byte w) (memory : MemoryState) (source : Tree α)
    (next : (Array RuntimeValue × MemoryState × Option ControlFlowAction) → Tree β) :
    CTree.Sim relation
      (CTree.bind (Veir.CTree.interpretOp' (.builtin .unrealized_conversion_cast) ()
        #[TypeAttr.of RegisterType {}] #[.byte w value] #[] memory) next) source ↔
      ∀ bits : BitVec w, CTree.Sim relation
        (next (#[.reg ⟨(value.val ||| (value.poison &&& bits)).zeroExtend 64⟩], memory, none)) source := by
  change CTree.Sim relation
      (CTree.bind (if value.poison = 0 then pure (#[.reg (LLVM.Byte.toReg value)], memory, none)
      else CTree.bind (CTree.CTree.choose (E := ErrorE ⊕ₑ CTree.UBE) (C := FreezeC)
        (SubC := FreezeC) (FreezeCIn.mk w))
        (fun bits => pure (#[.reg ⟨(value.val ||| (value.poison &&& bits)).zeroExtend 64⟩], memory, none))) next) source ↔ _
  by_cases h : value.poison = 0
  all_goals simp only [h, ↓reduceIte]
  all_goals simp [LLVM.Byte.toReg, CTree.CTree.choose_def, CTree.CTree.tau_def]

/-- Decoding a register as a byte is deterministic and preserves memory. -/
@[simp]
theorem interpretOpCTree_cast_reg_byte (w : Nat) (value : Data.RISCV.Reg)
    (memory : MemoryState) :
    Veir.CTree.interpretOp' (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of LLVM.ByteType ⟨w⟩] #[.reg value] #[] memory =
      pure (#[.byte w (RISCV.Reg.toByte value w)], memory, none) := by
  rfl

/-- Deterministic fallback operations can be rewritten before reasoning about refinement. -/
theorem interpretOpCTree_riscv_pure (op : Riscv) (props : propertiesOf (.riscv op : OpCode))
    (types : Array TypeAttr) (args values : Array RuntimeValue) (memory : MemoryState)
    (h : Veir.interpretOp' (.riscv op) props types args #[] memory =
      .ok (values, memory, none)) :
    Veir.CTree.interpretOp' (.riscv op) props types args #[] memory = pure (values, memory, none) := by
  simp [Veir.CTree.interpretOp', h, monadLift, MonadLift.monadLift]

/-- A RISC-V target step propagates terminal outcomes and continues successful ones. -/
@[simp]
theorem Tree.sim_target_bind_riscv {α β : Type} {relation : β → α → Prop}
    (op : Riscv) (props : propertiesOf (.riscv op : OpCode))
    (types : Array TypeAttr) (args : Array RuntimeValue) (memory : MemoryState)
    (source : Tree α)
    (next : (Array RuntimeValue × MemoryState × Option ControlFlowAction) → Tree β) :
    CTree.Sim relation
      (CTree.bind (Veir.CTree.interpretOp' (.riscv op) props types args #[] memory) next) source ↔
    match Veir.interpretOp' (.riscv op) props types args #[] memory with
    | .ok value => CTree.Sim relation (next value) source
    | .ub _ => CTree.Sim relation (ub : Tree _) source
    | .fail _ => CTree.Sim relation (fail : Tree _) source := by
  simp only [Veir.CTree.interpretOp']
  cases Veir.interpretOp' (.riscv op) props types args #[] memory <;>
    simp [monadLift, MonadLift.monadLift]

/-- All LLVM operations except freeze use the deterministic interpreter. -/
theorem interpretOpCTree_llvm_nonfreeze (op : Llvm) (hne : op ≠ .freeze)
    (props : propertiesOf (.llvm op : OpCode)) (types : Array TypeAttr)
    (args : Array RuntimeValue) (blocks : Array BlockPtr) (memory : MemoryState) :
    Veir.CTree.interpretOp' (.llvm op) props types args blocks memory =
      monadLift (Llvm.interpretOp' op props types args blocks memory .riscv64) := by
  cases op <;> simp_all [Veir.CTree.interpretOp', Llvm.interpretOpCTree]

/-- Possible outcomes of a deterministic, memory-preserving LLVM operation. -/
theorem CanInterpretTo.llvm_pure (op : Llvm) (hne : op ≠ .freeze)
    (props : propertiesOf (.llvm op : OpCode)) (types : Array TypeAttr)
    (args values : Array RuntimeValue)
    (h : ∀ memory, Llvm.interpretOp' op props types args #[] memory .riscv64 =
      .ok (values, memory, none)) (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm op) props types args results ↔ results = .ok values := by
  simp only [CanInterpretTo, interpretOpCTree_llvm_nonfreeze op hne, h]
  cases results <;> simp [monadLift, MonadLift.monadLift]

/-- Casting a concrete integer into a register zero-extends its bits. -/
@[simp]
theorem CanInterpretTo.cast_int_val (w : Nat) (value : BitVec w)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of RegisterType (RegisterType.mk none)] #[.int w (.val value)] results ↔
      results = .ok #[.reg ⟨value.zeroExtend 64⟩] := by
  unfold CanInterpretTo
  change (∀ memory, PureOrErr.CanInterpretTo (E := ErrorE ⊕ₑ CTree.UBE) (C := FreezeC)
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
  change (∀ memory, PureOrErr.CanInterpretTo (E := ErrorE ⊕ₑ CTree.UBE) (C := FreezeC)
    (CTree.bind (CTree.CTree.choose (E := ErrorE ⊕ₑ CTree.UBE) (C := FreezeC) (SubC := FreezeC) (FreezeCIn.mk 64))
      (fun bits => pure (#[.reg ⟨bits⟩], memory, none)))
    (results.map (·, memory, none))) ↔ _
  cases results <;> simp [PureOrErr.CanInterpretTo.bind_iff]

/-- Casting an integer zero-extends concrete bits or chooses any register value for poison. -/
@[simp]
theorem CanInterpretTo.cast_int_val' (w : Nat) value'
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.builtin .unrealized_conversion_cast) properties
      #[TypeAttr.of RegisterType (RegisterType.mk none)] #[.int w value'] results ↔
      ∃ bits : BitVec 64, results = .ok #[.reg ⟨match value' with
        | .val value => value.zeroExtend 64
        | .poison => bits⟩] := by
  cases properties
  cases value' <;> simp

/-- Casting a register back into an integer deterministically truncates/extends its bits. -/
@[simp]
theorem CanInterpretTo.cast_reg_int (ty : IntegerType) (value : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of IntegerType ty] #[.reg value] results ↔
      results = .ok #[.int ty.bitwidth (_root_.RISCV.Reg.toInt value ty.bitwidth)] := by
  unfold CanInterpretTo
  change (∀ memory, PureOrErr.CanInterpretTo (E := ErrorE ⊕ₑ CTree.UBE) (C := FreezeC)
    (pure (#[.int ty.bitwidth (RISCV.Reg.toInt value ty.bitwidth)], memory, none))
    (results.map (·, memory, none))) ↔ _
  cases results <;> simp

/-- A deterministic RISC-V instruction returning unchanged memory has exactly its computed result. -/
theorem CanInterpretTo.riscv_pure (op : Riscv) (props : propertiesOf (.riscv op : OpCode))
    (types : Array TypeAttr) (args values : Array RuntimeValue)
    (h : ∀ memory, Veir.interpretOp' (.riscv op) props types args #[] memory =
      .ok (values, memory, none)) (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv op) props types args results ↔ results = .ok values := by
  simp only [CanInterpretTo, Veir.CTree.interpretOp', h]
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

/-- Reduce straight-line register computations, leaving LLVM semantics and scalar
refinement to the caller. Poison casts remain universally quantified choices. -/
macro "simpRiscvTrees" : tactic =>
  `(tactic| simp only [Tree.sim_target_bind_cast_int, Tree.sim_target_bind_cast_byte,
    Tree.sim_target_bind_riscv, interpretOpCTree_cast_reg_int, interpretOpCTree_cast_reg_byte,
    Veir.interpretOp', Riscv.interpretOp', Interp.pure_eq,
    _root_.CTree.bind_pure, List.size_toArray, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.lt_add_one, getElem!_pos, List.getElem_toArray,
    List.getElem_cons_zero])

end
end Veir.Puddle.CTree
