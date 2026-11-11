module

import all Veir.PatternRewriter.Puddle.CTreeProofs

import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.Passes.InstructionSelection.Common
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.RISCV_Cf.OpInfo
import all Veir.Dialects.Builtin.OpInfo
import all Veir.GlobalOpInfo
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.Builtin.Interpreter
import all Veir.Data.Casting
import Veir.PatternRewriter.Puddle.Definitions
import Veir.PatternRewriter.Puddle.Validity
import Veir.PatternRewriter.Puddle.CTreeValidityTactics
public import Veir.IR.Simp

namespace Veir

open Puddle
open _root_.CTree

@[simp, ctree_semantics]
theorem TypeAttr.forall_of_eq_imp_iff {T : Type} [IsTypeAttr T] {P : TypeAttr → T → Prop} :
  (∀ (type : TypeAttr) (x : T),
    TypeAttr.of T x = type → P type x) ↔
  (∀ (x : T), P (TypeAttr.of T x) x)
    := by
  grind

@[simp, ctree_semantics]
theorem IntegerType.forall_bitwidth_eq_implies_iff (P : IntegerType → Prop) :
    (∀ (x : IntegerType), x.bitwidth = y → P x) ↔
    ∀ signedness, P (IntegerType.mk y signedness) := by
  grind [cases IntegerType]

/-- A pure tree is simulated by a choice followed by `after` exactly when one
choice result makes `after` simulate that pure tree. -/
@[simp, ctree_semantics]
theorem CTree.Sim.pure_bind_choose_iff
  {EIn CIn C'In SubCIn : Type} {E : EIn → Type} [HasUB EIn]
  {C : CIn → Type} {C' : C'In → Type} {SubC : SubCIn → Type} [SubC -< C']
  {α β : Type} (relation : α → β → Prop) (value : α) (choice : SubCIn)
  (after : SubC choice → CTree E C' β) :
  CTree.Sim relation (pure value : CTree E C α)
      (CTree.bind (CTree.choose choice) after) ↔
    ∃ chosen, CTree.Sim relation (pure value : CTree E C α) (after chosen) := by
  simp only [CTree.choose_def, CTree.tau_def, _root_.CTree.CTree.bind_tau,
    _root_.CTree.CTree.bind_ret, Sim.pure_tau]
  constructor
  · rintro ⟨chosen, h⟩
    exact ⟨Subeffect.mapCont SubC C' choice chosen, h⟩
  · rintro ⟨chosen, h⟩
    obtain ⟨branch, rfl⟩ := Subeffect.map_surj (ε₁ := SubC) (ε₂ := C') choice chosen
    exact ⟨branch, h⟩

@[ctree_semantics]
theorem CTree.Sim.bind_interpretUnrealizedConversionCastCTree_reg_int_iff {EIn : Type} {E : EIn → Type}
  [HasUB EIn] [ErrorE -< E] [UBE -< E]
  {C'In : Type} {C' : C'In → Type}
  {bitwidth : Nat} (a : Data.LLVM.Int bitwidth) (memory : MemoryState)
  (after : (Array RuntimeValue × MemoryState × Option ControlFlowAction) →
    CTree E FreezeC (Array RuntimeValue × MemoryState × Option ControlFlowAction))
  (other : CTree E C' (Array RuntimeValue × MemoryState × Option ControlFlowAction)) :
  (CTree.Sim (E := E) (C := FreezeC) (C' := C') f
    (CTree.bind
      (Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of RegisterType { }]
        #[RuntimeValue.int bitwidth a] memory) after)
    other) ↔
  (∀ (value : Data.RISCV.Reg),
    (∀ bits, a = .val bits → value.val = bits.setWidth 64) →
    CTree.Sim (E := E) (C := FreezeC) (C' := C') f
      (after (#[.reg value], memory, none)) other) := by
  rw [Builtin.interpretUnrealizedConversionCastCTree_reg_int]
  cases a with
  | val bits =>
    simp
    constructor
    · rintro h ⟨value⟩ rfl
      exact h
    · intro h
      exact h ⟨bits.setWidth 64⟩ rfl
  | poison =>
    simp only [CTree.choose_def, CTree.tau_def, Bind.bind,
      _root_.CTree.CTree.bind_tau, _root_.CTree.CTree.bind_ret, bind_pure, Sim.tau_l]
    simp
    constructor
    · rintro h ⟨value⟩
      exact h value
    · intro h value
      exact h ⟨value⟩

/-- Casting a byte to a register preserves defined bits and resolves poisoned bits before resizing. -/
@[ctree_semantics]
theorem CTree.Sim.bind_interpretUnrealizedConversionCastCTree_reg_byte_iff
  {EIn : Type} {E : EIn → Type}
  [HasUB EIn] [ErrorE -< E] [UBE -< E]
  {C'In : Type} {C' : C'In → Type}
  {bitwidth : Nat} (a : Data.LLVM.Byte bitwidth) (memory : MemoryState)
  (after : (Array RuntimeValue × MemoryState × Option ControlFlowAction) →
    CTree E FreezeC (Array RuntimeValue × MemoryState × Option ControlFlowAction))
  (other : CTree E C' (Array RuntimeValue × MemoryState × Option ControlFlowAction)) :
  CTree.Sim (E := E) (C := FreezeC) (C' := C') f
    (CTree.bind
      (Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of RegisterType { }]
        #[RuntimeValue.byte bitwidth a] memory) after)
    other ↔
  ∀ (value : Data.RISCV.Reg),
    (∃ bits : BitVec bitwidth,
      value.val = (a.val ||| (a.poison &&& bits)).setWidth 64) →
    CTree.Sim (E := E) (C := FreezeC) (C' := C') f
      (after (#[.reg value], memory, none)) other := by
  by_cases h : a.poison = 0#bitwidth
  · simp [Builtin.interpretUnrealizedConversionCastCTree, Attribute.of_def,
      -Attribute.registerType_eq_of, h, LLVM.Byte.toReg]
    constructor
    · rintro hsim ⟨value⟩ rfl
      exact hsim
    · intro hsim
      exact hsim ⟨a.val.setWidth 64⟩ rfl
  · simp [Builtin.interpretUnrealizedConversionCastCTree, Attribute.of_def,
      -Attribute.registerType_eq_of, h]
    simp only [map_eq_pure_bind, CTree.choose_def, CTree.tau_def, Bind.bind,
      _root_.CTree.CTree.bind_tau, _root_.CTree.CTree.bind_ret, CTree.bind_pure, Sim.tau_l]
    simp
    constructor
    · rintro hsim ⟨value⟩ bits rfl
      exact hsim bits
    · intro hsim bits
      exact hsim ⟨a.val.setWidth 64 ||| (a.poison.setWidth 64 &&& bits.setWidth 64)⟩ bits rfl

/-- Casting a register to an integer deterministically resizes its bits. -/
@[ctree_semantics]
theorem CTree.Sim.bind_interpretUnrealizedConversionCastCTree_int_reg_iff
  {EIn : Type} {E : EIn → Type}
  [HasUB EIn] [ErrorE -< E] [UBE -< E]
  {C'In : Type} {C' : C'In → Type}
  (type : IntegerType) (a : Data.RISCV.Reg) (memory : MemoryState)
  (after : (Array RuntimeValue × MemoryState × Option ControlFlowAction) →
    CTree E FreezeC (Array RuntimeValue × MemoryState × Option ControlFlowAction))
  (other : CTree E C' (Array RuntimeValue × MemoryState × Option ControlFlowAction)) :
  CTree.Sim (E := E) (C := FreezeC) (C' := C') f
    (CTree.bind
      (Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of IntegerType type]
        #[RuntimeValue.reg a] memory) after)
    other ↔
  CTree.Sim (E := E) (C := FreezeC) (C' := C') f
    (after (#[.int type.bitwidth (.val (a.val.setWidth type.bitwidth))], memory, none))
    other := by
  simp [Builtin.interpretUnrealizedConversionCastCTree, Attribute.of_def,
    RISCV.Reg.toInt, -Attribute.integerType_eq_of]

/-- Casting a register to a byte deterministically resizes its bits and produces no poison. -/
@[ctree_semantics]
theorem CTree.Sim.bind_interpretUnrealizedConversionCastCTree_byte_reg_iff
  {EIn : Type} {E : EIn → Type}
  [HasUB EIn] [ErrorE -< E] [UBE -< E]
  {C'In : Type} {C' : C'In → Type}
  (type : LLVM.ByteType) (a : Data.RISCV.Reg) (memory : MemoryState)
  (after : (Array RuntimeValue × MemoryState × Option ControlFlowAction) →
    CTree E FreezeC (Array RuntimeValue × MemoryState × Option ControlFlowAction))
  (other : CTree E C' (Array RuntimeValue × MemoryState × Option ControlFlowAction)) :
  CTree.Sim (E := E) (C := FreezeC) (C' := C') f
    (CTree.bind
      (Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of LLVM.ByteType type]
        #[RuntimeValue.reg a] memory) after)
    other ↔
  CTree.Sim (E := E) (C := FreezeC) (C' := C') f
    (after (#[.byte type.bitwidth ⟨a.val.setWidth type.bitwidth, 0, by simp⟩], memory, none))
    other := by
  simp [Builtin.interpretUnrealizedConversionCastCTree, Attribute.of_def,
    RISCV.Reg.toByte, -Attribute.byteType_eq_of]

/-- Casting an address to a register preserves its bits; poison permits any register value. -/
@[ctree_semantics]
theorem CTree.Sim.bind_interpretUnrealizedConversionCastCTree_reg_addr_iff
  {EIn : Type} {E : EIn → Type}
  [HasUB EIn] [ErrorE -< E] [UBE -< E]
  {C'In : Type} {C' : C'In → Type}
  (a : Data.LLVM.Ptr) (memory : MemoryState)
  (after : (Array RuntimeValue × MemoryState × Option ControlFlowAction) →
    CTree E FreezeC (Array RuntimeValue × MemoryState × Option ControlFlowAction))
  (other : CTree E C' (Array RuntimeValue × MemoryState × Option ControlFlowAction)) :
  CTree.Sim (E := E) (C := FreezeC) (C' := C') f
    (CTree.bind
      (Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of RegisterType { }]
        #[RuntimeValue.addr a] memory) after)
    other ↔
  ∀ (value : Data.RISCV.Reg),
    (∀ bits, a.toInt = .val bits → value.val = bits) →
    CTree.Sim (E := E) (C := FreezeC) (C' := C') f
      (after (#[.reg value], memory, none)) other := by
  have hcast :
      Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of RegisterType { }]
        #[RuntimeValue.addr a] memory =
      Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of RegisterType { }]
        #[RuntimeValue.int 64 a.toInt] memory := by
    cases h : a.toInt <;>
      simp [Builtin.interpretUnrealizedConversionCastCTree, Attribute.of_def,
        -Attribute.registerType_eq_of, h]
  rw [hcast, CTree.Sim.bind_interpretUnrealizedConversionCastCTree_reg_int_iff]
  simp

/-- Casting a register to an address decodes its bits using the current memory state. -/
@[ctree_semantics]
theorem CTree.Sim.bind_interpretUnrealizedConversionCastCTree_addr_reg_iff
  {EIn : Type} {E : EIn → Type}
  [HasUB EIn] [ErrorE -< E] [UBE -< E]
  {C'In : Type} {C' : C'In → Type}
  (type : LLVM.PointerType) (a : Data.RISCV.Reg) (memory : MemoryState)
  (after : (Array RuntimeValue × MemoryState × Option ControlFlowAction) →
    CTree E FreezeC (Array RuntimeValue × MemoryState × Option ControlFlowAction))
  (other : CTree E C' (Array RuntimeValue × MemoryState × Option ControlFlowAction)) :
  CTree.Sim (E := E) (C := FreezeC) (C' := C') f
    (CTree.bind
      (Builtin.interpretUnrealizedConversionCastCTree (E := E) #[TypeAttr.of LLVM.PointerType type]
        #[RuntimeValue.reg a] memory) after)
    other ↔
  CTree.Sim (E := E) (C := FreezeC) (C' := C') f
    (after (#[.addr (memory.ptrFromInt (.val a.val))], memory, none)) other := by
  simp [Builtin.interpretUnrealizedConversionCastCTree, Attribute.of_def,
    -Attribute.llvmPointerType_eq_of]

/-- Expose the outcome of an `Interp` computation lifted into the left tree.
Successful results run `after`; UB and failure bypass it. -/
theorem CTree.Sim.bind_monadLift_iff {EIn : Type} {E : EIn → Type}
  [HasUB EIn] [ErrorE -< E] [UBE -< E]
  {CIn C'In : Type} {C : CIn → Type} {C' : C'In → Type}
  {α β γ : Type} (relation : β → γ → Prop) (func : Interp α)
  (after : α → CTree E C β) (other : CTree E C' γ) :
  CTree.Sim relation (CTree.bind (monadLift func) after) other ↔
    match func with
    | .ok value => CTree.Sim relation (after value) other
    | .ub _ => CTree.Sim relation (ub : CTree E C β) other
    | .fail _ => CTree.Sim relation (fail : CTree E C β) other := by
  exact sim_monadLift_bind_left relation other func after

/-- Expose the outcome of an `Interp` computation forming the entire right tree. -/
@[ctree_semantics]
theorem CTree.Sim.bind_monadLift_right_iff {EIn : Type} {E : EIn → Type}
  [HasUB EIn] [ErrorE -< E] [UBE -< E]
  {CIn C'In : Type} {C : CIn → Type} {C' : C'In → Type}
  {α β : Type} (relation : α → β → Prop)
  (other : CTree E C α) (func : Interp β) :
  CTree.Sim relation other (monadLift func : CTree E C' β) ↔
    match func with
    | .ok value => CTree.Sim relation other (pure value : CTree E C' β)
    | .ub _ => CTree.Sim relation other (ub : CTree E C' β)
    | .fail _ => CTree.Sim relation other (fail : CTree E C' β) := by
  cases func <;> rfl
