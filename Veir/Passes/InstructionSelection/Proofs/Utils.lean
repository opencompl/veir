module

import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.Passes.InstructionSelection.Common
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.RISCV_Cf.OpInfo
import all Veir.Dialects.Builtin.OpInfo
import all Veir.GlobalOpInfo
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.Builtin.Interpreter
public import Veir.Dialects.Builtin.InterpreterLemmas
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

attribute [ctree_semantics]
  CTree.Sim.bind_interpretUnrealizedConversionCastCTree_reg_int_iff
  CTree.Sim.bind_interpretUnrealizedConversionCastCTree_int_reg_iff
  CTree.Sim.bind_interpretUnrealizedConversionCastCTree_byte_reg_iff
  CTree.Sim.bind_interpretUnrealizedConversionCastCTree_reg_addr_iff
  CTree.Sim.bind_interpretUnrealizedConversionCastCTree_addr_reg_iff

/-- Casting a byte to a register preserves defined bits and resolves poisoned bits before resizing:
`CTree.Sim.bind_interpretUnrealizedConversionCastCTree_reg_byte_iff`, quantified over the register. -/
@[ctree_semantics]
theorem CTree.Sim.bind_interpretUnrealizedConversionCastCTree_reg_byte_exists_iff
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
  rw [CTree.Sim.bind_interpretUnrealizedConversionCastCTree_reg_byte_iff]
  constructor
  · rintro h ⟨value⟩ ⟨bits, rfl⟩
    simpa [BitVec.setWidth_or, BitVec.setWidth_and] using h bits
  · intro h bits
    exact h _ ⟨bits, by simp [BitVec.setWidth_or, BitVec.setWidth_and]⟩

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
  exact Sim.bind_monadLift_left_iff relation other func after

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
