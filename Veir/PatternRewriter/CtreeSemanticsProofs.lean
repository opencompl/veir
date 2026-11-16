module

public import Veir.Dialects.Builtin.InterpreterLemmas
public import Veir.Data.Casting
import all Veir.Dialects.Builtin.Interpreter
import all Veir.Data.Casting

/-!
# The `ctree_semantics` simp set

  * the quantifier normalizations binding the type equations introduced by `TypeAttr` matchers and
    the bitwidth equations of integer types;
  * the simulation lemmas exposing the choice of a `CTree.choose`, of a lifted `Interp`
    computation, and of each `builtin.unrealized_conversion_cast` between values and registers;
  * the RISC-V CTree interpreter, which unfolds to the CTree loads and to the lifted basic
    interpreter.
-/

namespace Veir

open _root_.CTree

public section

/-- Bind a type equation introduced by a `TypeAttr` matcher. -/
@[simp, ctree_semantics]
theorem TypeAttr.forall_of_eq_imp_iff {T : Type} [IsTypeAttr T] {P : TypeAttr → T → Prop} :
    (∀ (type : TypeAttr) (x : T), TypeAttr.of T x = type → P type x) ↔
      (∀ (x : T), P (TypeAttr.of T x) x) := by
  grind

/-- Bind the bitwidth equation of an integer type, leaving its signedness free. -/
@[simp, ctree_semantics]
theorem IntegerType.forall_bitwidth_eq_implies_iff (P : IntegerType → Prop) :
    (∀ (x : IntegerType), x.bitwidth = y → P x) ↔
      ∀ signedness, P (IntegerType.mk y signedness) := by
  grind [cases IntegerType]

/-- Bind the properties of a `g_constant` to its integer attribute. -/
@[simp, ctree_semantics]
theorem forall_gmirConstantProperties (P : propertiesOf (OpCode.gmir GMIR.g_constant) → Prop) :
    (∀ (property : propertiesOf (OpCode.gmir GMIR.g_constant)), P property) ↔
      (∀ (value : IntegerAttr), P { value := value }) := by
  constructor
  · grind
  · intro h ⟨prop⟩
    grind

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

attribute [ctree_semantics]
  CTree.Sim.bind_interpretUnrealizedConversionCastCTree_reg_int_iff
  CTree.Sim.bind_interpretUnrealizedConversionCastCTree_reg_byte_iff
  CTree.Sim.bind_interpretUnrealizedConversionCastCTree_int_reg_iff
  CTree.Sim.bind_interpretUnrealizedConversionCastCTree_byte_reg_iff
  CTree.Sim.bind_interpretUnrealizedConversionCastCTree_reg_addr_iff
  CTree.Sim.bind_interpretUnrealizedConversionCastCTree_addr_reg_iff

end

end Veir
