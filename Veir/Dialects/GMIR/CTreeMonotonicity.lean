module

public import Veir.Interpreter.CTreeRefinement.Monotone
public import Veir.Dialects.GMIR.Monotonicity

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Data.LLVM.Int.Basic

public section

/-!
# Monotonicity of the gMIR opcodes in CTrees

Every gMIR opcode but `g_anyext`, `g_load` and `g_freeze` runs its `Interp` semantics in CTrees,
which is monotone in its operands and its memory. `g_anyext` and `g_load` choose the high bits of
their result: the source chooses the same high bits as the target, so the result of the source
extends a refined value, and refines the result of the target, poison staying poison. `g_freeze`
chooses what poison becomes, and so does any refinement of its operand. The types of the results
come from `ResultsConform`.
-/

open CTree
open Veir.Data

namespace Veir.CTree

/-- A gMIR opcode but `g_anyext`, `g_load` and `g_freeze` runs its `Interp` semantics. -/
theorem interpretOp'_gmir_of_lift {op : GMIR} (h₁ : op ≠ .g_anyext) (h₂ : op ≠ .g_load)
    (h₃ : op ≠ .g_freeze)
    (properties : propertiesOf (OpCode.gmir op)) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (blockOperands : Array BlockPtr) (mem : MemoryState)
    (regions : Array RegionPtr) :
    interpretOp' (.gmir op) properties resultTypes operands blockOperands mem regions =
      monadLift
        (Veir.interpretOp' (.gmir op) properties resultTypes operands blockOperands mem) := by
  cases op <;> simp_all [interpretOp', Veir.interpretOp', GMIR.interpretOpCTree]

/-- The values that a single integer refines are a single integer. -/
private theorem toList_int1_of_isRefinedBy_target {a b : Array RuntimeValue} (h : a ⊒ b) {w : Nat}
    {x' : LLVM.Int w} (hb : b.toList = [.int w x']) :
    ∃ x, a.toList = [.int w x] ∧ LLVM.Int.isRefinedBy x x' := by
  obtain rfl : b = #[.int w x'] := List.eq_toArray_iff.mpr hb
  have hsize : a.size = 1 := h.1
  obtain ⟨v, rfl⟩ : ∃ v, a = #[v] := by
    rcases a with ⟨_ | ⟨v, _ | _⟩⟩
    · simp at hsize
    · exact ⟨v, rfl⟩
    · simp at hsize
  obtain ⟨_, hw, hv⟩ := RuntimeValue.singleton_isRefinedBy_iff.mp h
  obtain rfl := (List.cons.inj (Array.mk.inj hw)).1
  cases v with
  | int w₁ x =>
    obtain ⟨x'', hx'', hx⟩ := RuntimeValue.int_of_isRefinedBy hv
    cases hx''
    exact ⟨x, rfl, hx⟩
  | _ => simp [RuntimeValue.isRefinedBy] at hv

/-- A tree that returns a result may return it. -/
private theorem mayReturn_pure {α : Type} (r : α) : MayReturn (pure r : Tree α) r :=
  (MayReturn.pure_iff _ _).mpr rfl

/-! ## `g_anyext` and `g_load` -/

/--
`g_anyext` is monotone in CTrees: the source extends with the high bits of the target, and the
result is of the types every result the target may return has.
-/
private theorem sim_g_anyext (properties : propertiesOf (OpCode.gmir .g_anyext))
    (resultTypes : Array TypeAttr) {operands operands' : Array RuntimeValue}
    (blockOperands : Array BlockPtr) {mem mem' : MemoryState} (regions : Array RegionPtr)
    (h : operands ⊒ operands') (hMem : mem ⊒ mem')
    (hT : ∀ vals m a, MayReturn
      (interpretOp' (.gmir .g_anyext) properties resultTypes operands' blockOperands mem' regions)
      (vals, m, a) → RuntimeValue.ArrayConforms vals resultTypes) :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ RuntimeValue.ArrayConforms t.1 resultTypes)
      (interpretOp' (.gmir .g_anyext) properties resultTypes operands' blockOperands mem' regions)
      (interpretOp' (.gmir .g_anyext) properties resultTypes operands blockOperands mem
        regions) := by
  rw [interpretOp'_regions, interpretOp'_regions] at hT ⊢
  simp only [interpretOp', GMIR.interpretOpCTree] at hT ⊢
  rcases hs : operands.toList with _ | ⟨v, _ | ⟨_, _⟩⟩
  · simp
  rotate_left
  · simp
  obtain ⟨v', hs', hv⟩ := toList_eq_singleton_of_isRefinedBy h hs
  simp only [hs'] at hT ⊢
  cases v with
  | int w x =>
    obtain ⟨x', rfl, hx⟩ := RuntimeValue.int_of_isRefinedBy hv
    rcases hr : resultTypes[0]? with _ | resType
    · simp
    simp only [hr] at hT ⊢
    rcases hTy : resType.val <;> simp only [hTy] at hT ⊢
    all_goals try simp
    rename_i resBw
    by_cases hw : resBw.bitwidth ≤ w
    · simp [hw]
    simp only [hw, ↓reduceDIte, CTree.tau_def] at hT ⊢
    refine (Sim.tau_l _ _ _ _).mpr fun msb => Sim.tau_r _ _ _ _ msb ?_
    refine (Sim.pure _ _ _).mpr ⟨OperationResult.isRefinedBy_def.mpr ⟨?_, hMem,
      ControlFlowAction.optionIsRefinedBy_refl _⟩,
      hT _ _ _ ((MayReturn.tauG_iff _ _ _).mpr ⟨msb, mayReturn_pure _⟩)⟩
    simp only [RuntimeValue.singleton_isRefinedBy_iff, Array.mk.injEq, List.cons.injEq, and_true,
      exists_eq_left']
    exact RuntimeValue.int_isRefinedBy_of
      (Data.LLVM.Int.isRefinedBy_map (f := fun z => z.ext _ msb _) rfl hx)
  | _ => simp

/--
`g_load` is monotone in CTrees: its `Interp` semantics is, and the source chooses the high bits
of a wider result as the target does. The result is of the types every result the target may
return has.
-/
private theorem sim_g_load (properties : propertiesOf (OpCode.gmir .g_load))
    (resultTypes : Array TypeAttr) {operands operands' : Array RuntimeValue}
    (blockOperands : Array BlockPtr) {mem mem' : MemoryState} (regions : Array RegionPtr)
    (h : operands ⊒ operands') (hMem : mem ⊒ mem')
    (hT : ∀ vals m a, MayReturn
      (interpretOp' (.gmir .g_load) properties resultTypes operands' blockOperands mem' regions)
      (vals, m, a) → RuntimeValue.ArrayConforms vals resultTypes) :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ RuntimeValue.ArrayConforms t.1 resultTypes)
      (interpretOp' (.gmir .g_load) properties resultTypes operands' blockOperands mem' regions)
      (interpretOp' (.gmir .g_load) properties resultTypes operands blockOperands mem regions) := by
  rw [interpretOp'_regions, interpretOp'_regions] at hT ⊢
  have hI := gmir_monotone_g_load.monotone properties resultTypes operands operands'
    blockOperands mem mem' h hMem
  simp only [interpretOp', GMIR.interpretOpCTree] at hT ⊢
  simp only [Veir.interpretOp'] at hI
  generalize GMIR.interpretOp' .g_load properties resultTypes operands blockOperands mem = src
    at hI ⊢
  generalize GMIR.interpretOp' .g_load properties resultTypes operands' blockOperands mem' = tgt
    at hI hT ⊢
  cases src with
  | ub _ =>
    simp only [monadLift, MonadLift.monadLift, tree_bind_eq, bind_ub]
    exact sim_ub _ _
  | fail _ =>
    simp only [monadLift, MonadLift.monadLift, tree_bind_eq, bind_fail]
    exact sim_fail _ _
  | ok r =>
    obtain ⟨r', rfl, hr⟩ := Interp.isRefinedBy_ok_target_iff.mp hI
    obtain ⟨res, m, a⟩ := r
    obtain ⟨res', m', a'⟩ := r'
    obtain ⟨hres, hm, ha⟩ := OperationResult.isRefinedBy_def.mp hr
    simp only [monadLift, MonadLift.monadLift, pure_bind] at hT ⊢
    split
    · next w val' hS' =>
      obtain ⟨val, hS, hval⟩ := toList_int1_of_isRefinedBy_target hres hS'
      obtain rfl : res' = #[.int w val'] := List.eq_toArray_iff.mpr hS'
      simp only at hT
      rw [hS]
      dsimp only
      by_cases hw : properties.size.toNat < w
      · simp only [hw, ↓reduceDIte, CTree.tau_def] at hT ⊢
        refine (Sim.tau_l _ _ _ _).mpr fun msb => Sim.tau_r _ _ _ _ msb ?_
        refine (Sim.pure _ _ _).mpr ⟨OperationResult.isRefinedBy_def.mpr ⟨?_, hm, ha⟩,
          hT _ _ _ ((MayReturn.tauG_iff _ _ _).mpr ⟨msb, mayReturn_pure _⟩)⟩
        simp only [RuntimeValue.singleton_isRefinedBy_iff, Array.mk.injEq, List.cons.injEq,
          and_true, exists_eq_left']
        exact RuntimeValue.int_isRefinedBy_of (Data.LLVM.Int.isRefinedBy_map
          (f := fun z => (z.trunc _ false false hw).ext w msb hw) rfl hval)
      · simp only [hw, ↓reduceDIte] at hT ⊢
        exact (Sim.pure _ _ _).mpr ⟨hr, hT _ _ _ (mayReturn_pure _)⟩
    · next hS' =>
      split
      · next w val hS =>
        obtain ⟨val', hT', -⟩ := RuntimeValue.toList_int1_of_isRefinedBy hres hS
        exact absurd hT' (hS' _ _)
      · split at hT
        · next w val' hS =>
          exact absurd hS (hS' _ _)
        · exact (Sim.pure _ _ _).mpr ⟨hr, hT _ _ _ (mayReturn_pure _)⟩

/-! ## `g_freeze` -/

/--
`g_freeze` is monotone in CTrees: where the source carries poison it chooses, and it chooses the
value the target froze to. The result is of the types every result the target may return has.

The `Interp` interpreter is not monotone here, as it replaces poison with a fixed value; the CTree
chooses instead, which is what makes the source able to follow the target.
-/
private theorem sim_g_freeze (properties : propertiesOf (OpCode.gmir .g_freeze))
    (resultTypes : Array TypeAttr) {operands operands' : Array RuntimeValue}
    (blockOperands : Array BlockPtr) {mem mem' : MemoryState} (regions : Array RegionPtr)
    (h : operands ⊒ operands') (hMem : mem ⊒ mem')
    (hT : ∀ vals m a, MayReturn
      (interpretOp' (.gmir .g_freeze) properties resultTypes operands' blockOperands mem' regions)
      (vals, m, a) → RuntimeValue.ArrayConforms vals resultTypes) :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ RuntimeValue.ArrayConforms t.1 resultTypes)
      (interpretOp' (.gmir .g_freeze) properties resultTypes operands' blockOperands mem' regions)
      (interpretOp' (.gmir .g_freeze) properties resultTypes operands blockOperands mem
        regions) := by
  rw [interpretOp'_regions, interpretOp'_regions] at hT ⊢
  simp only [interpretOp', GMIR.interpretOpCTree] at hT ⊢
  rcases hs : operands.toList with _ | ⟨v, _ | ⟨_, _⟩⟩
  · simp
  rotate_left
  · simp
  obtain ⟨v', hs', hv⟩ := toList_eq_singleton_of_isRefinedBy h hs
  simp only [hs'] at hT ⊢
  cases v with
  | int w x =>
    obtain ⟨x', rfl, hx⟩ := RuntimeValue.int_of_isRefinedBy hv
    cases x with
    | val a =>
      obtain rfl : x' = .val a := by
        have := RuntimeValue.int_val_isRefinedBy_iff.mp hv; simpa using this
      exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem (hT _ _ _ (mayReturn_pure _))
    | poison =>
      cases x' with
      | val a =>
        exact sim_choose_right _ a (sim_result (by simp [RuntimeValue.isRefinedBy]) hMem
          (hT _ _ _ (mayReturn_pure _)))
      | poison =>
        refine sim_choose_left _ fun bits => sim_choose_right _ bits ?_
        exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem
          (hT _ _ _ (mayReturn_choose_bind bits (mayReturn_pure _)))
  | _ => simp

end Veir.CTree

namespace Veir

/--
Every gMIR opcode whose results conform meets its CTree monotonicity obligation, `g_anyext`,
`g_load` and `g_freeze` by their own semantics.
-/
theorem OpCode.interpretCTree_monotone_gmir (op : GMIR) [Veir.ResultsConform (.gmir op)] :
    OpCode.interpretCTree_monotone (.gmir op) :=
  .of_sim fun properties resultTypes operands operands' blockOperands mem mem' regions h hMem
      hT => by
    by_cases h₁ : op = .g_anyext
    · subst h₁; exact CTree.sim_g_anyext properties resultTypes blockOperands regions h hMem hT
    by_cases h₂ : op = .g_load
    · subst h₂; exact CTree.sim_g_load properties resultTypes blockOperands regions h hMem hT
    by_cases h₃ : op = .g_freeze
    · subst h₃; exact CTree.sim_g_freeze properties resultTypes blockOperands regions h hMem hT
    have := gmir_interpretOp'Monotone h₃
    exact CTree.sim_of_lift
      (fun _ _ => CTree.interpretOp'_gmir_of_lift h₁ h₂ h₃ _ _ _ _ _ _) h hMem hT

instance (op : GMIR) [ResultsConform (.gmir op)] : InterpretCTreeMonotone (.gmir op) :=
  ⟨OpCode.interpretCTree_monotone_gmir op⟩

end Veir

end
