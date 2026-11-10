module

public import Veir.Interpreter.CTreeRefinement.Monotone
public import Veir.Dialects.GMIR.Monotonicity
public import Veir.Interpreter.CTreePrimitiveRefinement

import Veir.Dialects.ResultsConform
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Data.LLVM.Int.Basic

public section

/-!
# Monotonicity of the gMIR opcodes in CTrees

Every gMIR opcode but `g_anyext` and `g_load` runs its `Interp` semantics in CTrees, which is
monotone in its operands and its memory. `g_anyext` and `g_load` choose the high bits of their
result. The source chooses the same high bits as the target: the result of the source extends a
refined value, and so refines the result of the target, poison staying poison.
-/

open CTree
open Veir.Data

namespace Veir.CTree

/-- A gMIR opcode but `g_anyext` and `g_load` runs its `Interp` semantics. -/
theorem interpretOp'_gmir_of_lift {op : GMIR} (h₁ : op ≠ .g_anyext) (h₂ : op ≠ .g_load)
    (properties : propertiesOf (OpCode.gmir op)) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (blockOperands : Array BlockPtr) (mem : MemoryState)
    (regions : Array RegionPtr) :
    interpretOp' (.gmir op) properties resultTypes operands blockOperands mem regions =
      monadLift
        (Veir.interpretOp' (.gmir op) properties resultTypes operands blockOperands mem) := by
  cases op <;> simp_all [interpretOp', Veir.interpretOp', GMIR.interpretOpCTree]

/-- A refinement in `Interp` together with what holds of every result of the target. -/
private theorem Interp.isRefinedBy_and {R : α → β → Prop} {P : β → Prop} {s : Interp α}
    {t : Interp β} (h : Interp.isRefinedBy R s t) (hP : ∀ b, t = .ok b → P b) :
    Interp.isRefinedBy (fun a b => R a b ∧ P b) s t := by
  cases s <;> cases t <;> simp_all [Interp.isRefinedBy]

/-- The values that a single integer refines are a single integer. -/
private theorem toList_int1_of_isRefinedBy_target {a b : Array RuntimeValue} (h : a ⊒ b) {w : Nat}
    {x' : LLVM.Int w} (hb : b.toList = [.int w x']) :
    ∃ x, a.toList = [.int w x] ∧ _root_.isRefinedBy x x' := by
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

/--
What holds of the values of the target, `Q`, and is the same for all integers of a width: the
types of the values, or nothing.
-/
private def IntsAlike (Q : Array RuntimeValue → Prop) : Prop :=
  ∀ w (x y : LLVM.Int w), Q #[.int w x] → Q #[.int w y]

/-! ## `g_anyext` and `g_load` -/

/-- `g_anyext` is monotone in CTrees: the source extends with the high bits of the target. -/
private theorem sim_g_anyext {Q : Array RuntimeValue → Prop} (hQ : IntsAlike Q)
    (properties : propertiesOf (OpCode.gmir .g_anyext)) (resultTypes : Array TypeAttr)
    {operands operands' : Array RuntimeValue} (blockOperands : Array BlockPtr)
    {mem mem' : MemoryState} (regions : Array RegionPtr) (h : operands ⊒ operands')
    (hMem : mem ⊒ mem')
    (hTyped : ∀ vals m a, Veir.interpretOp' (.gmir .g_anyext) properties resultTypes operands'
      blockOperands mem' = .ok (vals, m, a) → Q vals) :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ Q t.1)
      (interpretOp' (.gmir .g_anyext) properties resultTypes operands' blockOperands mem' regions)
      (interpretOp' (.gmir .g_anyext) properties resultTypes operands blockOperands mem
        regions) := by
  rw [interpretOp'_regions, interpretOp'_regions]
  simp only [interpretOp', GMIR.interpretOpCTree]
  simp only [Veir.interpretOp', GMIR.interpretOp'] at hTyped
  rcases hs : operands.toList with _ | ⟨v, _ | ⟨_, _⟩⟩
  · simp
  rotate_left
  · simp
  obtain ⟨v', hs', hv⟩ := toList_eq_singleton_of_isRefinedBy h hs
  simp only [hs'] at hTyped ⊢
  cases v with
  | int w x =>
    obtain ⟨x', rfl, hx⟩ := RuntimeValue.int_of_isRefinedBy hv
    rcases hr : resultTypes[0]? with _ | resType
    · simp
    simp only [hr] at hTyped
    simp only
    rcases hT : resType.val <;> simp only [hT] at hTyped ⊢
    all_goals try simp
    rename_i resBw
    by_cases hw : resBw.bitwidth ≤ w
    · simp [hw]
    simp only [hw, ↓reduceDIte, CTree.tau_def] at hTyped ⊢
    refine (Sim.tau_l _ _ _ _).mpr fun msb => Sim.tau_r _ _ _ _ msb ?_
    refine (Sim.pure _ _ _).mpr ⟨OperationResult.isRefinedBy_def.mpr ⟨?_, hMem,
      ControlFlowAction.optionIsRefinedBy_refl _⟩, hQ _ _ _ (hTyped _ _ _ rfl)⟩
    simp only [RuntimeValue.singleton_isRefinedBy_iff, Array.mk.injEq, List.cons.injEq, and_true,
      exists_eq_left']
    exact RuntimeValue.int_isRefinedBy_of
      (Data.LLVM.Int.isRefinedBy_map (f := fun z => z.ext _ msb _) rfl hx)
  | _ => simp

/--
`g_load` is monotone in CTrees: its `Interp` semantics is, and the source chooses the high bits
of a wider result as the target does.
-/
private theorem sim_g_load {Q : Array RuntimeValue → Prop} (hQ : IntsAlike Q)
    (properties : propertiesOf (OpCode.gmir .g_load)) (resultTypes : Array TypeAttr)
    {operands operands' : Array RuntimeValue} (blockOperands : Array BlockPtr)
    {mem mem' : MemoryState} (regions : Array RegionPtr) (h : operands ⊒ operands')
    (hMem : mem ⊒ mem')
    (hTyped : ∀ vals m a, Veir.interpretOp' (.gmir .g_load) properties resultTypes operands'
      blockOperands mem' = .ok (vals, m, a) → Q vals) :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ Q t.1)
      (interpretOp' (.gmir .g_load) properties resultTypes operands' blockOperands mem' regions)
      (interpretOp' (.gmir .g_load) properties resultTypes operands blockOperands mem regions) := by
  rw [interpretOp'_regions, interpretOp'_regions]
  have hI := gmir_contextuallyMonotone_g_load.monotone properties resultTypes operands operands'
    blockOperands mem mem' h hMem
  simp only [interpretOp', GMIR.interpretOpCTree]
  simp only [Veir.interpretOp'] at hI hTyped
  generalize GMIR.interpretOp' .g_load properties resultTypes operands blockOperands mem = src
    at hI ⊢
  generalize GMIR.interpretOp' .g_load properties resultTypes operands' blockOperands mem' = tgt
    at hI hTyped ⊢
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
    have hQ' := hTyped _ _ _ rfl
    obtain ⟨hres, hm, ha⟩ := OperationResult.isRefinedBy_def.mp hr
    simp only [monadLift, MonadLift.monadLift, pure_bind]
    split
    · next w val' hT =>
      obtain ⟨val, hS, hval⟩ := toList_int1_of_isRefinedBy_target hres hT
      obtain rfl : res' = #[.int w val'] := List.eq_toArray_iff.mpr hT
      rw [hS]
      dsimp only
      by_cases hw : properties.size.toNat < w
      · simp only [hw, ↓reduceDIte, CTree.tau_def]
        refine (Sim.tau_l _ _ _ _).mpr fun msb => Sim.tau_r _ _ _ _ msb ?_
        refine (Sim.pure _ _ _).mpr ⟨OperationResult.isRefinedBy_def.mpr ⟨?_, hm, ha⟩,
          hQ _ _ _ hQ'⟩
        simp only [RuntimeValue.singleton_isRefinedBy_iff, Array.mk.injEq, List.cons.injEq,
          and_true, exists_eq_left']
        exact RuntimeValue.int_isRefinedBy_of (Data.LLVM.Int.isRefinedBy_map
          (f := fun z => (z.trunc _ false false hw).ext w msb hw) rfl hval)
      · simp only [hw, ↓reduceDIte]
        exact (Sim.pure _ _ _).mpr ⟨hr, hQ'⟩
    · next hT =>
      split
      · next w val hS =>
        obtain ⟨val', hT', -⟩ := RuntimeValue.toList_int1_of_isRefinedBy hres hS
        exact absurd hT' (hT _ _)
      · exact (Sim.pure _ _ _).mpr ⟨hr, hQ'⟩

/-! ## Every gMIR opcode -/

/--
A gMIR opcode is monotone in CTrees, with what holds of the `Interp` results of the target, `Q`,
holding of its CTree results.
-/
private theorem gmir_sim {op : GMIR} {Q : Array RuntimeValue → Prop} (hQ : IntsAlike Q)
    (properties : propertiesOf (OpCode.gmir op)) (resultTypes : Array TypeAttr)
    {operands operands' : Array RuntimeValue} (blockOperands : Array BlockPtr)
    {mem mem' : MemoryState} (regions : Array RegionPtr) (h : operands ⊒ operands')
    (hMem : mem ⊒ mem')
    (hTyped : ∀ vals m a, Veir.interpretOp' (.gmir op) properties resultTypes operands'
      blockOperands mem' = .ok (vals, m, a) → Q vals) :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ Q t.1)
      (interpretOp' (.gmir op) properties resultTypes operands' blockOperands mem' regions)
      (interpretOp' (.gmir op) properties resultTypes operands blockOperands mem regions) := by
  by_cases h₁ : op = .g_anyext
  · subst h₁; exact sim_g_anyext hQ _ _ _ _ h hMem hTyped
  by_cases h₂ : op = .g_load
  · subst h₂; exact sim_g_load hQ _ _ _ _ h hMem hTyped
  have := gmir_interpretOp'ContextuallyMonotone op
  rw [interpretOp'_gmir_of_lift h₁ h₂, interpretOp'_gmir_of_lift h₁ h₂]
  exact sim_monadLift_of_isRefinedBy (Interp.isRefinedBy_and
    (this.monotone properties resultTypes operands operands' blockOperands mem mem' h hMem)
    fun ⟨vals, m, a⟩ hok => hTyped vals m a hok)

/-- Every gMIR opcode is monotone in CTrees. -/
theorem gmir_interpretOpTreeMonotone (op : GMIR) : InterpretOpTreeMonotone (.gmir op) where
  monotone properties resultTypes operands operands' blockOperands mem mem' regions h hMem := by
    simpa using gmir_sim (Q := fun _ => True) (fun _ _ _ _ => trivial) properties resultTypes
      blockOperands regions h hMem fun _ _ _ _ => trivial

/-! ## With the types of the results -/

/-- A single result conforms as another single result of the same kind does. -/
private theorem arrayConforms_singleton {v v' : RuntimeValue} {types : Array TypeAttr}
    (h : RuntimeValue.ArrayConforms #[v] types) (hk : ∀ ty, v.Conforms ty → v'.Conforms ty) :
    RuntimeValue.ArrayConforms #[v'] types := by
  obtain ⟨hs, hc⟩ := h
  refine ⟨by simpa using hs, fun i hi => ?_⟩
  obtain rfl : i = 0 := by simp at hi; omega
  simpa using hk _ (by simpa using hc 0 (by simp))

/--
A gMIR opcode is monotone in CTrees, with the results of the target of the types that its
`Interp` results have.
-/
theorem gmir_sim_typed {op : GMIR} {opType : OpCode} (hType : opType = .gmir op)
    (properties : propertiesOf opType) (resultTypes types : Array TypeAttr)
    {operands operands' : Array RuntimeValue} (blockOperands : Array BlockPtr)
    {mem mem' : MemoryState} (regions : Array RegionPtr) (h : operands ⊒ operands')
    (hMem : mem ⊒ mem')
    (hTyped : ∀ vals m a, Veir.interpretOp' opType properties resultTypes operands' blockOperands
      mem' = .ok (vals, m, a) → RuntimeValue.ArrayConforms vals types) :
    Sim (fun t s => OperationResult.isRefinedBy s t ∧ RuntimeValue.ArrayConforms t.1 types)
      (interpretOp' opType properties resultTypes operands' blockOperands mem' regions)
      (interpretOp' opType properties resultTypes operands blockOperands mem regions) := by
  subst hType
  refine gmir_sim (fun _ _ _ hc => arrayConforms_singleton hc fun ty hc => ?_) properties
    resultTypes blockOperands regions h hMem hTyped
  obtain ⟨a, _⟩ := ty; cases a <;> exact hc

end Veir.CTree

namespace Veir

/--
Every gMIR opcode is monotone in CTrees, with the results of the target typed: the obligation of
`OpCode.interpretCTree_monotone` holds for gMIR. The types of the results come from
`interpretOp'_results_conform`.
-/
theorem OpCode.interpretCTree_monotone_gmir (op : GMIR) :
    OpCode.interpretCTree_monotone (.gmir op) := by
  intro ctx o oIn hType hVerified sv tv sm tm hConf hRef hMem
  simp only [OperationPtr.interpretCTree]
  refine CTree.gmir_sim_typed hType _ _ _ _ _ hRef hMem fun vals m a hok =>
    interpretOp'_results_conform (mem := tm) (mem' := m) (act := a) hVerified
      (hConf.of_isRefinedBy hRef) ?_
  simp only [OperationPtr.interpret]
  rw [OperationPtr.getOpType!_eq_getOpType oIn, OperationPtr.getProperties!_eq_getProperties oIn
    (by grind), OperationPtr.getResultTypes!_eq_getResultTypes oIn,
    OperationPtr.getSuccessors!_eq_getSuccessors oIn]
  exact hok

/--
info: 'Veir.OpCode.interpretCTree_monotone_gmir' depends on axioms: [propext,
 Sim,
 Classical.choice,
 Quot.sound,
 Sim.ret,
 Sim.tau_l,
 Sim.tau_r,
 Sim.ub,
 OpCode.resultsConform_assumed]
-/
#guard_msgs in
#print axioms OpCode.interpretCTree_monotone_gmir

instance (op : GMIR) : InterpretCTreeMonotone (.gmir op) :=
  ⟨OpCode.interpretCTree_monotone_gmir op⟩

end Veir

end
