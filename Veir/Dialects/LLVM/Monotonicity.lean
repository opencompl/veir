module

public import Veir.Interpreter.Lemmas
public import Veir.Interpreter.Refinement.MonoTactic
public import Veir.Dialects.LLVM.MemoryMonotonicity
import Veir.Interpreter.Refinement.Memory
import Veir.Data.LLVM.Byte.Refinement

import all Veir.Interpreter.Basic
import all Veir.Interpreter.Memory
import all Veir.Interpreter.Refinement.Basic
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.Refinement
import all Veir.Interpreter.Interp

import Veir.Interpreter.Refinement.Lemmas

public section

/-!
# Monotonicity of the LLVM interpreter

An LLVM opcode is monotone in its operands when refining its operands refines its result.

Every LLVM opcode but `llvm.freeze` is monotone in its operands. The arithmetic is strict in
poison, `select` and the branches pick operands without looking at them, byte operations refine
bitwise (`Veir.Data.LLVM.Byte.Refinement`), and a `getelementptr` with a poison pointer or index
is poison. `llvm.freeze` chooses what poison becomes, which only its CTree semantics can.

With refined memory (`InterpretOp'ContextuallyMonotone`), the opcodes that do not touch memory
carry their monotonicity over (`llvm_frame`), `switch` is proved directly, and the opcodes that
load, store or allocate are proved in `Veir.Dialects.LLVM.MemoryMonotonicity`.
-/

open Veir.Data

namespace Veir

/-- Refinement of operation results with equal memories, as `InterpretOp'Monotone` asks. -/
private abbrev sameMemory (s t : Array RuntimeValue × MemoryState × Option ControlFlowAction) :
    Prop :=
  OperationResult.isRefinedBy s t ∧ s.2.1 = t.2.1

/--
A load is monotone: a poison pointer is undefined behavior and
a concrete one is refined only by itself.
-/
instance llvm_monotone_load : InterpretOp'Monotone (.llvm .load) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · split
      · next ptr hOps =>
        obtain rfl : operands = #[.addr (.val ptr)] := List.eq_toArray_iff.mpr hOps
        obtain ⟨w, rfl, hRef⟩ := RuntimeValue.singleton_isRefinedBy_iff.mp h
        obtain rfl := RuntimeValue.addr_val_isRefinedBy_iff.mp hRef
        exact Interp.isRefinedBy_refl_operationResult_sameMemory _
      · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

/-! ## Arithmetic -/

instance llvm_monotone_add : InterpretOp'Monotone (.llvm .add) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.add, LLVM.Int.cast]

instance llvm_monotone_sub : InterpretOp'Monotone (.llvm .sub) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.sub, LLVM.Int.cast]

instance llvm_monotone_mul : InterpretOp'Monotone (.llvm .mul) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.mul, LLVM.Int.cast]

instance llvm_monotone_sdiv : InterpretOp'Monotone (.llvm .sdiv) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [Llvm.interpretOp'] [LLVM.Int.sdiv, LLVM.Int.isSignedDivisionUB, LLVM.Int.cast]

instance llvm_monotone_udiv : InterpretOp'Monotone (.llvm .udiv) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [Llvm.interpretOp'] [LLVM.Int.udiv, LLVM.Int.isUnsignedDivisionUB, LLVM.Int.cast]

instance llvm_monotone_srem : InterpretOp'Monotone (.llvm .srem) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [Llvm.interpretOp'] [LLVM.Int.srem, LLVM.Int.isSignedDivisionUB, LLVM.Int.cast]

instance llvm_monotone_urem : InterpretOp'Monotone (.llvm .urem) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [Llvm.interpretOp'] [LLVM.Int.urem, LLVM.Int.isUnsignedDivisionUB, LLVM.Int.cast]

instance llvm_monotone_ashr : InterpretOp'Monotone (.llvm .ashr) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.ashr, LLVM.Int.cast]

instance llvm_monotone_intr__fshl : InterpretOp'Monotone (.llvm .intr__fshl) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.fshl, LLVM.Int.cast]

instance llvm_monotone_intr__fshr : InterpretOp'Monotone (.llvm .intr__fshr) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.fshr, LLVM.Int.cast]

instance llvm_monotone_intr__ctlz : InterpretOp'Monotone (.llvm .intr__ctlz) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.ctlz, LLVM.Int.cast]

instance llvm_monotone_intr__cttz : InterpretOp'Monotone (.llvm .intr__cttz) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.cttz, LLVM.Int.cast]

instance llvm_monotone_intr__ctpop : InterpretOp'Monotone (.llvm .intr__ctpop) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.ctpop, LLVM.Int.cast]

instance llvm_monotone_intr__bswap : InterpretOp'Monotone (.llvm .intr__bswap) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.bswap, LLVM.Int.cast]

instance llvm_monotone_intr__bitreverse : InterpretOp'Monotone (.llvm .intr__bitreverse) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.bitreverse, LLVM.Int.cast]

instance llvm_monotone_and : InterpretOp'Monotone (.llvm .and) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.and, LLVM.Int.cast]

instance llvm_monotone_or : InterpretOp'Monotone (.llvm .or) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.or, LLVM.Int.cast]

instance llvm_monotone_xor : InterpretOp'Monotone (.llvm .xor) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.xor, LLVM.Int.cast]

instance llvm_monotone_intr__smax : InterpretOp'Monotone (.llvm .intr__smax) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.smax, LLVM.Int.cast]

instance llvm_monotone_intr__smin : InterpretOp'Monotone (.llvm .intr__smin) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.smin, LLVM.Int.cast]

instance llvm_monotone_intr__umax : InterpretOp'Monotone (.llvm .intr__umax) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.umax, LLVM.Int.cast]

instance llvm_monotone_intr__umin : InterpretOp'Monotone (.llvm .intr__umin) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.umin, LLVM.Int.cast]

instance llvm_monotone_intr__abs : InterpretOp'Monotone (.llvm .intr__abs) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.abs, LLVM.Int.cast]

instance llvm_monotone_intr__sadd__sat : InterpretOp'Monotone (.llvm .intr__sadd__sat) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.saddSat, LLVM.Int.cast]

instance llvm_monotone_intr__uadd__sat : InterpretOp'Monotone (.llvm .intr__uadd__sat) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.uaddSat, LLVM.Int.cast]

instance llvm_monotone_intr__ssub__sat : InterpretOp'Monotone (.llvm .intr__ssub__sat) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.ssubSat, LLVM.Int.cast]

instance llvm_monotone_intr__usub__sat : InterpretOp'Monotone (.llvm .intr__usub__sat) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.usubSat, LLVM.Int.cast]

instance llvm_monotone_intr__sshl__sat : InterpretOp'Monotone (.llvm .intr__sshl__sat) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.sshlSat, LLVM.Int.cast]

instance llvm_monotone_intr__ushl__sat : InterpretOp'Monotone (.llvm .intr__ushl__sat) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.ushlSat, LLVM.Int.cast]

instance llvm_monotone_zext : InterpretOp'Monotone (.llvm .zext) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.zext, LLVM.Int.cast]

instance llvm_monotone_sext : InterpretOp'Monotone (.llvm .sext) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.sext, LLVM.Int.cast]

instance llvm_monotone_icmp : InterpretOp'Monotone (.llvm .icmp) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Int.icmp, LLVM.Int.cast]

instance llvm_monotone_inttoptr : InterpretOp'Monotone (.llvm .inttoptr) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [MemoryState.ptrFromInt, LLVM.Int.cast]

instance llvm_monotone_ptrtoint : InterpretOp'Monotone (.llvm .ptrtoint) where
  monotone _ _ _ _ _ _ _ := by op_mono [Llvm.interpretOp'] [LLVM.Ptr.toInt, LLVM.Int.cast]

/-! ## Constants, `select` and control flow -/

instance llvm_monotone_mlir__constant : InterpretOp'Monotone (.llvm .mlir__constant) where
  monotone _ _ _ _ _ _ _ := Interp.isRefinedBy_refl_operationResult_sameMemory _

instance llvm_monotone_mlir__poison : InterpretOp'Monotone (.llvm .mlir__poison) where
  monotone _ _ _ _ _ _ _ := Interp.isRefinedBy_refl_operationResult_sameMemory _

instance llvm_monotone_mlir__zero : InterpretOp'Monotone (.llvm .mlir__zero) where
  monotone _ _ _ _ _ _ _ := Interp.isRefinedBy_refl_operationResult_sameMemory _

instance llvm_monotone_unreachable : InterpretOp'Monotone (.llvm .unreachable) where
  monotone _ _ _ _ _ _ _ := by simp [interpretOp', Llvm.interpretOp', Interp.isRefinedBy]

instance llvm_monotone_return : InterpretOp'Monotone (.llvm .return) where
  monotone _ _ _ _ _ _ h := by
    simp [interpretOp', Llvm.interpretOp', OperationResult.isRefinedBy,
      ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy, h]

instance llvm_monotone_br : InterpretOp'Monotone (.llvm .br) where
  monotone _ _ _ _ _ _ h := by
    simp only [interpretOp', Llvm.interpretOp']
    split <;> simp [Interp.isRefinedBy, OperationResult.isRefinedBy,
      ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy, h]

/-- `select` picks an operand by a condition that is not poison, which the target shares. -/
instance llvm_monotone_select : InterpretOp'Monotone (.llvm .select) where
  monotone _ _ _ _ _ _ h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · rename_i heq
      obtain ⟨_, _, _, hT, h1, h2, h3⟩ := RuntimeValue.toList_int3_of_isRefinedBy h heq
      simp only [hT]
      split
      · simp [Interp.isRefinedBy]
      · rcases h1 with rfl | ⟨c, rfl, rfl⟩
        · simp [LLVM.Int.select, Id.run, Interp.isRefinedBy, OperationResult.isRefinedBy,
            ControlFlowAction.optionIsRefinedBy, RuntimeValue.isRefinedBy, _root_.isRefinedBy]
        · by_cases hc : c = 1#1
          · rcases h2 with rfl | ⟨_, rfl, rfl⟩ <;>
              simp [LLVM.Int.select, Id.run, hc, Interp.isRefinedBy, OperationResult.isRefinedBy,
                ControlFlowAction.optionIsRefinedBy, RuntimeValue.isRefinedBy, _root_.isRefinedBy]
          · rcases h3 with rfl | ⟨_, rfl, rfl⟩ <;>
              simp [LLVM.Int.select, Id.run, hc, LLVM.Int.cast, Interp.isRefinedBy,
                OperationResult.isRefinedBy, ControlFlowAction.optionIsRefinedBy,
                RuntimeValue.isRefinedBy, _root_.isRefinedBy]
    · simp [Interp.isRefinedBy]

/-- `cond_br` on poison is undefined behavior; on a value, which the target shares, it passes on
a slice of its operands. -/
instance llvm_monotone_cond_br : InterpretOp'Monotone (.llvm .cond_br) where
  monotone _ _ _ _ _ _ h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · split
      · next condVal heq =>
        obtain ⟨v', h0, hv⟩ := RuntimeValue.getElem?_of_arrayIsRefinedBy h heq
        simp only [h0]
        split
        · split
          · next c =>
            obtain rfl := RuntimeValue.int_val_isRefinedBy_iff.mp hv
            split <;> rename_i hc <;> simp [hc, Interp.isRefinedBy, OperationResult.isRefinedBy,
              ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy,
              RuntimeValue.arrayIsRefinedBy_extract h, RuntimeValue.arrayIsRefinedBy_extract_size h]
          · simp [Interp.isRefinedBy]
          · simp [Interp.isRefinedBy]
        · simp [Interp.isRefinedBy]
      · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

instance llvm_monotone_switch : InterpretOp'Monotone (.llvm .switch) where
  monotone _ _ _ _ _ _ h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · split
      · next value heq =>
        obtain ⟨v', h0, hv⟩ := RuntimeValue.getElem?_of_arrayIsRefinedBy h heq
        simp only [h0]
        split
        · split
          · split
            · simp [Interp.isRefinedBy]
            · split
              · next bw v =>
                obtain rfl := RuntimeValue.int_val_isRefinedBy_iff.mp hv
                simp only
                refine Interp.isRefinedBy_bind
                  (R := fun (s s' : Option (Array RuntimeValue × MemoryState ×
                      Option ControlFlowAction) × Nat) => s.2 = s'.2 ∧
                    ((s.1 = none ∧ s'.1 = none) ∨
                      ∃ a a', s.1 = some a ∧ s'.1 = some a' ∧ sameMemory a a'))
                  (Interp.forIn_range_isRefinedBy _ _ _ _ (fun i b b' hb => ?_) _ _ (by simp)) ?_
                · obtain ⟨hsnd, -⟩ := hb
                  rw [hsnd]
                  split
                  · split
                    · split
                      · simp only [Interp.pure_eq, Interp.isRefinedBy_ok_ok, ForInStep.rel_done]
                        refine ⟨by simp, .inr ⟨_, _, rfl, rfl, ?_⟩⟩
                        simp [sameMemory, OperationResult.isRefinedBy,
                          ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy,
                          RuntimeValue.arrayIsRefinedBy_extract h]
                      · simp [Interp.isRefinedBy, Bind.bind]
                    · simp [Interp.isRefinedBy]
                  · simp [Interp.isRefinedBy, Bind.bind]
                · rintro ⟨r, base⟩ ⟨r', base'⟩ ⟨rfl, hr⟩
                  rcases hr with ⟨rfl, rfl⟩ | ⟨a, a', rfl, rfl, ha⟩
                  · simp [Interp.isRefinedBy, OperationResult.isRefinedBy,
                      ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy,
                      RuntimeValue.arrayIsRefinedBy_extract h]
                  · simpa [Interp.isRefinedBy] using ha
              · simp [Interp.isRefinedBy]
              · simp [Interp.isRefinedBy]
          · simp [Interp.isRefinedBy]
        · simp [Interp.isRefinedBy]
      · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

/-! ## `getelementptr`, shifts, truncation and casts -/

/-- A dynamic index of a GEP, read from refined operands: the same stride, and the same value
unless it is poison. -/
private theorem gepIndex_isRefinedBy {operands operands' : Array RuntimeValue}
    (h : operands ⊒ operands') {e : Option Nat × Nat} {r : Option Int × Nat}
    (hr : Llvm.gepIndex operands e = some r) :
    ∃ r', Llvm.gepIndex operands' e = some r' ∧
      ∀ x, (r.1.map (· * (r.2 : Int))) = some x → (r'.1.map (· * (r'.2 : Int))) = some x := by
  have hv : Llvm.gepOperand operands e.1 ⊒ Llvm.gepOperand operands' e.1 := by
    rcases e with ⟨_ | i, s⟩
    · exact RuntimeValue.isRefinedBy_refl _
    · exact RuntimeValue.getElem!_of_arrayIsRefinedBy
        (RuntimeValue.arrayIsRefinedBy_extract_size h 1) i
  simp only [Llvm.gepIndex] at hr ⊢
  revert hr hv
  generalize Llvm.gepOperand operands e.1 = v
  generalize Llvm.gepOperand operands' e.1 = v'
  intro hr hv
  cases v with
  | int w x =>
    obtain ⟨x', rfl, hx⟩ := RuntimeValue.int_isRefinedBy_iff.mp hv
    rcases hx with rfl | ⟨c, rfl, rfl⟩
    · simp only [Option.some.injEq] at hr
      subst hr
      cases x' <;> simp
    · simp only [Option.some.injEq] at hr
      subst hr
      exact ⟨_, rfl, fun x h => h⟩
  | _ => simp at hr

/-- Reading the dynamic indices of a GEP from refined operands. -/
private theorem gepIndices_isRefinedBy {operands operands' : Array RuntimeValue}
    (h : operands ⊒ operands') :
    ∀ (l : List (Option Nat × Nat)) (is : List (Option Int × Nat)),
      l.mapM (Llvm.gepIndex operands) = some is →
      ∃ is', l.mapM (Llvm.gepIndex operands') = some is' ∧
        ∀ ss, is.mapM (fun (idx, stride) => idx.map (· * (stride : Int))) = some ss →
          is'.mapM (fun (idx, stride) => idx.map (· * (stride : Int))) = some ss
  | [], is, hl => by
    simp at hl; subst hl; exact ⟨[], by simp, fun ss h => h⟩
  | e :: l, is, hl => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at hl
    obtain ⟨r, hr, rs, hrs, rfl⟩ := hl
    obtain ⟨r', hr', hsc⟩ := gepIndex_isRefinedBy h hr
    obtain ⟨rs', hrs', hscs⟩ := gepIndices_isRefinedBy h l rs hrs
    refine ⟨r' :: rs', by simp [List.mapM_cons, hr', hrs'], fun ss hss => ?_⟩
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hss ⊢
    obtain ⟨x, hx, xs, hxs, rfl⟩ := hss
    rcases r with ⟨i, s⟩
    rcases r' with ⟨i', s'⟩
    exact ⟨x, hsc x hx, xs, hscs xs hxs, rfl⟩

/-- A GEP of a poison pointer, or with a poison index, is poison. Otherwise the target reads the
same pointer and the same indices. -/
instance llvm_monotone_getelementptr : InterpretOp'Monotone (.llvm .getelementptr) where
  monotone _ _ operands operands' _ _ h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next ptr rest heq =>
      obtain ⟨y, ys, hT, hy⟩ : ∃ y ys, operands'.toList = y :: ys ∧ RuntimeValue.addr ptr ⊒ y := by
        have h' := h
        rw [← Array.toArray_toList (xs := operands), ← Array.toArray_toList (xs := operands'),
          heq] at h'
        obtain ⟨y, ys, hys, hy, -⟩ := RuntimeValue.cons_isRefinedBy_iff.mp h'
        exact ⟨y, ys, hys, hy⟩
      obtain ⟨ptr', rfl, hp⟩ := RuntimeValue.addr_isRefinedBy_iff.mp hy
      simp only [hT, ← h.1]
      rcases DataLayout.riscv64.gepOffsets _ _ with _ | ⟨offset, dynamic⟩
      · simp [Interp.isRefinedBy, Bind.bind]
      simp only [liftM, monadLift, MonadLift.monadLift, Bind.bind]
      rcases hi : Array.mapM (Llvm.gepIndex operands) dynamic with _ | indices
      · simp [Interp.isRefinedBy]
      have hl : dynamic.toList.mapM (Llvm.gepIndex operands) = some indices.toList := by
        rw [Array.mapM_eq_mapM_toList] at hi
        revert hi
        cases dynamic.toList.mapM (Llvm.gepIndex operands) <;> simp
        intro h; subst h; simp
      obtain ⟨is', hl', hsc⟩ := gepIndices_isRefinedBy h _ _ hl
      have hi' : Array.mapM (Llvm.gepIndex operands') dynamic = some is'.toArray := by
        rw [Array.mapM_eq_mapM_toList, hl']; rfl
      simp only [hi']
      /- Every outcome of the target is a pointer, which refines a poison pointer. -/
      have hPoison : ∀ (r : Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction)),
          (∃ p, r = pure (#[RuntimeValue.addr p], ‹MemoryState›, none)) →
          Interp.isRefinedBy sameMemory
            (pure (#[RuntimeValue.addr .poison], ‹MemoryState›, none)) r := by
        rintro r ⟨p, rfl⟩
        simp [Interp.isRefinedBy, sameMemory, OperationResult.isRefinedBy, RuntimeValue.isRefinedBy,
          ControlFlowAction.optionIsRefinedBy, LLVM.Ptr.isRefinedBy]
      rcases hp with rfl | ⟨q, rfl, rfl⟩
      · apply hPoison
        (repeat' split) <;> exact ⟨_, rfl⟩
      all_goals
      simp only
      split
      · next scaled hs =>
        have hsl : indices.toList.mapM
            (fun (idx, stride) => idx.map (· * (stride : Int))) = some scaled.toList := by
          rw [Array.mapM_eq_mapM_toList] at hs
          revert hs
          cases indices.toList.mapM (fun (idx, stride) => idx.map (· * (stride : Int))) <;> simp
          intro h; subst h; simp
        have hs' : Array.mapM (fun x => Option.map (fun x_1 => x_1 * (x.snd : Int)) x.fst)
            is'.toArray = some scaled := by
          rw [List.mapM_toArray, hsc _ hsl]; rfl
        simp only [hs']
        exact Interp.isRefinedBy_refl_operationResult_sameMemory _
      · apply hPoison
        (repeat' split) <;> exact ⟨_, rfl⟩
    · simp [Interp.isRefinedBy]

private theorem int_cast_isRefinedBy {w w' : Nat} {x x' : LLVM.Int w} (h : isRefinedBy x x')
    (hw : w = w') : isRefinedBy (x.cast hw) (x'.cast hw) := by
  subst hw
  cases x <;> cases x' <;> simp_all [isRefinedBy, LLVM.Int.cast]

/-- A single result, refined, with the memory and no control flow. -/
private theorem result_isRefinedBy {v v' : RuntimeValue} (h : v ⊒ v') (mem : MemoryState) :
    Interp.isRefinedBy sameMemory (pure (#[v], mem, none)) (pure (#[v'], mem, none)) := by
  simp [Interp.isRefinedBy, sameMemory, OperationResult.isRefinedBy,
    ControlFlowAction.optionIsRefinedBy, h]

/-- `shl` of an integer is monotone as the integer operations are; of a byte, bitwise. -/
instance llvm_monotone_shl : InterpretOp'Monotone (.llvm .shl) where
  monotone _ _ _ _ _ _ h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next lhs bw' rhs heq =>
      obtain ⟨l', r', hT, hl, hr⟩ := RuntimeValue.toList_pair_of_isRefinedBy h heq
      obtain ⟨rhs', rfl, hrhs⟩ := RuntimeValue.int_isRefinedBy_iff.mp hr
      simp only [hT]
      cases lhs with
      | int bw x =>
        obtain ⟨x', rfl, hx⟩ := RuntimeValue.int_isRefinedBy_iff.mp hl
        simp only
        rcases hx with rfl | ⟨_, rfl, rfl⟩ <;> rcases hrhs with rfl | ⟨_, rfl, rfl⟩ <;>
          first
            | exact Interp.isRefinedBy_refl_operationResult_sameMemory _
            | op_mono_finish [LLVM.Int.shl, LLVM.Int.cast]
      | byte bw b =>
        obtain ⟨b', rfl, hb⟩ := RuntimeValue.byte_of_isRefinedBy hl
        simp only
        split
        · simp [Interp.isRefinedBy]
        · split
          · simp [Interp.isRefinedBy]
          · refine result_isRefinedBy ?_ _
            exact RuntimeValue.byte_isRefinedBy_byte.mpr (LLVM.Byte.shl_isRefinedBy hb
              (int_cast_isRefinedBy (by rcases hrhs with rfl | ⟨_, rfl, rfl⟩ <;> simp [isRefinedBy])
              _) _)
      | _ => simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

/-- `lshr` of an integer is monotone as the integer operations are; of a byte, bitwise. -/
instance llvm_monotone_lshr : InterpretOp'Monotone (.llvm .lshr) where
  monotone _ _ _ _ _ _ h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next lhs bw' rhs heq =>
      obtain ⟨l', r', hT, hl, hr⟩ := RuntimeValue.toList_pair_of_isRefinedBy h heq
      obtain ⟨rhs', rfl, hrhs⟩ := RuntimeValue.int_isRefinedBy_iff.mp hr
      simp only [hT]
      cases lhs with
      | int bw x =>
        obtain ⟨x', rfl, hx⟩ := RuntimeValue.int_isRefinedBy_iff.mp hl
        simp only
        rcases hx with rfl | ⟨_, rfl, rfl⟩ <;> rcases hrhs with rfl | ⟨_, rfl, rfl⟩ <;>
          first
            | exact Interp.isRefinedBy_refl_operationResult_sameMemory _
            | op_mono_finish [LLVM.Int.lshr, LLVM.Int.cast]
      | byte bw b =>
        obtain ⟨b', rfl, hb⟩ := RuntimeValue.byte_of_isRefinedBy hl
        simp only
        split
        · simp [Interp.isRefinedBy]
        · exact result_isRefinedBy (RuntimeValue.byte_isRefinedBy_byte.mpr
            (LLVM.Byte.lshr_isRefinedBy hb (int_cast_isRefinedBy
              (by rcases hrhs with rfl | ⟨_, rfl, rfl⟩ <;> simp [isRefinedBy]) _) _)) _
      | _ => simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

/-- `trunc` of an integer is monotone as the integer operations are; of a byte, bitwise. -/
instance llvm_monotone_trunc : InterpretOp'Monotone (.llvm .trunc) where
  monotone _ _ _ _ _ _ h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next v heq =>
      obtain ⟨v', hT, hv⟩ := RuntimeValue.toList_single_of_isRefinedBy h heq
      simp only [hT]
      split
      · cases v with
        | int w x =>
          obtain ⟨x', rfl, hx⟩ := RuntimeValue.int_isRefinedBy_iff.mp hv
          simp only
          rcases hx with rfl | ⟨_, rfl, rfl⟩ <;>
            first
              | exact Interp.isRefinedBy_refl_operationResult_sameMemory _
              | op_mono_finish [LLVM.Int.trunc]
        | byte w b =>
          obtain ⟨b', rfl, hb⟩ := RuntimeValue.byte_of_isRefinedBy hv
          simp only
          split
          · split
            · simp [Interp.isRefinedBy]
            · exact result_isRefinedBy (RuntimeValue.byte_isRefinedBy_byte.mpr
                (LLVM.Byte.trunc_isRefinedBy hb _)) _
          · simp [Interp.isRefinedBy]
        | _ => simp [Interp.isRefinedBy]
      · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

/-- The pointer at an integer address: poison for poison. -/
private theorem ptrFromInt_isRefinedBy {mem : MemoryState} {x x' : LLVM.Int 64}
    (h : isRefinedBy x x') :
    RuntimeValue.addr (mem.ptrFromInt x) ⊒ RuntimeValue.addr (mem.ptrFromInt x') := by
  cases x <;> cases x' <;> simp_all [isRefinedBy, MemoryState.ptrFromInt, RuntimeValue.isRefinedBy,
    LLVM.Ptr.isRefinedBy]

/-- A bitcast of a refined value refines. -/
private theorem bitcastValue_isRefinedBy {mem : MemoryState} {v v' : RuntimeValue} (hv : v ⊒ v')
    (t : Attribute) :
    Interp.isRefinedBy (fun (a b : RuntimeValue) => a ⊒ b) (Llvm.bitcastValue mem v t)
      (Llvm.bitcastValue mem v' t) := by
  cases v with
  | int w x =>
    obtain ⟨x', rfl, hx⟩ := RuntimeValue.int_of_isRefinedBy hv
    cases t <;> simp only [Llvm.bitcastValue] <;> (try split) <;>
      simp [hv, RuntimeValue.byte_isRefinedBy_byte, LLVM.Byte.fromInt_isRefinedBy hx]
  | byte w b =>
    obtain ⟨b', rfl, hb⟩ := RuntimeValue.byte_of_isRefinedBy hv
    cases t <;> simp only [Llvm.bitcastValue] <;> (try split) <;>
      simp [RuntimeValue.isRefinedBy, LLVM.Byte.toInt_isRefinedBy hb, hb]
    next h =>
      subst h
      simpa [RuntimeValue.isRefinedBy] using
        ptrFromInt_isRefinedBy (mem := mem) (LLVM.Byte.toInt_isRefinedBy hb)
  | addr p =>
    cases v' <;> simp only [RuntimeValue.isRefinedBy] at hv
    cases t <;> simp only [Llvm.bitcastValue] <;> (try split) <;>
      simp [RuntimeValue.isRefinedBy,
        Data.LLVM.Ptr.toByte_isRefinedBy hv]
    simpa using hv
  | _ => simp [Llvm.bitcastValue]

/-- `bitcast` reinterprets its operand, which is monotone for each pair of types. -/
instance llvm_monotone_bitcast : InterpretOp'Monotone (.llvm .bitcast) where
  monotone _ _ _ _ _ mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next v heq =>
      obtain ⟨v', hT, hv⟩ := RuntimeValue.toList_single_of_isRefinedBy h heq
      simp only [hT]
      split
      · exact Interp.isRefinedBy_bind (bitcastValue_isRefinedBy hv _)
          fun a b hab => result_isRefinedBy hab mem
      · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

/-! ## Refined memory -/

/-- The LLVM opcodes whose interpretation reads or writes memory, or loops. -/
def Llvm.touchesMemory : Llvm → Bool
  | .load | .store | .alloca | .intr__memset | .intr__memcpy | .intr__memmove | .mlir__addressof
  | .switch => true
  | _ => false

set_option maxHeartbeats 4000000 in
/--
An LLVM opcode that does not touch memory returns the memory it is given, and reads only its
objects.
-/
theorem llvm_frame {opType : Llvm} (h : opType.touchesMemory = false)
    (properties : propertiesOf (OpCode.llvm opType)) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (blockOperands : Array BlockPtr) (mem mem' : MemoryState)
    (hObjects : mem.objects = mem'.objects) :
    interpretOp' (.llvm opType) properties resultTypes operands blockOperands mem' =
      (interpretOp' (.llvm opType) properties resultTypes operands blockOperands mem).map
        (fun r => (r.1, mem', r.2.2)) := by
  cases opType <;> simp [Llvm.touchesMemory] at h <;>
    simp only [interpretOp', Llvm.interpretOp', Llvm.bitcastValue] <;>
    (repeat' split) <;>
    simp [Interp.pure_eq, liftM, monadLift, MonadLift.monadLift, Bind.bind,
      MemoryState.ptrFromInt_eq_of_objects hObjects] <;>
    first | rfl | ((repeat' split) <;> simp [Interp.map])

/-- `switch` passes on slices of its operands and the memory it is given. -/
instance llvm_contextuallyMonotone_switch : InterpretOp'ContextuallyMonotone (.llvm .switch) where
  monotone _ _ _ _ _ _ _ h hMem := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · split
      · next value heq =>
        obtain ⟨v', h0, hv⟩ := RuntimeValue.getElem?_of_arrayIsRefinedBy h heq
        simp only [h0]
        split
        · split
          · split
            · simp [Interp.isRefinedBy]
            · split
              · next bw v =>
                obtain rfl := RuntimeValue.int_val_isRefinedBy_iff.mp hv
                simp only
                refine Interp.isRefinedBy_bind
                  (R := fun (s s' : Option (Array RuntimeValue × MemoryState ×
                      Option ControlFlowAction) × Nat) => s.2 = s'.2 ∧
                    ((s.1 = none ∧ s'.1 = none) ∨
                      ∃ a a', s.1 = some a ∧ s'.1 = some a' ∧
                        OperationResult.isRefinedBy a a'))
                  (Interp.forIn_range_isRefinedBy _ _ _ _ (fun i b b' hb => ?_) _ _ (by simp)) ?_
                · obtain ⟨hsnd, -⟩ := hb
                  rw [hsnd]
                  split
                  · split
                    · split
                      · simp only [Interp.pure_eq, Interp.isRefinedBy_ok_ok, ForInStep.rel_done]
                        refine ⟨by simp, .inr ⟨_, _, rfl, rfl, ?_⟩⟩
                        exact OperationResult.isRefinedBy_def.mpr
                          ⟨by simp, hMem, by simp [ControlFlowAction.optionIsRefinedBy,
                            ControlFlowAction.isRefinedBy, RuntimeValue.arrayIsRefinedBy_extract h]⟩
                      · simp [Interp.isRefinedBy, Bind.bind]
                    · simp [Interp.isRefinedBy]
                  · simp [Interp.isRefinedBy, Bind.bind]
                · rintro ⟨r, base⟩ ⟨r', base'⟩ ⟨rfl, hr⟩
                  rcases hr with ⟨rfl, rfl⟩ | ⟨a, a', rfl, rfl, ha⟩
                  · simp only [Interp.pure_eq, Interp.isRefinedBy_ok_ok]
                    exact OperationResult.isRefinedBy_def.mpr
                      ⟨by simp, hMem, by simp [ControlFlowAction.optionIsRefinedBy,
                        ControlFlowAction.isRefinedBy, RuntimeValue.arrayIsRefinedBy_extract h]⟩
                  · simpa [Interp.isRefinedBy] using ha
              · simp [Interp.isRefinedBy]
              · simp [Interp.isRefinedBy]
          · simp [Interp.isRefinedBy]
        · simp [Interp.isRefinedBy]
      · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

/--
Every LLVM opcode but `freeze` and those that touch memory is monotone in its operands. The
opcodes the interpreter does not know fail.
-/
theorem llvm_interpretOp'Monotone_of_touchesMemory_eq_false {opType : Llvm}
    (h : opType.touchesMemory = false) (hFreeze : opType ≠ .freeze) :
    InterpretOp'Monotone (.llvm opType) := by
  cases opType <;> simp [Llvm.touchesMemory] at h <;>
    first
      | exact absurd rfl hFreeze
      | infer_instance
      | exact ⟨fun _ _ _ _ _ _ _ => by simp [interpretOp', Llvm.interpretOp', Interp.isRefinedBy]⟩

/-- Every LLVM opcode but `freeze` is monotone in its operands and its memory. -/
theorem llvm_interpretOp'ContextuallyMonotone {opType : Llvm} (hFreeze : opType ≠ .freeze) :
    InterpretOp'ContextuallyMonotone (.llvm opType) := by
  cases hT : opType.touchesMemory
  · have := llvm_interpretOp'Monotone_of_touchesMemory_eq_false hT hFreeze
    exact .of_frame fun _ _ _ _ _ _ hObjects => llvm_frame hT _ _ _ _ _ _ hObjects
  · cases opType <;> simp [Llvm.touchesMemory] at hT <;> infer_instance

/--
`llvm.intr.memcpy` is monotone: a poison length or pointer is undefined behavior, and a copy
through refinements of its pointers copies the same.
-/
instance llvm_monotone_intr__memcpy : InterpretOp'Monotone (.llvm .intr__memcpy) where
  monotone props resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next dst src w len heq =>
      obtain ⟨a', b', l', hT, ha, hb, hl⟩ := RuntimeValue.toList_triple_of_isRefinedBy h heq
      obtain ⟨d', rfl, hd⟩ := RuntimeValue.addr_isRefinedBy_iff.mp ha
      obtain ⟨s', rfl, hs⟩ := RuntimeValue.addr_isRefinedBy_iff.mp hb
      obtain ⟨l', rfl, hlen⟩ := RuntimeValue.int_isRefinedBy_iff.mp hl
      simp only [hT]
      rcases hlen with rfl | ⟨c, rfl, rfl⟩
      · simp [Interp.isRefinedBy]
      dsimp only
      split
      · exact Interp.isRefinedBy_refl_operationResult_sameMemory _
      rcases hd with rfl | ⟨p, rfl, hp⟩
      · simp [Interp.isRefinedBy]
      rcases hs with rfl | ⟨q, rfl, hq⟩
      · simp [Interp.isRefinedBy]
      obtain ⟨p', rfl, hp'⟩ : ∃ p', d' = .val p' ∧ p ⊒ p' := by
        rcases hp with rfl | rfl <;> exact ⟨_, rfl, by simp⟩
      obtain ⟨q', rfl, hq'⟩ : ∃ q', s' = .val q' ∧ q ⊒ q' := by
        rcases hq with rfl | rfl <;> exact ⟨_, rfl, by simp⟩
      simp only [ite_true]
      refine Interp.isRefinedBy_trans_eq (Interp.isRefinedBy_refl_operationResult_sameMemory _) ?_
      exact Interp.isRefinedBy_eq_bind_left (Interp.isRefinedBy_eq_of_ok fun _ =>
        MemoryState.memcpy_of_isRefinedBy_of_ok hp' hq') _
    · simp [Interp.isRefinedBy]

end Veir

end
