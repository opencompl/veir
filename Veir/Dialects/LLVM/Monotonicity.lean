module

public import Veir.Interpreter.Lemmas
public import Veir.Interpreter.Refinement.MonoTactic
public import Veir.Dialects.LLVM.MemoryMonotonicity
import Veir.Interpreter.Refinement.Memory
import Veir.Data.LLVM.Byte.Lemmas

import all Veir.Interpreter.Basic
import all Veir.Interpreter.Memory
import all Veir.Interpreter.Refinement.Basic
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Interpreter.Interp

import Veir.Interpreter.Refinement.Lemmas

public section

/-!
# Monotonicity of the LLVM interpreter

An LLVM opcode is monotone when refining its operands and its memory refines its result.

Every LLVM opcode but `llvm.freeze` is monotone. The arithmetic is strict in poison, `select` and
the branches pick operands without looking at them, byte operations refine bitwise
(`Veir.Data.LLVM.Byte.Lemmas`), a `getelementptr` with a poison pointer or index is poison, and
the opcodes that store, allocate or copy are proved in `Veir.Dialects.LLVM.MemoryMonotonicity`.
`llvm.freeze` chooses what poison becomes, which only its CTree semantics can.
-/

open Veir.Data

namespace Veir

/--
`llvm.load` is monotone: a poison pointer is undefined behavior, and a load through a pointer
from refined memory gives a refined value.
-/
instance llvm_monotone_load : InterpretOp'Monotone (.llvm .load) where
  monotone properties resultTypes operands operands' blockOperands mem mem' h hMem := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next x heq =>
      obtain ⟨x', hT, rfl | ⟨c, rfl, hc⟩⟩ := RuntimeValue.toList_addr1_of_isRefinedBy h heq
      · simp
      obtain ⟨c', rfl, hc'⟩ : ∃ c', x' = .val c' ∧ (c ⊒ c') := by
        rcases hc with rfl | rfl <;> simp
      simp only [hT, Pointer.checkAlignment_of_isRefinedBy hc']
      rcases resultTypes.toList with _ | ⟨type, _ | _⟩
      · simp [liftM]
      · refine Interp.isRefinedBy_bind_same fun _ => ?_
        exact Interp.isRefinedBy_bind (MemoryState.llvmLoad_isRefinedBy_of_refines hMem hc' type)
          fun v v' hv => by simpa using result_single hv hMem
      · simp [liftM]
    · simp [Interp.isRefinedBy]

/-! ## Arithmetic -/

instance llvm_monotone_add : InterpretOp'Monotone (.llvm .add) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.add, LLVM.Int.cast]

instance llvm_monotone_sub : InterpretOp'Monotone (.llvm .sub) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.sub, LLVM.Int.cast]

instance llvm_monotone_mul : InterpretOp'Monotone (.llvm .mul) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.mul, LLVM.Int.cast]

instance llvm_monotone_intr__smulh : InterpretOp'Monotone (.llvm .intr__smulh) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.smulHigh, LLVM.Int.cast]

instance llvm_monotone_intr__umulh : InterpretOp'Monotone (.llvm .intr__umulh) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.umulHigh, LLVM.Int.cast]

instance llvm_monotone_intr__scmp : InterpretOp'Monotone (.llvm .intr__scmp) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.scmp, LLVM.Int.cast]

instance llvm_monotone_intr__ucmp : InterpretOp'Monotone (.llvm .intr__ucmp) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.ucmp, LLVM.Int.cast]

instance llvm_monotone_sdiv : InterpretOp'Monotone (.llvm .sdiv) where
  monotone _ _ _ _ _ _ _ _ hMem := by
    op_mono [Llvm.interpretOp'] [LLVM.Int.sdiv, LLVM.Int.isSignedDivisionUB, LLVM.Int.cast]

instance llvm_monotone_udiv : InterpretOp'Monotone (.llvm .udiv) where
  monotone _ _ _ _ _ _ _ _ hMem := by
    op_mono [Llvm.interpretOp'] [LLVM.Int.udiv, LLVM.Int.isUnsignedDivisionUB, LLVM.Int.cast]

instance llvm_monotone_srem : InterpretOp'Monotone (.llvm .srem) where
  monotone _ _ _ _ _ _ _ _ hMem := by
    op_mono [Llvm.interpretOp'] [LLVM.Int.srem, LLVM.Int.isSignedDivisionUB, LLVM.Int.cast]

instance llvm_monotone_urem : InterpretOp'Monotone (.llvm .urem) where
  monotone _ _ _ _ _ _ _ _ hMem := by
    op_mono [Llvm.interpretOp'] [LLVM.Int.urem, LLVM.Int.isUnsignedDivisionUB, LLVM.Int.cast]

instance llvm_monotone_ashr : InterpretOp'Monotone (.llvm .ashr) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.ashr, LLVM.Int.cast]

instance llvm_monotone_intr__fshl : InterpretOp'Monotone (.llvm .intr__fshl) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.fshl, LLVM.Int.cast]

instance llvm_monotone_intr__fshr : InterpretOp'Monotone (.llvm .intr__fshr) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.fshr, LLVM.Int.cast]

instance llvm_monotone_intr__ctlz : InterpretOp'Monotone (.llvm .intr__ctlz) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.ctlz, LLVM.Int.cast]

instance llvm_monotone_intr__cttz : InterpretOp'Monotone (.llvm .intr__cttz) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.cttz, LLVM.Int.cast]

instance llvm_monotone_intr__ctpop : InterpretOp'Monotone (.llvm .intr__ctpop) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.ctpop, LLVM.Int.cast]

instance llvm_monotone_intr__bswap : InterpretOp'Monotone (.llvm .intr__bswap) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.bswap, LLVM.Int.cast]

instance llvm_monotone_intr__bitreverse : InterpretOp'Monotone (.llvm .intr__bitreverse) where
  monotone _ _ _ _ _ _ _ _ hMem := by
    op_mono [Llvm.interpretOp'] [LLVM.Int.bitreverse, LLVM.Int.cast]

instance llvm_monotone_and : InterpretOp'Monotone (.llvm .and) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.and, LLVM.Int.cast]

instance llvm_monotone_or : InterpretOp'Monotone (.llvm .or) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.or, LLVM.Int.cast]

instance llvm_monotone_xor : InterpretOp'Monotone (.llvm .xor) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.xor, LLVM.Int.cast]

instance llvm_monotone_intr__smax : InterpretOp'Monotone (.llvm .intr__smax) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.smax, LLVM.Int.cast]

instance llvm_monotone_intr__smin : InterpretOp'Monotone (.llvm .intr__smin) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.smin, LLVM.Int.cast]

instance llvm_monotone_intr__umax : InterpretOp'Monotone (.llvm .intr__umax) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.umax, LLVM.Int.cast]

instance llvm_monotone_intr__umin : InterpretOp'Monotone (.llvm .intr__umin) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.umin, LLVM.Int.cast]

instance llvm_monotone_intr__abs : InterpretOp'Monotone (.llvm .intr__abs) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.abs, LLVM.Int.cast]

instance llvm_monotone_intr__sadd__sat : InterpretOp'Monotone (.llvm .intr__sadd__sat) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.saddSat, LLVM.Int.cast]

instance llvm_monotone_intr__uadd__sat : InterpretOp'Monotone (.llvm .intr__uadd__sat) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.uaddSat, LLVM.Int.cast]

instance llvm_monotone_intr__ssub__sat : InterpretOp'Monotone (.llvm .intr__ssub__sat) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.ssubSat, LLVM.Int.cast]

instance llvm_monotone_intr__usub__sat : InterpretOp'Monotone (.llvm .intr__usub__sat) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.usubSat, LLVM.Int.cast]

instance llvm_monotone_intr__sshl__sat : InterpretOp'Monotone (.llvm .intr__sshl__sat) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.sshlSat, LLVM.Int.cast]

instance llvm_monotone_intr__ushl__sat : InterpretOp'Monotone (.llvm .intr__ushl__sat) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.ushlSat, LLVM.Int.cast]

instance llvm_monotone_zext : InterpretOp'Monotone (.llvm .zext) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.zext, LLVM.Int.cast]

instance llvm_monotone_sext : InterpretOp'Monotone (.llvm .sext) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.sext, LLVM.Int.cast]

instance llvm_monotone_icmp : InterpretOp'Monotone (.llvm .icmp) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Int.icmp, LLVM.Int.cast]

instance llvm_monotone_inttoptr : InterpretOp'Monotone (.llvm .inttoptr) where
  monotone _ _ _ _ _ _ _ _ hMem := by
    op_mono [Llvm.interpretOp']
      [MemoryState.ptrFromInt, LLVM.Int.cast, MemoryState.decode]

instance llvm_monotone_ptrtoint : InterpretOp'Monotone (.llvm .ptrtoint) where
  monotone _ _ _ _ _ _ _ _ hMem := by op_mono [Llvm.interpretOp'] [LLVM.Ptr.toInt, LLVM.Int.cast]

/-! ## Constants, `select` and control flow -/

instance llvm_monotone_mlir__constant : InterpretOp'Monotone (.llvm .mlir__constant) where
  monotone _ _ _ _ _ _ _ _ hMem := by
    simp only [interpretOp', Llvm.interpretOp']
    (repeat' split) <;> simp [Interp.isRefinedBy, OperationResult.isRefinedBy,
      ControlFlowAction.optionIsRefinedBy, hMem]

instance llvm_monotone_mlir__poison : InterpretOp'Monotone (.llvm .mlir__poison) where
  monotone _ _ _ _ _ _ _ _ hMem := by
    simp only [interpretOp', Llvm.interpretOp']
    (repeat' split) <;> simp [Interp.isRefinedBy, OperationResult.isRefinedBy,
      ControlFlowAction.optionIsRefinedBy, hMem]

instance llvm_monotone_mlir__zero : InterpretOp'Monotone (.llvm .mlir__zero) where
  monotone _ _ _ _ _ _ _ _ hMem := by
    simp only [interpretOp', Llvm.interpretOp']
    (repeat' split) <;> simp [Interp.isRefinedBy, OperationResult.isRefinedBy,
      ControlFlowAction.optionIsRefinedBy, hMem]

instance llvm_monotone_unreachable : InterpretOp'Monotone (.llvm .unreachable) where
  monotone _ _ _ _ _ _ _ _ _ := by simp [interpretOp', Llvm.interpretOp', Interp.isRefinedBy]

instance llvm_monotone_return : InterpretOp'Monotone (.llvm .return) where
  monotone _ _ _ _ _ _ _ h hMem := by
    simp [interpretOp', Llvm.interpretOp', OperationResult.isRefinedBy,
      ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy, h, hMem]

instance llvm_monotone_br : InterpretOp'Monotone (.llvm .br) where
  monotone _ _ _ _ _ _ _ h hMem := by
    simp only [interpretOp', Llvm.interpretOp']
    split <;> simp [Interp.isRefinedBy, OperationResult.isRefinedBy,
      ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy, h, hMem]

/-- `select` picks an operand by a condition that is not poison, which the target shares. -/
instance llvm_monotone_select : InterpretOp'Monotone (.llvm .select) where
  monotone _ _ _ _ _ _ _ h hMem := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · rename_i heq
      obtain ⟨_, _, _, hT, h1, h2, h3⟩ := RuntimeValue.toList_int3_of_isRefinedBy h heq
      simp only [hT]
      split
      · simp [Interp.isRefinedBy]
      · rcases h1 with rfl | ⟨c, rfl, rfl⟩
        · simp [LLVM.Int.select, Id.run, Interp.isRefinedBy, OperationResult.isRefinedBy,
            ControlFlowAction.optionIsRefinedBy, RuntimeValue.isRefinedBy,
            Data.LLVM.Int.isRefinedBy, hMem]
        · by_cases hc : c = 1#1
          · rcases h2 with rfl | ⟨_, rfl, rfl⟩ <;>
              simp [LLVM.Int.select, Id.run, hc, Interp.isRefinedBy, OperationResult.isRefinedBy,
                ControlFlowAction.optionIsRefinedBy, RuntimeValue.isRefinedBy,
                Data.LLVM.Int.isRefinedBy, hMem]
          · rcases h3 with rfl | ⟨_, rfl, rfl⟩ <;>
              simp [LLVM.Int.select, Id.run, hc, LLVM.Int.cast, Interp.isRefinedBy,
                OperationResult.isRefinedBy, ControlFlowAction.optionIsRefinedBy,
                RuntimeValue.isRefinedBy, Data.LLVM.Int.isRefinedBy, hMem]
    · simp [Interp.isRefinedBy]

/-- `cond_br` on poison is undefined behavior; on a value, which the target shares, it passes on
a slice of its operands. -/
instance llvm_monotone_cond_br : InterpretOp'Monotone (.llvm .cond_br) where
  monotone _ _ _ _ _ _ _ h hMem := by
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
              RuntimeValue.arrayIsRefinedBy_extract h, RuntimeValue.arrayIsRefinedBy_extract_size h,
              hMem]
          · simp [Interp.isRefinedBy]
          · simp [Interp.isRefinedBy]
        · simp [Interp.isRefinedBy]
      · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

/--
`switch` on refined operands branches alike: it passes on slices of its operands and the
memory it is given. `hR` relates two such results.
-/
private theorem llvm_switch_isRefinedBy
    {R : Array RuntimeValue × MemoryState × Option ControlFlowAction →
      Array RuntimeValue × MemoryState × Option ControlFlowAction → Prop}
    (props : propertiesOf (OpCode.llvm .switch)) (resultTypes : Array TypeAttr)
    {operands operands' : Array RuntimeValue} (blockOperands : Array BlockPtr)
    (mem mem' : MemoryState) (h : operands ⊒ operands')
    (hR : ∀ a b dest, R (#[], mem, some (.branch (operands.extract a b) dest))
      (#[], mem', some (.branch (operands'.extract a b) dest))) :
    Interp.isRefinedBy R
      (interpretOp' (.llvm .switch) props resultTypes operands blockOperands mem)
      (interpretOp' (.llvm .switch) props resultTypes operands' blockOperands mem') := by
  simp only [interpretOp', Llvm.interpretOp']
  split
  · split
    · next value heq =>
      obtain ⟨v', h0, hv⟩ := RuntimeValue.getElem?_of_arrayIsRefinedBy h heq
      simp only [h0]
      split
      · split
        · next bw v =>
          obtain rfl := RuntimeValue.int_val_isRefinedBy_iff.mp hv
          rcases hcv : props.caseValues? bw with _ | caseValues
          · simp [hcv, Interp.isRefinedBy]
          · simp only [hcv]
            refine Interp.isRefinedBy_bind
              (R := fun (s s' : Option (Array RuntimeValue × MemoryState ×
                  Option ControlFlowAction) × Nat) => s.2 = s'.2 ∧
                ((s.1 = none ∧ s'.1 = none) ∨
                  ∃ a a', s.1 = some a ∧ s'.1 = some a' ∧ R a a'))
              (Interp.forIn_range_isRefinedBy _ _ _ _ (fun i b b' hb => ?_) _ _ (by simp)) ?_
            · obtain ⟨hsnd, -⟩ := hb
              rw [hsnd]
              split
              · split
                · split
                  · simp only [Interp.pure_eq, Interp.isRefinedBy_ok_ok, ForInStep.rel_done]
                    exact ⟨by simp, .inr ⟨_, _, rfl, rfl, hR _ _ _⟩⟩
                  · simp [Interp.isRefinedBy, Bind.bind]
                · simp [Interp.isRefinedBy]
              · simp [Interp.isRefinedBy, Bind.bind]
            · rintro ⟨r, base⟩ ⟨r', base'⟩ ⟨rfl, hr⟩
              rcases hr with ⟨rfl, rfl⟩ | ⟨a, a', rfl, rfl, ha⟩
              · simpa [Interp.isRefinedBy] using hR _ _ _
              · simpa [Interp.isRefinedBy] using ha
        · simp [Interp.isRefinedBy]
        · simp [Interp.isRefinedBy]
      · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]
  · simp [Interp.isRefinedBy]

instance llvm_monotone_switch : InterpretOp'Monotone (.llvm .switch) where
  monotone props _ _ _ _ mem mem' h hMem :=
    llvm_switch_isRefinedBy props _ _ mem mem' h fun _ _ _ =>
      OperationResult.isRefinedBy_def.mpr ⟨by simp, hMem, by
        simp [ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy,
          RuntimeValue.arrayIsRefinedBy_extract h]⟩

/-! ## `getelementptr`, shifts, truncation and casts -/

/-- A dynamic index of a GEP, read from refined operands: the same stride, and the same value
unless it is poison. -/
private theorem gepIndex_isRefinedBy {operands operands' : Array RuntimeValue}
    (h : operands ⊒ operands') {e : Option Nat × Nat} {r : Option Int × Nat}
    (hr : Llvm.gepIndex operands e = some r) :
    ∃ r', Llvm.gepIndex operands' e = some r' ∧
      ∀ x, (r.1.map (· * (r.2 : Int))) = some x → (r'.1.map (· * (r'.2 : Int))) = some x := by
  obtain ⟨v, hv⟩ : ∃ v, Llvm.gepOperand operands e.1 = some v := by
    rcases hop : Llvm.gepOperand operands e.1 with _ | v
    · simp [Llvm.gepIndex, hop] at hr
    · exact ⟨v, rfl⟩
  obtain ⟨v', hv', hvv⟩ : ∃ v', Llvm.gepOperand operands' e.1 = some v' ∧ v ⊒ v' := by
    rcases e with ⟨_ | i, s⟩
    · simp [Llvm.gepOperand] at hv
    · simp only [Llvm.gepOperand] at hv ⊢
      exact RuntimeValue.getElem?_of_arrayIsRefinedBy
        (RuntimeValue.arrayIsRefinedBy_extract_size h 1) hv
  simp only [Llvm.gepIndex, hv, hv'] at hr ⊢
  cases v with
  | int w x =>
    obtain ⟨x', rfl, hx⟩ := RuntimeValue.int_isRefinedBy_iff.mp hvv
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
  monotone _ _ operands operands' _ mem mem' h hMem := by
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
          (∃ p, r = pure (#[RuntimeValue.addr p], mem', none)) →
          Interp.isRefinedBy OperationResult.isRefinedBy
            (pure (#[RuntimeValue.addr .poison], mem, none)) r := by
        rintro r ⟨p, rfl⟩
        simp [Interp.isRefinedBy, OperationResult.isRefinedBy, RuntimeValue.isRefinedBy,
          ControlFlowAction.optionIsRefinedBy, LLVM.Ptr.isRefinedBy, hMem]
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
        simp [Interp.isRefinedBy, OperationResult.isRefinedBy, ControlFlowAction.optionIsRefinedBy,
          hMem]
      · apply hPoison
        (repeat' split) <;> exact ⟨_, rfl⟩
    · simp [Interp.isRefinedBy]

private theorem int_cast_isRefinedBy {w w' : Nat} {x x' : LLVM.Int w}
    (h : LLVM.Int.isRefinedBy x x') (hw : w = w') :
    LLVM.Int.isRefinedBy (x.cast hw) (x'.cast hw) := by
  subst hw
  cases x <;> cases x' <;> simp_all [LLVM.Int.isRefinedBy, LLVM.Int.cast]

/-- A single refined result, with refined memory and no control flow. -/
private theorem result_isRefinedBy {v v' : RuntimeValue} (h : v ⊒ v') {mem mem' : MemoryState}
    (hMem : mem ⊒ mem') :
    Interp.isRefinedBy OperationResult.isRefinedBy (pure (#[v], mem, none))
      (pure (#[v'], mem', none)) := by
  simp [Interp.isRefinedBy, OperationResult.isRefinedBy, ControlFlowAction.optionIsRefinedBy, h,
    hMem]

/-- `shl` of an integer is monotone as the integer operations are; of a byte, bitwise. -/
instance llvm_monotone_shl : InterpretOp'Monotone (.llvm .shl) where
  monotone _ _ _ _ _ _ _ h hMem := by
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
          op_mono_finish [LLVM.Int.shl, LLVM.Int.cast]
      | byte bw b =>
        obtain ⟨b', rfl, hb⟩ := RuntimeValue.byte_of_isRefinedBy hl
        simp only
        split
        · simp [Interp.isRefinedBy]
        · split
          · simp [Interp.isRefinedBy]
          · refine result_isRefinedBy ?_ hMem
            exact RuntimeValue.byte_isRefinedBy_byte.mpr
              (LLVM.Byte.shl_isRefinedBy_of_isRefinedBy hb (int_cast_isRefinedBy
                (by rcases hrhs with rfl | ⟨_, rfl, rfl⟩ <;> simp [LLVM.Int.isRefinedBy]) _))
      | _ => simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

/-- `lshr` of an integer is monotone as the integer operations are; of a byte, bitwise. -/
instance llvm_monotone_lshr : InterpretOp'Monotone (.llvm .lshr) where
  monotone _ _ _ _ _ _ _ h hMem := by
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
          op_mono_finish [LLVM.Int.lshr, LLVM.Int.cast]
      | byte bw b =>
        obtain ⟨b', rfl, hb⟩ := RuntimeValue.byte_of_isRefinedBy hl
        simp only
        split
        · simp [Interp.isRefinedBy]
        · exact result_isRefinedBy (RuntimeValue.byte_isRefinedBy_byte.mpr
            (LLVM.Byte.lshr_isRefinedBy_of_isRefinedBy hb (int_cast_isRefinedBy
              (by rcases hrhs with rfl | ⟨_, rfl, rfl⟩ <;> simp [LLVM.Int.isRefinedBy]) _))) hMem
      | _ => simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

/-- `trunc` of an integer is monotone as the integer operations are; of a byte, bitwise. -/
instance llvm_monotone_trunc : InterpretOp'Monotone (.llvm .trunc) where
  monotone _ _ _ _ _ _ _ h hMem := by
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
            op_mono_finish [LLVM.Int.trunc]
        | byte w b =>
          obtain ⟨b', rfl, hb⟩ := RuntimeValue.byte_of_isRefinedBy hv
          simp only
          split
          · split
            · simp [Interp.isRefinedBy]
            · exact result_isRefinedBy (RuntimeValue.byte_isRefinedBy_byte.mpr
                (LLVM.Byte.trunc_isRefinedBy hb _)) hMem
          · simp [Interp.isRefinedBy]
        | _ => simp [Interp.isRefinedBy]
      · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

/-- The pointer at an integer address: poison for poison. -/
private theorem ptrFromInt_isRefinedBy {mem : MemoryState} {x x' : LLVM.Int 64}
    (h : LLVM.Int.isRefinedBy x x') :
    RuntimeValue.addr (mem.ptrFromInt x) ⊒ RuntimeValue.addr (mem.ptrFromInt x') := by
  cases x <;> cases x' <;> simp_all [LLVM.Int.isRefinedBy, MemoryState.ptrFromInt,
    RuntimeValue.isRefinedBy, LLVM.Ptr.isRefinedBy]

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
  monotone _ _ _ _ _ _ _ h hMem := by
    simp only [interpretOp', Llvm.interpretOp']
    split
    · next v heq =>
      obtain ⟨v', hT, hv⟩ := RuntimeValue.toList_single_of_isRefinedBy h heq
      simp only [hT]
      split
      · exact Interp.isRefinedBy_bind (bitcastValue_isRefinedBy hv _)
          fun a b hab => result_isRefinedBy hab hMem
      · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

/-! ## Every opcode but `freeze` -/

/--
Every LLVM opcode but `freeze` is monotone in its operands and its memory. The opcodes the
interpreter does not know fail.
-/
theorem llvm_interpretOp'Monotone {opType : Llvm} (hFreeze : opType ≠ .freeze) :
    InterpretOp'Monotone (.llvm opType) := by
  cases opType <;>
    first
      | exact absurd rfl hFreeze
      | infer_instance
      | exact ⟨fun _ _ _ _ _ _ _ _ _ => by
          simp [interpretOp', Llvm.interpretOp', Interp.isRefinedBy]⟩

end Veir

end
