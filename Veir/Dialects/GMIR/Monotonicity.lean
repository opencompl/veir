module

public import Veir.Interpreter.Lemmas
public import Veir.Interpreter.Refinement.MonoTactic
import Veir.Interpreter.Refinement.Memory

import all Veir.Interpreter.Basic
import all Veir.Interpreter.Memory
import all Veir.Interpreter.Refinement.Basic
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR.Semantics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.Refinement
import all Veir.Interpreter.Interp

import Veir.Interpreter.Refinement.Lemmas

public section

/-!
# Monotonicity of the gMIR interpreter

An opcode is monotone in its operands when refining its operands refines its result.

Every gMIR opcode but `g_store` is monotone in its operands with the same memory. A refinement
of the operands replaces some poison operands by values. The operations are strict in poison, or,
as `g_select`, choose between operands without looking at them, so their results refine.
Division checks for undefined behavior with a poison operand as if it were the worst value, so a
refinement does not introduce it.

With refined memory (`InterpretOp'ContextuallyMonotone`), every gMIR opcode is monotone: the
opcodes that do not touch memory carry their monotonicity over (`gmir_frame`), and `g_load` and
`g_store` load from and store to refined memory. `g_store` of a refined value stores other bytes,
which only refined memory relates; a wider integer is truncated first, which keeps poison.
-/

open Veir.Data

namespace Veir

instance gmir_monotone_g_add : InterpretOp'Monotone (.gmir .g_add) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.add, LLVM.Int.cast]

instance gmir_monotone_g_sub : InterpretOp'Monotone (.gmir .g_sub) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.sub, LLVM.Int.cast]

instance gmir_monotone_g_mul : InterpretOp'Monotone (.gmir .g_mul) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.mul, LLVM.Int.cast]

instance gmir_monotone_g_and : InterpretOp'Monotone (.gmir .g_and) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.and, LLVM.Int.cast]

instance gmir_monotone_g_or : InterpretOp'Monotone (.gmir .g_or) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.or, LLVM.Int.cast]

instance gmir_monotone_g_xor : InterpretOp'Monotone (.gmir .g_xor) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.xor, LLVM.Int.cast]

instance gmir_monotone_g_sdiv : InterpretOp'Monotone (.gmir .g_sdiv) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.sdiv, LLVM.Int.isSignedDivisionUB, LLVM.Int.cast]

instance gmir_monotone_g_udiv : InterpretOp'Monotone (.gmir .g_udiv) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.udiv, LLVM.Int.isUnsignedDivisionUB, LLVM.Int.cast]

instance gmir_monotone_g_srem : InterpretOp'Monotone (.gmir .g_srem) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.srem, LLVM.Int.isSignedDivisionUB, LLVM.Int.cast]

instance gmir_monotone_g_urem : InterpretOp'Monotone (.gmir .g_urem) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.urem, LLVM.Int.isUnsignedDivisionUB, LLVM.Int.cast]

instance gmir_monotone_g_shl : InterpretOp'Monotone (.gmir .g_shl) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.shl, shiftAmount, LLVM.Int.cast]

instance gmir_monotone_g_lshr : InterpretOp'Monotone (.gmir .g_lshr) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.lshr, shiftAmount, LLVM.Int.cast]

instance gmir_monotone_g_ashr : InterpretOp'Monotone (.gmir .g_ashr) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.ashr, shiftAmount, LLVM.Int.cast]

instance gmir_monotone_g_icmp : InterpretOp'Monotone (.gmir .g_icmp) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.icmp, LLVM.Int.zext, LLVM.Int.cast]

instance gmir_monotone_g_anyext : InterpretOp'Monotone (.gmir .g_anyext) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.zext, LLVM.Int.cast]

instance gmir_monotone_g_sext : InterpretOp'Monotone (.gmir .g_sext) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.sext, LLVM.Int.cast]

instance gmir_monotone_g_zext : InterpretOp'Monotone (.gmir .g_zext) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.zext, LLVM.Int.cast]

instance gmir_monotone_g_trunc : InterpretOp'Monotone (.gmir .g_trunc) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.trunc, LLVM.Int.cast]

instance gmir_monotone_g_sext_inreg : InterpretOp'Monotone (.gmir .g_sext_inreg) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.trunc, LLVM.Int.sext, LLVM.Int.cast]

instance gmir_monotone_g_inttoptr : InterpretOp'Monotone (.gmir .g_inttoptr) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [MemoryState.ptrFromInt, LLVM.Int.cast]

instance gmir_monotone_g_ptrtoint : InterpretOp'Monotone (.gmir .g_ptrtoint) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Ptr.toInt, LLVM.Int.cast]

instance gmir_monotone_g_bswap : InterpretOp'Monotone (.gmir .g_bswap) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.bswap, LLVM.Int.cast]

instance gmir_monotone_g_bitreverse : InterpretOp'Monotone (.gmir .g_bitreverse) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.bitreverse, LLVM.Int.cast]

instance gmir_monotone_g_brev8 : InterpretOp'Monotone (.gmir .g_brev8) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [brev8, LLVM.Int.bswap, LLVM.Int.bitreverse, LLVM.Int.cast]

instance gmir_monotone_g_saddsat : InterpretOp'Monotone (.gmir .g_saddsat) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.saddSat, LLVM.Int.cast]

instance gmir_monotone_g_uaddsat : InterpretOp'Monotone (.gmir .g_uaddsat) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.uaddSat, LLVM.Int.cast]

instance gmir_monotone_g_ssubsat : InterpretOp'Monotone (.gmir .g_ssubsat) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.ssubSat, LLVM.Int.cast]

instance gmir_monotone_g_usubsat : InterpretOp'Monotone (.gmir .g_usubsat) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.usubSat, LLVM.Int.cast]

instance gmir_monotone_g_sshlsat : InterpretOp'Monotone (.gmir .g_sshlsat) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.sshlSat, shiftAmount, LLVM.Int.cast]

instance gmir_monotone_g_ushlsat : InterpretOp'Monotone (.gmir .g_ushlsat) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.ushlSat, shiftAmount, LLVM.Int.cast]

instance gmir_monotone_g_smin : InterpretOp'Monotone (.gmir .g_smin) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.smin, LLVM.Int.cast]

instance gmir_monotone_g_smax : InterpretOp'Monotone (.gmir .g_smax) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.smax, LLVM.Int.cast]

instance gmir_monotone_g_umin : InterpretOp'Monotone (.gmir .g_umin) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.umin, LLVM.Int.cast]

instance gmir_monotone_g_umax : InterpretOp'Monotone (.gmir .g_umax) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.umax, LLVM.Int.cast]

instance gmir_monotone_g_abs : InterpretOp'Monotone (.gmir .g_abs) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [LLVM.Int.abs, LLVM.Int.cast]

instance gmir_monotone_g_ctlz : InterpretOp'Monotone (.gmir .g_ctlz) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.ctlz, resizeCount, LLVM.Int.cast]

instance gmir_monotone_g_cttz : InterpretOp'Monotone (.gmir .g_cttz) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.cttz, resizeCount, LLVM.Int.cast]

instance gmir_monotone_g_ctlz_zero_poison : InterpretOp'Monotone (.gmir .g_ctlz_zero_poison) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.ctlz, resizeCount, LLVM.Int.cast]

instance gmir_monotone_g_cttz_zero_poison : InterpretOp'Monotone (.gmir .g_cttz_zero_poison) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.cttz, resizeCount, LLVM.Int.cast]

instance gmir_monotone_g_ctpop : InterpretOp'Monotone (.gmir .g_ctpop) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.ctpop, resizeCount, LLVM.Int.cast]

instance gmir_monotone_g_merge_values : InterpretOp'Monotone (.gmir .g_merge_values) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [mergeValues, LLVM.Int.cast]

instance gmir_monotone_g_unmerge_values : InterpretOp'Monotone (.gmir .g_unmerge_values) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [unmergeValues, LLVM.Int.cast]

instance gmir_monotone_g_uaddo : InterpretOp'Monotone (.gmir .g_uaddo) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.add, LLVM.Int.uaddOverflowFlag, LLVM.Int.cast]

instance gmir_monotone_g_uadde : InterpretOp'Monotone (.gmir .g_uadde) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [uaddWithCarry, LLVM.Int.cast]

instance gmir_monotone_g_usubo : InterpretOp'Monotone (.gmir .g_usubo) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.sub, LLVM.Int.usubOverflowFlag, LLVM.Int.cast]

instance gmir_monotone_g_usube : InterpretOp'Monotone (.gmir .g_usube) where
  monotone _ _ _ _ _ _ _ := by op_mono [GMIR.interpretOp'] [usubWithBorrow, LLVM.Int.cast]

instance gmir_monotone_g_saddo : InterpretOp'Monotone (.gmir .g_saddo) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.add, LLVM.Int.saddOverflowFlag, LLVM.Int.cast]

instance gmir_monotone_g_ssubo : InterpretOp'Monotone (.gmir .g_ssubo) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.sub, LLVM.Int.ssubOverflowFlag, LLVM.Int.cast]

instance gmir_monotone_g_fshl : InterpretOp'Monotone (.gmir .g_fshl) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.fshl, GMIR.funnelShiftAmount, LLVM.Int.cast]

instance gmir_monotone_g_fshr : InterpretOp'Monotone (.gmir .g_fshr) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [LLVM.Int.fshr, GMIR.funnelShiftAmount, LLVM.Int.cast]

instance gmir_monotone_g_rotl : InterpretOp'Monotone (.gmir .g_rotl) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [GMIR.rotl, LLVM.Int.fshl, GMIR.funnelShiftAmount, LLVM.Int.cast]

instance gmir_monotone_g_rotr : InterpretOp'Monotone (.gmir .g_rotr) where
  monotone _ _ _ _ _ _ _ := by
    op_mono [GMIR.interpretOp'] [GMIR.rotr, LLVM.Int.fshr, GMIR.funnelShiftAmount, LLVM.Int.cast]

/-- `g_select` picks an operand by a condition that is not poison, which the target shares. -/
instance gmir_monotone_g_select : InterpretOp'Monotone (.gmir .g_select) where
  monotone _ _ _ _ _ _ h := by
    simp only [interpretOp', GMIR.interpretOp']
    split
    · rename_i heq
      obtain ⟨_, _, _, hT, h1, h2, h3⟩ := RuntimeValue.toList_int3_of_isRefinedBy h heq
      simp only [hT]
      split
      · simp [Interp.isRefinedBy]
      · rcases h1 with rfl | ⟨c, rfl, rfl⟩
        · simp [GMIR.selectNonzero, Id.run, Interp.isRefinedBy, OperationResult.isRefinedBy,
            ControlFlowAction.optionIsRefinedBy, RuntimeValue.isRefinedBy, _root_.isRefinedBy]
        · by_cases hc : c = 0#_
          · rcases h3 with rfl | ⟨_, rfl, rfl⟩ <;>
              simp [GMIR.selectNonzero, Id.run, hc, LLVM.Int.cast, Interp.isRefinedBy,
                OperationResult.isRefinedBy, ControlFlowAction.optionIsRefinedBy,
                RuntimeValue.isRefinedBy, _root_.isRefinedBy]
          · rcases h2 with rfl | ⟨_, rfl, rfl⟩ <;>
              simp [GMIR.selectNonzero, Id.run, hc, Interp.isRefinedBy, OperationResult.isRefinedBy,
                ControlFlowAction.optionIsRefinedBy, RuntimeValue.isRefinedBy, _root_.isRefinedBy]
    · simp [Interp.isRefinedBy]

/-- A load from a poison pointer is undefined behavior, and a load from a pointer is the same. -/
instance gmir_monotone_g_load : InterpretOp'Monotone (.gmir .g_load) where
  monotone _ _ _ _ _ _ h := by
    simp only [interpretOp', GMIR.interpretOp']
    split
    · rename_i heq
      obtain ⟨_, hT, h1⟩ := RuntimeValue.toList_addr1_of_isRefinedBy h heq
      simp only [hT]
      rcases h1 with rfl | ⟨_, rfl, rfl⟩
      · split <;> simp [Interp.isRefinedBy]
      · exact Interp.isRefinedBy_refl_operationResult_sameMemory _
    · simp [Interp.isRefinedBy]

/-- A constant has no operands. -/
instance gmir_monotone_g_constant : InterpretOp'Monotone (.gmir .g_constant) where
  monotone _ _ _ _ _ _ _ := Interp.isRefinedBy_refl_operationResult_sameMemory _

/-- Poison reads its result type, not its operands. -/
instance gmir_monotone_g_poison : InterpretOp'Monotone (.gmir .g_poison) where
  monotone _ _ _ _ _ _ _ := Interp.isRefinedBy_refl_operationResult_sameMemory _

/-- A branch passes its operands on. -/
instance gmir_monotone_g_br : InterpretOp'Monotone (.gmir .g_br) where
  monotone _ _ _ _ _ _ h := by
    simp only [interpretOp', GMIR.interpretOp']
    split <;> simp [Interp.isRefinedBy, OperationResult.isRefinedBy,
      ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy, h]

/--
A conditional branch on poison is undefined behavior. On a value, which the target shares, it
passes on a slice of its operands.
-/
instance gmir_monotone_g_brcond : InterpretOp'Monotone (.gmir .g_brcond) where
  monotone _ _ _ _ _ _ h := by
    simp only [interpretOp', GMIR.interpretOp']
    split
    · split
      · split
        · rename_i heq
          obtain ⟨v', h0, hv⟩ := RuntimeValue.getElem?_of_arrayIsRefinedBy h heq
          obtain rfl := RuntimeValue.int_val_isRefinedBy_iff.mp hv
          simp only [h0]
          split <;> simp [Interp.isRefinedBy, OperationResult.isRefinedBy,
            ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy,
            RuntimeValue.arrayIsRefinedBy_extract h, RuntimeValue.arrayIsRefinedBy_extract_size h]
        · simp [Interp.isRefinedBy]
        · simp [Interp.isRefinedBy]
      · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]

/-! ## Refined memory -/

/-- A result of no values and refined memory. -/
private theorem result_empty {m m' : MemoryState} (hm : m ⊒ m') :
    OperationResult.isRefinedBy (#[], m, none) (#[], m', none) :=
  OperationResult.isRefinedBy_def.mpr
    ⟨RuntimeValue.arrayIsRefinedBy_refl _, hm, trivial⟩

/-- A result of one value and refined memory. -/
private theorem result_single {v v' : RuntimeValue} {m m' : MemoryState} (hv : v ⊒ v')
    (hm : m ⊒ m') :
    OperationResult.isRefinedBy (#[v], m, none) (#[v'], m', none) :=
  OperationResult.isRefinedBy_def.mpr
    ⟨RuntimeValue.singleton_isRefinedBy_iff.mpr ⟨_, rfl, hv⟩, hm, trivial⟩

/-- Integers of refined integers refine. -/
theorem RuntimeValue.int_isRefinedBy_of {w : Nat} {x x' : LLVM.Int w}
    (h : _root_.isRefinedBy x x') : RuntimeValue.int w x ⊒ RuntimeValue.int w x' := by
  simpa [RuntimeValue.isRefinedBy] using h

/-- A function of integers that keeps poison keeps refinement. -/
theorem Data.LLVM.Int.isRefinedBy_map {w w' : Nat} {f : LLVM.Int w → LLVM.Int w'}
    (hf : f .poison = .poison) {x x' : LLVM.Int w} (h : _root_.isRefinedBy x x') :
    _root_.isRefinedBy (f x) (f x') := by
  cases x with
  | poison => rw [hf]; exact _root_.poison_isRefinedBy _
  | val a =>
    cases x' with
    | poison => exact absurd h (by simp [_root_.isRefinedBy])
    | val b => obtain rfl : a = b := h; exact _root_.isRefinedBy_refl _

/--
`g_load` is monotone: a poison pointer is undefined behavior, and an integer or any other value
loaded from refined memory refines.
-/
instance gmir_contextuallyMonotone_g_load :
    InterpretOp'ContextuallyMonotone (.gmir .g_load) where
  monotone properties resultTypes operands operands' blockOperands mem mem' h hMem := by
    simp only [interpretOp', GMIR.interpretOp']
    split
    · next x heq =>
      obtain ⟨x', hT, rfl | ⟨c, rfl, rfl⟩⟩ := RuntimeValue.toList_addr1_of_isRefinedBy h heq
      · simp only [hT]; split <;> simp
      simp only [hT]
      split
      rotate_left
      · simp
      refine Interp.isRefinedBy_bind_same fun _ => ?_
      split
      · refine Interp.isRefinedBy_bind (MemoryState.intLoad_isRefinedBy_of_refines hMem
          (Pointer.isRefinedBy_iff.mpr rfl) _) fun y y' hy => ?_
        split
        · simpa using result_single (RuntimeValue.int_isRefinedBy_of
            (LLVM.Int.isRefinedBy_map (f := fun z => z.zext _ false _) rfl hy)) hMem
        · split
          · simpa using result_single (RuntimeValue.int_isRefinedBy_of
              (LLVM.Int.isRefinedBy_map (f := fun z => z.cast _) rfl hy)) hMem
          · simp
      · exact Interp.isRefinedBy_bind (MemoryState.llvmLoad_isRefinedBy_of_refines hMem
          (Pointer.isRefinedBy_iff.mpr rfl) _) fun v v' hv => by simpa using result_single hv hMem
    · simp

/--
`g_store` is monotone: a poison pointer is undefined behavior, a refined value has the same kind
and width, its truncation refines, and storing it into refined memory gives refined memory.
-/
instance gmir_contextuallyMonotone_g_store :
    InterpretOp'ContextuallyMonotone (.gmir .g_store) where
  monotone properties resultTypes operands operands' blockOperands mem mem' h hMem := by
    simp only [interpretOp', GMIR.interpretOp']
    split
    · next v x heq =>
      obtain ⟨v', a', hT, hv, ha⟩ := RuntimeValue.toList_pair_of_isRefinedBy h heq
      obtain ⟨x', rfl, rfl | ⟨c, rfl, rfl⟩⟩ := RuntimeValue.addr_isRefinedBy_iff.mp ha
      · simp only [hT]; simp
      simp only [hT]
      refine Interp.isRefinedBy_bind_same fun _ => ?_
      have hs : ∀ {u u' : RuntimeValue}, u ⊒ u' →
          Interp.isRefinedBy OperationResult.isRefinedBy
          (do let m ← mem.llvmStore c u; pure ((#[] : Array RuntimeValue), m,
            (none : Option ControlFlowAction)))
          (do let m ← mem'.llvmStore c u'; pure ((#[] : Array RuntimeValue), m,
            (none : Option ControlFlowAction))) := fun hu =>
        Interp.isRefinedBy_bind (MemoryState.llvmStore_isRefinedBy_of_refines hMem
          (Pointer.isRefinedBy_iff.mpr rfl) hu) fun _ _ hm => by simpa using result_empty hm
      cases v with
      | int w y =>
        obtain ⟨y', rfl, hy⟩ := RuntimeValue.int_isRefinedBy_iff.mp hv
        dsimp only
        split
        · simp only [pure_bind]
          exact hs (RuntimeValue.int_isRefinedBy_of
            (LLVM.Int.isRefinedBy_map (f := fun z => z.trunc _ false false _) rfl
              (by simpa [RuntimeValue.isRefinedBy] using hv)))
        · split
          · simp only [pure_bind]; exact hs hv
          · simp [liftM]
      | _ =>
        cases v' <;>
          first
            | (exfalso; simp [RuntimeValue.isRefinedBy] at hv; done)
            | (simp only [pure_bind]; exact hs hv)
    · simp

/-- The gMIR opcodes that read or write memory. -/
def GMIR.touchesMemory : GMIR → Bool
  | .g_load | .g_store => true
  | _ => false

theorem GMIR.touchesMemory_eq_false {op : GMIR} (hLoad : op ≠ .g_load) (hStore : op ≠ .g_store) :
    op.touchesMemory = false := by
  cases op <;> simp_all [GMIR.touchesMemory]

set_option maxHeartbeats 4000000 in
/--
A gMIR opcode that does not touch memory returns the memory it is given, and reads only its
objects.
-/
theorem gmir_frame {opType : GMIR} (h : opType.touchesMemory = false)
    (properties : propertiesOf (OpCode.gmir opType)) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (blockOperands : Array BlockPtr) (mem mem' : MemoryState)
    (hObjects : mem.objects = mem'.objects) :
    interpretOp' (.gmir opType) properties resultTypes operands blockOperands mem' =
      (interpretOp' (.gmir opType) properties resultTypes operands blockOperands mem).map
        (fun r => (r.1, mem', r.2.2)) := by
  cases opType <;> simp [GMIR.touchesMemory] at h <;>
    simp only [interpretOp', GMIR.interpretOp'] <;>
    (repeat' split) <;>
    simp [Interp.pure_eq, liftM, monadLift, MonadLift.monadLift, Bind.bind,
      MemoryState.ptrFromInt_eq_of_objects hObjects] <;>
    first | rfl | ((repeat' split) <;> simp [Interp.map])

/-- Every gMIR opcode but `g_store` is monotone in its operands, with the same memory. -/
theorem gmir_interpretOp'Monotone {opType : GMIR} (h : opType ≠ .g_store) :
    InterpretOp'Monotone (.gmir opType) := by
  cases opType <;> first | exact absurd rfl h | infer_instance

/-- Every gMIR opcode is monotone in its operands and its memory. -/
theorem gmir_interpretOp'ContextuallyMonotone (opType : GMIR) :
    InterpretOp'ContextuallyMonotone (.gmir opType) := by
  cases hT : opType.touchesMemory
  · have := gmir_interpretOp'Monotone (opType := opType)
      (by rintro rfl; simp [GMIR.touchesMemory] at hT)
    exact .of_frame fun _ _ _ _ _ _ hObjects => gmir_frame hT _ _ _ _ _ _ hObjects
  · cases opType <;> simp [GMIR.touchesMemory] at hT <;> infer_instance

end Veir

end
