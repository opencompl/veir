module

public import Veir.Interpreter.CTreeRefinement.Monotone

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.Builtin.Interpreter
import Veir.Data.Casting
import Veir.Interpreter.Refinement.Lemmas

public section

/-!
# Monotonicity of the builtin opcodes in CTrees

`builtin.unrealized_conversion_cast` casts between values and registers, which cannot be poison:
casting poison, or a byte with poison bits, to a register chooses the bits that are poison, and
casting a byte to an integer chooses the bits that are poison unless all of them are. A refined
operand has less poison, so the source can choose what the target has. The other builtin opcodes
fail.
-/

open CTree

namespace Veir.CTree

theorem sim_choose_left_map {RR : α → β → Prop} (i : FreezeCIn) {f : FreezeC i → α}
    {s : Tree β} (h : ∀ x, Sim RR (pure (f x) : Tree α) s) :
    Sim RR (f <$> (CTree.choose (E := ErrorE ⊕ₑ UBE) (SubC := FreezeC) i : Tree (FreezeC i))) s := by
  rw [map_eq_pure_bind]
  exact sim_choose_left i h

theorem sim_choose_right_map {RR : α → β → Prop} (i : FreezeCIn) {f : FreezeC i → β}
    {t : Tree α} (x : FreezeC i) (h : Sim RR t (pure (f x) : Tree β)) :
    Sim RR t (f <$> (CTree.choose (E := ErrorE ⊕ₑ UBE) (SubC := FreezeC) i : Tree (FreezeC i))) := by
  rw [map_eq_pure_bind]
  exact sim_choose_right i x h

/--
Casting a byte and its refinement to integers: whatever the target chooses for its poison bits,
the source can choose to give a refined integer.
-/
theorem sim_byteToIntCTree {w : Nat} {b b' : Data.LLVM.Byte w} (hb : b ⊒ b') {RR : α → β → Prop}
    {k : Data.LLVM.Int w → Tree β} {k' : Data.LLVM.Int w → Tree α}
    (hk : ∀ x x', isRefinedBy x x' → Sim RR (k' x') (k x)) :
    Sim RR (Builtin.byteToIntCTree b' >>= k') (Builtin.byteToIntCTree b >>= k) := by
  simp only [Builtin.byteToIntCTree]
  by_cases hp : b.poison = BitVec.allOnes w
  · simp only [hp, ↓reduceIte, LawfulMonad.pure_bind]
    split
    · simp only [LawfulMonad.pure_bind]; exact hk _ _ (by simp)
    · simp only [LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
      exact sim_choose_left _ fun _ => hk _ _ (by simp)
  · have hp' : ¬ b'.poison = BitVec.allOnes w :=
      fun h => hp (LLVM.Byte.poison_eq_allOnes_of_isRefinedBy hb h)
    simp only [hp, hp', ↓reduceIte, LawfulMonad.bind_assoc, LawfulMonad.pure_bind]
    refine sim_choose_left _ fun bits =>
      sim_choose_right _ (b'.val ||| (b'.poison &&& bits)) (hk _ _ ?_)
    simp [LLVM.Byte.resolve_of_isRefinedBy hb]

/-- Every builtin opcode is monotone in CTrees. -/
instance (op : Veir.Builtin) : InterpretOpTreeMonotone (.builtin op) where
  monotone properties resultTypes operands operands' blockOperands mem mem' regions h hMem := by
    rw [interpretOp'_regions, interpretOp'_regions]
    simp only [interpretOp', Builtin.interpretOpCTree]
    cases op <;> try simp
    rcases hr : resultTypes[0]? with _ | resType
    · simp
    simp only
    rcases hs : operands.toList with _ | ⟨v, _ | ⟨_, _⟩⟩
    · rcases resType.val <;> simp
    rotate_left
    · rcases resType.val <;> simp
    obtain ⟨v', hs', hv⟩ := toList_eq_singleton_of_isRefinedBy h hs
    simp only [hs']
    cases v with
    | int w x =>
      obtain ⟨x', rfl, hx⟩ := RuntimeValue.int_of_isRefinedBy hv
      rcases hT : resType.val <;> (try simp only) <;> first | (simp; done) | skip
      · cases x with
        | val a =>
          obtain rfl : x' = .val a := by
            have := RuntimeValue.int_val_isRefinedBy_iff.mp hv; simpa using this
          exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem
        | poison =>
          cases x' with
          | val a =>
            simp only
            exact sim_choose_right_map _ (a.setWidth 64)
              (sim_result (RuntimeValue.isRefinedBy_refl _) hMem)
          | poison =>
            simp only
            exact sim_choose_left_map _ fun bits => sim_choose_right_map _ bits
              (sim_result (RuntimeValue.isRefinedBy_refl _) hMem)
      · rename_i t
        by_cases hw : t.bitwidth = w
        · simp only [hw, ↓reduceIte]
          refine sim_result ?_ hMem
          cases x with
          | poison => simp [RuntimeValue.isRefinedBy]
          | val a =>
            obtain rfl : x' = .val a := by
              have := RuntimeValue.int_val_isRefinedBy_iff.mp hv; simpa using this
            exact RuntimeValue.isRefinedBy_refl _
        · simp only [hw, ↓reduceIte, map_eq_pure_bind, fail_bind]
          exact sim_fail _ _
    | byte w b =>
      obtain ⟨b', rfl, hb⟩ := RuntimeValue.byte_of_isRefinedBy hv
      /- The register of a resolved refinement is one the source may choose. -/
      have hReg : ∀ T : BitVec w, BitVec.setWidth 64 b.val ||| BitVec.setWidth 64 b.poison &&&
          (BitVec.setWidth 64 b'.val ||| BitVec.setWidth 64 b'.poison &&& BitVec.setWidth 64 T) =
          BitVec.setWidth 64 b'.val ||| BitVec.setWidth 64 b'.poison &&& BitVec.setWidth 64 T := by
        intro T
        have := congrArg (BitVec.setWidth 64) (LLVM.Byte.resolve_of_isRefinedBy hb T)
        simp only [BitVec.setWidth_or, BitVec.setWidth_and] at this
        exact this
      rcases hT : resType.val <;> (try simp only) <;> first | (simp; done) | skip
      · rename_i t
        by_cases hw : t.bitwidth = w
        · simp only [hw, ↓reduceIte]
          try rw [map_eq_pure_bind, map_eq_pure_bind]
          exact sim_byteToIntCTree hb fun x x' hx =>
            sim_result (by simp [RuntimeValue.isRefinedBy, hx]) hMem
        · simp only [hw, ↓reduceIte]
          exact sim_fail _ _
      · by_cases hp : b.poison = 0
        · obtain rfl := LLVM.Byte.eq_of_isRefinedBy_of_poison_eq_zero hb hp
          simp only [hp]
          exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem
        · simp only [show b.poison ≠ 0#w from hp, ↓reduceIte]
          split
          · next hp' =>
            refine sim_choose_right_map _ b'.val ?_
            have := hReg 0
            simp only [hp', BitVec.setWidth_zero, BitVec.zero_and, BitVec.or_zero] at this
            simp only [this, LLVM.Byte.toReg_eq]
            exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem
          · refine sim_choose_left_map _ fun bits =>
              sim_choose_right_map _ (b'.val ||| (b'.poison &&& bits)) ?_
            simp only [BitVec.setWidth_or, BitVec.setWidth_and, hReg]
            exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem
    | addr p =>
      cases v' <;> simp only [RuntimeValue.isRefinedBy] at hv
      rename_i p'
      rcases hT : resType.val <;> (try simp only) <;> first | (simp; done) | skip
      cases p with
      | poison =>
        simp only [Data.LLVM.Ptr.toInt_poison]
        cases p' with
        | val q =>
          simp only [Data.LLVM.Ptr.toInt_val]
          exact sim_choose_right_map _ q.address.toBitVec
            (sim_result (RuntimeValue.isRefinedBy_refl _) hMem)
        | poison =>
          simp only [Data.LLVM.Ptr.toInt_poison]
          exact sim_choose_left_map _ fun bits => sim_choose_right_map _ bits
            (sim_result (RuntimeValue.isRefinedBy_refl _) hMem)
      | val q =>
        cases p' <;> simp only [Data.LLVM.Ptr.isRefinedBy] at hv
        obtain rfl := Data.Pointer.isRefinedBy_iff.mp hv
        simp only [Data.LLVM.Ptr.toInt_val]
        exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem
    | reg r =>
      obtain rfl := RuntimeValue.reg_of_isRefinedBy hv
      rcases hT : resType.val <;> (try simp only) <;> try simp
      all_goals first
        | exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem
        | exact OperationResult.isRefinedBy_def.mpr
            ⟨by simp, hMem, ControlFlowAction.optionIsRefinedBy_refl _⟩
    | _ => rcases resType.val <;> simp

end Veir.CTree

end
