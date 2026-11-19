module

public import Veir.Interpreter.CTreeRefinement.Monotone
public import Veir.Dialects.Builtin.ResultsConform

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.Builtin.Interpreter
import Veir.Data.LLVM.Byte.Lemmas
import Veir.Interpreter.Refinement.Lemmas

public section

/-!
# Monotonicity of the builtin opcodes in CTrees

`builtin.unrealized_conversion_cast` casts between values and registers, which cannot be poison:
casting poison, or a byte with poison bits, to a register chooses the bits that are poison, and
casting a byte to an integer chooses the bits that are poison unless all of them are. A refined
operand has less poison, so the source can choose what the target has. The other builtin opcodes
fail. The types of the results come from `ResultsConform`.
-/

open CTree

namespace Veir.CTree

/-- A tree that returns a result may return it. -/
private theorem mayReturn_pure {α : Type} (r : α) : MayReturn (pure r : Tree α) r :=
  (MayReturn.pure_iff _ _).mpr rfl

/-- A tree may return what its continuation returns on a value its first part may return. -/
private theorem mayReturn_bind {t : Tree α} {k : α → Tree β} {x : α} (hx : MayReturn t x) {r : β}
    (h : MayReturn (k x) r) : MayReturn (t >>= k) r := by
  rw [tree_bind_eq]
  exact (MayReturn.bind_iff _ _ _).mpr ⟨x, hx, h⟩

theorem sim_choose_left_map {RR : α → β → Prop} (i : FreezeCIn) {f : FreezeC i → α}
    {s : Tree β} (h : ∀ x, EqSim RR (pure (f x) : Tree α) s) :
    EqSim RR (f <$> (CTree.choose (E := ErrorE ⊕ₑ UBE) (SubC := FreezeC) i : Tree (FreezeC i))) s := by
  rw [map_eq_pure_bind]
  exact sim_choose_left i h

theorem sim_choose_right_map {RR : α → β → Prop} (i : FreezeCIn) {f : FreezeC i → β}
    {t : Tree α} (x : FreezeC i) (h : EqSim RR t (pure (f x) : Tree β)) :
    EqSim RR t (f <$> (CTree.choose (E := ErrorE ⊕ₑ UBE) (SubC := FreezeC) i : Tree (FreezeC i))) := by
  rw [map_eq_pure_bind]
  exact sim_choose_right i x h

/-- A tree that maps a choice may return the image of any choice. -/
private theorem mayReturn_choose_map {i : FreezeCIn} {f : FreezeC i → α} (x : FreezeC i) :
    MayReturn (f <$> (CTree.choose (E := ErrorE ⊕ₑ UBE) (SubC := FreezeC) i : Tree (FreezeC i)))
      (f x) := by
  rw [map_eq_pure_bind]
  exact mayReturn_choose_bind x (mayReturn_pure _)

/-- Casting a byte whose bits are all poison to an integer gives poison. -/
private theorem mayReturn_byteToIntCTree_poison {w : Nat} {b : Data.LLVM.Byte w}
    (h : b.poison = BitVec.allOnes w) :
    MayReturn (Builtin.byteToIntCTree b : Tree (Data.LLVM.Int w)) .poison := by
  simp only [Builtin.byteToIntCTree, h, ↓reduceIte]
  exact mayReturn_pure _

/-- Casting a byte with a bit that is not poison to an integer may fill its poison bits with
any bits. -/
private theorem mayReturn_byteToIntCTree_val {w : Nat} {b : Data.LLVM.Byte w}
    (h : ¬ b.poison = BitVec.allOnes w) (bits : FreezeC.{0} (.mk w)) :
    MayReturn (Builtin.byteToIntCTree b : Tree (Data.LLVM.Int w)) (.val (b.fillPoison bits)) := by
  simp only [Builtin.byteToIntCTree, h, ↓reduceIte]
  exact mayReturn_choose_bind bits (mayReturn_pure _)

/--
Casting a byte and its refinement to integers: whatever the target chooses for its poison bits,
the source can choose to give a refined integer.
-/
theorem sim_byteToIntCTree {w : Nat} {b b' : Data.LLVM.Byte w} (hb : b ⊒ b') {RR : α → β → Prop}
    {k : Data.LLVM.Int w → Tree β} {k' : Data.LLVM.Int w → Tree α}
    (hk : ∀ x x', Data.LLVM.Int.isRefinedBy x x' →
      MayReturn (Builtin.byteToIntCTree b' : Tree (Data.LLVM.Int w)) x' →
      EqSim RR (k' x') (k x)) :
    EqSim RR (Builtin.byteToIntCTree b' >>= k') (Builtin.byteToIntCTree b >>= k) := by
  by_cases hp : b.poison = BitVec.allOnes w
  · by_cases hp' : b'.poison = BitVec.allOnes w
    · have h := hk .poison .poison (by simp) (mayReturn_byteToIntCTree_poison hp')
      simpa only [Builtin.byteToIntCTree, hp, hp', ↓reduceIte, LawfulMonad.pure_bind] using h
    · have h := fun (bits : FreezeC.{0} (.mk w)) => hk .poison _ (by simp) (mayReturn_byteToIntCTree_val hp' bits)
      simp only [Builtin.byteToIntCTree, hp, hp', ↓reduceIte, LawfulMonad.bind_assoc,
        LawfulMonad.pure_bind]
      exact sim_choose_left _ h
  · have hp' : ¬ b'.poison = BitVec.allOnes w :=
      fun h => hp (Data.LLVM.Byte.poison_eq_allOnes_of_isRefinedBy hb h)
    have h := fun (bits : FreezeC.{0} (.mk w)) => hk (.val (b.fillPoison (b'.fillPoison bits))) _
      (by simp [Data.LLVM.Byte.fillPoison_of_isRefinedBy hb]) (mayReturn_byteToIntCTree_val hp' bits)
    simp only [Builtin.byteToIntCTree, hp, hp', ↓reduceIte, LawfulMonad.bind_assoc,
      LawfulMonad.pure_bind]
    exact sim_choose_left _ fun bits => sim_choose_right _ (b'.fillPoison bits) (h bits)

/--
A builtin opcode is monotone in CTrees, with the results of the target of the given types
whenever every result it may return is.
-/
private theorem builtin_sim (op : Veir.Builtin) (properties : propertiesOf (OpCode.builtin op))
    (resultTypes : Array TypeAttr) {operands operands' : Array RuntimeValue}
    (blockOperands : Array BlockPtr) {mem mem' : MemoryState} (regions : Array RegionPtr)
    (h : operands ⊒ operands') (hMem : mem ⊒ mem')
    (hTy : ∀ vals m a, MayReturn
      (interpretOp' (.builtin op) properties resultTypes operands' blockOperands mem' regions)
      (vals, m, a) → RuntimeValue.ArrayConforms vals resultTypes) :
    EqSim (fun t s => OperationResult.isRefinedBy s t ∧ RuntimeValue.ArrayConforms t.1 resultTypes)
      (interpretOp' (.builtin op) properties resultTypes operands' blockOperands mem' regions)
      (interpretOp' (.builtin op) properties resultTypes operands blockOperands mem regions) := by
  rw [interpretOp'_regions, interpretOp'_regions] at hTy ⊢
  simp only [interpretOp', Builtin.interpretOpCTree,
    Builtin.interpretUnrealizedConversionCastCTree, Builtin.intToRegCTree,
    Builtin.byteToRegCTree] at hTy ⊢
  cases op <;> try simp
  rcases hr : resultTypes[0]? with _ | resType
  · simp
  simp only [hr] at hTy ⊢
  rcases hs : operands.toList with _ | ⟨v, _ | ⟨_, _⟩⟩
  · rcases resType.val <;> simp
  rotate_left
  · rcases resType.val <;> simp
  obtain ⟨v', hs', hv⟩ := toList_eq_singleton_of_isRefinedBy h hs
  simp only [hs'] at hTy ⊢
  cases v with
  | int w x =>
    obtain ⟨x', rfl, hx⟩ := RuntimeValue.int_of_isRefinedBy hv
    rcases hT : resType.val <;> simp only [hT] at hTy ⊢ <;> first | (simp; done) | skip
    · cases x with
      | val a =>
        obtain rfl : x' = .val a := by
          have := RuntimeValue.int_val_isRefinedBy_iff.mp hv; simpa using this
        simp only [map_eq_pure_bind, pure_bind] at hTy ⊢
        exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem (hTy _ _ _ (mayReturn_pure _))
      | poison =>
        cases x' with
        | val a =>
          simp only [map_eq_pure_bind, LawfulMonad.bind_assoc, pure_bind] at hTy ⊢
          exact sim_choose_right _ (a.setWidth 64)
            (sim_result (RuntimeValue.isRefinedBy_refl _) hMem (hTy _ _ _ (mayReturn_pure _)))
        | poison =>
          simp only [map_eq_pure_bind, LawfulMonad.bind_assoc, pure_bind] at hTy ⊢
          exact sim_choose_left _ fun bits => sim_choose_right _ bits
            (sim_result (RuntimeValue.isRefinedBy_refl _) hMem
              (hTy _ _ _ (mayReturn_choose_bind bits (mayReturn_pure _))))
    · rename_i t
      by_cases hw : t.bitwidth = w
      · simp only [hw, ne_eq, not_true_eq_false, ↓reduceIte] at hTy ⊢
        refine sim_result ?_ hMem (hTy _ _ _ (mayReturn_pure _))
        cases x with
        | poison => simp [RuntimeValue.isRefinedBy]
        | val a =>
          obtain rfl : x' = .val a := by
            have := RuntimeValue.int_val_isRefinedBy_iff.mp hv; simpa using this
          exact RuntimeValue.isRefinedBy_refl _
      · simp only [hw, ↓reduceIte, map_eq_pure_bind, tree_bind_eq, bind_fail]
        exact sim_fail _ _
  | byte w b =>
    obtain ⟨b', rfl, hb⟩ := RuntimeValue.byte_of_isRefinedBy hv
    rcases hT : resType.val <;> simp only [hT] at hTy ⊢ <;> first | (simp; done) | skip
    · rename_i t
      by_cases hw : t.bitwidth = w
      · simp only [hw, ne_eq, not_true_eq_false, ↓reduceIte, map_eq_pure_bind] at hTy ⊢
        exact sim_byteToIntCTree hb fun x x' hx hx' =>
          sim_result (by simp [RuntimeValue.isRefinedBy, hx]) hMem
            (hTy _ _ _ (mayReturn_bind hx' (mayReturn_pure _)))
      · simp only [hw, ↓reduceIte, map_eq_pure_bind, tree_bind_eq, bind_fail]
        exact sim_fail _ _
    · by_cases hp : b.poison = 0#w
      · obtain rfl := Data.LLVM.Byte.eq_of_isRefinedBy_of_poison_eq_zero hb hp
        simp only [hp, ↓reduceIte, map_eq_pure_bind, pure_bind] at hTy ⊢
        exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem (hTy _ _ _ (mayReturn_pure _))
      · by_cases hp' : b'.poison = 0#w
        · simp only [hp, hp', ↓reduceIte, map_eq_pure_bind, LawfulMonad.bind_assoc, pure_bind] at hTy ⊢
          refine sim_choose_right _ (b'.fillPoison 0#w) ?_
          rw [Data.LLVM.Byte.fillPoison_of_isRefinedBy hb]
          simp only [Data.LLVM.Byte.fillPoison_eq, BitVec.and_zero, BitVec.or_zero]
          exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem (hTy _ _ _ (mayReturn_pure _))
        · simp only [hp, hp', ↓reduceIte, map_eq_pure_bind, LawfulMonad.bind_assoc, pure_bind] at hTy ⊢
          refine sim_choose_left _ fun bits => sim_choose_right _ (b'.fillPoison bits) ?_
          rw [Data.LLVM.Byte.fillPoison_of_isRefinedBy hb]
          exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem
            (hTy _ _ _ (mayReturn_choose_bind _ (mayReturn_pure _)))
  | addr p =>
    cases v' <;> simp only [RuntimeValue.isRefinedBy] at hv
    rename_i p'
    rcases hT : resType.val <;> simp only [hT] at hTy ⊢ <;> first | (simp; done) | skip
    cases p with
    | poison =>
      simp only [Data.LLVM.Ptr.toInt_poison]
      cases p' with
      | val q =>
        simp only [Data.LLVM.Ptr.toInt_val] at hTy ⊢
        exact sim_choose_right_map _ q.address.toBitVec
          (sim_result (RuntimeValue.isRefinedBy_refl _) hMem (hTy _ _ _ (mayReturn_pure _)))
      | poison =>
        simp only [Data.LLVM.Ptr.toInt_poison] at hTy ⊢
        exact sim_choose_left_map _ fun bits => sim_choose_right_map _ bits
          (sim_result (RuntimeValue.isRefinedBy_refl _) hMem
            (hTy _ _ _ (mayReturn_choose_map bits)))
    | val q =>
      cases p' <;> simp only [Data.LLVM.Ptr.isRefinedBy] at hv
      obtain rfl := Data.Pointer.isRefinedBy_iff.mp hv
      simp only [Data.LLVM.Ptr.toInt_val] at hTy ⊢
      exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem (hTy _ _ _ (mayReturn_pure _))
  | reg r =>
    obtain rfl := RuntimeValue.reg_of_isRefinedBy hv
    rcases hT : resType.val <;> simp only [hT, MemoryState.ptrFromInt_val] at hTy ⊢ <;>
      first | (simp; done) | skip
    all_goals exact sim_result (RuntimeValue.isRefinedBy_refl _) hMem (hTy _ _ _ (mayReturn_pure _))
  | _ => rcases resType.val <;> simp

end Veir.CTree

namespace Veir

/-- Every builtin opcode whose results conform meets its CTree monotonicity obligation. -/
theorem OpCode.interpretCTree_monotone_builtin (op : Builtin)
    [Veir.ResultsConform (.builtin op)] : OpCode.interpretCTree_monotone (.builtin op) :=
  .of_sim fun properties resultTypes _ _ blockOperands _ _ regions h hMem hTy =>
    CTree.builtin_sim op properties resultTypes blockOperands regions h hMem hTy

instance (op : Builtin) [ResultsConform (.builtin op)] : InterpretCTreeMonotone (.builtin op) :=
  ⟨OpCode.interpretCTree_monotone_builtin op⟩

end Veir

end
