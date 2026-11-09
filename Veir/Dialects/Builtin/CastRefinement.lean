module

public import Veir.Dialects.Builtin.Interpreter
public import Veir.Interpreter.Refinement.Basic
import all Veir.Dialects.Builtin.Interpreter
import all Veir.Data.LLVM.Byte.Basic
import all Veir.Data.LLVM.Int.Bitblast
import all Veir.IR.Attribute
import all Veir.Data.Casting

namespace Veir.Builtin

public section

open Veir.Data

/-- Fully poisoned bytes retain integer poison. -/
@[simp]
theorem byteToIntCTree_allPoison {EIn : Type} {E : EIn → Type} (width : Nat) :
    byteToIntCTree (E := E) (LLVM.Byte.allPoison : LLVM.Byte width) = pure (.poison) := by
  simp [byteToIntCTree, LLVM.Byte.allPoison]

/-- A byte with no poison has exactly its concrete integer as a successful outcome. -/
theorem byteToIntCTree_concrete (value : LLVM.Byte width)
    (hzero : value.poison = 0) (hwidth : 0 < width) (result : LLVM.Int width) :
    PureOrErr.CanInterpretTo (byteToIntCTree (E := ErrorE ⊕ₑ _root_.CTree.UBE) value)
      (.ok result) ↔ result = .val value.val := by
  simp [byteToIntCTree, hzero, Nat.ne_of_gt hwidth,
    PureOrErr.CanInterpretTo.map_iff, PureOrErr.CanInterpretTo.choose_iff]

/-- Integer-to-byte-to-integer casts preserve both concrete integer outcomes and poison. -/
theorem byteToIntCTree_fromInt (value result : LLVM.Int width) (hwidth : 0 < width) :
    PureOrErr.CanInterpretTo
      (byteToIntCTree (E := ErrorE ⊕ₑ _root_.CTree.UBE) (LLVM.Byte.fromInt value))
      (.ok result) ↔ result = value := by
  cases value with
  | poison => simp [LLVM.Byte.fromInt, byteToIntCTree]
  | val value => exact byteToIntCTree_concrete _ rfl hwidth result

/-- Every filling of a byte that is not fully poisoned is an admitted result. -/
theorem byteToIntCTree_canInterpret_partial (value : LLVM.Byte width)
    (hfull : value.poison ≠ BitVec.allOnes width)
    (bits : BitVec width) :
    PureOrErr.CanInterpretTo (byteToIntCTree (E := ErrorE ⊕ₑ _root_.CTree.UBE) value)
      (.ok (.val (value.val ||| (value.poison &&& bits)))) := by
  simp only [byteToIntCTree, hfull, ↓reduceIte]
  apply (PureOrErr.CanInterpretTo.bind_iff _ _ _).mpr
  left
  exact ⟨bits, (PureOrErr.CanInterpretTo.choose_iff _ _).mpr ⟨bits, rfl⟩, .ret _⟩

/-- Regression: the low poisoned bit may be one, rather than being forced to zero. -/
theorem byteToIntCTree_partialPoison_admits_one :
    PureOrErr.CanInterpretTo
      (byteToIntCTree (E := ErrorE ⊕ₑ _root_.CTree.UBE) (⟨0, 1, by decide⟩ : LLVM.Byte 2))
      (.ok (.val 1)) := by
  simpa using byteToIntCTree_canInterpret_partial (⟨0, 1, by decide⟩ : LLVM.Byte 2)
    (by decide) 1

/-- The opcode delegates its byte-to-integer branch to the nondeterministic cast. -/
theorem interpretOpCTree_byteToInt (value : LLVM.Byte width) (memory : MemoryState) :
    Builtin.interpretOpCTree (E := ErrorE ⊕ₑ _root_.CTree.UBE) .unrealized_conversion_cast ()
      #[⟨.integerType (.signless width), by rfl⟩] #[.byte width value] #[] memory =
      (do let result ← byteToIntCTree value
          pure (#[.int width result], memory, none) :
        Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction)) := by
  cbv

/-- Regression on the actual cast opcode: a defined target value of one remains available. -/
theorem interpretOpCTree_partialPoison_admits_one (memory : MemoryState) :
    PureOrErr.CanInterpretTo
      (Builtin.interpretOpCTree (E := ErrorE ⊕ₑ _root_.CTree.UBE) .unrealized_conversion_cast ()
        #[⟨.integerType (.signless 2), by rfl⟩]
        #[.byte 2 (⟨0, 1, by decide⟩ : LLVM.Byte 2)] #[] memory)
      (.ok (#[.int 2 (.val 1)], memory, none)) := by
  rw [interpretOpCTree_byteToInt]
  apply (PureOrErr.CanInterpretTo.bind_iff _ _ _).mpr
  exact .inl ⟨.val 1, byteToIntCTree_partialPoison_admits_one, .ret _⟩

/-- Refinement preserves every concretization of the target's remaining poison bits. -/
theorem byte_concretize_of_refinement (source target : LLVM.Byte width)
    (href : source ⊒ target) (bits : BitVec width) :
    source.val ||| (source.poison &&& (target.val ||| (target.poison &&& bits))) =
      target.val ||| (target.poison &&& bits) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hr := congrArg (fun v : BitVec width => v.getLsbD i) href
  have hs := congrArg (fun v : BitVec width => v.getLsbD i) source.h
  have ht := congrArg (fun v : BitVec width => v.getLsbD i) target.h
  simp only [LLVM.Byte.isRefinedBy, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_xor, BitVec.getLsbD_not, BitVec.getLsbD_allOnes,
    hi, decide_true] at *
  generalize source.val.getLsbD i = sv at *
  generalize source.poison.getLsbD i = sp at *
  generalize target.val.getLsbD i = tv at *
  generalize target.poison.getLsbD i = tp at *
  generalize bits.getLsbD i = choice at *
  cases sv <;> cases sp <;> cases tv <;> cases tp <;> cases choice <;> simp_all

/-- A target byte can retain poison only where the source was already poisoned. -/
theorem byte_poison_mask_of_refinement (source target : LLVM.Byte width) (href : source ⊒ target) :
    source.poison &&& target.poison = target.poison := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hr := congrArg (fun v : BitVec width => v.getLsbD i) href
  simp only [LLVM.Byte.isRefinedBy, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_xor, BitVec.getLsbD_not, BitVec.getLsbD_allOnes,
    hi, decide_true] at *
  generalize source.val.getLsbD i = sv at *
  generalize source.poison.getLsbD i = sp at *
  generalize target.val.getLsbD i = tv at *
  generalize target.poison.getLsbD i = tp at *
  cases sv <;> cases sp <;> cases tv <;> cases tp <;> simp_all

/-- Each target integer outcome has a refining source outcome after byte refinement. -/
theorem byteToIntCTree_outcome_monotone (source target : LLVM.Byte width) (href : source ⊒ target)
    (result : LLVM.Int width)
    (hresult : PureOrErr.CanInterpretTo
      (byteToIntCTree (E := ErrorE ⊕ₑ _root_.CTree.UBE) target) (.ok result)) :
    ∃ sourceResult, PureOrErr.CanInterpretTo
      (byteToIntCTree (E := ErrorE ⊕ₑ _root_.CTree.UBE) source) (.ok sourceResult) ∧ sourceResult ⊒ result := by
  have hm := byte_poison_mask_of_refinement source target href
  by_cases hsfull : source.poison = BitVec.allOnes width
  · refine ⟨.poison, ?_, ?_⟩
    · simp [byteToIntCTree, hsfull]
    · simp
  · have htfull : target.poison ≠ BitVec.allOnes width := by
      intro hfull
      simp only [hfull, BitVec.and_allOnes] at hm
      exact hsfull hm
    have hout : ∃ bits : BitVec width, result = .val (target.val ||| (target.poison &&& bits)) := by
      simp only [byteToIntCTree, htfull, ↓reduceIte] at hresult
      have hr := (PureOrErr.CanInterpretTo.bind_iff _ _ _).mp hresult
      simpa [PureOrErr.CanInterpretTo.choose_iff] using hr
    obtain ⟨bits, rfl⟩ := hout
    refine ⟨.val (target.val ||| (target.poison &&& bits)), ?_, ?_⟩
    · have hw := byteToIntCTree_canInterpret_partial source hsfull
        (target.val ||| (target.poison &&& bits))
      simpa only [byte_concretize_of_refinement source target href bits] using hw
    · simp

private theorem sim_pure_of_outcome {α β : Type} (relation : α → β → Prop)
    {source : Tree β} {sourceValue : β} (targetValue : α)
    (h : PureOrErr.CanInterpretTo source (.ok sourceValue))
    (hrel : relation targetValue sourceValue) :
    _root_.CTree.Sim relation (pure targetValue : Tree α) source := by
  generalize heq : Interp.ok sourceValue = outcome at h
  induction h with
  | ret value => cases heq; exact (_root_.CTree.Sim.pure _ _ _).mpr hrel
  | tau choice next selected result h ih =>
    exact _root_.CTree.Sim.tau_r relation choice _ next selected (ih heq)
  | fail => cases heq
  | ub => cases heq

/-- The byte-to-integer CTree cast is monotone in the byte refinement ordering. -/
theorem byteToIntCTree_monotone (source target : LLVM.Byte width) (href : source ⊒ target) :
    _root_.CTree.Sim (fun (target source : LLVM.Int width) => source ⊒ target)
      (byteToIntCTree (E := ErrorE ⊕ₑ _root_.CTree.UBE) target)
      (byteToIntCTree (E := ErrorE ⊕ₑ _root_.CTree.UBE) source) := by
  have hsim (result : LLVM.Int width)
      (hresult : PureOrErr.CanInterpretTo
        (byteToIntCTree (E := ErrorE ⊕ₑ _root_.CTree.UBE) target) (.ok result)) :
      _root_.CTree.Sim (fun (target source : LLVM.Int width) => source ⊒ target)
        (pure result : Tree (LLVM.Int width)) (byteToIntCTree source) := by
    obtain ⟨value, hvalue, hrefine⟩ := byteToIntCTree_outcome_monotone source target href result hresult
    exact sim_pure_of_outcome _ result hvalue hrefine
  by_cases hfull : target.poison = BitVec.allOnes width
  · have heq : byteToIntCTree (E := ErrorE ⊕ₑ _root_.CTree.UBE) target = pure (.poison) := by
      simp only [byteToIntCTree, hfull, ↓reduceIte]
    rw [heq]
    apply hsim
    rw [heq]
    exact .ret _
  · have heq : byteToIntCTree (E := ErrorE ⊕ₑ _root_.CTree.UBE) target =
        (do let bits : BitVec width ← _root_.CTree.CTree.choose (SubC := FreezeC) (FreezeCIn.mk width)
            pure (.val (target.val ||| (target.poison &&& bits)))) := by
      simp only [byteToIntCTree, hfull, ↓reduceIte]
    rw [heq]
    simp only [_root_.CTree.CTree.choose_def, _root_.CTree.CTree.tau_def, Bind.bind,
      _root_.CTree.CTree.bind_tau, _root_.CTree.CTree.bind_ret,
      _root_.CTree.Sim.tau_l]
    intro bits
    exact hsim _ (byteToIntCTree_canInterpret_partial target hfull bits)

end

end Veir.Builtin
