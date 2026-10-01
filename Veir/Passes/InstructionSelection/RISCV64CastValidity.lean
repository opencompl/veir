module

public meta import Veir.PatternRewriter.Puddle.Definitions
public meta import Veir.PatternRewriter.Puddle.Validity
public import Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.Passes.InstructionSelection.RISCV64
public import Veir.Passes.InstructionSelection.RISCV64CTreeSemantics
import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.PatternRewriter.Puddle.CTreeValidity
import all Veir.PatternRewriter.Puddle.Validity
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Interpreter.CTree
import all Veir.IR.Attribute
import all Veir.OpCode
import all Veir.GlobalOpInfo
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.LLVM.Properties
import all Veir.Dialects.Builtin.OpInfo
import all Veir.Data.Casting
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Interpreter.Basic
import all Veir.Data.RISCV.Reg.Basic
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.LLVM.Byte.Basic
import all Veir.IR.OpInfo
import all Veir.PatternRewriter.Puddle.CreationM

namespace Veir
open Puddle Puddle.CTree
set_option backward.isDefEq.respectTransparency false

namespace Puddle.CTree

@[simp] theorem CanInterpretTo.constant_int (ty : IntegerType) (attr : IntegerAttr)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .mlir__constant) { value := .integer attr }
      #[TypeAttr.of IntegerType ty] #[] results ↔
    results = .ok #[.int ty.bitwidth (.val (match attr.type.bitwidth with
      | 1 => (BitVec.ofInt attr.type.bitwidth attr.value).zeroExtend ty.bitwidth
      | _ => (BitVec.ofInt attr.type.bitwidth attr.value).signExtend ty.bitwidth))] := by
  unfold CanInterpretTo
  change (∀ memory : MemoryState, PureOrErr.CanInterpretTo (E := ErrorE ⊕ₑ UBE) (C := FreezeC)
    (pure (#[.int ty.bitwidth (.val (match attr.type.bitwidth with
      | 1 => (BitVec.ofInt attr.type.bitwidth attr.value).zeroExtend ty.bitwidth
      | _ => (BitVec.ofInt attr.type.bitwidth attr.value).signExtend ty.bitwidth))], memory, none))
    (results.map (·, memory, none))) ↔ _
  cases results <;> simp

@[simp] theorem CanInterpretTo.freeze_int (ty : IntegerType)
    (value : Data.LLVM.Int ty.bitwidth) (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .freeze) () #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth value] results ↔
    ∃ v : BitVec ty.bitwidth, (value = .poison ∨ value = .val v) ∧
      results = .ok #[.int ty.bitwidth (.val v)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, bind_pure_comp, Functor.map]
  cases value <;> cases results <;> simp [PureOrErr.CanInterpretTo.bind_iff]

end Puddle.CTree

theorem freeze_pattern_valid : Puddle.CTree.Pattern.Valid freeze_pattern := by
  unfold freeze_pattern lowerCast castToReg castFromReg
  provePuddleValid
  simp only [TypeAttr.of_typeAttr]
  intro src x hx hs dst y hy hd value hv property heq
  subst x
  subst y
  cases heq
  rcases src with ⟨attr, ht⟩
  cases attr <;> simp only [Bool.false_eq_true] at hs
  rename_i ty
  change value.Conforms (TypeAttr.of IntegerType ty) at hv
  obtain ⟨iv, rfl⟩ := RuntimeValue.Conforms.integerType.mp hv
  cases property
  cases iv <;> simp [RISCV.Reg.toInt, TypeAttr.mk_of]
  · have hwidth : ty.bitwidth = 32 ∨ ty.bitwidth = 64 := of_decide_eq_true hs
    have width : ty.bitwidth ≤ 64 := by omega
    rw [BitVec.setWidth_setWidth_of_le _ width]
    simp
  · intro bits
    refine ⟨.ok #[.int ty.bitwidth (.val (bits.setWidth ty.bitwidth))], ?_, ?_⟩
    · exact ⟨_, rfl⟩
    · simp

namespace Puddle.CTree

@[simp] theorem CanInterpretTo.li_reg (props : RISCVImmediateProperties)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.riscv .li) props #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[] results ↔ results = .ok #[.reg ⟨props.value⟩] := by
  apply CanInterpretTo.riscv_pure
  intro memory
  rfl

@[simp] theorem CanInterpretTo.poison_int (ty : IntegerType)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .mlir__poison) () #[TypeAttr.of IntegerType ty] #[] results ↔
      results = .ok #[.int ty.bitwidth .poison] := by
  unfold CanInterpretTo
  change (∀ memory, PureOrErr.CanInterpretTo
    (pure (#[.int ty.bitwidth .poison], memory, none))
    (results.map (·, memory, none))) ↔ _
  cases results <;> simp

end Puddle.CTree

theorem constant_ctree_bits_eq_decode (w : Nat) (attr : IntegerAttr) :
    (match attr.type.bitwidth with
    | 1 => (BitVec.ofInt attr.type.bitwidth attr.value).zeroExtend w
    | _ => (BitVec.ofInt attr.type.bitwidth attr.value).signExtend w) =
      BitVec.ofInt w (decodeLLVMIntegerConstant attr) := by
  unfold decodeLLVMIntegerConstant
  split
  · rename_i h
    simp only [h, ↓reduceIte, BitVec.zeroExtend]
    rw [h, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  · rename_i h
    simp only [BitVec.signExtend]
    rw [ite_eq_right h]

theorem ofInt_toInt_setWidth_le64 (w : Nat) (h : w ≤ 64) (x : BitVec w) :
    (BitVec.ofInt 64 x.toInt).setWidth w = x := by
  change (x.signExtend 64).setWidth w = x
  rw [← BitVec.signExtend_eq_setWidth_of_le _ h]
  change BitVec.ofInt w (x.signExtend 64).toInt = x
  rw [BitVec.toInt_signExtend_of_le h, BitVec.ofInt_toInt]

theorem constant_pattern_valid : Puddle.CTree.Pattern.Valid constant_pattern := by
  unfold constant_pattern castFromReg
  provePuddleValid
  intro ty it heq hwidth property hp
  cases heq
  rcases property with ⟨prop⟩
  cases prop <;> simp only [Bool.false_eq_true] at hp
  rename_i attr
  have decode : constantIntValue (TypeAttr.of IntegerType it) { value := .integer attr } =
      some ((BitVec.ofInt it.bitwidth (decodeLLVMIntegerConstant attr)).toInt) := rfl
  simp only [decode]
  simp [RISCV.Reg.toInt, SemanticAssignment.bind]
  rw [constant_ctree_bits_eq_decode]
  have roundtrip := ofInt_toInt_setWidth_le64 it.bitwidth hwidth
    (BitVec.ofInt it.bitwidth (decodeLLVMIntegerConstant attr))
  simp only [BitVec.toInt_ofInt] at roundtrip
  rw [roundtrip]
  simp

private theorem fail_not_ok {CIn R} {C : CIn → Type} (r : R) :
    ¬ PureOrErr.CanInterpretTo (fail : _root_.CTree.CTree (ErrorE ⊕ₑ UBE) C R) (.ok r) := by
  intro h
  generalize heq : (fail : _root_.CTree.CTree (ErrorE ⊕ₑ UBE) C R) = t at h
  cases h <;> have hhead := congrArg _root_.CTree.CTree.unfold heq <;>
    simp [fail, _root_.CTree.CTree.trigger, _root_.CTree.unfold_vis,
      _root_.CTree.unfold_tauG] at hhead

private theorem cast_reg_ok_size (ty : TypeAttr) (reg : Data.RISCV.Reg)
    (values : Array RuntimeValue)
    (h : CanInterpretTo (.builtin .unrealized_conversion_cast) () #[ty] #[.reg reg] (.ok values)) :
    values.size = 1 := by
  have hm := h MemoryState.empty
  rcases ty with ⟨attr, ht⟩
  cases attr <;> simp only [Attribute.isType, Bool.false_eq_true] at ht
  all_goals first
    | change PureOrErr.CanInterpretTo (pure (_, MemoryState.empty, none))
        (.ok (values, MemoryState.empty, none)) at hm
    | change PureOrErr.CanInterpretTo fail (.ok (values, MemoryState.empty, none)) at hm
  all_goals first
    | exact False.elim (fail_not_ok _ hm)
    | have eq := (PureOrErr.CanInterpretTo.pure_iff _ _).mp hm
      cases eq
      rfl

theorem poisonConst_pattern_valid : Puddle.CTree.Pattern.Valid poisonConst_pattern := by
  unfold poisonConst_pattern emitImm emitRISCV castFromReg
  provePuddleValid
  simp only [TypeAttr.of_typeAttr]
  simp only [Riscv.propertiesOf, CanInterpretTo.li_reg]
  simpPuddlePlumbing
  simp [SemanticAssignment.bind]
  intro ty property
  cases property
  constructor
  · intro values h
    exact (cast_reg_ok_size ty _ values h).symm
  · intro target h
    rcases ty with ⟨attr, ht⟩
    cases attr <;> simp only [Attribute.isType, Bool.false_eq_true] at ht
    all_goals first
      | refine ⟨.fail none, ?_, by trivial⟩
        intro memory
        change PureOrErr.CanInterpretTo fail (.fail none)
        simp [fail, _root_.CTree.CTree.trigger]
        exact .fail
      | skip
    case integerType ty ht0 =>
      change ∃ source, CanInterpretTo (.llvm .mlir__poison) ()
        #[TypeAttr.of IntegerType ty] #[] source ∧
        Interp.isRefinedBy RuntimeValue.arrayIsRefinedBy source target
      change _ at h
      simp [SemanticAssignment.bind] at h
      subst target
      refine ⟨.ok #[.int ty.bitwidth .poison], ?_, ?_⟩
      · simp
      · simp [RuntimeValue.isRefinedBy, RISCV.Reg.toInt, isRefinedBy]
    case llvmPointerType ty ht0 =>
      rcases h with ⟨a, ⟨values, hv, rfl⟩, ha⟩ | ⟨op, hv, rfl⟩ | ⟨op, hv, rfl⟩
      · simp [SemanticAssignment.bind] at ha
        subst target
        have hm := hv MemoryState.empty
        change PureOrErr.CanInterpretTo (pure (_, MemoryState.empty, none))
          (.ok (values, MemoryState.empty, none)) at hm
        have heq := (PureOrErr.CanInterpretTo.pure_iff _ _).mp hm
        cases heq
        refine ⟨.ok #[.addr .poison], ?_, ?_⟩
        · intro memory
          change PureOrErr.CanInterpretTo (pure (#[RuntimeValue.addr .poison], memory, none))
            (.ok (#[RuntimeValue.addr .poison], memory, none))
          exact .ret _
        · simp [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy]
      all_goals have hm := hv MemoryState.empty
      all_goals change PureOrErr.CanInterpretTo (pure (_, MemoryState.empty, none)) _ at hm
      all_goals simp at hm

namespace Puddle.CTree

@[simp]
theorem CanInterpretTo.cast_byte_value (w : Nat) (value : Data.LLVM.Byte w)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of RegisterType {}] #[.byte w value] results ↔
      ∃ bits : BitVec w, results = .ok #[.reg ⟨(value.val ||| (value.poison &&& bits)).zeroExtend 64⟩] := by
  unfold CanInterpretTo
  change (∀ memory : MemoryState, PureOrErr.CanInterpretTo
      (if value.poison = 0 then pure (#[.reg (LLVM.Byte.toReg value)], memory, none) else
        CTree.bind (CTree.CTree.choose (E := ErrorE ⊕ₑ UBE) (C := FreezeC) (SubC := FreezeC) (FreezeCIn.mk w))
          (fun bits => pure (#[.reg ⟨(value.val ||| (value.poison &&& bits)).zeroExtend 64⟩], memory, none)))
      (results.map (·, memory, none))) ↔ _
  cases results <;> by_cases h : value.poison = 0
  all_goals simp only [h, ↓reduceIte, Interp.map]
  all_goals simp [LLVM.Byte.toReg, PureOrErr.CanInterpretTo.bind_iff]

@[simp]
theorem CanInterpretTo.cast_reg_byte_value (ty : LLVM.ByteType) (value : Data.RISCV.Reg)
    (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of LLVM.ByteType ty] #[.reg value] results ↔
      results = .ok #[.byte ty.bitwidth (RISCV.Reg.toByte value ty.bitwidth)] := by
  unfold CanInterpretTo
  change (∀ memory, PureOrErr.CanInterpretTo (pure (#[.byte ty.bitwidth (RISCV.Reg.toByte value ty.bitwidth)], memory, none))
    (results.map (·, memory, none))) ↔ _
  cases results <;> simp

end Puddle.CTree

theorem trunc_pattern_valid : Puddle.CTree.Pattern.Valid trunc_pattern := by
  unfold trunc_pattern lowerCast castToReg castFromReg
  provePuddleValid
  simp only [TypeAttr.of_typeAttr]
  intro src x hx hs dst y hy hd value hv property hg
  subst x
  subst y
  rcases src with ⟨srcAttr, hsrc⟩
  rcases dst with ⟨dstAttr, hdst⟩
  cases srcAttr <;> simp only [getIntByteTypeBitwidth, Option.isSome, Bool.false_eq_true] at hs
  all_goals cases dstAttr <;>
    simp only [getIntByteTypeBitwidth, Option.isSome, Bool.false_eq_true,
      Bool.false_and, Bool.true_and] at hd hg
  case integerType.integerType dst =>
    rename_i src
    have widths := of_decide_eq_true hg
    change value.Conforms (TypeAttr.of IntegerType src) at hv
    obtain ⟨iv, rfl⟩ := RuntimeValue.Conforms.integerType.mp hv
    cases iv <;> simp [RISCV.Reg.toInt, TypeAttr.mk_of]
    case val bits =>
      rw [BitVec.setWidth_setWidth_of_le _ (by omega)]
      refine ⟨.ok #[.int dst.bitwidth (Data.LLVM.Int.trunc (.val bits) dst.bitwidth
        property.nsw property.nuw widths.1)], ?_, ?_⟩
      · intro memory
        change PureOrErr.CanInterpretTo
          (if dst.bitwidth ≥ src.bitwidth then fail else
            pure (#[RuntimeValue.int dst.bitwidth
              (Data.LLVM.Int.trunc (.val bits) dst.bitwidth property.nsw property.nuw widths.1)], memory, none))
          (.ok (#[RuntimeValue.int dst.bitwidth
              (Data.LLVM.Int.trunc (.val bits) dst.bitwidth property.nsw property.nuw widths.1)], memory, none))
        simp only [show ¬ dst.bitwidth ≥ src.bitwidth by omega, ↓reduceIte]
        exact .ret _
      · simp [RuntimeValue.isRefinedBy, Data.LLVM.Int.trunc, Id.run]
        split
        · exact True.intro
        · split <;> first | exact True.intro | rfl
    case poison =>
      intro bits
      refine ⟨.ok #[.int dst.bitwidth .poison], ?_, ?_⟩
      · intro memory
        change PureOrErr.CanInterpretTo
          (if dst.bitwidth ≥ src.bitwidth then fail else
            pure (#[RuntimeValue.int dst.bitwidth .poison], memory, none))
          (.ok (#[RuntimeValue.int dst.bitwidth .poison], memory, none))
        simp only [show ¬ dst.bitwidth ≥ src.bitwidth by omega, ↓reduceIte]
        exact .ret _
      · simp [RuntimeValue.isRefinedBy, isRefinedBy]
  case byteType.byteType dst =>
    rename_i src
    have widths := of_decide_eq_true hg
    change value.Conforms (TypeAttr.of LLVM.ByteType src) at hv
    obtain ⟨bv, rfl⟩ := RuntimeValue.Conforms.byteType.mp hv
    simp [TypeAttr.mk_of]
    intro bits
    refine ⟨.ok #[.byte dst.bitwidth (Data.LLVM.Byte.trunc bv dst.bitwidth)], ?_, ?_⟩
    · intro memory
      change PureOrErr.CanInterpretTo
        (if dst.bitwidth ≥ src.bitwidth then fail else
          pure (#[RuntimeValue.byte dst.bitwidth (Data.LLVM.Byte.trunc bv dst.bitwidth)], memory, none))
        (.ok (#[RuntimeValue.byte dst.bitwidth (Data.LLVM.Byte.trunc bv dst.bitwidth)], memory, none))
      simp only [show ¬ dst.bitwidth ≥ src.bitwidth by omega, ↓reduceIte]
      exact .ret _
    · simp [RuntimeValue.isRefinedBy, RISCV.Reg.toByte, Data.LLVM.Byte.trunc]
      simp only [BitVec.setWidth_setWidth_of_le _ (show dst.bitwidth ≤ 64 by omega)]
      apply BitVec.eq_of_getLsbD_eq
      intro i
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_not,
        BitVec.getLsbD_and, BitVec.getLsbD_allOnes]
      by_cases hi : i < dst.bitwidth
      · simp only [hi]
        intro _
        cases (bv.val.setWidth dst.bitwidth).getLsbD i <;>
          cases (bv.poison.setWidth dst.bitwidth).getLsbD i <;>
          cases (bits.setWidth dst.bitwidth).getLsbD i <;> rfl
      · simp [hi]

end Veir
