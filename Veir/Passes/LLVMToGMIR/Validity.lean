module

public import Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.PatternRewriter.Puddle.CTreeProofs
public import Veir.Passes.LLVMToGMIR
import all Veir.Passes.Legalization.Validity.Common
import all Veir.Passes.LLVMToGMIR
import all Veir.Passes.LLVMToGMIR.Remaining
import all Veir.Passes.Legalization.LegalizerInfo
import all Veir.Passes.InstructionSelection.Common
import Veir.DataLayout.RISCV64
import all Veir.Interfaces.DataLayoutInterfaces
import all Veir.Dialects.LLVM.Properties
import all Veir.Dialects.GMIR.Properties
import all Veir.Interpreter.Memory
import all Veir.Interpreter.RuntimeValue.Conforms
import all Veir.Passes.CastsReconciliation.Reconciliation
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.GMIR.Semantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Dialects.Builtin.Interpreter
import all Veir.Dialects.Builtin.OpInfo
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Byte.Basic
import all Veir.Data.Casting
import all Veir.Data.Refinement
import all Init.Data.Array.Basic

/-!
# CTree validity of the LLVM to gMIR translation

`llvmToGMIRCertificates` holds a certificate for every Puddle pattern of `llvm-to-gmir`, in the
order of `llvmToGMIRPatternList`: a proof of `Puddle.CTree.Pattern.Valid`, or the reason why there
is none. Its type is indexed by the list, so changing the patterns of the pass without updating
the certificates does not build. The local rewrite of the GEP indices is not a Puddle pattern, and
the branches are translated by a separate step (`convertLLVMBranches`).

The unproven patterns (see `Unproven`):
* The byte shifts (`allPoisonByte`): an all-poison byte becomes a poison integer, so the shift can
  no longer move defined zero bits in. This is a property of the value, which no matcher can check
  (`byte_shl_frozen` and `byte_lshr_frozen` in `Veir.Passes.LLVMToGMIR.Remaining` prove the other
  bytes).
* The static `alloca` (`staticAlloca`).

The proofs are those of the gMIR legalization rules (`Veir.Passes.Legalization.Validity`), with the
LLVM and builtin interpreters added to the semantics. Most translations interpret the same
`Data.LLVM.Int` operation on both sides and close during normalization; the others close with a
local lemma relating the two interpreters.
-/

namespace Veir.LLVMToGMIR.CTreeProofs

open Puddle
open Puddle.CTree
open _root_.CTree

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  GMIR.interpretOp' GMIR.interpretOpCTree Llvm.interpretOpCTree Llvm.interpretOp' Builtin.interpretOpCTree
  Builtin.interpretUnrealizedConversionCastCTree

attribute [local simp] GMIR.isTerminator GMIR.getEffects Llvm.isTerminator Llvm.getEffects Builtin.getEffects

attribute [local implicit_reducible] TypeAttr

/- The normalization unfolds `Attribute.of` to case on the result types of the builtin casts, which
the lemmas folding each attribute constructor back would undo. -/
attribute [-simp]
  Attribute.floatType_eq_of Attribute.vectorType_eq_of Attribute.tensorType_eq_of Attribute.integerAttr_eq_of
  Attribute.indexAttr_eq_of Attribute.floatAttr_eq_of Attribute.fastMathFlagsAttr_eq_of Attribute.arithIntegerOverflowFlagsAttr_eq_of
  Attribute.cconvAttr_eq_of Attribute.linkageAttr_eq_of Attribute.framePointerKindAttr_eq_of Attribute.uwtableKindAttr_eq_of
  Attribute.tailCallKindAttr_eq_of Attribute.moduleFlagAttr_eq_of Attribute.tbaaTagAttr_eq_of Attribute.constantRangeAttr_eq_of
  Attribute.memoryEffectsAttr_eq_of Attribute.loopAnnotationAttr_eq_of Attribute.targetFeaturesAttr_eq_of Attribute.dlSpecAttr_eq_of
  Attribute.registerType_eq_of Attribute.registerAttr_eq_of Attribute.stringAttr_eq_of Attribute.unitAttr_eq_of
  Attribute.locationAttr_eq_of Attribute.arrayAttr_eq_of Attribute.denseArrayAttr_eq_of Attribute.denseElementsAttr_eq_of
  Attribute.dictionaryAttr_eq_of Attribute.functionType_eq_of Attribute.unregisteredAttr_eq_of Attribute.flatSymbolRefAttr_eq_of
  Attribute.symbolRefAttr_eq_of Attribute.modArithType_eq_of Attribute.feltType_eq_of Attribute.feltConstAttr_eq_of
  Attribute.indexType_eq_of Attribute.cirIntType_eq_of Attribute.cirBoolType_eq_of Attribute.cirFuncType_eq_of
  Attribute.cirIntAttr_eq_of Attribute.cirBoolAttr_eq_of Attribute.llvmVoidType_eq_of Attribute.byteType_eq_of
  Attribute.llvmPointerType_eq_of Attribute.llvmArrayType_eq_of Attribute.llvmStructType_eq_of Attribute.llvmFunctionType_eq_of
  Attribute.cudaTilePointerType_eq_of Attribute.ioAddressType_eq_of Attribute.hwModuleType_eq_of Attribute.pdlRangeType_eq_of
  Attribute.pdlAttributeType_eq_of Attribute.pdlOperationType_eq_of Attribute.pdlValueType_eq_of Attribute.pdlTypeType_eq_of
  Attribute.matchOptionalType_eq_of Attribute.seqClockType_eq_of Attribute.seqFirMemType_eq_of Attribute.smtSortType_eq_of

public section

/-- Why a pattern of `llvm-to-gmir` has no CTree validity proof. -/
inductive Unproven where
  /-- A byte shift is translated through an integer, which is entirely poison when every bit of
  the byte is. The byte shift moves defined zero bits into such a byte; the integer shift cannot. -/
  | allPoisonByte
  /-- The replacement's stack object is computed from the IR around the `llvm.alloca`
  (`MatchProg.inspectOperation`), which the semantics of the matched operation do not determine,
  and the pointer is cast back from an integer. -/
  | staticAlloca
  deriving Repr, DecidableEq

end

/-- A target that casts a byte to an integer simulates the source whatever bits it chooses. -/
@[local simp] theorem sim_bind_map_byteToIntCTree_left {X Y Z : Type} {RR : Y → Z → Prop}
    {w : Nat} (b : Data.LLVM.Byte w) (f : Data.LLVM.Int w → X) (k : X → Tree Y) (u : Tree Z) :
    Sim RR (CTree.bind (f <$> Builtin.byteToIntCTree b) k) u ↔
      ∀ bits, Sim RR (k (f (freezeByteWith b bits))) u := by
  unfold Builtin.byteToIntCTree freezeByteWith
  split <;> simp [CTree.choose_def, CTree.tau_def, Functor.map]

/-- A source that casts a byte to an integer simulates a value it can choose bits for. -/
@[local simp] theorem sim_pure_map_byteToIntCTree_right {X Y : Type} {RR : X → Y → Prop}
    {w : Nat} (b : Data.LLVM.Byte w) (f : Data.LLVM.Int w → Y) (x : X) :
    Sim RR (pure x : Tree X) (f <$> Builtin.byteToIntCTree b) ↔
      ∃ bits, RR x (f (freezeByteWith b bits)) := by
  unfold Builtin.byteToIntCTree freezeByteWith
  split <;> simp [CTree.choose_def, CTree.tau_def, Functor.map]

/-- A type with an `LLT` is an integer or pointer type, so no byte conforms to it. -/
@[local simp] theorem byte_conforms_of_LLT {bw : Nat} {v : Data.LLVM.Byte bw} {t : TypeAttr}
    (h : (LLT.ofType? t).isSome = true) : (RuntimeValue.byte bw v).Conforms t ↔ False := by
  rcases t with ⟨attr, ht⟩
  cases attr <;> simp_all [LLT.ofType?, RuntimeValue.Conforms]

/-- The integer type of a byte type. -/
@[local simp] theorem intOfByte_of (b : LLVM.ByteType) :
    (TypeAttr.of LLVM.ByteType b).intOfByte? = some (IntegerType.signless b.bitwidth) := by
  simp [TypeAttr.intOfByte?, TypeAttr.cast?, Attribute.cast?, TypeAttr.of, Attribute.of, IsAttr.inject,
    IsAttr.project,
    -Attribute.integerType_eq_of]

/-- `llvm.select` on an `i1` condition is `g_select`. -/
private theorem select_selectNonzero {w : Nat} (c : Data.LLVM.Int 1) (x y : Data.LLVM.Int w) :
    c.select x y ⊒ GMIR.selectNonzero c x y := by
  rw [GMIR.selectNonzero_one]
  exact isRefinedBy_refl _

/-- A same-width shift amount: gMIR's `shiftAmount` keeps it in range and makes it all ones out of
range, which every shift then treats as the out-of-range amount it was. -/
private theorem shiftAmount_val {w : Nat} (y : BitVec w) :
    shiftAmount w (.val y) = if y.toNat < w then .val y else .val (BitVec.allOnes w) := by
  simp only [shiftAmount]
  split <;> simp [BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem allOnes_ge {w : Nat} : BitVec.ofNat w w ≤ BitVec.allOnes w := by
  have := Nat.lt_two_pow_self (n := w)
  simp [BitVec.le_def, BitVec.toNat_allOnes, Nat.mod_eq_of_lt this]
  omega

private theorem ge_of_not_lt {w : Nat} {y : BitVec w} (h : ¬ y.toNat < w) : BitVec.ofNat w w ≤ y := by
  have := Nat.lt_two_pow_self (n := w)
  simp [BitVec.le_def, Nat.mod_eq_of_lt this]
  omega

/-- Closes the shift lemmas, by cases on whether the amount `y` is in range. -/
local macro "shift_tac" x:ident y:ident w:ident "[" op:Lean.Parser.Tactic.simpLemma "]" : tactic => `(tactic| (
  cases $x:ident with
  | poison => cases $y:ident <;> simp [shiftAmount, $op, Id.run, poison_isRefinedBy]
  | val $x:ident =>
    cases $y:ident with
    | poison => simp [shiftAmount, $op, Id.run, poison_isRefinedBy]
    | val $y:ident =>
      rw [shiftAmount_val]
      by_cases h : ($y).toNat < $w
      · simp only [h, ite_true]
        exact isRefinedBy_refl _
      · simp [h, $op, Id.run, ge_of_not_lt h, allOnes_ge, poison_isRefinedBy]))

private theorem shl_shiftAmount {w : Nat} (x y : Data.LLVM.Int w) (n u : Bool) :
    x.shl y n u ⊒ x.shl (shiftAmount w y) n u := by
  shift_tac x y w [Data.LLVM.Int.shl]

private theorem lshr_shiftAmount {w : Nat} (x y : Data.LLVM.Int w) (e : Bool) :
    x.lshr y e ⊒ x.lshr (shiftAmount w y) e := by
  shift_tac x y w [Data.LLVM.Int.lshr]

private theorem ashr_shiftAmount {w : Nat} (x y : Data.LLVM.Int w) (e : Bool) :
    x.ashr y e ⊒ x.ashr (shiftAmount w y) e := by
  shift_tac x y w [Data.LLVM.Int.ashr]

private theorem sshlSat_shiftAmount {w : Nat} (x y : Data.LLVM.Int w) :
    x.sshlSat y ⊒ x.sshlSat (shiftAmount w y) := by
  shift_tac x y w [Data.LLVM.Int.sshlSat]

private theorem ushlSat_shiftAmount {w : Nat} (x y : Data.LLVM.Int w) :
    x.ushlSat y ⊒ x.ushlSat (shiftAmount w y) := by
  shift_tac x y w [Data.LLVM.Int.ushlSat]

/-- `g_abs` is `llvm.intr.abs` without `is_int_min_poison`, which only adds poison. -/
private theorem abs_drop_int_min_poison {w : Nat} (x : Data.LLVM.Int w) (b : Bool) :
    x.abs b ⊒ x.abs false := by
  cases x <;> cases b <;> simp [Data.LLVM.Int.abs, Id.run, poison_isRefinedBy, isRefinedBy_refl, pure]
  all_goals split <;> simp [poison_isRefinedBy, isRefinedBy_refl]

/-- gMIR reduces the funnel shift amount modulo the width, as the funnel shift itself does. -/
private theorem fshl_funnelShiftAmount {w : Nat} (a b c : Data.LLVM.Int w) :
    a.fshl b c ⊒ a.fshl b (GMIR.funnelShiftAmount w c) := by
  cases a <;> cases b <;> cases c <;>
    simp [Data.LLVM.Int.fshl, GMIR.funnelShiftAmount, Id.run, poison_isRefinedBy, isRefinedBy_refl]
  rename_i a b c
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · exact BitVec.of_length_zero.trans BitVec.of_length_zero.symm
  · rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hw) (Nat.le_of_lt Nat.lt_two_pow_self)),
      Nat.mod_mod]
    exact isRefinedBy_refl _

private theorem fshr_funnelShiftAmount {w : Nat} (a b c : Data.LLVM.Int w) :
    a.fshr b c ⊒ a.fshr b (GMIR.funnelShiftAmount w c) := by
  cases a <;> cases b <;> cases c <;>
    simp [Data.LLVM.Int.fshr, GMIR.funnelShiftAmount, Id.run, poison_isRefinedBy, isRefinedBy_refl]
  rename_i a b c
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · exact BitVec.of_length_zero.trans BitVec.of_length_zero.symm
  · rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hw) (Nat.le_of_lt Nat.lt_two_pow_self)),
      Nat.mod_mod]
    exact isRefinedBy_refl _


/-- The int/byte round trip: an integer type and a byte type of the same nonzero width. -/
@[local simp] theorem isIntToByteRoundTrip_iff (a b : TypeAttr) :
    isIntToByteRoundTrip a b = true ↔
      ∃ i, a.val = .integerType i ∧ ∃ bt, b.val = .byteType bt ∧ i.bitwidth = bt.bitwidth ∧
        0 < i.bitwidth := by
  rcases a with ⟨a, _⟩
  rcases b with ⟨b, _⟩
  cases a <;> cases b <;> simp [isIntToByteRoundTrip, -Attribute.integerType_eq_of]

/-- A failing operation mapped to a result still has no successful outcome. -/
@[local simp] theorem canInterpretTo_map_fail_ok {R X : Type} (f : X → R) (v : R) :
    PureOrErr.CanInterpretTo (f <$> (fail : CTree (ErrorE ⊕ₑ UBE) FreezeC X)) (.ok v) ↔ False := by
  simp [PureOrErr.CanInterpretTo.map_iff]

/-- Only an integer of its width conforms to a type whose attribute is an integer type. -/
theorem conforms_of_val_integerType {v : RuntimeValue} {t : TypeAttr} {i : IntegerType}
    (h : t.val = .integerType i) :
    v.Conforms t ↔ (match v with | .int bw _ => i.bitwidth = bw | _ => False) := by
  rcases t with ⟨attr, _⟩
  subst h
  cases v <;> simp [RuntimeValue.Conforms]

theorem constant_valid : Puddle.CTree.Pattern.Valid lowerIntegerConstant := by
  proveLegalValid with
    cases h : (‹propertiesOf (OpCode.llvm Llvm.mlir__constant)›).value <;> simp_all [isRefinedBy_refl]

attribute [local simp] conforms_of_val_integerType in
theorem round_trip_valid : Puddle.CTree.Pattern.Valid (reconcilePairingCast isIntToByteRoundTrip) := by
  proveLegalValid with
    exact ⟨0, by rw [freezeByteWith_fromInt ‹0 < _›]; exact isRefinedBy_refl _⟩

theorem add_valid : Puddle.CTree.Pattern.Valid (lowerBinop .add .g_add) := by
  proveLegalValid using isRefinedBy_refl

theorem sub_valid : Puddle.CTree.Pattern.Valid (lowerBinop .sub .g_sub) := by
  proveLegalValid using isRefinedBy_refl

theorem select_valid : Puddle.CTree.Pattern.Valid (lowerSelect) := by
  proveLegalValid using select_selectNonzero

theorem sext_valid : Puddle.CTree.Pattern.Valid (lowerIntegerCast .sext .g_sext) := by
  proveLegalValid using isRefinedBy_refl

theorem zext_valid : Puddle.CTree.Pattern.Valid (lowerIntegerCast .zext .g_zext) := by
  proveLegalValid using isRefinedBy_refl

theorem trunc_valid : Puddle.CTree.Pattern.Valid (lowerIntegerCast .trunc .g_trunc) := by
  proveLegalValid using isRefinedBy_refl

theorem and_valid : Puddle.CTree.Pattern.Valid (lowerBinop .and .g_and) := by
  proveLegalValid using isRefinedBy_refl

theorem or_valid : Puddle.CTree.Pattern.Valid (lowerBinop .or .g_or) := by
  proveLegalValid using isRefinedBy_refl

theorem xor_valid : Puddle.CTree.Pattern.Valid (lowerBinop .xor .g_xor) := by
  proveLegalValid using isRefinedBy_refl

theorem shl_valid : Puddle.CTree.Pattern.Valid (lowerBinop .shl .g_shl) := by
  proveLegalValid using shl_shiftAmount

theorem lshr_valid : Puddle.CTree.Pattern.Valid (lowerBinop .lshr .g_lshr) := by
  proveLegalValid using lshr_shiftAmount

theorem ashr_valid : Puddle.CTree.Pattern.Valid (lowerBinop .ashr .g_ashr) := by
  proveLegalValid using ashr_shiftAmount

theorem mul_valid : Puddle.CTree.Pattern.Valid (lowerBinop .mul .g_mul) := by
  proveLegalValid using isRefinedBy_refl

theorem sdiv_valid : Puddle.CTree.Pattern.Valid (lowerBinop .sdiv .g_sdiv) := by
  proveLegalValid using isRefinedBy_refl

theorem udiv_valid : Puddle.CTree.Pattern.Valid (lowerBinop .udiv .g_udiv) := by
  proveLegalValid using isRefinedBy_refl

theorem srem_valid : Puddle.CTree.Pattern.Valid (lowerBinop .srem .g_srem) := by
  proveLegalValid using isRefinedBy_refl

theorem urem_valid : Puddle.CTree.Pattern.Valid (lowerBinop .urem .g_urem) := by
  proveLegalValid using isRefinedBy_refl

theorem bswap_valid : Puddle.CTree.Pattern.Valid (lowerUnop .intr__bswap .g_bswap id) := by
  proveLegalValid using isRefinedBy_refl

theorem bitreverse_valid : Puddle.CTree.Pattern.Valid (lowerUnop .intr__bitreverse .g_bitreverse id) := by
  proveLegalValid using isRefinedBy_refl

theorem smax_valid : Puddle.CTree.Pattern.Valid (lowerBinop .intr__smax .g_smax) := by
  proveLegalValid using isRefinedBy_refl

theorem smin_valid : Puddle.CTree.Pattern.Valid (lowerBinop .intr__smin .g_smin) := by
  proveLegalValid using isRefinedBy_refl

theorem umax_valid : Puddle.CTree.Pattern.Valid (lowerBinop .intr__umax .g_umax) := by
  proveLegalValid using isRefinedBy_refl

theorem umin_valid : Puddle.CTree.Pattern.Valid (lowerBinop .intr__umin .g_umin) := by
  proveLegalValid using isRefinedBy_refl

theorem abs_valid : Puddle.CTree.Pattern.Valid (lowerUnop .intr__abs .g_abs (fun _ => ())) := by
  proveLegalValid using abs_drop_int_min_poison

theorem fshl_valid : Puddle.CTree.Pattern.Valid (lowerFunnelShiftIntrinsic .intr__fshl .g_fshl) := by
  proveLegalValid using fshl_funnelShiftAmount

theorem fshr_valid : Puddle.CTree.Pattern.Valid (lowerFunnelShiftIntrinsic .intr__fshr .g_fshr) := by
  proveLegalValid using fshr_funnelShiftAmount

theorem saddsat_valid : Puddle.CTree.Pattern.Valid (lowerBinop .intr__sadd__sat .g_saddsat) := by
  proveLegalValid using isRefinedBy_refl

theorem uaddsat_valid : Puddle.CTree.Pattern.Valid (lowerBinop .intr__uadd__sat .g_uaddsat) := by
  proveLegalValid using isRefinedBy_refl

theorem ssubsat_valid : Puddle.CTree.Pattern.Valid (lowerBinop .intr__ssub__sat .g_ssubsat) := by
  proveLegalValid using isRefinedBy_refl

theorem usubsat_valid : Puddle.CTree.Pattern.Valid (lowerBinop .intr__usub__sat .g_usubsat) := by
  proveLegalValid using isRefinedBy_refl

theorem sshlsat_valid : Puddle.CTree.Pattern.Valid (lowerBinop .intr__sshl__sat .g_sshlsat) := by
  proveLegalValid using sshlSat_shiftAmount

theorem ushlsat_valid : Puddle.CTree.Pattern.Valid (lowerBinop .intr__ushl__sat .g_ushlsat) := by
  proveLegalValid using ushlSat_shiftAmount

theorem icmp_valid : Puddle.CTree.Pattern.Valid lowerIcmp := by
  proveLegalValid using isRefinedBy_refl

/-- A count is refined by itself resized to the width it has. -/
private theorem isRefinedBy_resizeCount {w : Nat} (c : Data.LLVM.Int w) : c ⊒ resizeCount w c := by
  rw [resizeCount_self]
  exact isRefinedBy_refl _

theorem ctlz_valid : Puddle.CTree.Pattern.Valid
    (lowerCount .intr__ctlz .g_ctlz (fun _ => ()) (!·.is_zero_poison)) := by
  proveLegalValid using isRefinedBy_resizeCount

theorem cttz_valid : Puddle.CTree.Pattern.Valid
    (lowerCount .intr__cttz .g_cttz (fun _ => ()) (!·.is_zero_poison)) := by
  proveLegalValid using isRefinedBy_resizeCount

theorem ctlz_zero_poison_valid : Puddle.CTree.Pattern.Valid
    (lowerCount .intr__ctlz .g_ctlz_zero_poison (fun _ => ()) (·.is_zero_poison)) := by
  proveLegalValid using isRefinedBy_resizeCount

theorem cttz_zero_poison_valid : Puddle.CTree.Pattern.Valid
    (lowerCount .intr__cttz .g_cttz_zero_poison (fun _ => ()) (·.is_zero_poison)) := by
  proveLegalValid using isRefinedBy_resizeCount

theorem ctpop_valid : Puddle.CTree.Pattern.Valid (lowerCount .intr__ctpop .g_ctpop id) := by
  proveLegalValid using isRefinedBy_resizeCount

theorem byte_trunc_valid : Puddle.CTree.Pattern.Valid
    (lowerUnaryByteOp .trunc .g_trunc (fun _ => ⟨false, false⟩)) := by
  proveLegalValid with exact byte_trunc_frozen _ _ _

/-- A byte and an integer type of the same nonzero width, in either order. -/
@[local simp] theorem isByteIntBitcast_iff (a b : TypeAttr) :
    isByteIntBitcast a b = true ↔
      (∃ bt, a.val = .byteType bt ∧ ∃ i, b.val = .integerType i ∧ bt.bitwidth = i.bitwidth ∧
        0 < bt.bitwidth) ∨
      (∃ i, a.val = .integerType i ∧ ∃ bt, b.val = .byteType bt ∧ bt.bitwidth = i.bitwidth ∧
        0 < bt.bitwidth) := by
  rcases a with ⟨a, _⟩
  rcases b with ⟨b, _⟩
  cases a <;> cases b <;> simp [isByteIntBitcast, -Attribute.integerType_eq_of]

/-- Only a byte of its width conforms to a type whose attribute is a byte type. -/
theorem conforms_of_val_byteType {v : RuntimeValue} {t : TypeAttr} {b : LLVM.ByteType}
    (h : t.val = .byteType b) :
    v.Conforms t ↔ (match v with | .byte bw _ => b.bitwidth = bw | _ => False) := by
  rcases t with ⟨attr, _⟩
  subst h
  cases v <;> simp [RuntimeValue.Conforms]

attribute [local simp] conforms_of_val_integerType conforms_of_val_byteType in
theorem byte_int_bitcast_valid : Puddle.CTree.Pattern.Valid lowerByteIntBitcast := by
  proveLegalValid with
    first
    | exact byte_toInt_frozen ‹_› _ _
    | (split <;> (try simp_all) <;> rename_i heq <;> split at heq <;> cases heq)

/-! ## Loads

`lowerLoad_pattern` accepts a load whose `loadMemOperand?` is defined: a naturally aligned load
of an `i8`, `i16`, `i32`, `i64` or pointer. Its `g_load` checks the alignment of the memory
operand, which is the alignment `llvm.load` checks (`Llvm.accessAlignment`), wrapped to 64 bits:
an alignment of `2 ^ 64` or more makes the `llvm.load` of any non-null pointer undefined
behavior. The loaded values agree by the lemmas of `Veir.Passes.LLVMToGMIR.Remaining`. -/

/-- What `loadMemOperand?` accepts, and the memory operand it builds. -/
theorem loadMemOperand?_some {type : TypeAttr} {props : LoadProperties} {mmo : MachineMemOperand}
    (h : loadMemOperand? type props = some mmo) :
    mmo.alignment.toNat = Llvm.accessAlignment .riscv64 props.alignment type.val % 2 ^ 64 ∧
    ((∃ s, type.val = .integerType ⟨8, s⟩ ∧ mmo.size.toNat = 8) ∨
     (∃ s, type.val = .integerType ⟨16, s⟩ ∧ mmo.size.toNat = 16) ∨
     (∃ s, type.val = .integerType ⟨32, s⟩ ∧ mmo.size.toNat = 32) ∨
     (∃ s, type.val = .integerType ⟨64, s⟩ ∧ mmo.size.toNat = 64) ∨
     (∃ p, type.val = .llvmPointerType p ∧ mmo.size.toNat = 64)) := by
  rcases type with ⟨val, hval⟩
  cases val <;> simp [loadMemOperand?, memAccessWidth?, DataLayout.getTypeSize,
    DataLayout.getTypeABIAlignment, Llvm.accessAlignment, guard, Option.bind_eq_some_iff,
    -Attribute.integerType_eq_of] at h ⊢
  · obtain ⟨a, ⟨h8, ⟨a1, ⟨h0, rfl⟩, rfl⟩, hw⟩, hsync, hmmo⟩ := h
    rename_i t
    rcases t with ⟨bw, sg⟩
    dsimp only at h8 h0 hw hmmo ⊢
    have hbw : bw = 8 ∨ bw = 16 ∨ bw = 32 ∨ bw = 64 := by omega
    rcases hbw with rfl | rfl | rfl | rfl <;>
      by_cases hv : props.alignment.value = 0 <;>
      simp [hv, Option.bind_eq_some_iff] at hmmo ⊢
    all_goals first
      | (subst hmmo; simp)
      | (obtain ⟨-, rfl⟩ := hmmo; simp)
  · obtain ⟨hsync, h⟩ := h
    by_cases hv : props.alignment.value = 0 <;> simp [hv, Option.bind_eq_some_iff] at h ⊢
    · subst h; simp
    · obtain ⟨-, rfl⟩ := h; simp

/-- A target that lifts the source's own interpretation `S`, then continues with `m` and `k`,
simulates the source when the continuation simulates each successful outcome. -/
theorem sim_match_eq {α β γ : Type} {R : γ → α → Prop} (S : Interp α) (m : α → Tree β)
    (k : β → Tree γ) (hk : ∀ v, S = .ok v → Sim R (CTree.bind (m v) k) (pure v : Tree α)) :
    (match (generalizing := false) S with
      | .ok v => Sim R (CTree.bind (CTree.bind (monadLift S : Tree α) m) k) (pure v : Tree α)
      | .ub _ => True
      | .fail _ => True) := by
  cases S with
  | ok v => simpa using hk v rfl
  | ub _ => trivial
  | fail _ => trivial

theorem load_valid : Puddle.CTree.Pattern.Valid lowerLoad_pattern := by
  conv => arg 1; cbv
  simpPuddleValid
  intro addrType type value hconf props hsome mem
  simp only [TypeAttr.of_typeAttr] at hsome hconf ⊢
  obtain ⟨mmo, hmmo⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨halign, htype⟩ := loadMemOperand?_some hmmo
  simp only [hmmo]
  simpLegalSemantics
  /- Only a defined address runs the load: otherwise the source fails or is undefined. -/
  cases value
  case addr addr =>
    cases addr
    case poison => simp
    case val p =>
      dsimp only
      rw [halign]
      by_cases hA : Llvm.accessAlignment DataLayout.riscv64 props.alignment type.val < 2 ^ 64
      · rw [Nat.mod_eq_of_lt hA]
        rcases htype with ⟨s, ht, hs⟩ | ⟨s, ht, hs⟩ | ⟨s, ht, hs⟩ | ⟨s, ht, hs⟩ | ⟨pt, ht, hs⟩
        case inr.inr.inr.inr =>
          /- A pointer: both sides run `llvmLoad`. -/
          rw [llvmLoad_ptr mem p type pt ht]
          simp only [ht]
          refine sim_match_eq _ _ _ ?_
          intro v hv
          simp only [Interp.bind_eq_ok_iff, Interp.ok.injEq] at hv
          obtain ⟨_, _, w, hw, rfl⟩ := hv
          by_cases hp : p = .null
          · simp [hp] at hw
          · simp only [hp, ite_false, Interp.bind_eq_ok_iff, Interp.pure_eq, Interp.ok.injEq] at hw
            obtain ⟨b, _, rfl⟩ := hw
            simp [RuntimeValue.arrayIsRefinedBy_refl, MemoryState.isRefinedBy_refl,
              ControlFlowAction.optionIsRefinedBy]
        /- An integer: `llvmLoad` is the `intLoad` of the operand's size, which is the width. -/
        all_goals
          first
            | rw [llvmLoad_i8 mem p s type ht] | rw [llvmLoad_i16 mem p s type ht]
            | rw [llvmLoad_i32 mem p s type ht] | rw [llvmLoad_i64 mem p s type ht]
          generalize mmo.size.toNat = sz at hs ⊢
          subst hs
          simp only [ht, Nat.lt_irrefl, dite_false, dite_true, Data.LLVM.Int.cast_self,
            LawfulMonad.bind_assoc, Interp.pure_eq, Interp.bind_ok]
          refine sim_match_eq _ _ _ ?_
          intro v hv
          simp only [Interp.bind_eq_ok_iff, Interp.ok.injEq] at hv
          obtain ⟨_, _, val, _, rfl⟩ := hv
          simp [RuntimeValue.arrayIsRefinedBy_refl, MemoryState.isRefinedBy_refl,
            ControlFlowAction.optionIsRefinedBy]
      · rw [checkAlignment_of_le (Nat.le_of_not_lt hA)]
        by_cases hp : p = .null
        · subst hp
          simp [llvmLoad_null]
        · simp [hp]
  all_goals simp

set_option maxRecDepth 100000 in
/-- A certificate for every pattern of `llvm-to-gmir`, in `llvmToGMIRPatternList` order. -/
public def llvmToGMIRCertificates : Puddle.CTree.Certificates Unproven llvmToGMIRPatternList :=
  .proven add_valid <|
  .proven sub_valid <|
  .proven icmp_valid <|
  .proven select_valid <|
  .proven sext_valid <|
  .proven zext_valid <|
  .proven trunc_valid <|
  .proven and_valid <|
  .proven or_valid <|
  .proven xor_valid <|
  .proven shl_valid <|
  .proven lshr_valid <|
  .proven ashr_valid <|
  .proven mul_valid <|
  .proven sdiv_valid <|
  .proven udiv_valid <|
  .proven srem_valid <|
  .proven urem_valid <|
  .proven bswap_valid <|
  .proven bitreverse_valid <|
  .proven smax_valid <|
  .proven smin_valid <|
  .proven umax_valid <|
  .proven umin_valid <|
  .proven abs_valid <|
  .proven fshl_valid <|
  .proven fshr_valid <|
  .proven saddsat_valid <|
  .proven uaddsat_valid <|
  .proven ssubsat_valid <|
  .proven usubsat_valid <|
  .proven sshlsat_valid <|
  .proven ushlsat_valid <|
  .proven ctlz_valid <|
  .proven cttz_valid <|
  .proven ctlz_zero_poison_valid <|
  .proven cttz_zero_poison_valid <|
  .proven ctpop_valid <|
  .proven constant_valid <|
  .proven byte_trunc_valid <|
  .unproven .allPoisonByte <| -- byte_shl
  .unproven .allPoisonByte <| -- byte_lshr
  .proven byte_int_bitcast_valid <|
  .unproven .staticAlloca <| -- static_alloca
  .proven load_valid <|
  .proven round_trip_valid <|
  .nil

/-- Every pattern `llvm-to-gmir` runs is proven valid or recorded as unproven. -/
theorem llvmToGMIRPatternList_certified (pattern : Pattern OpCode)
    (h : pattern ∈ llvmToGMIRPatternList) :
    pattern ∈ llvmToGMIRCertificates.provenPatterns ∨
      pattern ∈ llvmToGMIRCertificates.unprovenPatterns.map Prod.fst :=
  llvmToGMIRCertificates.covers pattern h

/-- Every proven pattern of `llvm-to-gmir` satisfies the CTree validity predicate. -/
theorem llvmToGMIRCertificates_valid (pattern : Pattern OpCode)
    (h : pattern ∈ llvmToGMIRCertificates.provenPatterns) :
    Puddle.CTree.Pattern.Valid pattern :=
  llvmToGMIRCertificates.valid pattern h

end Veir.LLVMToGMIR.CTreeProofs
