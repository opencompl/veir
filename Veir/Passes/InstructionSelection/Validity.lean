module

public import Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.PatternRewriter.Puddle.CTreeProofs
public import Veir.Passes.InstructionSelection.RISCV64
public import Veir.Passes.InstructionSelection.RISCV64Branches

import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.Passes.InstructionSelection.RISCV64Branches
import all Veir.Passes.Legalization.Validity.Common
import all Veir.Interpreter.RuntimeValue.Conforms
import all Veir.Interpreter.Basic
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.Builtin.Interpreter
import all Veir.Dialects.Builtin.OpInfo
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR_RISCV.OpInfo
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV.Interpreter
import all Veir.Dialects.RISCV_Cf.OpInfo
import all Veir.Dialects.RV64.OpInfo
import all Veir.GlobalOpInfo
import all Veir.IR.Attribute
import all Veir.Data.RISCV.Reg.Basic
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Casting
import all Veir.Data.Refinement
import Veir.Passes.InstructionSelection.Proofs
import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.Tactic.BVDecide

/-!
# CTree validity of the RISC-V 64 instruction selection

The Puddle patterns of `isel-riscv64` and `isel-br-riscv64` that the branch
`math-fehr/puddle-ctree-wip` does not prove valid
(`Veir/Passes/InstructionSelection/Proofs/RISCV64/` there; the other patterns of both passes are
proven there, and their proofs are to be cherry-picked). Each is handled by normalizing its
semantics down to a goal over `Data.LLVM.Int` as the legalizer proofs do
(`Veir.Passes.Legalization.Validity.Common`), with the register casts of the selector added to
the semantics (`normalizeIselValid`):

* `gmirTrunc_pattern` and `gmirAnyext_pattern` reduce to a round trip of the operand through a
  64-bit register (`TruncRoundTrip`, `AnyextRoundTrip`; `gmir_trunc_valid_of_narrow`,
  `gmir_anyext_valid_of_narrow`). The round trip holds for operands of at most 64 bits
  (`trunc_narrow`, `anyext_narrow`) and fails above (`trunc_wide`, `anyext_wide`), which the
  matchers accept since the legalizer marks both operations `alwaysLegal`.
* `memIntrinsicCallPattern` lowers to a `riscv_cf.call`, which the interpreter cannot run
  (`memcpy_call_fails`, `memset_call_fails`).
* `unreachable_pattern` rewrites a terminator, which `Pattern.Valid` does not support
  (`unreachable_unsupported`).

The rewrites that are not Puddle patterns have no statement: the local rewrites
`splitLoad_local`, `splitStore_local`, `memIntrinsicInline_local` and `getelementptrGeneral` of
`isel-riscv64`, the branch lowering of `isel-br-riscv64`, and `lowerReturn` and `lowerOp` of
`isel-abi-riscv64`.
-/

namespace Veir.ISel.CTreeProofs

open Puddle
open Puddle.CTree
open _root_.CTree
open Veir.Legalization.CTreeProofs

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  GMIR.interpretOp' GMIR.interpretOpCTree GMIR_RISCV.interpretOp'
  Llvm.interpretOp' Llvm.interpretOpCTree
  Riscv.interpretOp' Riscv.interpretOpCTree Rv64.interpretOp' Riscv_Cf.interpretOp'
  Builtin.interpretOpCTree Builtin.interpretUnrealizedConversionCastCTree

attribute [local simp] GMIR.isTerminator GMIR.getEffects GMIR_RISCV.base Builtin.getEffects
  Llvm.getEffects Llvm.isTerminator Riscv.getEffects Rv64.getEffects Riscv_Cf.getEffects
  Riscv_Cf.isTerminator

attribute [local implicit_reducible] TypeAttr

/- The normalization unfolds `Attribute.of` to case on the result types of the casts, which the
lemmas folding each attribute constructor back would undo (as in
`Veir.Passes.CastsReconciliation.Validity`). -/
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

/-- Why a pattern of the instruction selection has no CTree validity proof. -/
inductive Unproven where
  /-- The pattern casts its operand to a 64-bit register and back, and the legalizer marks the
  operation `alwaysLegal`, so the matcher accepts operands wider than 64 bits, whose high bits
  the register loses (`trunc_wide`, `anyext_wide`). The reduced goal holds for every operand of
  at most 64 bits (`trunc_narrow`, `anyext_narrow`). -/
  | wideOperand
  /-- The replacement is a `riscv_cf.call`, which the interpreter cannot run, while the
  intrinsic it replaces has semantics (`memcpy_call_fails`, `memset_call_fails`): a target that
  fails is not a refinement. -/
  | callWithoutSemantics
  /-- The pattern rewrites a terminator, which `Pattern.Supported` excludes
  (`unreachable_unsupported`). -/
  | terminator
  deriving Repr, DecidableEq

end

/-- Normalize an instruction selection validity goal after `simpLegalSemantics`, down to goals
over `Data.LLVM.Int`: split the matched values, including a matched integer into a value or
poison, since the casts to a register match on it; case the result types the casts match on;
split the width guards; then resolve the register a cast of poison chooses (universally) and
the high bits a matched `g_anyext` chooses (existentially). -/
macro "normalizeIselValid" : tactic => `(tactic| (
  intros
  casesConformingValues
  all_goals (try casesLocalsOf Data.LLVM.Int)
  all_goals (simp_all [RuntimeValue.isRefinedBy, Attribute.of, IntegerType.signless, -Attribute.integerType_eq_of])
  all_goals (try casesResultTypes)
  all_goals (try simp only [RuntimeValue.isRefinedBy, IntegerType.signless, Attribute.of, TypeAttr.of_def,
    Attribute.of_def])
  all_goals (try simp [RuntimeValue.isRefinedBy, -Attribute.integerType_eq_of])
  all_goals (try splitGuards)
  all_goals (try simp [RuntimeValue.isRefinedBy, le_eq_false_of_lt, lt_eq_false_of_le, -Attribute.integerType_eq_of, *])
  all_goals (try simp [CTree.choose_def, CTree.tau_def, Functor.map, Sim.tau_l, _root_.CTree.CTree.bind_tau,
      Sim.bind_monadLift_right_iff, RuntimeValue.isRefinedBy, TypeAttr.of_def, Attribute.of_def,
      -Attribute.integerType_eq_of, Id.run])))

/-- Truncating poison is poison, so the register a cast of poison chooses refines it. -/
@[local simp] theorem trunc_poison {w₁ w₂ : Nat} (nsw nuw : Bool) (h : w₁ > w₂) :
    (Data.LLVM.Int.poison : Data.LLVM.Int w₁).trunc w₂ nsw nuw h = .poison := rfl

/-- Extending poison is poison, whatever the high bits. -/
@[local simp] theorem ext_poison {w₁ w₂ : Nat} (msb : BitVec (w₂ - w₁)) (h : w₁ < w₂) :
    (Data.LLVM.Int.poison : Data.LLVM.Int w₁).ext w₂ msb h = .poison := rfl

/-! ## The register round trips of `gmirTrunc_pattern` and `gmirAnyext_pattern`

`gmirTrunc_pattern` and `gmirAnyext_pattern` cast their operand to a register and the register
to the result type. Their validity reduces to the goals over `Data.LLVM.Int` below, stated at
every operand width as the matchers accept, which hold up to 64 bits and fail above. -/

/-- The goal `gmirTrunc_pattern` reduces to: truncating a value is refined by casting it to a
register and the register to the result width. -/
def TruncRoundTrip : Prop :=
  ∀ {w : Nat} (a : BitVec w) (tb : Nat) (h : w > tb) (nsw nuw : Bool),
    (Data.LLVM.Int.val a).trunc tb nsw nuw h ⊒ RISCV.Reg.toInt ⟨BitVec.setWidth 64 a⟩ tb

/-- The goal `gmirAnyext_pattern` reduces to: a `g_anyext` of a value may choose its high bits
as casting the value to a register and the register to the result width does. -/
def AnyextRoundTrip : Prop :=
  ∀ {w : Nat} (a : BitVec w) (tb : Nat) (h : w < tb),
    ∃ msb, (Data.LLVM.Int.val a).ext tb msb h ⊒ RISCV.Reg.toInt ⟨BitVec.setWidth 64 a⟩ tb

/-- The low `tb` bits of an operand of at most 64 bits survive the round trip through a register
(`Data.RISCV.trunc_refinement_le64`). -/
theorem trunc_narrow {w : Nat} (hw : w ≤ 64) (a : BitVec w) (tb : Nat) (h : w > tb) (nsw nuw : Bool) :
    (Data.LLVM.Int.val a).trunc tb nsw nuw h ⊒ RISCV.Reg.toInt ⟨BitVec.setWidth 64 a⟩ tb :=
  Data.RISCV.trunc_refinement_le64 hw

/-- Above 64 bits the register loses the operand's high bits: bit 100 of an `i129` is dropped by
the round trip, and kept by the truncation to `i128`. -/
theorem trunc_wide : ¬ TruncRoundTrip := fun h => by
  have := h (1#129 <<< 100) 128 (by omega) false false
  simp [Data.LLVM.Int.trunc, RISCV.Reg.toInt, isRefinedBy, Id.run] at this

/-- A `g_anyext` of an operand of at most 64 bits may choose zero high bits, which is what the
round trip through a register produces. -/
theorem anyext_narrow {w : Nat} (hw : w ≤ 64) (a : BitVec w) (tb : Nat) (h : w < tb) :
    ∃ msb, (Data.LLVM.Int.val a).ext tb msb h ⊒ RISCV.Reg.toInt ⟨BitVec.setWidth 64 a⟩ tb := by
  refine ⟨0, ?_⟩
  simp only [Data.LLVM.Int.ext, RISCV.Reg.toInt, isRefinedBy, Data.LLVM.Int.cast, Id.run]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_cast, BitVec.getElem_append, BitVec.getElem_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getElem_zero]
  by_cases hiw : i < w
  · simp [hiw, show i < 64 by omega, BitVec.getLsbD_eq_getElem hiw]
  · simp [hiw, BitVec.getLsbD_of_ge a i (by omega)]

/-- Above 64 bits no choice of high bits recovers bit 100 of an `i128`, which the round trip
through a register drops. -/
theorem anyext_wide_msb (msb : BitVec 1) :
    ¬ ((Data.LLVM.Int.val (1#128 <<< 100)).ext 129 msb (by omega) ⊒
      RISCV.Reg.toInt ⟨BitVec.setWidth 64 (1#128 <<< 100)⟩ 129) := by
  simp [Data.LLVM.Int.ext, RISCV.Reg.toInt, isRefinedBy, Data.LLVM.Int.cast, Id.run, BitVec.cast_eq]
  bv_decide

theorem anyext_wide : ¬ AnyextRoundTrip := fun h =>
  have ⟨msb, h⟩ := h (1#128 <<< 100) 129 (by omega)
  anyext_wide_msb msb h

/-! ## The memory intrinsic calls and `unreachable` -/

/-- A zero-length `memcpy` succeeds in empty memory, while the call it is lowered to fails. -/
theorem memcpy_call_fails :
    Llvm.interpretOp' .intr__memcpy ⟨false, none, none, none, none, none, none⟩ #[]
      #[.addr (.val ⟨0⟩), .addr (.val ⟨0⟩), .int 64 (.val 0)] #[] MemoryState.empty .riscv64 =
      Interp.ok (#[], MemoryState.empty, none) ∧
    Riscv_Cf.interpretOp' .call ⟨some ⟨"@memcpy"⟩⟩ #[] #[.reg ⟨0⟩, .reg ⟨0⟩, .reg ⟨0⟩] #[] = Interp.fail none :=
  ⟨rfl, rfl⟩

/-- A zero-length `memset` succeeds in empty memory, while the call it is lowered to fails. -/
theorem memset_call_fails :
    Llvm.interpretOp' .intr__memset ⟨false, none, none, none, none, none, none⟩ #[]
      #[.addr (.val ⟨0⟩), .int 8 (.val 0), .int 64 (.val 0)] #[] MemoryState.empty .riscv64 =
      Interp.ok (#[], MemoryState.empty, none) ∧
    Riscv_Cf.interpretOp' .call ⟨some ⟨"@memset"⟩⟩ #[] #[.reg ⟨0⟩, .reg ⟨0⟩, .reg ⟨0⟩] #[] = Interp.fail none :=
  ⟨rfl, rfl⟩

/-- `llvm.unreachable` is a terminator, so `Pattern.Valid` does not support its pattern. -/
theorem unreachable_unsupported : ¬ CTree.Pattern.Supported unreachable_pattern := by
  unfold unreachable_pattern
  conv => arg 1; cbv
  simp only [CTree.Pattern.Supported, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true]
  simp [get_effects, is_terminator]

/-! ## Status of the patterns without a validity proof -/

theorem memcpy_call_status : Status Unproven (memIntrinsicCallPattern false) :=
  .unproven .callWithoutSemantics

theorem memset_call_status : Status Unproven (memIntrinsicCallPattern true) :=
  .unproven .callWithoutSemantics

/-- `gmirTrunc_pattern` is valid as soon as the round trip of the operand through a register
keeps its low bits at every operand width: the only goal left over `Data.LLVM.Int`, which
`trunc_narrow` proves up to 64 bits and `trunc_wide` refutes above. -/
theorem gmir_trunc_valid_of_narrow (narrow : TruncRoundTrip) :
    Puddle.CTree.Pattern.Valid gmirTrunc_pattern := by
  unfold gmirTrunc_pattern lowerRegCast
  simpPuddleValid
  simpLegalSemantics
  normalizeIselValid
  exact narrow _ _ _ _ _

theorem gmir_trunc_status : Status Unproven gmirTrunc_pattern := .unproven .wideOperand

/-- `gmirAnyext_pattern` is valid as soon as the round trip of the operand through a register is
a choice of high bits of the matched `g_anyext` at every operand width: the only goal left over
`Data.LLVM.Int`, which `anyext_narrow` proves up to 64 bits and `anyext_wide` refutes above. -/
theorem gmir_anyext_valid_of_narrow (narrow : AnyextRoundTrip) :
    Puddle.CTree.Pattern.Valid gmirAnyext_pattern := by
  unfold gmirAnyext_pattern lowerRegCast
  simpPuddleValid
  simpLegalSemantics
  normalizeIselValid
  exact narrow _ _ _

theorem gmir_anyext_status : Status Unproven gmirAnyext_pattern := .unproven .wideOperand

theorem unreachable_status : Status Unproven unreachable_pattern := .unproven .terminator

end Veir.ISel.CTreeProofs
