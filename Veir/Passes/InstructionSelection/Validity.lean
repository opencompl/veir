module

public import Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.PatternRewriter.Puddle.CTreeProofs
public import Veir.Passes.InstructionSelection.RISCV64
public import Veir.Passes.InstructionSelection.RISCV64Branches
public import Veir.Passes.InstructionSelection.RISCV64Abi
public import Veir.PatternRewriter.Semantics

import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.Passes.InstructionSelection.RISCV64Branches
import all Veir.Passes.InstructionSelection.RISCV64Abi
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

The remaining Puddle patterns, which their drivers instantiate at parameters computed from the
matched operation (the split loads and stores, the inline memory intrinsics, `getelementptr` and
the argument lowering of `isel-abi-riscv64`), are stated at every parameter; the argument
lowering is proven (`formal_argument_valid`). The
branch lowering of `isel-br-riscv64` is not a Puddle pattern; it is stated as a refinement of
every function of the module. The lowering of returns and calls of `isel-abi-riscv64` has no
statement: it needs a refinement up to the ABI (see the last section).
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

/-! ## The memory intrinsic calls -/

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
  all_goals intros
  all_goals simp [ctree_semantics, RuntimeValue.Conforms, RuntimeValue.isRefinedBy, -Attribute.integerType_eq_of]
  all_goals exact narrow _ _ _ _ _

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
  all_goals intros
  all_goals simp [ctree_semantics, RuntimeValue.Conforms, RuntimeValue.isRefinedBy, -Attribute.integerType_eq_of]
  all_goals exact narrow _ _ _

theorem gmir_anyext_status : Status Unproven gmirAnyext_pattern := .unproven .wideOperand

/-! ## The remaining rewrites

The split loads and stores, the inline memory intrinsics, the `getelementptr` lowering and the
argument lowering of `isel-abi-riscv64` are Puddle patterns, stated at every parameter their
drivers instantiate them at. The argument lowering is proven; the three memory families need the
support of memory effects in `Pattern.Supported`, as the loads and stores proven on the wip
branch do, and `getelementptr` the address lemmas of that branch. -/

theorem split_load_valid (bytes : Nat) (hbytes : bytes ∈ [3, 5, 6, 7]) :
    Puddle.CTree.Pattern.Valid (splitLoad_pattern bytes) := by
  sorry

theorem split_store_valid (bytes : Nat) (hbytes : bytes ∈ [3, 5, 6, 7]) :
    Puddle.CTree.Pattern.Valid (splitStore_pattern bytes) := by
  sorry

/-- The accesses are those of `memIntrinsicAccesses?`, which the matcher checks: they partition
the intrinsic's length, and a `memcpy` reads each piece before writing it. -/
theorem mem_intrinsic_inline_valid (isMemset : Bool) (accesses : Array (Nat × Nat)) (fill : MemFill) :
    Puddle.CTree.Pattern.Valid (memIntrinsicInline_pattern isMemset accesses fill) := by
  sorry

/-- The address computed on registers is `interpretGEP` of the indices, as `gepDecomposition?`
decomposes it. -/
theorem getelementptr_valid (strides : Array Nat) (offset : GEPOffset) :
    Puddle.CTree.Pattern.Valid (getelementptr_pattern strides offset) := by
  sorry

/-- The `g_trunc` of a register's `i64` reads the low bits that the narrow cast of the register
reads. -/
theorem toInt_trunc_toInt (r : Data.RISCV.Reg) (tb : Nat) (h : 64 > tb) :
    RISCV.Reg.toInt r tb ⊒ (RISCV.Reg.toInt r 64).trunc tb false false h := by
  simp [RISCV.Reg.toInt, Data.LLVM.Int.trunc, isRefinedBy, Id.run,
    BitVec.setWidth_setWidth_of_le r.val (by omega : tb ≤ 64)]

/-- The argument lowering reduces to `toInt_trunc_toInt`: the matcher bounds the narrow width
by 64, which the remaining width guard contradicts. -/
theorem formal_argument_valid : Puddle.CTree.Pattern.Valid lowerFormalArgument_pattern := by
  unfold lowerFormalArgument_pattern
  simpPuddleValid
  simpLegalSemantics
  normalizeIselValid
  all_goals first
    | (exfalso; omega)
    | exact toInt_trunc_toInt _ _ _

/-- The branch lowering of `isel-br-riscv64` rewrites terminators and block arguments, which no
local rewrite statement covers, so its obligation is that every function of the module is
refined by its lowering: the casts to registers before each branch and back at each block
argument are the identity on the values that reach the block, and a fused compare-and-branch
tests what the `g_icmp` it replaces computed. -/
theorem convertModule_refines {ctx ctx' : WfIRContext OpCode} (h : convertModule ctx = .ok ctx')
    (op : OperationPtr) (opIn : op.InBounds ctx.raw) (opIn' : op.InBounds ctx'.raw)
    (hfunc : (FunctionOp.of? op ctx.raw).isSome) :
    op.isRefinedByAsFunction ctx op ctx' opIn opIn' := by
  sorry

/- `lowerReturn` and `lowerCall` of `isel-abi-riscv64` are not `LocalRewritePattern.Sound`, and
the pass is not a function refinement either: a return copies an `i32` result into its register
sign-extended as the ABI requires, so the lowered function returns a different register value,
and a `riscv_cf.call` has no semantics in the interpreter (`memcpy_call_fails`). Their statement
is a refinement up to the ABI, relating a function's results and arguments to the registers that
carry them, which does not exist yet. -/

end Veir.ISel.CTreeProofs
