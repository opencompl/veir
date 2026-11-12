module

public import Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.PatternRewriter.Puddle.CTreeProofs
public import Veir.Passes.CastsReconciliation.Reconciliation
public import Veir.Passes.Pipeline.Soundness
import all Veir.Passes.Legalization.Validity.Common
import all Veir.Passes.CastsReconciliation.Reconciliation
import all Veir.Interpreter.RuntimeValue.Conforms
import all Veir.Dialects.Builtin.Interpreter
import all Veir.Dialects.Builtin.OpInfo
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV.Properties
import all Veir.Dialects.RISCV.Interpreter
import all Veir.Dialects.RV64.OpInfo
import all Veir.Data.RISCV.Reg.Basic
import all Veir.Data.RISCV.Reg.Lemmas
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.Casting
import all Veir.Data.Refinement
import all Veir.Interpreter.Memory
import all Init.Data.Array.Basic

/-!
# CTree validity of the cast reconciliation

Every Puddle pattern of `reconcile-cast` has a `Status`: a proof of `Puddle.CTree.Pattern.Valid`,
or the reason why there is none (see `Unproven`).

* The round trips of a register through `i64`, and through an `i8`, `i16` or `i32` (as `zext.b`,
  `zext.h` and `zext.w`), are proven: casting a register to an integer is never poison.
* The `mod_arith` and `cir` round trips are proven vacuously: the interpreter has no semantics
  for those casts, so the source fails.
* The pointer/register round trips and the two-shift register round trip are not valid, for the
  reasons in `Unproven`.

The proofs are those of the gMIR legalization rules (`Veir.Passes.Legalization.Validity`), with
the builtin and RISC-V interpreters added to the semantics.
-/

namespace Veir.CastsReconciliation.CTreeProofs

open Puddle
open Puddle.CTree
open _root_.CTree

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Builtin.interpretOpCTree Builtin.interpretUnrealizedConversionCastCTree
  Riscv.interpretOp' Rv64.interpretOp' RISCV.Reg.toInt

attribute [local simp] Builtin.getEffects

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

/-- Only a register conforms to a register type. -/
theorem conforms_of_val_registerType {v : RuntimeValue} {t : TypeAttr}
    {r : RegisterType} (h : t.val = .registerType r) :
    v.Conforms t ↔ (match v with | .reg _ => True | _ => False) := by
  rcases t with ⟨attr, _⟩
  subst h
  cases v <;> simp [RuntimeValue.Conforms]

/-- Only an integer of its width conforms to an integer type. -/
theorem conforms_of_val_integerType {v : RuntimeValue} {t : TypeAttr}
    {i : IntegerType} (h : t.val = .integerType i) :
    v.Conforms t ↔ (match v with | .int bw _ => i.bitwidth = bw | _ => False) := by
  rcases t with ⟨attr, _⟩
  subst h
  cases v <;> simp [RuntimeValue.Conforms]

/-- Only an address conforms to a pointer type. -/
theorem conforms_of_val_llvmPointerType {v : RuntimeValue} {t : TypeAttr}
    {p : LLVM.PointerType} (h : t.val = .llvmPointerType p) :
    v.Conforms t ↔ (match v with | .addr _ => True | _ => False) := by
  rcases t with ⟨attr, _⟩
  subst h
  cases v <;> simp [RuntimeValue.Conforms]

/-- Only an integer of the width of its modulus conforms to a `mod_arith` type. -/
theorem conforms_of_val_modArithType {v : RuntimeValue} {t : TypeAttr}
    {m : ModArithType} (h : t.val = .modArithType m) :
    v.Conforms t ↔ (match v with | .int bw _ => m.modulus.type.bitwidth = bw | _ => False) := by
  rcases t with ⟨attr, _⟩
  subst h
  cases v <;> simp [RuntimeValue.Conforms]

/-- No value conforms to a `cir` integer type. -/
theorem conforms_of_val_cirIntType {v : RuntimeValue} {t : TypeAttr}
    {c : CirIntType} (h : t.val = .cirIntType c) : v.Conforms t ↔ False := by
  rcases t with ⟨attr, _⟩
  subst h
  cases v <;> simp [RuntimeValue.Conforms]

/-- No value conforms to the `cir` boolean type. -/
theorem conforms_of_val_cirBoolType {v : RuntimeValue} {t : TypeAttr}
    {c : CirBoolType} (h : t.val = .cirBoolType c) : v.Conforms t ↔ False := by
  rcases t with ⟨attr, _⟩
  subst h
  cases v <;> simp [RuntimeValue.Conforms]

public section

/-- Why a pattern of `reconcile-cast` has no CTree validity proof. -/
inductive Unproven where
  /-- The `ptr -> reg -> ptr` round trip freezes a poison pointer: the cast to a register chooses
  its bits, so the source yields a defined pointer, while the rewrite returns the poison pointer
  itself. This is the reason `i64 -> reg -> i64` is not reconciled, and why `isRiscvRegToPtrCast`
  only matches the `reg -> ptr -> reg` round trip, which is the identity. -/
  | freezesPoisonPointer
  /-- The matcher accepts a register round trip through an integer of any width but 0, 8, 16 and
  32, while the replacement is only created below width 64, so that over-wide casts keep making
  the pass fail. A replacement that fails is a target that fails, which `Pattern.Valid` does not
  allow. Below width 64 the two shifts are the round trip (`srli_slli_eq`). -/
  | createFailsOverWide
  deriving Repr, DecidableEq

end

/-- A register cast to an `i8` and back is its `zext.b`. -/
theorem zextb_eq (r : Data.RISCV.Reg) :
    ({ val := BitVec.setWidth 64 (BitVec.setWidth 8 r.val) } : Data.RISCV.Reg) = Data.RISCV.zextb r := by
  cases r
  simp only [Data.RISCV.zextb, Data.RISCV.andi, Data.RISCV.Reg.mk.injEq]
  bv_decide

/-- A register cast to an `i16` and back is its `zext.h`. -/
theorem zexth_eq (r : Data.RISCV.Reg) :
    ({ val := BitVec.setWidth 64 (BitVec.setWidth 16 r.val) } : Data.RISCV.Reg) = Data.RISCV.zexth r := by
  cases r
  simp only [Data.RISCV.zexth, Data.RISCV.Reg.mk.injEq]
  bv_decide

/-- A register cast to an `i32` and back is its `zext.w`. -/
theorem zextw_eq (r : Data.RISCV.Reg) :
    ({ val := BitVec.setWidth 64 (BitVec.setWidth 32 r.val) } : Data.RISCV.Reg) = Data.RISCV.zextw r := by
  cases r
  simp only [Data.RISCV.zextw, Data.RISCV.adduw, Data.RISCV.li, Data.RISCV.Reg.mk.injEq]
  bv_decide

/-- Shifting a register left and back right by `64 - w` keeps its low `w` bits, for `0 < w < 64`:
the register round trip through an `iw`. -/
theorem srli_slli_eq {w : Nat} (h0 : w ≠ 0) (h : w < 64) (r : Data.RISCV.Reg) :
    Data.RISCV.srli (RISCVImmediateProperties.immField ⟨BitVec.ofNat 64 (64 - w)⟩ 6)
        (Data.RISCV.slli (RISCVImmediateProperties.immField ⟨BitVec.ofNat 64 (64 - w)⟩ 6) r) =
      { val := BitVec.setWidth 64 (BitVec.setWidth w r.val) } := by
  cases r with | mk v =>
  simp only [Data.RISCV.srli, Data.RISCV.slli, RISCVImmediateProperties.immField,
    Data.RISCV.Reg.mk.injEq]
  ext i hi
  simp
  rw [Nat.mod_eq_of_lt (by omega : 64 - w < 64)]
  by_cases hiw : i < w <;> simp [hiw] <;> omega

/-- The register round trip through `i64`. -/
@[local simp] theorem isRegToI64RoundTrip_iff (a b : TypeAttr) :
    isRegToI64RoundTrip a b = true ↔
      (∃ r, a.val = .registerType r) ∧ ∃ i, b.val = .integerType i ∧ i.bitwidth = 64 := by
  rcases a with ⟨a, _⟩
  rcases b with ⟨b, _⟩
  cases a <;> cases b <;> simp [isRegToI64RoundTrip, -Attribute.integerType_eq_of]

/-- The register round trip through a pointer. -/
@[local simp] theorem isRiscvRegToPtrCast_iff (a b : TypeAttr) :
    isRiscvRegToPtrCast a b = true ↔
      (∃ r, a.val = .registerType r) ∧ ∃ p, b.val = .llvmPointerType p := by
  rcases a with ⟨a, _⟩
  rcases b with ⟨b, _⟩
  cases a <;> cases b <;> simp [isRiscvRegToPtrCast, -Attribute.integerType_eq_of]

/-- The `mod_arith`/integer round trips, in either order. -/
@[local simp] theorem isPreservingModArithToIntCast_iff (a b : TypeAttr) :
    isPreservingModArithToIntCast a b = true ↔
      ((∃ m, a.val = .modArithType m) ∧ ∃ i, b.val = .integerType i) ∨
        ((∃ i, a.val = .integerType i) ∧ ∃ m, b.val = .modArithType m) := by
  rcases a with ⟨a, _⟩
  rcases b with ⟨b, _⟩
  cases a <;> cases b <;> simp [isPreservingModArithToIntCast, -Attribute.integerType_eq_of]

/-- The `cir`/integer round trips, in either order, at the width of the `cir` type. -/
@[local simp] theorem isCirToIntRoundTrip_iff (a b : TypeAttr) :
    isCirToIntRoundTrip a b = true ↔
      (∃ it, a.val = .cirIntType it ∧ ∃ i, b.val = .integerType i ∧ i.bitwidth = it.width) ∨
      (∃ i, a.val = .integerType i ∧ ∃ it, b.val = .cirIntType it ∧ i.bitwidth = it.width) ∨
      ((∃ c, a.val = .cirBoolType c) ∧ ∃ i, b.val = .integerType i ∧ i.bitwidth = 1) ∨
      (∃ i, a.val = .integerType i ∧ i.bitwidth = 1 ∧ ∃ c, b.val = .cirBoolType c) := by
  rcases a with ⟨a, _⟩
  rcases b with ⟨b, _⟩
  cases a <;> cases b <;> simp [isCirToIntRoundTrip, -Attribute.integerType_eq_of]

attribute [local simp] conforms_of_val_registerType conforms_of_val_integerType
  conforms_of_val_llvmPointerType conforms_of_val_modArithType conforms_of_val_cirIntType
  conforms_of_val_cirBoolType in
theorem reg_i64_valid : Puddle.CTree.Pattern.Valid (reconcilePairingCast isRegToI64RoundTrip) := by
  proveLegalValid using isRefinedBy_refl

attribute [local simp] conforms_of_val_registerType conforms_of_val_integerType
  conforms_of_val_llvmPointerType conforms_of_val_modArithType conforms_of_val_cirIntType
  conforms_of_val_cirBoolType in
theorem reg_ptr_valid : Puddle.CTree.Pattern.Valid (reconcilePairingCast isRiscvRegToPtrCast) := by
  proveLegalValid using isRefinedBy_refl

attribute [local simp] conforms_of_val_registerType conforms_of_val_integerType
  conforms_of_val_llvmPointerType conforms_of_val_modArithType conforms_of_val_cirIntType
  conforms_of_val_cirBoolType in
theorem mod_arith_int_valid :
    Puddle.CTree.Pattern.Valid (reconcilePairingCast isPreservingModArithToIntCast) := by
  proveLegalValid using isRefinedBy_refl

attribute [local simp] conforms_of_val_registerType conforms_of_val_integerType
  conforms_of_val_llvmPointerType conforms_of_val_modArithType conforms_of_val_cirIntType
  conforms_of_val_cirBoolType in
theorem cir_int_valid : Puddle.CTree.Pattern.Valid (reconcilePairingCast isCirToIntRoundTrip) := by
  proveLegalValid with
    obtain ⟨_, h, _⟩ | ⟨_, _, h⟩ := ‹_ ∨ _› <;> simp [h] at *

theorem reg_i8_valid : Puddle.CTree.Pattern.Valid (reconcileRegIntExt 8 .zextb ()) := by
  proveLegalValid with exact zextb_eq _

theorem reg_i16_valid : Puddle.CTree.Pattern.Valid (reconcileRegIntExt 16 .zexth ()) := by
  proveLegalValid with exact zexth_eq _

theorem reg_i32_valid : Puddle.CTree.Pattern.Valid (reconcileRegIntExt 32 .zextw ()) := by
  proveLegalValid with exact zextw_eq _

/-! ## Status of every pattern of `reconcile-cast` -/

theorem reg_i64_status : Status Unproven (reconcilePairingCast isRegToI64RoundTrip) :=
  .proven reg_i64_valid

theorem reg_ptr_status : Status Unproven (reconcilePairingCast isRiscvRegToPtrCast) :=
  .proven reg_ptr_valid

theorem mod_arith_int_status :
    Status Unproven (reconcilePairingCast isPreservingModArithToIntCast) :=
  .proven mod_arith_int_valid

theorem cir_int_status : Status Unproven (reconcilePairingCast isCirToIntRoundTrip) :=
  .proven cir_int_valid

theorem reg_i8_status : Status Unproven (reconcileRegIntExt 8 .zextb ()) :=
  .proven reg_i8_valid

theorem reg_i16_status : Status Unproven (reconcileRegIntExt 16 .zexth ()) :=
  .proven reg_i16_valid

theorem reg_i32_status : Status Unproven (reconcileRegIntExt 32 .zextw ()) :=
  .proven reg_i32_valid

theorem reg_int_shift_status : Status Unproven reconcileRegIntShift :=
  .unproven .createFailsOverWide

/-! ## The pass -/

public section

/-- Every pattern the pass applies is valid. -/
theorem reconcilePatterns_valid :
    ∀ rule ∈ reconcilePatterns, Puddle.CTree.Pattern.Valid rule := by
  intro rule member
  simp only [reconcilePatterns, List.mem_toArray, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact reg_i64_valid
  · exact reg_ptr_valid
  · exact mod_arith_int_valid
  · exact cir_int_valid
  · exact reg_i8_valid
  · exact reg_i16_valid
  · exact reg_i32_valid

/-- The `reconcile-cast` pass refines the module and leaves it verified. -/
theorem CastReconcilePass.run_sound : CastReconcilePass.run.Sound :=
  checkedContextPasses_sound fun pattern member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact RewritePattern.PointwiseValid.greedy_compiled reconcilePatterns_valid
    · exact RewritePattern.PointwiseValid.empty

/-- The pass with its IO returns what `CastReconcilePass.run` does. -/
theorem CastReconcilePass.impl_eq_run (ctx : WfIRContext OpCode) (op : OperationPtr)
    (opIn : op.InBounds ctx.raw) :
    CastReconcilePass.impl ctx op opIn = ExceptT.mk (pure (CastReconcilePass.run ctx op)) := by
  rw [CastReconcilePass.impl]

end
end Veir.CastsReconciliation.CTreeProofs
