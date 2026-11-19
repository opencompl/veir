module

public import Veir.Passes.LLVMToGMIR.BranchSimulation
public import Veir.Passes.KeptValuesSimulation
public import Veir.Passes.LLVMToGMIR.BranchPass
public import Veir.Passes.InstructionSelection.Branches.Pass
public import Veir.Passes.Legalization.Legalizer
public import Veir.Passes.Legalization.LegalizerHelper

import all Veir.Passes.Legalization.LegalizerHelper
import all Veir.Passes.Legalization.Legalizer
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Data.LLVM.Int.Basic
import all Veir.IR.Attribute
import Veir.Interpreter.Lemmas
import Veir.Interpreter.Refinement.Lemmas
import Veir.Interpreter.Refinement.Monotonicity
import Veir.Dialects.GMIR.Lemmas
import all Veir.Interpreter.VariableState
import all Veir.Interpreter.Refinement.Basic
import all Veir.IR.Basic
import all Veir.Interfaces.FunctionInterfaces
import all Veir.GlobalOpInfo
import all Veir.Dialects.Func.OpInfo
import all Veir.Interpreter.CTreeInterpreter

public section

/-!
# Widening the branch conditions refines the module

`widenBrconds` succeeds only with a module that is the `BrcondWidening` of its input: every
`g_brcond` it widens is replaced, in the list of its block, by a `g_zext` of its condition and a
`g_brcond` on it, with the other operands, the successors and the properties of the branch.
Everything else, the values and their types included, is unchanged. The module it returns refines
its input, if the operations of the input are monotone in CTrees: the widening keeps every value
(`Veir.Passes.KeptValuesSimulation`), so it only has to show that the operations of each block
simulate those of the source, as the branch step of `llvm-to-gmir` does.
-/

open CTree Veir.CTree

namespace Veir

/-! ## The widened branch -/

/-- A `g_zext` of a defined integer to a wider integer type is its zero extension. -/
theorem interpretOp'_gmir_g_zext_val {properties : propertiesOf (OpCode.gmir .g_zext)}
    {w width : Nat} (cond : BitVec w) (hw : w < width) (hNneg : properties.nneg = false)
    (successors : Array BlockPtr) (mem : MemoryState) :
    Veir.interpretOp' (.gmir .g_zext) properties #[(IntegerType.signless width : TypeAttr)]
        #[.int w (.val cond)] successors mem =
      .ok (#[.int width (.val (cond.zeroExtend width))], mem, none) := by
  have : ¬ width ≤ w := by omega
  simp [Veir.interpretOp', GMIR.interpretOp', Data.LLVM.Int.zext, hNneg, Id.run,
    IntegerType.signless, TypeAttr.of_def, Attribute.of_def, IsAttr.inject,
    -Attribute.integerType_eq_of]
  split <;> rename_i h
  · obtain rfl := Option.some.inj (h.symm.trans rfl)
    simp [this]
  · exact absurd rfl (h _)

/-- The `g_brcond` of a zero extension of a condition branches where one on the condition does: the
zero extension of a value to a wider integer is zero exactly when the value is. -/
theorem zeroExtend_ne_zero_iff {w width : Nat} (hw : w ≤ width) (cond : BitVec w) :
    cond.zeroExtend width ≠ 0 ↔ cond ≠ 0 := by
  have hlt : cond.toNat < 2 ^ width :=
    Nat.lt_of_lt_of_le cond.isLt (Nat.pow_le_pow_right (by decide) hw)
  constructor
  · intro h hc
    exact h (by subst hc; simp)
  · intro h hz
    apply h
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat hz
    simp only [BitVec.toNat_setWidth, BitVec.truncate_eq_setWidth] at this
    simp at this
    rw [Nat.mod_eq_of_lt hlt] at this
    simpa using this

/-- The operands of the new `g_brcond` past the condition are those of the old one. -/
theorem extract_cons_tail {α : Type} (x : α) (b : Array α) (hb : 0 < b.size) {i j : Nat}
    (hi : 1 ≤ i) : (#[x] ++ b.extract 1 b.size).extract i j = b.extract i j := by
  apply Array.ext
  · simp; omega
  · intro k hk₁ hk₂
    simp only [Array.getElem_extract, Array.getElem_append]
    grind

/-- The first operand of the new `g_brcond` is the zero extension. -/
theorem getElem!_cons_extract_zero {α : Type} [Inhabited α] (x : α) (b : Array α) :
    (#[x] ++ b.extract 1 b.size)[0]! = x := by
  rw [getElem!_pos _ 0 (by simp; omega)]
  simp

/-- The other operands of the new `g_brcond` are those of the old one. -/
theorem getElem!_cons_extract_tail {α : Type} [Inhabited α] (x : α) (b : Array α) {i : Nat}
    (hi0 : 0 < i) (hi : i < b.size) : (#[x] ++ b.extract 1 b.size)[i]! = b[i] := by
  rw [getElem!_pos _ i (by simp; omega)]
  simp only [Array.getElem_append, Array.getElem_extract]
  grind

/-- The condition of the new `g_brcond` is the zero extension. -/
theorem getElem?_cons_extract_zero {α : Type} (x : α) (b : Array α) :
    (#[x] ++ b.extract 1 b.size)[0]? = some x := by
  rw [Array.getElem?_eq_getElem (by simp; omega)]
  simp

/-! ## What widening the branch conditions does to a module -/

/-- The operations that stand for `op` after the widening: the `g_zext` of its condition and the
new `g_brcond` if `op` is widened, and `op` itself otherwise. -/
@[expose]
def widenOp (widened : OperationPtr → Bool) (ext newBranch : OperationPtr → OperationPtr)
    (op : OperationPtr) : List OperationPtr :=
  if widened op then [ext op, newBranch op] else [op]

/-- What widening the condition of the `g_brcond` `op` of `ctx` leaves in `ctx'`: a `g_zext` `ext`
of its condition to a wider integer, and a `g_brcond` `newBranch` on it, with the other operands,
the successors and the properties of `op`. -/
structure WidenedBrcond (ctx ctx' : WfIRContext OpCode) (op ext newBranch : OperationPtr) :
    Prop where
  brcond : op.getOpType! ctx.raw = .gmir .g_brcond
  numResults : op.getNumResults! ctx.raw = 0
  extIn : ext.InBounds ctx'.raw
  extFresh : ∀ value : ValuePtr, value.InBounds ctx.raw → value ≠ .opResult (ext.getResult 0)
  extType : ext.getOpType! ctx'.raw = .gmir .g_zext
  extOperands : ext.getOperands! ctx'.raw = #[(op.getOperands! ctx.raw)[0]!]
  extNneg : (ext.getProperties! ctx'.raw (OpCode.gmir .g_zext)).nneg = false
  extWidth : ∃ type : IntegerType, ∃ width,
    (0 < (op.getOperands! ctx.raw).size →
      ((op.getOperands! ctx.raw)[0]!.getType! ctx.raw).val = .integerType type) ∧
    type.bitwidth < width ∧
    ext.getResultTypes! ctx'.raw = #[(IntegerType.signless width : TypeAttr)]
  newIn : newBranch.InBounds ctx'.raw
  newType : newBranch.getOpType! ctx'.raw = .gmir .g_brcond
  newResultTypes : newBranch.getResultTypes! ctx'.raw = #[]
  newOperands : newBranch.getOperands! ctx'.raw =
    #[ValuePtr.opResult (ext.getResult 0)] ++
      (op.getOperands! ctx.raw).extract 1 (op.getOperands! ctx.raw).size
  newSuccessors : newBranch.getSuccessors! ctx'.raw = op.getSuccessors! ctx.raw
  newSegments : (newBranch.getProperties! ctx'.raw (OpCode.gmir .g_brcond)).operandSegmentSizes =
    (op.getProperties! ctx.raw (OpCode.gmir .g_brcond)).operandSegmentSizes

/-- `ctx'` is `ctx` with the conditions of the branches `widened` widened. -/
structure BrcondWidening (ctx ctx' : WfIRContext OpCode) where
  /-- The branches whose condition is widened. -/
  widened : OperationPtr → Bool
  /-- The `g_zext` of the condition of a widened branch. -/
  ext : OperationPtr → OperationPtr
  /-- The `g_brcond` that replaces a widened branch. -/
  newBranch : OperationPtr → OperationPtr
  /-- The blocks and regions stay. -/
  ctxSame : CtxSame ctx.raw ctx'.raw
  /-- The values and their types stay. -/
  types : ∀ value : ValuePtr, value.InBounds ctx.raw →
    value.InBounds ctx'.raw ∧ value.getType! ctx'.raw = value.getType! ctx.raw
  /-- An operation other than a widened branch stays. -/
  opSame {op : OperationPtr} : op.InBounds ctx.raw → widened op = false →
    OpSame id ctx.raw ctx'.raw op
  /-- In the list of a block, each widened branch is replaced by its `g_zext` and new branch. -/
  opList {block : BlockPtr} (blockIn : block.InBounds ctx.raw) :
    block.opList ctx' (ctxSame.blockIn blockIn) =
      (block.opList ctx blockIn).flatMap (widenOp widened ext newBranch)
  /-- A widened branch is a `g_brcond` replaced as `WidenedBrcond` says. -/
  spec {op : OperationPtr} : op.InBounds ctx.raw → widened op = true →
    WidenedBrcond ctx ctx' op (ext op) (newBranch op)

variable {ctx ctx' : WfIRContext OpCode}

namespace BrcondWidening

variable (W : BrcondWidening ctx ctx')

include W

/-! ## The relations of the proof -/

/-- An operation that is not a `g_brcond` is not widened. -/
theorem widened_eq_false {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hType : op.getOpType! ctx.raw ≠ .gmir .g_brcond) : W.widened op = false := by
  cases hW : W.widened op
  · rfl
  · exact absurd (W.spec opIn hW).brcond hType

/-- The widening keeps every value: it only replaces branches. -/
theorem keptValues : KeptValues ctx ctx' :=
  ⟨W.ctxSame, W.types, fun funcIn hFunc => W.opSame funcIn (W.widened_eq_false funcIn (by simp [hFunc]))⟩

/-- Every value of the source stands for itself in the target. -/
abbrev mapping : ValueMapping ctx ctx' := W.keptValues.mapping

@[simp] theorem mapping_val {value : ValuePtr} {valueIn : value.InBounds ctx.raw} :
    (W.mapping ⟨value, valueIn⟩).val = value := rfl

theorem applyToArray_mapping {values : Array ValuePtr}
    (valuesIn : ∀ v ∈ values, v.InBounds ctx.raw) :
    W.mapping.applyToArray values valuesIn = values :=
  W.keptValues.applyToArray_mapping valuesIn

/-- Two states whose variables and memories refine. -/
abbrev StateRel := W.keptValues.StateRel

/-- How the outcomes of an operation and of what stands for it relate. -/
abbrev OpRel := W.keptValues.OpRel

/-- The values of source values in a related target state refine their values in the source. -/
theorem mapM_getVar?_isRefinedBy {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    (hState : W.StateRel state state') {values : Array ValuePtr}
    (valuesIn : ∀ v ∈ values, v.InBounds ctx.raw) {sources : Array RuntimeValue}
    (h : values.mapM state.variables.getVar? = some sources) :
    ∃ targets, values.mapM state'.variables.getVar? = some targets ∧ sources ⊒ targets := by
  have hSize := Array.size_eq_of_mapM_eq_some h
  have hTarget : ∀ i (hi : i < values.size), ∃ tv,
      state'.variables.getVar? values[i] = some tv ∧ sources[i]! ⊒ tv := by
    intro i hi
    have hs := Array.mapM_option_eq_some_implies h i (by omega)
    obtain ⟨tv, hTv, hRef⟩ := hState.2 _ (valuesIn _ (Array.getElem_mem hi)) _ hs
    exact ⟨tv, by simpa using hTv, by rw [getElem!_pos sources i (by omega)]; exact hRef⟩
  obtain ⟨targets, hTargets⟩ := Array.mapM_option_isSome (f := state'.variables.getVar?)
    (l := values) fun i hi => by
      obtain ⟨tv, hTv, -⟩ := hTarget i hi
      simp [hTv]
  have hSize' := Array.size_eq_of_mapM_eq_some hTargets
  refine ⟨targets, hTargets, by omega, fun i hi => ?_⟩
  obtain ⟨tv, hTv, hRef⟩ := hTarget i (by omega)
  have ht := Array.mapM_option_eq_some_implies hTargets i (by omega)
  rw [hTv] at ht
  rw [getElem!_pos targets i (by omega), ← Option.some.inj ht]
  exact hRef

/--
  The `g_zext` and the new `g_brcond` of a widened branch run as the branch does, where the branch
  is defined, on refined operands: the condition is defined, so its refinement is the condition,
  which the `g_zext` widens without changing whether it is zero, and the other operands are those
  of the branch.
-/
theorem interpretOp_widened {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hW : W.widened op = true) {state : InterpreterState ctx} {state' : InterpreterState ctx'}
    (hState : W.StateRel state state') {source : InterpreterState ctx}
    {action : Option ControlFlowAction}
    (hsrc : Veir.interpretOp op state opIn = .ok (source, action)) :
    ∃ mid, Veir.interpretOp (W.ext op) state' (W.spec opIn hW).extIn = .ok (mid, none) ∧
      ∃ target action',
        Veir.interpretOp (W.newBranch op) mid (W.spec opIn hW).newIn = .ok (target, action') ∧
        W.StateRel source target ∧ ControlFlowAction.optionIsRefinedBy action action' := by
  have S := W.spec opIn hW
  obtain ⟨operands, results, mem, variables, hOperands, hInterp, hSet, rfl⟩ :=
    interpretOp_some_iff.mp hsrc
  simp only [OperationPtr.interpret] at hInterp
  rw [S.brcond] at hInterp
  obtain ⟨destTrue, destFalse, w, cond, n, hSucc, hCond, hN, rfl, rfl, rfl⟩ :=
    interpretOp'_gmir_g_brcond_eq_ok_iff.mp hInterp
  have hVariables : state.variables = variables := by
    rw [VariableState.setResultValues?_empty S.numResults] at hSet
    exact Option.some.inj hSet
  subst hVariables
  /- The operands of the branch, in the source and in the target. -/
  have ptrsIn : ∀ v ∈ op.getOperands! ctx.raw, v.InBounds ctx.raw := by grind
  have hOperands' : (op.getOperands! ctx.raw).mapM state.variables.getVar? = some operands :=
    hOperands
  obtain ⟨targets, hTargets, hRefined⟩ := W.mapM_getVar?_isRefinedBy hState ptrsIn hOperands'
  have hSize := Array.size_eq_of_mapM_eq_some hOperands'
  have h0 : 0 < operands.size := by
    obtain ⟨h0, -⟩ := Array.getElem?_eq_some_iff.mp hCond; exact h0
  /- The condition is defined, of the width of its type. -/
  obtain ⟨type, width, hType, hWidth, hExtTypes⟩ := S.extWidth
  have hCondVar : state.variables.getVar? (op.getOperands! ctx.raw)[0]! =
      some (.int w (.val cond)) := by
    have := Array.mapM_option_eq_some_implies hOperands' 0 h0
    rw [getElem!_pos _ 0 (by omega), this, ← Array.getElem?_eq_getElem]
    exact hCond
  have hConf := VariableState.getVar?_conforms hCondVar
  have hw : w = type.bitwidth := by
    revert hConf
    have hType := hType (by omega)
    rcases hTy : (op.getOperands! ctx.raw)[0]!.getType! ctx.raw with ⟨attr, hattr⟩
    simp only [hTy] at hType
    subst hType
    simp [RuntimeValue.Conforms, eq_comm]
  subst hw
  have hTarget0 : targets[0]! = .int type.bitwidth (.val cond) := by
    have := hRefined.2 0 h0
    rw [getElem!_pos operands 0 h0, Array.getElem?_eq_some_iff.mp hCond |>.2] at this
    exact RuntimeValue.int_val_isRefinedBy_iff.mp this
  have hTSize := Array.size_eq_of_mapM_eq_some hTargets
  have hCondVar' : state'.variables.getVar? (op.getOperands! ctx.raw)[0]! =
      some (.int type.bitwidth (.val cond)) := by
    have := Array.mapM_option_eq_some_implies hTargets 0 (by omega)
    rw [getElem!_pos _ 0 (by omega), this, ← hTarget0, getElem!_pos targets 0 (by omega)]
  /- The `g_zext` binds the zero extension of the condition. -/
  have hExtOperands : state'.variables.getOperandValues (W.ext op) =
      some #[.int type.bitwidth (.val cond)] := by
    simp only [OperationPtr.getOperands!.getElem!_eq_getOperand!] at hCondVar'
    simp [VariableState.getOperandValues, S.extOperands, hCondVar']
  have hExtRun : (W.ext op).interpret ctx'.raw #[.int type.bitwidth (.val cond)] state'.memory =
      .ok (#[.int width (.val (cond.zeroExtend width))], state'.memory, none) := by
    simp only [OperationPtr.interpret]
    rw [S.extType, hExtTypes]
    exact interpretOp'_gmir_g_zext_val cond hWidth S.extNneg _ _
  have hExtConforms : RuntimeValue.ArrayConforms #[.int width (.val (cond.zeroExtend width))]
      ((W.ext op).getResultTypes! ctx'.raw) := by
    simp [RuntimeValue.ArrayConforms, hExtTypes, IntegerType.signless]
  obtain ⟨midVars, hMidSet⟩ :=
    (VariableState.setResultValues?_isSome_iff_conforms state'.variables S.extIn).mp hExtConforms
  refine ⟨⟨midVars, state'.memory⟩,
    (interpretOp_ok_iff_of_getOperandValues_eq_some hExtOperands).mpr ⟨_, hExtRun, hMidSet⟩, ?_⟩
  have hExtNum : (W.ext op).getNumResults! ctx'.raw = 1 := by
    rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hExtTypes]; rfl
  have hMidExt : midVars.getVar? ((W.ext op).getResult 0) =
      some (.int width (.val (cond.zeroExtend width))) := by
    rw [VariableState.getVar?_setResultValues? hMidSet]
    simp [OperationPtr.getResult_def, hExtNum]
  /- A value of the source is not a result of the `g_zext`, which the source does not have. -/
  have hMidSource : ∀ v : ValuePtr, v.InBounds ctx.raw →
      midVars.getVar? v = state'.variables.getVar? v := by
    intro v vIn
    refine VariableState.getVar?_setResultValues?_of_notMem_getResults! ?_ hMidSet
    intro hMem
    obtain ⟨index, hIndex, rfl⟩ := OperationPtr.getResults!.mem_iff_exists_index.mp hMem
    obtain rfl : index = 0 := by omega
    exact S.extFresh _ vIn rfl
  /- The new branch reads the zero extension and the other operands of the branch. -/
  have hT0 : 0 < targets.size := by omega
  let values' : Array RuntimeValue :=
    #[.int width (.val (cond.zeroExtend width))] ++ targets.extract 1 targets.size
  have hValuesSize : values'.size = targets.size := by simp [values']; omega
  have hNum : op.getNumOperands! ctx.raw = targets.size := by
    rw [← OperationPtr.getOperands!.size_eq_getNumOperands!]; exact hTSize
  have hNewOperands : midVars.getOperandValues (W.newBranch op) = some values' := by
    simp only [VariableState.getOperandValues, S.newOperands]
    rw [Array.mapM_eq_some_iff_of_size_eq (by simp [values']; omega)]
    intro i hi
    simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add, Array.size_extract] at hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [getElem!_cons_extract_zero, getElem!_cons_extract_zero]
      exact hMidExt
    · have hiT : i < targets.size := by omega
      rw [getElem!_cons_extract_tail _ _ hi0 (by omega),
        getElem!_cons_extract_tail _ _ hi0 hiT,
        hMidSource _ (ptrsIn _ (Array.getElem_mem _))]
      exact Array.mapM_option_eq_some_implies hTargets i hiT
  have hNewNum : (W.newBranch op).getNumResults! ctx'.raw = 0 := by
    rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, S.newResultTypes]; rfl
  have hNewRun : (W.newBranch op).interpret ctx'.raw values' state'.memory =
      .ok (#[], state'.memory, some (if cond.zeroExtend width ≠ 0 then
        .branch (values'.extract 1 (n.toNat + 1)) destTrue
        else .branch (values'.extract (n.toNat + 1) values'.size) destFalse)) := by
    simp only [OperationPtr.interpret]
    rw [S.newType, S.newResultTypes, S.newSuccessors, hSucc]
    exact interpretOp'_gmir_g_brcond_eq_ok_iff.mpr ⟨destTrue, destFalse, width,
      cond.zeroExtend width, n, rfl, getElem?_cons_extract_zero _ _, by rw [S.newSegments]; exact hN,
      rfl, rfl,
      rfl⟩
  refine ⟨⟨midVars, state'.memory⟩, _,
    (interpretOp_ok_iff_of_getOperandValues_eq_some hNewOperands).mpr
      ⟨#[], hNewRun, VariableState.setResultValues?_empty hNewNum⟩,
    ⟨hState.1, fun v vIn sv hv => ?_⟩, ?_⟩
  · obtain ⟨tv, hTv, hRef⟩ := hState.2 v vIn sv hv
    exact ⟨tv, by simpa [hMidSource v vIn] using hTv, hRef⟩
  · have hTail : ∀ j, values'.extract 1 j = targets.extract 1 j := fun j =>
      extract_cons_tail _ _ hT0 (Nat.le_refl 1)
    have hTail' : values'.extract (n.toNat + 1) values'.size =
        targets.extract (n.toNat + 1) targets.size := by
      rw [hValuesSize]; exact extract_cons_tail _ _ hT0 (by omega)
    simp only [zeroExtend_ne_zero_iff (Nat.le_of_lt hWidth), hTail, hTail']
    by_cases hc : cond = 0
    · simpa [hc, ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy] using
        RuntimeValue.arrayIsRefinedBy_extract_size hRefined (n.toNat + 1)
    · have hc' : ¬ cond = 0#type.bitwidth := hc
      simpa [hc', ControlFlowAction.optionIsRefinedBy, ControlFlowAction.isRefinedBy] using
        RuntimeValue.arrayIsRefinedBy_extract hRefined 1 (n.toNat + 1)

/-- An operation that is not widened is the same operation after the widening. -/
theorem preservesOperation {op : OperationPtr} (opIn : op.InBounds ctx.raw)
    (hW : W.widened op = false) :
    W.mapping.PreservesOperation op op opIn (W.opSame opIn hW).inBounds := by
  have hSame := W.opSame opIn hW
  have hNum : op.getNumResults! ctx'.raw = op.getNumResults! ctx.raw := by
    rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hSame.resultTypes,
      OperationPtr.getResultTypes!.size_eq_getNumResults!]
  refine ⟨hSame.opType, ?_, hSame.resultTypes, hSame.successors, ?_, ?_, ?_⟩
  · rw [hSame.properties]
    exact OperationPtr.getProperties!_cast hSame.opType
  · rw [W.applyToArray_mapping, hSame.operands]; simp
  · rw [W.applyToArray_mapping]; simp [OperationPtr.getResults!, hNum]
  · intro value valueIn i h
    simpa using h

/-! ## Single operations -/

/--
  What the proof needs of the operations that the widening keeps: each is refined by itself on
  refined states.
-/
@[expose]
def KeptOpsSim : Prop :=
  ∀ {op : OperationPtr} (opIn : op.InBounds ctx.raw) (hW : W.widened op = false)
    {state : InterpreterState ctx} {state' : InterpreterState ctx'},
    W.StateRel state state' →
    Sim W.OpRel (interpretOperationTree op state' (W.opSame opIn hW).inBounds)
      (interpretOperationTree op state opIn)

/-- The operations of a module that are monotone in CTrees are refined by themselves. -/
theorem keptOpsSim_of_treeMonotoneOps (hMono : TreeMonotoneOps ctx) : W.KeptOpsSim :=
  fun opIn hW _ _ hState => sim_mono
    (interpretOperationTree_sim_of_preservesOperation opIn _ (hMono _ opIn) hState
      (W.preservesOperation opIn hW)) fun _ _ h => ⟨h.1, h.2.1⟩

theorem widenOp_inBounds {op : OperationPtr} (opIn : op.InBounds ctx.raw) :
    ∀ o ∈ widenOp W.widened W.ext W.newBranch op, o.InBounds ctx'.raw := by
  intro o hMem
  unfold widenOp at hMem
  split at hMem
  · next hW =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact (W.spec opIn hW).extIn
    · exact (W.spec opIn hW).newIn
  · next hW =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
    subst hMem
    exact (W.opSame opIn (by simpa using hW)).inBounds

/-! ## Blocks -/

/-- A list of operations is refined by its widening. -/
theorem sim_opList (hKept : W.KeptOpsSim) : ∀ {ops : List OperationPtr}
    (opsIn : ∀ op ∈ ops, op.InBounds ctx.raw)
    (opsIn' : ∀ op ∈ ops.flatMap (widenOp W.widened W.ext W.newBranch), op.InBounds ctx'.raw)
    {state : InterpreterState ctx} {state' : InterpreterState ctx'},
    W.StateRel state state' →
    Sim W.OpRel (opListTree (ops.flatMap (widenOp W.widened W.ext W.newBranch)) state' opsIn')
      (opListTree ops state opsIn)
  | [], _, _, _, _, hState => by
    simp only [List.flatMap_nil, opListTree_nil]
    exact (Sim.pure _ _ _).mpr ⟨hState, trivial⟩
  | op :: ops, opsIn, opsIn', state, state', hState => by
    have opIn := opsIn op (by simp)
    /- What runs after the operations that stand for `op`. -/
    have hCont : ∀ (target : InterpreterState ctx') (action' : Option ControlFlowAction)
        (source : InterpreterState ctx) (action : Option ControlFlowAction)
        (restIn : ∀ o ∈ ops, o.InBounds ctx.raw)
        (restIn' : ∀ o ∈ ops.flatMap (widenOp W.widened W.ext W.newBranch), o.InBounds ctx'.raw),
        W.StateRel source target → ControlFlowAction.optionIsRefinedBy action action' →
        Sim W.OpRel (action'.elim (opListTree _ target restIn') fun cf => pure (target, some cf))
          (action.elim (opListTree ops source restIn) fun cf => pure (source, some cf)) := by
      intro target action' source action restIn restIn' hRel hAction
      rcases action with _ | cf <;> rcases action' with _ | cf' <;>
        simp only [ControlFlowAction.optionIsRefinedBy] at hAction
      · exact sim_opList hKept _ _ hRel
      · exact (Sim.pure _ _ _).mpr ⟨hRel, hAction⟩
    cases hW : W.widened op
    · /- An operation that is kept. -/
      have hList : (op :: ops).flatMap (widenOp W.widened W.ext W.newBranch) =
          op :: ops.flatMap (widenOp W.widened W.ext W.newBranch) := by
        simp [widenOp, hW]
      rw [opListTree_congr hList, opListTree_cons, opListTree_cons]
      apply sim_tau1_left
      apply sim_tau1_right
      rw [tree_bind_eq, tree_bind_eq]
      refine Sim.bind _ _ _ _ (hKept opIn hW hState) ?_
      rintro ⟨target, action'⟩ ⟨source, action⟩ ⟨hRel, hAction⟩
      exact hCont _ _ _ _ _ _ hRel hAction
    · /- A widened branch: its `g_zext` and its new branch. -/
      have S := W.spec opIn hW
      have hList : (op :: ops).flatMap (widenOp W.widened W.ext W.newBranch) =
          W.ext op :: W.newBranch op :: ops.flatMap (widenOp W.widened W.ext W.newBranch) := by
        simp [widenOp, hW]
      rw [opListTree_congr hList, opListTree_cons, opListTree_cons]
      apply sim_tau1_left
      apply sim_tau1_right
      rw [interpretOperationTree_eq_monadLift state opIn (by rw [S.brcond]; rfl)]
      refine sim_monadLift_bind fun ⟨source, action⟩ hsrc => ?_
      obtain ⟨mid, hExt, target, action', hNew, hRel, hAction⟩ :=
        W.interpretOp_widened opIn hW hState hsrc
      rw [interpretOperationTree_eq_monadLift state' _ (by rw [S.extType]; rfl), hExt]
      simp only [monadLift, MonadLift.monadLift, pure_bind, Option.elim_none]
      rw [opListTree_cons]
      apply sim_tau1_left
      rw [interpretOperationTree_eq_monadLift mid _ (by rw [S.newType]; rfl), hNew]
      simp only [monadLift, MonadLift.monadLift, pure_bind]
      exact hCont _ _ _ _ _ _ hRel hAction

/-- The blocks of the widening simulate those of the source. -/
theorem blockListsSim (hKept : W.KeptOpsSim) : W.keptValues.BlockListsSim := by
  intro block blockIn blockIn' state state' hState
  have hList := W.opList blockIn
  simp only [BlockPtr.opList] at hList
  rw [opListTree_congr hList]
  exact W.sim_opList hKept _ _ hState

/-- A module is refined by its widening, in CTrees. -/
theorem isModuleRefinedByCTree (hKept : W.KeptOpsSim) (module : OperationPtr) :
    module.isModuleRefinedByCTree ctx module ctx' :=
  W.keptValues.isModuleRefinedByCTree (W.blockListsSim hKept) module

end BrcondWidening

/-! ## Widening one branch -/

/-- What widening the condition of the branch `op` does. -/
structure BrcondStep (ctx ctx' : WfIRContext OpCode) (op ext newBranch : OperationPtr) : Prop where
  ops : ∀ o, o.InBounds ctx.raw → o ≠ op → OpSame id ctx.raw ctx'.raw o
  ctxSame : CtxSame ctx.raw ctx'.raw
  types : ∀ value : ValuePtr, value.InBounds ctx.raw →
    value.InBounds ctx'.raw ∧ value.getType! ctx'.raw = value.getType! ctx.raw
  widened : WidenedBrcond ctx ctx' op ext newBranch
  extNotIn : ¬ ext.InBounds ctx.raw
  newNotIn : ¬ newBranch.InBounds ctx.raw
  opList : ∀ (block : BlockPtr) (blockIn : block.InBounds ctx.raw),
    block.opList ctx' (ctxSame.blockIn blockIn) =
      (block.opList ctx blockIn).replaceBy op [ext, newBranch]

/-- The step from the creation of the `g_zext` and of the new branch in front of `op`, and the
erasure of `op`. -/
theorem BrcondStep.of_creates {width : Nat} {type : IntegerType}
    {ctx ctx₁ ctx₂ : WfIRContext OpCode} {op ext newBranch : OperationPtr}
    (opIn : op.InBounds ctx.raw) (hType : op.getOpType! ctx.raw = .gmir .g_brcond)
    (hResults₀ : op.getNumResults! ctx.raw = 0) (hRegions₀ : op.getNumRegions! ctx.raw = 0)
    (hCondType : ((op.getOperands! ctx.raw)[0]!.getType! ctx.raw).val = .integerType type)
    (hWidth : type.bitwidth < width)
    (hCreate₁ : WfRewriter.createOp! ctx GMIR.g_zext #[IntegerType.signless width]
      #[(op.getOperands! ctx.raw)[0]!] #[] #[] (NnegProperties.mk false) (some (.before op)) =
      some (ctx₁, ext))
    (hCreate₂ : WfRewriter.createOp! ctx₁ GMIR.g_brcond #[]
      (#[ValuePtr.opResult (ext.getResult 0)] ++ (op.getOperands! ctx.raw).extract 1)
      (op.getSuccessors! ctx.raw) #[]
      (op.getProperties! ctx.raw (OpCode.gmir .g_brcond) : GMIRBrCondProperties)
      (some (.before op)) = some (ctx₂, newBranch)) :
    BrcondStep ctx (WfRewriter.eraseOp! ctx₂ op) op ext newBranch := by
  obtain ⟨h₁, h₂, h₃, h₄, hCreate₁⟩ := WfRewriter.createOp_of_createOp! hCreate₁
  have hProps₁ := WfRewriter.createOp_gmir_properties hCreate₁
  obtain ⟨extNotIn, extIn₁, hOps₁, hCtx₁, hTypes₁, hExtType, hExtResultTypes, hExtOperands,
    -⟩ := WfRewriter.createOp_frame hCreate₁
  obtain ⟨h₁', h₂', h₃', h₄', hCreate₂⟩ := WfRewriter.createOp_of_createOp! hCreate₂
  have hProps₂ := WfRewriter.createOp_gmir_properties hCreate₂
  obtain ⟨newNotIn₁, newIn₂, hOps₂, hCtx₂, hTypes₂, hNewType, hNewResultTypes, hNewOperands,
    hNewSuccessors⟩ := WfRewriter.createOp_frame hCreate₂
  have hMono₁ := fun ptr => WfRewriter.createOp_inBounds_mono (ptr := ptr) hCreate₁
  have hMono₂ := fun ptr => WfRewriter.createOp_inBounds_mono (ptr := ptr) hCreate₂
  /- `op` is still there and unchanged before its erasure. -/
  have hSame₁ := hOps₁ op opIn
  have hSame₂ := hOps₂ op hSame₁.inBounds
  have opIn₂ : op.InBounds ctx₂.raw := hSame₂.inBounds
  have hRegions : op.getNumRegions! ctx₂.raw = 0 := by
    rw [hSame₂.numRegions, hSame₁.numRegions]; exact hRegions₀
  have hUses : op.hasUses! ctx₂.raw = false := by
    have : op.getNumResults! ctx₂.raw = 0 := by
      rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, hSame₂.resultTypes,
        hSame₁.resultTypes, OperationPtr.getResultTypes!.size_eq_getNumResults!]
      exact hResults₀
    rw [Bool.eq_false_iff, ne_eq, OperationPtr.hasUses!_eq_true_iff_hasUses!_getResult]
    simp [this]
  rw [WfRewriter.eraseOp!_eq opIn₂ hRegions (by simp [hUses])]
  obtain ⟨hOps₃, hCtx₃, hTypes₃, hValues₃⟩ := WfRewriter.eraseOp_frame (ctx := ctx₂) (op := op)
    (hRegions := hRegions) (hUses := by simp [hUses]) (opIn := opIn₂)
  have hExtNe : ext ≠ op := fun hEq => extNotIn (hEq ▸ opIn)
  have hNewNe : newBranch ≠ op := fun hEq => newNotIn₁ (hEq ▸ hSame₁.inBounds)
  have newNotIn : ¬ newBranch.InBounds ctx.raw := fun hIn =>
    newNotIn₁ (by simpa using hMono₁ (.operation newBranch) (by simpa using hIn))
  have hExtSame := (hOps₂ ext extIn₁).trans_id (hOps₃ ext (hOps₂ ext extIn₁).inBounds hExtNe)
  have hNewSame := hOps₃ newBranch newIn₂ hNewNe
  /- A value of `ctx` stays, with its type: `op` has no results. -/
  have hValues : ∀ value : ValuePtr, value.InBounds ctx.raw →
      value.InBounds (WfRewriter.eraseOp ctx₂ op hRegions (by simp [hUses]) opIn₂).raw ∧
      value.getType! (WfRewriter.eraseOp ctx₂ op hRegions (by simp [hUses]) opIn₂).raw =
        value.getType! ctx.raw := by
    intro v vIn
    have vIn₁ : v.InBounds ctx₁.raw := by simpa using hMono₁ (.value v) (by simpa using vIn)
    have vIn₂ : v.InBounds ctx₂.raw := by simpa using hMono₂ (.value v) (by simpa using vIn₁)
    have vIn₃ := hValues₃ v vIn₂ (fun r hr hEq => by
      subst hr
      obtain ⟨_, hIndex⟩ := OpResultPtr.inBounds_def.mp (by simpa using vIn)
      grind)
    exact ⟨vIn₃, (hTypes₃ v vIn₃).trans ((hTypes₂ v vIn₁).trans (hTypes₁ v vIn))⟩
  refine {
    ops := fun o oIn hNe => ((hOps₁ o oIn).trans_id (hOps₂ o (hOps₁ o oIn).inBounds)).trans_id
      (hOps₃ o ((hOps₂ o (hOps₁ o oIn).inBounds)).inBounds hNe)
    ctxSame := (hCtx₁.trans hCtx₂).trans hCtx₃
    types := hValues
    widened := ?_
    extNotIn := extNotIn
    newNotIn := newNotIn
    opList := fun block blockIn => ?_ }
  · refine {
      brcond := hType
      numResults := hResults₀
      extIn := hExtSame.inBounds
      extFresh := fun v vIn hEq => ?_
      extType := by rw [hExtSame.opType, hExtType, ofDialect_gmir]
      extOperands := by rw [hExtSame.operands, hExtOperands]; simp
      extNneg := by rw [hExtSame.properties, hProps₁]
      extWidth := ⟨type, width, fun _ => hCondType, hWidth,
        by rw [hExtSame.resultTypes, hExtResultTypes]⟩
      newIn := hNewSame.inBounds
      newType := by rw [hNewSame.opType, hNewType, ofDialect_gmir]
      newResultTypes := by rw [hNewSame.resultTypes, hNewResultTypes]
      newOperands := by rw [hNewSame.operands, hNewOperands]; simp
      newSuccessors := by rw [hNewSame.successors, hNewSuccessors]
      newSegments := by rw [hNewSame.properties, hProps₂] }
    subst hEq
    exact extNotIn (OpResultPtr.inBounds_def.mp (by simpa [OperationPtr.getResult_def] using vIn)).1
  · have blockIn₁ := hCtx₁.blockIn blockIn
    have blockIn₂ := hCtx₂.blockIn blockIn₁
    rw [WfRewriter.eraseOp_opList blockIn₂,
      WfRewriter.createOp_before_opList hCreate₂ blockIn₁ blockIn₂,
      WfRewriter.createOp_before_opList hCreate₁ blockIn blockIn₁,
      show [ext, op] = [ext] ++ [op] by simp, List.replaceBy_replaceBy (by simpa using hExtNe.symm),
      show [ext] ++ [newBranch, op] = [ext, newBranch] ++ [op] by simp,
      List.erase_replaceBy BlockPtr.opList_nodup (by simp [hExtNe.symm, hNewNe.symm])]

/-- What `widenBrcondCondition` leaves behind. -/
theorem widenBrcondCondition_step {width : Nat} {ctx ctx' : WfIRContext OpCode} {op : OperationPtr}
    (opIn : op.InBounds ctx.raw) (hType : op.getOpType! ctx.raw = .gmir .g_brcond)
    (hResults₀ : op.getNumResults! ctx.raw = 0) (hRegions₀ : op.getNumRegions! ctx.raw = 0)
    (h : widenBrcondCondition width ctx op = some ctx') :
    ∃ ext newBranch, BrcondStep ctx ctx' op ext newBranch := by
  simp only [widenBrcondCondition] at h
  split at h
  · rename_i type hCondType
    split at h
    · rename_i hWidth
      split at h
      · rename_i ctx₁ ext hCreate₁
        split at h
        · rename_i ctx₂ newBranch hCreate₂
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨ext, newBranch, BrcondStep.of_creates opIn hType hResults₀ hRegions₀ hCondType
            hWidth hCreate₁ hCreate₂⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- What a step of `widenBrconds` leaves behind. -/
theorem LegalizerInfo.widenBrcond_ok {info : LegalizerInfo} {ctx ctx' : WfIRContext OpCode}
    {op : OperationPtr} (opIn : op.InBounds ctx.raw) (h : info.widenBrcond ctx op = .ok ctx') :
    ctx' = ctx ∨ ∃ ext newBranch, BrcondStep ctx ctx' op ext newBranch := by
  unfold LegalizerInfo.widenBrcond at h
  split at h
  · rename_i hType
    split at h
    · split at h
      · simp at h
      · rename_i hCounts
        simp only [not_or, Decidable.not_not] at hCounts
        split at h
        · rename_i hWiden
          simp only [Except.ok.injEq] at h
          subst h
          exact .inr (widenBrcondCondition_step opIn hType hCounts.1 hCounts.2 hWiden)
        · simp at h
    · simp only [Except.ok.injEq] at h
      exact .inl h.symm
  · simp only [Except.ok.injEq] at h
    exact .inl h.symm

/-- A widened branch whose `g_zext` and new branch stay the same stays widened. -/
theorem WidenedBrcond.mono {ctx₀ ctx ctx' : WfIRContext OpCode} {op ext newBranch : OperationPtr}
    (h : WidenedBrcond ctx₀ ctx op ext newBranch) (hExt : OpSame id ctx.raw ctx'.raw ext)
    (hNew : OpSame id ctx.raw ctx'.raw newBranch) : WidenedBrcond ctx₀ ctx' op ext newBranch where
  brcond := h.brcond
  numResults := h.numResults
  extIn := hExt.inBounds
  extFresh := h.extFresh
  extType := hExt.opType.trans h.extType
  extOperands := by rw [hExt.operands, h.extOperands]; simp
  extNneg := by rw [hExt.properties]; exact h.extNneg
  extWidth := by
    obtain ⟨type, width, h₁, h₂, h₃⟩ := h.extWidth
    exact ⟨type, width, h₁, h₂, hExt.resultTypes.trans h₃⟩
  newIn := hNew.inBounds
  newType := hNew.opType.trans h.newType
  newResultTypes := hNew.resultTypes.trans h.newResultTypes
  newOperands := by rw [hNew.operands, h.newOperands]; simp
  newSuccessors := hNew.successors.trans h.newSuccessors
  newSegments := by rw [hNew.properties]; exact h.newSegments

/-- A widened branch of a context whose branch and values are those of `ctx₀` is one of `ctx₀`. -/
theorem WidenedBrcond.transport {ctx₀ ctx ctx' : WfIRContext OpCode} {op ext newBranch : OperationPtr}
    (h : WidenedBrcond ctx ctx' op ext newBranch) (opIn₀ : op.InBounds ctx₀.raw)
    (hSame : OpSame id ctx₀.raw ctx.raw op)
    (hTypes : ∀ value : ValuePtr, value.InBounds ctx₀.raw →
      value.InBounds ctx.raw ∧ value.getType! ctx.raw = value.getType! ctx₀.raw) :
    WidenedBrcond ctx₀ ctx' op ext newBranch := by
  have hOperands : op.getOperands! ctx.raw = op.getOperands! ctx₀.raw := by
    rw [hSame.operands]; simp
  refine {
    brcond := hSame.opType.symm.trans h.brcond
    numResults := by
      rw [← OperationPtr.getResultTypes!.size_eq_getNumResults!, ← hSame.resultTypes,
        OperationPtr.getResultTypes!.size_eq_getNumResults!]
      exact h.numResults
    extIn := h.extIn
    extFresh := fun v vIn => h.extFresh v (hTypes v vIn).1
    extType := h.extType
    extOperands := by rw [h.extOperands, hOperands]
    extNneg := h.extNneg
    extWidth := ?_
    newIn := h.newIn
    newType := h.newType
    newResultTypes := h.newResultTypes
    newOperands := by rw [h.newOperands, hOperands]
    newSuccessors := by rw [h.newSuccessors, hSame.successors]
    newSegments := by rw [h.newSegments, hSame.properties] }
  obtain ⟨type, width, h₁, h₂, h₃⟩ := h.extWidth
  refine ⟨type, width, fun h0 => ?_, h₂, h₃⟩
  rw [← hOperands] at h0 ⊢
  have hCondIn : (op.getOperands! ctx.raw)[0]!.InBounds ctx₀.raw := by
    rw [hOperands, getElem!_pos _ 0 (by rw [← hOperands]; exact h0)]
    grind
  rw [← (hTypes _ hCondIn).2]
  exact h₁ h0

/-! ## Widening every branch -/

private theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih fun b hb => h b (by simp [hb])]

/-- The module after the branches among `done` that `widened` says were widened. The operations
created for a widened branch are none of the operations of `ctx₀` that are still there. -/
structure WideningInv (ctx₀ ctx : WfIRContext OpCode) (done : List OperationPtr)
    (widened : OperationPtr → Bool) (ext newBranch : OperationPtr → OperationPtr) : Prop where
  widenedDone : ∀ o, widened o = true → o ∈ done
  ops : ∀ o, o.InBounds ctx₀.raw → widened o = false → OpSame id ctx₀.raw ctx.raw o
  ctxSame : CtxSame ctx₀.raw ctx.raw
  types : ∀ value : ValuePtr, value.InBounds ctx₀.raw →
    value.InBounds ctx.raw ∧ value.getType! ctx.raw = value.getType! ctx₀.raw
  branch : ∀ o, o.InBounds ctx₀.raw → widened o = true →
    WidenedBrcond ctx₀ ctx o (ext o) (newBranch o)
  created : ∀ o, widened o = true → ∀ o', o'.InBounds ctx₀.raw → widened o' = false →
    ext o ≠ o' ∧ newBranch o ≠ o'
  opList : ∀ (block : BlockPtr) (blockIn : block.InBounds ctx₀.raw),
    block.opList ctx (ctxSame.blockIn blockIn) =
      (block.opList ctx₀ blockIn).flatMap (widenOp widened ext newBranch)

theorem WideningInv.init {ctx₀ : WfIRContext OpCode} {ext newBranch : OperationPtr → OperationPtr} :
    WideningInv ctx₀ ctx₀ [] (fun _ => false) ext newBranch where
  widenedDone := by simp
  ops := fun _ oIn _ => OpSame.refl oIn
  ctxSame := CtxSame.refl
  types := fun _ vIn => ⟨vIn, rfl⟩
  branch := by simp
  created := by simp
  opList := fun _ _ => by
    have : widenOp (fun _ => false) ext newBranch = fun o => [o] := by
      funext o; simp [widenOp]
    rw [this, List.flatMap_singleton']

theorem WideningInv.step {info : LegalizerInfo} {ctx₀ ctx ctx' : WfIRContext OpCode}
    {done : List OperationPtr} {widened : OperationPtr → Bool}
    {ext newBranch : OperationPtr → OperationPtr} {op : OperationPtr}
    (hInv : WideningInv ctx₀ ctx done widened ext newBranch)
    (opIn₀ : op.InBounds ctx₀.raw) (hNotDone : op ∉ done)
    (h : info.widenBrcond ctx op = .ok ctx') :
    ∃ widened' ext' newBranch', WideningInv ctx₀ ctx' (op :: done) widened' ext' newBranch' := by
  have hNotWidened : widened op = false := by
    cases hW : widened op
    · rfl
    · exact absurd (hInv.widenedDone op hW) hNotDone
  have hSame := hInv.ops op opIn₀ hNotWidened
  rcases LegalizerInfo.widenBrcond_ok hSame.inBounds h with rfl | ⟨e, n, hStep⟩
  · exact ⟨widened, ext, newBranch, fun o hW => List.mem_cons_of_mem _ (hInv.widenedDone o hW),
      hInv.ops, hInv.ctxSame, hInv.types, hInv.branch, hInv.created, hInv.opList⟩
  let widened' : OperationPtr → Bool := fun o => if o = op then true else widened o
  let ext' : OperationPtr → OperationPtr := fun o => if o = op then e else ext o
  let newBranch' : OperationPtr → OperationPtr := fun o => if o = op then n else newBranch o
  /- The operations created before are not `op`, which is still an operation of `ctx₀`. -/
  have hOld : ∀ o, widened o = true → ext o ≠ op ∧ newBranch o ≠ op := fun o hW =>
    hInv.created o hW op opIn₀ hNotWidened
  refine ⟨widened', ext', newBranch', ?_, ?_, hInv.ctxSame.trans hStep.ctxSame, ?_, ?_, ?_, ?_⟩
  · intro o hW
    by_cases hEq : o = op
    · simp [hEq]
    · simp only [widened', hEq, ↓reduceIte] at hW
      exact List.mem_cons_of_mem _ (hInv.widenedDone o hW)
  · intro o oIn hW
    by_cases hEq : o = op
    · simp [widened', hEq] at hW
    · simp only [widened', hEq, ↓reduceIte] at hW
      have hO := hInv.ops o oIn hW
      exact hO.trans_id (hStep.ops o hO.inBounds hEq)
  · intro v vIn
    have h₁ := hInv.types v vIn
    have h₂ := hStep.types v h₁.1
    exact ⟨h₂.1, h₂.2.trans h₁.2⟩
  · intro o oIn hW
    by_cases hEq : o = op
    · subst hEq
      simp only [ext', newBranch', ↓reduceIte]
      exact hStep.widened.transport opIn₀ hSame hInv.types
    · simp only [widened', ext', newBranch', hEq, ↓reduceIte] at hW ⊢
      have hB := hInv.branch o oIn hW
      exact hB.mono (hStep.ops _ hB.extIn (hOld o hW).1) (hStep.ops _ hB.newIn (hOld o hW).2)
  · intro o hW o' o'In hW'
    have hNe' : o' ≠ op := fun hEq => by simp [widened', hEq] at hW'
    simp only [widened', hNe', ↓reduceIte] at hW'
    by_cases hEq : o = op
    · subst hEq
      simp only [ext', newBranch', ↓reduceIte]
      have o'In := (hInv.ops o' o'In hW').inBounds
      exact ⟨fun h => hStep.extNotIn (h ▸ o'In), fun h => hStep.newNotIn (h ▸ o'In)⟩
    · simp only [widened', ext', newBranch', hEq, ↓reduceIte] at hW ⊢
      exact hInv.created o hW o' o'In hW'
  · intro block blockIn
    rw [hStep.opList block (hInv.ctxSame.blockIn blockIn), hInv.opList block blockIn]
    simp only [List.replaceBy, List.flatMap_assoc]
    refine flatMap_congr_mem fun o hMem => ?_
    have oIn : o.InBounds ctx₀.raw := by
      simp only [BlockPtr.opList] at hMem
      grind [BlockPtr.operationListWF, BlockPtr.OpChain]
    by_cases hEq : o = op
    · subst hEq
      simp [widenOp, widened', ext', newBranch', hNotWidened]
    · unfold widenOp
      by_cases hW : widened o = true
      · have := hOld o hW
        simp [widened', ext', newBranch', hEq, hW, this.1, this.2]
      · simp [widened', hEq, hW]

theorem WideningInv.foldlM {info : LegalizerInfo} {ctx₀ ctx ctx' : WfIRContext OpCode}
    {done rest : List OperationPtr} {widened : OperationPtr → Bool}
    {ext newBranch : OperationPtr → OperationPtr}
    (hInv : WideningInv ctx₀ ctx done widened ext newBranch)
    (restIn : ∀ o ∈ rest, o.InBounds ctx₀.raw) (hNodup : rest.Nodup)
    (hDisjoint : ∀ o ∈ rest, o ∉ done)
    (h : rest.foldlM info.widenBrcond ctx = .ok ctx') :
    ∃ done' widened' ext' newBranch', WideningInv ctx₀ ctx' done' widened' ext' newBranch' := by
  induction rest generalizing ctx done widened ext newBranch with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨done, widened, ext, newBranch, hInv⟩
  | cons op rest ih =>
    simp only [List.foldlM_cons, Bind.bind, Except.bind] at h
    split at h
    next => simp at h
    next ctx₁ hStep =>
      obtain ⟨widened₁, ext₁, newBranch₁, hInv₁⟩ :=
        hInv.step (restIn op (by simp)) (hDisjoint op (by simp)) hStep
      have hNodup' := List.nodup_cons.mp hNodup
      exact ih hInv₁ (fun o ho => restIn o (by simp [ho])) hNodup'.2
        (fun o ho hMem => by
          rcases List.mem_cons.mp hMem with rfl | hMem
          · exact hNodup'.1 ho
          · exact hDisjoint o (by simp [ho]) hMem) h

/-- Widening the branch conditions computes a branch widening of its input. -/
theorem LegalizerInfo.widenBrconds_widening {info : LegalizerInfo} {ctx ctx' : WfIRContext OpCode}
    (h : info.widenBrconds ctx = .ok ctx') : Nonempty (BrcondWidening ctx ctx') := by
  have hKeys : ∀ o : OperationPtr, o ∈ ctx.raw.operations.keys → o.InBounds ctx.raw := fun o ho => by
    rw [Std.HashMap.mem_keys, ← OperationPtr.inBounds_def] at ho; exact ho
  have hNodup : ctx.raw.operations.keys.Nodup := by
    have := ctx.raw.operations.distinct_keys
    simpa [List.Nodup] using this
  obtain ⟨done, widened, ext, newBranch, hInv⟩ :=
    (WideningInv.init (ext := fun _ => default) (newBranch := fun _ => default)).foldlM
      hKeys hNodup (fun _ _ h => by simp at h) h
  exact ⟨{
    widened := widened
    ext := ext
    newBranch := newBranch
    ctxSame := hInv.ctxSame
    types := hInv.types
    opSame := fun opIn hW => hInv.ops _ opIn hW
    opList := fun blockIn => hInv.opList _ blockIn
    spec := fun opIn hW => hInv.branch _ opIn hW }⟩

/-- Widening the conditions of the `g_brcond`s of a module that verifies refines it, in CTrees. -/
theorem LegalizerInfo.widenBrconds_isModuleRefinedByCTree (info : LegalizerInfo)
    {ctx ctx' : WfIRContext OpCode} {root : OperationPtr} (hVerified : ctx.Verified root)
    (h : info.widenBrconds ctx = .ok ctx') (module : OperationPtr) :
    module.isModuleRefinedByCTree ctx module ctx' := by
  obtain ⟨W⟩ := LegalizerInfo.widenBrconds_widening h
  exact W.isModuleRefinedByCTree
    (W.keptOpsSim_of_treeMonotoneOps (treeMonotoneOps_of_verified hVerified)) module

end Veir
