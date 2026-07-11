import Veir.Interpreter.EquationLemma
import Veir.Fold.Semantics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas

/-!
  # Agreement of `ValuePtr.constantValue` with interpreted SSA values

  Layer A of the folding soundness proofs (see `Veir.Fold.Semantics`): in any
  interpreter state satisfying the SSA invariant (`EquationLemmaAt`) at an
  operation, the constant operand values recovered syntactically by
  `ValuePtr.constantValue` agree (`ConstOperands.Agree`) with the runtime
  operand values held by the state. This discharges the `Agree` hypothesis of
  `OpCode.foldDecision_refines` for the states arising in a
  `LocalRewritePattern.PreservesSemantics` proof.

  The structure follows the packaged graph lemmas of
  `Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas` (whose
  `llvm.mlir.constant` lemmas are reused directly): purity of each
  constant-materializing opcode, verifier inversion for its structural counts,
  one interpretation-unfolding lemma per constant kind, and a keystone lemma
  tying a successful `constantValue` to `getVar?`.
-/

namespace Veir

/-! ## Purity of the constant-materializing opcodes -/

/-- `arith.constant` is pure: its interpretation neither reads nor writes memory. -/
theorem OperationPtr.Pure.arith_constant {op : OperationPtr} {ctx : IRContext OpCode}
    (hType : op.getOpType! ctx = .arith .constant) : op.Pure ctx := by
  unfold OperationPtr.Pure
  rw [hType]
  intro operands memory₁ memory₂
  simp only [interpretOp', Arith.interpretOp']
  repeat' split
  all_goals first
    | rfl
    | simp [Interp.map, Option.map, UBOr.map, pure, bind, Option.bind]

/-- `llvm.mlir.poison` is pure: its interpretation neither reads nor writes memory. -/
theorem OperationPtr.Pure.llvm_mlir__poison {op : OperationPtr} {ctx : IRContext OpCode}
    (hType : op.getOpType! ctx = .llvm .mlir__poison) : op.Pure ctx := by
  unfold OperationPtr.Pure
  rw [hType]
  intro operands memory₁ memory₂
  simp only [interpretOp', Llvm.interpretOp']
  repeat' split
  all_goals first
    | rfl
    | simp [Interp.map, Option.map, UBOr.map, pure, bind, Option.bind]

/-- `riscv.li` is pure: its interpretation neither reads nor writes memory. -/
theorem OperationPtr.Pure.riscv_li {op : OperationPtr} {ctx : IRContext OpCode}
    (hType : op.getOpType! ctx = .riscv .li) : op.Pure ctx := by
  unfold OperationPtr.Pure
  rw [hType]
  intro operands memory₁ memory₂
  simp only [interpretOp', Riscv.interpretOp']
  repeat' split
  all_goals first
    | rfl
    | simp [Interp.map, Option.map, UBOr.map, pure, bind, Option.bind]

/-! ## Forward unfolding of one interpretation step per constant kind

`llvm.mlir.constant` is covered by `constantOp_interpretOp_unfold` from
`CommonGraphLemmas`; the lemmas below are its analogues for the other three
constant kinds recognized by `ValuePtr.constantValue`. -/

/-- Interpreting an `arith.constant` with integer result type `intType` binds its result to
    the (never-poison) constant value of its `value` property. -/
theorem arithConstantOp_interpretOp_unfold {ctx : WfIRContext OpCode} {cstOp : OperationPtr}
    {intType : IntegerType} {hIsTy}
    {state newState : InterpreterState ctx} {cf} (inBounds : cstOp.InBounds ctx.raw)
    (hOpType : cstOp.getOpType! ctx.raw = .arith .constant)
    (hNumResults : cstOp.getNumResults! ctx.raw = 1)
    (hResType : ((cstOp.getResult 0).get! ctx.raw).type = ⟨.integerType intType, hIsTy⟩)
    (hinterp : interpretOp cstOp state inBounds = some (.ok (newState, cf))) :
    newState.variables.getVar? (cstOp.getResult 0) =
      some (RuntimeValue.int intType.bitwidth
        (.val (BitVec.ofInt intType.bitwidth
          (cstOp.getProperties! ctx.raw (.arith .constant)).value.value))) := by
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues, resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  have hResTypes0 : (cstOp.getResultTypes! ctx.raw)[0]?
      = some ⟨.integerType intType, hIsTy⟩ := by
    have hsz : (cstOp.getResultTypes! ctx.raw).size = 1 := by
      rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
    have helem := OperationPtr.getResultTypes!.getElem!_eq (op := cstOp) (ctx := ctx.raw)
      (index := 0) (by omega)
    rw [Array.getElem?_eq_getElem (by omega),
      show (cstOp.getResultTypes! ctx.raw)[0] = (cstOp.getResultTypes! ctx.raw)[0]! from by grind,
      helem, hResType]
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [interpretOp', Arith.interpretOp', hResTypes0, pure, bind, Interp] at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ :
      resValues = #[RuntimeValue.int intType.bitwidth
        (.val (BitVec.ofInt intType.bitwidth
          (cstOp.getProperties! ctx.raw (.arith .constant)).value.value))] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

/-- Interpreting an `llvm.mlir.poison` with integer result type `intType` binds its result
    to poison. -/
theorem poisonOp_interpretOp_unfold {ctx : WfIRContext OpCode} {cstOp : OperationPtr}
    {intType : IntegerType} {hIsTy}
    {state newState : InterpreterState ctx} {cf} (inBounds : cstOp.InBounds ctx.raw)
    (hOpType : cstOp.getOpType! ctx.raw = .llvm .mlir__poison)
    (hNumResults : cstOp.getNumResults! ctx.raw = 1)
    (hResType : ((cstOp.getResult 0).get! ctx.raw).type = ⟨.integerType intType, hIsTy⟩)
    (hinterp : interpretOp cstOp state inBounds = some (.ok (newState, cf))) :
    newState.variables.getVar? (cstOp.getResult 0) =
      some (RuntimeValue.int intType.bitwidth
        (Data.LLVM.Int.mlir_poison intType.bitwidth)) := by
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues, resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  have hResTypes0 : (cstOp.getResultTypes! ctx.raw)[0]?
      = some ⟨.integerType intType, hIsTy⟩ := by
    have hsz : (cstOp.getResultTypes! ctx.raw).size = 1 := by
      rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hNumResults]
    have helem := OperationPtr.getResultTypes!.getElem!_eq (op := cstOp) (ctx := ctx.raw)
      (index := 0) (by omega)
    rw [Array.getElem?_eq_getElem (by omega),
      show (cstOp.getResultTypes! ctx.raw)[0] = (cstOp.getResultTypes! ctx.raw)[0]! from by grind,
      helem, hResType]
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [interpretOp', Llvm.interpretOp', hResTypes0, pure, Interp] at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ :
      resValues = #[RuntimeValue.int intType.bitwidth
        (Data.LLVM.Int.mlir_poison intType.bitwidth)] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

/-- Interpreting a `riscv.li` binds its result to the register holding its immediate. -/
theorem liOp_interpretOp_unfold {ctx : WfIRContext OpCode} {cstOp : OperationPtr}
    {state newState : InterpreterState ctx} {cf} (inBounds : cstOp.InBounds ctx.raw)
    (hOpType : cstOp.getOpType! ctx.raw = .riscv .li)
    (hNumResults : cstOp.getNumResults! ctx.raw = 1)
    (hinterp : interpretOp cstOp state inBounds = some (.ok (newState, cf))) :
    newState.variables.getVar? (cstOp.getResult 0) =
      some (RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64
        (cstOp.getProperties! ctx.raw (.riscv .li)).value.value))) := by
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues, resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [interpretOp', Riscv.interpretOp', pure, Interp] at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ :
      resValues = #[RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64
        (cstOp.getProperties! ctx.raw (.riscv .li)).value.value))] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

/-! ## The keystone: `constantValue` agrees with `getVar?` -/

/-- A value defined (through `getDefiningOp!`) by a single-result operation is that
    operation's result 0. -/
theorem ValuePtr.eq_getResult_zero_of_getDefiningOp! {ctx : WfIRContext OpCode}
    {v : ValuePtr} {defOp : OperationPtr}
    (hvIn : v.InBounds ctx.raw)
    (hDef : v.getDefiningOp! ctx.raw = some defOp)
    (hNumResults : defOp.getNumResults! ctx.raw = 1) :
    v = .opResult (defOp.getResult 0) := by
  cases v with
  | blockArgument ba => simp [ValuePtr.getDefiningOp!] at hDef
  | opResult ptr =>
    simp only [ValuePtr.getDefiningOp!, Option.some.injEq] at hDef
    have hPtrIn : ptr.InBounds ctx.raw := by grind
    have hOpIn : ptr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
    have hIdx : ptr.index < ptr.op.getNumResults! ctx.raw := by
      grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
    have hPtrEq : ptr = ptr.op.getResult ptr.index := by
      cases ptr; rfl
    have hOwner := (ctx.wellFormed.operations ptr.op hOpIn).result_owner ptr.index hIdx
    rw [← hPtrEq] at hOwner
    have hOpEq : defOp = ptr.op := by rw [← hDef, hOwner]
    subst hOpEq
    have hidx0 : ptr.index = 0 := by omega
    cases ptr
    grind [OperationPtr.getResult]

set_option maxHeartbeats 1000000 in
/-- Semantic content of a successful `v.constantValue = some rv` at a program point dominated
    by `v` (an operand of `op`): in any source state satisfying `EquationLemmaAt` before `op`,
    the runtime value of `v` is exactly `rv`. This is the `ValuePtr.constantValue` analogue of
    `matchConstantIntVal_getVar?_of_EquationLemmaAt`. -/
theorem ValuePtr.constantValue_getVar?_of_EquationLemmaAt {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {v : ValuePtr} {rv : RuntimeValue}
    (hConst : v.constantValue ctx.raw = some rv)
    (hOperand : v ∈ op.getOperands! ctx.raw) :
    state.variables.getVar? v = some rv := by
  have hvIn : v.InBounds ctx.raw := by grind
  -- Unfold `constantValue`: `v` is defined by one of the four constant kinds.
  simp only [ValuePtr.constantValue, Option.bind_eq_bind, Option.bind_eq_some_iff] at hConst
  obtain ⟨defOp, hDef, hConst⟩ := hConst
  -- The defining op strictly dominates `op`, so `EquationLemmaAt` applies to it.
  have hSDom : defOp.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hDef hOperand
  have hDomIp : defOp.dominatesIp (InsertPoint.before op) ctx := by grind
  split at hConst
  case h_1 hType =>
    -- arith.constant
    split at hConst
    case h_1 intType hVType =>
      simp only [pure, Option.some.injEq] at hConst
      subst rv
      have hDefIn : defOp.InBounds ctx.raw := by grind
      have hVerified : defOp.Verified ctx hDefIn := by grind
      obtain ⟨hNumResults, -, -, -, -⟩ :=
        OperationPtr.Verified.arith_constant hVerified hType
      have hvEq := ValuePtr.eq_getResult_zero_of_getDefiningOp! hvIn hDef hNumResults
      have hResType : ((defOp.getResult 0).get! ctx.raw).type
          = ⟨.integerType intType, by grind⟩ := by
        apply Subtype.ext
        rw [show ((defOp.getResult 0).get! ctx.raw).type
            = (v.getType! ctx.raw) from by rw [hvEq]; rfl]
        exact hVType
      have hPure : defOp.Pure ctx.raw := OperationPtr.Pure.arith_constant hType
      obtain ⟨cf, hInterpC⟩ := stateWf defOp hDefIn hPure hDomIp
      have hVal := arithConstantOp_interpretOp_unfold hDefIn hType hNumResults hResType hInterpC
      rw [hvEq]
      exact hVal
    case h_2 => simp at hConst
  case h_2 hType =>
    -- llvm.mlir.constant
    split at hConst
    case h_1 intType hVType =>
      split at hConst
      case h_1 intAttr hProps =>
        simp only [pure, Option.some.injEq] at hConst
        subst rv
        have hDefIn : defOp.InBounds ctx.raw := by grind
        have hVerified : defOp.Verified ctx hDefIn := by grind
        obtain ⟨hNumResults, -, -, -⟩ :=
          OperationPtr.Verified.llvm_mlir__constant hVerified hType
        have hvEq := ValuePtr.eq_getResult_zero_of_getDefiningOp! hvIn hDef hNumResults
        have hResType : ((defOp.getResult 0).get! ctx.raw).type
            = ⟨.integerType intType, by grind⟩ := by
          apply Subtype.ext
          rw [show ((defOp.getResult 0).get! ctx.raw).type
              = (v.getType! ctx.raw) from by rw [hvEq]; rfl]
          exact hVType
        have hPure : defOp.Pure ctx.raw := OperationPtr.Pure.llvm_mlir__constant hType
        obtain ⟨cf, hInterpC⟩ := stateWf defOp hDefIn hPure hDomIp
        have hVal := constantOp_interpretOp_unfold hDefIn hType hNumResults hProps hResType
          hInterpC
        rw [hvEq]
        exact hVal
      case h_2 => simp at hConst
    case h_2 => simp at hConst
  case h_3 hType =>
    -- llvm.mlir.poison
    split at hConst
    case h_1 intType hVType =>
      simp only [pure, Option.some.injEq] at hConst
      subst rv
      have hDefIn : defOp.InBounds ctx.raw := by grind
      have hVerified : defOp.Verified ctx hDefIn := by grind
      obtain ⟨hNumResults, -, -, -⟩ :=
        OperationPtr.Verified.llvm_mlir__poison hVerified hType
      have hvEq := ValuePtr.eq_getResult_zero_of_getDefiningOp! hvIn hDef hNumResults
      have hResType : ((defOp.getResult 0).get! ctx.raw).type
          = ⟨.integerType intType, by grind⟩ := by
        apply Subtype.ext
        rw [show ((defOp.getResult 0).get! ctx.raw).type
            = (v.getType! ctx.raw) from by rw [hvEq]; rfl]
        exact hVType
      have hPure : defOp.Pure ctx.raw := OperationPtr.Pure.llvm_mlir__poison hType
      obtain ⟨cf, hInterpC⟩ := stateWf defOp hDefIn hPure hDomIp
      have hVal := poisonOp_interpretOp_unfold hDefIn hType hNumResults hResType hInterpC
      rw [hvEq]
      exact hVal
    case h_2 => simp at hConst
  case h_4 hType =>
    -- riscv.li
    split at hConst
    case h_1 regType hVType =>
      simp only [pure, Option.some.injEq] at hConst
      subst rv
      have hDefIn : defOp.InBounds ctx.raw := by grind
      have hVerified : defOp.Verified ctx hDefIn := by grind
      obtain ⟨hNumResults, -, -, -⟩ :=
        OperationPtr.Verified.riscv_li hVerified hType
      have hvEq := ValuePtr.eq_getResult_zero_of_getDefiningOp! hvIn hDef hNumResults
      have hPure : defOp.Pure ctx.raw := OperationPtr.Pure.riscv_li hType
      obtain ⟨cf, hInterpC⟩ := stateWf defOp hDefIn hPure hDomIp
      have hVal := liOp_interpretOp_unfold hDefIn hType hNumResults hInterpC
      rw [hvEq]
      exact hVal
    case h_2 => simp at hConst
  case h_5 hType =>
    -- mod_arith.constant: the dialect is uninterpreted, so no state satisfying
    -- the SSA invariant can exist at a point dominated by it — the hypotheses
    -- are contradictory.
    exfalso
    have hDefIn : defOp.InBounds ctx.raw := by grind
    have hPure : defOp.Pure ctx.raw := by
      unfold OperationPtr.Pure
      rw [hType]
      intro operands memory₁ memory₂
      rfl
    obtain ⟨cf, hInterpC⟩ := stateWf defOp hDefIn hPure hDomIp
    rw [interpretOp_some_iff] at hInterpC
    obtain ⟨operandValues, resValues, mem', varState', -, hInterp', -, -⟩ := hInterpC
    simp only [OperationPtr.interpret] at hInterp'
    rw [hType] at hInterp'
    simp only [interpretOp'] at hInterp'
    exact nomatch hInterp'
  case h_6 => simp at hConst

/-! ## The packaged agreement theorem -/

/--
  Layer A: in any interpreter state satisfying the SSA invariant before `op`, the constant
  operand values recovered syntactically by `ValuePtr.constantValue` (as consumed by
  `foldDecision`) agree with the runtime operand values. Together with
  `OpCode.foldDecision_refines` this makes every fold decision computed on the real IR sound
  for the real operand values.
-/
theorem foldConstOperands_agree {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {actualOperands : Array RuntimeValue}
    (hOperands : state.variables.getOperandValues op = some actualOperands) :
    ConstOperands.Agree
      ((op.getOperands! ctx.raw).map (ValuePtr.constantValue · ctx.raw))
      actualOperands := by
  obtain ⟨hSize, hAt⟩ := VariableState.getOperandValues_eq_some_iff.mp hOperands
  have hOpsSize : (op.getOperands! ctx.raw).size = op.getNumOperands! ctx.raw :=
    OperationPtr.getOperands!.size_eq_getNumOperands!
  constructor
  · simp [hOpsSize, hSize]
  · intro i value hKnown
    obtain ⟨hi, hKnown⟩ := Array.getElem?_eq_some_iff.mp hKnown
    rw [Array.size_map] at hi
    simp only [Array.getElem_map] at hKnown
    have hMem : (op.getOperands! ctx.raw)[i] ∈ op.getOperands! ctx.raw :=
      Array.getElem_mem hi
    have hVar := ValuePtr.constantValue_getVar?_of_EquationLemmaAt ctxDom ctxVerif
      opInBounds stateWf hKnown hMem
    have hOperandEq : op.getOperand! ctx.raw i = (op.getOperands! ctx.raw)[i] := by
      grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
    have hActual := hAt i (by omega)
    rw [hOperandEq, hVar] at hActual
    have hlt : i < actualOperands.size := by omega
    rw [Array.getElem?_eq_getElem hlt]
    grind

end Veir
