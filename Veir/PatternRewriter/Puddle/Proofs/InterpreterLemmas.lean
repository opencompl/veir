module

public import Veir.PatternRewriter.Puddle.Proofs.MatchInvariants
public import Veir.Interpreter.Evaluate
public import Veir.PatternRewriter.Semantics

import Veir.Data.Refinement
import all Veir.Dialects.Arith.OpInfo
import all Veir.GlobalOpInfo
import Veir.Interpreter.Lemmas
import Veir.Interpreter.Refinement.Lemmas
import all Veir.Interpreter.Basic
import all Veir.Interpreter.EquationLemma
import all Veir.Interpreter.Refinement.Basic
import all Veir.IR.Basic
import all Veir.PatternRewriter.Semantics
import all Veir.Verifier.Lemmas

/-! Interpreter facts used to connect concrete Puddle matches to their denotational semantics. -/

namespace Veir.Puddle

public section

variable {OpInfo : Type} [HasOpInfo OpInfo]

@[simp]
theorem OpCode.arith_getEffects_eq_none
    (opCode : Arith) (actual : propertiesOf (OpCode.arith opCode)) :
    HasOpInfo.getEffects (OpCode.arith opCode) actual = .none := by
  change OpCode.getEffects (OpCode.arith opCode) actual = .none
  simp [OpCode.getEffects, Arith.getEffects]

@[simp]
theorem OpCode.arith_isTerminator_eq_false (opCode : Arith) :
    HasOpInfo.isTerminator (OpCode.arith opCode) = false := by
  rfl

@[simp]
theorem interpretOp'_arith_constant
    {width : Nat} (properties : ArithConstantProperties)
    (successors : Array BlockPtr) (memory : MemoryState) :
    interpretOp' (.arith .constant) properties
      #[(IntegerType.mk width : TypeAttr)] #[] successors memory =
      .ok (#[.int width (.val (BitVec.ofInt width properties.value.value))],
        memory, none) := by
  simp [interpretOp', Arith.interpretOp', bind, pure, Interp]

@[simp]
theorem interpretOp'_arith_addi
    {width : Nat} (properties : ArithIntegerOverflowFlagsProperties)
    (resultTypes : Array TypeAttr) (lhs rhs : Data.LLVM.Int width)
    (successors : Array BlockPtr) (memory : MemoryState) :
    interpretOp' (.arith .addi) properties resultTypes
      #[.int width lhs, .int width rhs] successors memory =
      .ok (#[.int width
        (Data.LLVM.Int.add lhs rhs properties.attr.nsw properties.attr.nuw)], memory, none) := by
  simp [interpretOp', Arith.interpretOp', bind, pure, Interp]

@[simp]
theorem interpretOp'_arith_subi
    {width : Nat} (properties : ArithIntegerOverflowFlagsProperties)
    (resultTypes : Array TypeAttr) (lhs rhs : Data.LLVM.Int width)
    (successors : Array BlockPtr) (memory : MemoryState) :
    interpretOp' (.arith .subi) properties resultTypes
      #[.int width lhs, .int width rhs] successors memory =
      .ok (#[.int width
        (Data.LLVM.Int.sub lhs rhs properties.attr.nsw properties.attr.nuw)], memory, none) := by
  simp [interpretOp', Arith.interpretOp', bind, pure, Interp]

@[simp]
theorem interpretOp'_arith_muli
    {width : Nat} (properties : ArithIntegerOverflowFlagsProperties)
    (resultTypes : Array TypeAttr) (lhs rhs : Data.LLVM.Int width)
    (successors : Array BlockPtr) (memory : MemoryState) :
    interpretOp' (.arith .muli) properties resultTypes
      #[.int width lhs, .int width rhs] successors memory =
      .ok (#[.int width
        (Data.LLVM.Int.mul lhs rhs properties.attr.nsw properties.attr.nuw)], memory, none) := by
  simp [interpretOp', Arith.interpretOp', bind, pure, Interp]

/-- Read an unchanged runtime value from the refined target state of a local rewrite. -/
theorem LocalRewritePattern.exists_refined_getVar?
    {ctx : WfIRContext OpCode}
    {ipIn : ip.InBounds ctx.raw}
    {pattern : LocalRewritePattern OpCode}
    {hpattern : pattern ctx op = some (newCtx, some (newOps, newValues))}
    {hreturn : pattern.ReturnValuesInBounds} {hreturn₂ : pattern.ReturnValues}
    {hreturn₃ : pattern.ReturnCtxChanges}
    {state : InterpreterState ctx} {state' : InterpreterState newCtx}
    {ipIn' : ip.InBounds newCtx.raw}
    (valueRefinement : state.variables.isRefinedByAt state'.variables
      (LocalRewritePattern.mapping hpattern hreturn hreturn₂ hreturn₃) (.at ip) (.at ip))
    (state'Dom : state'.DefinesDominating ip)
    (vIn : v.InBounds ctx.raw)
    (hxVal : state.variables.getVar? v = some runtimeValue)
    (hDomCtx : v.dominatesIp ip ctx) (hDom' : v.dominatesIp ip newCtx)
    (hNotRes : v ∉ op.getResults! ctx.raw) :
    ∃ targetRuntime, state'.variables.getVar? v = some targetRuntime ∧
      runtimeValue ⊒ targetRuntime := by
  have ⟨tv, hTv⟩ := InterpreterState.DefinesDominating.exists_getVar_of_dominatesIp state'Dom
      (hreturn₃.valuePtr_inBounds hpattern vIn) hDom'
  have hRef : runtimeValue ⊒ tv := by
    grind [LocalRewritePattern.mapping, valueRefinement v]
  exact ⟨tv, hTv, hRef⟩

theorem InterpreterState.exists_getVar_of_operand
    {ctx : WfIRContext OpCode} {operation : OperationPtr}
    {state after : InterpreterState ctx} {cf}
    (operationIn : operation.InBounds ctx.raw)
    {value : ValuePtr}
    (hvalue : value ∈ operation.getOperands! ctx.raw)
    (hinterp : interpretOp operation state operationIn = .ok (after, cf)) :
    ∃ runtimeValue, state.variables.getVar? value = some runtimeValue := by
  obtain ⟨operandValues, _, _, _, hvalues, _, _, _⟩ := interpretOp_some_iff.mp hinterp
  obtain ⟨_, hget⟩ := VariableState.getOperandValues_eq_some_iff.mp hvalues
  obtain ⟨index, hindex, hoperand⟩ :=
    OperationPtr.getOperands!.mem_iff_exists_index.mp hvalue
  exact ⟨operandValues[index]!, by simpa [hoperand] using hget index hindex⟩

theorem Assignment.Rooted.exists_getValue
    {assignment : Assignment OpCode} {ctx : WfIRContext OpCode}
    {root : OperationPtr} (hrooted : Assignment.Rooted assignment ctx root)
    (rootIn : root.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before root) (by grind))
    {rootState : InterpreterState ctx} {rootCf}
    (rootInterp : interpretOp root state = .ok (rootState, rootCf))
    {handle : Handle OpCode .value} {value : ValuePtr}
    (hget : Assignment.getValue assignment handle = some value) :
    ∃ runtimeValue, state.variables.getVar? value = some runtimeValue := by
  obtain ⟨consumer, consumerIn, hconsumer, hpure, hoperand⟩ :=
    hrooted.2 handle value hget
  rcases hconsumer with rfl | hdominates
  · exact InterpreterState.exists_getVar_of_operand rootIn hoperand rootInterp
  · have hdomIp : consumer.dominatesIp (InsertPoint.before root) ctx := by grind
    obtain ⟨consumerCf, consumerInterp⟩ := stateWf consumer consumerIn hpure hdomIp
    exact InterpreterState.exists_getVar_of_operand consumerIn hoperand consumerInterp


theorem pureOperation_interpret_memory_cf
    {ctx : WfIRContext OpCode} {operation : OperationPtr}
    {state after : InterpreterState ctx} {cf}
    (operationIn : operation.InBounds ctx.raw)
    (hpure : operation.Pure ctx.raw)
    (hterminator : HasOpInfo.isTerminator (operation.getOpType! ctx.raw) = false)
    (hinterp : interpretOp operation state operationIn = .ok (after, cf)) :
    state.memory = after.memory ∧ cf = none := by
  obtain ⟨operandValues, resultValues, memory, variables, hvalues, hinterpret, hset, hafter⟩ :=
    interpretOp_some_iff.mp hinterp
  simp only [OperationPtr.interpret] at hinterpret
  constructor
  · have hmemory := OperationPtr.Pure.interpretOp'_eq_ok_implies_memory_eq hpure hinterpret
    subst after
    simpa using hmemory
  · exact controlFlow_eq_none_of_isTerminator_eq_false hterminator hinterpret


end

end Veir.Puddle
