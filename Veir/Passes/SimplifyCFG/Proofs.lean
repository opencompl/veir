module

public import Veir.Passes.SimplifyCFG
public import Veir.Interpreter.CFG
public import Veir.Interfaces.FunctionInterfaces

import all Veir.Passes.SimplifyCFG
import Veir.Interpreter.Lemmas
import all Veir.Interpreter.Basic
import all Veir.Interpreter.Util

namespace Veir.SimplifyCFG

/-- The interpreted direct branches only carry their operands to the successor. -/
private theorem interpret_directBranch
    {ctx : WfIRContext OpCode} {op : OperationPtr} {opIn : op.InBounds ctx.raw}
    {state : InterpreterState ctx} {values : Array RuntimeValue} {target : BlockPtr}
    (hcode : op.getOpType! ctx.raw = .cf .br ∨ op.getOpType! ctx.raw = .llvm .br ∨
      op.getOpType! ctx.raw = .riscv_cf .branch)
    (hread : state.variables.getOperandValues op = some values)
    (hsuccessors : op.getSuccessors! ctx.raw = #[target])
    (hresults : op.getNumResults! ctx.raw = 0) :
    interpretOp op state opIn = .ok (state, some (.branch values target)) := by
  apply (interpretOp_ok_iff_of_getOperandValues_eq_some hread).mpr
  refine ⟨#[], ?_, ?_⟩
  · unfold OperationPtr.interpret
    rcases hcode with hcode | hcode | hcode
    all_goals
      rw [hcode]
      simp [interpretOp', Cf.interpretOp', Llvm.interpretOp', Riscv_Cf.interpretOp',
        hsuccessors, pure, bind]
  · simp [VariableState.setResultValues?, hresults, VariableState.setResultValues?_loop]

/-- Substituting an incoming operand reads the same runtime value as entering
    the forwarding block and reading its bound argument. -/
private theorem substituteArgument_getVar
    {ctx : WfIRContext OpCode} {before after : VariableState ctx}
    {block : BlockPtr} {blockIn : block.InBounds ctx.raw}
    {arguments : Array ValuePtr} {values : Array RuntimeValue}
    (hsize : arguments.size = block.getNumArguments! ctx.raw)
    (hread : arguments.mapM before.getVar? = some values)
    (hbind : before.setArgumentValues? block values blockIn = some after)
    {value : ValuePtr} (valueIn : value.InBounds ctx.raw) :
    before.getVar? (substituteArgument block arguments value) = after.getVar? value := by
  rw [VariableState.getVar?_setArgumentValues? hbind]
  cases value with
  | opResult result => rfl
  | blockArgument argument =>
      rcases argument with ⟨owner, index⟩
      by_cases howner : owner = block
      · subst owner
        have hindex : index < block.getNumArguments! ctx.raw := by
          grind [ValuePtr.InBounds, BlockArgumentPtr.inBounds_def]
        have hvaluesSize := Array.size_eq_of_mapM_eq_some hread
        have hvalue := Array.mapM_option_eq_some_implies hread index (by omega)
        simpa [substituteArgument, hindex,
          getElem!_pos arguments index (by omega), getElem!_pos values index (by omega)] using hvalue
      · simp only [substituteArgument, howner, false_and, if_false]

/-- The full forwarded operand segment has the same runtime values after
    substitution, including permutations, duplication, and captured operands. -/
private theorem substituteArguments_getValues
    {ctx : WfIRContext OpCode} {before after : VariableState ctx}
    {block : BlockPtr} {blockIn : block.InBounds ctx.raw}
    {arguments outgoing : Array ValuePtr} {values forwarded : Array RuntimeValue}
    (hsize : arguments.size = block.getNumArguments! ctx.raw)
    (hread : arguments.mapM before.getVar? = some values)
    (hbind : before.setArgumentValues? block values blockIn = some after)
    (outgoingIn : ∀ value ∈ outgoing, value.InBounds ctx.raw)
    (hforwarded : outgoing.mapM after.getVar? = some forwarded) :
    (outgoing.map (substituteArgument block arguments)).mapM before.getVar? = some forwarded := by
  rw [Array.mapM_map]
  have hforwardedSize := Array.size_eq_of_mapM_eq_some hforwarded
  apply (Array.mapM_eq_some_iff_of_size_eq hforwardedSize).mpr
  intro i hi
  have hvalue := Array.mapM_option_eq_some_implies hforwarded i (by omega)
  have hin : outgoing[i]!.InBounds ctx.raw := by
    rw [getElem!_pos outgoing i hi]
    exact outgoingIn _ (Array.getElem_mem hi)
  change before.getVar? (substituteArgument block arguments outgoing[i]!) = _
  rw [substituteArgument_getVar hsize hread hbind hin]
  simpa only [getElem!_pos outgoing i hi, getElem!_pos forwarded i (by omega)] using hvalue

/-- Executing a forwarding block binds its arguments and takes its direct branch,
    leaving memory unchanged. -/
private theorem interpret_forwardingBlock
    {ctx : WfIRContext OpCode} {block target : BlockPtr} {op : OperationPtr}
    {blockIn : block.InBounds ctx.raw} {opIn : op.InBounds ctx.raw}
    {state : InterpreterState ctx} {bound : VariableState ctx}
    {arguments forwarded : Array RuntimeValue}
    (hfirst : (block.get! ctx.raw).firstOp = some op)
    (hcode : op.getOpType! ctx.raw = .cf .br ∨ op.getOpType! ctx.raw = .llvm .br ∨
      op.getOpType! ctx.raw = .riscv_cf .branch)
    (hbind : state.variables.setArgumentValues? block arguments blockIn = some bound)
    (hread : bound.getOperandValues op = some forwarded)
    (hsuccessors : op.getSuccessors! ctx.raw = #[target])
    (hresults : op.getNumResults! ctx.raw = 0) :
    interpretBlock block arguments state blockIn =
      .ok (⟨bound, state.memory⟩, .branch forwarded target) := by
  have hfirst' : (block.get ctx.raw blockIn).firstOp = some op := by grind
  have hop := interpret_directBranch (opIn := opIn)
    (state := ⟨bound, state.memory⟩) hcode hread hsuccessors hresults
  simp only [interpretBlock, hbind, hfirst', Interp.liftOption_some, Interp.bind_ok]
  rw [interpretOpChain]
  simp only [hop, Interp.bind_ok, Interp.pure_eq]

/-- The contexts visited by a successful traversal, recording its local rewrites. -/
private inductive RunSteps : WfIRContext OpCode → WfIRContext OpCode → Prop where
  | refl (ctx) : RunSteps ctx ctx
  | step {ctx ctx' final} (op : OperationPtr)
      (rewrite : simplifyBranch ctx op = .ok ctx')
      (tail : RunSteps ctx' final) : RunSteps ctx final

/-- Success of the driver is witnessed by a finite sequence of local rewrites. -/
private theorem run_steps {ctx newCtx : WfIRContext OpCode} {root : OperationPtr}
    (hRun : run ctx root = .ok newCtx) : RunSteps ctx newCtx := by
  have hwork : runWorklist ctx [.operation root] = some (.ok newCtx) := by
    simp only [run] at hRun
    cases h : runWorklist ctx [.operation root] with
    | none => simp only [h, Option.getD_none] at hRun; contradiction
    | some result => simpa only [h, Option.getD_some, Option.some.injEq] using hRun
  apply runWorklist.partial_correctness
    (fun ctx _ result => ∀ final, result = .ok final → RunSteps ctx final)
    ?_ ctx [.operation root] (.ok newCtx) hwork newCtx rfl
  intro recurse ih ctx pending result hresult final hfinal
  subst result
  cases pending with
  | nil =>
      simp only [Option.some.injEq, Except.ok.injEq] at hresult
      subst final
      exact .refl ctx
  | cons task rest =>
      cases task with
      | operation op => exact ih _ _ _ hresult final rfl
      | region region => exact ih _ _ _ hresult final rfl
      | blocks block => exact ih _ _ _ hresult final rfl
      | operations op => exact ih _ _ _ hresult final rfl
      | rewrite op =>
          cases hrewrite : simplifyBranch ctx op with
          | error err => simp [hrewrite] at hresult
          | ok ctx' =>
              simp only [hrewrite] at hresult
              exact .step op hrewrite (ih _ _ _ hresult final rfl)

/--
A successful `simplifycfg` run on verified IR satisfying SSA dominance preserves
the semantics of every function under the pass root, including the root itself
when it is a function. Function pointers survive the transformation.

For the same arguments and initial memory, every defined source execution is
matched by a target execution with equal final memory and pointwise-refined
return values. As in `Interp.isRefinedBy`, source UB and interpreter failure
(including unsupported operations) impose no obligation on the target.

This states correctness of the pure implementation used by `SimplifyCFGPass`.
It uses the function interface so that LLVM functions are covered as well as
`func.func`. The proof is intentionally left for future work.
-/
public theorem preservesSemantics
    {ctx newCtx : WfIRContext OpCode} {root : OperationPtr}
    (rootIn : root.InBounds ctx.raw)
    (ctxDom : ctx.Dom) (ctxVerified : ctx.Verified root)
    (hRun : run ctx root = .ok newCtx) :
    ∀ (func : OperationPtr) (funcIn : func.InBounds ctx.raw),
      func.isFunctionLike ctx.raw →
      (IRNode.operation root).Ancestor (.operation func) ctx →
      ∃ funcIn' : func.InBounds newCtx.raw,
        ∀ (args : Array RuntimeValue) (mem : MemoryState),
          Interp.isRefinedBy FunctionResult.isRefinedBy
            (interpretFunction func args mem (ctx := ctx) funcIn)
            (interpretFunction func args mem (ctx := newCtx) funcIn') := by
  sorry

end Veir.SimplifyCFG
