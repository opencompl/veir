module

public import Veir.Passes.Legalization.Validity.Phi
public import Veir.Passes.InstructionSelection.Branches.SimulationCTree
import all Veir.Interpreter.CTreeInterpreter
import all Veir.IR.Attribute
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.GMIR.OpInfo

public section

namespace Veir.Legalization.CTreeProofs

open Veir.CTree

/-- An inserted cast continues execution after setting its sole result. -/
def SetsCastResult {ctx : WfIRContext OpCode} (op : OperationPtr) (before : InterpreterState ctx)
    (value : RuntimeValue) (r : InterpreterState ctx × Option ControlFlowAction) : Prop :=
  r.2 = none ∧ r.1.memory = before.memory ∧ ∀ v, r.1.variables.getVar? v =
    if v = op.getResult 0 then some value else before.variables.getVar? v

/-- Executing an extension in a predecessor binds a widened value. Whenever that value arrives
as the destination argument, the inserted truncation binds the original value. -/
theorem returns_widenedArgumentOperations {ctx : WfIRContext OpCode}
    {ext trunc : OperationPtr} {operand : ValuePtr} {arg : BlockArgumentPtr}
    {narrow : IntegerType} {width : Nat} (wider : narrow.bitwidth < width)
    (extIn : ext.InBounds ctx.raw) (extCode : ext.getOpType! ctx.raw = .gmir .g_anyext)
    (extTypes : ext.getResultTypes! ctx.raw = #[(IntegerType.signless width : TypeAttr)])
    (extOperands : ext.getOperands! ctx.raw = #[operand])
    (truncIn : trunc.InBounds ctx.raw) (truncCode : trunc.getOpType! ctx.raw = .gmir .g_trunc)
    (truncTypes : trunc.getResultTypes! ctx.raw = #[(narrow : TypeAttr)])
    (truncProps : trunc.getProperties! ctx.raw (OpCode.gmir .g_trunc) =
      ({ nsw := false, nuw := false } : NswNuwProperties))
    (truncOperands : trunc.getOperands! ctx.raw = #[.blockArgument arg])
    (before : InterpreterState ctx) {value : Data.LLVM.Int narrow.bitwidth}
    (input : before.variables.getVar? operand = some (.int narrow.bitwidth value)) :
    Returns (interpretOperationTree ext before extIn) (fun r =>
      ∃ wide : Data.LLVM.Int width, SetsCastResult ext before (.int width wide) r ∧
        ∀ entered : InterpreterState ctx,
        entered.variables.getVar? (.blockArgument arg) = some (.int width wide) →
        Returns (interpretOperationTree trunc entered truncIn)
          (SetsCastResult trunc entered (.int narrow.bitwidth value))) := by
  let recovers := fun (v : RuntimeValue) => ∀ memory,
    Veir.CTree.interpretOp' (.gmir .g_trunc) { nsw := false, nuw := false }
      #[(narrow : TypeAttr)] #[v] #[] memory = pure (#[.int narrow.bitwidth value], memory, none)
  have extReturns := returns_interpretOperationTree_unary
    (Q := fun v => ∃ wide : Data.LLVM.Int width, v = .int width wide ∧ recovers v)
    extIn extCode extTypes extOperands input (fun successors => by
      apply (returns_widenedBlockArgument wider value before.memory).mono
      rintro r ⟨wide, rfl, recover⟩
      exact ⟨.int width wide, ⟨wide, rfl, recover⟩, by simp [IntegerType.signless], rfl⟩)
  apply extReturns.mono
  rintro r ⟨noAction, mem, _, ⟨wide, rfl, recovers'⟩, vars⟩
  refine ⟨wide, ⟨noAction, mem, vars⟩, fun entered incoming => ?_⟩
  have truncReturns := returns_interpretOperationTree_unary (Q := (· = .int narrow.bitwidth value))
    truncIn truncCode truncTypes truncOperands incoming (fun successors => by
      rw [truncProps]
      have eq := recovers' entered.memory
      change Veir.CTree.interpretOp' (.gmir .g_trunc) { nsw := false, nuw := false }
        #[(narrow : TypeAttr)] #[.int width wide] #[] entered.memory = _ at eq
      change Returns (Veir.CTree.interpretOp' (.gmir .g_trunc) { nsw := false, nuw := false }
        #[(narrow : TypeAttr)] #[.int width wide] #[] entered.memory) _
      rw [eq, returns_pure]
      exact ⟨_, rfl, by simp, rfl⟩)
  exact truncReturns.mono fun _ ⟨noAction, mem, _, rfl, vars⟩ => ⟨noAction, mem, vars⟩

end Veir.Legalization.CTreeProofs
