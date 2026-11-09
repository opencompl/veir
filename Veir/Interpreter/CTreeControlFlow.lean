module

public import Veir.Interpreter.CTreeMemoryPreservation
public import Veir.Interpreter.CTreeResultConformance
import all Veir.Interpreter.CTreeMemoryPreservation
import all Veir.Interpreter.Basic
import all Veir.Interpreter.Interp
import all Veir.GlobalOpInfo
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.GMIR_RISCV.OpInfo
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV_Cf.OpInfo
import all Veir.Dialects.RISCV_Stack.OpInfo
import all Veir.Dialects.RV64.OpInfo
import all Veir.Dialects.Cf.OpInfo
import all Veir.Dialects.Arith.OpInfo
import all Veir.Dialects.ModArith.OpInfo
import all Veir.Dialects.LLZK.Felt.OpInfo
import all Veir.Dialects.Comb.OpInfo
import all Veir.Dialects.HW.OpInfo
import all Veir.Dialects.Func.OpInfo
import all Veir.Dialects.Cir.OpInfo
import all Veir.Dialects.GMIR.OpInfo

public section

namespace Veir

set_option maxHeartbeats 2000000 in
/-- GEP never transfers control. -/
theorem Llvm.interpretOp'_gep_no_action
    (properties : propertiesOf Llvm.getelementptr) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (layout : DataLayout)
    (h : Llvm.interpretOp' .getelementptr properties types operands successors before layout =
      .ok (results, after, action)) : action = none := by
  simp only [Llvm.interpretOp'] at h
  repeat first
    | cases h; rfl
    | contradiction
    | split at h
    | simp only [Bind.bind, Pure.pure, liftM, monadLift, MonadLift.monadLift] at h
  all_goals try grind

set_option maxHeartbeats 4000000 in
/-- A successful deterministic nonterminator leaves control at the following operation. -/
theorem interpretOp'_no_action_of_nonterm
    (code : OpCode) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (nonterm : code.isTerminator = false)
    (h : Veir.interpretOp' code properties types operands successors before = .ok (results, after, action)) :
    action = none := by
  cases code with
  | llvm code =>
    by_cases gep : code = .getelementptr
    · subst code
      exact Llvm.interpretOp'_gep_no_action properties types operands successors before after results action .riscv64 h
    · cases code <;> simp_all only [OpCode.isTerminator, Llvm.isTerminator]
      all_goals simp only [Veir.interpretOp', Llvm.interpretOp'] at h
      all_goals
        repeat first
          | cases h; rfl
          | contradiction
          | split at h
          | simp only [Bind.bind, Pure.pure, liftM, monadLift, MonadLift.monadLift] at h
  | _ =>
    first
    | solve | simp [Veir.interpretOp', liftM, monadLift, MonadLift.monadLift] at h
    | rename_i code
      cases code <;> simp_all only [OpCode.isTerminator, Func.isTerminator, Cir.isTerminator,
        Riscv_Cf.isTerminator, Cf.isTerminator, GMIR.isTerminator]
      all_goals simp only [Veir.interpretOp', Arith.interpretOp', Riscv.interpretOp',
        Riscv_Cf.interpretOp', Riscv_Stack.interpretOp', Rv64.interpretOp', Cf.interpretOp',
        ModArith.interpretOp', HW.interpretOp', Comb.interpretOp', GMIR.interpretOp',
        GMIR_RISCV.interpretOp', Felt.interpretOp'] at h
      all_goals
        repeat first
          | cases h; rfl
          | contradiction
          | split at h
          | simp only [Bind.bind, Pure.pure, liftM, monadLift, MonadLift.monadLift] at h
      all_goals
        try simp_all only [Bind.bind, Pure.pure, liftM, monadLift, MonadLift.monadLift, Option.bind]
        repeat first
          | solve | simp_all
          | split at *
      all_goals grind

/-- Every successful CTree return of a nonterminator continues to the next operation. -/
theorem CTree.interpretOp'_no_action_of_nonterm
    (code : OpCode) (properties : propertiesOf code) (types : Array TypeAttr)
    (operands : Array RuntimeValue) (successors : Array BlockPtr)
    (before after : MemoryState) (results : Array RuntimeValue) (action : Option ControlFlowAction)
    (regions : Array RegionPtr) (nonterm : code.isTerminator = false)
    (outcome : PureOrErr.CanInterpretTo
      (CTree.interpretOp' code properties types operands successors before regions)
      (.ok (results, after, action))) : action = none := by
  obtain ⟨deterministic, legacy, _⟩ :=
    CTree.interpretOp'_result_shape code properties types operands successors
      before after results action regions outcome
  exact Veir.interpretOp'_no_action_of_nonterm code properties types operands successors
    before after deterministic action nonterm legacy

end Veir
