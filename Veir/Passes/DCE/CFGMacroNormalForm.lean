module

public import Veir.Passes.DCE.CFGMacroRefinement
public import Veir.Passes.DCE.MacroSuffix
import all Veir.Passes.DCE.Structure
import all Veir.Passes.DCE.StateRefinement
import all Veir.IR.Basic
import all Veir.Interfaces.SideEffectInterfaces

public section

namespace Veir.DCE

/-- The original well-formed operation chain supplies a strictly decreasing
rank, independently of the changing linked lists during DCE. -/
noncomputable def cfgOperationRank (ctx : WfIRContext OpCode) (operation : OperationPtr) : Nat :=
  if inBounds : operation.InBounds ctx.raw then
    operation.idxInParentFromTail ctx.raw inBounds ctx.wellFormed else 0

theorem cfgStep_rank_decreases (ctx : WfIRContext OpCode)
    (state next : CTree.interpretCFG.StateLocation ctx × InterpreterState ctx)
    (operation nextOperation : OperationPtr)
    (identifies : cfgOperationAt state = some operation)
    (eligible : Eligible ctx.raw operation)
    (executes : PureOrErr.CanInterpretTo
      (CTree.interpretCFGTreeStep state.1 state.2) (.ok (.inl next)))
    (identifiesNext : cfgOperationAt next = some nextOperation) :
    cfgOperationRank ctx nextOperation < cfgOperationRank ctx operation := by
  rcases state with ⟨location, source⟩
  cases location with
  | inl block => cases identifies
  | inr sourceOperation =>
    rcases sourceOperation with ⟨sourceOperation, sourceIn⟩
    have : sourceOperation = operation := Option.some.inj identifies
    subst sourceOperation
    have hstate : StatesRefineOn (fun _ => False) source source :=
      ⟨Tree.Refinement.MemoryState.isRefinedBy_refl _, fun _ impossible => False.elim impossible⟩
    rcases eligible with ⟨hregions, hwrite, hallocate, hterminator⟩
    simp only [OperationPtr.getEffects, hregions, bne_self_eq_false, Bool.false_eq_true,
      ↓reduceIte] at hwrite hallocate
    have hwrite' : (OpCode.getEffects (operation.getOpType! ctx.raw)
        (operation.getProperties! ctx.raw (operation.getOpType! ctx.raw))).writes = false := by
      simpa [HasOpInfo.getEffects, instHasOpInfoOpCode] using hwrite
    have hallocate' : (OpCode.getEffects (operation.getOpType! ctx.raw)
        (operation.getProperties! ctx.raw (operation.getOpType! ctx.raw))).allocates = false := by
      simpa [HasOpInfo.getEffects, instHasOpInfoOpCode] using hallocate
    have hterminator' : OpCode.isTerminator (operation.getOpType! ctx.raw) = false := by
      simpa [HasOpInfo.isTerminator, instHasOpInfoOpCode] using hterminator
    obtain ⟨nextOp, nextIn, nextState, hnext, resultEq, _⟩ :=
      interpretCFGTreeStep_discarded_frame operation source source sourceIn (fun _ => False)
        hstate (fun _ impossible => False.elim impossible) hwrite' hallocate' hterminator'
        (.inl next) executes
    have nextEq : next = (.inr ⟨nextOp, nextIn⟩, nextState) := Sum.inl.inj resultEq
    subst next
    have : nextOp = nextOperation := Option.some.inj identifiesNext
    subst nextOp
    have hnext' : operation.getNextOp! ctx.raw = some nextOperation := by
      simpa only [eq_bang] using hnext
    simpa only [cfgOperationRank, dite_eq_left sourceIn, dite_eq_left nextIn] using
      OperationPtr.idxInParentFromTail_next_lt_idxInParentFromTail operation ctx.raw nextOperation
        hnext' nextIn sourceIn ctx.wellFormed

/-- A normalized source step cannot stop at any operation deleted by the pass. -/
theorem ErasureTrace.macroBody_endpoint_survives
    {sourceCtx targetCtx : WfIRContext OpCode} {operations : List OperationPtr}
    (trace : ErasureTrace sourceCtx operations targetCtx)
    (state next : CTree.interpretCFG.StateLocation sourceCtx × InterpreterState sourceCtx)
    (operation : OperationPtr)
    (executes : PureOrErr.CanInterpretTo
      (macroBody cfgOperationAt (fun (location, state) => CTree.interpretCFGTreeStep location state)
        operations state) (.ok (.inl next)))
    (identifies : cfgOperationAt next = some operation) : operation.InBounds targetCtx.raw := by
  have outside := macroBody_endpoint_not_deleted cfgOperationAt
    (fun (location, state) => CTree.interpretCFGTreeStep location state)
    (Eligible sourceCtx.raw) (cfgOperationRank sourceCtx) (cfgStep_rank_decreases sourceCtx)
    operations trace.eligible state next operation executes identifies
  have sourceIn : operation.InBounds sourceCtx.raw := by
    rcases next with ⟨location, nextState⟩
    cases location with
    | inl block => cases identifies
    | inr sourceOperation =>
      rcases sourceOperation with ⟨sourceOperation, sourceIn⟩
      have : sourceOperation = operation := Option.some.inj identifies
      subst sourceOperation
      exact sourceIn
  by_cases survives : operation.InBounds targetCtx.raw
  · exact survives
  · exact False.elim (outside ((trace.deleted_iff operation sourceIn).mpr survives))

theorem ErasureTrace.macroSuffix_endpoint_survives
    {sourceCtx targetCtx : WfIRContext OpCode} {operations : List OperationPtr}
    (trace : ErasureTrace sourceCtx operations targetCtx)
    (initial : (CTree.interpretCFG.StateLocation sourceCtx × InterpreterState sourceCtx) ⊕
      (InterpreterState sourceCtx × Array RuntimeValue))
    (next : CTree.interpretCFG.StateLocation sourceCtx × InterpreterState sourceCtx)
    (operation : OperationPtr)
    (executes : PureOrErr.CanInterpretTo
      (macroSuffix cfgOperationAt (fun (location, state) => CTree.interpretCFGTreeStep location state)
        operations initial) (.ok (.inl next)))
    (identifies : cfgOperationAt next = some operation) : operation.InBounds targetCtx.raw := by
  have outside := macroSuffix_endpoint_not_deleted cfgOperationAt
    (fun (location, state) => CTree.interpretCFGTreeStep location state)
    (Eligible sourceCtx.raw) (cfgOperationRank sourceCtx) (cfgStep_rank_decreases sourceCtx)
    operations trace.eligible initial next operation executes identifies
  have sourceIn : operation.InBounds sourceCtx.raw := by
    rcases next with ⟨location, nextState⟩
    cases location with
    | inl block => cases identifies
    | inr sourceOperation =>
      rcases sourceOperation with ⟨sourceOperation, sourceIn⟩
      have : sourceOperation = operation := Option.some.inj identifies
      subst sourceOperation
      exact sourceIn
  by_cases survives : operation.InBounds targetCtx.raw
  · exact survives
  · exact False.elim (outside ((trace.deleted_iff operation sourceIn).mpr survives))

end Veir.DCE
