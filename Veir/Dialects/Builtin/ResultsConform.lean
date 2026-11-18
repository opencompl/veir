module

public import Veir.Interpreter.ResultsConform
public import Veir.Interpreter.ResultsConformLemmas

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.Builtin.Interpreter
import all Veir.Dialects.Builtin.OpInfo
import all Veir.Verifier

public section

/-!
# The results of the builtin operations conform to their types

`builtin.unrealized_conversion_cast` casts its one operand to its one result type, and builds the
result from that type, so whatever bits it chooses for poison, the result conforms. The other
builtin operations have no semantics: their CTrees fail and return nothing.
-/

namespace Veir

variable {ctx : WfIRContext OpCode} {op : OperationPtr} {opIn : op.InBounds ctx.raw}

/-- A single value of a single type conforms if the value does. -/
private theorem arrayConforms_singleton {v : RuntimeValue} {t : TypeAttr} (h : v.Conforms t) :
    RuntimeValue.ArrayConforms #[v] #[t] := by
  refine ⟨rfl, fun i hi => ?_⟩
  obtain rfl : i = 0 := by simpa using hi
  exact h

private theorem reg_conforms_of_val {r : Data.RISCV.Reg} {ty : TypeAttr} {rt : RegisterType}
    (h : ty.val = .registerType rt) : (RuntimeValue.reg r).Conforms ty := by
  obtain ⟨a, _⟩ := ty; simp only at h; subst h; trivial

/-- A verified `builtin.unrealized_conversion_cast` has one result. -/
private theorem cast_numResults_eq_one
    (hType : op.getOpType! ctx.raw = .builtin .unrealized_conversion_cast)
    (opVerif : op.Verified ctx opIn) : op.getNumResults! ctx.raw = 1 := by
  simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants,
    HasOpInfo.verifyLocalInvariants, OpCode.verifyLocalInvariants,
    ← OperationPtr.getOpType!_eq_getOpType, hType, Builtin.verifyLocalInvariants] at opVerif
  have h := bind_ok_left opVerif
  simp only [OperationPtr.verifyPlainOpCounts, OperationPtr.verifyOpCounts] at h
  split at h
  · simp [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · exact verifyNonOperandCounts_ok h

/-- The results of a CTree run of every builtin opcode conform to their types. -/
theorem OpCode.resultsConform_builtin (op : Builtin) : OpCode.ResultsConform (.builtin op) := by
  refine OpCode.resultsConform_def.mpr
    fun ctx o opIn hType opVerif operands mem conforms vals mem' act h => ?_
  have hType! : o.getOpType! ctx.raw = .builtin op := by
    rw [OperationPtr.getOpType!_eq_getOpType opIn]; exact hType
  rw [OperationPtr.interpretCTree_def!, hType!] at h
  cases op with
  | unregistered => simp [CTree.interpretOp', Builtin.interpretOpCTree] at h
  | module => simp [CTree.interpretOp', Builtin.interpretOpCTree] at h
  | unrealized_conversion_cast =>
    obtain ⟨t, ht⟩ : ∃ t, o.getResultTypes! ctx.raw = #[t] := by
      rw [← Array.size_eq_one_iff, OperationPtr.getResultTypes!.size_eq_getNumResults!]
      exact cast_numResults_eq_one hType! opVerif
    rw [ht] at h ⊢
    have h0 : (#[t] : Array TypeAttr)[0]? = some t := rfl
    simp only [CTree.interpretOp', Builtin.interpretOpCTree,
      Builtin.interpretUnrealizedConversionCastCTree, h0] at h
    repeat' split at h
    all_goals
      simp only [Bind.bind, CTree.MayReturn.bind_iff, CTree.MayReturn.pure_iff,
        CTree.MayReturn.fail_iff, Prod.mk.injEq, false_and, exists_false] at h
    all_goals
      first | (obtain ⟨rfl, -, -⟩ := h) | (obtain ⟨_, -, rfl, -, -⟩ := h)
      refine arrayConforms_singleton ?_
      first
        | exact reg_conforms_of_val ‹_›
        | exact int_conforms_of_val ‹_› rfl
        | exact byte_conforms_of_val ‹_› rfl
        | exact addr_conforms_of_val ⟨_, ‹_›⟩
        | exact int_conforms_of_val ‹_› (by omega)
        | exact byte_conforms_of_val ‹_› (by omega)

instance (op : Builtin) : ResultsConform (.builtin op) := ⟨OpCode.resultsConform_builtin op⟩

end Veir

end
