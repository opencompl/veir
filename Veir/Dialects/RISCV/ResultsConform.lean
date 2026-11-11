module

public import Veir.Interpreter.Lemmas
public import Veir.Dialects.RISCV.Monotonicity
public import Veir.Verifier
import all Veir.Verifier.Basic
import all Veir.Verifier.Lemmas
import all Veir.Verifier
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Interpreter.Basic
import all Veir.IR.Basic
import all Veir.IR.OpCode
import all Veir.IR.Attribute
import Veir.ForLean

public section

/-!
# The results of RISC-V operations conform to their types

A verified RISC-V operation returns, if its interpretation succeeds, results that conform to its
result types (`OpCode.resultsConform`). Every result of a RISC-V operation is a register, the
verifier makes every result type `!riscv.reg`, and a store has no result where every other opcode
has one.
-/

namespace Veir

variable {ctx : WfIRContext OpCode} {op : OperationPtr} {opIn : op.InBounds ctx.raw}

/-- The number of results of a RISC-V opcode: none for a store, one otherwise. -/
private def Riscv.numResults : Riscv → Nat
  | .sd | .sw | .sh | .sb => 0
  | _ => 1

/-- A register conforms to a register type. -/
private theorem reg_conforms_of_val {r : Data.RISCV.Reg} {ty : TypeAttr}
    (h : ∃ rt, ty.val = .registerType rt) : (RuntimeValue.reg r).Conforms ty := by
  obtain ⟨a, _⟩ := ty; obtain ⟨rt, h⟩ := h; simp only at h; subst h; trivial

/-! ## Interpretation -/

/-- A RISC-V operation returns as many registers as its opcode has results. -/
private theorem Riscv.interpretOp'_ok_vals {opT : Riscv} {properties : propertiesOf opT}
    {resultTypes : Array TypeAttr} {operands : Array RuntimeValue} {bs : Array BlockPtr}
    {mem mem' : MemoryState} {vals : Array RuntimeValue} {act : Option ControlFlowAction}
    (h : Riscv.interpretOp' opT properties resultTypes operands bs mem = .ok (vals, mem', act)) :
    vals.size = opT.numResults ∧ ∀ v ∈ vals, ∃ r, v = .reg r := by
  refine ⟨?_, ?_⟩
  · cases opT <;> simp only [Riscv.interpretOp'] at h <;> grind [Riscv.numResults]
  · rcases (Riscv.interpretOp'_ok_results h).1 with ⟨r, rfl⟩ | rfl <;> simp

/-! ## Verifier -/

/-- The first check of a successful sequence of checks succeeds. -/
private theorem bind_ok_left {ε α : Type} {x : Except ε PUnit} {f : PUnit → Except ε α}
    {a : α} (h : (x >>= f) = .ok a) : x = .ok () := by
  cases x with
  | ok u => rfl
  | error e => simp [bind, Except.bind] at h

private theorem riscvVerified {opT : Riscv} (hType : op.getOpType! ctx.raw = .riscv opT)
    (hV : op.Verified ctx opIn) : Riscv.verifyLocalInvariants opT op ctx opIn = .ok () := by
  simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants,
    HasOpInfo.verifyLocalInvariants, OpCode.verifyLocalInvariants,
    ← OperationPtr.getOpType!_eq_getOpType, hType] at hV
  exact hV

/--
What every step of a successful loop that only yields or throws establishes holds for every element.
-/
private theorem Except.forIn_list_ok {α ε : Type} {l : List α}
    {f : α → PUnit → Except ε (ForInStep PUnit)} (P : α → Prop)
    (hf : ∀ a s, f a PUnit.unit = .ok s → s = .yield PUnit.unit ∧ P a)
    (h : forIn l PUnit.unit f = .ok PUnit.unit) : ∀ a ∈ l, P a := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.forIn_cons] at h
    rcases hfa : f a PUnit.unit with e | s <;> rw [hfa] at h
    · simp [bind, Except.bind] at h
    · obtain ⟨rfl, hP⟩ := hf a _ hfa
      simp only [bind, Except.bind] at h
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hP
      · exact ih h b hb

private theorem Except.forIn_range_ok {ε : Type} {n : Nat}
    {f : Nat → PUnit → Except ε (ForInStep PUnit)} (P : Nat → Prop)
    (hf : ∀ a s, f a PUnit.unit = .ok s → s = .yield PUnit.unit ∧ P a)
    (h : forIn [0:n] PUnit.unit f = .ok PUnit.unit) : ∀ i < n, P i := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  intro i hi
  exact Except.forIn_list_ok P hf h i (by simp [List.mem_range'_1]; omega)

private theorem verifyNonOperandCounts_ok {r g s : Nat}
    (h : op.verifyNonOperandCounts ctx opIn r g s = .ok ()) : op.getNumResults! ctx.raw = r := by
  rw [OperationPtr.getNumResults!_eq_getNumResults opIn]
  simp only [OperationPtr.verifyNonOperandCounts] at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · rename_i hne; simpa using hne

private theorem verifyPlainOpCounts_ok {o r : Nat}
    (h : op.verifyPlainOpCounts ctx opIn o r = .ok ()) : op.getNumResults! ctx.raw = r := by
  simp only [OperationPtr.verifyPlainOpCounts, OperationPtr.verifyOpCounts] at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · exact verifyNonOperandCounts_ok h

/-- A verified RISC-V operation has as many results as its opcode. -/
private theorem riscv_verify_numResults {opT : Riscv}
    (h : Riscv.verifyLocalInvariants opT op ctx opIn = .ok ()) :
    op.getNumResults! ctx.raw = opT.numResults := by
  unfold Riscv.verifyLocalInvariants at h
  have h' := Except.ok_of_bind_ok h
  cases opT <;>
    simp only [OperationPtr.verifyRISCVimm12, OperationPtr.verifyRISCVuimm5,
      OperationPtr.verifyRISCVuimm6, OperationPtr.verifyRISCVneg] at h' <;>
    first
      | exact verifyPlainOpCounts_ok (bind_ok_left h')
      | exact verifyPlainOpCounts_ok (bind_ok_left (bind_ok_left h'))

/-- Every result of an operation that `verifyRISCVRegisterTypes` accepts is a register. -/
private theorem verifyRISCVRegisterTypes_ok (h : op.verifyRISCVRegisterTypes ctx opIn = .ok ()) :
    ∀ i < op.getNumResults ctx.raw opIn,
      ∃ rt, ((op.getResult i).getType! ctx.raw).val = .registerType rt := by
  simp only [OperationPtr.verifyRISCVRegisterTypes] at h
  refine Except.forIn_range_ok _ (fun a s hs => ?_) (bind_ok_left (Except.ok_of_bind_ok h))
  split at hs
  · next _ hT =>
    simp only [pure, Except.pure, Except.ok.injEq] at hs
    exact ⟨hs.symm, _, hT⟩
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hs

/-- The type of a result, as an element of the result types. -/
private theorem resultType_eq {i : Nat} (hi : i < op.getNumResults ctx.raw opIn) :
    (op.getResult i).getType! ctx.raw = (op.getResultTypes! ctx.raw)[i]! := by
  rw [OperationPtr.getResultTypes!.getElem!_eq]
  rwa [OperationPtr.getNumResults!_eq_getNumResults opIn]

/-! ## The opcodes -/

/--
A verified RISC-V operation returns, if its interpretation succeeds, results that conform to its
result types.
-/
theorem Riscv.interpretOp'_results_conform (opT : Riscv)
    (hType : op.getOpType! ctx.raw = .riscv opT) (hV : op.Verified ctx opIn)
    (h : Riscv.interpretOp' opT (op.getProperties! ctx.raw (OpCode.riscv opT))
      (op.getResultTypes! ctx.raw) operands bs mem = .ok (vals, mem', act)) :
    RuntimeValue.ArrayConforms vals (op.getResultTypes! ctx.raw) := by
  have hVL := riscvVerified hType hV
  have hN := riscv_verify_numResults hVL
  have hRegs := verifyRISCVRegisterTypes_ok (bind_ok_left hVL)
  obtain ⟨hs, hr⟩ := Riscv.interpretOp'_ok_vals h
  have hsN : vals.size = op.getNumResults ctx.raw opIn := by
    rw [← OperationPtr.getNumResults!_eq_getNumResults opIn, hN, hs]
  refine ⟨by rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hN, hs], fun i hi => ?_⟩
  obtain ⟨r, hv⟩ := hr _ (Array.getElem_mem hi)
  have hT := hRegs i (hsN ▸ hi)
  rw [resultType_eq (hsN ▸ hi)] at hT
  rw [getElem!_pos vals i hi, hv]
  exact reg_conforms_of_val hT

/-- The results of every RISC-V opcode conform to their types. -/
theorem OpCode.resultsConform_riscv (opT : Riscv) : OpCode.resultsConform (.riscv opT) := by
  refine OpCode.resultsConform_def.mpr
    fun ctx op opIn hType hV operands vals mem mem' act _ h => ?_
  have hType! : op.getOpType! ctx.raw = .riscv opT := by
    rw [OperationPtr.getOpType!_eq_getOpType opIn]; exact hType
  simp only [OperationPtr.interpret] at h
  rw [hType!] at h
  simp only [Veir.interpretOp'] at h
  exact Riscv.interpretOp'_results_conform opT hType! hV h

/--
info: 'Veir.OpCode.resultsConform_riscv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OpCode.resultsConform_riscv

instance (op : Riscv) : ResultsConform (.riscv op) :=
  ⟨OpCode.resultsConform_riscv op⟩

end Veir

end
