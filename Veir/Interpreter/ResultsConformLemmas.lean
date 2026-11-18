module

public import Veir.Interpreter.ResultsConform
public import Veir.Verifier

import all Veir.Verifier.Basic
import all Veir.Verifier.Lemmas
import all Veir.Verifier
import all Veir.Interpreter.Basic
import all Veir.Interpreter.Memory
import all Veir.IR.Basic
import all Veir.IR.OpCode
import all Veir.IR.Attribute

public section

/-!
# Conformance from the verifier

Every dialect reads the same facts off a successful verifier run and turns them into conformance
of a result. The lemmas that do it live here rather than being repeated once per dialect.
-/

namespace Veir

variable {ctx : WfIRContext OpCode} {op : OperationPtr} {opIn : op.InBounds ctx.raw}

theorem ite_throw_ok {ε : Type} {c : Prop} [Decidable c] {e : ε}
    (h : (if c then throw e else pure () : Except ε PUnit) = .ok ()) : ¬c := by
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · assumption

theorem Interp.exists_of_bind_eq_ok {α β : Type} {x : Interp α} {f : α → Interp β}
    {b : β} (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp_all

theorem int_conforms_of_val {w : Nat} {x : Data.LLVM.Int w} {ty : TypeAttr}
    {it : IntegerType} (h : ty.val = .integerType it) (hw : it.bitwidth = w) :
    (RuntimeValue.int w x).Conforms ty := by
  obtain ⟨a, _⟩ := ty; simp only at h; subst h; exact hw

theorem byte_conforms_of_val {w : Nat} {x : Data.LLVM.Byte w} {ty : TypeAttr}
    {bt : LLVM.ByteType} (h : ty.val = .byteType bt) (hw : bt.bitwidth = w) :
    (RuntimeValue.byte w x).Conforms ty := by
  obtain ⟨a, _⟩ := ty; simp only at h; subst h; exact hw

theorem addr_conforms_of_val {x : Data.LLVM.Ptr} {ty : TypeAttr}
    (h : ∃ p, ty.val = .llvmPointerType p) : (RuntimeValue.addr x).Conforms ty := by
  obtain ⟨a, _⟩ := ty; obtain ⟨p, h⟩ := h; simp only at h; subst h; trivial

theorem verifyLlvmPointerType_ok {ty : TypeAttr} {msg : String}
    (h : ty.verifyLlvmPointerType msg = .ok ()) : ∃ p, ty.val = .llvmPointerType p := by
  simp only [TypeAttr.verifyLlvmPointerType] at h
  split at h
  · exact ⟨_, by assumption⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A load returns a value of the type it loads. -/
theorem llvmLoad_conforms {mem : MemoryState} {p : Data.Pointer} {t : TypeAttr}
    {v : RuntimeValue} (h : mem.llvmLoad p t = .ok v) : v.Conforms t := by
  simp only [MemoryState.llvmLoad] at h
  split at h
  · simp at h
  split at h <;>
    (repeat' (first
      | (obtain ⟨_, -, h⟩ := Interp.exists_of_bind_eq_ok h)
      | split at h)) <;>
    (try simp only [Interp.pure_eq, Interp.ok.injEq] at h) <;> (try subst h) <;>
    first
      | (simp at h; done)
      | exact int_conforms_of_val ‹_› rfl
      | exact byte_conforms_of_val ‹_› rfl
      | exact addr_conforms_of_val ⟨_, ‹_›⟩

/-- The first check of a successful sequence of checks succeeds. -/
theorem bind_ok_left {ε α : Type} {x : Except ε PUnit} {f : PUnit → Except ε α}
    {a : α} (h : (x >>= f) = .ok a) : x = .ok () := by
  cases x with
  | ok u => rfl
  | error e => simp [bind, Except.bind] at h

/--
What every step of a successful loop that only yields or throws establishes holds for every element.
-/
theorem Except.forIn_list_ok {α ε : Type} {l : List α}
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

theorem Except.forIn_range_ok {ε : Type} {n : Nat}
    {f : Nat → PUnit → Except ε (ForInStep PUnit)} (P : Nat → Prop)
    (hf : ∀ a s, f a PUnit.unit = .ok s → s = .yield PUnit.unit ∧ P a)
    (h : forIn [0:n] PUnit.unit f = .ok PUnit.unit) : ∀ i < n, P i := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  intro i hi
  exact Except.forIn_list_ok P hf h i (by simp [List.mem_range'_1]; omega)

theorem verifyNonOperandCounts_ok {r g s : Nat}
    (h : op.verifyNonOperandCounts ctx opIn r g s = .ok ()) : op.getNumResults! ctx.raw = r := by
  rw [OperationPtr.getNumResults!_eq_getNumResults opIn]
  simp only [OperationPtr.verifyNonOperandCounts] at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · rename_i hne; simpa using hne

/-- The type of a result, as an element of the result types. -/
theorem resultType_eq {i : Nat} (hi : i < op.getNumResults ctx.raw opIn) :
    (op.getResult i).getType! ctx.raw = (op.getResultTypes! ctx.raw)[i]! := by
  rw [OperationPtr.getResultTypes!.getElem!_eq]
  rwa [OperationPtr.getNumResults!_eq_getNumResults opIn]

end Veir

end
