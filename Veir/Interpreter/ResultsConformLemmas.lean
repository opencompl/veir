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

end Veir

end
