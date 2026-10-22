import Veir.InstSimplify.MiscSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS5693p
/-- An operational model witness, not a Pattern.Valid counterexample. -/
def witnessPointer : LLVM.Ptr := .val ⟨1,1⟩
def witnessMemory : MemoryState := { bytes := {}, objects := #[⟨0,0⟩,⟨1,1⟩] }
def ity : TypeAttr := IntegerType.mk 64 .signless
def pty : TypeAttr := LLVM.PointerType.mk

theorem pointer_to_integer :
    interpretOp' (.llvm .ptrtoint) () #[ity] #[.addr witnessPointer] #[] MemoryState.empty =
      .ok (#[.int 64 (.val 1)],MemoryState.empty,none) := by rfl

theorem integer_to_pointer_empty :
    interpretOp' (.llvm .inttoptr) () #[pty] #[.int 64 (.val 1)] #[] MemoryState.empty =
      .ok (#[.addr (.val ⟨0,1⟩)],MemoryState.empty,none) := by rfl

theorem integer_to_pointer_allocated :
    interpretOp' (.llvm .inttoptr) () #[pty] #[.int 64 (.val 1)] #[] witnessMemory =
      .ok (#[.addr witnessPointer],witnessMemory,none) := by rfl

theorem operational_roundtrip_differs :
    LLVM.Ptr.val ⟨0,1⟩ ≠ witnessPointer := by decide

/-- The local pure judgment cannot provide a single result for this integer-to-pointer cast. -/
theorem no_memory_uniform_result :
    ¬ ∃ v, InterpretsTo (.llvm .inttoptr) () #[pty] #[.int 64 (.val 1)] #[v] := by
  rintro ⟨v,hi⟩
  have h0 := hi.2 MemoryState.empty
  have h1 := hi.2 witnessMemory
  rw [integer_to_pointer_empty] at h0
  rw [integer_to_pointer_allocated] at h1
  have h0 : v = .addr (.val ⟨0,1⟩) := by simpa using h0.symm
  have h1 : v = .addr witnessPointer := by simpa using h1.symm
  rw [h0] at h1
  exact operational_roundtrip_differs (RuntimeValue.addr.inj h1)
end Veir.InstSimplify.IS5693p
