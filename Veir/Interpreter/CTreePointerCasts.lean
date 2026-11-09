module

public import Veir.PatternRewriter.Puddle.CTreeValidity
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Interpreter.Memory
import all Veir.Interpreter.CTree
import all Veir.GlobalOpInfo
import all Veir.IR.Attribute

public section

namespace Veir.CTreePointerCasts

/-!
Integer-to-pointer casts no longer recover object identity from the memory state. Pointers carry only
addresses, so allocating memory cannot change the result of an otherwise identical cast.
-/

/-- Decoding an address is independent of the allocated objects. -/
theorem decode_memory_independent (before after : MemoryState) (address : UInt64) :
    before.decode address = after.decode address := by rfl

/-- Integer-to-pointer casts are independent of memory, including for poison. -/
theorem ptrFromInt_memory_independent (before after : MemoryState) (value : Data.LLVM.Int 64) :
    before.ptrFromInt value = after.ptrFromInt value := by
  cases value <;> rfl

/-- The state obtained by allocating one byte from empty memory. -/
def allocated : MemoryState :=
  { MemoryState.empty with objects := #[⟨0, 0⟩, ⟨65536, 1⟩] }

theorem alloc_reaches_allocated :
    MemoryState.empty.alloc 1 = .ok (allocated, ⟨65536⟩) := by rfl

theorem decode_empty : MemoryState.empty.decode 65536 = ⟨65536⟩ := by rfl

theorem decode_allocated : allocated.decode 65536 = ⟨65536⟩ := by rfl

def pointerType : TypeAttr := ⟨.llvmPointerType .mk, by rfl⟩

def intOperand : Array RuntimeValue := #[.int 64 (.val 65536)]

theorem inttoptr_no_effects (properties : propertiesOf (OpCode.llvm .inttoptr)) :
    HasOpInfo.getEffects (OpCode.llvm .inttoptr) properties = .none := by rfl

theorem inttoptr_not_terminator : HasOpInfo.isTerminator (OpCode.llvm .inttoptr) = false := by rfl

theorem inttoptr_empty :
    Llvm.interpretOp' .inttoptr () #[pointerType] intOperand #[] MemoryState.empty .riscv64 =
      .ok (#[.addr (.val ⟨65536⟩)], MemoryState.empty, none) := by simp [Llvm.interpretOp', pointerType, intOperand]; rfl

theorem inttoptr_allocated :
    Llvm.interpretOp' .inttoptr () #[pointerType] intOperand #[] allocated .riscv64 =
      .ok (#[.addr (.val ⟨65536⟩)], allocated, none) := by simp [Llvm.interpretOp', pointerType, intOperand]; rfl


theorem inttoptr_tree (mem : MemoryState) :
    CTree.interpretOp' (.llvm .inttoptr) () #[pointerType] intOperand #[] mem =
      (pure (#[.addr (mem.ptrFromInt (.val 65536))], mem, none) :
        Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction)) := by
  simp [CTree.interpretOp', Llvm.interpretOpCTree, Llvm.interpretOp', pointerType, intOperand,
    monadLift, MonadLift.monadLift]
  rfl

/-- The matcher's historical constraint admits the result observed before allocation. -/
theorem inttoptr_historical_empty :
    Puddle.CTree.CanInterpretTo (.llvm .inttoptr) () #[pointerType] intOperand
      (.ok #[.addr (.val ⟨65536⟩)]) := by
  refine ⟨MemoryState.empty, ?_⟩
  rw [inttoptr_tree]
  exact .ret _

/-- Allocating memory preserves the result admitted by the historical constraint. -/
theorem inttoptr_historical_allocated :
    Puddle.CTree.CanInterpretTo (.llvm .inttoptr) () #[pointerType] intOperand
      (.ok #[.addr (.val ⟨65536⟩)]) := by
  refine ⟨allocated, ?_⟩
  rw [inttoptr_tree]
  exact .ret _

end Veir.CTreePointerCasts
