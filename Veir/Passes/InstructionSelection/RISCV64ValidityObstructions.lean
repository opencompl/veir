module

public import Veir.PatternRewriter.Puddle.CTreeValidity
import all Veir.OpCode
import all Veir.Interpreter.Memory
import all Veir.PatternRewriter.Puddle.CTreeValidity
import all Veir.Interpreter.CTree
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.Builtin.Interpreter
import all Veir.IR.Attribute
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.Pointer.Basic

/-!
Pointer provenance examples relevant to stateful instruction selection.
Numerical address equality alone does not establish a valid pointer round trip.
-/

namespace Veir

/-- Decoding a register as a pointer depends on memory's object boundaries, so there may
be no memory-independent pointer outcome even though pointer-to-register casts read an address. -/
theorem register_pointer_cast_has_no_uniform_outcome (results : Interp (Array RuntimeValue)) :
    ¬ Puddle.CTree.CanInterpretTo (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of LLVM.PointerType {}]
      #[.reg ⟨65536#64⟩] results := by
  intro h
  have h0 := h ({ bytes := {}, objects := #[⟨0, 0⟩, ⟨65536, 1⟩] } : MemoryState)
  have h1 := h ({ bytes := {}, objects := #[⟨0, 0⟩, ⟨65552, 1⟩] } : MemoryState)
  change PureOrErr.CanInterpretTo (E := ErrorE ⊕ₑ CTree.UBE) (C := FreezeC)
    (pure (#[.addr (.val ⟨1, 65536⟩)], ({ bytes := {}, objects := #[⟨0, 0⟩, ⟨65536, 1⟩] } : MemoryState), none))
    (results.map (·, ({ bytes := {}, objects := #[⟨0, 0⟩, ⟨65536, 1⟩] } : MemoryState), none)) at h0
  change PureOrErr.CanInterpretTo (E := ErrorE ⊕ₑ CTree.UBE) (C := FreezeC)
    (pure (#[.addr (.val ⟨0, 65536⟩)], ({ bytes := {}, objects := #[⟨0, 0⟩, ⟨65552, 1⟩] } : MemoryState), none))
    (results.map (·, ({ bytes := {}, objects := #[⟨0, 0⟩, ⟨65552, 1⟩] } : MemoryState), none)) at h1
  cases results <;> simp_all

/-- Numerical address round trips need a provenance hypothesis: an address can
reach another object's base and decoding then selects that other object. -/
theorem pointer_register_roundtrip_changes_object :
    let memory : MemoryState :=
      { bytes := {}, objects := #[⟨0, 0⟩, ⟨65536, 1⟩,
        ⟨65552, 1⟩] }
    let pointer : Data.LLVM.Ptr := .val ⟨1, 65552⟩
    memory.ptrFromInt (pointer.toInt) ≠ pointer := by
  decide

end Veir
