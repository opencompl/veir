module

public import Veir.Passes.InstructionSelection.RISCV64
public import Veir.PatternRewriter.Puddle.CTreeValidity
import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.OpCode
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
import all Veir.IR.OpInfo
import all Veir.Interpreter.Memory
import all Veir.PatternRewriter.Puddle.CTreeValidity
import all Veir.Interpreter.CTree
import all Veir.IR.Attribute
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.Pointer.Basic

/-!
The current CTree Puddle validity predicate only supports operations without
memory effects. These theorems record why the memory instruction-selection
patterns require a stateful validity predicate before they can be certified.
-/

namespace Veir

open Puddle

theorem llvm_alloca_not_supported : ¬ SupportedOpCode (OpCode.llvm .alloca) := by
  intro h
  have impossible := h.2 default
  cbv at impossible
  contradiction

theorem llvm_load_not_supported : ¬ SupportedOpCode (OpCode.llvm .load) := by
  intro h
  have impossible := h.2 default
  cbv at impossible
  contradiction

theorem llvm_store_not_supported : ¬ SupportedOpCode (OpCode.llvm .store) := by
  intro h
  have impossible := h.2 default
  cbv at impossible
  contradiction

theorem alloca_pattern_not_supported : ¬ alloca_pattern.Supported := by
  unfold alloca_pattern
  unfoldPuddleBuilder
  simp [Pattern.Supported, MatchProg.Supported, MatchDecl.Supported,
    llvm_alloca_not_supported]

theorem alloca_pattern_not_valid : ¬ Puddle.CTree.Pattern.Valid alloca_pattern := by
  exact fun h => alloca_pattern_not_supported h.Supported

theorem load_pattern_not_supported (bw : Nat) (rop : Riscv)
    (h : Riscv.propertiesOf rop = RISCVMemProperties) (foldAddr : Bool) :
    ¬ (load_pattern bw rop h foldAddr).Supported := by
  cases foldAddr <;> unfold load_pattern matchFoldedAddr matchIntConstant
  all_goals
    unfoldPuddleBuilder
    simp [Pattern.Supported, MatchProg.Supported, MatchDecl.Supported,
      llvm_load_not_supported]

theorem load_pattern_not_valid (bw : Nat) (rop : Riscv)
    (h : Riscv.propertiesOf rop = RISCVMemProperties) (foldAddr : Bool) :
    ¬ Puddle.CTree.Pattern.Valid (load_pattern bw rop h foldAddr) := by
  exact fun valid => load_pattern_not_supported bw rop h foldAddr valid.Supported

theorem store_pattern_not_supported (bw : Nat) (rop : Riscv)
    (h : Riscv.propertiesOf rop = RISCVMemProperties) (foldAddr : Bool) :
    ¬ (store_pattern bw rop h foldAddr).Supported := by
  cases foldAddr <;> unfold store_pattern matchFoldedAddr matchIntConstant
  all_goals
    unfoldPuddleBuilder
    simp [Pattern.Supported, MatchProg.Supported, MatchDecl.Supported,
      llvm_store_not_supported]

theorem store_pattern_not_valid (bw : Nat) (rop : Riscv)
    (h : Riscv.propertiesOf rop = RISCVMemProperties) (foldAddr : Bool) :
    ¬ Puddle.CTree.Pattern.Valid (store_pattern bw rop h foldAddr) := by
  exact fun valid => store_pattern_not_supported bw rop h foldAddr valid.Supported

/-- A pointer-to-register cast may have no memory-independent outcome at all.
This is why dropping the pure-operation restriction does not suffice to certify
pointer and memory patterns using the current `CanInterpretTo` predicate. -/
theorem pointer_cast_has_no_uniform_outcome (results : Interp (Array RuntimeValue)) :
    ¬ Puddle.CTree.CanInterpretTo (.builtin .unrealized_conversion_cast) ()
      #[TypeAttr.of RegisterType (RegisterType.mk none)]
      #[.addr (.val ⟨1, 0⟩)] results := by
  intro h
  have h0 := h ({ objects := #[MemoryObject.ofSize 0 0, MemoryObject.ofSize 65536 1] } : MemoryState)
  have h1 := h ({ objects := #[MemoryObject.ofSize 0 0, MemoryObject.ofSize 65552 1] } : MemoryState)
  change PureOrErr.CanInterpretTo
    (pure (#[.reg ⟨65536#64⟩], ({ objects := #[MemoryObject.ofSize 0 0, MemoryObject.ofSize 65536 1] } : MemoryState), none))
    (results.map (·, ({ objects := #[MemoryObject.ofSize 0 0, MemoryObject.ofSize 65536 1] } : MemoryState), none)) at h0
  change PureOrErr.CanInterpretTo
    (pure (#[.reg ⟨65552#64⟩], ({ objects := #[MemoryObject.ofSize 0 0, MemoryObject.ofSize 65552 1] } : MemoryState), none))
    (results.map (·, ({ objects := #[MemoryObject.ofSize 0 0, MemoryObject.ofSize 65552 1] } : MemoryState), none)) at h1
  cases results <;> simp_all

/-- Numerical address round trips need a provenance hypothesis: an offset can
reach another object's base and decoding then selects that other object. -/
theorem pointer_register_roundtrip_changes_object :
    let memory : MemoryState :=
      { objects := #[MemoryObject.ofSize 0 0, MemoryObject.ofSize 65536 1,
        MemoryObject.ofSize 65552 1] }
    let pointer : Data.LLVM.Ptr := .val ⟨1, 16⟩
    memory.ptrFromInt (memory.intFromPtr pointer) ≠ pointer := by
  decide

end Veir
