import Veir.Dialects.RISCV.Interpreter

open Veir Veir.Data

private def loadMemory (value poison : UInt8) : MemoryState :=
  { MemoryState.empty with
    objects := #[⟨0, 0⟩, ⟨0x10000, 8⟩]
    bytes := .ofList ((List.range 8).map fun i =>
      (0x10000 + i.toUInt64, ⟨value, poison⟩)) }

/-- A bounded observer for these finite trees, supplying the requested poison bits. -/
private def sample (bits : Nat) : Nat → Tree α → Option α
  | 0, _ => none
  | fuel + 1, tree =>
    match tree.unfold with
    | .ret value => some value
    | .vis _ _ => none
    | .tau (.inl .c1) next => sample bits fuel (next PUnit.unit)
    | .tau (.inr (.mk width)) next => sample bits fuel (next (BitVec.ofNat width bits))
    | .tau (.inr .pointer) next => sample bits fuel (next Pointer.null)

private def loadResult (opcode : Riscv) (properties : propertiesOf opcode)
    (memory : MemoryState) (bits : Nat := 0) : Option (BitVec 64) := do
  let (values, _, _) ← sample bits 8
    (Riscv.interpretOpCTree opcode properties #[RegisterType.mk] #[.reg ⟨0x10000⟩] #[] memory)
  let .reg value ← values[0]? | none
  return value.val

/- Every load opcode retains its width and signedness on concrete memory. -/
#guard loadResult .ld default (loadMemory 0x80 0) = some 0x8080808080808080
#guard loadResult .lw default (loadMemory 0x80 0) = some 0xffffffff80808080
#guard loadResult .lwu default (loadMemory 0x80 0) = some 0x80808080
#guard loadResult .lh default (loadMemory 0x80 0) = some 0xffffffffffff8080
#guard loadResult .lhu default (loadMemory 0x80 0) = some 0x8080
#guard loadResult .lb default (loadMemory 0x80 0) = some 0xffffffffffffff80
#guard loadResult .lbu default (loadMemory 0x80 0) = some 0x80

/- The poisoned sign bit may become zero despite its raw stored one. Known
   low bits remain one, and sign extension follows the choice. -/
#guard loadResult .lb default (loadMemory 0xff 0x80) 0 = some 127
#guard loadResult .lb default (loadMemory 0xff 0x80) 128 = some 0xffffffffffffffff
#guard loadResult .lbu default (loadMemory 0xff 0x80) 128 = some 255

/- The access check still yields UB before any nondeterministic choice. -/
#guard match (riscvLoadCTree (loadMemory 0x80 0) 0x10008 1 .zeroExt).unfold with
  | .vis (.inr _) _ => true
  | _ => false
