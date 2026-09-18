import Veir.Interpreter.Basic

/-!
  `freeze` of a poison value yields whatever the interpreter's oracle picks
  for it, zero by default; a value without poison is returned unchanged and
  draws nothing.
-/

open Veir

private def i8 : TypeAttr := IntegerType.mk 8
private def b8 : TypeAttr := LLVM.ByteType.mk 8

/- An oracle that substitutes `42` for poison at every freeze. -/
private def picks42 : MemoryState := { MemoryState.empty with oracle := { freeze := fun _ w => BitVec.ofNat w 42 } }

private def freezeInt (mem : MemoryState) (x : Data.LLVM.Int 8) : Option (BitVec 8 × Nat) :=
  match Llvm.interpretOp' .freeze () #[i8] #[.int 8 x] #[] mem with
  | .ok (#[.int 8 (.val v)], mem, none) => some (v, mem.freezes)
  | _ => none

/- Poison becomes the oracle's choice, and the draw is counted. -/
#guard freezeInt picks42 .poison = some (42, 1)

/- By default the choice is zero. -/
#guard freezeInt MemoryState.empty .poison = some (0, 1)

/- A defined value is unchanged and draws nothing. -/
#guard freezeInt picks42 (.val 7) = some (7, 0)

private def freezeByte (mem : MemoryState) (b : Data.LLVM.Byte 8) : Option (BitVec 8 × Nat) :=
  match Llvm.interpretOp' .freeze () #[b8] #[.byte 8 b] #[] mem with
  | .ok (#[.byte 8 b], mem, none) => if b.poison = 0 then some (b.val, mem.freezes) else none
  | _ => none

/- Only the poison bits take the oracle's bits: value `0b0000_0101` with the high nibble poison becomes `0x25`. -/
#guard freezeByte picks42 ⟨0x05, 0xf0, by decide⟩ = some (0x25, 1)
