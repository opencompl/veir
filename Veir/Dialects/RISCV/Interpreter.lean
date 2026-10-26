module

public import Veir.Interpreter.Basic
public import Veir.Interpreter.CTree

public section

open CTree
open Veir.Data

namespace Veir

/-- Read little-endian bits, choosing each poison bit before extending the
loaded value to a register. Access checks are the same as for `riscvLoad`. -/
def riscvLoadCTree (mem : MemoryState) (eaddr : BitVec 64) (bytes : Nat)
    (extension : LoadExtension) : Tree (BitVec 64 × MemoryState) := do
  let pointer := mem.decode (UInt64.ofBitVec eaddr)
  let raw ← monadLift (mem.load pointer bytes.toUInt64)
  let poisonBytes ← monadLift (mem.loadPoison pointer bytes.toUInt64)
  let value := raw.toBitVecLE (8 * bytes)
  let poison := poisonBytes.toBitVecLE (8 * bytes)
  let frozen ← if poison = 0 then pure value else do
    let bits : FreezeC (.mk (8 * bytes)) ← CTree.choose (FreezeCIn.mk (8 * bytes))
    pure ((value &&& ~~~poison) ||| (poison &&& bits))
  let extended := match extension with
    | .signExt => frozen.signExtend 64
    | .zeroExt => frozen.setWidth 64
  return (extended, mem)

private def interpretRiscvLoad (properties : RISCVMemProperties)
    (operands : Array RuntimeValue) (mem : MemoryState) (bytes : Nat)
    (extension : LoadExtension)
    : Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction) := do
  let [.reg address] := operands.toList | fail
  let effectiveAddress := riscvEffectiveAddr address.val properties.imm12
  let (value, mem) ← riscvLoadCTree mem effectiveAddress bytes extension
  return (#[.reg ⟨value⟩], mem, none)

/-- RISC-V loads concretize poisoned memory with explicit choices. All other
instructions retain the outcome-monad interpreter's semantics. -/
def Riscv.interpretOpCTree (opType : Riscv) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState) : Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .ld => interpretRiscvLoad properties operands mem 8 .zeroExt
  | .lw => interpretRiscvLoad properties operands mem 4 .signExt
  | .lwu => interpretRiscvLoad properties operands mem 4 .zeroExt
  | .lh => interpretRiscvLoad properties operands mem 2 .signExt
  | .lhu => interpretRiscvLoad properties operands mem 2 .zeroExt
  | .lb => interpretRiscvLoad properties operands mem 1 .signExt
  | .lbu => interpretRiscvLoad properties operands mem 1 .zeroExt
  | other => monadLift (Riscv.interpretOp' other properties resultTypes operands blockOperands mem)

end Veir
