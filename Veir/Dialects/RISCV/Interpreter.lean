module

public import Veir.Interpreter.RuntimeValue
public import Veir.Interpreter.Memory
public import Veir.Interpreter.CTree
public import Veir.Dialects.RISCV.OpInfo

public section

open CTree
open Veir.Data

/-!
  # CTree-based RISC-V Interpreter

  This file contains the CTree interpreter for RISC-V. The loads have CTree semantics of their own;
  the other operations lift the semantics of the basic interpreter.
-/

namespace Veir

/--
A RISC-V load loads `bytes` bytes into a 64-bit register. Registers cannot carry poison, so we
use a ctree choice to set the poison bits of a loaded value: bits marked as poison in memory are
nondeterministically assigned concrete in-register bits.
-/
def riscvLoadCTree {EIn : Type} {E : EIn → Type} [ErrorE -< E] [UBE -< E]
    (imm12 : BitVec 12) (operands : Array RuntimeValue) (mem : MemoryState) (bytes : Nat)
    (ext : LoadExtension) :
    CTree E FreezeC ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) := do
  let [.reg addr] := operands.toList | fail
  let eaddr := riscvEffectiveAddr addr.val imm12
  let b ← monadLift (mem.loadByte (mem.decode (UInt64.ofBitVec eaddr)) (8 * bytes))
  let bits : FreezeC (.mk (8 * bytes)) ← CTree.choose (FreezeCIn.mk (8 * bytes))
  let val := b.val ||| (b.poison &&& bits)
  let extended := match ext with
    | .signExt => val.signExtend 64
    | .zeroExt => val.setWidth 64
  return (#[.reg ⟨extended⟩], mem, none)

/-- Interpret a RISC-V operation using CTrees. -/
def Riscv.interpretOpCTree {EIn : Type} {E : EIn → Type}
    [ErrorE -< E] [UBE -< E] (opType : Veir.Riscv) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState)
    : CTree E FreezeC (((Array RuntimeValue) × MemoryState × Option ControlFlowAction)) :=
  match opType with
  | .ld => riscvLoadCTree properties.imm12 operands mem 8 .zeroExt
  | .lw => riscvLoadCTree properties.imm12 operands mem 4 .signExt
  | .lwu => riscvLoadCTree properties.imm12 operands mem 4 .zeroExt
  | .lh => riscvLoadCTree properties.imm12 operands mem 2 .signExt
  | .lhu => riscvLoadCTree properties.imm12 operands mem 2 .zeroExt
  | .lb => riscvLoadCTree properties.imm12 operands mem 1 .signExt
  | .lbu => riscvLoadCTree properties.imm12 operands mem 1 .zeroExt
  | opType => do
      monadLift $ Riscv.interpretOp' opType properties resultTypes operands blockOperands mem

end Veir
