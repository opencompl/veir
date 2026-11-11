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

  This file contains a CTree interpreter for the nondeterministic RISC-V operations: the loads.
  Registers cannot carry poison, so a load chooses the bits of the loaded bytes that are poison,
  such as those of a byte that nothing was stored to. The other operations are delegated to the
  basic interpreter.
-/

namespace Veir

/--
CTree counterpart of a RISC-V load of `bytes` bytes through the register in `operands`, with the
immediate offset `imm12`: read the bytes and their poison bits, choose the bits that are poison,
and extend the value to 64 bits according to `ext`. With the poison bits chosen as zeros, this is
what `riscvLoad` reads.
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
@[ctree_semantics]
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
