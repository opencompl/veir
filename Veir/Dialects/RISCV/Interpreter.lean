module

public import Veir.Interpreter.RuntimeValue
public import Veir.Interpreter.Memory
public import Veir.Interpreter.CTree
public import Veir.Dialects.RISCV.OpInfo
import all Veir.Data.LLVM.Byte.Basic

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
  let val := b.fillPoison bits
  let extended := match ext with
    | .signExt => val.signExtend 64
    | .zeroExt => val.setWidth 64
  return (#[.reg ⟨extended⟩], mem, none)

/-- `x` is a value a RISC-V load of `n` bytes at `p` can produce: the bits stored at `p`, with each
poison bit frozen to some concrete value. It is kept folded, so that the validity proofs treat the
loaded value as an arbitrary bitvector. -/
def LoadsBits (mem : MemoryState) (p : Data.Pointer) (n : Nat) (x : BitVec (8 * n)) : Prop :=
  ∃ b, mem.loadByte p (8 * n) = .ok b ∧ ∃ bits, x = b.val ||| (b.poison &&& bits)

/-- A RISC-V load CTree that succeeds returns the bits it read, extended to a register, and leaves
memory unchanged. -/
theorem riscvLoadCTree_canInterpretTo_ok {EIn : Type} {E : EIn → Type}
    [ErrorE -< E] [UBE -< E] {imm12 : BitVec 12} {addr : Data.RISCV.Reg}
    {mem mem' : MemoryState} {n : Nat} {ext : LoadExtension} {v : RuntimeValue} :
    PureOrErr.CanInterpretTo (E := E) (riscvLoadCTree imm12 #[.reg addr] mem n ext)
        (.ok (#[v], mem', none)) ↔
      ∃ x, LoadsBits mem (mem.decode (UInt64.ofBitVec (riscvEffectiveAddr addr.val imm12))) n x ∧
        v = .reg ⟨match ext with
          | .signExt => x.signExtend 64
          | .zeroExt => x.setWidth 64⟩ ∧
        mem' = mem := by
  simp [riscvLoadCTree, Bind.bind, PureOrErr.CanInterpretTo.bind_iff, LoadsBits]
  constructor
  · rintro ⟨b, hb, ⟨bits, rfl⟩, rfl⟩
    exact ⟨_, ⟨b, hb, bits, rfl⟩, by cases ext <;> simp [Data.LLVM.Byte.fillPoison], rfl⟩
  · rintro ⟨_, ⟨b, hb, bits, rfl⟩, rfl, rfl⟩
    exact ⟨b, hb, ⟨bits, by cases ext <;> simp [Data.LLVM.Byte.fillPoison]⟩, rfl⟩

/-- `riscvLoadCTree_canInterpretTo_ok` for the matched result of a load, which the validity goal
quantifies over together with the input and output memories: the result is substituted by the
extended loaded bits and the output memory by the input memory. -/
theorem forall_riscvLoadCTree_canInterpretTo_ok {EIn : Type}
    {E : EIn → Type} [ErrorE -< E] [UBE -< E] {imm12 : BitVec 12} {addr : Data.RISCV.Reg}
    {n : Nat} {ext : LoadExtension} {P : RuntimeValue → MemoryState → MemoryState → Prop} :
    (∀ v mem mem', PureOrErr.CanInterpretTo (E := E) (riscvLoadCTree imm12 #[.reg addr] mem n ext)
        (.ok (#[v], mem', none)) → P v mem mem') ↔
      ∀ mem x, LoadsBits mem (mem.decode (UInt64.ofBitVec (riscvEffectiveAddr addr.val imm12))) n x →
        P (.reg ⟨match ext with
          | .signExt => x.signExtend 64
          | .zeroExt => x.setWidth 64⟩) mem mem := by
  simp only [riscvLoadCTree_canInterpretTo_ok]
  constructor
  · exact fun h mem x hx => h _ _ _ ⟨x, hx, rfl, rfl⟩
  · rintro h v mem mem' ⟨x, hx, rfl, rfl⟩
    exact h _ x hx

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
