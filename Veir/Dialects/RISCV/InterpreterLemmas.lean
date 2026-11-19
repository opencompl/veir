module

public import Veir.Dialects.RISCV.Interpreter
import all Veir.Dialects.RISCV.Interpreter
import all Veir.Data.LLVM.Byte.Basic

public section

open CTree
open Veir.Data


namespace Veir

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

/-- A root store and a created store that write the same bytes simulate each other.
The statement is the normal form that `Veir.Sim.bind_monadLift_left_iff` and
`Veir.Sim.monadLift_right_iff` give for the simulation of the two lifted stores: a match on the
root store, whose success case matches on the created store. It is polymorphic in the result type
`β`, so that its matchers have the same shape as the matchers of those lemmas and unify with them. -/
theorem store_pure_store {β : Type} {P : β → β → Prop} {Qub Qfail : β → Prop}
    (f : MemoryState → β) (hP : ∀ mem, P (f mem) (f mem))
    (mem : MemoryState) (p : Data.Pointer) (source target poison : ByteArray)
    (hsource : poison.size = source.size) (htarget : poison.size = target.size)
    (hbytes : source = target) :
    match (mem.store p source poison hsource >>= fun mem => Interp.ok (f mem)) with
    | .ok value =>
      match (mem.store p target poison htarget >>= fun mem => Interp.ok (f mem)) with
      | .ok value' => P value value'
      | .ub _ => Qub value
      | .fail _ => Qfail value
    | .ub _ => True
    | .fail _ => True := by
  subst hbytes
  cases mem.store p source poison hsource <;> simp [hP, Bind.bind]

end Veir
