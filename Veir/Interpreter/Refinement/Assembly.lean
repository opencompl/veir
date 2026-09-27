module

public import Veir.Interpreter.Refinement.Basic

import all Veir.Interpreter.Memory

public section

/-!
# Refinement in assembly mode

The refinement relation of `Veir.Interpreter.Refinement.Basic` compares two
pointers by the object they name and the offset they hold. A target that has
been lowered to machine code holds no such thing: a register, and a byte of
memory written through the machine interface, hold only an address. Alive2
draws the same distinction and switches to *assembly mode* (`--tgt-is-asm`)
for a machine-code target, where a pointer of the source is matched by the
address it has in the source memory.

This file gives that relation. It differs from the ordinary one in two places:

* a pointer is compared by its address, so a source pointer may be matched by
  a target pointer into another object, or by a bare register, as long as the
  address agrees;
* the two memory states need not be equal, only refined, since the target
  reaches the same addresses through different objects.

Everything else is inherited: on values that are not pointers the relation
falls back to `RuntimeValue.isRefinedBy`.

The relation is stated over both memory states because an address is not a
property of a pointer alone.

Three things are left for the pass that first uses this relation:

* `RuntimeValue.ofReg?` cannot turn a register back into a pointer, since
  finding the object an address belongs to needs the memory state; the cast
  has the state and has to pass it on.
* `MemoryState.decode_address`, the converse of `address_decode`, holds only
  under `MemoryState.LayoutWf`, which also has to be shown to survive `alloc`.
  It is what makes an access through a decoded pointer reach the object the
  source accessed.
* Once a byte of memory can hold a pointer fragment, memory refinement needs
  an assembly-mode reading of its own, in which a fragment is matched by the
  byte of the address it stands for.
-/

open Veir.Data

namespace Veir

/-! ## The layout of a memory state -/

/--
Two memory states lay their objects out the same way: the same number of
objects, each at the same address. A pass that neither allocates nor frees
relates its two states this way, and then a pointer has the same address on
both sides.
-/
structure MemoryState.SameLayout (source target : MemoryState) : Prop where
  /-- The two states hold the same number of objects. -/
  size : source.objects.size = target.objects.size
  /-- Corresponding objects start at the same address. -/
  base : ∀ i : Nat, source.objects[i]?.map (·.base) = target.objects[i]?.map (·.base)

theorem MemoryState.SameLayout.address {source target : MemoryState}
    (h : source.SameLayout target) (p : Pointer) : source.address p = target.address p := by
  simp only [MemoryState.address, h.base]

theorem MemoryState.SameLayout.refl (mem : MemoryState) : mem.SameLayout mem :=
  ⟨rfl, fun _ => rfl⟩

/--
The invariant that `alloc` maintains and that nothing states: objects are laid
out in increasing order of address, an object ends before the next one begins,
and no object wraps the address space.

`decode` recovers a pointer from an address by finding the last object that
starts at or below it, which is the object the address belongs to only under
this invariant.
-/
structure MemoryState.LayoutWf (mem : MemoryState) : Prop where
  /-- An object ends, guard byte included, before the next one begins. -/
  disjoint : ∀ i : Nat, i + 1 < mem.objects.size →
    mem.objects[i]!.base.toNat + mem.objects[i]!.size < mem.objects[i + 1]!.base.toNat
  /-- No object reaches past the end of the address space. -/
  noWrap : ∀ i : Nat, i < mem.objects.size →
    mem.objects[i]!.base.toNat + mem.objects[i]!.size < 2 ^ 64

/-! ## The address of a decoded pointer -/

/--
An address decodes to a pointer with that same address, whichever object the
decoding lands in. This is what makes a pointer survive a register in assembly
mode: the pointer that comes back may name another object, but it has the
address that went in.
-/
theorem MemoryState.address_decode (mem : MemoryState) (addr : UInt64) :
    mem.address (mem.decode addr) = addr := by
  simp only [MemoryState.address, MemoryState.decode]
  generalize (Option.map (·.base) mem.objects[mem.objectOfAddress addr]?).getD 0 = base
  rw [UInt64.add_comm, UInt64.sub_add_cancel]

/-! ## The relation -/

/--
Refinement of runtime values in assembly mode, between a source value in the
memory state `source` and a target value in the memory state `target`.

A pointer is compared by its address, and is matched by a pointer or by the
register holding its address. Every other pair of values is compared as in the
ordinary relation; integer to register punning would extend the same way.
-/
@[expose]
def RuntimeValue.isRefinedByAsm (source target : MemoryState) :
    RuntimeValue → RuntimeValue → Prop
  | .addr .poison, _ => True
  | .addr (.val p), .addr (.val q) => source.address p = target.address q
  | .addr (.val p), .reg r => (source.address p).toBitVec = r.val
  | s, t => s ⊒ t

/-- An array of runtime values refined pointwise in assembly mode. -/
@[expose]
def RuntimeValue.arrayIsRefinedByAsm (source target : MemoryState)
    (vals vals' : Array RuntimeValue) : Prop :=
  vals.size = vals'.size ∧
    ∀ (i : Nat) (_ : i < vals.size), isRefinedByAsm source target vals[i]! vals'[i]!

/--
A function result refined in assembly mode: the memories are refined rather
than equal, because the target may hold an address where the source holds a
pointer, and the returned values are refined by address.
-/
@[expose]
def FunctionResult.isRefinedByAsm (source target : MemoryState × Array RuntimeValue) : Prop :=
  source.1 ⊒ target.1 ∧ RuntimeValue.arrayIsRefinedByAsm source.1 target.1 source.2 target.2

/-! ## Assembly mode is weaker -/

/--
Ordinary refinement implies refinement in assembly mode, as long as the two
states agree on where their objects are. Assembly mode only ever admits more
targets, so a proof in the ordinary relation carries over.
-/
theorem RuntimeValue.isRefinedByAsm_of_isRefinedBy {source target : MemoryState}
    (hLayout : source.SameLayout target) {v v' : RuntimeValue} (h : v ⊒ v') :
    RuntimeValue.isRefinedByAsm source target v v' := by
  match v, v' with
  | .addr .poison, _ => trivial
  | .addr (.val p), .addr (.val q) =>
    have : p = q := by simpa [RuntimeValue.isRefinedBy] using h
    simp [RuntimeValue.isRefinedByAsm, this, hLayout.address]
  | .addr (.val _), .addr .poison => simp [RuntimeValue.isRefinedBy] at h
  | .addr (.val _), .reg _ => simp [RuntimeValue.isRefinedBy] at h
  | .int _ _, _ | .byte _ _, _ | .float _ _, _ | .reg _, _ | .felt _ _, _ => exact h

/--
A pointer is refined, in assembly mode, by the pointer that its address
decodes to. This is the step the branch lowering needs: a pointer cast to a
register and back is a pointer to the same address, which is all assembly mode
asks of it.
-/
theorem RuntimeValue.isRefinedByAsm_decode_address (mem : MemoryState) (p : Pointer) :
    RuntimeValue.isRefinedByAsm mem mem (.addr (.val p))
      (.addr (.val (mem.decode (mem.address p)))) := by
  simp only [isRefinedByAsm, mem.address_decode]

/--
A pointer is refined, in assembly mode, by the register holding its address.
-/
theorem RuntimeValue.isRefinedByAsm_reg_address (mem : MemoryState) (p : Pointer) :
    RuntimeValue.isRefinedByAsm mem mem (.addr (.val p)) (.reg ⟨(mem.address p).toBitVec⟩) :=
  rfl

end Veir
