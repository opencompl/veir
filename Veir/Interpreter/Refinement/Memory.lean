module

public import Veir.Interpreter.Refinement.Lemmas

import all Veir.Interpreter.Memory
import all Veir.ForLean
import all Veir.Data.LLVM.Byte.Basic
import all Veir.Data.LLVM.Ptr.Basic
import Veir.Data.LLVM.Ptr.Lemmas
import all Std.Data.ByteSlice
import Veir.Data.Casting
import Veir.Data.LLVM.Byte.Refinement

public section

/-!
# Memory operations under memory refinement

Loads and stores are monotone under memory refinement: a load from refined memory gives a refined
value, and a store of a refined value into refined memory gives refined memory.
-/

/-! ## Byte arrays -/

private theorem ByteArray.mk_getElem! (a : Array UInt8) (k : Nat) (h : k < a.size) :
    (ByteArray.mk a)[k]! = a[k] := by
  rw [getElem!_pos (ByteArray.mk a) k h]; rfl

private theorem ByteArray.extend_getElem! (ba : ByteArray) (n : Nat) (v : UInt8) (i : Nat)
    (h₁ : ba.size ≤ i) (h₂ : i < ba.size + n) : (ba.extend n v)[i]! = v := by
  induction n with
  | zero => omega
  | succ n ih =>
    have : ba.extend (n + 1) v = (ba.extend n v).push v := by
      simp [ByteArray.extend, Nat.fold_succ]
    rw [this, ByteArray.getElem!_push]
    split
    · rfl
    · exact ih (by simp at *; omega)

private theorem ByteArray.replicate_getElem! (n : Nat) (v : UInt8) (i : Nat) (h : i < n) :
    (ByteArray.replicate n v)[i]! = v :=
  ByteArray.extend_getElem! _ _ _ _ (by simp) (by simpa using h)

private theorem UInt16.toByteArrayLE_size (u : UInt16) : u.toByteArrayLE.size = 2 := rfl

private theorem UInt32.toByteArrayLE_size (u : UInt32) : u.toByteArrayLE.size = 4 := rfl

private theorem ByteArray.toByteSlice_size (ba : ByteArray) : ba.toByteSlice.size = ba.size := by
  simp [ByteArray.toByteSlice, ByteSlice.size, ByteSlice.start, ByteSlice.stop]

private theorem ByteArray.toByteSlice_getElem (ba : ByteArray) (i : Nat)
    (h : i < ba.toByteSlice.size) :
    ba.toByteSlice[i] = ba[i]'(ByteArray.toByteSlice_size ba ▸ h) := by
  simp [ByteArray.toByteSlice, GetElem.getElem, ByteSlice.get, ByteSlice.start,
    ByteSlice.byteArray]

/--
  The loop of `ByteSlice.foldr` in `ByteArray.toBitVecLE`: with `s.size - i` bytes left, bit `j`
  comes from the byte `j / 8` if it is left, and from the accumulator otherwise.
-/
private theorem ByteSlice.foldrM_loop_getLsbD (s : ByteSlice) (w : Nat) (i : Nat)
    (acc : BitVec w) (j : Nat) (hj : j < w) (hi : i ≤ s.size) :
    ((ByteSlice.foldrM.loop (m := Id)
        (fun (b : UInt8) (acc : BitVec w) =>
          (pure (acc <<< 8 ||| BitVec.setWidth w b.toBitVec) : Id (BitVec w)))
        s i acc).run).getLsbD j =
      if h : j / 8 < s.size - i then s[j / 8].toBitVec.getLsbD (j % 8)
      else acc.getLsbD (j - 8 * (s.size - i)) := by
  induction i, acc using ByteSlice.foldrM.loop.induct s with
  | case1 i acc hlt ih =>
    unfold ByteSlice.foldrM.loop
    simp only [hlt, dite_true]
    have ih' := ih (acc <<< 8 ||| BitVec.setWidth w s[s.size - 1 - i].toBitVec) (by omega)
    simp only [Id.run, bind, pure] at ih' ⊢
    rw [ih']
    by_cases h1 : j / 8 < s.size - (i + 1)
    · have h2 : j / 8 < s.size - i := by omega
      simp [h1, h2]
    · by_cases h2 : j / 8 < s.size - i
      · have h3 : j / 8 = s.size - 1 - i := by omega
        have h4 : j - 8 * (s.size - (i + 1)) = j % 8 := by omega
        simp only [h1, h2, dite_false, dite_true, h4, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
          BitVec.getLsbD_setWidth]
        have h5 : j % 8 < w := by omega
        have h6 : j % 8 < 8 := Nat.mod_lt _ (by omega)
        simp [h5, h6, ← h3]
      · have h4 : j - 8 * (s.size - (i + 1)) - 8 = j - 8 * (s.size - i) := by omega
        simp only [h1, h2, dite_false, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
          BitVec.getLsbD_setWidth]
        have h5 : j - 8 * (s.size - (i + 1)) < w := by omega
        have h6 : ¬ j - 8 * (s.size - (i + 1)) < 8 := by omega
        simp [h5, h6, h4, BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_lt h6)]
  | case2 i acc hge =>
    unfold ByteSlice.foldrM.loop
    have : s.size - i = 0 := by omega
    simp [hge, this]

/-- Bit `j` of the little-endian bits of a byte array is bit `j % 8` of byte `j / 8`. -/
theorem ByteArray.getLsbD_toBitVecLE (ba : ByteArray) (w j : Nat) :
    (ba.toBitVecLE w).getLsbD j =
      (decide (j < w) &&
        if h : j / 8 < ba.size then ba[j / 8].toBitVec.getLsbD (j % 8) else false) := by
  by_cases hj : j < w
  · unfold ByteArray.toBitVecLE ByteSlice.foldr ByteSlice.foldrM
    rw [ByteSlice.foldrM_loop_getLsbD _ _ _ _ _ hj (Nat.zero_le _)]
    simp only [Nat.sub_zero, ByteArray.toByteSlice_size, hj, decide_true, Bool.true_and]
    split
    · rw [ByteArray.toByteSlice_getElem]
    · simp
  · simp [hj, BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_lt hj)]

private theorem List.any_congr_mem {α : Type _} {l : List α} {p q : α → Bool}
    (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l <;> simp_all

private theorem foldl_attach_congr {α β : Type _} {l : List α} {f : β → {a // a ∈ l} → β}
    {g : β → α → β} (h : ∀ b a (ha : a ∈ l), f b ⟨a, ha⟩ = g b a) (init : β) :
    l.attach.foldl f init = l.foldl g init := by
  rw [← List.foldl_attach (l := l) (f := g)]
  have : f = fun b x => g b x.1 := by
    funext b ⟨a, ha⟩; exact h b a ha
  subst this; rfl

open Veir.Data

namespace Veir

/-!
## Operations that only read the objects

Refined memories have the same objects, so these agree on them.
-/

theorem MemoryState.decode_eq_of_objects {mem mem' : MemoryState}
    (_h : mem.objects = mem'.objects) : mem.decode = mem'.decode := by
  funext addr
  simp [MemoryState.decode]

theorem MemoryState.ptrFromInt_eq_of_objects {mem mem' : MemoryState}
    (h : mem.objects = mem'.objects) : mem.ptrFromInt = mem'.ptrFromInt := by
  funext i
  cases i <;> simp [MemoryState.ptrFromInt, decode_eq_of_objects h]

theorem MemoryState.ptrOfByte_eq_of_objects {mem mem' : MemoryState}
    (h : mem.objects = mem'.objects) : mem.ptrOfByte = mem'.ptrOfByte := by
  funext b
  simp [MemoryState.ptrOfByte, decode_eq_of_objects h]

theorem MemoryState.checkAccess_eq_of_objects {mem mem' : MemoryState}
    (h : mem.objects = mem'.objects) : mem.checkAccess = mem'.checkAccess := by
  funext p size
  simp [MemoryState.checkAccess, h]

/-- Refined memories have the same globals. -/
theorem MemoryState.pointerToGlobal_eq_of_isRefinedBy {mem mem' : MemoryState}
    (h : mem ⊒ mem') : mem.pointerToGlobal = mem'.pointerToGlobal := by
  funext symbol
  simp [MemoryState.pointerToGlobal, h.objects_eq, (MemoryState.isRefinedBy_def.mp h).2]

/-! ## Refinement of interpretations -/

/-! ## Refinement of memory bytes -/

private theorem UInt8.toBitVec_0xff_getLsbD {m : Nat} (hm : m < 8) :
    (0xff : UInt8).toBitVec.getLsbD m = true := by
  have : (0xff : UInt8).toBitVec = BitVec.allOnes 8 := rfl
  rw [this, BitVec.getLsbD_allOnes]; simp [hm]

theorem MemoryByte.getLsbD_of_isRefinedBy {b b' : MemoryByte} (h : b ⊒ b') {m : Nat}
    (hm : m < 8) :
    b.poison.toBitVec.getLsbD m = true ∨
      (b.value.toBitVec.getLsbD m = b'.value.toBitVec.getLsbD m ∧
        b'.poison.toBitVec.getLsbD m = false) := by
  have h' := congrArg (fun x : UInt8 => x.toBitVec.getLsbD m) h
  simp only [UInt8.toBitVec_or, UInt8.toBitVec_and, UInt8.toBitVec_xor, UInt8.toBitVec_not,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, hm,
    decide_true, Bool.true_and, UInt8.toBitVec_0xff_getLsbD hm] at h'
  rcases Bool.eq_false_or_eq_true (b.poison.toBitVec.getLsbD m) with h₁ | h₁ <;>
  rcases Bool.eq_false_or_eq_true (b.value.toBitVec.getLsbD m) with h₂ | h₂ <;>
  rcases Bool.eq_false_or_eq_true (b'.value.toBitVec.getLsbD m) with h₃ | h₃ <;>
  rcases Bool.eq_false_or_eq_true (b'.poison.toBitVec.getLsbD m) with h₄ | h₄ <;>
  simp_all

theorem MemoryByte.isRefinedBy_of_getLsbD {b b' : MemoryByte}
    (h : ∀ m < 8, b.poison.toBitVec.getLsbD m = true ∨
      (b.value.toBitVec.getLsbD m = b'.value.toBitVec.getLsbD m ∧
        b'.poison.toBitVec.getLsbD m = false)) : b ⊒ b' := by
  apply UInt8.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro m hm
  simp only [UInt8.toBitVec_or, UInt8.toBitVec_and, UInt8.toBitVec_xor, UInt8.toBitVec_not,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not, hm,
    decide_true, Bool.true_and, UInt8.toBitVec_0xff_getLsbD hm]
  rcases h m hm with h₁ | ⟨h₂, h₃⟩
  · simp [h₁]
  · simp [h₂, h₃]

theorem Data.LLVM.Byte.getLsbD_of_isRefinedBy {w : Nat} {b b' : LLVM.Byte w} (h : b ⊒ b')
    {m : Nat} (hm : m < w) :
    b.poison.getLsbD m = true ∨
      (b.val.getLsbD m = b'.val.getLsbD m ∧ b'.poison.getLsbD m = false) := by
  have h' := congrArg (·.getLsbD m) h
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor,
    BitVec.getLsbD_not, BitVec.getLsbD_allOnes, hm, decide_true, Bool.true_and] at h'
  rcases Bool.eq_false_or_eq_true (b.poison.getLsbD m) with h₁ | h₁ <;>
  rcases Bool.eq_false_or_eq_true (b.val.getLsbD m) with h₂ | h₂ <;>
  rcases Bool.eq_false_or_eq_true (b'.val.getLsbD m) with h₃ | h₃ <;>
  rcases Bool.eq_false_or_eq_true (b'.poison.getLsbD m) with h₄ | h₄ <;>
  simp_all

theorem MemoryByte.isRefinedBy_ofBitVec {b b' : LLVM.Byte 8} (hb : b ⊒ b') :
    (⟨UInt8.ofBitVec b.val, UInt8.ofBitVec b.poison⟩ : MemoryByte) ⊒
      ⟨UInt8.ofBitVec b'.val, UInt8.ofBitVec b'.poison⟩ :=
  MemoryByte.isRefinedBy_of_getLsbD fun _ hm => LLVM.Byte.getLsbD_of_isRefinedBy hb hm

theorem MemoryByte.eq_of_isRefinedBy {b b' : MemoryByte} (h : b ⊒ b') (hp : b.poison = 0) :
    b' = b := by
  have hbit : ∀ m < 8, b.value.toBitVec.getLsbD m = b'.value.toBitVec.getLsbD m ∧
      b'.poison.toBitVec.getLsbD m = false := by
    intro m hm
    rcases MemoryByte.getLsbD_of_isRefinedBy h hm with h₁ | h₁
    · simp [hp] at h₁
    · exact h₁
  rcases b with ⟨v, p⟩
  rcases b' with ⟨v', p'⟩
  simp only at hp hbit
  subst hp
  simp only [MemoryByte.mk.injEq]
  constructor
  · apply UInt8.toBitVec_inj.mp
    exact BitVec.eq_of_getLsbD_eq fun m hm => (hbit m hm).1.symm
  · apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq fun m hm => ?_
    simp [(hbit m hm).2]

theorem MemoryByte.isRefinedBy_of_poison_eq {b : MemoryByte} (hp : b.poison = 0xff)
    (b' : MemoryByte) : b ⊒ b' :=
  MemoryByte.isRefinedBy_of_getLsbD fun _ hm => .inl (hp ▸ UInt8.toBitVec_0xff_getLsbD hm)

/-- The bits of a pointer refine as the pointer does. -/
theorem Data.LLVM.Ptr.toByte_isRefinedBy {q q' : LLVM.Ptr} (hq : q ⊒ q') :
    q.toByte ⊒ q'.toByte := by
  cases q with
  | poison =>
    simp only [LLVM.Ptr.toByte, LLVM.Byte.isRefinedBy, LLVM.Byte.allPoison, BitVec.allOnes_or]
  | val a =>
    cases q' with
    | poison => simp at hq
    | val a' =>
      simp only [LLVM.Ptr.isRefinedBy, Pointer.isRefinedBy_iff] at hq
      subst hq
      exact LLVM.Byte.isRefinedBy_refl _

/-! ## Stores -/

/-- The bytes of memory after a store of `val` with the poison bits `poison` at `p`. -/
private def storeBytes (bytes : Std.ExtHashMap UInt64 MemoryByte) (p : Pointer)
    (val poison : ByteArray) : Std.ExtHashMap UInt64 MemoryByte :=
  (List.range val.size).foldl
    (fun b i => b.insert (p.address + i.toUInt64) ⟨val[i]!, poison[i]!⟩) bytes

private theorem MemoryState.store_eq (mem : MemoryState) (p : Pointer) (val poison : ByteArray)
    (h : poison.size = val.size) :
    mem.store p val poison h = (do
      mem.checkAccess p val.size.toUInt64
      return { mem with bytes := storeBytes mem.bytes p val poison }) := by
  unfold MemoryState.store
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', List.forIn'_pure_yield_eq_foldl,
    Std.Legacy.Range.size, Nat.add_one_sub_one, Nat.div_one, Nat.sub_zero]
  unfold storeBytes
  rw [List.range_eq_range', foldl_attach_congr (g := fun b i =>
    b.insert (p.address + i.toUInt64) ⟨val[i]!, poison[i]!⟩)]
  · rfl
  · intro b a ha
    have : a < val.size := by simp at ha; omega
    simp [getElem!_pos val a this, getElem!_pos poison a (h ▸ this)]

/-- Byte maps that refine bytewise, an absent byte being poison. -/
private def BytesRefine (b b' : Std.ExtHashMap UInt64 MemoryByte) : Prop :=
  ∀ addr, b.getD addr .poisoned ⊒ b'.getD addr .poisoned

private theorem foldl_bytesRefine (l : List Nat) (f f' : Nat → UInt64 × MemoryByte)
    (hf : ∀ i ∈ l, (f i).1 = (f' i).1 ∧ (f i).2 ⊒ (f' i).2)
    (b b' : Std.ExtHashMap UInt64 MemoryByte) (h : BytesRefine b b') :
    BytesRefine (l.foldl (fun b i => b.insert (f i).1 (f i).2) b)
      (l.foldl (fun b i => b.insert (f' i).1 (f' i).2) b') := by
  induction l generalizing b b' with
  | nil => exact h
  | cons i l ih =>
    simp only [List.foldl_cons]
    apply ih (fun j hj => hf j (List.mem_cons_of_mem _ hj))
    intro addr
    obtain ⟨h1, h2⟩ := hf i (List.mem_cons_self ..)
    simp only [Std.ExtHashMap.getD_insert, h1]
    split
    · exact h2
    · exact h addr

/--
  A store of bytes into refined memory gives refined memory, when the stored bytes and their
  poison bits refine bytewise.
-/
theorem MemoryState.store_isRefinedBy {mem mem' : MemoryState}
    (h : mem ⊒ mem') (p : Pointer) {val poison val' poison' : ByteArray}
    (hp : poison.size = val.size) (hp' : poison'.size = val'.size)
    (hsize : val.size = val'.size)
    (hb : ∀ i < val.size,
      (⟨val[i]!, poison[i]!⟩ : MemoryByte) ⊒ ⟨val'[i]!, poison'[i]!⟩) :
    Interp.isRefinedBy MemoryState.isRefinedBy
      (mem.store p val poison hp) (mem'.store p val' poison' hp') := by
  rw [MemoryState.store_eq, MemoryState.store_eq, ← hsize,
    ← checkAccess_eq_of_objects h.objects_eq]
  cases mem.checkAccess p val.size.toUInt64 with
  | fail => simp
  | ub => simp
  | ok =>
    simp only [Interp.bind_ok, Interp.pure_eq, Interp.isRefinedBy_ok_target_iff, Interp.ok.injEq,
      exists_eq_left']
    obtain ⟨⟨hobj, hbytes⟩, hglobals⟩ := MemoryState.isRefinedBy_def.mp h
    refine MemoryState.isRefinedBy_def.mpr ⟨⟨hobj, ?_⟩, hglobals⟩
    intro addr
    simp only [MemoryState.byte, storeBytes, ← hsize]
    exact foldl_bytesRefine _ (fun i => (p.address + i.toUInt64, ⟨val[i]!, poison[i]!⟩))
      (fun i => (p.address + i.toUInt64, ⟨val'[i]!, poison'[i]!⟩))
      (fun i hi => ⟨rfl, hb i (List.mem_range.mp hi)⟩) _ _ hbytes addr

/-- A store of bytes that are all poison is refined by any store of as many bytes. -/
theorem MemoryState.store_poison_isRefinedBy {mem mem' : MemoryState}
    (h : mem ⊒ mem') (p : Pointer) {val poison val' poison' : ByteArray}
    (hp : poison.size = val.size) (hp' : poison'.size = val'.size)
    (hsize : val.size = val'.size) (hpoison : ∀ i < val.size, poison[i]! = 0xff) :
    Interp.isRefinedBy MemoryState.isRefinedBy
      (mem.store p val poison hp) (mem'.store p val' poison' hp') :=
  store_isRefinedBy h p hp hp' hsize fun i hi =>
    MemoryByte.isRefinedBy_of_poison_eq (hpoison i hi) _

/-- A store of the same bytes into refined memory gives refined memory. -/
theorem MemoryState.store_same_isRefinedBy {mem mem' : MemoryState}
    (h : mem ⊒ mem') (p : Pointer) (val poison : ByteArray)
    (hp : poison.size = val.size) :
    Interp.isRefinedBy MemoryState.isRefinedBy
      (mem.store p val poison hp) (mem'.store p val poison hp) :=
  store_isRefinedBy h p hp hp rfl fun _ _ => MemoryByte.isRefinedBy_refl _

/-- Poisoning `n` bytes is refined by any store of `n` bytes. -/
theorem MemoryState.empoison_isRefinedBy {mem mem' : MemoryState}
    (h : mem ⊒ mem') (p : Pointer) (n : Nat) {val' poison' : ByteArray}
    (hp' : poison'.size = val'.size) (hsize : val'.size = n) :
    Interp.isRefinedBy MemoryState.isRefinedBy
      (mem.empoison p n) (mem'.store p val' poison' hp') := by
  unfold MemoryState.empoison
  apply store_poison_isRefinedBy h p _ hp' (by simp [hsize])
  intro i hi
  exact ByteArray.replicate_getElem! _ _ _ (by simpa using hi)

/-- A store of the 64 bits of refined bytes into refined memory gives refined memory. -/
theorem MemoryState.storeByte64_isRefinedBy {mem mem' : MemoryState}
    (h : mem ⊒ mem') (p : Pointer) {b b' : LLVM.Byte 64} (hb : b ⊒ b') :
    Interp.isRefinedBy MemoryState.isRefinedBy
      (mem.storeByte64 p b) (mem'.storeByte64 p b') := by
  unfold MemoryState.storeByte64
  apply store_isRefinedBy h p _ _ (by simp)
  intro i hi
  simp only [UInt64.toByteArrayLE_size] at hi
  apply MemoryByte.isRefinedBy_of_getLsbD
  intro m hm
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  all_goals simp [UInt64.toByteArrayLE, ByteArray.mk_getElem!, hm]
  all_goals exact LLVM.Byte.getLsbD_of_isRefinedBy hb (by omega)

/-- A store of a refined value into refined memory gives refined memory. -/
theorem MemoryState.llvmStore_isRefinedBy {mem mem' : MemoryState}
    (h : mem ⊒ mem') (p : Pointer) {v v' : RuntimeValue} (hv : v ⊒ v') :
    Interp.isRefinedBy MemoryState.isRefinedBy
      (mem.llvmStore p v) (mem'.llvmStore p v') := by
  unfold MemoryState.llvmStore
  by_cases hnull : p = .null
  · simp [hnull]
  simp only [hnull, ite_false]
  split
  case h_1 n x =>
    obtain ⟨x', rfl, -⟩ := RuntimeValue.int_of_isRefinedBy hv
    cases x with
    | val a =>
      rw [RuntimeValue.int_val_isRefinedBy_iff.mp hv]
      dsimp only [MemoryState.storeBits]
      exact store_same_isRefinedBy h p _ _ _
    | poison =>
      cases x'
      · dsimp only [MemoryState.storeBits]
        exact empoison_isRefinedBy h p _ _ (by show Array.size _ = _; rw [Array.size_ofFn])
      · exact empoison_isRefinedBy h p _ _ (by simp)
  case h_2 b =>
    obtain ⟨b', rfl, hb⟩ := RuntimeValue.byte_of_isRefinedBy hv
    apply store_isRefinedBy h p _ _ (by simp)
    intro i hi
    obtain rfl : i = 0 := by simpa using hi
    exact MemoryByte.isRefinedBy_ofBitVec hb
  case h_3 b =>
    obtain ⟨b', rfl, hb⟩ := RuntimeValue.byte_of_isRefinedBy hv
    exact storeByte64_isRefinedBy h p hb
  case h_4 q =>
    obtain ⟨q', rfl, -⟩ := RuntimeValue.addr_isRefinedBy_iff.mp hv
    exact storeByte64_isRefinedBy h p (Data.LLVM.Ptr.toByte_isRefinedBy hv)
  case h_5 => simp [liftM]

/-! ## Loads -/

/-- The loop of `MemoryState.hasPoison` over the last `i` poison bytes. -/
private theorem forIn_loop_hasPoison (as : ByteArray) (i : Nat) (h : i ≤ as.size) (acc : Bool) :
    ByteArray.forIn.loop (m := Interp) as
      (fun b s => if b ≠ 0 then pure (ForInStep.done true) else pure (ForInStep.yield s))
      i h acc =
      .ok (acc || (List.range' (as.size - i) i).any fun k => as[k]! != 0) := by
  induction i generalizing acc with
  | zero =>
    unfold ByteArray.forIn.loop
    simp
  | succ i ih =>
    simp only [Interp.pure_eq] at ih
    unfold ByteArray.forIn.loop
    have hr : List.range' (as.size - (i + 1)) (i + 1) =
        (as.size - 1 - i) :: List.range' (as.size - i) i := by
      rw [List.range'_succ, show as.size - (i + 1) + 1 = as.size - i by omega,
        show as.size - (i + 1) = as.size - 1 - i by omega]
    have hget : as[as.size - 1 - i]! = as[as.size - 1 - i] := getElem!_pos _ _ _
    by_cases hb : as[as.size - 1 - i] ≠ 0
    · simp [hb, hr, hget]
    · simp only [hb, ite_false, Interp.pure_eq, Interp.bind_ok]
      rw [ih]
      have hb' : as[as.size - 1 - i] = 0 := by simpa using hb
      simp [hr, hget, hb']

/-- Whether any of the `n` bytes at `p` has a poison bit. -/
private theorem MemoryState.hasPoison_eq (mem : MemoryState) (p : Pointer) (n : UInt64) :
    mem.hasPoison p n = (do
      mem.checkAccess p n
      return (List.range n.toNat).any fun k =>
        (mem.byte (p.address + k.toUInt64)).poison != 0) := by
  unfold MemoryState.hasPoison MemoryState.loadPoison
  simp only [forIn, ByteArray.forIn, bind_assoc, pure_bind]
  rw [Interp.bind_eq_bind_iff]
  intro _ _
  rw [forIn_loop_hasPoison]
  simp only [List.range_eq_range', Interp.pure_eq]
  congr 1
  have hs : (ByteArray.mk (Array.ofFn fun (i : Fin n.toNat) =>
      (mem.byte (p.address + i.val.toUInt64)).poison)).size = n.toNat := by
    simp [ByteArray.size]
  rw [hs]
  simp only [Nat.sub_self, Bool.false_or, Interp.bind_ok]
  congr 1
  apply List.any_congr_mem
  intro k hk
  simp only [List.mem_range'_1] at hk
  rw [ByteArray.mk_getElem! _ _ (by simpa using hk.2)]
  simp

private theorem getLsbD_toBitVecLE_ofFn {n : Nat} (f : Fin n → UInt8) (w j : Nat) :
    ((ByteArray.mk (Array.ofFn f)).toBitVecLE w).getLsbD j =
      (decide (j < w) &&
        if h : j / 8 < n then (f ⟨j / 8, h⟩).toBitVec.getLsbD (j % 8) else false) := by
  rw [ByteArray.getLsbD_toBitVecLE]
  have hs : (ByteArray.mk (Array.ofFn f)).size = n := by simp [ByteArray.size]
  by_cases h : j / 8 < n
  · have h' : j / 8 < (ByteArray.mk (Array.ofFn f)).size := by rw [hs]; exact h
    simp only [h, h', dite_true]
    rw [show (ByteArray.mk (Array.ofFn f))[j / 8] = (Array.ofFn f)[j / 8]'(by simpa using h)
      from rfl, Array.getElem_ofFn]
  · have h' : ¬ j / 8 < (ByteArray.mk (Array.ofFn f)).size := by rw [hs]; exact h
    simp only [h, h', dite_false]

/-- A bit of a loaded byte, with its value bit masked by its poison bit, refines. -/
private theorem loadedBit_of_isRefinedBy {b b' : MemoryByte} (h : b ⊒ b') {m : Nat}
    (hm : m < 8) :
    (b.poison.toBitVec.getLsbD m ||
      (b.value.toBitVec.getLsbD m && !b.poison.toBitVec.getLsbD m ^^
          !(b'.value.toBitVec.getLsbD m && !b'.poison.toBitVec.getLsbD m)) &&
        !b'.poison.toBitVec.getLsbD m) = true := by
  rcases MemoryByte.getLsbD_of_isRefinedBy h hm with h₁ | ⟨h₂, h₃⟩
  · simp [h₁]
  · rw [h₂, h₃]
    cases b'.value.toBitVec.getLsbD m <;> cases b.poison.toBitVec.getLsbD m <;> rfl

/-- A load of `w` bits, poison bits included, from refined memory gives refined bits. -/
theorem MemoryState.loadByte_isRefinedBy {mem mem' : MemoryState}
    (h : mem ⊒ mem') (p : Pointer) (w : Nat) :
    Interp.isRefinedBy (fun (b b' : LLVM.Byte w) => b ⊒ b')
      (mem.loadByte p w) (mem'.loadByte p w) := by
  unfold MemoryState.loadByte MemoryState.loadPoison MemoryState.load
  split
  · simp
  rw [← checkAccess_eq_of_objects h.objects_eq]
  simp only [bind_assoc, pure_bind]
  refine Interp.isRefinedBy_bind_same fun _ => Interp.isRefinedBy_bind_same fun _ => ?_
  · simp only [Interp.pure_eq, Interp.isRefinedBy_ok_target_iff, Interp.ok.injEq,
      exists_eq_left', LLVM.Byte.isRefinedBy]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_not,
      BitVec.getLsbD_allOnes, getLsbD_toBitVecLE_ofFn, hj, decide_true, Bool.true_and]
    split
    · exact loadedBit_of_isRefinedBy (h.byte_refines _) (Nat.mod_lt _ (by omega))
    · simp

/-- A load of the bytes of `w` bits succeeds where a load of the bits with their poison does. -/
theorem MemoryState.load_eq_ok_of_loadByte_eq_ok {mem : MemoryState} {p : Pointer} {w : Nat}
    {b : LLVM.Byte w} (h : mem.loadByte p w = .ok b) :
    ∃ ba, mem.load p (w / 8).toUInt64 = .ok ba := by
  unfold MemoryState.loadByte MemoryState.loadPoison at h
  unfold MemoryState.load
  split at h
  · simp at h
  cases hc : mem.checkAccess p (w / 8).toUInt64 <;> simp_all

/--
  An integer load from refined memory: poison if any byte is, otherwise the bytes are those of
  the refinement.
-/
private theorem MemoryState.intLoad_isRefinedBy {mem mem' : MemoryState}
    (h : mem ⊒ mem') (p : Pointer) (n : UInt64) (w : Nat)
    (F : ByteArray → LLVM.Int w) :
    Interp.isRefinedBy (fun (v v' : RuntimeValue) => v ⊒ v')
      (do
        let ba ← mem.load p n
        let c ← mem.hasPoison p n
        if c = true then pure (RuntimeValue.int w .poison) else pure (RuntimeValue.int w (F ba)))
      (do
        let ba ← mem'.load p n
        let c ← mem'.hasPoison p n
        if c = true then pure (RuntimeValue.int w .poison)
        else pure (RuntimeValue.int w (F ba))) := by
  simp only [MemoryState.load, MemoryState.hasPoison_eq, ← checkAccess_eq_of_objects h.objects_eq,
    bind_assoc, pure_bind]
  refine Interp.isRefinedBy_bind_same fun _ => Interp.isRefinedBy_bind_same fun _ => ?_
  by_cases hc : ((List.range n.toNat).any fun k =>
      (mem.byte (p.address + k.toUInt64)).poison != 0) = true
  · simp only [hc, ite_true]
    split
    all_goals exact (Interp.isRefinedBy_ok_target_iff.mpr
      ⟨_, rfl, RuntimeValue.int_isRefinedBy_iff.mpr ⟨_, rfl, .inl rfl⟩⟩)
  · have heq : ∀ k < n.toNat,
        mem'.byte (p.address + k.toUInt64) = mem.byte (p.address + k.toUInt64) := by
      intro k hk
      apply MemoryByte.eq_of_isRefinedBy (h.byte_refines _)
      simp only [Bool.not_eq_true, List.any_eq_false, List.mem_range, bne_iff_ne, ne_eq,
        Decidable.not_not] at hc
      exact hc k hk
    have hany :
        ((List.range n.toNat).any fun k => (mem'.byte (p.address + k.toUInt64)).poison != 0) =
          ((List.range n.toNat).any fun k => (mem.byte (p.address + k.toUInt64)).poison != 0) :=
      List.any_congr_mem fun k hk => by rw [heq k (List.mem_range.mp hk)]
    have harr :
        (Array.ofFn fun (i : Fin n.toNat) => (mem'.byte (p.address + i.val.toUInt64)).value) =
          Array.ofFn fun (i : Fin n.toNat) => (mem.byte (p.address + i.val.toUInt64)).value := by
      congr 1; funext i; rw [heq i.val i.isLt]
    rw [hany, harr]
    split
    all_goals exact
      Interp.isRefinedBy_ok_target_iff.mpr ⟨_, rfl, RuntimeValue.isRefinedBy_refl _⟩

/--
  An integer load of any width from refined memory: poison if a bit of the value is, otherwise
  the bits are those of the refinement.
-/
private theorem MemoryState.anyIntLoad_isRefinedBy {mem mem' : MemoryState}
    (h : mem ⊒ mem') (p : Pointer) (n : Nat) :
    Interp.isRefinedBy (fun (v v' : RuntimeValue) => v ⊒ v')
      (do
        let b ← mem.loadByte p (8 * ((n + 7) / 8))
        if b.poison.truncate n ≠ 0 then pure (RuntimeValue.int n .poison)
        else pure (RuntimeValue.int n (.val (b.val.truncate n))))
      (do
        let b ← mem'.loadByte p (8 * ((n + 7) / 8))
        if b.poison.truncate n ≠ 0 then pure (RuntimeValue.int n .poison)
        else pure (RuntimeValue.int n (.val (b.val.truncate n)))) := by
  refine Interp.isRefinedBy_bind (loadByte_isRefinedBy h p _) fun b b' hb => ?_
  by_cases hp : b.poison.truncate n = 0
  · -- No bit of the value is poison, so the refinement has the same bits.
    have hbit : ∀ m < n, b'.poison.getLsbD m = false ∧ b'.val.getLsbD m = b.val.getLsbD m := by
      intro m hm
      have hpm := congrArg (·.getLsbD m) hp
      simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, hm, decide_true,
        Bool.true_and] at hpm
      rcases LLVM.Byte.getLsbD_of_isRefinedBy hb (m := m) (by omega) with h₁ | ⟨h₁, h₂⟩
      · simp_all
      · exact ⟨h₂, h₁.symm⟩
    have hp' : b'.poison.truncate n = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro m hm; simp [hm, (hbit m hm).1]
    have hv' : b'.val.truncate n = b.val.truncate n := by
      apply BitVec.eq_of_getLsbD_eq; intro m hm; simp [hm, (hbit m hm).2]
    simp only [hp, hp', hv', ne_eq, not_true_eq_false, ite_false]
    exact Interp.isRefinedBy_ok_target_iff.mpr ⟨_, rfl, RuntimeValue.isRefinedBy_refl _⟩
  · simp only [hp, ne_eq, not_false_eq_true, ite_true]
    split
    all_goals exact (Interp.isRefinedBy_ok_target_iff.mpr
      ⟨_, rfl, RuntimeValue.int_isRefinedBy_iff.mpr ⟨_, rfl, .inl rfl⟩⟩)

/--
  A load from refined memory gives a refined value. An integer or pointer load is poison as soon
  as one bit of the source is, and otherwise reads the same bytes in the refinement.
-/
theorem MemoryState.llvmLoad_isRefinedBy {mem mem' : MemoryState}
    (h : mem ⊒ mem') (p : Pointer) (type : TypeAttr) :
    Interp.isRefinedBy (fun (v v' : RuntimeValue) => v ⊒ v')
      (mem.llvmLoad p type) (mem'.llvmLoad p type) := by
  unfold MemoryState.llvmLoad
  by_cases hnull : p = .null
  · simp [hnull]
  simp only [hnull, ite_false]
  split
  case h_1 | h_2 | h_3 | h_4 => exact intLoad_isRefinedBy h p _ _ _
  case h_5 => exact anyIntLoad_isRefinedBy h p _
  case h_6 | h_7 =>
    refine Interp.isRefinedBy_bind (loadByte_isRefinedBy h p _) fun b b' hb => ?_
    exact Interp.isRefinedBy_ok_target_iff.mpr ⟨_, rfl, ⟨rfl, by simpa using hb⟩⟩
  case h_8 =>
    refine Interp.isRefinedBy_bind (loadByte_isRefinedBy h p _) fun b b' hb => ?_
    refine Interp.isRefinedBy_ok_target_iff.mpr ⟨_, rfl, ?_⟩
    by_cases hp : b.poison = 0#64
    · rw [LLVM.Byte.eq_of_isRefinedBy_of_poison_eq_zero hb hp, ptrOfByte_eq_of_objects h.objects_eq]
      exact RuntimeValue.isRefinedBy_refl _
    · simp [MemoryState.ptrOfByte, hp, RuntimeValue.isRefinedBy]
  case h_9 => simp [liftM]

/-! ## Refined pointers -/

/-- Loading through a refined pointer from refined memory gives a refined value. -/
theorem MemoryState.llvmLoad_isRefinedBy_of_refines {mem mem' : MemoryState} (h : mem ⊒ mem')
    {p p' : Pointer} (hp : p ⊒ p') (type : TypeAttr) :
    Interp.isRefinedBy (fun (v v' : RuntimeValue) => v ⊒ v')
      (mem.llvmLoad p type) (mem'.llvmLoad p' type) := by
  rw [Pointer.isRefinedBy_iff.mp hp]
  exact MemoryState.llvmLoad_isRefinedBy h p type

/-- Storing a refined value through a refined pointer into refined memory gives refined memory. -/
theorem MemoryState.llvmStore_isRefinedBy_of_refines {mem mem' : MemoryState} (h : mem ⊒ mem')
    {p p' : Pointer} (hp : p ⊒ p') {v v' : RuntimeValue} (hv : v ⊒ v') :
    Interp.isRefinedBy MemoryState.isRefinedBy (mem.llvmStore p v) (mem'.llvmStore p' v') := by
  rw [Pointer.isRefinedBy_iff.mp hp]
  exact MemoryState.llvmStore_isRefinedBy h p hv

/--
An integer load through a refined pointer from refined memory gives a refined integer: the source
is poison if any loaded bit is, and otherwise loads the bits of the target.
-/
theorem MemoryState.intLoad_isRefinedBy_of_refines {mem mem' : MemoryState} (h : mem ⊒ mem')
    {p p' : Pointer} (hp : p ⊒ p') (w : Nat) :
    Interp.isRefinedBy (fun (x x' : LLVM.Int w) => _root_.isRefinedBy x x')
      (mem.intLoad p w) (mem'.intLoad p' w) := by
  rw [Pointer.isRefinedBy_iff.mp hp]
  unfold MemoryState.intLoad
  split
  · simp
  · exact Interp.isRefinedBy_bind (MemoryState.loadByte_isRefinedBy h p w) fun _ _ hb =>
      Interp.isRefinedBy_ok_target_iff.mpr ⟨_, rfl, LLVM.Byte.toInt_isRefinedBy hb⟩

end Veir

end
