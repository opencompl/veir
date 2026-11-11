module

import all Veir.Passes.Legalization.Validity.Common
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Byte.Basic
import all Veir.Data.LLVM.Ptr.Basic
import all Veir.Data.Casting
import all Veir.Data.Refinement
import all Veir.Interpreter.Memory
import all Init.Data.ByteArray.Extra
import all Veir.Data.Pointer.Basic

/-!
# Local lemmas for the byte, count and `alloca` translations

The local lemmas for the patterns of `llvm-to-gmir` that relate a byte to the integer of its bits,
or a count to its resized form. The patterns match the condition each lemma needs:

| Pattern | Lemma | Condition, and where it is checked |
|---|---|---|
| the counts | `resizeCount_self` | the result has the operand's type (`lowerCount`) |
| byte `trunc` | `byte_trunc_frozen` | no `nsw`/`nuw`, which the translation drops |
| byte/integer `bitcast` | `byte_toInt_frozen` | a nonzero width (`isByteIntBitcast`) |
| integer/byte round trip | `freezeByteWith_fromInt` | a nonzero width (`isIntToByteRoundTrip`) |
| byte `shl`, byte `lshr` | `byte_shl_frozen`, `byte_lshr_frozen` | the byte is not entirely poison |
| static `alloca` | `ptrFromInt_toInt` | the stack object has the size of the `alloca` |
| `load` | `llvmLoad_i8` … `llvmLoad_i64`, `llvmLoad_ptr` | an `i8`/`i16`/`i32`/`i64` or pointer (`loadMemOperand?`) |

The last two are not used: whether a byte is entirely poison is a property of the value, which no
matcher can check, and the static `alloca` computes the size of its stack object from the IR
(`MatchProg.inspectOperation`), which `Pattern.Valid` quantifies over.
-/

namespace Veir.LLVMToGMIR.CTreeProofs

open Data

/-- A count resized to the width it has is unchanged. -/
private theorem resizeCount_self {w : Nat} (c : LLVM.Int w) : resizeCount w c = c := by
  simp only [resizeCount, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  split <;> rfl

/-- The integer a byte casts to when the poison bits of `b` are frozen to `bits`: poison if every
bit of `b` is (see `Builtin.byteToIntCTree`). With `bits = 0`, it is `LLVM.Byte.toFrozenInt b`. -/
def freezeByteWith {w : Nat} (b : LLVM.Byte w) (bits : BitVec w) : LLVM.Int w :=
  if b.poison = BitVec.allOnes w then .poison else .val (b.val ||| (b.poison &&& bits))

/-- An integer cast to a byte and back is unchanged, at a nonzero width, whatever bits the cast
back chooses. -/
private theorem freezeByteWith_fromInt {w : Nat} (h : 0 < w) (x : LLVM.Int w) (bits : BitVec w) :
    freezeByteWith (LLVM.Byte.fromInt x) bits = x := by
  cases x <;> simp [freezeByteWith, LLVM.Byte.fromInt, LLVM.Int.isPoison] <;> grind

/-- `llvm.trunc` of a byte, through the integer of its bits, without the flags that LLVM ignores on
bytes, whatever bits the cast to the integer chooses. -/
private theorem byte_trunc_frozen {w w' : Nat} (h : w > w') (b : LLVM.Byte w) (bits : BitVec w) :
    LLVM.Byte.isRefinedBy (b.trunc w')
      (LLVM.Byte.fromInt ((freezeByteWith b bits).trunc w' false false h)) := by
  simp only [LLVM.Byte.isRefinedBy, LLVM.Byte.fromInt, freezeByteWith, BitVec.ofNat_eq_ofNat]
  veir_bv_normalize
  split
  · case _ h =>
    ext k hk
    simp [h]
    omega
  · case _ h =>
    ext k hk
    simp
    by_cases hp : b.poison.getLsbD k <;> simp [hp]

private theorem shiftAmount_val {w : Nat} (y : BitVec w) :
    shiftAmount w (.val y) = if y.toNat < w then .val y else .val (BitVec.allOnes w) := by
  simp only [shiftAmount]
  split <;> simp [BitVec.ofNat_toNat, BitVec.setWidth_eq]

private theorem not_ge_of_lt {w : Nat} {y : BitVec w} (h : y.toNat < w) : ¬ y ≥ (w : BitVec w) := by
  rw [ge_iff_le, BitVec.le_def, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt Nat.lt_two_pow_self]
  omega

private theorem ge_of_not_lt {w : Nat} {y : BitVec w} (h : ¬ y.toNat < w) : y ≥ (w : BitVec w) := by
  rw [ge_iff_le, BitVec.le_def, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt Nat.lt_two_pow_self]
  omega

private theorem id_pure {α : Type} (x : α) : (pure x : Id α) = x := rfl

/-- Closes the bitwise goals left by the byte shift cases. -/
local macro "byte_shift_tac" y:ident : tactic => `(tactic| (
  all_goals try simp_all [id_pure, LLVM.Byte.allPoison, LLVM.Int.isPoison]
  all_goals (ext k hk; try simp_all)
  all_goals (by_cases hlt : k < ($y).toNat <;> simp [hlt])))

/-- The frozen integer of a byte that is not entirely poison is its bits. -/
private theorem toFrozenInt_of_ne {w : Nat} {b : LLVM.Byte w} (hb : b.poison ≠ BitVec.allOnes w) :
    _root_.LLVM.Byte.toFrozenInt b = .val b.val := by
  simp [_root_.LLVM.Byte.toFrozenInt, hb]

/-- `llvm.shl` of a byte that is not entirely poison, through the integer of its bits. -/
private theorem byte_shl_frozen {w : Nat} (b : LLVM.Byte w) (y : LLVM.Int w) (nuw : Bool)
    (hb : b.poison ≠ BitVec.allOnes w) :
    LLVM.Byte.isRefinedBy (b.shl y nuw)
      (LLVM.Byte.fromInt ((_root_.LLVM.Byte.toFrozenInt b).shl (shiftAmount w y) false nuw)) := by
  rw [toFrozenInt_of_ne hb]
  cases y with
  | poison =>
    simp only [LLVM.Byte.shl, Id.run]
    exact LLVM.Byte.allPoison_isRefinedBy _
  | val y =>
    rw [shiftAmount_val]
    by_cases hy : y.toNat < w
    · simp only [hy, ite_true]
      cases nuw <;>
        simp [LLVM.Byte.shl, LLVM.Int.shl, Id.run, LLVM.Byte.fromInt] <;>
        (try split) <;> (try split) <;> (try split) <;>
        byte_shift_tac y
    · simp only [LLVM.Byte.shl, Id.run, ge_of_not_lt hy, ite_true]
      exact LLVM.Byte.allPoison_isRefinedBy _

/-- `llvm.lshr` of a byte that is not entirely poison, through the integer of its bits. -/
private theorem byte_lshr_frozen {w : Nat} (b : LLVM.Byte w) (y : LLVM.Int w) (exact : Bool)
    (hb : b.poison ≠ BitVec.allOnes w) :
    LLVM.Byte.isRefinedBy (b.lshr y exact)
      (LLVM.Byte.fromInt ((_root_.LLVM.Byte.toFrozenInt b).lshr (shiftAmount w y) exact)) := by
  rw [toFrozenInt_of_ne hb]
  cases y with
  | poison =>
    simp only [LLVM.Byte.lshr, LLVM.Int.isPoison, Bool.true_or, ite_true]
    exact LLVM.Byte.allPoison_isRefinedBy _
  | val y =>
    rw [shiftAmount_val]
    by_cases hy : y.toNat < w
    · simp only [hy, ite_true]
      cases exact <;>
        simp [LLVM.Byte.lshr, LLVM.Int.lshr, Id.run, LLVM.Byte.fromInt,
          LLVM.Int.isPoison, LLVM.Int.getValueD] <;>
        (try split) <;> (try split) <;> (try split) <;>
        byte_shift_tac y
    · simp only [LLVM.Byte.lshr, LLVM.Int.getValueD, ge_of_not_lt hy, decide_true, Bool.or_true,
        ite_true]
      exact LLVM.Byte.allPoison_isRefinedBy _

/-- `llvm.bitcast` of a byte to an integer, at a nonzero width: freezing the poison bits, to any
`bits`, refines the integer, which is poison if any bit is. -/
private theorem byte_toInt_frozen {w : Nat} (hw : 0 < w) (b : LLVM.Byte w) (bits : BitVec w) :
    _root_.isRefinedBy b.toInt (freezeByteWith b bits) := by
  simp only [LLVM.Byte.toInt, freezeByteWith]
  split <;> split
  · rename_i h h'
    rw [h] at h'
    have := congrArg BitVec.toNat h'
    simp [BitVec.toNat_allOnes] at this
    have := Nat.one_lt_two_pow (n := w) (by omega)
    omega
  all_goals first | exact isRefinedBy_refl _ | exact poison_isRefinedBy _ | simp_all

/-- The pointer cast back from the address of an allocation refines it: it is the allocation's
pointer without its provenance. -/
theorem ptrFromInt_toInt (mem : MemoryState) (p : Pointer) :
    LLVM.Ptr.isRefinedBy (.val p) (mem.ptrFromInt (LLVM.Ptr.toInt (.val p))) := by
  simp only [LLVM.Ptr.isRefinedBy, MemoryState.ptrFromInt, LLVM.Ptr.toInt, MemoryState.decode,
    UInt64.ofBitVec_toBitVec, Pointer.isRefinedBy_iff]

/-! ## Loads

`llvm.load` of an `i8`, `i16`, `i32` or `i64` reads the same value as `g_load`: both are poison
when any loaded bit is, and read the bytes little-endian (`MemoryState.llvmLoad` vs
`MemoryState.intLoad`). The proofs unfold both loads to the memory bytes at the address, with
`ByteArray.toBitVecLE_eq_foldr` and the lemmas below for `hasPoison` and `toUInt64LE!`. -/

/-- The loop of `hasPoison` finds a nonzero byte among the last `i`. -/
private theorem forIn_loop_poison (as : ByteArray) (i : Nat) (h : i ≤ as.size) :
    ByteArray.forIn.loop (m := Interp) as
        (fun b s => if b ≠ 0 then pure (.done true) else pure (.yield s)) i h false
      = pure ((as.data.toList.drop (as.size - i)).any (· != 0)) := by
  induction i with
  | zero =>
    simp [ByteArray.forIn.loop, List.drop_of_length_le]
  | succ i ih =>
    rw [ByteArray.forIn.loop]
    have hlt : as.size - 1 - i < as.data.toList.length := by simp; omega
    rw [show as.size - (i + 1) = as.size - 1 - i by omega, List.drop_eq_getElem_cons hlt,
      show as.size - 1 - i + 1 = as.size - i by omega]
    simp only [List.any_cons, Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data]
    split
    · simp_all
    · simp only [pure_bind]
      rw [ih]
      simp_all

/-- `hasPoison` reads the poison bytes and tests whether any is nonzero. -/
private theorem hasPoison_eq (mem : MemoryState) (p : Pointer) (n : UInt64) :
    mem.hasPoison p n = (mem.loadPoison p n >>= fun pb => pure (pb.data.toList.any (· != 0))) := by
  simp only [MemoryState.hasPoison, forIn, ByteArray.forIn]
  congr 1
  funext pb
  rw [forIn_loop_poison]
  simp

/-- An access check succeeds or is undefined behavior. -/
private theorem checkAccess_cases (mem : MemoryState) (p : Pointer) (s : UInt64) :
    mem.checkAccess p s = .ok () ∨ mem.checkAccess p s = .ub none := by
  simp only [MemoryState.checkAccess]
  by_cases h0 : s = 0
  · simp [h0]
  · by_cases hany : mem.objects.any (·.holds p.address s.toNat)
    · simp [h0, hany]
    · simp [h0, hany]

/-- The little-endian value of two bytes is zero iff both are. -/
private theorem foldr_eq_zero_iff_2 (g : Fin 2 → UInt8) :
    (List.ofFn g).foldr (fun (b : UInt8) (acc : BitVec 16) => acc <<< 8 ||| b.toBitVec.setWidth 16) 0
        = 0 ↔
      (List.ofFn g).any (· != 0) = false := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil, List.any_cons,
    List.any_nil, Bool.or_false, Bool.or_eq_false_iff, bne_eq_false_iff_eq, ← UInt8.toBitVec_inj]
  simp only [Fin.succ_zero_eq_one, UInt8.toBitVec_ofNat]
  bv_decide

/-- The little-endian value of four bytes is zero iff all are. -/
private theorem foldr_eq_zero_iff_4 (g : Fin 4 → UInt8) :
    (List.ofFn g).foldr (fun (b : UInt8) (acc : BitVec 32) => acc <<< 8 ||| b.toBitVec.setWidth 32) 0
        = 0 ↔
      (List.ofFn g).any (· != 0) = false := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil, List.any_cons,
    List.any_nil, Bool.or_false, Bool.or_eq_false_iff, bne_eq_false_iff_eq, ← UInt8.toBitVec_inj]
  simp only [UInt8.toBitVec_ofNat]
  bv_decide

/-- The little-endian value of eight bytes is zero iff all are. -/
private theorem foldr_eq_zero_iff_8 (g : Fin 8 → UInt8) :
    (List.ofFn g).foldr (fun (b : UInt8) (acc : BitVec 64) => acc <<< 8 ||| b.toBitVec.setWidth 64) 0
        = 0 ↔
      (List.ofFn g).any (· != 0) = false := by
  simp only [List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil, List.any_cons,
    List.any_nil, Bool.or_false, Bool.or_eq_false_iff, bne_eq_false_iff_eq, ← UInt8.toBitVec_inj]
  simp only [UInt8.toBitVec_ofNat]
  bv_decide

/-- `toUInt64LE!` reads the same little-endian value as `toBitVecLE`. -/
private theorem toUInt64LE_eq_foldr (g : Fin 8 → UInt8) :
    BitVec.ofNat 64 (ByteArray.mk (Array.ofFn g)).toUInt64LE!.toNat =
      (List.ofFn g).foldr (fun (b : UInt8) (acc : BitVec 64) => acc <<< 8 ||| b.toBitVec.setWidth 64)
        0 := by
  have hs : (ByteArray.mk (Array.ofFn g)).size = 8 := by simp only [ByteArray.size, Array.size_ofFn]
  simp only [ByteArray.toUInt64LE!, ByteArray.get!, hs, beq_self_eq_true, ite_true, List.ofFn_succ,
    List.ofFn_zero, List.foldr_cons, List.foldr_nil]
  simp only [getElem!_pos, Array.size_ofFn, Array.getElem_ofFn, Nat.reduceLT, Fin.reduceSucc,
    Fin.isValue, Fin.zero_eta,
    show (⟨1, by decide⟩ : Fin 8) = 1 from rfl, show (⟨2, by decide⟩ : Fin 8) = 2 from rfl,
    show (⟨3, by decide⟩ : Fin 8) = 3 from rfl,
    show (⟨4, by decide⟩ : Fin 8) = 4 from rfl, show (⟨5, by decide⟩ : Fin 8) = 5 from rfl,
    show (⟨6, by decide⟩ : Fin 8) = 6 from rfl, show (⟨7, by decide⟩ : Fin 8) = 7 from rfl]
  rw [← UInt64.toNat_toBitVec, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt8.toBitVec_toUInt64,
    UInt64.toBitVec_ofNat]
  bv_decide

/-- `llvm.load` of an `i8` is the `g_load` of 8 bits. -/
private theorem llvmLoad_i8 (mem : MemoryState) (p : Pointer) (s : IntegerType.Signedness)
    (type : TypeAttr) (h : type.val = .integerType ⟨8, s⟩) :
    mem.llvmLoad p type = (mem.intLoad p 8 >>= fun v => pure (RuntimeValue.int 8 v)) := by
  simp only [MemoryState.llvmLoad, MemoryState.intLoad, MemoryState.loadByte, h]
  clear h s type
  by_cases hp : p = Pointer.null
  · simp [hp]
  have e1 : (8 / 8).toUInt64 = (1 : UInt64) := rfl
  simp only [hp, ite_false, MemoryState.load, MemoryState.loadPoison, hasPoison_eq, e1,
    Nat.reduceMod, ne_eq, not_true_eq_false]
  rcases checkAccess_cases mem p 1 with hacc | hacc <;>
    simp only [hacc, Interp.bind_ok, Interp.bind_ub, Interp.pure_eq]
  clear hacc
  rw [getElem!_pos _ _ (by simp only [ByteArray.size, Array.size_ofFn]; decide)]
  simp [ByteArray.toBitVecLE_eq_foldr, List.ofFn_succ, LLVM.Byte.toInt,
    ByteArray.getElem_eq_getElem_data]
  by_cases hz : (mem.byte p.address).poison = 0
  · simp [hz]
    bv_decide
  · have hz' : (mem.byte p.address).poison.toBitVec ≠ 0#8 := fun e => hz (UInt8.toBitVec_inj.mp e)
    simp [hz, hz']

/-- `llvm.load` of an `i16` is the `g_load` of 16 bits. -/
private theorem llvmLoad_i16 (mem : MemoryState) (p : Pointer) (s : IntegerType.Signedness)
    (type : TypeAttr) (h : type.val = .integerType ⟨16, s⟩) :
    mem.llvmLoad p type = (mem.intLoad p 16 >>= fun v => pure (RuntimeValue.int 16 v)) := by
  simp only [MemoryState.llvmLoad, MemoryState.intLoad, MemoryState.loadByte, h]
  clear h s type
  by_cases hp : p = Pointer.null
  · simp [hp]
  have e1 : (16 / 8).toUInt64 = (2 : UInt64) := rfl
  simp only [hp, ite_false, MemoryState.load, MemoryState.loadPoison, hasPoison_eq, e1,
    Nat.reduceMod, ne_eq, not_true_eq_false]
  rcases checkAccess_cases mem p 2 with hacc | hacc <;>
    simp only [hacc, Interp.bind_ok, Interp.bind_ub, Interp.pure_eq]
  clear hacc
  simp only [ByteArray.toBitVecLE_eq_foldr, Array.toList_ofFn, LLVM.Byte.toInt]
  have key := foldr_eq_zero_iff_2 (fun i => (mem.byte (p.address + (i : Nat).toUInt64)).poison)
  split <;> rename_i hany <;> simp_all
  all_goals bv_decide

/-- `llvm.load` of an `i32` is the `g_load` of 32 bits. -/
private theorem llvmLoad_i32 (mem : MemoryState) (p : Pointer) (s : IntegerType.Signedness)
    (type : TypeAttr) (h : type.val = .integerType ⟨32, s⟩) :
    mem.llvmLoad p type = (mem.intLoad p 32 >>= fun v => pure (RuntimeValue.int 32 v)) := by
  simp only [MemoryState.llvmLoad, MemoryState.intLoad, MemoryState.loadByte, h]
  clear h s type
  by_cases hp : p = Pointer.null
  · simp [hp]
  have e1 : (32 / 8).toUInt64 = (4 : UInt64) := rfl
  simp only [hp, ite_false, MemoryState.load, MemoryState.loadPoison, hasPoison_eq, e1,
    Nat.reduceMod, ne_eq, not_true_eq_false]
  rcases checkAccess_cases mem p 4 with hacc | hacc <;>
    simp only [hacc, Interp.bind_ok, Interp.bind_ub, Interp.pure_eq]
  clear hacc
  simp only [ByteArray.toBitVecLE_eq_foldr, Array.toList_ofFn, LLVM.Byte.toInt]
  have key := foldr_eq_zero_iff_4 (fun i => (mem.byte (p.address + (i : Nat).toUInt64)).poison)
  split <;> rename_i hany <;> simp_all
  all_goals bv_decide

/-- `llvm.load` of an `i64` is the `g_load` of 64 bits. -/
private theorem llvmLoad_i64 (mem : MemoryState) (p : Pointer) (s : IntegerType.Signedness)
    (type : TypeAttr) (h : type.val = .integerType ⟨64, s⟩) :
    mem.llvmLoad p type = (mem.intLoad p 64 >>= fun v => pure (RuntimeValue.int 64 v)) := by
  simp only [MemoryState.llvmLoad, MemoryState.intLoad, MemoryState.loadByte, h]
  clear h s type
  by_cases hp : p = Pointer.null
  · simp [hp]
  have e1 : (64 / 8).toUInt64 = (8 : UInt64) := rfl
  simp only [hp, ite_false, MemoryState.load, MemoryState.loadPoison, hasPoison_eq, e1,
    Nat.reduceMod, ne_eq, not_true_eq_false]
  rcases checkAccess_cases mem p 8 with hacc | hacc <;>
    simp only [hacc, Interp.bind_ok, Interp.bind_ub, Interp.pure_eq]
  clear hacc
  simp only [ByteArray.toBitVecLE_eq_foldr, Array.toList_ofFn, LLVM.Byte.toInt, toUInt64LE_eq_foldr]
  have key := foldr_eq_zero_iff_8 (fun i => (mem.byte (p.address + (i : Nat).toUInt64)).poison)
  split <;> rename_i hany <;> simp_all
  all_goals bv_decide

/-- `llvm.load` of a pointer, which `g_load` reads the same way. -/
private theorem llvmLoad_ptr (mem : MemoryState) (p : Pointer) (type : TypeAttr)
    (pt : LLVM.PointerType) (h : type.val = .llvmPointerType pt) :
    mem.llvmLoad p type =
      (if p = .null then .ub none
        else mem.loadByte p 64 >>= fun b => pure (.addr (mem.ptrOfByte b))) := by
  simp only [MemoryState.llvmLoad, h]

/-- A load from the null pointer is undefined behavior. -/
private theorem llvmLoad_null (mem : MemoryState) (type : TypeAttr) :
    mem.llvmLoad .null type = .ub none := by
  simp [MemoryState.llvmLoad]

/-- An alignment of `2 ^ 64` or more only accepts the null pointer. -/
private theorem checkAlignment_of_le {p : Pointer} {A : Nat} (hA : 2 ^ 64 ≤ A) :
    p.checkAlignment A = if p = .null then .ok () else .ub none := by
  simp only [Data.Pointer.checkAlignment]
  have hlt : p.address.toNat < A := by
    have := UInt64.toNat_lt_size p.address
    simp only [UInt64.size] at this
    omega
  rw [Nat.mod_eq_of_lt hlt]
  rcases p with ⟨a⟩
  by_cases ha : a = 0
  · subst ha
    simp [Data.Pointer.null]
  · have hne : a.toNat ≠ 0 := by
      intro h0
      apply ha
      exact UInt64.toNat_inj.mp (by rw [UInt64.toNat_zero]; exact h0)
    simp [Data.Pointer.null, show A ≠ 0 by omega, hne, ha]

end Veir.LLVMToGMIR.CTreeProofs
