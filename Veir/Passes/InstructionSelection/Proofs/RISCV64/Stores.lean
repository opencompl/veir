module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Interpreter.Memory
import all Veir.Data.Pointer.Basic
import all Veir.ForLean
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.MemoryLemmas
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.MemoryAddressLemmas
import all Std.Data.ExtHashMap.Lemmas
import all Init.Data.Range.Polymorphic.Lemmas

/-! Instruction-selection validity proofs: Stores to indexed, constant-offset, and register addresses. -/

namespace Veir

open Puddle
open _root_.CTree

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree Riscv.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

private theorem memory_insert_refines (source target : MemoryState) (addr : UInt64)
    (sb tb : MemoryByte) (hm : source ⊒ target) (hb : sb ⊒ tb) :
    ({ source with bytes := source.bytes.insert addr sb } : MemoryState) ⊒
      ({ target with bytes := target.bytes.insert addr tb } : MemoryState) := by
  refine ⟨⟨hm.1.1, ?_⟩, hm.2⟩
  intro key
  simp only [MemoryState.byte, Std.ExtHashMap.getD_insert]
  split <;> first | exact hb | exact hm.1.2 key

private theorem rawStore1 (memory : MemoryState) (p : Data.Pointer) (v poison : UInt8) :
    memory.store p ⟨#[v]⟩ ⟨#[poison]⟩ (by simp [ByteArray.size]) =
      (do memory.checkAccess p 1
          return {memory with bytes := memory.bytes.insert p.address ⟨v, poison⟩}) := by
  unfold MemoryState.store
  simp only [ByteArray.size, Array.size_push, Array.size_empty]
  simp [Std.Rco.forIn'_eq_if, ByteArray.getElem_eq_getElem_data]

private theorem rawStore_refines (memory : MemoryState) (p : Data.Pointer)
    (n : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8)
    (sv sp tv tp : ByteArray) (hsv : sv.size = n) (hsp : sp.size = n)
    (htv : tv.size = n) (htp : tp.size = n)
    (hb : ∀ i (hi : i < n), (⟨sv[i]'(hsv ▸ hi), sp[i]'(hsp ▸ hi)⟩ : MemoryByte) ⊒
      (⟨tv[i]'(htv ▸ hi), tp[i]'(htp ▸ hi)⟩ : MemoryByte)) :
    Interp.isRefinedBy MemoryState.isRefinedBy
      (memory.store p sv sp (hsp.trans hsv.symm))
      (memory.store p tv tp (htp.trans htv.symm)) := by
  unfold MemoryState.store
  simp only [hsv, htv]
  cases hc : memory.checkAccess p n.toUInt64 <;>
    simp only [hc, Interp.bind_ok, Interp.bind_ub, Interp.bind_fail, Interp.isRefinedBy]
  rcases hn with rfl | rfl | rfl | rfl
  all_goals simp +zetaDelta [hsv, htv, Std.Rco.forIn'_eq_if]
  all_goals simp -failIfUnchanged only [List.range'_succ, List.range'_zero, List.forIn'_cons,
    List.forIn'_nil, Interp.bind_ok, Interp.pure_eq]
  all_goals refine ⟨⟨rfl, ?_⟩, rfl⟩
  all_goals intro key
  all_goals simp only [MemoryState.byte, Std.ExtHashMap.getD_insert]
  all_goals repeat' first
    | split <;> simp_all -failIfUnchanged only [ite_true, ite_false]
    | exact hb _ (by veir_bv_decide)
    | exact MemoryByte.isRefinedBy_refl _

private theorem emptyArray_size (α : Type) : (Array.empty : Array α).size = 0 := rfl
private theorem emptyCapacity_size (α : Type) (n : Nat) :
    (Array.emptyWithCapacity n : Array α).size = 0 := rfl

theorem llvmStoreInt_refines (memory : MemoryState) (p : Data.Pointer)
    (n : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8)
    (x : Data.LLVM.Int (8 * n)) (v : BitVec 64)
    (hx : x ⊒ Data.LLVM.Int.val (v.setWidth (8 * n))) :
    Interp.isRefinedBy MemoryState.isRefinedBy
      (memory.llvmStore p (.int (8 * n) x))
      (memory.store p ((UInt64.ofBitVec v).toByteArrayLE.extract 0 n)) := by
  unfold MemoryState.llvmStore
  split
  · simp [Interp.isRefinedBy]
  cases x
  case val bits =>
    have he : bits = v.setWidth (8 * n) := by simpa [isRefinedBy] using hx
    subst bits
    rcases hn with rfl | rfl | rfl | rfl
    · unfold MemoryState.storeBits
      apply rawStore_refines memory p 1 (.inl rfl)
      all_goals try rfl
      all_goals try simp only [ByteArray.replicate_size, ByteArray.size_extract, UInt64.toByteArrayLE_size,
        Nat.sub_zero]
      all_goals try rfl
      all_goals intro i hi
      all_goals have hc : i = 0 := by omega
      all_goals rcases hc with rfl
      all_goals simp only [ByteArray.getElem_extract]
      all_goals simp [ByteArray.replicate, ByteArray.extend, ByteArray.emptyWithCapacity,
        Nat.fold_succ, Nat.fold_zero, Nat.min_def, ByteArray.getElem_eq_getElem_data,
        Array.size_empty, Array.size_push, Array.getElem_push, UInt64.toByteArrayLE, MemoryByte.isRefinedBy]
      all_goals simp -failIfUnchanged [getElem!, Array.size_empty]
      all_goals veir_bv_normalize
      all_goals simp -failIfUnchanged only [emptyArray_size, emptyCapacity_size, Array.size_empty, Array.size_push, Nat.lt_irrefl, Nat.not_lt_zero, ↓reduceDIte, ↓reduceIte]
      all_goals veir_bv_decide
    · unfold MemoryState.storeBits
      apply rawStore_refines memory p 2 (.inr (.inl rfl))
      all_goals try rfl
      all_goals try simp only [ByteArray.replicate_size, ByteArray.size_extract, UInt64.toByteArrayLE_size,
        Nat.sub_zero]
      all_goals try rfl
      all_goals intro i hi
      all_goals have hc : i = 0 ∨ i = 1 := by omega
      all_goals rcases hc with rfl | rfl
      all_goals simp only [ByteArray.getElem_extract]
      all_goals simp [ByteArray.replicate, ByteArray.extend, ByteArray.emptyWithCapacity,
        Nat.fold_succ, Nat.fold_zero, Nat.min_def, ByteArray.getElem_eq_getElem_data,
        Array.size_empty, Array.size_push, Array.getElem_push, UInt64.toByteArrayLE, MemoryByte.isRefinedBy]
      all_goals simp -failIfUnchanged [getElem!, Array.size_empty]
      all_goals veir_bv_normalize
      all_goals simp -failIfUnchanged only [emptyArray_size, emptyCapacity_size, Array.size_empty, Array.size_push, Nat.lt_irrefl, Nat.not_lt_zero, ↓reduceDIte, ↓reduceIte]
      all_goals veir_bv_decide
    · unfold MemoryState.storeBits
      apply rawStore_refines memory p 4 (.inr (.inr (.inl rfl)))
      all_goals try rfl
      all_goals try simp only [ByteArray.replicate_size, ByteArray.size_extract, UInt64.toByteArrayLE_size,
        Nat.sub_zero]
      all_goals try rfl
      all_goals intro i hi
      all_goals have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      all_goals rcases hc with rfl | rfl | rfl | rfl
      all_goals simp only [ByteArray.getElem_extract]
      all_goals simp [ByteArray.replicate, ByteArray.extend, ByteArray.emptyWithCapacity,
        Nat.fold_succ, Nat.fold_zero, Nat.min_def, ByteArray.getElem_eq_getElem_data,
        Array.size_empty, Array.size_push, Array.getElem_push, UInt64.toByteArrayLE, MemoryByte.isRefinedBy]
      all_goals simp -failIfUnchanged [getElem!, Array.size_empty]
      all_goals veir_bv_normalize
      all_goals simp -failIfUnchanged only [emptyArray_size, emptyCapacity_size, Array.size_empty, Array.size_push, Nat.lt_irrefl, Nat.not_lt_zero, ↓reduceDIte, ↓reduceIte]
      all_goals veir_bv_decide
    · unfold MemoryState.storeBits
      apply rawStore_refines memory p 8 (.inr (.inr (.inr rfl)))
      all_goals try rfl
      all_goals try simp only [ByteArray.replicate_size, ByteArray.size_extract, UInt64.toByteArrayLE_size,
        Nat.sub_zero]
      all_goals try rfl
      all_goals intro i hi
      all_goals have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      all_goals rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [ByteArray.getElem_extract]
      all_goals simp [ByteArray.replicate, ByteArray.extend, ByteArray.emptyWithCapacity,
        Nat.fold_succ, Nat.fold_zero, Nat.min_def, ByteArray.getElem_eq_getElem_data,
        Array.size_empty, Array.size_push, Array.getElem_push, UInt64.toByteArrayLE, MemoryByte.isRefinedBy]
      all_goals simp -failIfUnchanged [getElem!, Array.size_empty]
      all_goals veir_bv_normalize
      all_goals simp -failIfUnchanged only [emptyArray_size, emptyCapacity_size, Array.size_empty, Array.size_push, Nat.lt_irrefl, Nat.not_lt_zero, ↓reduceDIte, ↓reduceIte]
      all_goals veir_bv_decide
  case poison =>
    rcases hn with rfl | rfl | rfl | rfl
    · unfold MemoryState.empoison
      apply rawStore_refines memory p 1 (.inl rfl)
      all_goals try rfl
      all_goals try simp only [ByteArray.replicate_size, ByteArray.size_extract, UInt64.toByteArrayLE_size,
        Nat.sub_zero]
      all_goals try rfl
      all_goals intro i hi
      all_goals have hc : i = 0 := by omega
      all_goals rcases hc with rfl
      all_goals simp only [ByteArray.getElem_extract]
      all_goals simp [ByteArray.replicate, ByteArray.extend, ByteArray.emptyWithCapacity,
        Nat.fold_succ, Nat.fold_zero, Nat.min_def, ByteArray.getElem_eq_getElem_data,
        Array.size_empty, Array.size_push, Array.getElem_push, UInt64.toByteArrayLE, MemoryByte.isRefinedBy]
      all_goals simp -failIfUnchanged [getElem!, Array.size_empty]
      all_goals veir_bv_normalize
      all_goals simp -failIfUnchanged only [emptyArray_size, emptyCapacity_size, Array.size_empty, Array.size_push, Nat.lt_irrefl, Nat.not_lt_zero, ↓reduceDIte, ↓reduceIte]
      all_goals veir_bv_decide
    · unfold MemoryState.empoison
      apply rawStore_refines memory p 2 (.inr (.inl rfl))
      all_goals try rfl
      all_goals try simp only [ByteArray.replicate_size, ByteArray.size_extract, UInt64.toByteArrayLE_size,
        Nat.sub_zero]
      all_goals try rfl
      all_goals intro i hi
      all_goals have hc : i = 0 ∨ i = 1 := by omega
      all_goals rcases hc with rfl | rfl
      all_goals simp only [ByteArray.getElem_extract]
      all_goals simp [ByteArray.replicate, ByteArray.extend, ByteArray.emptyWithCapacity,
        Nat.fold_succ, Nat.fold_zero, Nat.min_def, ByteArray.getElem_eq_getElem_data,
        Array.size_empty, Array.size_push, Array.getElem_push, UInt64.toByteArrayLE, MemoryByte.isRefinedBy]
      all_goals simp -failIfUnchanged [getElem!, Array.size_empty]
      all_goals veir_bv_normalize
      all_goals simp -failIfUnchanged only [emptyArray_size, emptyCapacity_size, Array.size_empty, Array.size_push, Nat.lt_irrefl, Nat.not_lt_zero, ↓reduceDIte, ↓reduceIte]
      all_goals veir_bv_decide
    · unfold MemoryState.empoison
      apply rawStore_refines memory p 4 (.inr (.inr (.inl rfl)))
      all_goals try rfl
      all_goals try simp only [ByteArray.replicate_size, ByteArray.size_extract, UInt64.toByteArrayLE_size,
        Nat.sub_zero]
      all_goals try rfl
      all_goals intro i hi
      all_goals have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      all_goals rcases hc with rfl | rfl | rfl | rfl
      all_goals simp only [ByteArray.getElem_extract]
      all_goals simp [ByteArray.replicate, ByteArray.extend, ByteArray.emptyWithCapacity,
        Nat.fold_succ, Nat.fold_zero, Nat.min_def, ByteArray.getElem_eq_getElem_data,
        Array.size_empty, Array.size_push, Array.getElem_push, UInt64.toByteArrayLE, MemoryByte.isRefinedBy]
      all_goals simp -failIfUnchanged [getElem!, Array.size_empty]
      all_goals veir_bv_normalize
      all_goals simp -failIfUnchanged only [emptyArray_size, emptyCapacity_size, Array.size_empty, Array.size_push, Nat.lt_irrefl, Nat.not_lt_zero, ↓reduceDIte, ↓reduceIte]
      all_goals veir_bv_decide
    · unfold MemoryState.empoison
      apply rawStore_refines memory p 8 (.inr (.inr (.inr rfl)))
      all_goals try rfl
      all_goals try simp only [ByteArray.replicate_size, ByteArray.size_extract, UInt64.toByteArrayLE_size,
        Nat.sub_zero]
      all_goals try rfl
      all_goals intro i hi
      all_goals have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      all_goals rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [ByteArray.getElem_extract]
      all_goals simp [ByteArray.replicate, ByteArray.extend, ByteArray.emptyWithCapacity,
        Nat.fold_succ, Nat.fold_zero, Nat.min_def, ByteArray.getElem_eq_getElem_data,
        Array.size_empty, Array.size_push, Array.getElem_push, UInt64.toByteArrayLE, MemoryByte.isRefinedBy]
      all_goals simp -failIfUnchanged [getElem!, Array.size_empty]
      all_goals veir_bv_normalize
      all_goals simp -failIfUnchanged only [emptyArray_size, emptyCapacity_size, Array.size_empty, Array.size_push, Nat.lt_irrefl, Nat.not_lt_zero, ↓reduceDIte, ↓reduceIte]
      all_goals veir_bv_decide

private theorem llvmStorePtr_toInt_refines (memory : MemoryState) (p : Data.Pointer)
    (x : Data.LLVM.Ptr) (v : BitVec 64)
    (hx : x.toInt ⊒ Data.LLVM.Int.val v) :
    Interp.isRefinedBy MemoryState.isRefinedBy
      (memory.llvmStore p (.addr x))
      (memory.store p (UInt64.ofBitVec v).toByteArrayLE) := by
  unfold MemoryState.llvmStore
  split
  · simp [Interp.isRefinedBy]
  cases x
  case val q =>
    have he : q.address.toBitVec = v := by simpa [Data.LLVM.Ptr.toInt, isRefinedBy] using hx
    subst v
    unfold MemoryState.storeByte64
    apply rawStore_refines memory p 8 (.inr (.inr (.inr rfl)))
    all_goals try simp only [UInt64.toByteArrayLE_size, ByteArray.replicate_size]
    all_goals intro i hi
    all_goals have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    all_goals rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Data.LLVM.Ptr.toByte, Data.LLVM.Byte.fromUInt64, MemoryByte.isRefinedBy,
      UInt64.toByteArrayLE, ByteArray.replicate, ByteArray.extend, ByteArray.emptyWithCapacity,
      Nat.fold_succ, Nat.fold_zero, ByteArray.getElem_eq_getElem_data, Array.getElem_push,
      emptyArray_size, emptyCapacity_size]
    all_goals veir_bv_normalize
    all_goals simp -failIfUnchanged only [emptyArray_size, emptyCapacity_size, Nat.not_lt_zero, ↓reduceDIte, ↓reduceIte]
    all_goals veir_bv_decide
  case poison =>
    unfold MemoryState.storeByte64
    apply rawStore_refines memory p 8 (.inr (.inr (.inr rfl)))
    all_goals try simp only [UInt64.toByteArrayLE_size, ByteArray.replicate_size]
    all_goals intro i hi
    all_goals have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    all_goals rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [Data.LLVM.Ptr.toByte, Data.LLVM.Byte.allPoison, MemoryByte.isRefinedBy,
      UInt64.toByteArrayLE, ByteArray.replicate, ByteArray.extend, ByteArray.emptyWithCapacity,
      Nat.fold_succ, Nat.fold_zero, ByteArray.getElem_eq_getElem_data, Array.getElem_push,
      emptyArray_size, emptyCapacity_size]
    all_goals veir_bv_normalize
    all_goals simp -failIfUnchanged only [emptyArray_size, emptyCapacity_size, Nat.not_lt_zero, ↓reduceDIte, ↓reduceIte]
    all_goals change (255 : UInt8) ||| _ = 255
    all_goals veir_bv_decide

theorem llvmStorePtr_refines (memory : MemoryState) (p : Data.Pointer)
    (x : Data.LLVM.Ptr) (v : BitVec 64)
    (hx : x ⊒ Data.LLVM.Ptr.val ⟨UInt64.ofBitVec v⟩) :
    Interp.isRefinedBy MemoryState.isRefinedBy
      (memory.llvmStore p (.addr x))
      (memory.store p ((UInt64.ofBitVec v).toByteArrayLE.extract 0 8)) := by
  have hi : x.toInt ⊒ Data.LLVM.Int.val v := by
    cases x with
    | val q =>
      have hq : q = ⟨UInt64.ofBitVec v⟩ := by
        simpa [Data.LLVM.Ptr.isRefinedBy, Data.Pointer.isRefinedBy, eq_comm] using hx
      subst q
      simp [Data.LLVM.Ptr.toInt, isRefinedBy]
    | poison => simp [Data.LLVM.Ptr.toInt, isRefinedBy]
  have he : (UInt64.ofBitVec v).toByteArrayLE.extract 0 8 = (UInt64.ofBitVec v).toByteArrayLE := by
    simpa only [UInt64.toByteArrayLE_size] using (ByteArray.extract_zero_size (b := (UInt64.ofBitVec v).toByteArrayLE))
  simp only [he]
  exact llvmStorePtr_toInt_refines memory p x v hi

end Veir
