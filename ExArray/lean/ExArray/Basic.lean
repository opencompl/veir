module

public import Std.Tactic.BVDecide
meta import Std.Tactic.BVDecide
public import ExArray.Ranges

/-! # Extensible arrays

This file defines the `ExArray` type. It essentially the same as `ByteArray`
except that it has an `extend` function to append many zeroes in one call, and
functions to read and write fixed sized integers.
-/

public section

-- First, some missing theorems about UInt64. May be upstreamed?
@[grind =]
theorem UInt64.add_toNat_lt {a b : UInt64} (h : a.toNat + b.toNat < UInt64.size) :
    ((a + b).toNat = a.toNat + b.toNat) := by
  grind only [UInt64.toNat_add, Nat.mod_eq_of_lt]

theorem Nat_mod_mod_eq_mod_mod_of_two_pow {a b c: Nat} :
    a % 2 ^ b % 2 ^ c = a % 2 ^ c % 2 ^ b := by
  grind only [Nat.pow_dvd_pow, Nat.mod_mod_eq_mod_mod_of_dvd]

-- Upstream?
def _root_.BitVec.ofFn {w : Nat} (f : Fin w → Bool) : BitVec w :=
  BitVec.iunfoldr (fun i _ => ((), f i)) () |>.2

abbrev Int64.maxNatValue : Nat := 2^63 - 1

@[grind =]
theorem Int64.maxNatValue_maxValue : maxValue.toInt.toNat = maxNatValue := by rfl

@[grind =]
theorem Int64.maxNatValue_maxValue_toInt : Int.ofNat maxNatValue = maxValue.toInt := by rfl

/--
An `ExArray` is essentially the same as `ByteArray` except that it has an
`extend` function to append many zeroes in one call, and functions to read and
write fixed sized integers.
-/
structure ExArray where
  data : Array UInt8
  data_fits_in_memory : data.size < Int64.maxNatValue

attribute [local grind! .] ExArray.data_fits_in_memory

attribute [extern "buffed_ex_array_mk"] ExArray.mk
attribute [extern "buffed_ex_array_data"] ExArray.data

namespace ExArray

deriving instance BEq for ExArray

attribute [ext] ExArray

instance : DecidableEq ExArray :=
  fun _ _ => decidable_of_decidable_of_iff ExArray.ext_iff.symm

@[extern "buffed_mk_empty_ex_array"]
def emptyWithCapacity (c : @& Nat) : ExArray :=
  { data := #[], data_fits_in_memory := (by grind) }

abbrev empty : ExArray := emptyWithCapacity 0

instance : EmptyCollection ExArray where
  emptyCollection := ExArray.empty

instance : Inhabited ExArray where
  default := empty

instance : EmptyCollection ExArray where
  emptyCollection := ExArray.empty

@[extern "buffed_ex_array_size"]
def size : (@& ExArray) → Nat
  | ⟨bs, _⟩ => bs.size

@[extern "buffed_ex_array_usize", grind =]
def usize (a: @& ExArray) : UInt64 := a.size.toUInt64

@[simp, grind =]
theorem emptyWithCapacity_size : (emptyWithCapacity n).size = 0 := by rfl

@[simp, grind =]
theorem emptyWithCapacity_usize : (emptyWithCapacity n).usize = 0 := by rfl

@[grind .]
theorem fits_in_memory (a : ExArray) : a.size < Int64.maxNatValue := by
  cases a
  simpa only [size]

@[grind .]
theorem fits_in_memory_uint64 (a : ExArray) : a.size < UInt64.size := by
  cases a
  simp only [size]
  grind

@[grind .]
theorem fits_in_memory_toInt (a : ExArray) : a.size < Int64.maxValue.toInt := by
  cases a
  simp only [size]
  grind

@[grind →]
theorem in_bounds_in_memory (a : ExArray) (i : Nat) :
    (i ≤ a.size) → (i < Int64.maxNatValue) := by
  grind [a.fits_in_memory]

@[simp, grind =]
theorem usize_size_toNat (a : ExArray) :
    a.usize.toNat = a.size := by
  simp only [usize]
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.reducePow, Nat.mod_succ_eq_iff_lt,
    Nat.succ_eq_add_one, Nat.reduceAdd]
  grind [Nat.mod_eq_of_lt, a.fits_in_memory]

@[grind =]
theorem ofNat_size_eq_usize (a : ExArray) : UInt64.ofNat a.size = a.usize := by
  grind

def range (a : ExArray) : CORange := 0...a.size

@[simp, grind =]
theorem range_lower (a : ExArray) : a.range.lower = 0 := by simp [range]

@[simp, grind =]
theorem range_upper (a : ExArray) : a.range.upper = a.size := by simp [range]

@[grind →]
theorem included_range (a : ExArray) (r: CORange) :
    IsIncluded r a.range → r.upper < Int64.maxNatValue := by
  grind

@[extern "buffed_ex_array_uset"]
def uset : (a : ExArray) → (i : UInt64) → UInt8 → (h : i.toNat < a.size := by grind) → ExArray
  | ⟨bs, _⟩, i, v, h => ⟨bs.set i.toNat v (by grind [size]), (by simpa)⟩

@[simp, grind =]
theorem uset_size (a : ExArray) (i : UInt64) (v : UInt8) (h : i.toNat < a.size) :
    (a.uset i v h).size = a.size := by
  unfold uset size
  simp

@[simp, grind =]
theorem uset_range (a : ExArray) (i : UInt64) (v : UInt8) (h : i.toNat < a.size) :
    (a.uset i v h).range = a.range := by
  simp only [range, uset_size]

def get : (a : ExArray) → (i : Nat) → (h : i < a.size := by grind) → UInt8
  | ⟨bs, _⟩, i, h => bs[i]

@[extern "buffed_ex_array_uget"]
def uget : (a : @& ExArray) → (i : UInt64) → (h : i.toNat < a.size := by grind) → UInt8
  | ⟨bs, _⟩, i, h => bs[i.toNat]

@[simp, grind =]
theorem uget_uset_self (a : ExArray) (i : UInt64) (v : UInt8) h h' :
    (a.uset i v h).uget i h' = v := by
  apply Array.getElem_set_self

@[simp, grind =]
theorem uget_uset_ne (a : ExArray) (i j : UInt64) (v : UInt8) h h' :
    i ≠ j → (a.uset i v h).uget j h' = a.uget j := by
  intros hne
  apply Array.getElem_set_ne
  grind [UInt64.toNat_inj]

@[simp, grind =]
theorem uget_uset_split (a : ExArray) (i j : UInt64) (v : UInt8) h h' :
    (a.uset i v h).uget j h' = if j == i then v else a.uget j := by
  grind only [= uget_uset_ne, = uget_uset_self]

@[ext (iff := false)]
theorem uget_ext {a b : ExArray} (h : a.size = b.size) :
    (∀ (i : UInt64), (hin : i.toNat < a.size) → a.uget i = b.uget i) →
    a = b := by
  intros h'
  have ⟨a, ah⟩ := a
  have ⟨b, bh⟩ := b
  congr 1
  simp only [size] at h h'
  ext i hi hi'
  · grind
  have : i.toUInt64.toNat = i := by simp; grind [=Nat.mod_eq_of_lt]
  simp [uget] at h'
  specialize h' i.toUInt64 (by apply Nat.mod_lt_of_lt; grind)
  grind

@[extern "buffed_ex_array_push"]
def push (a: ExArray) (value: UInt8) (h: a.size + 1 < Int64.maxNatValue) : ExArray :=
  { data := a.data.push value, data_fits_in_memory := (by simp_all only [size, Array.size_push]) }

theorem push_size {a : ExArray} {value h} :
    (a.push value h).size = a.size + 1 := by
  simp only [push, size, Array.size_push]

def extendNat : (a : ExArray) → (len : Nat) → (a.size + len < Int64.maxNatValue) → ExArray
  | a, 0, h => a
  | a, Nat.succ len', h => (a.push 0 (by lia)).extendNat len' (by simp [push_size]; lia)

theorem extendNat_size :
    ∀ (len : Nat) (a : ExArray) (h : a.size + len < Int64.maxNatValue),
    (a.extendNat len h).size = a.size + len := by
  intros len
  induction len with
  | zero => intros a h; simp only [extendNat, Nat.add_zero]
  | succ len' ih =>
    intros a h
    simp only [extendNat, ih, push_size]
    lia

@[extern "buffed_ex_array_extend"]
def extend (a : ExArray) (len : UInt64) (h: a.size + len.toNat < Int64.maxNatValue := by grind) : ExArray :=
  a.extendNat len.toNat (by simpa [size])

@[simp, grind =]
theorem extend_size (a : ExArray) (len : UInt64) (h: a.size + len.toNat < Int64.maxNatValue) :
    (a.extend len h).size = a.size + len.toNat := by
  simp only [extend, extendNat_size]

@[simp, grind =]
theorem extend_range (a : ExArray) (len : UInt64) (h: a.size + len.toNat < Int64.maxNatValue) :
    (a.extend len h).range = 0...(a.size + len.toNat) := by
  simp [range]

@[simp, grind .]
theorem extend_range_included (a : ExArray) (len : UInt64) (h: a.size + len.toNat < Int64.maxNatValue) :
    IsIncluded a.range (a.extend len h).range := by
  grind

def blitRec {w: Nat} (buf : ExArray) (n : UInt64) (k : Nat) (x : BitVec w)
    (h : IsIncluded (n.toNat...(n.toNat + k)) buf.range := by grind) : ExArray :=
  match k with
  | 0 => buf
  | k+1 =>
    let buf' := buf.uset n (UInt8.ofBitVec $ x.setWidth 8)
    blitRec buf' (n + 1) k (x >>> 8) (by grind)

@[local simp, local grind =, extern "buffed_ex_array_blit"]
def blit {w : @&Nat} (buf : ExArray) (n : UInt64) (numBytes : UInt64) (x : @&BitVec w)
    (h : IsIncluded (n.toNat...(n.toNat + numBytes.toNat)) buf.range := by grind) :=
  blitRec buf n numBytes.toNat x

@[simp, grind =]
def blitNat (buf : ExArray) (n : UInt64) (len : UInt64) (x : Nat)
    (h : IsIncluded (n.toNat...(n.toNat + len.toNat)) buf.range := by grind)
     : ExArray :=
  blit buf n len (BitVec.ofNat (8 * len.toNat) x)

def readRec (buf : ExArray) (n : UInt64) (numBytes : Nat)
    (h : IsIncluded (n.toNat...(n.toNat + numBytes)) buf.range := by grind) : BitVec w :=
  match numBytes with
  | 0 => 0
  | k+1 =>
    let x := buf.uget n (by grind) |>.toBitVec |>.setWidth w
    let next := readRec buf (n + 1) k (by grind)
    x + (next <<< 8)

@[local simp, local grind =, extern "buffed_ex_array_read"]
def read (buf : @& ExArray) (n : UInt64) (len : UInt64)
    (h : IsIncluded (n.toNat...(n.toNat + len.toNat)) buf.range := by grind) : BitVec w :=
  readRec buf n len.toNat (by grind)

@[local simp, local grind =]
def read! (buf : @& ExArray) (n : UInt64) (len : UInt64) : BitVec w :=
  if h : IsIncluded (n.toNat...(n.toNat + len.toNat)) buf.range then
    read buf n len h
  else
    default

@[simp, grind =]
theorem read_eq_read! {buf : ExArray} h :
    buf.read (w := w) n len h = buf.read! n len := by
  grind [read, read!]

@[simp, grind =]
def readNat (buf : @& ExArray) (n : UInt64) (len : UInt64)
    (h : IsIncluded (n.toNat...(n.toNat + len.toNat)) buf.range := by grind) : Nat :=
  read (w := len.toNat) buf n len h |>.toNat

@[extern "buffed_ex_array_blit32", simp, grind =]
def blit32 (buf : ExArray) (n : UInt64) (x : UInt32)
    (h : IsIncluded (n.toNat...(n.toNat + 4)) buf.range := by grind)
     : ExArray :=
  blit buf n (numBytes := 4) x.toBitVec

@[extern "buffed_ex_array_blit64", local simp, local grind =]
def blit64 (buf : ExArray) (n : UInt64) (x : UInt64)
    (h : IsIncluded (n.toNat...(n.toNat + 8)) buf.range := by grind)
     : ExArray :=
  blit buf n (numBytes := 8) x.toBitVec

@[extern "buffed_ex_array_read32", local simp, local grind =]
def read32 (buf : @& ExArray) (n : UInt64)
    (h : IsIncluded (n.toNat...(n.toNat + 4)) buf.range := by grind)
     : UInt32 :=
  UInt32.ofBitVec (read buf n 4 (h := by grind))

@[extern "buffed_ex_array_read64", local simp, local grind =]
def read64 (buf : @& ExArray) (n : UInt64)
    (h : IsIncluded (n.toNat...(n.toNat + 8)) buf.range := by grind)
     : UInt64 :=
  UInt64.ofBitVec (read buf n 8 (h := by grind))

def read64! (buf : @& ExArray) (n : UInt64) : UInt64 :=
  UInt64.ofBitVec (read! buf n 8)

def read32! (buf : @& ExArray) (n : UInt64) : UInt32 :=
  UInt32.ofBitVec (read! buf n 4)

@[simp, grind =]
theorem read64_eq_read64! {buf : ExArray} h :
    buf.read64 n h = buf.read64! n := by
  grind [read64!]

@[simp, grind =]
theorem read32_eq_read32! {buf : ExArray} h :
    buf.read32 n h = buf.read32! n := by
  grind [read32!]

@[simp, grind =]
theorem blitRec_zero (buf: ExArray) n {w} (x: BitVec w) h :
    buf.blitRec n 0 x h = buf := by
  simp only [blitRec]

@[simp, grind =]
theorem blitRec_one (buf: ExArray) n {w} (x: BitVec w) h hNe :
    buf.blitRec n 1 x h = (buf.uset n (UInt8.ofBitVec (x.truncate 8)) (by omega)) := by
  simp only [blitRec]

theorem blitRec_succ (buf: ExArray) n numBytes {w} (x: BitVec w) h :
    buf.blitRec n (numBytes + 1) x h =
    (buf.uset n (UInt8.ofBitVec (x.truncate 8)) (by grind)).blitRec (n + 1) numBytes (x >>> 8) (by grind) := by
  simp only [blitRec]

@[simp, grind =]
theorem blitRec_size (buf: ExArray) n numBytes x h :
    (buf.blitRec (w := w) n numBytes x h).size = buf.size := by
  induction numBytes generalizing x n buf
  case zero => simp [blitRec]
  case succ numBytes ih =>
    simp [blitRec, *]

@[simp, grind =]
theorem blit_size (buf: ExArray) n numBytes x h :
    (buf.blit (w := w) n numBytes x h).size = buf.size := by
  grind

@[simp, grind =]
theorem blit32_size (buf: ExArray) n x h :
    (buf.blit32 n x h).size = buf.size := by
  grind

@[simp, grind =]
theorem blit64_size (buf: ExArray) n x h :
    (buf.blit64 n x h).size = buf.size := by
  grind

abbrev support (n numBytes : Nat) := n...(n + numBytes)

/-! Lemmas about range preservation -/

@[local grind =]
theorem size_blitRec {buf : ExArray} {x : BitVec w} h :
    (buf.blitRec n k x h).size = buf.size := by
  fun_induction ExArray.blitRec with grind

@[simp, grind =]
theorem size_blit {buf : ExArray} {x : BitVec w} h :
    (buf.blit n k x h).size = buf.size := by
  grind

@[local grind =]
theorem range_blitRec {buf : ExArray} {x : BitVec w} h :
    (buf.blitRec n k x h).range = buf.range := by
  fun_induction ExArray.blitRec with grind

@[simp, grind =]
theorem range_blit {buf : ExArray} {x : BitVec w} h :
    (buf.blit n k x h).range = buf.range := by
  grind

@[simp, grind =]
theorem range_blit64 {buf : ExArray} {x : UInt64} h :
    (buf.blit64 n x h).range = buf.range := by
  grind

@[simp, grind =]
theorem range_blit32 {buf : ExArray} {x : UInt32} h :
    (buf.blit32 n x h).range = buf.range := by
  grind

@[grind =]
theorem blitRec_uget_disjoint {w} (buf: ExArray) n numBytes m (x : BitVec w) h h' :
    m.toNat ∉ support n.toNat numBytes →
    (buf.blitRec n numBytes x h).uget m = buf.uget m h' := by
  induction numBytes generalizing n buf x <;> grind [blitRec_succ]

@[simp, grind =]
theorem blitRec_uget_mem {w} (x : BitVec w) m n numBytes (buf: ExArray) h h'
    (hin : m.toNat ∈ support n.toNat numBytes) :
    (buf.blitRec n numBytes x h).uget m h' = (x.toNat >>> (8 * (m.toNat - n.toNat))).toUInt8 := by
  have hLt: m ≥ n := by grind [UInt64.le_iff_toNat_le]
  induction numBytes generalizing x n m buf
  case zero => grind
  case succ numBytes ih =>
    simp only [blitRec] --cannot apply blitRec_succ here
    by_cases h : n = m
    · subst m
      grind [UInt8.ofNat]
    · rw [ih]
      · simp only [BitVec.toNat_ushiftRight, Nat.toUInt8_eq]
        rw [← Nat.shiftRight_add, UInt64.add_toNat_lt]
        · grind [UInt64.lt_iff_toNat_lt, →UInt64.lt_of_le_of_ne]
        · grind
      · grind [UInt64.toNat_inj]
      · grind

theorem blitRec_uget_split {w} (buf: ExArray) n numBytes m (x : BitVec w) h h' :
    (buf.blitRec n numBytes x h).uget m h' =
    if m.toNat ∈ support n.toNat numBytes
    then (x.toNat >>> (8 * (m.toNat - n.toNat))).toUInt8
    else buf.uget m := by
  grind only [= blitRec_uget_mem, = blitRec_size, = blitRec_uget_disjoint]

theorem blitRec_succ_comm (buf: ExArray) n numBytes {w} (x: BitVec w) h :
    buf.blitRec n (numBytes + 1) x h =
    (buf.blitRec (n + 1) numBytes (x >>> 8) (by grind)).uset n (UInt8.ofBitVec (x.truncate 8)) (by grind) := by
  simp only [blitRec_succ]
  apply uget_ext <;> grind

theorem blitRec_uset_disjoint {w} (buf: ExArray) n numBytes m (x : BitVec w)
    (hDisjoint: m.toNat ∉ support n.toNat numBytes) h₁ h₂ h₃ h₄ :
    (buf.blitRec n numBytes x h₁).uset m (UInt8.ofBitVec (x.truncate 8)) h₂ =
    (buf.uset m (UInt8.ofBitVec (x.truncate 8)) h₃).blitRec n numBytes x h₄ := by
  apply uget_ext <;> grind

theorem blitRec_comm_disjoint {w} (buf: ExArray) n n' numBytes numBytes' (x x': BitVec w)
    (hDisjoint: IsDisjoint (support n.toNat numBytes) (support n'.toNat numBytes')) h₁ h₂ :
    (buf.blitRec n numBytes x h₁).blitRec n' numBytes' x' h₂ =
    (buf.blitRec n' numBytes' x').blitRec n numBytes x := by
  apply uget_ext <;> grind

@[simp, grind =]
theorem readRec_zero (w : Nat) (buf : ExArray) (n : UInt64) h :
    buf.readRec (w := w) n 0 h = 0 := by
  simp only [readRec]

@[simp, grind =]
theorem readRec_one (w : Nat) (buf : ExArray) (n : UInt64) h:
    buf.readRec (w := w) n 1 h = ((buf.uget n) |>.toBitVec |>.setWidth w) := by
  simp only [readRec]
  grind

theorem readRec_succ (w : Nat) (buf : ExArray) (n : UInt64) numBytes h :
    buf.readRec (w := w) n (numBytes + 1) h =
    ((buf.uget n (by grind)).toBitVec |>.setWidth w) + (buf.readRec (n + 1) numBytes (by grind) <<< 8) := by
  simp only [readRec]

@[grind =]
theorem readRec_uset_disjoint {w : Nat} (buf : ExArray) (n: UInt64) numBytes m (x: UInt8)
    (hDisjoint: m.toNat ∉ support n.toNat numBytes) h₁ h₂ :
    (buf.uset m x h₁).readRec n numBytes h₂ = buf.readRec (w := w) n numBytes (by grind) := by
  induction numBytes generalizing n buf x <;> grind [readRec_succ]

@[simp, grind =]
theorem readRec_blitRec_self (w : Nat) (buf : ExArray) (n : UInt64) numBytes (x : BitVec w) h h' :
    (buf.blitRec n numBytes x h).readRec n numBytes h' = (x |>.setWidth (8*numBytes) |>.setWidth w) := by
  induction numBytes generalizing x n buf
  case zero => grind
  case succ numBytes ih =>
    simp only [blitRec_succ_comm, readRec_succ, uget_uset_self, BitVec.truncate]
    rw [readRec_uset_disjoint] <;> try grind
    rw [ih]
    simp only [BitVec.toNat_eq, BitVec.toNat_add, BitVec.toNat_setWidth,
      BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.add_mod_mod, Nat.mod_add_mod]
    rw [Nat_mod_mod_eq_mod_mod_of_two_pow]
    have hlt : (x.toNat >>> 8) < 2 ^ w := by omega
    rw [Nat.mod_eq_of_lt hlt]
    congr 1
    simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    simp only [←Nat.mod_mul_left_div_self]
    rw [←@Nat.mod_mod_of_dvd (2 ^ 8) (2 ^ (8 * (numBytes + 1))) x.toNat (by grind)]
    grind

theorem read!_blit_self (w w' : Nat) (buf : ExArray) (n : UInt64) numBytes (x : BitVec w) h (heq : w = w') :
    (buf.blit n numBytes x h).read! (w := w') n numBytes = (x |>.setWidth (8*numBytes.toNat) |>.setWidth w') := by
  grind [read!]

@[simp, grind =]
theorem read!_blit_self_aligned (w w' : Nat) (buf : ExArray) (n : UInt64) numBytes (x : BitVec w) h (heq : w = w') :
    (w = 8 * numBytes.toNat) →
    (buf.blit n numBytes x h).read! (w := w') n numBytes = x.cast heq := by
  grind [BitVec.setWidth_setWidth_of_le, read!_blit_self]

@[simp, grind =]
theorem readRec_blitRec_disjoint (w w' : Nat) (buf : ExArray) (n n' : UInt64) numBytes numBytes' (x : BitVec w) h h' :
    IsDisjoint (support n.toNat numBytes) (support n'.toNat numBytes') →
    (buf.blitRec n' numBytes' x h).readRec (w := w') n numBytes h' = buf.readRec (w := w') n numBytes (by grind) := by
  induction numBytes' generalizing n' buf x <;>
    grind [IsDisjoint, blitRec_succ_comm]

@[simp, grind =]
theorem size_blit64 (buf : ExArray) (n : UInt64) (x : UInt64) h :
    (buf.blit64 n x h).size = buf.size := by
  simp

@[simp, grind =]
theorem read64_blit64_self (buf : ExArray) (n : UInt64) (x : UInt64) h h' :
    (buf.blit64 n x h).read64 n h' = x := by
  simp

@[simp, grind =]
theorem read64!_blit64_self (buf : ExArray) (n : UInt64) (x : UInt64) h :
    (buf.blit64 n x h).read64! n  = x := by
  grind [=_ read64_eq_read64!]

@[simp, grind =]
theorem read32_blit32_self (buf : ExArray) (n : UInt64) (x : UInt32) h h' :
    (buf.blit32 n x h).read32 n h' = x := by
  simp

@[simp, grind =]
theorem read32!_blit32_self (buf : ExArray) (n : UInt64) (x : UInt32) h :
    (buf.blit32 n x h).read32! n = x := by
  grind [=_ read32_eq_read32!]
@[simp, grind =]
theorem read64_blit64_disjoint (buf : ExArray) (n n' : UInt64) (x : UInt64) h h' :
    IsDisjoint (n.toNat ... (n.toNat + 8)) (n'.toNat ... (n'.toNat + 8)) →
    (buf.blit64 n' x h).read64 n h' = buf.read64 n (by grind) := by
  grind

@[simp, grind =]
theorem read32_blit32_disjoint (buf : ExArray) (n n' : UInt64) (x : UInt32) h h' :
    IsDisjoint (n.toNat ... (n.toNat + 4)) (n'.toNat ... (n'.toNat + 4)) →
    (buf.blit32 n' x h).read32 n h' = buf.read32 n (by grind) := by
  grind

@[simp, grind =]
theorem read64!_blit64_disjoint (buf : ExArray) (n n' : UInt64) (x : UInt64) h :
    IsDisjoint (n.toNat ... (n.toNat + 8)) (n'.toNat ... (n'.toNat + 8)) →
    (buf.blit64 n' x h).read64! n = buf.read64! n := by
  grind [read64!]

@[simp, grind =]
theorem read32!_blit64_disjoint (buf : ExArray) (n n' : UInt64) (x : UInt64) h :
    IsDisjoint (n.toNat ... (n.toNat + 4)) (n'.toNat ... (n'.toNat + 8)) →
    (buf.blit64 n' x h).read32! n = buf.read32! n := by
  grind [read32!]

@[simp, grind =]
theorem read64!_blit_disjoint (buf : ExArray) (n n' : UInt64) (x : BitVec w) h :
    IsDisjoint (n.toNat ... (n.toNat + 8)) (n'.toNat ... (n'.toNat + len.toNat)) →
    (buf.blit n' len x h).read64! n = buf.read64! n := by
  grind [read64!]

@[simp, grind =]
theorem read32!_blit_disjoint (buf : ExArray) (n n' : UInt64) (x : BitVec w) h :
    IsDisjoint (n.toNat ... (n.toNat + 4)) (n'.toNat ... (n'.toNat + len.toNat)) →
    (buf.blit n' len x h).read32! n = buf.read32! n := by
  grind [read32!]

@[simp, grind =]
theorem read!_blit64_disjoint (buf : ExArray) (n n' : UInt64) (x : UInt64) h :
    IsDisjoint (n.toNat ... (n.toNat + len.toNat)) (n'.toNat ... (n'.toNat + 8)) →
    (buf.blit64 n' x h).read! (w := w) n len = buf.read! n len := by
  grind [read!]

@[simp, grind =]
theorem read!_blit_disjoint (buf : ExArray) (n n' : UInt64) (x : BitVec w') h :
    IsDisjoint (n.toNat ... (n.toNat + len.toNat)) (n'.toNat ... (n'.toNat + len'.toNat)) →
    (buf.blit (w := w') n' len' x h).read! (w := w) n len = buf.read! n len := by
  grind [read!]

@[simp, grind =]
theorem read!_blit32_disjoint (buf : ExArray) (n n' : UInt64) (x : UInt32) h :
    IsDisjoint (n.toNat ... (n.toNat + len.toNat)) (n'.toNat ... (n'.toNat + 4)) →
    (buf.blit32 n' x h).read! (w := w) n len = buf.read! n len := by
  grind [read!]

@[simp, grind =]
theorem read64!_blit32_disjoint (buf : ExArray) (n n' : UInt64) (x : UInt32) h :
    IsDisjoint (n.toNat ... (n.toNat + 8)) (n'.toNat ... (n'.toNat + 4)) →
    (buf.blit32 n' x h).read64! n = buf.read64! n := by
  grind [read64!]

@[simp, grind =]
theorem read32!_blit32_disjoint (buf : ExArray) (n n' : UInt64) (x : UInt32) h :
    IsDisjoint (n.toNat ... (n.toNat + 4)) (n'.toNat ... (n'.toNat + 4)) →
    (buf.blit32 n' x h).read32! n = buf.read32! n := by
  grind [read32!]

theorem uget_push (buf : ExArray) (n : UInt64) (x: UInt8) h h' :
    (buf.push x h).uget n h' = if h'': n.toNat < buf.size then buf.uget n h'' else x := by
  simp only [push, uget, Array.getElem_push, size]
  grind

theorem readRec_push (w : Nat) (buf : ExArray) (n : UInt64) (x: UInt8) (len: Nat) h h' h'' :
    (buf.push x h).readRec (w := w) n len h' = buf.readRec n len h'' := by
  induction len generalizing n <;> grind [readRec_succ, uget_push]

theorem readRec_extend_nat (w : Nat) (buf : ExArray) (n : UInt64) (len len': Nat) h h' h'' :
    (buf.extendNat len h).readRec (w := w) n len' h' = buf.readRec n len' h'' := by
  induction len generalizing buf
  case zero => simp only [extendNat]
  case succ len ih =>
    simp only [extendNat]
    rw [ih]
    rw [readRec_push]
    grind [push_size, UInt64.toNat_inj]

@[simp, grind =]
theorem readRec_extend (w : Nat) (buf : ExArray) (n : UInt64) (len : Nat) (ext_len: UInt64) h h'
    (h'' : IsIncluded (n.toNat...(n.toNat + len)) buf.range) :
    (buf.extend ext_len h).readRec (w := w) n len h' =
    buf.readRec n len h'' := by
  simp only [extend]
  rw [readRec_extend_nat]

@[simp, grind =]
theorem read!_extend (buf : ExArray) (n : UInt64) (len : UInt64) (extLen: UInt64) h
    (h'' : IsIncluded (n.toNat...(n.toNat + len.toNat)) buf.range) :
    (buf.extend extLen h).read! (w := w) n len = buf.read! n len := by
  grind [read!]

@[simp, grind =]
theorem read64!_extend (buf : ExArray) (n : UInt64) (extLen: UInt64) h
    (h'' : IsIncluded (n.toNat...(n.toNat + 8)) buf.range) :
    (buf.extend extLen h).read64! n = buf.read64! n := by
  grind [read64!]

@[simp, grind =]
theorem read32!_extend (buf : ExArray) (n : UInt64) (extLen: UInt64) h
    (h'' : IsIncluded (n.toNat...(n.toNat + 4)) buf.range) :
    (buf.extend extLen h).read32! n = buf.read32! n := by
  grind [read32!]
