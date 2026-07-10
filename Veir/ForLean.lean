module

public import Std.Data.ExtHashSet
public import Std.Data.HashMap
public import Veir.Meta.BVNormalizeSimp
import all Init.Data.Array.Basic -- unfold [Array.popWhile] in Array.getElem?_popWhile_of_false
public section

/--
  We compare `ByteArray`s by with lexicographic ordering.
-/
instance : Ord ByteArray where
  compare ba1 ba2 := compare ba1.data ba2.data

/-- Checks if a UInt8 character is an alphabetic character or underscore in UTF-8. -/
@[inline]
def UInt8.isAlphaOrUnderscore (c : UInt8) : Bool :=
  (c >= 'a'.toUInt8 && c <= 'z'.toUInt8) || (c >= 'A'.toUInt8 && c <= 'Z'.toUInt8) || (c == '_'.toUInt8)

/-- Checks if a UInt8 character is representing a digit in UTF-8. -/
@[inline]
def UInt8.isDigit (c : UInt8) : Bool :=
  c >= '0'.toUInt8 && c <= '9'.toUInt8

@[inline]
def UInt8.isHexDigit (c : UInt8) : Bool :=
  c.isDigit || (c >= 'a'.toUInt8 && c <= 'f'.toUInt8) || (c >= 'A'.toUInt8 && c <= 'F'.toUInt8)

def UInt16.toByteArrayLE (u : UInt16) : ByteArray :=
  ByteArray.mk (Array.mk [
    u.toUInt8,
    (u >>> 0x08).toUInt8,
  ])

def UInt32.toByteArrayLE (u : UInt32) : ByteArray :=
  ByteArray.mk (Array.mk [
    u.toUInt8,
    (u >>> 0x08).toUInt8,
    (u >>> 0x10).toUInt8,
    (u >>> 0x18).toUInt8,
  ])

def UInt64.toByteArrayLE (u : UInt64) : ByteArray :=
  ByteArray.mk (Array.mk [
    u.toUInt8,
    (u >>> 0x08).toUInt8,
    (u >>> 0x10).toUInt8,
    (u >>> 0x18).toUInt8,
    (u >>> 0x20).toUInt8,
    (u >>> 0x28).toUInt8,
    (u >>> 0x30).toUInt8,
    (u >>> 0x38).toUInt8,
  ])

@[simp, grind =]
theorem UInt64.toByteArrayLE_size (u : UInt64) :
    u.toByteArrayLE.size = 8 := by
  simp [toByteArrayLE, ByteArray.size]

namespace ByteArray

@[simp, grind =]
theorem size_emptyWithCapacity (n : Nat) :
    (ByteArray.emptyWithCapacity n).size = 0 := by constructor

def extend (ba : ByteArray) (n : Nat) (val : UInt8) : ByteArray :=
  n.fold (init := ba) fun _ _ ba => ba.push val

@[simp, grind =]
theorem extend_zero (ba : ByteArray) (val : UInt8) :
    ba.extend 0 val = ba := by
  simp [extend]

@[simp, grind =]
theorem extend_size (ba : ByteArray) (n : Nat) (val : UInt8) :
    (ba.extend n val).size = ba.size + n := by
  induction n
  case zero => simp
  case succ n h =>
    grind [Nat.fold_succ, size_push, extend]

@[simp]
def replicate (n : Nat) (v : UInt8) : ByteArray :=
  (ByteArray.emptyWithCapacity n).extend n v

@[simp, grind =]
theorem replicate_size (n : Nat) (v : UInt8) :
    (ByteArray.replicate n v).size = n := by
  simp

@[inline]
def getD (ba : ByteArray) (i : Nat) (default : UInt8) : UInt8 :=
  if h : i < ba.size then ba[i] else default

/-- Interpret the bytes of a little-endian `ByteArray`
    as a `BitVec (8 * bytes)` (byte 0 is the least significant). -/
def toBitVecLE (ba : ByteArray) (bytes : Nat) : BitVec (8 * bytes) :=
  ba.toByteSlice.foldr (fun b acc => acc <<< 8 ||| b.toBitVec.setWidth (8 * bytes)) 0

axiom toBitVecLE_one (ba : ByteArray) :
    ba.toBitVecLE 1 = BitVec.ofNat 8 ba[0]!.toNat

axiom toBitVecLE_eight (ba : ByteArray) :
    ba.toBitVecLE 8 = BitVec.ofNat 64 ba.toUInt64LE!.toNat

end ByteArray

/--
  Convert a hexadecimal digit character to its Nat value.
-/
def Char.hexValue? (c : Char) : Option Nat :=
  match c with
  | '0' => some 0
  | '1' => some 1
  | '2' => some 2
  | '3' => some 3
  | '4' => some 4
  | '5' => some 5
  | '6' => some 6
  | '7' => some 7
  | '8' => some 8
  | '9' => some 9
  | 'a' | 'A' => some 0xA
  | 'b' | 'B' => some 0xB
  | 'c' | 'C' => some 0xC
  | 'd' | 'D' => some 0xD
  | 'e' | 'E' => some 0xE
  | 'f' | 'F' => some 0xF
  | _ => none

/--
  Parse a sequence of hexadecimal digit characters into a Nat.
-/
def ByteArray.hexToNat? (str : ByteArray) : Option Nat := Id.run do
  let mut res := 0
  for h: i in 2...(str.size) do
    let hexValue := (Char.ofUInt8 (str[i]'(by simp [Membership.mem] at h; grind))).hexValue?
    if let some value := hexValue then
      res := value + (res <<< 4)
    else
      return none
  some res

private theorem List.dropWhile_head_false (p : α → Bool) (l : List α)
    (hl : List.dropWhile p l ≠ []) : p ((List.dropWhile p l).head hl) = false := by
  induction l <;> grind [List.dropWhile]

private theorem List.reverse_toArray_back {l : List α} (hl : l ≠ []) (h : 0 < l.reverse.toArray.size) :
    l.reverse.toArray.back h = l.head hl := by
  have hLen : 0 < l.length := List.ne_nil_iff_length_pos.mp hl
  grind

@[grind .]
theorem Array.back_popWhile {as : Array α} {p : α → Bool} (h : 0 < (as.popWhile p).size) :
    p ((as.popWhile p).back h) = false := by
  rcases as with ⟨as⟩
  have hKey : (Array.mk as).popWhile p = (List.dropWhile p as.reverse).reverse.toArray :=
    by rw [show Array.mk as = as.toArray from rfl, ← List.popWhile_toArray]
  have hNe : List.dropWhile p as.reverse ≠ [] := by
    intro heq; simp [hKey, heq] at h
  simp only [hKey, List.reverse_toArray_back hNe]
  exact List.dropWhile_head_false p as.reverse hNe

theorem Array.getElem?_popWhile_of_false {p : α → Bool} {as : Array α} {i : Nat}
    (hi : i < as.size) (hp : p (as[i]'hi) = false) :
    (as.popWhile p)[i]? = as[i]? := by
  fun_induction Array.popWhile <;> grind

theorem Array.reverse_singleton (a : α) :
    #[a].reverse = #[a] := by
  simp

theorem List.length_of_mapM_option_eq_some {f : α → Option β} {l : List α} {r : List β}
    (h : l.mapM f = some r) : l.length = r.length := by
  induction l generalizing r <;> grind [Option.bind_eq_some_iff]

theorem List.getElem?_of_mapM_option_eq_some {f : α → Option β} {l : List α} {r : List β}
    (h : l.mapM f = some r) (i : Nat) : l[i]?.bind f = r[i]? := by
  induction l generalizing r i <;> grind [Option.bind_eq_some_iff]

theorem List.mapM_option_isSome {f : α → Option β} {l : List α}
    (h : ∀ a ∈ l, (f a).isSome) : ∃ r, l.mapM f = some r := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a t ih =>
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h a (by simp))
    grind [ih (fun x hx => h x (by grind))]

@[grind →]
theorem Array.size_eq_of_mapM_eq_some (h : Array.mapM f l = some res) :
  l.size = res.size := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hm : List.mapM f l.toList with
  | none => simp [hm] at h
  | some r => grind [List.length_of_mapM_option_eq_some hm]

theorem Array.mapM_option_eq_some_implies {l : Array α} {res : Array β} (h : Array.mapM f l = some res) :
    ∀ i (h : i < res.size), f (l[i]'(by grind)) = some res[i] := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hm : List.mapM f l.toList with
  | none => simp [hm] at h
  | some r =>
    intro i hi
    grind [List.getElem?_of_mapM_option_eq_some hm i]

theorem Array.mapM_option_isSome {α : Type u} {β : Type v} {f : α → Option β}
    {l : Array α} (h : ∀ i (hi : i < l.size), (f l[i]).isSome) :
    ∃ r, l.mapM f = some r := by
  rw [Array.mapM_eq_mapM_toList]
  obtain ⟨r, hr⟩ := List.mapM_option_isSome (f := f) (l := l.toList)
    (fun a ha => by obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha; simpa using h i (by simpa using hi))
  exact ⟨r.toArray, by simp [hr]⟩

theorem Array.mapM_eq_some_iff_of_size_eq [Inhabited α] [Inhabited β] {a₁ : Array α} {a₂ : Array β} :
    a₁.size = a₂.size →
    (Array.mapM f a₁ = some a₂ ↔
    (∀ i, (hi : i < a₁.size) → f a₁[i]! = some a₂[i]!)) := by
  intro hsize
  constructor
  · grind [Array.mapM_option_eq_some_implies]
  · intro h
    have ⟨r, hr⟩ := Array.mapM_option_isSome (f := f) (l := a₁) (by grind)
    have hrsize := Array.size_eq_of_mapM_eq_some hr
    suffices r = a₂ by grind
    grind [Array.mapM_option_eq_some_implies]

theorem Array.exists_mapM_option_eq_some_iff {f : α → Option β} {l : Array α} :
    (∃ r, l.mapM f = some r) ↔ (∀ i (hi : i < l.size), ∃ v, f l[i] = some v) := by
  constructor
  · rintro ⟨r, hr⟩ i hi
    grind [Array.mapM_option_eq_some_implies hr i (by grind)]
  · intro h
    apply Array.mapM_option_isSome
    grind

namespace ForLean.List

theorem idxOf_getElem [DecidableEq α] {l : List α} (H : l.Nodup) (i : Nat) (h : i < l.length) :
    List.idxOf l[i] l = i := by
  induction l generalizing i <;> grind

theorem getElem_idxOf [DecidableEq α] {l : List α} (h : l.idxOf x < l.length) :
    l[l.idxOf x] = x := by
  induction l <;> grind

end ForLean.List

section
open ForLean

@[simp, grind =]
theorem Array.getElem?_idxOf [DecidableEq α] {l : Array α} (h : l.idxOf x < l.size) :
    l[l.idxOf x]? = some x := by
  rcases l; grind [List.getElem_idxOf]

@[simp, grind =]
theorem Array.getElem_idxOf [DecidableEq α] {l : Array α} (h : l.idxOf x < l.size) :
    l[l.idxOf x] = x := by
  rcases l; grind [List.getElem_idxOf]

end

@[simp, grind =]
theorem Array.toList_erase [BEq α] (l : Array α) (a : α) :
    (l.erase a).toList = l.toList.erase a := by
  cases l; grind

theorem Array.singleton_getElem_append_extract_succ_eq {a : Array α} {k : Nat} (h : k < a.size) :
    #[a[k]] ++ a.extract (k + 1) a.size = a.extract k a.size := by
  cases a
  simp [←List.length_drop]

theorem Array.head_tail_if_firstElem_nonnull (as : Array α) :
    as[0]? = some head →
    ∃ tail, as = #[head] ++ tail := by
  intros
  have ⟨list⟩ := as
  cases list <;> simp_all <;> grind

theorem Array.erase_head_concat {α : Type} [BEq α] [LawfulBEq α] {arrayHead : α} {arrayTail} :
    (#[arrayHead] ++ arrayTail).erase arrayHead = arrayTail := by
  have ⟨list⟩ := arrayTail
  induction list <;> grind

theorem Nat.eq_iff_forall_lessthan :
    (∀ (i : Nat), i < n ↔ i < m) → n = m := by
  intros hi
  cases n
  case zero =>
    have := hi 0
    grind
  case succ i =>
    have := hi i
    have := hi (i + 1)
    grind

deriving instance DecidableEq for Except

@[simp, grind =]
theorem Std.ExtHashSet.filter_empty {α : Type} [Hashable α] [BEq α] [LawfulBEq α] (f : α → Bool) :
    (∅ : Std.ExtHashSet α).filter f = ∅ := by
  grind

theorem Std.ExtHashSet.filter_erase_eq {α : Type} [Hashable α] [BEq α] [LawfulBEq α]
    (s : Std.ExtHashSet α) (a : α) (f : α → Bool) :
    (s.erase a).filter f = (s.filter f).erase a := by
  grind

theorem Std.ExtHashSet.filter_insert_eq_of_true_eq {α : Type} [Hashable α] [BEq α] [LawfulBEq α]
    (s : Std.ExtHashSet α) (a : α) (f : α → Bool) :
    f a = true →
    (s.insert a).filter f = (s.filter f).insert a := by
  grind

theorem Std.ExtHashSet.filter_insert_eq_of_false_eq {α : Type} [Hashable α] [BEq α] [LawfulBEq α]
    (s : Std.ExtHashSet α) (a : α) (f : α → Bool) :
    f a = false →
    (s.insert a).filter f = s.filter f := by
  intro h
  ext; grind

theorem Std.ExtHashSet.insertMany_list_insert_comm [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] [BEq α] [LawfulBEq α]
    (s : Std.ExtHashSet α) (a : α) (l : List α) :
    (s.insert a).insertMany l = (s.insertMany l).insert a := by
  ext; grind

theorem Std.ExtHashSet.insertMany_empty_eq_ofList [BEq α] [EquivBEq α] [Hashable α] [LawfulHashable α] [BEq α] [LawfulBEq α]
    (l : List α) :
    (∅ : Std.ExtHashSet α).insertMany l = Std.ExtHashSet.ofList l := by
  ext; grind

/--
  A version of `Std.HashMap.keys.for` that also passes to the given function a proof
  that the key exists in the map.
  It is currently not as efficient as it could be, as we check dynamically that the key is
  indeed in the map (although it should always be the case). This could be improved by
  modifying the `Std.HashMap` implementation to pass such proof statically.
-/
def Std.HashMap.forKeysDepM [BEq α] [Hashable α] {m : Type w → Type w'} [Monad m]
    (b : Std.HashMap α β) (f : ∀ (a : α), a ∈ b → m PUnit) : m PUnit :=
  b.forM (fun k v => do if h : k ∈ b then f k (by grind))

section ranges

open Std

@[grind=]
theorem mem_range_nat (i: Nat) (r: Rco Nat) : (i ∈ r) ↔ r.lower ≤ i ∧ i < r.upper := by
  simp only [Membership.mem]

end ranges


/-!
  This section adapts the standard library's `Array.isEqv` to also provide a proof
  that the elements being related are members of their relative arrays. This
  allows us to define `Attribute.instDecidableEq` in a somewhat compositional way.
-/

namespace Array

@[specialize]
def isEqvAux' (xs ys : Array α) (hsz : xs.size = ys.size) (p : (x: α) → (y : α) → x ∈ xs → y ∈ ys → Bool) :
    ∀ (i : Nat) (_ : i ≤ xs.size), Bool
  | 0, _ => true
  | i+1, h =>
    p xs[i] (ys[i]'(hsz ▸ h)) (by grind) (by grind) && isEqvAux' xs ys hsz p i (Nat.le_trans (Nat.le_add_right i 1) h)

@[inline] def isEqv' (xs ys : Array α) (p : (x: α) → (y : α) → x ∈ xs → y ∈ ys → Bool) : Bool :=
  if h : xs.size = ys.size then
    isEqvAux' xs ys h p xs.size (Nat.le_refl xs.size)
  else
    false

private theorem rel_of_isEqvAux'  {xs ys : Array α}
    {r : (x: α) → (y : α) → x ∈ xs → y ∈ ys → Bool} (hsz : xs.size = ys.size) {i : Nat} (hi : i ≤ xs.size)
    (heqv : Array.isEqvAux' xs ys hsz r i hi)
    {j : Nat} (hj : j < i) : r xs[j] ys[j] (by grind) (by grind) := by
  induction i with
  | zero => omega
  | succ i ih => simp only [Array.isEqvAux', Bool.and_eq_true] at heqv; grind

private theorem isEqvAux'_of_rel {xs ys : Array α}
    {r : (x: α) → (y : α) → x ∈ xs → y ∈ ys → Bool} (hsz : xs.size = ys.size) {i : Nat} (hi : i ≤ xs.size)
    (w : ∀ j, (hj : j < i) → r xs[j] ys[j] (by grind) (by grind)) : Array.isEqvAux' xs ys hsz r i hi := by
  induction i with
  | zero => simp [Array.isEqvAux']
  | succ i ih =>
    simp only [isEqvAux', Bool.and_eq_true]
    exact ⟨w i (Nat.lt_add_one i), ih _ fun j hj => w j (Nat.lt_add_right 1 hj)⟩

private theorem rel_of_isEqv'  {xs ys : Array α} {r : (x: α) → (y : α) → x ∈ xs → y ∈ ys → Bool} :
    Array.isEqv' xs ys r → ∃ h : xs.size = ys.size, ∀ (i : Nat) (h' : i < xs.size), r (xs[i]) (ys[i]'(h ▸ h')) (by grind) (by grind) := by
  simp only [isEqv']
  split <;> rename_i h
  · exact fun h' => ⟨h, fun i => rel_of_isEqvAux' h (Nat.le_refl ..) h'⟩
  · intro; contradiction

theorem isEqv'_iff_rel {xs ys : Array α} {r} :
    Array.isEqv' xs ys r ↔
      ∃ h : xs.size = ys.size, ∀ (i : Nat) (h' : i < xs.size), r (xs[i]) (ys[i]'(h ▸ h')) (by grind) (by grind) :=
  ⟨rel_of_isEqv', fun ⟨h, w⟩ => by
    simp only [isEqv', ← h, ↓reduceDIte]
    exact isEqvAux'_of_rel h (by simp [h]) w⟩

theorem isEqv'_decide_iff_eq {xs ys : Array α} (inst: (x y : α) → x ∈ xs → y ∈ ys → Decidable (x = y)) :
    Array.isEqv' xs ys (fun x y hx hy => @decide _ (inst x y hx hy)) ↔  xs = ys := by
  grind [isEqv'_iff_rel]

public def instDecidabelEq' (xs ys : Array α) (inst: (x y : α) → x ∈ xs → y ∈ ys → Decidable (x = y)) :
    Decidable (xs = ys) :=
  if h : Array.isEqv' xs ys (fun x y hx hy => @decide _ (inst x y hx hy)) then
    .isTrue ((isEqv'_decide_iff_eq inst).mp h)
  else
    .isFalse (by grind [isEqv'_iff_rel])

end Array

namespace BitVec

@[grind =]
theorem saddOverflow_comm {w : Nat} (x y : BitVec w) :
    x.saddOverflow y = y.saddOverflow x := by
  grind [BitVec.saddOverflow]

@[grind =]
theorem uaddOverflow_comm {w : Nat} (x y : BitVec w) :
    x.uaddOverflow y = y.uaddOverflow x := by
  grind [BitVec.uaddOverflow]

@[grind =]
theorem smulOverflow_comm {w : Nat} (x y : BitVec w) :
    x.smulOverflow y = y.smulOverflow x := by
  grind [BitVec.smulOverflow]

@[grind =]
theorem umulOverflow_comm {w : Nat} (x y : BitVec w) :
    x.umulOverflow y = y.umulOverflow x := by
  grind [BitVec.umulOverflow]

@[veir_bv_normalize]
theorem udiv_one_shl {w₁ w₂ : Nat} (x : BitVec w₁) (k : BitVec w₂) :
    x / 1#w₁ <<< k = x >>> k := by
  rw [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', ← BitVec.twoPow_eq]
  rcases Nat.lt_or_ge k.toNat w₁ with hk | hk
  · exact BitVec.udiv_twoPow_eq_of_lt hk
  · have htw : BitVec.twoPow w₁ k.toNat = 0#w₁ := BitVec.eq_of_toNat_eq (by
      rw [BitVec.toNat_twoPow_of_le hk, BitVec.toNat_ofNat, Nat.zero_mod])
    rw [htw, BitVec.udiv_zero, BitVec.ushiftRight_eq_zero hk]

/-- The heterogeneous-width variant of `toInt_sshiftRight'`, which is only stated for a shift
    amount of the same width as the shifted value. -/
theorem toInt_sshiftRight'' {w₁ w₂ : Nat} (x : BitVec w₁) (k : BitVec w₂) :
    (x.sshiftRight' k).toInt = x.toInt >>> k.toNat := by
  simp

/-- An exact `sdiv` by a power of two (i.e. one where the dividend has no fractional part to
    round, witnessed by `x.smod (2^k) = 0`) agrees with the arithmetic shift `x.sshiftRight' k`.
    `k` must leave room for a sign bit (`k.toNat + 1 < w`, i.e. `2^k` isn't `x`'s own `intMin`),
    matching the range for which `sdivPow2Exact`/`sdivwPow2Exact` are selected. -/
@[veir_bv_normalize_post]
theorem sdiv_one_shl_of_smod_eq_zero {w₁ w₂ : Nat} (x : BitVec w₁) (k : BitVec w₂)
    (hk : k.toNat + 1 < w₁) (h : x.smod ((1#w₁) <<< k) = 0#w₁) :
    x.sdiv ((1#w₁) <<< k) = x.sshiftRight' k := by
  have hy : ((1#w₁) <<< k).toInt = ((2 ^ k.toNat : Nat) : Int) := by
    rw [BitVec.shiftLeft_eq', ← BitVec.twoPow_eq, BitVec.toInt_twoPow, if_neg (by omega),
      if_neg (by omega)]
    exact (Int.natCast_pow 2 k.toNat).symm
  apply BitVec.eq_of_toInt_eq
  have hsmod : x.toInt.fmod ((1#w₁) <<< k).toInt = 0 := by
    rw [← BitVec.toInt_smod, h, BitVec.toInt_zero]
  rw [hy] at hsmod
  rw [BitVec.toInt_sdiv, toInt_sshiftRight'', hy]
  have hnn : (0 : Int) ≤ ((2 ^ k.toNat : Nat) : Int) := Int.natCast_nonneg _
  rw [Int.fmod_eq_emod_of_nonneg _ hnn] at hsmod
  have hdvd : ((2 ^ k.toNat : Nat) : Int) ∣ x.toInt := Int.dvd_of_emod_eq_zero hsmod
  rw [Int.tdiv_eq_ediv_of_dvd hdvd, ← Int.shiftRight_eq_div_pow]
  have hcancel := BitVec.toInt_bmod_cancel (x.sshiftRight' k)
  rwa [toInt_sshiftRight''] at hcancel

/-- The `toInt` of a negated power of two. Unlike `toInt_twoPow`, this needs no case split on
    whether `2^k` is itself `intMin`: negating `intMin` wraps back to `intMin` (`neg_intMin`),
    whose `toInt` is `-2^(w-1)`, i.e. exactly `-2^k` at that boundary too. -/
theorem toInt_neg_one_shl {w₁ w₂ : Nat} (k : BitVec w₂) (hk : k.toNat < w₁) :
    (-((1#w₁) <<< k)).toInt = -((2 ^ k.toNat : Nat) : Int) := by
  have hle : 2 ^ k.toNat ≤ 2 ^ (w₁ - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hlt : 2 ^ k.toNat < 2 ^ w₁ := Nat.pow_lt_pow_right (by omega) hk
  have h2 : 2 ^ (w₁ - 1) * 2 = 2 ^ w₁ := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  have hy : ((1#w₁) <<< k).toNat = 2 ^ k.toNat := by
    rw [BitVec.shiftLeft_eq', ← BitVec.twoPow_eq, BitVec.toNat_twoPow_of_lt hk]
  obtain ⟨q, hq⟩ := Nat.le.dest (Nat.le_of_lt hlt)
  have hsubval : 2 ^ w₁ - 2 ^ k.toNat = q := by omega
  have hneg : (-((1#w₁) <<< k)).toNat = q := by
    rw [BitVec.toNat_neg, hy, Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos w₁) (Nat.two_pow_pos k.toNat)),
      hsubval]
  have hcond : ¬ (2 * (-((1#w₁) <<< k)).toNat < 2 ^ w₁) := by rw [hneg]; omega
  rw [BitVec.toInt_eq_toNat_cond, if_neg hcond, hneg]
  omega

/-- Negative-divisor analogue of `sdiv_one_shl_of_smod_eq_zero`: an exact `sdiv` by `-2^k` agrees
    with the negated arithmetic shift. No bound relating `k` to `w` is needed beyond `k < w`
    (unlike the positive-divisor version): `-2^(w-1)` is itself a valid divisor, since negating
    it wraps back to itself. -/
@[veir_bv_normalize_post]
theorem sdiv_neg_one_shl_of_smod_eq_zero {w₁ w₂ : Nat} (x : BitVec w₁) (k : BitVec w₂)
    (hk : k.toNat < w₁) (h : x.smod (-((1#w₁) <<< k)) = 0#w₁) :
    x.sdiv (-((1#w₁) <<< k)) = -(x.sshiftRight' k) := by
  apply BitVec.eq_of_toInt_eq
  have hsmod : x.toInt.fmod (-((2 ^ k.toNat : Nat) : Int)) = 0 := by
    have hcong := congrArg BitVec.toInt h
    rwa [BitVec.toInt_smod, toInt_neg_one_shl k hk, BitVec.toInt_zero] at hcong
  have hdvd : ((2 ^ k.toNat : Nat) : Int) ∣ x.toInt :=
    Int.neg_dvd.mp (Int.dvd_of_fmod_eq_zero hsmod)
  rw [BitVec.toInt_sdiv, toInt_neg_one_shl k hk, Int.tdiv_neg,
    Int.tdiv_eq_ediv_of_dvd hdvd, ← Int.shiftRight_eq_div_pow,
    BitVec.toInt_neg, toInt_sshiftRight'']

end BitVec

/-- The Hacker's-Delight bias/shift identity underlying `sdivPow2`/`sdivwPow2`: truncating
    division by a positive `p` equals floor division of the dividend biased by `p - 1` when the
    dividend is negative (so the floor rounds toward zero instead of toward `-∞`). -/
theorem Int.tdiv_eq_ediv_add_of_pos {a p : Int} (hp : 0 < p) :
    a.tdiv p = (a + (if a < 0 then p - 1 else 0)) / p := by
  have hpne : p ≠ 0 := by omega
  rw [Int.tdiv_eq_ediv, Int.sign_eq_one_of_pos hp]
  by_cases ha : a < 0
  · rw [if_pos ha]
    by_cases hdvd : p ∣ a
    · rw [if_pos (Or.inr hdvd)]
      obtain ⟨q, hq⟩ := hdvd
      subst hq
      have hrw : p * q + (p - 1) = (p - 1) + q * p := by
        rw [Int.mul_comm q p, Int.add_comm]
      rw [hrw, Int.add_mul_ediv_right (p - 1) q hpne]
      have h1 : (0:Int) ≤ p - 1 := by omega
      have h2 : p - 1 < p := by omega
      rw [Int.ediv_eq_zero_of_lt h1 h2, Int.mul_ediv_cancel_left q hpne]
      omega
    · have hnotor : ¬ (0 ≤ a ∨ p ∣ a) := fun h => h.elim (fun h0 => absurd h0 (by omega)) hdvd
      rw [if_neg hnotor]
      have hr : a % p + a / p * p = a := Int.emod_add_ediv_mul a p
      have hr0 : 0 ≤ a % p := Int.emod_nonneg a hpne
      have hrlt : a % p < p := Int.emod_lt_of_pos a hp
      have hrne : a % p ≠ 0 := fun h => hdvd (Int.dvd_of_emod_eq_zero h)
      have key : a + (p - 1) = (a % p - 1) + (a / p + 1) * p := by
        have expand : (a / p + 1) * p = a / p * p + p := by
          rw [Int.add_mul, Int.one_mul]
        rw [expand]
        omega
      rw [key, Int.add_mul_ediv_right (a % p - 1) (a / p + 1) hpne]
      have h1 : (0:Int) ≤ a % p - 1 := by omega
      have h2 : a % p - 1 < p := by omega
      rw [Int.ediv_eq_zero_of_lt h1 h2]
      simp
  · have haux : 0 ≤ a ∨ p ∣ a := Or.inl (by omega)
    rw [if_neg ha, if_pos haux, Int.add_zero, Int.add_zero]

/-- A shifted-in-from-the-left all-ones mask (`(2^w - 1) >>> (w - k)`, i.e. the top `w - k` bits
    of `allOnes w` cleared) is exactly the `k`-bit all-ones mask `2^k - 1`. Used to compute the
    Hacker's-Delight sign-extension bias as a plain arithmetic shift. -/
theorem Nat.shiftRight_two_pow_sub_one {w k : Nat} (hk : k < w) :
    (2 ^ w - 1) >>> (w - k) = 2 ^ k - 1 := by
  rw [Nat.shiftRight_eq_div_pow]
  have hsplit : w - k + k = w := by omega
  have hpow : 2 ^ (w - k) * 2 ^ k = 2 ^ w := by
    rw [← Nat.pow_add, hsplit]
  have hle : 2 ^ (w - k) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
  have hge2 : 1 ≤ 2 ^ (w - k) := Nat.one_le_two_pow
  have heq : 2 ^ w - 1 = 2 ^ (w - k) * (2 ^ k - 1) + (2 ^ (w - k) - 1) := by
    rw [Nat.mul_sub_one, hpow]
    omega
  rw [heq, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]

namespace BitVec

/-- The bias term added before the arithmetic shift in the Hacker's-Delight bias/shift sequence
    for signed division by `2^k`: `2^k - 1` when `x` is negative, `0` otherwise, computed as a
    plain arithmetic-then-logical shift (mirroring `sign := srai 63 x; corr := srli (64-k) sign`
    in the `sdivPow2`/`sdivwPow2` lowering). -/
theorem toNat_sign_mask_shift {w₁ : Nat} (x : BitVec w₁) (k : Nat) (hk : k < w₁) :
    (x.sshiftRight (w₁ - 1) >>> (w₁ - k)).toNat = if x.msb then 2 ^ k - 1 else 0 := by
  have hdouble : 2 ^ (w₁ - 1) * 2 = 2 ^ w₁ := by
    rw [← Nat.pow_succ]
    congr 1
    omega
  rw [BitVec.toNat_ushiftRight]
  by_cases hmsb : x.msb = true
  · rw [if_pos hmsb, BitVec.toNat_sshiftRight_of_msb_true hmsb]
    have hxge : 2 ^ (w₁ - 1) ≤ x.toNat := BitVec.le_toNat_of_msb_true hmsb
    have hxlt : x.toNat < 2 ^ w₁ := x.isLt
    have hzero : (2 ^ w₁ - 1 - x.toNat) >>> (w₁ - 1) = 0 := by
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega)]
    rw [hzero, Nat.sub_zero]
    exact Nat.shiftRight_two_pow_sub_one hk
  · rw [if_neg hmsb]
    have hmsb' : x.msb = false := by simpa using hmsb
    rw [BitVec.toNat_sshiftRight_of_msb_false hmsb']
    have hxlt : x.toNat < 2 ^ (w₁ - 1) := BitVec.toNat_lt_of_msb_false hmsb'
    have hinner : x.toNat >>> (w₁ - 1) = 0 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_eq_of_lt hxlt
    rw [hinner, Nat.zero_shiftRight]

/-- `sdivPow2` (general, non-`exact` positive divisor): dividing by `2^k` equals arithmetic-shifting
    `x` biased by `2^k - 1` when `x` is negative (so truncation rounds toward zero instead of
    toward `-∞`). Unlike `sdiv_one_shl_of_smod_eq_zero`, this holds for *every* `x` (no `smod = 0`
    side condition), but — like it — needs `k.toNat + 1 < w₁` to keep `2^k` off `x`'s own `intMin`.
    Stated with plain `Nat`-indexed shifts; see `sdiv_one_shl_eq_biased_sshiftRight_bv` for the
    `BitVec`-typed-shift-amount form that `bv_decide` can actually bitblast. -/
theorem sdiv_one_shl_eq_biased_sshiftRight {w₁ w₂ : Nat} (x : BitVec w₁) (k : BitVec w₂)
    (hk : k.toNat + 1 < w₁) :
    x.sdiv ((1#w₁) <<< k) =
      (x + (x.sshiftRight (w₁ - 1) >>> (w₁ - k.toNat))).sshiftRight' k := by
  have hy : ((1#w₁) <<< k).toInt = ((2 ^ k.toNat : Nat) : Int) := by
    rw [BitVec.shiftLeft_eq', ← BitVec.twoPow_eq, BitVec.toInt_twoPow, if_neg (by omega),
      if_neg (by omega)]
    exact (Int.natCast_pow 2 k.toNat).symm
  generalize hcorr_def : x.sshiftRight (w₁ - 1) >>> (w₁ - k.toNat) = corr
  have hcorrNat : corr.toNat = if x.msb then 2 ^ k.toNat - 1 else 0 := by
    rw [← hcorr_def]
    exact toNat_sign_mask_shift x k.toNat (by omega)
  have hple : (2:Nat) ^ k.toNat ≤ 2 ^ (w₁ - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hcorrInt : corr.toInt = if x.toInt < 0 then ((2 ^ k.toNat : Nat) : Int) - 1 else 0 := by
    rw [BitVec.msb_eq_toInt] at hcorrNat
    simp only [decide_eq_true_eq] at hcorrNat
    by_cases hx : x.toInt < 0
    · rw [if_pos hx] at hcorrNat
      rw [if_pos hx]
      have hlt : 2 * corr.toNat < 2 ^ w₁ := by
        rw [hcorrNat]
        have : 2 ^ (w₁ - 1) * 2 = 2 ^ w₁ := by
          rw [← Nat.pow_succ]; congr 1; omega
        omega
      rw [BitVec.toInt_eq_toNat_of_lt hlt, hcorrNat]
      exact Int.natCast_sub Nat.one_le_two_pow
    · rw [if_neg hx] at hcorrNat
      rw [if_neg hx]
      have hlt : 2 * corr.toNat < 2 ^ w₁ := by
        rw [hcorrNat]
        have := Nat.two_pow_pos w₁
        omega
      rw [BitVec.toInt_eq_toNat_of_lt hlt, hcorrNat]
      rfl
  have hsum : (x + corr).toInt = x.toInt + corr.toInt := by
    have hpleMul : (2:Nat) ^ k.toNat * 2 ≤ 2 ^ w₁ := by
      have h1 : 2 ^ (k.toNat + 1) ≤ 2 ^ w₁ := Nat.pow_le_pow_right (by omega) (by omega)
      rwa [Nat.pow_succ] at h1
    have hpleInt : ((2 ^ k.toNat : Nat) : Int) * 2 ≤ ((2 ^ w₁ : Nat) : Int) := by
      exact_mod_cast hpleMul
    rw [BitVec.toInt_add]
    have hxlt := BitVec.toInt_lt (x := x)
    have hxge := BitVec.le_toInt (x := x)
    have hdoubleNat : (2:Nat) ^ (w₁ - 1) * 2 = 2 ^ w₁ := by
      rw [← Nat.pow_succ]; congr 1; omega
    have hdouble : (2:Int) ^ (w₁ - 1) * 2 = ((2 ^ w₁ : Nat) : Int) := by exact_mod_cast hdoubleNat
    rw [hcorrInt]
    by_cases hx : x.toInt < 0
    · rw [if_pos hx]
      have hb1 : (0:Int) ≤ ((2 ^ k.toNat : Nat) : Int) - 1 := by
        have : (1:Int) ≤ ((2 ^ k.toNat : Nat) : Int) := by exact_mod_cast Nat.one_le_two_pow
        omega
      apply Int.bmod_eq_of_le <;> omega
    · rw [if_neg hx]
      simp only [Int.add_zero]
      apply Int.bmod_eq_of_le <;> omega
  have hppos : (0:Int) < ((2 ^ k.toNat : Nat) : Int) := by
    exact_mod_cast Nat.two_pow_pos k.toNat
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sdiv, hy, Int.tdiv_eq_ediv_add_of_pos hppos, ← hcorrInt, ← hsum,
    ← Int.shiftRight_eq_div_pow, ← toInt_sshiftRight'']
  exact BitVec.toInt_bmod_cancel _

/-- Negative-divisor analogue of `sdiv_one_shl_eq_biased_sshiftRight` (`sdivPow2`, negative
    divisor): negate the biased-shift result. Like `sdiv_neg_one_shl_of_smod_eq_zero`, no bound
    relating `k` to `w` is needed beyond `k < w`: `-2^(w-1)` is itself a valid divisor here too.
    Stated with plain `Nat`-indexed shifts; see `sdiv_neg_one_shl_eq_neg_biased_sshiftRight_bv`. -/
theorem sdiv_neg_one_shl_eq_neg_biased_sshiftRight {w₁ w₂ : Nat} (x : BitVec w₁) (k : BitVec w₂)
    (hk : k.toNat < w₁) :
    x.sdiv (-((1#w₁) <<< k)) =
      -((x + (x.sshiftRight (w₁ - 1) >>> (w₁ - k.toNat))).sshiftRight' k) := by
  have hz : (-((1#w₁) <<< k)).toInt = -((2 ^ k.toNat : Nat) : Int) := toInt_neg_one_shl k hk
  generalize hcorr_def : x.sshiftRight (w₁ - 1) >>> (w₁ - k.toNat) = corr
  have hcorrNat : corr.toNat = if x.msb then 2 ^ k.toNat - 1 else 0 := by
    rw [← hcorr_def]
    exact toNat_sign_mask_shift x k.toNat hk
  have hple : (2:Nat) ^ k.toNat ≤ 2 ^ (w₁ - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hcorrInt : corr.toInt = if x.toInt < 0 then ((2 ^ k.toNat : Nat) : Int) - 1 else 0 := by
    rw [BitVec.msb_eq_toInt] at hcorrNat
    simp only [decide_eq_true_eq] at hcorrNat
    by_cases hx : x.toInt < 0
    · rw [if_pos hx] at hcorrNat
      rw [if_pos hx]
      have hlt : 2 * corr.toNat < 2 ^ w₁ := by
        rw [hcorrNat]
        have : 2 ^ (w₁ - 1) * 2 = 2 ^ w₁ := by
          rw [← Nat.pow_succ]; congr 1; omega
        omega
      rw [BitVec.toInt_eq_toNat_of_lt hlt, hcorrNat]
      exact Int.natCast_sub Nat.one_le_two_pow
    · rw [if_neg hx] at hcorrNat
      rw [if_neg hx]
      have hlt : 2 * corr.toNat < 2 ^ w₁ := by
        rw [hcorrNat]
        have := Nat.two_pow_pos w₁
        omega
      rw [BitVec.toInt_eq_toNat_of_lt hlt, hcorrNat]
      rfl
  have hsum : (x + corr).toInt = x.toInt + corr.toInt := by
    have hpleMul : (2:Nat) ^ k.toNat * 2 ≤ 2 ^ w₁ := by
      have h1 : 2 ^ (w₁ - 1) * 2 = 2 ^ w₁ := by rw [← Nat.pow_succ]; congr 1; omega
      calc (2:Nat) ^ k.toNat * 2 ≤ 2 ^ (w₁ - 1) * 2 := Nat.mul_le_mul_right 2 hple
        _ = 2 ^ w₁ := h1
    have hpleInt : ((2 ^ k.toNat : Nat) : Int) * 2 ≤ ((2 ^ w₁ : Nat) : Int) := by
      exact_mod_cast hpleMul
    rw [BitVec.toInt_add]
    have hxlt := BitVec.toInt_lt (x := x)
    have hxge := BitVec.le_toInt (x := x)
    have hdoubleNat : (2:Nat) ^ (w₁ - 1) * 2 = 2 ^ w₁ := by
      rw [← Nat.pow_succ]; congr 1; omega
    have hdouble : (2:Int) ^ (w₁ - 1) * 2 = ((2 ^ w₁ : Nat) : Int) := by exact_mod_cast hdoubleNat
    rw [hcorrInt]
    by_cases hx : x.toInt < 0
    · rw [if_pos hx]
      have hb1 : (0:Int) ≤ ((2 ^ k.toNat : Nat) : Int) - 1 := by
        have : (1:Int) ≤ ((2 ^ k.toNat : Nat) : Int) := by exact_mod_cast Nat.one_le_two_pow
        omega
      apply Int.bmod_eq_of_le <;> omega
    · rw [if_neg hx]
      simp only [Int.add_zero]
      apply Int.bmod_eq_of_le <;> omega
  have hppos : (0:Int) < ((2 ^ k.toNat : Nat) : Int) := by
    exact_mod_cast Nat.two_pow_pos k.toNat
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sdiv, hz, Int.tdiv_neg, Int.tdiv_eq_ediv_add_of_pos hppos, ← hcorrInt, ← hsum,
    ← Int.shiftRight_eq_div_pow, ← toInt_sshiftRight'', BitVec.toInt_neg]

/-- `(-v).toNat` in terms of `v.toNat`, for `v` nonzero (no `% 2^w` needed: `2^w - v.toNat` is
    already in range). -/
theorem toNat_neg_eq_sub {w : Nat} (v : BitVec w) (hv : 0 < v.toNat) :
    (-v).toNat = 2 ^ w - v.toNat := by
  rw [BitVec.toNat_neg]
  exact Nat.mod_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos w) hv)

/-- `BitVec`-typed-shift-amount form of `sdiv_one_shl_eq_biased_sshiftRight`, matching the shape
    `sdivPow2`/`sdivwPow2` actually lower to: RISC-V immediates are register-width-sized (`w₂` bits
    for a `2^w₂`-bit register), so the source's `srai (w₁-1) x`/`srli (w₁-k) sign` are literally
    `sshiftRight' (-1)`/`ushiftRight (-k)` once the `w₁`-valued immediate wraps to `0` in `w₂` bits.
    `bv_decide` can only bitblast a shift by a genuine `BitVec` value (not a symbolic `Nat`
    expression like `w₁ - k.toNat`), so this is the form registered for `veir_bv_normalize`. -/
@[veir_bv_normalize_post]
theorem sdiv_one_shl_eq_biased_sshiftRight_bv {w₁ w₂ : Nat} (x : BitVec w₁) (k : BitVec w₂)
    (hw2 : 0 < w₂) (hk0 : 0 < k.toNat) (hk : k.toNat + 1 < w₁) (hw : w₁ = 2 ^ w₂) :
    x.sdiv ((1#w₁) <<< k) =
      (x + (x.sshiftRight' (-1 : BitVec w₂) >>> (-k))).sshiftRight' k := by
  have h1 : (1 : BitVec w₂).toNat = 1 := BitVec.toNat_one hw2
  have heq1 : (-1 : BitVec w₂).toNat = w₁ - 1 := by
    rw [toNat_neg_eq_sub _ (by omega), hw, h1]
  have heq2 : (-k : BitVec w₂).toNat = w₁ - k.toNat := by
    rw [toNat_neg_eq_sub _ hk0, hw]
  show x.sdiv ((1#w₁) <<< k) =
    (x + (x.sshiftRight (-1 : BitVec w₂).toNat >>> (-k : BitVec w₂).toNat)).sshiftRight k.toNat
  rw [heq1, heq2]
  exact sdiv_one_shl_eq_biased_sshiftRight x k hk

/-- `BitVec`-typed-shift-amount form of `sdiv_neg_one_shl_eq_neg_biased_sshiftRight`; see
    `sdiv_one_shl_eq_biased_sshiftRight_bv` for why this form (rather than the `Nat`-indexed one)
    is what gets registered for `veir_bv_normalize`. -/
@[veir_bv_normalize_post]
theorem sdiv_neg_one_shl_eq_neg_biased_sshiftRight_bv {w₁ w₂ : Nat} (x : BitVec w₁) (k : BitVec w₂)
    (hw2 : 0 < w₂) (hk0 : 0 < k.toNat) (hk : k.toNat < w₁) (hw : w₁ = 2 ^ w₂) :
    x.sdiv (-((1#w₁) <<< k)) =
      -((x + (x.sshiftRight' (-1 : BitVec w₂) >>> (-k))).sshiftRight' k) := by
  have h1 : (1 : BitVec w₂).toNat = 1 := BitVec.toNat_one hw2
  have heq1 : (-1 : BitVec w₂).toNat = w₁ - 1 := by
    rw [toNat_neg_eq_sub _ (by omega), hw, h1]
  have heq2 : (-k : BitVec w₂).toNat = w₁ - k.toNat := by
    rw [toNat_neg_eq_sub _ hk0, hw]
  show x.sdiv (-((1#w₁) <<< k)) =
    -((x + (x.sshiftRight (-1 : BitVec w₂).toNat >>> (-k : BitVec w₂).toNat)).sshiftRight k.toNat)
  rw [heq1, heq2]
  exact sdiv_neg_one_shl_eq_neg_biased_sshiftRight x k hk

/-- When `x` is nonnegative, `sdiv_one_shl_eq_biased_sshiftRight`'s correction term is always `0`,
    so `x.sdiv (2^k) = x.sshiftRight' k` outright — and unlike the general lemma, this needs no
    bound on `k` at all: at the `k = 63` boundary (`2^k` wraps to `intMin`), both sides are
    separately `0` (`x.toNat < 2^63` forces the shift to `0`, and `x ≠ intMin` forces the `sdiv`
    to `0` too, via `BitVec.sdiv_intMin`). -/
theorem sdiv_one_shl_eq_sshiftRight_of_msb_false (x : BitVec 64) (k : BitVec 6)
    (hx : x.msb = false) :
    x.sdiv ((1#64) <<< k) = x.sshiftRight' k := by
  by_cases hk : k.toNat + 1 < 64
  · have hcorr0 : x.sshiftRight 63 >>> (64 - k.toNat) = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [toNat_sign_mask_shift x k.toNat (by omega), if_neg (by simp [hx])]
      rfl
    rw [sdiv_one_shl_eq_biased_sshiftRight x k hk]
    show (x + (x.sshiftRight (63 : Nat) >>> (64 - k.toNat))).sshiftRight k.toNat =
      x.sshiftRight k.toNat
    rw [hcorr0, BitVec.add_zero]
  · have hk63 : k = (-1 : BitVec 6) := by bv_omega
    subst hk63
    have hy : (1#64) <<< (-1 : BitVec 6) = BitVec.intMin 64 := by
      apply BitVec.eq_of_toNat_eq
      decide
    rw [hy, BitVec.sdiv_intMin]
    have hxne : x ≠ BitVec.intMin 64 := by
      intro h; rw [h] at hx; simp [BitVec.msb_intMin] at hx
    rw [if_neg hxne]
    apply BitVec.eq_of_toNat_eq
    show (0 : BitVec 64).toNat = (x.sshiftRight (-1 : BitVec 6).toNat).toNat
    rw [BitVec.toNat_sshiftRight_of_msb_false hx]
    have heq : (-1 : BitVec 6).toNat = 63 := by decide
    rw [heq]
    have hxlt : x.toNat < 2 ^ 63 := BitVec.toNat_lt_of_msb_false hx
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (by omega)]
    rfl

/-- `sdiv_one_shl_eq_biased_sshiftRight_bv`, specialized to the `i64` register width (`w₁ = 64`,
    `w₂ = 6`) and restated as an `if` on `x.msb` instead of always adding the (possibly-zero)
    correction term: whenever the correction isn't needed the RHS is a bare `sshiftRight'`, no
    `add` required — that's the `x.msb = false` case (any `k`, via
    `sdiv_one_shl_eq_sshiftRight_of_msb_false`) and the `k = 0` case (dividing by `1` is always
    exact, regardless of sign). The only case that can't be phrased as a shift is `x.msb = true`
    at `k = 63`, where `2^k` wraps to `intMin` and the identity genuinely doesn't hold (a real
    counterexample: `x = intMin` gives `sdiv = 1` but the shift form gives `-1`); there the `if`
    resolves to `BitVec.sdiv_intMin`'s closed form directly, so the RHS never needs `sdiv` at all. -/
@[veir_bv_normalize_post]
theorem sdiv_one_shl_eq_ite_sshiftRight (x : BitVec 64) (k : BitVec 6) :
    x.sdiv ((1#64) <<< k) =
      if x.msb then
        if k = 0 then
          x.sshiftRight' k
        else if k ≠ (-1 : BitVec 6) then
          (x + (x.sshiftRight' (-1 : BitVec 6) >>> (-k))).sshiftRight' k
        else
          if x = BitVec.intMin 64 then 1#64 else 0#64
      else
        x.sshiftRight' k := by
  by_cases hx : x.msb
  · rw [if_pos hx]
    by_cases hk0 : k = 0
    · rw [if_pos hk0, hk0]
      simp [BitVec.sshiftRight_eq', BitVec.sdiv_one]
    · rw [if_neg hk0]
      by_cases hk63 : k ≠ (-1 : BitVec 6)
      · rw [if_pos hk63]
        have hk0' : 0 < k.toNat := by bv_omega
        have hk' : k.toNat + 1 < 64 := by bv_omega
        have h1 : (1 : BitVec 6).toNat = 1 := BitVec.toNat_one (by decide)
        have heq1 : (-1 : BitVec 6).toNat = 63 := by
          rw [toNat_neg_eq_sub _ (by omega), h1]
        have heq2 : (-k : BitVec 6).toNat = 64 - k.toNat := by
          rw [toNat_neg_eq_sub _ hk0']
        show x.sdiv ((1#64) <<< k) =
          (x + (x.sshiftRight (-1 : BitVec 6).toNat >>> (-k : BitVec 6).toNat)).sshiftRight k.toNat
        rw [heq1, heq2]
        exact sdiv_one_shl_eq_biased_sshiftRight x k hk'
      · rw [if_neg hk63]
        have hk63' : k = (-1 : BitVec 6) := Decidable.not_not.mp hk63
        have hy : (1#64) <<< k = BitVec.intMin 64 := by rw [hk63']; decide
        rw [hy, BitVec.sdiv_intMin]
  · rw [if_neg hx]
    exact sdiv_one_shl_eq_sshiftRight_of_msb_false x k (by simpa using hx)

/-- Negative-divisor analogue of `sdiv_one_shl_eq_sshiftRight_of_msb_false`: when `x` is
    nonnegative, `sdiv_neg_one_shl_eq_neg_biased_sshiftRight`'s correction term is always `0`, for
    *any* `k` — unlike the positive-divisor case, there's no `k = 63` boundary to worry about here,
    since `-2^63` is itself a valid divisor (negating `intMin` just gives `intMin` back). -/
theorem sdiv_neg_one_shl_eq_neg_sshiftRight_of_msb_false (x : BitVec 64) (k : BitVec 6)
    (hx : x.msb = false) :
    x.sdiv (-((1#64) <<< k)) = -(x.sshiftRight' k) := by
  have hk : k.toNat < 64 := k.isLt
  have hcorr0 : x.sshiftRight 63 >>> (64 - k.toNat) = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_sign_mask_shift x k.toNat (by omega), if_neg (by simp [hx])]
    rfl
  rw [sdiv_neg_one_shl_eq_neg_biased_sshiftRight x k hk, hcorr0, BitVec.add_zero]

/-- Negative-divisor analogue of `sdiv_one_shl_eq_ite_sshiftRight`. Simpler than the positive
    case: there's no `sdiv` fallback branch needed at all, since `sdiv_neg_one_shl_eq_neg_biased_sshiftRight`
    already holds for every `k` (no `k = 63` exclusion) — the only special case is `k = 0`
    (dividing by `-1` is always exact, via `BitVec.sdiv_neg`/`BitVec.sdiv_one`), where the
    correction term isn't well-defined as written (`-k = 0` shifts by `0` instead of the intended
    "shift out everything"), so it's spelled out directly rather than going through the general
    correction formula. -/
@[veir_bv_normalize_post]
theorem sdiv_neg_one_shl_eq_ite_sshiftRight (x : BitVec 64) (k : BitVec 6) :
    x.sdiv (-((1#64) <<< k)) =
      if x.msb then
        if k = 0 then
          -(x.sshiftRight' k)
        else
          -((x + (x.sshiftRight' (-1 : BitVec 6) >>> (-k))).sshiftRight' k)
      else
        -(x.sshiftRight' k) := by
  by_cases hx : x.msb
  · rw [if_pos hx]
    by_cases hk0 : k = 0
    · rw [if_pos hk0, hk0]
      have hy : (-((1#64) <<< (0 : BitVec 6))) = (-1 : BitVec 64) := by simp
      rw [hy, BitVec.sdiv_neg (by decide)]
      simp [BitVec.sdiv_one, BitVec.sshiftRight_eq']
    · rw [if_neg hk0]
      have hk0' : 0 < k.toNat := by bv_omega
      have hk' : k.toNat < 64 := k.isLt
      have h1 : (1 : BitVec 6).toNat = 1 := BitVec.toNat_one (by decide)
      have heq1 : (-1 : BitVec 6).toNat = 63 := by
        rw [toNat_neg_eq_sub _ (by omega), h1]
      have heq2 : (-k : BitVec 6).toNat = 64 - k.toNat := by
        rw [toNat_neg_eq_sub _ hk0']
      show x.sdiv (-((1#64) <<< k)) =
        -((x + (x.sshiftRight (-1 : BitVec 6).toNat >>> (-k : BitVec 6).toNat)).sshiftRight k.toNat)
      rw [heq1, heq2]
      exact sdiv_neg_one_shl_eq_neg_biased_sshiftRight x k hk'
  · rw [if_neg hx]
    exact sdiv_neg_one_shl_eq_neg_sshiftRight_of_msb_false x k (by simpa using hx)

@[veir_bv_normalize]
theorem setWidth_ofInt_32_64 (v : Int) :
    BitVec.setWidth 32 (BitVec.ofInt 64 v) = BitVec.ofInt 32 v := by
  rw [← BitVec.toInt_inj]
  simp only [BitVec.toInt_setWidth, BitVec.toNat_ofInt, Nat.reducePow, Int.cast_ofNat_Int, Int.ofNat_toNat,
    BitVec.toInt_ofInt]
  grind

@[veir_bv_normalize]
theorem setWidth_ofInt_8_64 (v : Int) :
    BitVec.setWidth 8 (BitVec.ofInt 64 v) = BitVec.ofInt 8 v := by
  rw [← BitVec.toInt_inj]
  simp only [BitVec.toInt_setWidth, BitVec.toNat_ofInt, Nat.reducePow, Int.cast_ofNat_Int, Int.ofNat_toNat,
    BitVec.toInt_ofInt]
  grind

@[veir_bv_normalize]
theorem setWidth_ofInt_1_64 (v : Int) :
    BitVec.setWidth 1 (BitVec.ofInt 64 v) = BitVec.ofInt 1 v := by
  rw [← BitVec.toInt_inj]
  simp only [BitVec.toInt_setWidth, BitVec.toNat_ofInt, Nat.reducePow, Int.cast_ofNat_Int, Int.ofNat_toNat,
    BitVec.toInt_ofInt]
  grind

@[grind =]
theorem eq_setWidth_zero (x : BitVec w) :
    x = 0#w → x.setWidth w' = 0#w' := by
  grind

end BitVec

namespace Rat

/-- `2` raised to a (possibly negative) integer power as a `Rat`. -/
def twoPow (k : Int) : Rat := 2 ^ k

end Rat
