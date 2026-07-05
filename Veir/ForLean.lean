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

@[veir_bv_normalize]
theorem setWidth_ofInt_32_64 (v : Int) :
    BitVec.setWidth 32 (BitVec.ofInt 64 v) = BitVec.ofInt 32 v := by
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
