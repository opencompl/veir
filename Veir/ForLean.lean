module

public import Std.Data.ExtHashSet

public section

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

@[inline]
def ByteArray.getD (ba : ByteArray) (i : Nat) (default : UInt8) : UInt8 :=
  if h : i < ba.size then ba[i] else default

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

set_option warn.sorry false in
@[grind .]
theorem Array.back_popWhile {as : Array α} {p : α → Bool} (h : 0 < (as.popWhile p).size) :
    p ((as.popWhile p).back h) = false := by
  sorry

theorem Array.reverse_singleton (a : α) :
    #[a].reverse = #[a] := by
  simp

theorem List.idxOf_getElem [DecidableEq α] {l : List α} (H : Nodup l) (i : Nat) (h : i < l.length) :
    idxOf l[i] l = i := by
  induction l generalizing i <;> grind

theorem List.getElem?_idxOf [DecidableEq α] {l : List α} (h : l.idxOf x < l.length) :
    l[l.idxOf x] = x := by
  induction l <;> grind

@[simp, grind =]
theorem Array.getElem?_idxOf [DecidableEq α] {l : Array α} (h : l.idxOf x < l.size) :
    l[l.idxOf x]? = some x := by
  rcases l; grind [List.getElem?_idxOf]

@[simp, grind =]
theorem Array.getElem_idxOf [DecidableEq α] {l : Array α} (h : l.idxOf x < l.size) :
    l[l.idxOf x] = x := by
  rcases l; grind [List.getElem?_idxOf]

@[simp, grind =]
theorem Array.toList_erase [BEq α] (l : Array α) (a : α) :
    (l.erase a).toList = l.toList.erase a := by
  cases l; grind

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

end

section ranges

open Std

@[grind=]
theorem mem_range_nat (i: Nat) (r: Rco Nat) : (i ∈ r) ↔ r.lower ≤ i ∧ i < r.upper := by
  simp only [Membership.mem]

end ranges
