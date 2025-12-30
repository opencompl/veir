module

public section

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

section ranges

open Std

@[grind=]
theorem mem_range_nat (i: Nat) (r: Rco Nat) : (i ∈ r) ↔ r.lower ≤ i ∧ i < r.upper := by
  simp only [Membership.mem]

end ranges
