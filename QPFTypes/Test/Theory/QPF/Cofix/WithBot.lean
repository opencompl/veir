module

import QPFTypes

/-!
# `partial_fixpoint` on a `CofixWithBot` type

Streams, `StreamF α S = α × S`, have no shape free of `α`, so `Cofix StreamF` has no
`HasBot` instance without assuming `α` inhabited. `CofixWithBot StreamF` has one regardless:
the result is the type of *partial* streams, where `⊥` cuts the stream off.
-/

namespace QPFTypes.Test.WithBot

open QPF Lean.Order

@[qpf] def StreamF (α S : liveParam Type) := α × S



/-- Possibly-partial streams. -/
def PStream (a : Type) : Type :=
  CofixWithBot (@TypeFun.ofCurried 2 StreamF) #t[a]
  deriving CCPO

variable {a b : Type}

def PStream.cons (x : a) (xs : PStream a) : PStream a :=
  Cofix.mk (Comp.mk (some (x, xs)))

def PStream.dest (xs : PStream a) : Option (a × PStream a) :=
  Cofix.dest xs

/-- `codef` unfolds `Stream.cons` into `Cofix.mk (x, _)`, and translates that into
`CofixWithBot.mk (x, _)`; this lemma makes the latter monotone. -/
@[partial_fixpoint_monotone]
theorem PStream.mk_mono {γ : Type} [PartialOrder γ] (x : a) (f : γ → PStream a)
    (hf : monotone f) :
    monotone (fun y =>
      CofixWithBot.mk (F := @TypeFun.ofCurried 2 StreamF) (α := #t[a]) (x, f y)) :=
  CofixWithBot.mk_map_mono ((x, ()) : StreamF a Unit) (fun y _ => f y)
    fun y₁ y₂ h _ => hf y₁ y₂ h

@[simp, grind =]
theorem PStream.dest_cons (x : a) (xs : PStream a) :
    (Cofix.dest (cons x xs)).get = some (x, xs) := by
  simp [cons]; rfl

@[partial_fixpoint_monotone]
theorem PStream.cons_mono {γ : Type} [PartialOrder γ] (x : a) (f : γ → PStream a)
    (hf : monotone f) : monotone (fun y => PStream.cons x (f y)) := by
  apply Cofix.mk_map_mono
    (Comp.mk (some (x, ())) : (@TypeFun.ofCurried 2 StreamF).WithBot (#t[a] ::: Unit))
    (fun y _ => f y)
  exact fun y₁ y₂ h _ => hf y₁ y₂ h

/-- Not productive: `⊥`. -/
def PStream.spin : PStream a := PStream.spin
partial_fixpoint

/-- Drops elements until `p` holds; not productive. -/
def PStream.dropUntil (p : a → Bool) (xs : PStream a) : PStream a :=
  match PStream.dest xs with
  | none => Cofix.bot _
  | some (x, xs') => if p x then .cons x xs' else PStream.dropUntil p xs'
partial_fixpoint


/-! ## Casting a total stream out of `CofixWithBot` -/

/-- Total streams. -/
def Stream (a : Type) : Type :=
  Cofix (@TypeFun.ofCurried 2 StreamF) #t[a]

@[qpf_elim]
def Stream.head (xs : Stream a) : a := (Cofix.dest xs).1

@[qpf_elim]
def Stream.tail (xs : Stream a) : Stream a := (Cofix.dest xs).2

/-! `@[qpf_elim]` defines the partial versions of `Stream.head` and `Stream.tail`. -/

/--
info: @Stream.tail.__partial : {a : Type} →
  CofixWithBot (TypeFun.ofCurried StreamF) (TypeVec.nil ::: a) →
    CofixWithBot (TypeFun.ofCurried StreamF) (TypeVec.nil ::: a)
-/
#guard_msgs in
#check @Stream.tail.__partial

/--
info: @Stream.tail.__partial_mono : ∀ {δ : Sort u_1} [inst : PartialOrder δ] {a : Type}
  (xs_fn : δ → CofixWithBot (TypeFun.ofCurried StreamF) (TypeVec.nil ::: a)),
  monotone xs_fn → monotone fun z => Stream.tail.__partial (xs_fn z)
-/
#guard_msgs in
#check @Stream.tail.__partial_mono

/--
info: @Stream.tail.__partial_ofCofix : ∀ {a : Type} (xs : Stream a),
  CofixWithBot.ofCofix xs.tail = Stream.tail.__partial (CofixWithBot.ofCofix xs)
-/
#guard_msgs in
#check @Stream.tail.__partial_ofCofix

-- `Stream.head` returns an `a`, which has no `⊥`: its partial version is in
-- continuation-passing style.
/--
info: @Stream.head.__partial : {a : Type} →
  CofixWithBot (TypeFun.ofCurried StreamF) (TypeVec.nil ::: a) →
    {m : Nat} → {G : TypeFun (m + 1)} → [inst : QPF G] → {β : TypeVec m} → (a → CofixWithBot G β) → CofixWithBot G β
-/
#guard_msgs in
#check @Stream.head.__partial

/--
info: @Stream.head.__partial_mono : ∀ {δ : Sort u_2} [inst : PartialOrder δ] {a : Type}
  (xs_fn : δ → CofixWithBot (TypeFun.ofCurried StreamF) (TypeVec.nil ::: a)),
  monotone xs_fn →
    ∀ {m : Nat} {G : TypeFun (m + 1)} [inst_1 : QPF G] {β : TypeVec m} [inst_2 : IsPolynomial G]
      (k_fn : δ → a → CofixWithBot G β), monotone k_fn → monotone fun z => Stream.head.__partial (xs_fn z) (k_fn z)
-/
#guard_msgs in
#check @Stream.head.__partial_mono

def Stream.cons (x : a) (xs : Stream a) : Stream a := Cofix.mk (x, xs)

@[simp, grind =]
theorem Stream.head_cons : (cons x xs).head = x := by
  simp [cons, head]
  erw [Cofix.dest_mk]
  -- FIXME: why does this need `erw` rather than just `rw`?

@[simp, grind =]
theorem Stream.tail_cons : (cons x xs).tail = xs := by
  simp [cons, tail]
  erw [Cofix.dest_mk]
  -- FIXME: why does this need `erw` rather than just `rw`?

/-- Bisimulation for total streams: related streams have equal heads and related tails. -/
theorem Stream.bisim (R : Stream α → Stream α → Prop)
    (hR : ∀ xs ys, R xs ys → xs.head = ys.head ∧ R xs.tail ys.tail) :
    ∀ {xs ys}, R xs ys → xs = ys := by
  intro xs ys h
  apply Cofix.bisim_rel R _ xs ys h
  intro (xs : Stream α) (ys : Stream α) h
  obtain ⟨hh, ht⟩ := hR xs ys h
  have : Quot.mk R xs.tail = Quot.mk R ys.tail := Quot.sound ht
  show (xs.head, Quot.mk R xs.tail) = (ys.head, Quot.mk R ys.tail)
  rw [hh, this]

/-! ### repeat -/

def PStream.repeat (x : a) : PStream a := .cons x (PStream.repeat x)
partial_fixpoint

theorem PStream.repeat_hasNoBot (x : a) : (PStream.repeat x).HasNoBot := by
  apply CofixWithBot.HasNoBot.coinduct (fun z => z = PStream.repeat x) _ _ rfl
  rintro _ rfl
  refine ⟨(x, PStream.repeat x), ?_, (IsPolynomial.liftPLast_iff _ _).2 fun _ => rfl⟩
  conv => lhs; rw [PStream.repeat.eq_1]
  exact congrArg Comp.get (Cofix.dest_mk _)

/-- `repeat x`, as a total stream. -/
def Stream.repeat (x : a) : Stream a :=
  CofixWithBot.get (PStream.repeat x) (PStream.repeat_hasNoBot x)

/-! ### map -/

def PStream.map (f : α → β) (xs : Stream α) : PStream β :=
  .cons (f xs.head) (map f xs.tail)
partial_fixpoint

def Stream.map' (xs : Stream α) (f : α → β) : Stream β :=
  CofixWithBot.get (PStream.map f xs) <| by
    apply CofixWithBot.HasNoBot.coinduct (fun z => ∃ xs, z = PStream.map f xs) _ _ ⟨xs, rfl⟩
    rintro _ ⟨xs, rfl⟩
    rw [PStream.map.eq_1]
    exact ⟨_, PStream.dest_cons _ _, (IsPolynomial.liftPLast_iff _ _).2 fun _ => ⟨_, rfl⟩⟩

codef Stream.map (f : α → β) (xs : Stream α) : Stream β :=
  cons (f xs.head) (map f xs.tail)
productive_by
  erw [CofixWithBot.dest_mk]
  refine ⟨_, rfl, ?_⟩
  exact (IsPolynomial.liftPLast_iff _ _).2 fun _ => ⟨_, rfl⟩


@[simp, grind =]
theorem Stream.head_map (f : α → β) (xs : Stream α) : (Stream.map f xs).head = f xs.head := by
  rw [Stream.map, Stream.head_cons]

@[simp, grind =]
theorem Stream.tail_map (f : α → β) (xs : Stream α) :
    (Stream.map f xs).tail = Stream.map f xs.tail := by
  rw [Stream.map, Stream.tail_cons]

namespace Stream

/-! ### filter -/
section Filter

/-- Some element of `xs`, now or later, satisfies `P`. -/
inductive Eventually (P : α → Bool) : Stream α → Prop
  | here {xs : Stream α} : P xs.head → Eventually P xs
  | later {xs : Stream α} : Eventually P xs.tail → Eventually P xs

/-- At every point of `xs`, some future element satisfies `P`. -/
coinductive InfOften (P : α → Bool) : Stream α → Prop
  | mk {xs : Stream α} :
      Eventually P xs → InfOften P xs.tail → InfOften P xs

theorem InfOften.tail {P : α → Bool} {xs : Stream α} (h : xs.InfOften P) :
    xs.tail.InfOften P := by
  cases h with | mk _ h => exact h

codef filter (P : α → Bool) (xs : Stream α) (h : xs.InfOften P) : Stream α :=
  if P xs.head then
    cons xs.head (filter P xs.tail h.tail)
  else
    filter P xs.tail h.tail
productive_by
  cases h with | mk hev hinf =>
  induction hev with
  | @here xs hP =>
    rw [hP]
    exact ⟨_, CofixWithBot.dest_mk _, (IsPolynomial.liftPLast_iff _ _).2 fun _ => ⟨_, _, rfl⟩⟩
  | @later xs hev ih =>
    split
    · exact ⟨_, CofixWithBot.dest_mk _, (IsPolynomial.liftPLast_iff _ _).2 fun _ => ⟨_, _, rfl⟩⟩
    · rw [filter.__partial]
      cases hinf with | mk _ hinf' => exact ih hinf'

/--
info: '_private.Test.Theory.QPF.Cofix.WithBot.0.QPFTypes.Test.WithBot.Stream.filter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms filter

@[grind =]
theorem filter_of_pos {P : α → Bool} {xs : Stream α} (h : xs.InfOften P)
    (hP : P xs.head) :
    filter P xs h = cons xs.head (filter P xs.tail h.tail) := by
  rw [filter]; grind

@[grind =]
theorem filter_of_neg {P : α → Bool} {xs : Stream α} (h : xs.InfOften P)
    (hP : ¬P xs.head) :
    filter P xs h = filter P xs.tail h.tail := by
  rw [filter]; grind

theorem head_filter {P : α → Bool} {xs : Stream α} (h : xs.InfOften P)
    (hP : P xs.head) : (filter P xs h).head = xs.head := by
  rw [filter_of_pos h hP, head_cons]

theorem tail_filter {P : α → Bool} {xs : Stream α} (h : xs.InfOften P)
    (hP : P xs.head) : (filter P xs h).tail = filter P xs.tail h.tail := by
  rw [filter_of_pos h hP, tail_cons]

end Filter

/-! ## nats -/
section Nats

codef nats (fro : Nat) : Stream Nat :=
  .cons fro (nats <| fro + 1)
productive_by
  simp [CofixWithBot.mk]
  refine ⟨?y, by rfl, ?_⟩
  refine (IsPolynomial.liftPLast_iff _ _).2 fun i => ?_
  exists fro + 1

@[simp, grind =]
theorem head_nats : (nats n).head = n := by
  rw [nats]; simp

@[simp, grind =]
theorem tail_nats : (nats n).tail = nats (n + 1) := by
  rw [nats]; simp

end Nats

section Get

@[grind]
def get (xs : Stream α) : Nat → α
  | 0 => xs.head
  | i + 1 => xs.tail.get i

variable {xs : Stream α}

@[simp, grind =] theorem get_zero : xs.get 0 = xs.head := rfl
@[simp, grind =] theorem get_succ : xs.get (i + 1) = xs.tail.get i := rfl

@[simp, grind =]
theorem get_nats : (nats n).get i = n + i := by
  induction i generalizing n <;> grind

@[simp, grind =]
theorem get_map (xs : Stream α) (f : α → β) (i : Nat) :
    (xs.map f).get i = f (xs.get i) := by
  induction i generalizing xs
  <;> simp [*]

end Get

section EvensExample

def evens := (nats 0).map (· * 2)

@[simp, grind =]
theorem get_evens : evens.get i = i * 2 := by
  simp [evens]

def Nat.isEven (n : Nat) : Bool :=
  n % 2 == 0

def evens' := (nats 0).filter Nat.isEven <| by
  apply Stream.InfOften.coinduct _ (fun z => ∃ n, z = nats n)
  · rintro _ ⟨n, rfl⟩
    rw [tail_nats]
    refine ⟨?n, ?_, by rfl⟩
    induction n
    case zero =>
      apply Stream.Eventually.here
      rw [head_nats]
      rfl
    case succ n ih =>
      cases ih
      case here ih =>
        apply Stream.Eventually.later
        apply Stream.Eventually.here
        grind [Nat.isEven]
      case later ih =>
        simpa using ih
  · exact ⟨_, rfl⟩

example (i) : evens'.get i = evens.get i := by
  simp only [get_evens, evens']
  suffices ∀ n (h : _) (hn : Nat.isEven n),
      (Stream.filter Nat.isEven (nats n) h).get i = n + i * 2
    by grind [Nat.isEven]
  intro n h hn
  induction i generalizing n
  case zero => grind [filter.__unfold]
  case succ i ih =>
    rw [filter.__unfold, filter.__unfold]
    have : Nat.isEven (n + 1) = false := by grind [Nat.isEven]
    specialize ih (n + 2) (by grind) (by grind [Nat.isEven])
    simp [*]; grind

end EvensExample

section Map2

/-
The recursive call is destructed with `Stream.tail`, which is translated to its partial version
`Stream.tail.__partial` (see `@[qpf_elim]` on `Stream.tail`).

The productivity proof is still missing: the motive set up by `productive_by_intro` only covers
the recursive calls `cursedMap.__partial f xs`, but the second layer is
`mk (f xs.head, tail.__partial (cursedMap.__partial f xs.tail))`.
-/
codef cursedMap (f : α → β) (xs : Stream α) : Stream β :=
  cons (f xs.head) <| cons (f xs.head) (cursedMap f xs.tail).tail
productive_by
  sorry

example (f : α → β) (xs : Stream α) : (cursedMap f xs).tail.head = f xs.head := by
  rw [cursedMap, tail_cons, head_cons]

/-
FIXME: the following ought to work

```
codef map2 (f : α → α) (xs : Stream α) : Stream α :=
  cons (f xs.head) (map2 f <| map2 f xs.tail)
productive_by
  sorry
```
-/

end Map2


/-! ### Errors -/

/--
error: codef: the type of `QPFTypes.Test.WithBot.Stream.notCofix` should be a `Cofix` type:
failed to unify
  Nat
with
  Cofix ?F ?α
-/
#guard_msgs in
codef notCofix (n : Nat) : Nat := notCofix n
productive_by
  sorry

/--
error: codef: nested recursive calls are not supported
  Stream.nested.__codef_raw (Stream.nested.__codef_raw xs.tail)
-/
#guard_msgs in
codef Stream.nested (xs : Stream α) : Stream α :=
  Stream.cons xs.head (Stream.nested (Stream.nested xs.tail))
productive_by
  sorry

/-- A copy of `Stream.tail`, without `@[qpf_elim]`. -/
def tail' (xs : Stream α) : Stream α := (Cofix.dest xs).2

/--
error: codef: cannot destruct a possibly-partial value with `Cofix.dest`
  Cofix.dest (tailOfRec.__codef_raw xs.tail)
`tail'` destructs a possibly-partial value, but has no partial version (`__partial`); mark `tail'` with `@[qpf_elim]` to define it
-/
#guard_msgs in
codef tailOfRec (xs : Stream α) : Stream α :=
  cons xs.head (tail' (tailOfRec xs.tail))
productive_by
  sorry

-- `Stream.head.__partial` is in continuation-passing style, which `codef` does not use yet.
/--
error: codef: cannot use `head.__partial`, the partial version of `head`, in
  (headOfRec.__codef_raw xs.tail).head
it should have the same universe parameters as `head`. Note that partial versions in continuation-passing style, for eliminators whose result is not of a coinductive type, are not supported yet
-/
#guard_msgs in
codef headOfRec (xs : Stream α) : Stream α :=
  cons (headOfRec xs.tail).head xs
productive_by
  sorry

/-- error: @[qpf_elim]: `notAnElim` has no argument of a `Cofix` type -/
#guard_msgs in
@[qpf_elim] def notAnElim (n : Nat) : Nat := n

/--
error: @[qpf_elim]: `noDest` does not destruct any of its arguments of type
  Stream α
-/
#guard_msgs in
@[qpf_elim] def noDest (xs : Stream α) : Stream α := xs

-- Unproductive definitions are accepted as `__partial`; only the proof is missing.
/-- warning: declaration uses `sorry` -/
#guard_msgs in
codef Stream.unproductive (xs : Stream α) : Stream α := Stream.unproductive xs.tail
productive_by
  sorry
