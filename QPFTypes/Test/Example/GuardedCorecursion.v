(* Rocq counterparts of the Lean examples in this directory.
   Checked with Rocq 9.1.1, Stdlib 9.0.0; see README.md for the command.

   These use native coinductives in place of Lean's Cofix encodings. They check
   guardedness of the corresponding bodies, not an implementation of Lean codef.
   No Unset Guard Checking, axioms, or admitted obligations are used.
   Fail tests below are deliberately well-typed apart from guardedness. *)

From Stdlib Require Import Vectors.Fin Lists.List.
Import ListNotations.
Set Implicit Arguments.

Module Streams.
  CoInductive Stream (A : Type) := cons : A -> Stream A -> Stream A.
  Arguments cons {A} _ _.
  Definition head {A} (s : Stream A) : A := match s with cons a _ => a end.
  Definition tail {A} (s : Stream A) : Stream A := match s with cons _ t => t end.

  CoFixpoint iterate {A} (step : A -> A) (a : A) : Stream A :=
    let rest := iterate step (step a) in id (cons a rest).

  CoFixpoint interleave {A} (s t : Stream A) : Stream A :=
    match s with cons a s' => cons a (interleave t s') end.

  CoFixpoint stutter {A} (s : Stream A) : Stream A :=
    match s with cons a s' => cons a (cons a (stutter s')) end.

  CoFixpoint sample {A} (skipNext : A -> bool) (s : Stream A) : Stream A :=
    cons (head s) (if skipNext (head s)
      then sample skipNext (tail (tail s)) else sample skipNext (tail s)).

  CoFixpoint truesFalses : Stream bool := cons true falsesTrues
  with falsesTrues : Stream bool := cons false truesFalses.

  (* A branch can search forever without producing a constructor. *)
  Fail CoFixpoint filter {A} (p : A -> bool) (s : Stream A) : Stream A :=
    match s with cons a s' =>
      if p a then cons a (filter p s') else filter p s'
    end.

  (* A constructor canceled by a destructor is not a guard. *)
  Fail CoFixpoint canceled : Stream nat := tail (cons 0 canceled).

  (* Productive, but not syntactically guarded: map is not a constructor. *)
  CoFixpoint map {A B} (f : A -> B) (s : Stream A) : Stream B :=
    match s with cons a s' => cons (f a) (map f s') end.
  Fail CoFixpoint natsMapped : Stream nat := cons 0 (map S natsMapped).

  (* An outer guard does not permit recursive occurrences in call arguments,
     case scrutinees, or nonrecursive constructor fields, respectively. *)
  Fail CoFixpoint nested (s : Stream nat) : Stream nat :=
    cons 0 (nested (nested s)).
  Fail CoFixpoint scrutinized : Stream nat :=
    cons 0 (match scrutinized with cons _ s => s end).
  Fail CoFixpoint wrongField : Stream nat := cons (head wrongField) wrongField.
End Streams.

Module CoLists.
  CoInductive CoList (A : Type) :=
  | nil : CoList A
  | cons : A -> CoList A -> CoList A.
  Arguments nil {A}.
  Arguments cons {A} _ _.

  (* The existing safe CoList.map is also in the guarded fragment. *)
  CoFixpoint map {A B} (f : A -> B) (xs : CoList A) : CoList B :=
    match xs with nil => nil | cons x xs' => cons (f x) (map f xs') end.

  (* Unlike map above, f is captured outside the recursive binder. This is
     game-trees' comap, needed by the nested CoTrees examples below. *)
  Definition mapCorec {A B} (f : A -> B) : CoList A -> CoList B :=
    cofix go (xs : CoList A) : CoList B :=
      match xs with nil => nil | cons x xs' => cons (f x) (go xs') end.

  CoFixpoint append {A} (xs ys : CoList A) : CoList A :=
    match xs with nil => ys | cons x xs' => cons x (append xs' ys) end.
End CoLists.

Module Delays.
  CoInductive Delay (A : Type) := now : A -> Delay A | later : Delay A -> Delay A.
  Arguments now {A} _.
  Arguments later {A} _.

  CoFixpoint search {A} (p : A -> bool) (s : Streams.Stream A) : Delay A :=
    if p (Streams.head s) then now (Streams.head s)
    else later (search p (Streams.tail s)).
End Delays.

Module Trees.
  CoInductive Tree (A : Type) :=
  | leaf : Tree A
  | node : A -> Tree A -> Tree A -> Tree A.
  Arguments leaf {A}.
  Arguments node {A} _ _ _.

  CoFixpoint mirror {A} (t : Tree A) : Tree A :=
    match t with leaf => leaf | node a l r => node a (mirror r) (mirror l) end.
End Trees.

Module RoseTrees.
  CoInductive RoseTree (A : Type) :=
  | node : A -> {n : nat & Fin.t n -> RoseTree A} -> RoseTree A.
  Arguments node {A} _ _.

  CoFixpoint unfold {A State} (label : State -> A) (arity : State -> nat)
      (next : forall s, Fin.t (arity s) -> State) (s : State) : RoseTree A :=
    node (label s) (existT _ (arity s) (fun i => unfold label arity next (next s i))).

  (* Nested inductive constructors are allowed, but this does not make
     arbitrary traversal of an unknown list guarded. Kept here as a boundary
     probe, not as a second Lean API for rose trees. *)
  CoInductive ListRose := listRose : list ListRose -> ListRose.
  CoFixpoint binaryRose : ListRose := listRose [binaryRose; binaryRose].
  Fail CoFixpoint copy (t : ListRose) : ListRose :=
    match t with listRose ts => listRose (List.map copy ts) end.
End RoseTrees.

(* Korkut, A Rose Tree Is Blooming (CPP 2026), section 3, and
   bloomberg/game-trees, theories/Cotrees.v: comap_cotree and unfold_cotree. *)
Module CoTrees.
  Import CoLists.

  CoInductive CoTree (A : Type) := node : A -> CoList (CoTree A) -> CoTree A.
  Arguments node {A} _ _.

  CoFixpoint map {A B} (f : A -> B) (t : CoTree A) : CoTree B :=
    match t with
    | node a children => node (f a) (mapCorec (map f) children)
    end.

  CoFixpoint unfold {A} (next : A -> CoList A) (a : A) : CoTree A :=
    node a (mapCorec (unfold next) (next a)).

  (* The all-parameter CoLists.map passes in isolation, but these uses do not:
     the outer recursive reference is now an argument to the inner cofixpoint
     rather than captured in its body. This is not the inductive List.map case. *)
  Fail CoFixpoint mapAll {A B} (f : A -> B) (t : CoTree A) : CoTree B :=
    match t with
    | node a children => node (f a) (CoLists.map (mapAll f) children)
    end.

  Fail CoFixpoint unfoldAll {A} (next : A -> CoList A) (a : A) : CoTree A :=
    node a (CoLists.map (unfoldAll next) (next a)).
End CoTrees.

Module Languages.
  CoInductive Language (A : Type) := node : bool -> (A -> Language A) -> Language A.
  Arguments node {A} _ _.
  Definition acceptsEmpty {A} (l : Language A) := match l with node b _ => b end.
  Definition derivative {A} (l : Language A) := match l with node _ k => k end.

  CoFixpoint union {A} (l r : Language A) : Language A :=
    node (orb (acceptsEmpty l) (acceptsEmpty r))
      (fun a => union (derivative l a) (derivative r a)).

  (* The usual derivative equation is productive, but the union surrounding
     concat is not a constructor. Isabelle's support for such equations in
     Traytel's article must not be mistaken for Rocq guardedness. *)
  Fail CoFixpoint concat {A} (l r : Language A) : Language A :=
    node (andb (acceptsEmpty l) (acceptsEmpty r))
      (fun a => if acceptsEmpty l
        then union (concat (derivative l a) r) (derivative r a)
        else concat (derivative l a) r).
End Languages.

Module ITrees.
  CoInductive ITree {E : Type} (Ans : E -> Type) (R : Type) :=
  | ret : R -> ITree Ans R
  | tau : ITree Ans R -> ITree Ans R
  | vis : forall e, (Ans e -> ITree Ans R) -> ITree Ans R.
  Arguments ret {E Ans R} _.
  Arguments tau {E Ans R} _.
  Arguments vis {E Ans R} _ _.

  Definition bind {E Ans R S} (t : @ITree E Ans R) (k : R -> @ITree E Ans S)
      : @ITree E Ans S :=
    (cofix go (t : @ITree E Ans R) : @ITree E Ans S :=
      match t with
      | ret r => k r
      | tau t' => tau (go t')
      | vis e h => vis e (fun a => go (h a))
      end) t.

  CoFixpoint iter {E Ans R S} (step : S -> @ITree E Ans (S + R)) (s : S)
      : @ITree E Ans R :=
    bind (step s) (fun result =>
      match result with inl s' => tau (iter step s') | inr r => ret r end).

  (* A superficially interchangeable bind with the continuation as a recursive
     argument still passes on its own, but not when used in iter! *)
  CoFixpoint bindAll {E Ans R S} (t : @ITree E Ans R) (k : R -> @ITree E Ans S)
      : @ITree E Ans S :=
    match t with
    | ret r => k r
    | tau t' => tau (bindAll t' k)
    | vis e h => vis e (fun a => bindAll (h a) k)
    end.
  Fail CoFixpoint iterAll {E Ans R S} (step : S -> @ITree E Ans (S + R)) (s : S)
      : @ITree E Ans R :=
    bindAll (step s) (fun result =>
      match result with inl s' => tau (iterAll step s') | inr r => ret r end).

  (* Capturing the continuation does not remove the need for an outer guard. *)
  Fail CoFixpoint iterNoTau {E Ans R S} (step : S -> @ITree E Ans (S + R)) (s : S)
      : @ITree E Ans R :=
    bind (step s) (fun result =>
      match result with inl s' => iterNoTau step s' | inr r => ret r end).
End ITrees.
