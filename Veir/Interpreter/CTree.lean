module

public import CTree.Defs
public import CTree.UB
public import CTree.Iter
public import CTree.Interp
public import CTree.Sim

public import Veir.Interpreter.Interp
public import Veir.Interpreter.RuntimeValue

public section

open CTree

/-!
  Infrastructure for CTree-based interpretation.

  A CTree-based interpreter can give semantics to effects, to nondeterminism and to non-termination.
-/

namespace Veir

/-! ## Undefined Behavior Effect -/

/-- Emit an immediate undefined behavior -/
def ub {EIn CIn} {E : EIn → Type} {C : CIn → Type} {R} [UBE -< E] : CTree E C R := do
  let x ← CTree.trigger (SubE := UBE) UBEIn.mk
  by cases x

/-- Undefined behavior does not run a subsequent computation. -/
@[simp]
theorem bind_ub {EIn CIn} {E : EIn → Type} {C : CIn → Type} [UBE -< E]
    (next : α → CTree E C β) :
    CTree.bind ub next = ub := by
  simp only [ub, CTree.trigger_def, Bind.bind, CTree.CTree.bind_vis]
  congr 1
  funext impossible
  exact nomatch Subeffect.mapCont UBE E UBEIn.mk impossible

/-- Explicit UB in the source permits any target behavior when the embedded event is UB. -/
@[simp, grind .]
theorem sim_ub {EIn CIn C'In} {E : EIn → Type} {C : CIn → Type}
    {C' : C'In → Type} [HasUB EIn] [UBE -< E]
    (relation : α → β → Prop) (target : CTree E C α)
    (isUB : HasUB.isUB (Subeffect.mapEff UBE E UBEIn.mk) := by trivial) :
    Sim relation target (ub : CTree E C' β) := by
  simp only [ub, CTree.trigger_def, Bind.bind, CTree.CTree.bind_vis]
  apply Sim.ub
  exact isUB

/-! ## Error Effect -/

/-- Effect materializing an ill-formed program -/
structure ErrorEIn : Type u where

/-- Effect materializing an ill-formed program -/
@[expose]
def ErrorE (e : ErrorEIn.{u}) :=
  match e with
  | .mk => Empty

/-- Interpreter errors allow any behavior in simulation, just like explicit UB. -/
instance : HasUB ErrorEIn where
  isUB := fun _ => True

@[simp, grind .]
theorem ErrorEIn.isUB (e : ErrorEIn) : HasUB.isUB e := trivial

/-- Emit an effect materializing an ill-formed program -/
def fail {EIn CIn} {E : EIn → Type} {C : CIn → Type} {R} [ErrorE -< E] : CTree E C R := do
  let x ← CTree.trigger (SubE := ErrorE) ErrorEIn.mk
  by cases x

/-- Interpreter failure does not run a subsequent computation. -/
@[simp]
theorem bind_fail {EIn CIn} {E : EIn → Type} {C : CIn → Type} [ErrorE -< E]
    (next : α → CTree E C β) :
    CTree.bind fail next = fail := by
  simp only [fail, CTree.trigger_def, Bind.bind, CTree.CTree.bind_vis]
  congr 1
  funext impossible
  exact nomatch Subeffect.mapCont ErrorE E ErrorEIn.mk impossible

/-- Interpreter failure in the source permits any target behavior when the embedded event is UB. -/
@[simp, grind .]
theorem sim_fail {EIn CIn C'In} {E : EIn → Type} {C : CIn → Type}
    {C' : C'In → Type} [HasUB EIn] [ErrorE -< E]
    (relation : α → β → Prop) (target : CTree E C α)
    (isUB : HasUB.isUB (Subeffect.mapEff ErrorE E ErrorEIn.mk) := by trivial) :
    Sim relation target (fail : CTree E C' β) := by
  simp only [fail, CTree.trigger_def, Bind.bind, CTree.CTree.bind_vis]
  apply Sim.ub
  exact isUB

/-! ## Freeze Effect -/

/-- Choice of a bitvector of a given bitwidth (input type) -/
structure FreezeCIn : Type u where
  bw : Nat

/-- Choice of a bitvector of a given bitwidth (output type) -/
abbrev FreezeC (c : FreezeCIn.{u}) : Type :=
  match c with
  | .mk bw => BitVec bw

/-! ## Region Runner Effect -/

/-- A region call effect (input type), including its arguments and the state visible to its body. -/
structure RunRegionEIn (ctx : WfIRContext OpCode) (σ : Type) where
  region : RegionPtr
  values : Array RuntimeValue
  state : σ
  regionInBounds : region.InBounds ctx.raw := by grind

/-- A region call effect output type. A region returns its final state and its yielded values. -/
abbrev RunRegionE (ctx : WfIRContext OpCode) (σ : Type) (_ : RunRegionEIn ctx σ) : Type :=
  σ × Array RuntimeValue

/-- Trees whose region calls have not yet been interpreted. -/
abbrev RegionTree (ctx : WfIRContext OpCode) (σ α : Type) :=
  CTree (RunRegionE ctx σ ⊕ₑ (ErrorE ⊕ₑ UBE)) FreezeC α

/-- Request region execution without choosing its recursive interpretation. -/
def runRegion (region : RegionPtr) (values : Array RuntimeValue) (state : σ)
    (inBounds : region.InBounds ctx.raw := by grind) : RegionTree ctx σ (σ × Array RuntimeValue) :=
  CTree.trigger (SubE := RunRegionE ctx σ) ⟨region, values, state, inBounds⟩

/-- A CTree with the error and UB effect, and the freeze choice. -/
abbrev Tree (α : Type) := CTree (ErrorE ⊕ₑ UBE) FreezeC α

/-! ## Monad Lifting To CTrees -/

instance [ErrorE -< E] : MonadLift Option (CTree E C) where
  monadLift
    | .none => fail
    | .some v => return v

instance [ErrorE -< E] [UBE -< E] : MonadLift Interp (CTree E C) where
  monadLift
    | .ub _ => ub
    | .fail _ => fail
    | .ok v => return v

@[simp]
theorem Sim.monadLift_ub {EIn CIn} {E : EIn → Type} {C : CIn → Type} [ErrorE -< E] [UBE -< E]
    (location : Option OperationPtr) :
    (monadLift (Interp.ub location) : CTree E C α) = ub := by
  rfl

@[simp]
theorem Sim.monadLift_fail {EIn CIn} {E : EIn → Type} {C : CIn → Type} [ErrorE -< E] [UBE -< E]
    (location : Option OperationPtr) :
    (monadLift (Interp.fail location) : CTree E C α) = fail := by
  rfl

theorem Sim.bind_monadLift_left_iff {EIn CIn C'In} {E : EIn → Type}
    {C : CIn → Type} {C' : C'In → Type} [HasUB EIn] [ErrorE -< E] [UBE -< E]
    (relation : α → γ → Prop) (source : CTree E C' γ)
    (outcome : Interp β) (next : β → CTree E C α) :
    Sim relation (CTree.bind (monadLift outcome) next) source ↔
    match outcome with
    | .ok value => Sim relation (next value) source
    | .ub _ => Sim relation (ub : CTree E C α) source
    | .fail _ => Sim relation (fail : CTree E C α) source := by
  cases outcome <;> simp [monadLift, MonadLift.monadLift]

theorem Sim.monadLift_right_iff {EIn : Type} {E : EIn → Type}
  [HasUB EIn] [ErrorE -< E] [UBE -< E]
  {CIn C'In : Type} {C : CIn → Type} {C' : C'In → Type}
  {α β : Type} (relation : α → β → Prop)
  (target : CTree E C α) (func : Interp β) :
  CTree.Sim relation target (monadLift func : CTree E C' β) ↔
    match func with
    | .ok value => CTree.Sim relation target (pure value : CTree E C' β)
    | .ub _ => CTree.Sim relation target (ub : CTree E C' β)
    | .fail _ => CTree.Sim relation target (fail : CTree E C' β) := by
  cases func <;> rfl

/-! ## The values a CTree can return -/

/--
`CTree.MayReturn t r` holds when `t` can return `r`: some finite path through its choices, and
through whatever its effects may answer, reaches `CTree.ret r`.
-/
inductive CTree.MayReturn {EIn CIn R : Type} {E : EIn → Type} {C : CIn → Type} :
    CTree E C R → R → Prop where
  /-- A tree that returns `r` returns `r`. -/
  | ret (r : R) : MayReturn (CTree.ret r) r
  /-- A choice returns what one of its branches returns. -/
  | tau (c : C1In ⊕ CIn) k : ∀ x {r : R}, MayReturn (k x) r → MayReturn (CTree.tauG c k) r
  /-- A visible effect returns what its continuation returns on one of the answers. -/
  | vis (e : EIn) (k : E e → CTree E C R) (x : E e) {r : R} :
      MayReturn (k x) r → MayReturn (CTree.vis e k) r

namespace CTree.MayReturn

variable {EIn CIn R : Type} {E : EIn → Type} {C : CIn → Type}

/-- A tree that returns determines what it returns. -/
@[simp, grind =]
theorem pure_iff (v r : R) : MayReturn (pure v : CTree E C R) r ↔ r = v := by
  constructor
  · intro h
    generalize heq : (pure v : CTree E C R) = t at h
    cases h <;> have hhead := congrArg CTree.unfold heq <;> grind
  · rintro rfl
    exact .ret _

/-- A generic choice node returns what one of its branches returns. -/
@[simp, grind =]
theorem tauG_iff (c : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) c → CTree E C R) (r : R) :
    MayReturn (CTree.tauG c k) r ↔ ∃ x, MayReturn (k x) r := by
  constructor
  · intro h
    generalize heq : CTree.tauG c k = t at h
    cases h <;> have hhead := congrArg CTree.unfold heq <;>
      simp only [unfold_ret, unfold_tauG, unfold_vis] at hhead <;> cases hhead <;> grind
  · rintro ⟨x, h⟩
    exact .tau c k x h

/-- A custom choice node returns what one of its branches returns. -/
@[simp, grind =]
theorem tau_iff (c : CIn) (k : C c → CTree E C R) (r : R) :
    MayReturn (CTree.tau c k) r ↔ ∃ x, MayReturn (k x) r := by
  simp only [CTree.tau_def]
  exact tauG_iff (.inr c) k r

/-- A visible node returns what its continuation returns on one of the answers. -/
@[simp, grind =]
theorem vis_iff (e : EIn) (k : E e → CTree E C R) (r : R) :
    MayReturn (CTree.vis e k) r ↔ ∃ x, MayReturn (k x) r := by
  constructor
  · intro h
    generalize heq : CTree.vis e k = t at h
    cases h with
    | ret r' =>
      have hhead := congrArg CTree.unfold heq
      simp [unfold_vis] at hhead
    | tau c f x hx =>
      have hhead := congrArg CTree.unfold heq
      simp [unfold_tauG, unfold_vis] at hhead
    | vis e' k' x hx =>
      have hhead := congrArg CTree.unfold heq
      simp only [unfold_vis] at hhead
      injection hhead with he hk
      subst he
      obtain rfl : k = k' := eq_of_heq hk
      exact ⟨x, hx⟩
  · rintro ⟨x, h⟩
    exact .vis e k x h

/-- Binding returns what the continuation returns on a value the first tree returns. -/
@[simp, grind =]
theorem bind_iff {X : Type} (t : CTree E C X) (k : X → CTree E C R) (r : R) :
    MayReturn (CTree.bind t k) r ↔ ∃ x, MayReturn t x ∧ MayReturn (k x) r := by
  constructor
  · intro h
    generalize heq : CTree.bind t k = tk at h
    induction h generalizing t <;> cases t with
    | ret x => exact ⟨x, .ret x, by grind⟩
    | tau | vis =>
      have hhead := congrArg CTree.unfold heq
      simp only [CTree.CTree.bind_tau, CTree.CTree.bind_vis, unfold_ret, unfold_tauG,
        unfold_vis] at hhead
      cases hhead <;> grind
  · rintro ⟨x, ht, hk⟩
    induction ht <;> grind

/-- A failing computation returns nothing: nothing answers its effect. -/
@[simp, grind =]
theorem fail_iff [ErrorE -< E] (r : R) : MayReturn (Veir.fail : CTree E C R) r ↔ False := by
  simp only [Veir.fail, Bind.bind, bind_iff, iff_false, not_exists, not_and]
  exact fun x _ => nomatch x

/-- A computation that is undefined behaviour returns nothing. -/
@[simp, grind =]
theorem ub_iff [UBE -< E] (r : R) : MayReturn (Veir.ub : CTree E C R) r ↔ False := by
  simp only [Veir.ub, Bind.bind, bind_iff, iff_false, not_exists, not_and]
  exact fun x _ => nomatch x

/-- A choice may return any value of its type. -/
@[simp, grind =]
theorem choose_iff {SubCIn : Type} {SubC : SubCIn → Type} [SubC -< C] (c : SubCIn)
    (r : SubC c) : MayReturn (CTree.choose (E := E) (C := C) c) r ↔ True := by
  simp only [CTree.choose_def, tau_iff, CTree.ret_pure, pure_iff, iff_true]
  obtain ⟨y, hy⟩ := Subeffect.map_surj (ε₁ := SubC) (ε₂ := C) c r
  grind

/-- A lifted `Interp` computation returns only what that computation returns. -/
@[simp, grind =]
theorem monadLift_iff [ErrorE -< E] [UBE -< E] {α : Type} (x : Interp α) (r : α) :
    MayReturn (monadLift x : CTree E C α) r ↔ x = .ok r := by
  cases x with
  | ok v =>
    simp only [monadLift, MonadLift.monadLift, pure_iff, Interp.ok.injEq]
    exact eq_comm
  | fail e => simp [monadLift, MonadLift.monadLift]
  | ub e => simp [monadLift, MonadLift.monadLift]

end CTree.MayReturn

/-! ## Definition of Pure CTrees -/

/--
A `PureOrErr` CTree has a finite depth, and no visible effect except for failure or UB.
-/
inductive PureOrErr {EIn CIn R} {E : EIn → Type} {C : CIn → Type}
    [ErrorE -< E] [UBE -< E] :
  CTree E C R → Prop where
| ret (r : R) : PureOrErr (CTree.ret r)
| tau (c : C1In ⊕ CIn) k : (forall x, PureOrErr (k x)) → PureOrErr (CTree.tauG c k)
| fail {k} : PureOrErr (CTree.vis (Subeffect.mapEff ErrorE E ErrorEIn.mk) k)
| ub {k} : PureOrErr (CTree.vis (Subeffect.mapEff UBE E UBEIn.mk) k)

attribute [simp, grind .] PureOrErr.tau PureOrErr.ret PureOrErr.fail PureOrErr.ub

theorem PureOrErr.bind {EIn CIn X Y} {E : EIn → Type} {C : CIn → Type}
    [ErrorE -< E] [UBE -< E] (t : CTree E C Y) (k : Y → CTree E C X) :
  PureOrErr t →
  (forall x, PureOrErr (k x)) →
  PureOrErr (Bind.bind t k) := by
  intros ht
  induction ht <;> grind

/--
`CanInterpretTo t r` means that the CTree `t` can produce the outcome `r` when interpreted.
If the `CTree` is `PureOrErr`, then `CanInterpretTo t` represents the exact set of outcomes that
`t` can produce.
-/
inductive PureOrErr.CanInterpretTo {EIn CIn R} {E : EIn → Type} {C : CIn → Type}
    [ErrorE -< E] [UBE -< E] : CTree E C R → Interp R → Prop where
| ret (r : R) : CanInterpretTo (CTree.ret r) (.ok r)
| tau (c : C1In ⊕ CIn) k : ∀ x r, CanInterpretTo (k x) r → CanInterpretTo (CTree.tauG c k) r
| fail {k} : CanInterpretTo (CTree.vis (Subeffect.mapEff ErrorE E ErrorEIn.mk) k) (.fail none)
| ub {k} : CanInterpretTo (CTree.vis (Subeffect.mapEff UBE E UBEIn.mk) k) (.ub none)

namespace PureOrErr.CanInterpretTo

variable {EIn CIn R} {E : EIn → Type} {C : CIn → Type}
    [ErrorE -< E] [UBE -< E]

/-- A return node has exactly its successful return value as an outcome. -/
@[simp, grind =]
theorem pure_iff (v : R) (r : Interp R) :
    CanInterpretTo (pure v : CTree E C R) r ↔ r = .ok v := by
  constructor
  · intro h
    generalize heq : (pure v : CTree E C R) = t at h
    cases h <;> have hhead := congrArg CTree.unfold heq <;> grind
  · rintro rfl
    exact .ret _

/-- A generic choice node can produce an outcome iff one of its branches can. -/
@[simp, grind =]
theorem tauG_iff (c : C1In ⊕ CIn) (k : (C1 ⊕ₑ C) c → CTree E C R)
    (r : Interp R) :
    CanInterpretTo (CTree.tauG c k) r ↔ ∃ x, CanInterpretTo (k x) r := by
  constructor
  · intro h
    generalize heq : CTree.tauG c k = t at h
    cases h <;> have hhead := congrArg CTree.unfold heq <;>
      simp only [unfold_ret, unfold_tauG, unfold_vis] at hhead <;> cases hhead <;> grind
  · rintro ⟨x, h⟩
    exact .tau c k x r h

/-- A custom choice node can produce an outcome iff one of its branches can. -/
@[simp, grind =]
theorem tau_iff (c : CIn) (k : C c → CTree E C R) (r : Interp R) :
    CanInterpretTo (CTree.tau c k) r ↔ ∃ x, CanInterpretTo (k x) r := by
  simp only [CTree.tau_def]
  exact tauG_iff (.inr c) k r

/-- A sub-choice node can produce an outcome iff one of its branches can. -/
@[simp, grind =]
theorem choose_iff {SubCIn} {SubC : SubCIn → Type} [SubC -< C]
    (c : SubCIn) (r : Interp (SubC c)) :
    CanInterpretTo (CTree.choose (E := E) (C := C) c) r ↔ ∃ x, r = .ok x := by
  simp only [CTree.choose_def, tau_iff, CTree.ret_pure, pure_iff]
  constructor
  · grind
  · rintro ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := Subeffect.map_surj (ε₁ := SubC) (ε₂ := C) c x
    grind

/-- A visible node can only produce failure or UB, independently of its continuation. -/
@[simp, grind =]
theorem vis_iff (e : EIn) (k : E e → CTree E C R) (r : Interp R) :
    CanInterpretTo (CTree.vis e k) r ↔
      (e = Subeffect.mapEff ErrorE E ErrorEIn.mk ∧ r = .fail none) ∨
      (e = Subeffect.mapEff UBE E UBEIn.mk ∧ r = .ub none) := by
  constructor
  · intro h
    generalize heq : CTree.vis e k = t at h
    cases h <;> have hhead := congrArg CTree.unfold heq <;>
      simp only [unfold_ret, unfold_tauG, unfold_vis] at hhead <;> cases hhead <;> grind
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact .fail
    · exact .ub



/-- Lifting an `Interp` computation preserves its successful outcome. -/
@[simp, grind =]
theorem monadLift_interp_ok_iff (outcome : Interp R) (v : R) :
    CanInterpretTo (monadLift outcome : CTree E C R) (.ok v) ↔ outcome = .ok v := by
  cases outcome <;>
    simp [monadLift, MonadLift.monadLift, Veir.fail, Veir.ub, CTree.trigger_def,
      Bind.bind, CTree.CTree.bind_vis, eq_comm]

/-- Binding continues successful outcomes and propagates failure or UB. -/
@[grind =]
theorem bind_iff {X} (t : CTree E C X) (k : X → CTree E C R)
    (r : Interp R) :
    CanInterpretTo (CTree.bind t k) r ↔
      (∃ x, CanInterpretTo t (.ok x) ∧ CanInterpretTo (k x) r) ∨
      (CanInterpretTo t (.fail none) ∧ r = .fail none) ∨
      (CanInterpretTo t (.ub none) ∧ r = .ub none) := by
  constructor
  · intro h
    generalize heq : CTree.bind t k = tk at h
    have hbound := h
    induction h generalizing t
    all_goals
      cases t with
      | ret x =>
        simp only [← CTree.ret_pure, CTree.bind_ret] at heq
        exact .inl ⟨x, .ret x, heq ▸ hbound⟩
      | tau c f =>
        simp only [CTree.CTree.bind_tau] at heq
        have hhead := congrArg CTree.unfold heq
        simp only [unfold_ret, unfold_tauG, unfold_vis] at hhead
        cases hhead <;> grind
      | vis e f => grind
  · rintro (⟨x, ht, hk⟩ | ⟨ht, rfl⟩ | ⟨ht, rfl⟩)
    · generalize hs : Interp.ok x = s at ht
      induction ht <;> grind
    · generalize hs : Interp.fail (α := X) none = s at ht
      induction ht <;> grind
    · generalize hs : Interp.ub (α := X) none = s at ht
      induction ht <;> grind

/-- Mapping transforms successful outcomes and propagates failure or UB. -/
@[grind =]
theorem map_iff {X} (f : X → R) (t : CTree E C X) (r : Interp R) :
    CanInterpretTo (Functor.map f t) r ↔
      (∃ x, CanInterpretTo t (.ok x) ∧ r = .ok (f x)) ∨
      (CanInterpretTo t (.fail none) ∧ r = .fail none) ∨
      (CanInterpretTo t (.ub none) ∧ r = .ub none) := by
  simpa only [map_eq_pure_bind, Bind.bind, pure_iff] using
    (bind_iff t (fun x => pure (f x)) r)

/-- An interpreter failure has no successful outcome. -/
@[simp, grind =]
theorem fail_ok_iff (v : R) : CanInterpretTo (Veir.fail : CTree E C R) (.ok v) ↔ False := by
  simp [Veir.fail, CTree.trigger_def, Bind.bind, CTree.CTree.bind_vis]

/-- Undefined behavior has no successful outcome. -/
@[simp, grind =]
theorem ub_ok_iff (v : R) : CanInterpretTo (Veir.ub : CTree E C R) (.ok v) ↔ False := by
  simp [Veir.ub, CTree.trigger_def, Bind.bind, CTree.CTree.bind_vis]

end PureOrErr.CanInterpretTo

end Veir
