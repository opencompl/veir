module

public import Veir.Pass
public import Veir.Passes.Pipeline.Soundness
import all Init.System.ST
import all Init.System.IO
import all Veir.Pass

/-!
# From the pass runner to the pure pipeline

`PassPipeline.run` runs the passes in `IO`, where each pass may only throw. A pass whose run
under some options is a pure function (`Pass.PureUnder`) makes its step of the runner pure, and a
pipeline of such passes, run without timing, is the pure `PassPipeline.runChecked`: the cores in
order, each followed by the verifier unless it is disabled. A successful `runChecked` is a
successful `runPure` of the cores, to which the soundness theorems apply.
-/

public section
namespace Veir

/-! ## `IO` is a lawful monad -/

instance instLawfulMonadEST {ε σ : Type} : LawfulMonad (EST ε σ) :=
  LawfulMonad.mk' (EST ε σ)
    (id_map := fun x => by
      funext s
      change (match x s with
        | EST.Out.ok a s => EST.Out.ok a s
        | EST.Out.error e s => EST.Out.error e s) = x s
      cases x s <;> rfl)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun x f g => by
      funext s
      change (match (match x s with
          | EST.Out.ok a s => f a s
          | EST.Out.error e s => EST.Out.error e s) with
        | EST.Out.ok a s => g a s
        | EST.Out.error e s => EST.Out.error e s) = (match x s with
        | EST.Out.ok a s => (match f a s with
          | EST.Out.ok a s => g a s
          | EST.Out.error e s => EST.Out.error e s)
        | EST.Out.error e s => EST.Out.error e s)
      cases x s <;> rfl)

instance instLawfulMonadEIO {ε : Type} : LawfulMonad (EIO ε) :=
  inferInstanceAs (LawfulMonad (EST ε IO.RealWorld))

/-- Catching around a pure result inspects that result. -/
theorem ExceptT.run_tryCatch_pure {ε α : Type} (x : Except ε α) (handle : ε → ExceptT ε IO α) :
    (tryCatch (ExceptT.mk (pure x)) handle : ExceptT ε IO α).run =
      (match x with | .ok a => pure (.ok a) | .error e => (handle e).run) := by
  cases x <;> rfl

/-! ## Pure passes -/

/-- The pass, run under `options`, is the pure `core`. -/
@[expose]
def Pass.PureUnder (pass : Pass OpCode) (options : PassOptions) (core : PurePass) : Prop :=
  ∀ (ctx : WfIRContext OpCode) (op : OperationPtr) (h : op.InBounds ctx.raw),
    pass.run options ctx op h = ExceptT.mk (pure (core ctx op))

namespace PassPipeline

/-- `step` for the pure `core` of a pass named `name`, as a pure function. -/
@[expose]
def stepPure (name : String) (core : PurePass) (ctx : WfIRContext OpCode)
    (moduleOp : OperationPtr) (disableVerifiers : Bool) : Except String (WfIRContext OpCode) :=
  if moduleOp.InBounds ctx.raw then
    match core ctx moduleOp with
    | .error message => .error s!"pass '{name}' failed: {message}"
    | .ok ctx' =>
      if !disableVerifiers then
        match ctx'.verify moduleOp with
        | .error message => .error s!"verification failed after pass '{name}': {message}"
        | .ok () => .ok ctx'
      else .ok ctx'
  else .error s!"module is not in bounds before pass '{name}'"

/-- `runFrom` for the pure cores of the passes, as a pure function. -/
@[expose]
def runChecked : List (Pass OpCode × PassOptions) → List PurePass → WfIRContext OpCode →
    OperationPtr → Bool → Except String (WfIRContext OpCode)
  | (pass, _) :: passes, core :: cores, ctx, moduleOp, disableVerifiers => do
    let ctx ← stepPure pass.name core ctx moduleOp disableVerifiers
    runChecked passes cores ctx moduleOp disableVerifiers
  | _, _, ctx, _, _ => .ok ctx

/-- The passes are pure, under their options, with the cores. -/
@[expose]
def PureList : List (Pass OpCode × PassOptions) → List PurePass → Prop
  | [], [] => True
  | (pass, options) :: passes, core :: cores => pass.PureUnder options core ∧ PureList passes cores
  | _, _ => False

/-- The untimed step of a pure pass is its pure step. -/
theorem step_eq_stepPure {pass : Pass OpCode} {options : PassOptions} {core : PurePass}
    (pureUnder : pass.PureUnder options core) (ctx : WfIRContext OpCode)
    (moduleOp : OperationPtr) (disableVerifiers : Bool) :
    (step pass options ctx moduleOp disableVerifiers false).run =
      pure (stepPure pass.name core ctx moduleOp disableVerifiers) := by
  unfold step stepPure
  by_cases h : moduleOp.InBounds ctx.raw
  · rw [dite_eq_left h, ite_eq_left h, pureUnder ctx moduleOp h]
    cases core ctx moduleOp with
    | error message =>
      simp only [Bool.false_eq_true, ↓reduceIte, ExceptT.run_bind, ExceptT.run_tryCatch_pure,
        ExceptT.run_throw, pure_bind]
    | ok ctx' =>
      cases disableVerifiers with
      | true =>
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_true, ExceptT.run_bind,
          ExceptT.run_tryCatch_pure, ExceptT.run_pure, pure_bind]
      | false =>
        cases verify : ctx'.verify moduleOp with
        | error message =>
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, ExceptT.run_bind,
            ExceptT.run_tryCatch_pure, verify, ExceptT.run_throw, pure_bind]
        | ok u =>
          cases u
          simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, ExceptT.run_bind,
            ExceptT.run_tryCatch_pure, verify, ExceptT.run_pure, pure_bind]
  · rw [dite_eq_right h, ite_eq_right h, ExceptT.run_throw]

/-- The untimed run of pure passes is the pure run of their cores. -/
theorem runFrom_eq_runChecked {passes : List (Pass OpCode × PassOptions)} {cores : List PurePass}
    (pureList : PureList passes cores) (ctx : WfIRContext OpCode) (moduleOp : OperationPtr)
    (disableVerifiers : Bool) :
    (runFrom passes ctx moduleOp disableVerifiers false).run =
      pure (runChecked passes cores ctx moduleOp disableVerifiers) := by
  induction passes generalizing cores ctx with
  | nil =>
    cases cores with
    | nil => rfl
    | cons core cores => exact absurd pureList id
  | cons passOptions passes ih =>
    obtain ⟨pass, options⟩ := passOptions
    cases cores with
    | nil => exact absurd pureList id
    | cons core cores =>
      obtain ⟨pureUnder, pureList⟩ := pureList
      show (step pass options ctx moduleOp disableVerifiers false >>= fun ctx =>
        runFrom passes ctx moduleOp disableVerifiers false).run =
        pure (stepPure pass.name core ctx moduleOp disableVerifiers >>= fun ctx =>
          runChecked passes cores ctx moduleOp disableVerifiers)
      rw [ExceptT.run_bind, step_eq_stepPure pureUnder, pure_bind]
      cases stepPure pass.name core ctx moduleOp disableVerifiers with
      | error message => rfl
      | ok ctx' =>
        simp only [Bind.bind, Except.bind]
        exact ih pureList ctx'

/-- A successful checked run is a successful run of the cores, to the same context. -/
theorem runChecked_ok {passes : List (Pass OpCode × PassOptions)} {cores : List PurePass}
    (pureList : PureList passes cores) {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr}
    {disableVerifiers : Bool}
    (run : runChecked passes cores ctx moduleOp disableVerifiers = .ok ctx') :
    runPure cores ctx moduleOp = .ok ctx' := by
  induction passes generalizing cores ctx with
  | nil =>
    cases cores with
    | nil => cases run; rfl
    | cons core cores => exact absurd pureList id
  | cons passOptions passes ih =>
    obtain ⟨pass, options⟩ := passOptions
    cases cores with
    | nil => exact absurd pureList id
    | cons core cores =>
      obtain ⟨_, pureList⟩ := pureList
      rw [runPure_cons]
      change (stepPure pass.name core ctx moduleOp disableVerifiers >>= fun ctx =>
        runChecked passes cores ctx moduleOp disableVerifiers) = .ok ctx' at run
      unfold stepPure at run
      by_cases h : moduleOp.InBounds ctx.raw
      · rw [ite_eq_left h] at run
        cases step : core ctx moduleOp with
        | error message => simp [step, Bind.bind, Except.bind] at run
        | ok middle =>
          rw [step] at run
          cases disableVerifiers with
          | true =>
            simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind] at run ⊢
            exact ih pureList run
          | false =>
            simp only [Bool.not_false, ↓reduceIte] at run
            cases verify : middle.verify moduleOp with
            | error message => simp [verify, Bind.bind, Except.bind] at run
            | ok u =>
              cases u
              simp only [verify, Bind.bind, Except.bind] at run ⊢
              exact ih pureList run
      · rw [ite_eq_right h] at run
        simp [Bind.bind, Except.bind] at run

/-- A successful untimed run of a pipeline of sound pure passes refines the module and leaves it
verified. The first pass must be sound: the runner checks nothing of its input. -/
theorem run_sound {pipeline : PassPipeline OpCode} {core : PurePass} {cores : List PurePass}
    (pureList : PureList pipeline.passes.toList (core :: cores))
    (sound : ∀ core' ∈ core :: cores, core'.Sound)
    {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr} {disableVerifiers : Bool}
    {s s' : Void IO.RealWorld}
    (run : (pipeline.run ctx moduleOp disableVerifiers false).run s = .ok (.ok ctx') s') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ctx'.Verified moduleOp := by
  unfold PassPipeline.run at run
  rw [runFrom_eq_runChecked pureList] at run
  change EST.Out.ok (runChecked pipeline.passes.toList (core :: cores) ctx moduleOp
    disableVerifiers) s = EST.Out.ok (.ok ctx') s' at run
  obtain ⟨checked, rfl⟩ := EST.Out.ok.inj run
  exact runPure_sound_of_head sound (runChecked_ok pureList checked)

end PassPipeline
end Veir
end
