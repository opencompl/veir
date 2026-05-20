module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring

namespace Veir.Data.Felt

public section

/-!
  ## Felt semantic model

  A field-element value, modeled as `ZMod p` where `p` is the
  (eventual) prime modulus of the underlying field.

  LLZK leaves the modulus implicit at the dialect level (`!felt.type`
  vs. `!felt.type<"bn254">`), so the IR is agnostic about which
  specific `ZMod p` it will eventually be specialized to. The
  semantic model therefore parameterizes on `p` and the surrounding
  proofs quantify universally over `p`.

  History: Phase E.1 through E.4 used the provisional `abbrev Felt
  := Int`, sound only for identities that hold under reduction by
  any modulus. Phase E.5 (2026-05-19) upgraded to the proper field
  model after adding Mathlib as a dependency.

  Note: identities such as `x + 0 = x` and `x - x = 0` hold in every
  `ZMod p` regardless of primality, so the `[Fact p.Prime]` instance
  is *not* threaded through these basic rewrites. Multiplicative
  inverses and division will need primality; the relevant lemmas
  will pick it up via `Fact (p.Prime)` at the call site.

  The `linter.dupNamespace` warning on `Veir.Data.Felt.Felt` is
  suppressed locally; changing the outer namespace would touch every
  consumer.
-/

set_option linter.dupNamespace false in
abbrev Felt (p : Nat) := ZMod p

/-- The constant `n` as a felt under modulus `p`. -/
def const (p : Nat) (n : Int) : Felt p := (n : ZMod p)

/-- Field addition. -/
def add {p : Nat} (a b : Felt p) : Felt p := a + b

/-- Field subtraction. -/
def sub {p : Nat} (a b : Felt p) : Felt p := a - b

end

end Veir.Data.Felt
