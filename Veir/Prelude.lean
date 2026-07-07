module

public import Lean
public import Veir.PrePrelude
public meta import Veir.PrePrelude
meta import Veir.PrePrelude

public section

@[simp, grind norm]
theorem UInt64.add_int64_zero (x : UInt64) : x + (0 : Int64) = x := by
  simp [UInt64.add_int64_r_def]

@[simp, grind norm]
theorem UInt64.uint64_zero_add (x : Int64) : (0 : UInt64) + x = x.toUInt64 := by
  simp [UInt64.add_int64_r_def]

open Lean Meta Simp in
def mkInst : Expr := mkConst  `instHAddInt64UInt64_veir []
open Lean Meta Simp in
def mkInst' : Expr := mkConst `instHAddUInt64Int64_veir []

builtin_dsimproc_decl normNatAddInst ((_ + _ : Int64)) :=
  Lean.Meta.Grind.Arith.normInst 3 mkInst
builtin_dsimproc_decl normNatAddInst' ((_ + _ : UInt64)) :=
  Lean.Meta.Grind.Arith.normInst 3 mkInst'

attribute [seval] normNatAddInst normNatAddInst'

open Lean Meta Simp

private meta def uint64Lit? (e : Expr) : Option UInt64 := do
  return UInt64.ofNat (← e.nat?)

private meta def int64Lit? (e : Expr) : Option Int64 :=
  match_expr e with
  | OfNat.ofNat _ _ _ =>
    (Int64.ofNat ·) <$> e.nat?
  | Neg.neg _ _ x => do
    let_expr OfNat.ofNat _ _ _ := x | none
    return -Int64.ofNat (← e.int?.map (·.toNat))
  | _ => none

dsimproc_decl reduceMixedAdd ((_ : Int64) + (_ : UInt64)) := fun e => do
  let_expr HAdd.hAdd _ _ _ _ x y := e | return .continue
  let some xv := int64Lit? x | return .continue
  let some yv := uint64Lit? y | return .continue
  return .done (toExpr (xv + yv))

attribute [seval] reduceMixedAdd

-- TODO: Move in prelude?
instance : HAdd Nat (Std.Rco Int) (Std.Rco Int) where
  hAdd x y := (x + y.lower)...(x + y.upper)

@[grind =, layout_simp]
theorem add_nat_range_def (n : Nat) (r : Std.Rco Int) : n + r = (n+r.lower)...(n + r.upper) := rfl

attribute [grind norm] add_nat_range_def

axiom Array.usize_size (ar : Array α) : ar.usize.toUInt64.toNat = ar.size

theorem Array.size_le_uint64_size (ar : Array α) : ar.size < UInt64.size := by
  rw [← usize_size]
  exact UInt64.toNat_lt_size ar.usize.toUInt64

theorem Array.size_le_toNat {ar : Array α} {x : UInt64} (h : ar.usize.toUInt64 ≤ x) : ar.size ≤ x.toNat := by
  have := Array.usize_size ar
  rw [← this]
  assumption

macro:50 "rlet" pat:term ":=" expr:term rest:term : term =>
  `(match _ : $expr:term with
      | $pat => $rest)

macro:50 "rlet" pat:term "←" expr:term  rest:term : term =>
  `(match _ : $expr:term with
      | none => none
      | some $pat => $rest)

macro:50 "rlet" h:ident ":" pat:term "←" expr:term  rest:term : term =>
  `(match $h:ident : $expr:term with
      | none => none
      | some $pat => $rest)

-- TODO: remove this
macro:50 "rlet" pat:term "←" expr:term "in" rest:term : term =>
  `(match _ : $expr:term with
      | none => none
      | some $pat => $rest)

def Option.maybe (p : α → β → Prop) (x : Option α) (y : β) : Prop :=
  ∀ z, x = some z → p z y

theorem Option.maybe_def (p : α → β → Prop) (x : Option α) (y : β) :
    x.maybe p y ↔ ∀ z, x = some z → p z y := by
  simp [Option.maybe]

@[simp, grind =] theorem Option.maybe_some : (some x).maybe p y ↔ p x y := by grind [maybe]
@[simp, grind .] theorem Option.maybe_none : none.maybe p y := by grind [maybe]

def Option.maybe₁ (p : α → Prop) (x : Option α)  : Prop :=
  ∀ z, x = some z → p z

theorem Option.maybe₁_def (p : α → Prop) (x : Option α) :
    x.maybe₁ p ↔ ∀ z, x = some z → p z := by
  simp [Option.maybe₁]

@[simp, grind =] theorem Option.maybe₁_some : (some x).maybe₁ p ↔ p x := by grind [maybe₁]
@[simp, grind .] theorem Option.maybe₁_none : none.maybe₁ p := by grind [maybe₁]
