module

public import Lean
public import Veir.PrePrelude
meta import Veir.PrePrelude

public section

@[simp, grind norm]
theorem UInt64.add_int64_zero (x : UInt64) : x + (0 : Int64) = x := by
  simp [UInt64.add_int64_r_def]

@[simp, grind norm]
theorem UInt64.uint64_zero_add (x : Int64) : (0 : UInt64) + x = x.toUInt64 := by
  simp [UInt64.add_int64_r_def]


@[grind =]
theorem UInt64.toNat_toUSize_of_lt (i : UInt64) (hi : i.toNat < 2^32) :
    i.toUSize.toNat = i.toNat := by
  grind [UInt64.toNat_toUSize, System.Platform.numBits_eq]

@[grind =]
theorem Array.uget_eq_get_of_lt_uint32_max (i : UInt64) (hi : i.toNat < 2^32) (a : Array α) h :
    a.uget i.toUSize h = a[i.toNat]'(by grind) := by
  grind [Array.uget]

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

/-- When an array's size fits in a `UInt64`, `size.toUInt64` round-trips back to `size`. -/
theorem Array.size_toUInt64_toNat (ar : Array α) (h : ar.size < UInt64.size) :
    ar.size.toUInt64.toNat = ar.size := by
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  grind [Nat.mod_eq_of_lt]

theorem Array.size_le_toNat {ar : Array α} {x : UInt64}
    (hsz : ar.size < UInt64.size) (h : ar.size.toUInt64 ≤ x) : ar.size ≤ x.toNat := by
  have := Array.size_toUInt64_toNat ar hsz
  rw [← this]
  grind [UInt64.le_iff_toNat_le]

/-- When an array's size fits in a `UInt32` (in particular under the `countCard` guards of the rewriter's `create*` entry points), `usize.toUInt64` round-trips back to `size`. -/
theorem Array.usize_toUInt64_toNat (ar : Array α) (h : ar.size < UInt32.size) :
    ar.usize.toUInt64.toNat = ar.size := by
  have husize : ar.usize = USize.ofNat ar.size := rfl
  rw [husize, USize.toNat_toUInt64, USize.toNat_ofNat_of_lt_32 h]

theorem Array.usize_toUInt64_eq (ar : Array α) (h : ar.size < UInt32.size) :
    ar.usize.toUInt64 = ar.size.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [Array.usize_toUInt64_toNat ar h,
    Array.size_toUInt64_toNat ar (Nat.lt_trans h (by decide))]

theorem Array.usize_le_toNat {ar : Array α} {x : UInt64}
    (hsz : ar.size < UInt32.size) (h : ar.usize.toUInt64 ≤ x) : ar.size ≤ x.toNat := by
  have := Array.usize_toUInt64_toNat ar hsz
  rw [← this]
  grind [UInt64.le_iff_toNat_le]

/-- An array's size as a `UInt64`. -/
@[irreducible] def Array.sizeU64 (ar : Array α) : UInt64 := ar.size.toUInt64

theorem Array.sizeU64_eq (ar : Array α) : ar.sizeU64 = ar.size.toUInt64 := by
  unfold Array.sizeU64
  rfl

theorem Array.sizeU64_toNat (ar : Array α) (h : ar.size < UInt64.size) :
    ar.sizeU64.toNat = ar.size := by
  rw [sizeU64_eq]
  exact ar.size_toUInt64_toNat h

macro:50 "rlet" pat:term ":=" expr:term rest:term : term =>
  `(match _ : $expr:term with
      | $pat => $rest)

macro:50 "rlet" h:ident ":" pat:term ":=" expr:term rest:term : term =>
  `(match $h:ident : $expr:term with
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
