module

public import Veir.Analysis.DataFlow.Domains.AbstractDomain
public import Veir.GlobalOpInfo

public section

namespace Veir

/-!
# ModArith range analysis helpers

This file adds the lattice structure and helper functions used by ModArith range analysis.
Proofs have not been added yet.
-/

/-- A closed integer interval with an associated bitwidth. -/
structure IntegerRange where
  bitwidth : Nat
  lower : Int
  upper : Int
deriving BEq, DecidableEq, Repr

/-- Abstract integer range lattice element. -/
inductive IntegerRangeLattice where
  | bottom
  | top
  | interval (range : IntegerRange)
deriving BEq, DecidableEq, Repr

namespace IntegerRangeLattice

instance : Bot IntegerRangeLattice where
  bot := .bottom

instance : Top IntegerRangeLattice where
  top := .top

/-- Construct a singleton range for a known integer literal. -/
def singleton  (bitwidth : Nat) (value : Int) : IntegerRangeLattice :=
  .interval { bitwidth, lower := value, upper := value }

/-- Construct an exact range from an integer attribute. -/
def ofIntegerAttr (attr : IntegerAttr) : IntegerRangeLattice :=
  singleton attr.type.bitwidth attr.value

/-- Union-like merge of two abstract ranges. -/
def join : IntegerRangeLattice → IntegerRangeLattice → IntegerRangeLattice
  | .bottom, rhs => rhs
  | lhs, .bottom => lhs
  | .top, _ => .top
  | _, .top => .top
  | .interval lhs, .interval rhs =>
      if lhs.bitwidth = rhs.bitwidth then
        .interval
          { bitwidth := lhs.bitwidth
            lower := min lhs.lower rhs.lower
            upper := max lhs.upper rhs.upper }
      else
        .top

/-- Intersection-like overlap of two abstract ranges. -/
def meet : IntegerRangeLattice → IntegerRangeLattice → IntegerRangeLattice
  | .bottom, _ => .bottom
  | _, .bottom => .bottom
  | .top, rhs => rhs
  | lhs, .top => lhs
  | .interval lhs, .interval rhs =>
      if lhs.bitwidth = rhs.bitwidth then
        .interval
          { bitwidth := lhs.bitwidth
            lower := max lhs.lower rhs.lower
            upper := min lhs.upper rhs.upper }
      else
        .top


instance : Join IntegerRangeLattice where
  join := join

/-- Add two abstract integer ranges. -/
def addRange (lhs rhs : IntegerRangeLattice) : IntegerRangeLattice :=
  match lhs, rhs with
  | .bottom, _ | _, .bottom => .bottom
  | .top, _ | _, .top => .top
  | .interval lhs, .interval rhs =>
      if lhs.bitwidth = rhs.bitwidth then
        .interval
          { bitwidth := lhs.bitwidth
            lower := lhs.lower + rhs.lower
            upper := lhs.upper + rhs.upper }
      else
        .top

/-- Multiply two abstract integer ranges. -/
def mulRange (lhs rhs : IntegerRangeLattice) : IntegerRangeLattice :=
  match lhs, rhs with
  | .bottom, _ | _, .bottom => .bottom
  | .top, _ | _, .top => .top
  | .interval lhs, .interval rhs =>
      if lhs.bitwidth = rhs.bitwidth then
        let candidates := #[
          lhs.lower * rhs.lower,
          lhs.lower * rhs.upper,
          lhs.upper * rhs.lower,
          lhs.upper * rhs.upper]
        let lo := candidates.foldl min candidates[0]!
        let hi := candidates.foldl max candidates[0]!
        .interval { bitwidth := lhs.bitwidth, lower := lo, upper := hi }
      else
        .top

end IntegerRangeLattice

end Veir
