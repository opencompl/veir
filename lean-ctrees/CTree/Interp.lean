-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

module

public import CTree.Defs
public import CTree.Iter

public section

namespace CTree
open Coinductive Lean.Order

variable {EIn E'In FIn CIn C'In DIn X Y : Type u} {E : EIn → Type u} {E' : E'In → Type u} {F : FIn → Type u}
  {C : CIn → Type u} {C' : C'In → Type u} {D : DIn → Type u} {R R' : Type u} (RR : R → R' → Prop)

-- TODO this should be generalized to a larger result choice family D

-- TODO do not duplicate taus when interpreting them

/--
Substitute events with subtrees according to the provided handler `h`
-/
def interp (h : (i : EIn) → CTree F C (E i)) : CTree E C X → CTree F C X :=
  iter fun t =>
    match t.unfold with
    | .ret r => return (.inr r)
    | .tau i k => .tauG i (fun x => return (.inl (k x)))
    | .vis i k => do
        let o ← h i
        return (.inl (k o))

/--
The `interp_mrec` combinator interprets effects whose interpretation can generate more of these effects,
starting from the given CTree. This is typically useful for function call effects.
-/
def interp_mrec (h : (i : EIn) → CTree (E ⊕ₑ E') C (E i)) : CTree (E ⊕ₑ E') C X → CTree E' C X :=
  iter fun (t : CTree (E ⊕ₑ E') _ _) =>
    match t.unfold with
    | .ret r => return (.inr r)
    | .tau i k => .tauG i (fun x => return (.inl (k x)))
    | .vis (.inl i) k => do
        return (.inl (h i >>= k))
    | .vis (.inr i) k => do
        .vis i (fun x => return (.inl (k x)))

/--
The `mrec` combinator interprets effects whose interpretation can generate more of these effects,
starting from the given effect. This is typically useful for function call effects.
-/
def mrec (h : (i : EIn) → CTree (E ⊕ₑ E') C (E i)) (i : EIn) : CTree E' C (E i) :=
  interp_mrec h (h i)

/--
Substitute choice nodes with subtrees according to the provided handler `h`
-/
def refine (h : (i : CIn) → CTree E D (C i)) : CTree E C X → CTree E D X :=
  iter fun t =>
    match t.unfold with
    | .ret r => return (.inr r)
    | .tau (.inl _) k => .tau1 (return .inl (k .unit))
    | .tau (.inr i) k => do
        let o ← h i
        return (.inl (k o))
    | .vis i k => .vis i (fun x => return (.inl (k x)))
