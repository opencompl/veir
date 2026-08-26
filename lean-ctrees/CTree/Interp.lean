-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

module

public import CTree.Definition
public import CTree.Iter

public section

namespace CTree
open Coinductive Lean.Order

variable {EIn FIn CIn C'In DIn X Y : Type u} {E : EIn → Type u} {F : FIn → Type u} {C : CIn → Type u} {C' : C'In → Type u} {D : DIn → Type u} {R R' : Type u} (RR : R → R' → Prop)

-- FIXME D
def interp (h : (i: EIn) → CTree F C (E i)) : CTree E C X → CTree F C X :=
  iter fun t =>
    match t.unfold with
    | .ret r => return (.inr r)
    | .tau i k => .tauG i (fun x => return (.inl (k x)))
    | .vis i k => do
        let o ← h i
        return (.inl (k o))

-- TODO X vs R

-- sim_interp not established yet

-- FIXME F
def refine (h : (i: CIn) → CTree E D (C i)) : CTree E C X → CTree E D X :=
  iter fun t =>
    match t.unfold with
    | .ret r => return (.inr r)
    | .tau (.inl _) k => .tau1 (return .inl (k .unit))
    | .tau (.inr i) k => do
        let o ← h i
        return (.inl (k o))
    | .vis i k => .vis i (fun x => return (.inl (k x)))
