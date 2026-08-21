-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception AND BSD-3-Clause

module

public import CTree.Definition
public import CTree.Iter

@[expose] public section

namespace CTree
open Coinductive Lean.Order


-- FIXME D
def interp {X} (f : (i: EIn) → CTree F C (E i)) : CTree E C X → CTree F C X :=
  iter fun t =>
    match t.unfold with
    | .ret r => return (.inr r)
    | .tau i k => .tauG i (fun x => return (.inl (k x)))
    | .vis i k => do
        let o ← f i
        return (.inl (k o))

-- TODO X vs R

-- sim_interp not established yet

-- FIXME F
def refine {X} (f : (i: CIn) → CTree E D (C i)) : CTree E C X → CTree E D X :=
  iter fun t =>
    match t.unfold with
    | .ret r => return (.inr r)
    | .tau (.inl _) k => .tau1 (return .inl (k .unit))
    | .tau (.inr i) k => do
        let o ← f i
        return (.inl (k o))
    | .vis i k => .vis i (fun x => return (.inl (k x)))
