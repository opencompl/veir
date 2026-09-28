-- SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

module

public import CTree.Defs

public section

namespace CTree

/--
The `iter` combinator loops over `body` while it returns a value in `I`,
and finally returns when it returns a value in `X`.
-/
def iter {I X} (body : I -> CTree E C (I ⊕ X)) (i : I) : CTree E C X := do
  let r ← body i
  match r with
  -- Delay recursion under the continuation: Lean evaluates tau1 arguments eagerly.
  | .inl i => .tauG (.inl .c1) (fun _ => iter body i)
  | .inr r => return r
partial_fixpoint

end CTree

