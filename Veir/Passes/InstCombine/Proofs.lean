module

import Veir.Passes.InstCombine.Proofs.Basic
import Veir.Passes.InstCombine.Proofs.Bitwise
import Veir.Passes.InstCombine.Proofs.Constants
import Veir.Passes.InstCombine.Proofs.Unsigned
import Veir.Passes.InstCombine.Proofs.Signed

/-!
Validity proofs for 69 of the 312 `InstructionSimplify` rule families, using the same
`Puddle.CTree.Pattern.Valid` contract as the RV64 passes. Each named theorem
quantifies over every operand orientation. No restriction on integer width is
added beyond the original matcher.

This is not yet a proof of the entire rewrite table. In particular, aggregate
and overflow-result rules lack aggregate interpreter semantics, pointer-valued
selects lack interpreter support, and undef rules need nondeterministic semantics.
The remaining arithmetic and bit-manipulation rules also require proofs.
-/
