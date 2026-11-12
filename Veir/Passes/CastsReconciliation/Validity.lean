module

public import Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.PatternRewriter.Puddle.CTreeProofs
public import Veir.Passes.CastsReconciliation.Reconciliation

import all Veir.Passes.CastsReconciliation.Reconciliation

/-!
# CTree validity of the cast reconciliation

The statements of `Puddle.CTree.Pattern.Valid` for every Puddle pattern that `reconcile-cast`
runs, in the order the pass tries them. None is proven yet: each is `sorry`. The integer/byte
round trip of `llvm-to-gmir`, which uses the same `reconcilePairingCast`, is proven in
`Veir.Passes.LLVMToGMIR.Validity` (`round_trip_valid`). The dead parent casts the patterns leave
behind are removed by `eliminateDeadOp`, which is not a Puddle pattern.
-/

namespace Veir.CastsReconciliation.CTreeProofs

open Puddle

theorem reg_to_i64_valid : Puddle.CTree.Pattern.Valid (reconcilePairingCast isRegToI64RoundTrip) := by
  sorry

theorem reg_to_ptr_valid : Puddle.CTree.Pattern.Valid (reconcilePairingCast isRiscvRegToPtrCast) := by
  sorry

theorem mod_arith_to_int_valid :
    Puddle.CTree.Pattern.Valid (reconcilePairingCast isPreservingModArithToIntCast) := by
  sorry

theorem cir_to_int_valid : Puddle.CTree.Pattern.Valid (reconcilePairingCast isCirToIntRoundTrip) := by
  sorry

theorem reg_int_zextb_valid : Puddle.CTree.Pattern.Valid (reconcileRegIntExt 8 .zextb ()) := by
  sorry

theorem reg_int_zexth_valid : Puddle.CTree.Pattern.Valid (reconcileRegIntExt 16 .zexth ()) := by
  sorry

theorem reg_int_zextw_valid : Puddle.CTree.Pattern.Valid (reconcileRegIntExt 32 .zextw ()) := by
  sorry

theorem reg_int_shift_valid : Puddle.CTree.Pattern.Valid reconcileRegIntShift := by
  sorry

end Veir.CastsReconciliation.CTreeProofs
