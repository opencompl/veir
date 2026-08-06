import Veir.Data.BitVec.Elim

open Veir.Data.BitVec

theorem trace_add_comm_manual (w : Nat) (x y : BitVec w)
  (hw : w ≤ 4)
  : x + y = y + x := by
  apply pbv_width_elim 4 w
  intro mw h_mw
  revert x
  apply pbv_var_elim 4 w hw
  intro x h_xmw
  rw[← h_mw] at h_xmw
  revert y
  apply pbv_var_elim 4 w hw
  intro y h_ymw
  rw[← h_mw] at h_ymw
  have mw_mask := mask_isMask hw h_mw
  sorry
  -- apply setWidth_inj hw
  -- simp only[pbv_setWidth_add hw, pbv_setWidth_setWidth hw]
  -- repeat rw[← h_mw]
  -- repeat rw[BitVec.setWidth_eq]
  -- bv_decide
