import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Passes.RISCVCombines.MIRCombinesVeir
import Veir.Passes.RISCVCombines.Combine_1
import Veir.Passes.RISCVCombines.Combine_2
import Veir.Passes.RISCVCombines.Combine_3
import Veir.Passes.RISCVCombines.Combine_4
import Veir.Passes.RISCVCombines.Combine_5
import Veir.Passes.RISCVCombines.Combine_6
import Veir.Passes.RISCVCombines.Combine_7
import Veir.Passes.RISCVCombines.Combine_8
import Veir.Passes.RISCVCombines.Combine_9
import Veir.Passes.RISCVCombines.Combine_10
import Veir.Passes.RISCVCombines.Combine_11
import Veir.Passes.RISCVCombines.Combine_12
import Veir.Passes.RISCVCombines.Combine_13
import Veir.Passes.RISCVCombines.Combine_14

namespace Veir.RISCV

/-!
  RISC-V GlobalISel-style combines.

  The immediate-selection rewrites that used to live here (folding a materialized
  constant into the immediate form of a RISC-V op) are now performed during
  instruction selection in `isel-sdag-riscv64`, matching the LLVM op directly —
  mirroring LLVM's `PatGprImm` TableGen patterns. What remains here are algebraic
  simplifications over already-selected RISC-V ops. New RISC-V combines can be
  added to the pattern list in `Combine.impl`.
-/

def Combine.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let patterns : Array (RewritePattern OpCode) :=
    #[ right_identity_zero_add
     , srl_sra_signbit
     , srlw_sraw_signbit
     , drop_slli_srli_slt
     , drop_slli_srli_sltu
     , drop_slli_srli_slti
     , drop_slli_srli_sltiu
     , drop_slli_srli_seqz
     , drop_slli_srli_snez
     , drop_slli_srli_sltz
     , drop_slli_srli_sgtz
     , zextw_zextw
     , drop_zextw_addw
     , drop_zextw_addiw
     , drop_zextw_roriw
     , drop_zextw_srliw
     , drop_zextw_sextw
     , zextw_and
     , zextw_or
     , zextw_xor
     , drop_zextw_sw
     , zextw_x0
     , zextw_li_low32
     , sextw_sextw
     , drop_sextw_addw
     , drop_sextw_addiw
     , drop_sextw_roriw
     , drop_sextw_srliw
     , drop_sextw_zextw
     , sextw_and
     , sextw_or
     , sextw_xor
     , drop_sextw_sw
     , sextw_x0
     , sextw_li_low32
     , zextb_zextb
     , zexth_zexth
     , sextb_sextb
     , sexth_sexth
     , zextb_and
     , zextb_or
     , zextb_xor
     , zexth_and
     , zexth_or
     , zexth_xor
     , sextb_and
     , sextb_or
     , sextb_xor
     , sexth_and
     , sexth_or
     , sexth_xor
     , drop_zexth_sh
     , drop_sexth_sh
     , drop_zextb_sb
     , drop_sextb_sb
     , zextb_x0
     , zexth_x0
     , sextb_x0
     , sexth_x0
     , zextb_li_low8
     , zexth_li_low16
     , sextb_li_low8
     , sexth_li_low16
     , li_zero_to_x0
     , select_same_val_self
     , select_constant_cmp_true
     , select_constant_cmp_false
     , AndSextSext
     , OrSextSext
     , XorSextSext
     , AndZextZext
     , OrZextZext
     , XorZextZext
     , AndTruncTrunc
     , OrTruncTrunc
     , XorTruncTrunc
     , AndShlShl
     , OrShlShl
     , XorShlShl
     , AndLshrLshr
     , OrLshrLshr
     , XorLshrLshr
     , AndAshrAshr
     , OrAshrAshr
     , XorAshrAshr
     , AndAndAnd
     , OrAndAnd
     , XorAndAnd
     , sub_add_reg_x_add_y_sub_y
     , sub_add_reg_x_add_y_sub_x
     , sub_add_reg_x_sub_y_add_x
     , sub_add_reg_x_sub_x_add_y
     , xor_of_and_with_same_reg
     , select_to_iminmax_ugt
     , select_to_iminmax_uge
     , select_to_iminmax_sgt
     , select_to_iminmax_sge
     , select_to_iminmax_ult
     , select_to_iminmax_ule
     , select_to_iminmax_slt
     , select_to_iminmax_sle
     , trunc_of_zext
     , select_of_zext_rw
     , select_of_truncate_rw
     , mulo_by_2_unsigned_signed
     , add_shift
     , add_shift_commute
     , redundant_binop_in_equality_XPlusYEqX
     , redundant_binop_in_equality_XPlusYNeX
     , redundant_binop_in_equality_XMinusYEqX
     , redundant_binop_in_equality_XMinusYNeX
     , redundant_binop_in_equality_XXorYEqX
     , redundant_binop_in_equality_XXorYNeX
     , select_1_0
     , select_neg1_0
     , select_0_1
     , select_0_neg1
     , not_cmp_fold_eq
     , not_cmp_fold_ne
     , not_cmp_fold_ugt
     , not_cmp_fold_uge
     , not_cmp_fold_sgt
     , not_cmp_fold_sge
     , double_icmp_zero_and_combine
     , double_icmp_zero_or_combine
     , NotAPlusNegOne_rw
     , sub_one_from_sub_rw
     , APlusC1MinusC2
     , C2MinusAPlusC1
     , AMinusC1MinusC2
     , C1MinusAMinusC2
     , AMinusC1PlusC2
     , or_and_xor_to_xor_or
     , and_xor_or_to_xor_and
     , combine_or_of_and_l
     , combine_or_of_and_r
     , AMinusBMinusC
     , shl_left_to_zero
     , lshr_left_to_zero
     , ashr_left_to_zero
     , mul_left_to_zero
     , SubSmaxSub
     , SubUmaxSub
     , narrow_binop_add
     , narrow_binop_sub
     , narrow_binop_mul
     , truncate_of_sext
     , zext_of_zext
     , sext_of_sext
     , sub_to_add
     , sub_of_mul_const
     , select_not
     , commute_const_add
     , commute_const_mul
     , commute_const_and
     , commute_const_or
     , commute_const_xor
     , SubSminSub
     , SubUminSub
     , lshr_of_trunc_of_lshr
     , funnel_shift_right_zero
     , funnel_shift_left_zero
     , canonicalize_icmp
     , bitreverse_shl
     , bitreverse_lshr
     , udiv_by_pow2
     , mul_to_shl
     , urem_pow2_to_mask
     , funnel_shift_overshift_l
     , funnel_shift_overshift_r
     , funnel_shift_or_shift_to_funnel_shift_left
     , funnel_shift_or_shift_to_funnel_shift_right
     , constant_fold_binop
     ,
     ] ++ mir_pattern_combines
  let pattern := RewritePattern.GreedyRewritePattern patterns
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def Combine : Pass OpCode :=
  { name := "riscv-combine"
    description := "GlobalISel RISCV combines"
    run := Combine.impl }
