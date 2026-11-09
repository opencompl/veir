module

import all Veir.Passes.RISCVCombines.Validity.Common

/-! CTree validity proofs for the RISC-V combines: extensions of a stored value. -/

namespace Veir.RISCV.CTreeProofs

open Puddle
open _root_.CTree

set_option linter.unusedSimpArgs false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Rv64.interpretOp'

attribute [local implicit_reducible] TypeAttr Veir._propertiesOf Riscv.propertiesOf

/-- `zextw` preserves the low 32 bits, hence the first 4 stored byte(s). -/
theorem zextw_store_bytes_4 (v : Data.RISCV.Reg) :
    ({ toBitVec := (Data.RISCV.zextw v).val } : UInt64).toByteArrayLE.extract 0 4 =
      ({ toBitVec := v.val } : UInt64).toByteArrayLE.extract 0 4 :=
  toByteArrayLE_extract_four (by veir_bv_decide)

theorem drop_zextw_sw_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .zextw .sw) := by
  unfold drop_ext_store_pattern
  proveStoreValid zextw_store_bytes_4

/-- `sextw` preserves the low 32 bits, hence the first 4 stored byte(s). -/
theorem sextw_store_bytes_4 (v : Data.RISCV.Reg) :
    ({ toBitVec := (Data.RISCV.sextw v).val } : UInt64).toByteArrayLE.extract 0 4 =
      ({ toBitVec := v.val } : UInt64).toByteArrayLE.extract 0 4 :=
  toByteArrayLE_extract_four (by veir_bv_decide)

theorem drop_sextw_sw_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .sextw .sw) := by
  unfold drop_ext_store_pattern
  proveStoreValid sextw_store_bytes_4

/-- `zexth` preserves the low 16 bits, hence the first 2 stored byte(s). -/
theorem zexth_store_bytes_2 (v : Data.RISCV.Reg) :
    ({ toBitVec := (Data.RISCV.zexth v).val } : UInt64).toByteArrayLE.extract 0 2 =
      ({ toBitVec := v.val } : UInt64).toByteArrayLE.extract 0 2 :=
  toByteArrayLE_extract_two (by veir_bv_decide)

theorem drop_zexth_sh_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .zexth .sh) := by
  unfold drop_ext_store_pattern
  proveStoreValid zexth_store_bytes_2

/-- `sexth` preserves the low 16 bits, hence the first 2 stored byte(s). -/
theorem sexth_store_bytes_2 (v : Data.RISCV.Reg) :
    ({ toBitVec := (Data.RISCV.sexth v).val } : UInt64).toByteArrayLE.extract 0 2 =
      ({ toBitVec := v.val } : UInt64).toByteArrayLE.extract 0 2 :=
  toByteArrayLE_extract_two (by veir_bv_decide)

theorem drop_sexth_sh_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .sexth .sh) := by
  unfold drop_ext_store_pattern
  proveStoreValid sexth_store_bytes_2

/-- `zextb` preserves the low 8 bits, hence the first 1 stored byte(s). -/
theorem zextb_store_bytes_1 (v : Data.RISCV.Reg) :
    ({ toBitVec := (Data.RISCV.zextb v).val } : UInt64).toByteArrayLE.extract 0 1 =
      ({ toBitVec := v.val } : UInt64).toByteArrayLE.extract 0 1 :=
  toByteArrayLE_extract_one (by veir_bv_decide)

theorem drop_zextb_sb_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .zextb .sb) := by
  unfold drop_ext_store_pattern
  proveStoreValid zextb_store_bytes_1

/-- `sextb` preserves the low 8 bits, hence the first 1 stored byte(s). -/
theorem sextb_store_bytes_1 (v : Data.RISCV.Reg) :
    ({ toBitVec := (Data.RISCV.sextb v).val } : UInt64).toByteArrayLE.extract 0 1 =
      ({ toBitVec := v.val } : UInt64).toByteArrayLE.extract 0 1 :=
  toByteArrayLE_extract_one (by veir_bv_decide)

theorem drop_sextb_sb_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .sextb .sb) := by
  unfold drop_ext_store_pattern
  proveStoreValid sextb_store_bytes_1

/-- `zextw` preserves the low 8 bits, hence the first 1 stored byte(s). -/
theorem zextw_store_bytes_1 (v : Data.RISCV.Reg) :
    ({ toBitVec := (Data.RISCV.zextw v).val } : UInt64).toByteArrayLE.extract 0 1 =
      ({ toBitVec := v.val } : UInt64).toByteArrayLE.extract 0 1 :=
  toByteArrayLE_extract_one (by veir_bv_decide)

theorem drop_zextw_sb_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .zextw .sb) := by
  unfold drop_ext_store_pattern
  proveStoreValid zextw_store_bytes_1

/-- `sextw` preserves the low 8 bits, hence the first 1 stored byte(s). -/
theorem sextw_store_bytes_1 (v : Data.RISCV.Reg) :
    ({ toBitVec := (Data.RISCV.sextw v).val } : UInt64).toByteArrayLE.extract 0 1 =
      ({ toBitVec := v.val } : UInt64).toByteArrayLE.extract 0 1 :=
  toByteArrayLE_extract_one (by veir_bv_decide)

theorem drop_sextw_sb_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .sextw .sb) := by
  unfold drop_ext_store_pattern
  proveStoreValid sextw_store_bytes_1

end Veir.RISCV.CTreeProofs
