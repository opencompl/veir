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

theorem drop_zextw_sw_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .zextw .sw) := by
  proveStoreValid Data.RISCV.drop_zextw_sw

theorem drop_sextw_sw_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .sextw .sw) := by
  proveStoreValid Data.RISCV.drop_sextw_sw

theorem drop_zexth_sh_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .zexth .sh) := by
  proveStoreValid Data.RISCV.drop_zexth_sh

theorem drop_sexth_sh_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .sexth .sh) := by
  proveStoreValid Data.RISCV.drop_sexth_sh

theorem drop_zextb_sb_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .zextb .sb) := by
  proveStoreValid Data.RISCV.drop_zextb_sb

theorem drop_sextb_sb_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .sextb .sb) := by
  proveStoreValid Data.RISCV.drop_sextb_sb

theorem drop_zextw_sb_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .zextw .sb) := by
  proveStoreValid Data.RISCV.drop_zextw_sb

theorem drop_sextw_sb_valid :
    Puddle.CTree.Pattern.Valid (drop_ext_store_pattern .sextw .sb) := by
  proveStoreValid Data.RISCV.drop_sextw_sb

end Veir.RISCV.CTreeProofs
