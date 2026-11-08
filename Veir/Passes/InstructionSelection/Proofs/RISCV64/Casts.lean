module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common

/-! Instruction-selection validity proofs: Truncation, bitcasts, and integer extensions. -/

namespace Veir

open Puddle
open _root_.CTree

set_option warn.sorry false

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  Riscv.interpretOp' Llvm.interpretOp' GMIR.interpretOp'
  Builtin.interpretOpCTree Llvm.interpretOpCTree GMIR.interpretOpCTree

attribute [local implicit_reducible] TypeAttr

theorem truncInt_pattern_valid :
    Puddle.CTree.Pattern.Valid (trunc_pattern IntegerType (·.bitwidth)) := by
  unfold trunc_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

theorem truncByte_pattern_valid :
    Puddle.CTree.Pattern.Valid (trunc_pattern LLVM.ByteType (·.bitwidth)) := by
  unfold trunc_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.byteType_eq_of]
  sorry

theorem bitcastIntInt_pattern_valid :
    Puddle.CTree.Pattern.Valid
      (bitcast_pattern IntegerType IntegerType (·.bitwidth) (·.bitwidth)) := by
  unfold bitcast_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

theorem bitcastIntByte_pattern_valid :
    Puddle.CTree.Pattern.Valid
      (bitcast_pattern IntegerType LLVM.ByteType (·.bitwidth) (·.bitwidth)) := by
  unfold bitcast_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.byteType_eq_of]
  sorry

theorem bitcastIntPtr_pattern_valid :
    Puddle.CTree.Pattern.Valid
      (bitcast_pattern IntegerType LLVM.PointerType (·.bitwidth) (fun _ => 64)) := by
  unfold bitcast_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.llvmPointerType_eq_of]

theorem bitcastByteInt_pattern_valid :
    Puddle.CTree.Pattern.Valid
      (bitcast_pattern LLVM.ByteType IntegerType (·.bitwidth) (·.bitwidth)) := by
  unfold bitcast_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]
  sorry

theorem bitcastByteByte_pattern_valid :
    Puddle.CTree.Pattern.Valid
      (bitcast_pattern LLVM.ByteType LLVM.ByteType (·.bitwidth) (·.bitwidth)) := by
  unfold bitcast_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.byteType_eq_of]
  sorry

theorem bitcastPtrInt_pattern_valid :
    Puddle.CTree.Pattern.Valid
      (bitcast_pattern LLVM.PointerType IntegerType (fun _ => 64) (·.bitwidth)) := by
  unfold bitcast_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.integerType_eq_of]

theorem bitcastPtrByte_pattern_valid :
    Puddle.CTree.Pattern.Valid
      (bitcast_pattern LLVM.PointerType LLVM.ByteType (fun _ => 64) (·.bitwidth)) := by
  unfold bitcast_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.byteType_eq_of]
  sorry

theorem bitcastPtrPtr_pattern_valid :
    Puddle.CTree.Pattern.Valid
      (bitcast_pattern LLVM.PointerType LLVM.PointerType (fun _ => 64) (fun _ => 64)) := by
  unfold bitcast_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics, ←Attribute.llvmPointerType_eq_of]
  sorry

theorem gmirTrunc_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirTrunc_pattern := by
  unfold gmirTrunc_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirAnyext_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirAnyext_pattern := by
  unfold gmirAnyext_pattern
  simp only [lowerRegCast]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem gmirAnyextOfReg_pattern_valid :
    Puddle.CTree.Pattern.Valid gmirAnyextOfReg_pattern := by
  unfold gmirAnyextOfReg_pattern
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem sext16_pattern_valid :
    Puddle.CTree.Pattern.Valid sext16_pattern := by
  unfold sext16_pattern
  simp only [lowerExt, lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem sext32_pattern_valid :
    Puddle.CTree.Pattern.Valid sext32_pattern := by
  unfold sext32_pattern
  simp only [lowerExt, lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem sextInReg8_valid :
    Puddle.CTree.Pattern.Valid (sextInRegExt_pattern 8 .sextb ()) := by
  dsimp only [sextInRegExt_pattern, matchSextInReg, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem sextInReg16_valid :
    Puddle.CTree.Pattern.Valid (sextInRegExt_pattern 16 .sexth ()) := by
  dsimp only [sextInRegExt_pattern, matchSextInReg, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem sextInReg32_valid :
    Puddle.CTree.Pattern.Valid (sextInRegExt_pattern 32 .sextw ()) := by
  dsimp only [sextInRegExt_pattern, matchSextInReg, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem sextInRegShift_pattern_valid :
    Puddle.CTree.Pattern.Valid sextInRegShift_pattern := by
  unfold sextInRegShift_pattern
  simp only [matchSextInReg, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem zext16_pattern_valid :
    Puddle.CTree.Pattern.Valid zext16_pattern := by
  unfold zext16_pattern
  simp only [lowerExt, lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

theorem zext32_pattern_valid :
    Puddle.CTree.Pattern.Valid zext32_pattern := by
  unfold zext32_pattern
  simp only [lowerExt, lowerUnary, matchLegal]
  simpPuddleValid
  simp [ctree_semantics]
  sorry

end Veir
