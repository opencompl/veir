module

import all Veir.Passes.InstructionSelection.RISCV64
public meta import Veir.PatternRewriter.Puddle.Validity

open Veir Veir.Puddle

/-- Check every new variant's handle bindings, native metadata dependencies, and replacement arity. -/
private def migratedPatterns : Array (Pattern OpCode) :=
  (#[32, 64].flatMap fun bw =>
    #[bswap_pattern bw, bitreverse_pattern bw, lowerConstRotate true bw,
      lowerConstRotate false bw, lowerFunnelShift true bw, lowerFunnelShift false bw]) ++
  #[lowerByteShift .shl 32 .sllw rfl, lowerByteShift .shl 64 .sll rfl,
    lowerByteShift .lshr 32 .srlw rfl, lowerByteShift .lshr 64 .srl rfl] ++
  (#[8, 32, 64].flatMap fun bw =>
    #[ashr_pattern bw, icmp_pattern bw .eq true, icmp_pattern bw .ne true] ++
    #[Data.LLVM.IntPred.eq, .ne, .slt, .sgt, .ult, .ugt, .sge, .sle, .uge, .ule].map
      (icmp_pattern bw ·)) ++
  #[constant_pattern, trunc_pattern, bitcast_pattern, freeze_pattern, poisonConst_pattern,
    select_pattern false true, select_pattern true false, select_pattern false false,
    saddSat_pattern, ssubSat_pattern, uaddSat_pattern, usubSat_pattern,
    sshlSat_pattern, ushlSat_pattern, abs_pattern,
    alloca_pattern] ++
  (#[true, false].flatMap fun foldAddr =>
    #[load_pattern 8 .lb rfl foldAddr, load_pattern 16 .lh rfl foldAddr,
      load_pattern 32 .lw rfl foldAddr, load_pattern 64 .ld rfl foldAddr,
      store_pattern 8 .sb rfl foldAddr, store_pattern 16 .sh rfl foldAddr,
      store_pattern 32 .sw rfl foldAddr, store_pattern 64 .sd rfl foldAddr]) ++
  (Array.range 6).map getelementptr_pattern

example : migratedPatterns.all (fun pattern => pattern.checkStructure.isSome) = true := by
  native_decide
