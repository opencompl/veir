module

public import Veir.PatternRewriter.Puddle.CTreeValidity
import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.Passes.InstructionSelection.RISCV64UnaryValidity
import all Veir.Passes.InstructionSelection.RISCV64BinaryValidity
import all Veir.Passes.InstructionSelection.RISCV64ComparisonValidity
import all Veir.Passes.InstructionSelection.RISCV64ZeroComparisonValidity
import all Veir.Passes.InstructionSelection.RISCV64ShiftValidity
import all Veir.Passes.InstructionSelection.RISCV64ByteShiftValidity
import all Veir.Passes.InstructionSelection.RISCV64CastValidity
import all Veir.Passes.InstructionSelection.RISCV64SequenceValidity
import all Veir.Passes.InstructionSelection.RISCV64SequenceExtraValidity
import all Veir.Passes.InstructionSelection.RISCV64BitcastValidity
import all Veir.Passes.InstructionSelection.RISCV64ValidityObstructions

/-!
CTree validity certificates for the pure instruction-selection patterns.

The list below records each certified pattern together with its proof. It covers
the integer and byte lowerings, with `scalarBitcast_pattern` specializing the
original bitcast matcher to integer and byte types. It does not certify the
pointer cases of `bitcast_pattern` or the GEP patterns: `CanInterpretTo` erases
the input memory, which is needed to relate pointer provenance and numerical
addresses. `RISCV64ValidityObstructions` proves that alloca, load, and store
cannot satisfy this `Valid` predicate because it excludes memory effects.
-/

namespace Veir.InstructionSelection.CTreeProofs

open Puddle

public section

/-- The certified portion of RISCV64 instruction selection, including scalar bitcasts. -/
def certifiedPatterns : List { pattern : Pattern OpCode // Puddle.CTree.Pattern.Valid pattern } :=
  [
    ⟨ctlz64_pattern, Veir.InstructionSelection.CTreeProofs.ctlz64_valid⟩,
    ⟨ctlz32_pattern, Veir.InstructionSelection.CTreeProofs.ctlz32_valid⟩,
    ⟨cttz64_pattern, Veir.InstructionSelection.CTreeProofs.cttz64_valid⟩,
    ⟨cttz32_pattern, Veir.InstructionSelection.CTreeProofs.cttz32_valid⟩,
    ⟨ctpop64_pattern, Veir.InstructionSelection.CTreeProofs.ctpop64_valid⟩,
    ⟨ctpop32_pattern, Veir.InstructionSelection.CTreeProofs.ctpop32_valid⟩,
    ⟨add64_pattern, Veir.add64_pattern_valid⟩,
    ⟨add32_pattern, Veir.add32_pattern_valid⟩,
    ⟨sub64_pattern, Veir.sub64_pattern_valid⟩,
    ⟨sub32_pattern, Veir.sub32_pattern_valid⟩,
    ⟨mul64_pattern, Veir.mul64_pattern_valid⟩,
    ⟨mul32_pattern, Veir.mul32_pattern_valid⟩,
    ⟨xor64_pattern, Veir.xor64_pattern_valid⟩,
    ⟨xor32_pattern, Veir.xor32_pattern_valid⟩,
    ⟨smax64_pattern, Veir.smax64_pattern_valid⟩,
    ⟨smin64_pattern, Veir.smin64_pattern_valid⟩,
    ⟨smax32_pattern, Veir.smax32_pattern_valid⟩,
    ⟨smin32_pattern, Veir.smin32_pattern_valid⟩,
    ⟨and_pattern, Veir.and_pattern_valid⟩,
    ⟨or_pattern, Veir.or_pattern_valid⟩,
    ⟨umax_pattern, Veir.umax_pattern_valid⟩,
    ⟨umin_pattern, Veir.umin_pattern_valid⟩,
    ⟨fshl64_pattern, Veir.fshl64_pattern_valid⟩,
    ⟨fshl32_pattern, Veir.fshl32_pattern_valid⟩,
    ⟨fshr64_pattern, Veir.fshr64_pattern_valid⟩,
    ⟨fshr32_pattern, Veir.fshr32_pattern_valid⟩,
    ⟨sdiv64_pattern, Veir.sdiv64_pattern_valid⟩,
    ⟨sdiv32_pattern, Veir.sdiv32_pattern_valid⟩,
    ⟨udiv64_pattern, Veir.udiv64_pattern_valid⟩,
    ⟨udiv32_pattern, Veir.udiv32_pattern_valid⟩,
    ⟨srem64_pattern, Veir.srem64_pattern_valid⟩,
    ⟨srem32_pattern, Veir.srem32_pattern_valid⟩,
    ⟨urem64_pattern, Veir.urem64_pattern_valid⟩,
    ⟨urem32_pattern, Veir.urem32_pattern_valid⟩,
    ⟨sext8_pattern, Veir.sext8_pattern_valid⟩,
    ⟨sext16_pattern, Veir.sext16_pattern_valid⟩,
    ⟨sext32_pattern, Veir.sext32_pattern_valid⟩,
    ⟨zext8_pattern, Veir.zext8_pattern_valid⟩,
    ⟨zext16_pattern, Veir.zext16_pattern_valid⟩,
    ⟨zext32_pattern, Veir.zext32_pattern_valid⟩,
    ⟨(icmp_pattern 64 .eq), Veir.InstructionSelection.CTreeProofs.icmp64_eq_valid⟩,
    ⟨(icmp_pattern 64 .ne), Veir.InstructionSelection.CTreeProofs.icmp64_ne_valid⟩,
    ⟨(icmp_pattern 64 .slt), Veir.InstructionSelection.CTreeProofs.icmp64_slt_valid⟩,
    ⟨(icmp_pattern 64 .sle), Veir.InstructionSelection.CTreeProofs.icmp64_sle_valid⟩,
    ⟨(icmp_pattern 64 .sgt), Veir.InstructionSelection.CTreeProofs.icmp64_sgt_valid⟩,
    ⟨(icmp_pattern 64 .sge), Veir.InstructionSelection.CTreeProofs.icmp64_sge_valid⟩,
    ⟨(icmp_pattern 64 .ult), Veir.InstructionSelection.CTreeProofs.icmp64_ult_valid⟩,
    ⟨(icmp_pattern 64 .ule), Veir.InstructionSelection.CTreeProofs.icmp64_ule_valid⟩,
    ⟨(icmp_pattern 64 .ugt), Veir.InstructionSelection.CTreeProofs.icmp64_ugt_valid⟩,
    ⟨(icmp_pattern 64 .uge), Veir.InstructionSelection.CTreeProofs.icmp64_uge_valid⟩,
    ⟨(icmp_pattern 32 .eq), Veir.InstructionSelection.CTreeProofs.icmp32_eq_valid⟩,
    ⟨(icmp_pattern 32 .ne), Veir.InstructionSelection.CTreeProofs.icmp32_ne_valid⟩,
    ⟨(icmp_pattern 32 .slt), Veir.InstructionSelection.CTreeProofs.icmp32_slt_valid⟩,
    ⟨(icmp_pattern 32 .sle), Veir.InstructionSelection.CTreeProofs.icmp32_sle_valid⟩,
    ⟨(icmp_pattern 32 .sgt), Veir.InstructionSelection.CTreeProofs.icmp32_sgt_valid⟩,
    ⟨(icmp_pattern 32 .sge), Veir.InstructionSelection.CTreeProofs.icmp32_sge_valid⟩,
    ⟨(icmp_pattern 32 .ult), Veir.InstructionSelection.CTreeProofs.icmp32_ult_valid⟩,
    ⟨(icmp_pattern 32 .ule), Veir.InstructionSelection.CTreeProofs.icmp32_ule_valid⟩,
    ⟨(icmp_pattern 32 .ugt), Veir.InstructionSelection.CTreeProofs.icmp32_ugt_valid⟩,
    ⟨(icmp_pattern 32 .uge), Veir.InstructionSelection.CTreeProofs.icmp32_uge_valid⟩,
    ⟨(icmp_pattern 8 .eq), Veir.InstructionSelection.CTreeProofs.icmp8_eq_valid⟩,
    ⟨(icmp_pattern 8 .ne), Veir.InstructionSelection.CTreeProofs.icmp8_ne_valid⟩,
    ⟨(icmp_pattern 8 .slt), Veir.InstructionSelection.CTreeProofs.icmp8_slt_valid⟩,
    ⟨(icmp_pattern 8 .sle), Veir.InstructionSelection.CTreeProofs.icmp8_sle_valid⟩,
    ⟨(icmp_pattern 8 .sgt), Veir.InstructionSelection.CTreeProofs.icmp8_sgt_valid⟩,
    ⟨(icmp_pattern 8 .sge), Veir.InstructionSelection.CTreeProofs.icmp8_sge_valid⟩,
    ⟨(icmp_pattern 8 .ult), Veir.InstructionSelection.CTreeProofs.icmp8_ult_valid⟩,
    ⟨(icmp_pattern 8 .ule), Veir.InstructionSelection.CTreeProofs.icmp8_ule_valid⟩,
    ⟨(icmp_pattern 8 .ugt), Veir.InstructionSelection.CTreeProofs.icmp8_ugt_valid⟩,
    ⟨(icmp_pattern 8 .uge), Veir.InstructionSelection.CTreeProofs.icmp8_uge_valid⟩,
    ⟨(icmp_pattern 64 .eq true), Veir.InstructionSelection.CTreeProofs.icmp64_eq_zero_valid⟩,
    ⟨(icmp_pattern 64 .ne true), Veir.InstructionSelection.CTreeProofs.icmp64_ne_zero_valid⟩,
    ⟨(icmp_pattern 32 .eq true), Veir.InstructionSelection.CTreeProofs.icmp32_eq_zero_valid⟩,
    ⟨(icmp_pattern 32 .ne true), Veir.InstructionSelection.CTreeProofs.icmp32_ne_zero_valid⟩,
    ⟨(icmp_pattern 8 .eq true), Veir.InstructionSelection.CTreeProofs.icmp8_eq_zero_valid⟩,
    ⟨(icmp_pattern 8 .ne true), Veir.InstructionSelection.CTreeProofs.icmp8_ne_zero_valid⟩,
    ⟨(ashr_pattern 8), Veir.InstructionSelection.CTreeProofs.ashr8_valid⟩,
    ⟨(ashr_pattern 32), Veir.InstructionSelection.CTreeProofs.ashr32_valid⟩,
    ⟨(ashr_pattern 64), Veir.InstructionSelection.CTreeProofs.ashr64_valid⟩,
    ⟨(lowerByteShift .lshr 32 .srlw rfl), Veir.InstructionSelection.CTreeProofs.lshr32_valid⟩,
    ⟨(lowerByteShift .lshr 64 .srl rfl), Veir.InstructionSelection.CTreeProofs.lshr64_valid⟩,
    ⟨(lowerByteShift .shl 32 .sllw rfl), Veir.InstructionSelection.CTreeProofs.shl32_valid⟩,
    ⟨(lowerByteShift .shl 64 .sll rfl), Veir.InstructionSelection.CTreeProofs.shl64_valid⟩,
    ⟨freeze_pattern, Veir.freeze_pattern_valid⟩,
    ⟨constant_pattern, Veir.constant_pattern_valid⟩,
    ⟨poisonConst_pattern, Veir.poisonConst_pattern_valid⟩,
    ⟨trunc_pattern, Veir.trunc_pattern_valid⟩,
    ⟨abs_pattern, Veir.abs_pattern_valid⟩,
    ⟨usubSat_pattern, Veir.usubSat_pattern_valid⟩,
    ⟨uaddSat_pattern, Veir.uaddSat_pattern_valid⟩,
    ⟨saddSat_pattern, Veir.saddSat_pattern_valid⟩,
    ⟨ssubSat_pattern, Veir.ssubSat_pattern_valid⟩,
    ⟨sshlSat_pattern, Veir.sshlSat_pattern_valid⟩,
    ⟨ushlSat_pattern, Veir.ushlSat_pattern_valid⟩,
    ⟨(bswap_pattern 64), Veir.bswap64_pattern_valid⟩,
    ⟨(bswap_pattern 32), Veir.bswap32_pattern_valid⟩,
    ⟨(bitreverse_pattern 64), Veir.bitreverse64_pattern_valid⟩,
    ⟨(bitreverse_pattern 32), Veir.bitreverse32_pattern_valid⟩,
    ⟨(lowerFunnelShift true 64), Veir.fshl64General_pattern_valid⟩,
    ⟨(lowerFunnelShift true 32), Veir.fshl32General_pattern_valid⟩,
    ⟨(lowerFunnelShift false 64), Veir.fshr64General_pattern_valid⟩,
    ⟨(lowerFunnelShift false 32), Veir.fshr32General_pattern_valid⟩,
    ⟨(select_pattern false false), Veir.selectGeneral_pattern_valid⟩,
    ⟨(select_pattern false true), Veir.selectZeroFalse_pattern_valid⟩,
    ⟨(select_pattern true false), Veir.selectZeroTrue_pattern_valid⟩,
    ⟨(lowerConstRotate true 64), Veir.fshl64Const_pattern_valid⟩,
    ⟨(lowerConstRotate true 32), Veir.fshl32Const_pattern_valid⟩,
    ⟨(lowerConstRotate false 64), Veir.fshr64Const_pattern_valid⟩,
    ⟨(lowerConstRotate false 32), Veir.fshr32Const_pattern_valid⟩,
    ⟨scalarBitcast_pattern, Veir.scalarBitcast_pattern_valid⟩
  ]

/-- Every pattern in the certificate inventory satisfies the CTree validity predicate. -/
theorem certifiedPatterns_valid (pattern : Pattern OpCode)
    (h : pattern ∈ certifiedPatterns.map Subtype.val) :
    Puddle.CTree.Pattern.Valid pattern := by
  obtain ⟨certificate, _, rfl⟩ := List.mem_map.mp h
  exact certificate.property

end
end Veir.InstructionSelection.CTreeProofs
