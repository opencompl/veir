import Veir.Pass
import Veir.Passes.Matching

namespace Veir.RISCV

/-!
  This file replicates LLVM's GlobalISel RISC-V legalizer (RISCVLegalizerInfo).

  On RV64, an LLVM operation is legal when the RISC-V 64-bit instruction selection pass
  can directly lower it without first transforming types or widths:
  - Integer arithmetic (add, sub, mul, sdiv, udiv, srem, urem): legal iff all types are i64.
  - Bitwise/shift (and, or, xor, shl, lshr, ashr): legal iff all types are i64.
  - Comparison (icmp): legal iff both operands are i64.
  - Constant: legal iff the result is i64.
  - Type conversions (sext, zext, trunc): legal iff both source and result widths are ≤ 64.
  - Memory (load): legal iff the loaded type is i64.
-/

/-! ## Helpers -/

private def isIntWidth (v : ValuePtr) (ctx : IRContext OpCode) (w : Nat) : Bool :=
  match (v.getType! ctx).val with
  | .integerType t => t.bitwidth == w
  | _ => false

private def isIntWidthAtMost (v : ValuePtr) (ctx : IRContext OpCode) (w : Nat) : Bool :=
  match (v.getType! ctx).val with
  | .integerType t => t.bitwidth ≤ w
  | _ => false

private def resultIsIntWidth (op : OperationPtr) (ctx : IRContext OpCode) (w : Nat) : Bool :=
  match ((op.getResult 0).get! ctx).type.val with
  | .integerType t => t.bitwidth == w
  | _ => false

private def resultIsIntWidthAtMost (op : OperationPtr) (ctx : IRContext OpCode) (w : Nat) : Bool :=
  match ((op.getResult 0).get! ctx).type.val with
  | .integerType t => t.bitwidth ≤ w
  | _ => false

private def binaryI64Legal (op : OperationPtr) (ctx : IRContext OpCode) (lhs rhs : ValuePtr) : Bool :=
  isIntWidth lhs ctx 64 && isIntWidth rhs ctx 64 && resultIsIntWidth op ctx 64

/-! ## Per-operation legality predicates -/

/--
  `llvm.constant` is legal iff the result type is `i64`.
  Mirrors: `setAction({G_CONSTANT, s64}, Legal)`.
-/
def isLegalConstant (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchConstantIntOp op ctx with
  | none => false
  | some _ => resultIsIntWidth op ctx 64

/--
  `llvm.add` is legal iff both operands and the result are `i64`.
  Mirrors: `setAction({G_ADD, s64}, Legal)`.
-/
def isLegalAdd (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchAdd op ctx with
  | none => false
  | some (lhs, rhs, _) => binaryI64Legal op ctx lhs rhs

/--
  `llvm.sub` is legal iff both operands and the result are `i64`.
  Mirrors: `setAction({G_SUB, s64}, Legal)`.
-/
def isLegalSub (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchSub op ctx with
  | none => false
  | some (lhs, rhs, _) => binaryI64Legal op ctx lhs rhs

/--
  `llvm.mul` is legal iff both operands and the result are `i64`.
  Mirrors: `setAction({G_MUL, s64}, Legal)` (requires Zmmul/M extension).
-/
def isLegalMul (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchMul op ctx with
  | none => false
  | some (lhs, rhs, _) => binaryI64Legal op ctx lhs rhs

/--
  `llvm.sdiv` is legal iff both operands and the result are `i64`.
  Mirrors: `setAction({G_SDIV, s64}, Legal)` (requires M extension).
-/
def isLegalSdiv (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchSdiv op ctx with
  | none => false
  | some (lhs, rhs, _) => binaryI64Legal op ctx lhs rhs

/--
  `llvm.udiv` is legal iff both operands and the result are `i64`.
  Mirrors: `setAction({G_UDIV, s64}, Legal)` (requires M extension).
-/
def isLegalUdiv (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchUdiv op ctx with
  | none => false
  | some (lhs, rhs, _) => binaryI64Legal op ctx lhs rhs

/--
  `llvm.srem` is legal iff both operands and the result are `i64`.
  Mirrors: `setAction({G_SREM, s64}, Legal)` (requires M extension).
-/
def isLegalSrem (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchSrem op ctx with
  | none => false
  | some (lhs, rhs, _) => binaryI64Legal op ctx lhs rhs

/--
  `llvm.urem` is legal iff both operands and the result are `i64`.
  Mirrors: `setAction({G_UREM, s64}, Legal)` (requires M extension).
-/
def isLegalUrem (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchUrem op ctx with
  | none => false
  | some (lhs, rhs, _) => binaryI64Legal op ctx lhs rhs

/--
  `llvm.and` is legal iff both operands and the result are `i64`.
  Mirrors: `setAction({G_AND, s64}, Legal)`.
-/
def isLegalAnd (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchAnd op ctx with
  | none => false
  | some (lhs, rhs) => binaryI64Legal op ctx lhs rhs

/--
  `llvm.or` is legal iff both operands and the result are `i64`.
  Mirrors: `setAction({G_OR, s64}, Legal)`.
-/
def isLegalOr (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchOr op ctx with
  | none => false
  | some (lhs, rhs, _) => binaryI64Legal op ctx lhs rhs

/--
  `llvm.xor` is legal iff both operands and the result are `i64`.
  Mirrors: `setAction({G_XOR, s64}, Legal)`.
-/
def isLegalXor (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchXor op ctx with
  | none => false
  | some (lhs, rhs, _) => binaryI64Legal op ctx lhs rhs

/--
  `llvm.ashr` is legal iff both operands and the result are `i64`.
  Mirrors: `setAction({G_ASHR, {s64, s64}}, Legal)`.
-/
def isLegalAshr (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchAshr op ctx with
  | none => false
  | some (lhs, rhs, _) => binaryI64Legal op ctx lhs rhs

/--
  `llvm.lshr` is legal iff both operands and the result are `i64`.
  Mirrors: `setAction({G_LSHR, {s64, s64}}, Legal)`.
-/
def isLegalLshr (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchLshr op ctx with
  | none => false
  | some (lhs, rhs, _) => binaryI64Legal op ctx lhs rhs

/--
  `llvm.shl` is legal iff both operands and the result are `i64`.
  Mirrors: `setAction({G_SHL, {s64, s64}}, Legal)`.
-/
def isLegalShl (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchShl op ctx with
  | none => false
  | some (lhs, rhs, _) => binaryI64Legal op ctx lhs rhs

/--
  `llvm.icmp` is legal iff both operands are `i64`.
  The result type (i1) is always produced correctly.
  Mirrors: `setAction({G_ICMP, {s64, s64}}, Legal)`.
-/
def isLegalIcmp (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchIcmp op ctx with
  | none => false
  | some (lhs, rhs, _) => isIntWidth lhs ctx 64 && isIntWidth rhs ctx 64

/--
  `llvm.sext` is legal iff both source and destination widths are ≤ 64.
  Covers i8→iY via sextb, i16→iY via sexth, i32→iY via sextw,
  and iX→iY via slli/srai for all other widths.
  Mirrors: `setAction({G_SEXT, {sXLen, s8/s16/s32}}, Legal)`.
-/
def isLegalSext (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchSext op ctx with
  | none => false
  | some (operand, _) =>
    isIntWidthAtMost operand ctx 64 && resultIsIntWidthAtMost op ctx 64

/--
  `llvm.zext` is legal iff both source and destination widths are ≤ 64.
  Covers i8→iY via zextb, i16→iY via zexth, i32→iY via zextw,
  narrow widths via andi, and general widths via slli/srli.
  Mirrors: `setAction({G_ZEXT, {sXLen, s8/s16/s32}}, Legal)`.
-/
def isLegalZext (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchZext op ctx with
  | none => false
  | some (operand, _) =>
    isIntWidthAtMost operand ctx 64 && resultIsIntWidthAtMost op ctx 64

/--
  `llvm.trunc` is legal iff both source and destination widths are ≤ 64.
  Truncation requires no instruction on RV64 (a register reinterpretation suffices).
  Mirrors: `setAction({G_TRUNC, ...}, Legal)`.
-/
def isLegalTrunc (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchTrunc op ctx with
  | none => false
  | some (operand, _) =>
    isIntWidthAtMost operand ctx 64 && resultIsIntWidthAtMost op ctx 64

/--
  `llvm.load` is legal iff the loaded type is `i64`.
  Mirrors: `setAction({G_LOAD, s64}, Legal)`.
-/
def isLegalLoad (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match matchLoad op ctx with
  | none => false
  | some _ => resultIsIntWidth op ctx 64

/-! ## Dispatch -/

/--
  Returns true iff the given LLVM operation is legal for RV64 instruction selection.
  An operation is legal when the RISC-V 64-bit isel pass can lower it directly.
-/
def isLegal (op : OperationPtr) (ctx : IRContext OpCode) : Bool :=
  match op.getOpType! ctx with
  | .llvm .mlir__constant => isLegalConstant op ctx
  | .llvm .add            => isLegalAdd      op ctx
  | .llvm .sub            => isLegalSub      op ctx
  | .llvm .mul            => isLegalMul      op ctx
  | .llvm .sdiv           => isLegalSdiv     op ctx
  | .llvm .udiv           => isLegalUdiv     op ctx
  | .llvm .srem           => isLegalSrem     op ctx
  | .llvm .urem           => isLegalUrem     op ctx
  | .llvm .and            => isLegalAnd      op ctx
  | .llvm .or             => isLegalOr       op ctx
  | .llvm .xor            => isLegalXor      op ctx
  | .llvm .ashr           => isLegalAshr     op ctx
  | .llvm .lshr           => isLegalLshr     op ctx
  | .llvm .shl            => isLegalShl      op ctx
  | .llvm .icmp           => isLegalIcmp     op ctx
  | .llvm .sext           => isLegalSext     op ctx
  | .llvm .zext           => isLegalZext     op ctx
  | .llvm .trunc          => isLegalTrunc    op ctx
  | .llvm .load           => isLegalLoad     op ctx
  | _                     => false

end Veir.RISCV
