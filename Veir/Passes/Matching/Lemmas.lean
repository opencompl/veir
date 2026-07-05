import Veir.Passes.Matching.Basic

/-! This file contains lemmas that characterize the behavior of the matching functions. -/

namespace Veir

/-- What the generic `matchOp` helper syntactically guarantees. -/
@[grind →]
theorem matchOp_implies {op : OperationPtr} {ctx : IRContext OpCode}
    {opType numOperands operands props} :
    matchOp op ctx opType numOperands = some (operands, props) →
    op.getOpType! ctx = opType ∧
    op.getNumOperands! ctx = numOperands ∧
    op.getNumResults! ctx = 1 ∧
    operands = op.getOperands! ctx ∧
    props = op.getProperties! ctx opType := by
  intro hmatch
  simp only [matchOp, bind, pure, Option.bind, guard, failure] at hmatch
  grind

/-- What matching `llvm.add` (via `matchAddi`) syntactically guarantees. -/
theorem matchAddi_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchAddi op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .add ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .add) := by
  intro hmatch
  simp only [matchAddi, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.add` (via `matchAdd`) syntactically guarantees. -/
theorem matchAdd_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchAdd op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .add ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .add) := by
  intro hmatch
  simp only [matchAdd, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.sub` (via `matchSubi`) syntactically guarantees. -/
theorem matchSubi_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchSubi op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .sub ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .sub) := by
  intro hmatch
  simp only [matchSubi, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.mul` (via `matchMuli`) syntactically guarantees. -/
theorem matchMuli_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchMuli op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .mul ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .mul) := by
  intro hmatch
  simp only [matchMuli, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.and` (via `matchAndi`) syntactically guarantees. -/
theorem matchAndi_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs} :
    matchAndi op ctx = some (lhs, rhs) →
    op.getOpType! ctx = .llvm .and ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] := by
  intro hmatch
  simp only [matchAndi, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.and` (via `matchAnd`) syntactically guarantees. -/
theorem matchAnd_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchAnd op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .and ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .and) := by
  intro hmatch
  simp only [matchAnd, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.or` (via `matchOri`) syntactically guarantees. -/
theorem matchOri_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchOri op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .or ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .or) := by
  intro hmatch
  simp only [matchOri, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.xor` (via `matchXori`) syntactically guarantees. -/
theorem matchXori_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs} :
    matchXori op ctx = some (lhs, rhs) →
    op.getOpType! ctx = .llvm .xor ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] := by
  intro hmatch
  simp only [matchXori, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.mlir.constant` (via `matchConstantIntOp`) syntactically guarantees. -/
theorem matchConstantIntOp_implies {op : OperationPtr} {ctx : IRContext OpCode} {intAttr} :
    matchConstantIntOp op ctx = some intAttr →
    op.getOpType! ctx = .llvm .mlir__constant ∧
    (op.getProperties! ctx (.llvm .mlir__constant)).value = .integer intAttr := by
  intro hmatch
  simp only [matchConstantIntOp, pure] at hmatch
  grind

/-- What matching a constant integer value (via `matchConstantIntVal`) syntactically guarantees. -/
theorem matchConstantIntVal_implies {val : ValuePtr} {ctx : IRContext OpCode} {intAttr} :
    matchConstantIntVal val ctx = some intAttr →
    ∃ opResultPtr, val = .opResult opResultPtr ∧
      matchConstantIntOp opResultPtr.op ctx = some intAttr := by
  intro hmatch
  simp only [matchConstantIntVal] at hmatch
  grind

/-- What matching a zero constant (via `matchConstantZero`) syntactically guarantees. -/
theorem matchConstantZero_implies {val : ValuePtr} {ctx : IRContext OpCode} {result} :
    matchConstantZero val ctx = some result →
    result = val ∧ ∃ attr, matchConstantIntVal val ctx = some attr ∧ attr.value = 0 := by
  intro hmatch
  simp only [matchConstantZero, bind, pure, Option.bind, guard, failure] at hmatch
  grind

/-- What `getDefiningOp` syntactically guarantees. -/
theorem getDefiningOp_implies {val : ValuePtr} {ctx : IRContext OpCode} {op} :
    getDefiningOp val ctx = some op →
    ∃ opResultPtr, val = .opResult opResultPtr ∧ op = opResultPtr.op := by
  intro hmatch
  simp only [getDefiningOp] at hmatch
  grind

/-- What matching `builtin.unrealized_conversion_cast` (via `matchCastOp`) syntactically guarantees. -/
theorem matchCastOp_implies {op : OperationPtr} {ctx : IRContext OpCode} {operand} :
    matchCastOp op ctx = some operand →
    op.getOpType! ctx = .builtin .unrealized_conversion_cast ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[operand] := by
  intro hmatch
  simp only [matchCastOp, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.ashr` (via `matchAshr`) syntactically guarantees. -/
theorem matchAshr_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchAshr op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .ashr ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .ashr) := by
  intro hmatch
  simp only [matchAshr, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.icmp` (via `matchIcmp`) syntactically guarantees. -/
theorem matchIcmp_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchIcmp op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .icmp ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .icmp) := by
  intro hmatch
  simp only [matchIcmp, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.or` (via `matchOr`) syntactically guarantees. -/
theorem matchOr_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchOr op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .or ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .or) := by
  intro hmatch
  simp only [matchOr, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.select` (via `matchSelect`) syntactically guarantees. -/
theorem matchSelect_implies {op : OperationPtr} {ctx : IRContext OpCode} {cond tval fval} :
    matchSelect op ctx = some (cond, tval, fval) →
    op.getOpType! ctx = .llvm .select ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[cond, tval, fval] := by
  intro hmatch
  simp only [matchSelect, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.xor` (via `matchXor`) syntactically guarantees. -/
theorem matchXor_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchXor op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .xor ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .xor) := by
  intro hmatch
  simp only [matchXor, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.intr.smax` (via `matchSmax`) syntactically guarantees. -/
theorem matchSmax_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs} :
    matchSmax op ctx = some (lhs, rhs) →
    op.getOpType! ctx = .llvm .intr__smax ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] := by
  intro hmatch
  simp only [matchSmax, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.intr.smin` (via `matchSmin`) syntactically guarantees. -/
theorem matchSmin_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs} :
    matchSmin op ctx = some (lhs, rhs) →
    op.getOpType! ctx = .llvm .intr__smin ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] := by
  intro hmatch
  simp only [matchSmin, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.intr.umax` (via `matchUmax`) syntactically guarantees. -/
theorem matchUmax_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs} :
    matchUmax op ctx = some (lhs, rhs) →
    op.getOpType! ctx = .llvm .intr__umax ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] := by
  intro hmatch
  simp only [matchUmax, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.intr.umin` (via `matchUmin`) syntactically guarantees. -/
theorem matchUmin_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs} :
    matchUmin op ctx = some (lhs, rhs) →
    op.getOpType! ctx = .llvm .intr__umin ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] := by
  intro hmatch
  simp only [matchUmin, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.intr.fshl` (via `matchFshl`) syntactically guarantees. -/
theorem matchFshl_implies {op : OperationPtr} {ctx : IRContext OpCode} {a b amt} :
    matchFshl op ctx = some (a, b, amt) →
    op.getOpType! ctx = .llvm .intr__fshl ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[a, b, amt] := by
  intro hmatch
  simp only [matchFshl, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.intr.fshr` (via `matchFshr`) syntactically guarantees. -/
theorem matchFshr_implies {op : OperationPtr} {ctx : IRContext OpCode} {a b amt} :
    matchFshr op ctx = some (a, b, amt) →
    op.getOpType! ctx = .llvm .intr__fshr ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[a, b, amt] := by
  intro hmatch
  simp only [matchFshr, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `xor X, -1` (the canonical "not X", via `matchNot`) syntactically guarantees. -/
theorem matchNot_implies {val : ValuePtr} {ctx : IRContext OpCode} {lhs} :
    matchNot val ctx = some lhs →
    ∃ opResultPtr rhs cst,
      val = .opResult opResultPtr ∧
      matchXori opResultPtr.op ctx = some (lhs, rhs) ∧
      matchConstantIntVal rhs ctx = some cst ∧
      cst.value = -1 := by
  intro hmatch
  simp only [matchNot, bind, pure, Option.bind, guard, failure] at hmatch
  grind

/-- What matching `llvm.mul` (via `matchMul`) syntactically guarantees. -/
theorem matchMul_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchMul op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .mul ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .mul) := by
  intro hmatch
  simp only [matchMul, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.sdiv` (via `matchSdiv`) syntactically guarantees. -/
theorem matchSdiv_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchSdiv op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .sdiv ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .sdiv) := by
  intro hmatch
  simp only [matchSdiv, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.udiv` (via `matchUdiv`) syntactically guarantees. -/
theorem matchUdiv_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchUdiv op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .udiv ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .udiv) := by
  intro hmatch
  simp only [matchUdiv, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.srem` (via `matchSrem`) syntactically guarantees. -/
theorem matchSrem_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchSrem op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .srem ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .srem) := by
  intro hmatch
  simp only [matchSrem, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.urem` (via `matchUrem`) syntactically guarantees. -/
theorem matchUrem_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchUrem op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .urem ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .urem) := by
  intro hmatch
  simp only [matchUrem, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.sext` (via `matchSext`) syntactically guarantees. -/
theorem matchSext_implies {op : OperationPtr} {ctx : IRContext OpCode} {operand props} :
    matchSext op ctx = some (operand, props) →
    op.getOpType! ctx = .llvm .sext ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[operand] ∧
    props = op.getProperties! ctx (.llvm .sext) := by
  intro hmatch
  simp only [matchSext, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.trunc` (via `matchTrunc`) syntactically guarantees. -/
theorem matchTrunc_implies {op : OperationPtr} {ctx : IRContext OpCode} {operand props} :
    matchTrunc op ctx = some (operand, props) →
    op.getOpType! ctx = .llvm .trunc ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[operand] ∧
    props = op.getProperties! ctx (.llvm .trunc) := by
  intro hmatch
  simp only [matchTrunc, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.zext` (via `matchZext`) syntactically guarantees. -/
theorem matchZext_implies {op : OperationPtr} {ctx : IRContext OpCode} {operand props} :
    matchZext op ctx = some (operand, props) →
    op.getOpType! ctx = .llvm .zext ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[operand] ∧
    props = op.getProperties! ctx (.llvm .zext) := by
  intro hmatch
  simp only [matchZext, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.shl` (via `matchShl`) syntactically guarantees. -/
theorem matchShl_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchShl op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .shl ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .shl) := by
  intro hmatch
  simp only [matchShl, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.lshr` (via `matchLshr`) syntactically guarantees. -/
theorem matchLshr_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchLshr op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .lshr ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .lshr) := by
  intro hmatch
  simp only [matchLshr, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.sub` (via `matchSub`) syntactically guarantees. -/
theorem matchSub_implies {op : OperationPtr} {ctx : IRContext OpCode} {lhs rhs props} :
    matchSub op ctx = some (lhs, rhs, props) →
    op.getOpType! ctx = .llvm .sub ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[lhs, rhs] ∧
    props = op.getProperties! ctx (.llvm .sub) := by
  intro hmatch
  simp only [matchSub, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.load` (via `matchLoad`) syntactically guarantees. -/
theorem matchLoad_implies {op : OperationPtr} {ctx : IRContext OpCode} {operand props} :
    matchLoad op ctx = some (operand, props) →
    op.getOpType! ctx = .llvm .load ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[operand] ∧
    props = op.getProperties! ctx (.llvm .load) := by
  intro hmatch
  simp only [matchLoad, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.intr.ctlz` syntactically guarantees. -/
theorem matchCtlz_implies {op : OperationPtr} {ctx : IRContext OpCode} {operand props} :
    matchCtlz op ctx = some (operand, props) →
    op.getOpType! ctx = .llvm .intr__ctlz ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[operand] ∧
    props = op.getProperties! ctx (.llvm .intr__ctlz) := by
  intro hmatch
  simp only [matchCtlz, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.intr.cttz` (via `matchCttz`) syntactically guarantees. -/
theorem matchCttz_implies {op : OperationPtr} {ctx : IRContext OpCode} {operand props} :
    matchCttz op ctx = some (operand, props) →
    op.getOpType! ctx = .llvm .intr__cttz ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[operand] ∧
    props = op.getProperties! ctx (.llvm .intr__cttz) := by
  intro hmatch
  simp only [matchCttz, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.intr.ctpop` (via `matchCtpop`) syntactically guarantees. -/
theorem matchCtpop_implies {op : OperationPtr} {ctx : IRContext OpCode} {operand} :
    matchCtpop op ctx = some operand →
    op.getOpType! ctx = .llvm .intr__ctpop ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[operand] := by
  intro hmatch
  simp only [matchCtpop, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.intr.bswap` (via `matchBswap`) syntactically guarantees. -/
theorem matchBswap_implies {op : OperationPtr} {ctx : IRContext OpCode} {operand} :
    matchBswap op ctx = some operand →
    op.getOpType! ctx = .llvm .intr__bswap ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[operand] := by
  intro hmatch
  simp only [matchBswap, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.intr.bitreverse` (via `matchBitreverse`) syntactically guarantees. -/
theorem matchBitreverse_implies {op : OperationPtr} {ctx : IRContext OpCode} {operand} :
    matchBitreverse op ctx = some operand →
    op.getOpType! ctx = .llvm .intr__bitreverse ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[operand] := by
  intro hmatch
  simp only [matchBitreverse, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.getelementptr` (via `matchGetelementptr`) syntactically guarantees. -/
theorem matchGetelementptr_implies {op : OperationPtr} {ctx : IRContext OpCode} {base idx props} :
    matchGetelementptr op ctx = some (base, idx, props) →
    op.getOpType! ctx = .llvm .getelementptr ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[base, idx] ∧
    props = op.getProperties! ctx (.llvm .getelementptr) := by
  intro hmatch
  simp only [matchGetelementptr, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.mlir.poison` (via `matchPoison`) syntactically guarantees. -/
theorem matchPoison_implies {op : OperationPtr} {ctx : IRContext OpCode} :
    matchPoison op ctx = some () →
    op.getOpType! ctx = .llvm .mlir__poison ∧
    op.getNumOperands! ctx = 0 ∧
    op.getNumResults! ctx = 1 := by
  intro hmatch
  simp only [matchPoison, bind, Option.bind, pure] at hmatch
  grind

/-- What matching `llvm.store` (via `matchStore`) syntactically guarantees. -/
theorem matchStore_implies {op : OperationPtr} {ctx : IRContext OpCode} {value ptr props} :
    matchStore op ctx = some (value, ptr, props) →
    op.getOpType! ctx = .llvm .store ∧
    op.getOperands! ctx = #[value, ptr] ∧
    props = op.getProperties! ctx (.llvm .store) := by
  intro hmatch
  simp only [matchStore, bind, pure, Option.bind, guard, failure] at hmatch
  grind

/-- What matching `llvm.freeze` (via `matchFreeze`) syntactically guarantees. -/
theorem matchFreeze_implies {op : OperationPtr} {ctx : IRContext OpCode} {operand} :
    matchFreeze op ctx = some operand →
    op.getOpType! ctx = .llvm .freeze ∧
    op.getNumResults! ctx = 1 ∧
    op.getOperands! ctx = #[operand] := by
  intro hmatch
  simp only [matchFreeze, bind, Option.bind, pure] at hmatch
  grind
