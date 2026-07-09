import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir.RISCV

/--
  If `v` is a `ValuePtr` defined by an integer constant whose value is a positive
  power of two, return its base-2 logarithm `k` (so that `v = 2^k`). Otherwise
  `none`. Total: `k` is computed by a bounded recursion counting trailing zeros. -/
def isConstantPowerOfTwo (v : ValuePtr) (ctx : IRContext OpCode) : Option Nat := do
  let attr ← matchConstantIntVal v ctx
  guard (attr.value > 0)
  let n : Nat := attr.value.toNat
  guard (n &&& (n - 1) = 0)
  -- `n` is a power of two; count trailing zeros to recover `k`.
  let rec log2Aux (m : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => 0
    | fuel + 1 => if m ≤ 1 then 0 else 1 + log2Aux (m / 2) fuel
  return log2Aux n n

set_option warn.sorry false in

/-! ### lshr_of_trunc_of_lshr :  (lshr (trunc (lshr x, C1)), C2) → trunc (lshr x, (C1 + C2))

  C1, C2 constants. The two logical right shifts compose at x's full width, then a
  single trunc narrows to the result type. -/

set_option warn.sorry false in
def lshr_of_trunc_of_lshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (truncV, c2v, _) := matchLshr op rewriter.ctx | return rewriter
  let some c2 := matchConstantIntVal c2v rewriter.ctx | return rewriter
  let some dTrunc := getDefiningOp truncV rewriter.ctx | return rewriter
  let some (innerLshrV, _) := matchTrunc dTrunc rewriter.ctx | return rewriter
  let some dInner := getDefiningOp innerLshrV rewriter.ctx | return rewriter
  let some (x, c1v, ip) := matchLshr dInner rewriter.ctx | return rewriter
  let some c1 := matchConstantIntVal c1v rewriter.ctx | return rewriter
  let .integerType xty := (x.getType! rewriter.ctx.raw).val | return rewriter
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c1.value + c2.value) xty))
  let (rewriter, cf) ← rewriter.createOp (.llvm .mlir__constant) #[x.getType! rewriter.ctx.raw] #[]
    #[] #[] folded (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newLshr) ← rewriter.createOp (.llvm .lshr) #[x.getType! rewriter.ctx.raw] #[x, (cf.getResult 0)]
    #[] #[] ip (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .trunc) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(newLshr.getResult 0)]
    #[] #[] (NswNuwProperties.mk false false) (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### funnel_shift_{right,left}_zero :  fshr x, y, 0 → y ,  fshl x, y, 0 → x -/

set_option warn.sorry false in
def funnel_shift_right_zero (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (_x, y, amt) := matchFshr op rewriter.ctx | return rewriter
  let some c := matchConstantIntVal amt rewriter.ctx | return rewriter
  if c.value ≠ 0 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) y sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
def funnel_shift_left_zero (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (x, _y, amt) := matchFshl op rewriter.ctx | return rewriter
  let some c := matchConstantIntVal amt rewriter.ctx | return rewriter
  if c.value ≠ 0 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) x sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-! ### canonicalize_icmp :  (icmp pred C, x) → (icmp swappedPred x, C)

  Moves a constant left operand of an icmp to the right, flipping the predicate to
  its swapped form. Mirrors LLVM's `matchCanonicalizeICmp`: fires only when the LHS
  is a constant and the RHS is not (so it does not oscillate). -/

set_option warn.sorry false in
def canonicalize_icmp (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, ip) := matchIcmp op rewriter.ctx | return rewriter
  let some _ := matchConstantIntVal lhs rewriter.ctx | return rewriter
  if (matchConstantIntVal rhs rewriter.ctx).isSome then return rewriter
  let swapped : Data.LLVM.IntPred := match ip.predicate with
    | .slt => .sgt | .sgt => .slt | .sle => .sge | .sge => .sle
    | .ult => .ugt | .ugt => .ult | .ule => .uge | .uge => .ule
    | p => p
  let (rewriter, newOp) ← rewriter.createOp (.llvm .icmp) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[rhs, lhs]
    #[] #[] (IcmpProperties.mk swapped) (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### bitreverse_shl / bitreverse_lshr

  `bitreverse(shl(bitreverse x), y) → lshr x, y` and the mirror
  `bitreverse(lshr(bitreverse x), y) → shl x, y`. Reversing, shifting one way,
  and reversing again is equivalent to a single shift the other way. -/

set_option warn.sorry false in
def bitreverse_shl (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some rev := matchBitreverse op rewriter.ctx | return rewriter
  let some dShl := getDefiningOp rev rewriter.ctx | return rewriter
  let some (inner, y, _) := matchShl dShl rewriter.ctx | return rewriter
  let some dInner := getDefiningOp inner rewriter.ctx | return rewriter
  let some x := matchBitreverse dInner rewriter.ctx | return rewriter
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .lshr) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, y]
    #[] #[] (ExactProperties.mk false) (some $ .before op)
  return rewriter.replaceOp! op newOp

set_option warn.sorry false in
def bitreverse_lshr (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some rev := matchBitreverse op rewriter.ctx | return rewriter
  let some dLshr := getDefiningOp rev rewriter.ctx | return rewriter
  let some (inner, y, _) := matchLshr dLshr rewriter.ctx | return rewriter
  let some dInner := getDefiningOp inner rewriter.ctx | return rewriter
  let some x := matchBitreverse dInner rewriter.ctx | return rewriter
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .shl) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, y]
    #[] #[] (NswNuwProperties.mk false false) (some $ .before op)
  return rewriter.replaceOp! op newOp

/-! ### udiv_by_pow2 / mul_to_shl / urem_pow2_to_mask

  Strength reductions against a power-of-two constant:
    `udiv x, 2^k → lshr x, k`,  `mul x, 2^k → shl x, k`,
    `urem x, 2^k → and x, (2^k − 1)`. -/

set_option warn.sorry false in
def udiv_by_pow2 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (x, yv, _) := matchUdiv op rewriter.ctx | return rewriter
  let some k := isConstantPowerOfTwo yv rewriter.ctx | return rewriter
  let .integerType xty := (x.getType! rewriter.ctx.raw).val | return rewriter
  let kConst := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (k : Int) xty))
  let (rewriter, ck) ← rewriter.createOp! (.llvm .mlir__constant) #[x.getType! rewriter.ctx.raw] #[]
    #[] #[] kConst (some $ .before op)
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .lshr) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, (ck.getResult 0)]
    #[] #[] (ExactProperties.mk false) (some $ .before op)
  return rewriter.replaceOp! op newOp

set_option warn.sorry false in
def mul_to_shl (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (x, yv, mp) := matchMul op rewriter.ctx | return rewriter
  let some k := isConstantPowerOfTwo yv rewriter.ctx | return rewriter
  let .integerType xty := (x.getType! rewriter.ctx.raw).val | return rewriter
  let kConst := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (k : Int) xty))
  let (rewriter, ck) ← rewriter.createOp! (.llvm .mlir__constant) #[x.getType! rewriter.ctx.raw] #[]
    #[] #[] kConst (some $ .before op)
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .shl) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, (ck.getResult 0)]
    #[] #[] mp (some $ .before op)
  return rewriter.replaceOp! op newOp

set_option warn.sorry false in
def urem_pow2_to_mask (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (x, yv, _) := matchUrem op rewriter.ctx | return rewriter
  let some k := isConstantPowerOfTwo yv rewriter.ctx | return rewriter
  let .integerType xty := (x.getType! rewriter.ctx.raw).val | return rewriter
  let mask : Int := (2 ^ k : Int) - 1
  let maskConst := LLVMConstantProperties.mk (.integer (IntegerAttr.mk mask xty))
  let (rewriter, cm) ← rewriter.createOp! (.llvm .mlir__constant) #[x.getType! rewriter.ctx.raw] #[]
    #[] #[] maskConst (some $ .before op)
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .and) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, (cm.getResult 0)]
    #[] #[] () (some $ .before op)
  return rewriter.replaceOp! op newOp

/-! ### funnel_shift_overshift :  fshl/fshr x, y, C → fshl/fshr x, y, (C % bw)   (C ≥ bw)

  A funnel shift amount is taken modulo the bit-width, so an over-large constant
  amount is reduced to its residue. -/

set_option warn.sorry false in
def funnel_shift_overshift_l (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (x, y, amt) := matchFshl op rewriter.ctx | return rewriter
  let some c := matchConstantIntVal amt rewriter.ctx | return rewriter
  let .integerType aty := (amt.getType! rewriter.ctx.raw).val | return rewriter
  let bw : Int := (aty.bitwidth : Int)
  if c.value < bw then return rewriter
  let newAmt := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c.value % bw) aty))
  let (rewriter, cn) ← rewriter.createOp! (.llvm .mlir__constant) #[amt.getType! rewriter.ctx.raw] #[]
    #[] #[] newAmt (some $ .before op)
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .intr__fshl) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, y, (cn.getResult 0)]
    #[] #[] () (some $ .before op)
  return rewriter.replaceOp! op newOp

set_option warn.sorry false in
def funnel_shift_overshift_r (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (x, y, amt) := matchFshr op rewriter.ctx | return rewriter
  let some c := matchConstantIntVal amt rewriter.ctx | return rewriter
  let .integerType aty := (amt.getType! rewriter.ctx.raw).val | return rewriter
  let bw : Int := (aty.bitwidth : Int)
  if c.value < bw then return rewriter
  let newAmt := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c.value % bw) aty))
  let (rewriter, cn) ← rewriter.createOp! (.llvm .mlir__constant) #[amt.getType! rewriter.ctx.raw] #[]
    #[] #[] newAmt (some $ .before op)
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .intr__fshr) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[x, y, (cn.getResult 0)]
    #[] #[] () (some $ .before op)
  return rewriter.replaceOp! op newOp

/-! ### funnel_shift_or_shift_to_funnel_shift_{left,right}

  `(fshl x, z, y) | (shl x, y) → fshl x, z, y` and the mirror
  `(fshr z, x, y) | (lshr x, y) → fshr z, x, y`. The plain shift is subsumed by
  the funnel shift that already produces the wanted bits, so the OR collapses to
  the existing funnel-shift value. G_OR is commutative: both operand orders are
  handled. -/

set_option warn.sorry false in
def funnel_shift_or_shift_to_funnel_shift_left (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (o0, o1, _) := matchOr op rewriter.ctx | return rewriter
  -- Try (fshl = o0, shl = o1) then (fshl = o1, shl = o0).
  let tryOrder (fshlV shlV : ValuePtr) : Option ValuePtr := do
    let some dFshl := getDefiningOp fshlV rewriter.ctx | none
    let some (fx, _fz, fy) := matchFshl dFshl rewriter.ctx | none
    let some dShl := getDefiningOp shlV rewriter.ctx | none
    let some (sx, sy, _) := matchShl dShl rewriter.ctx | none
    guard (fx = sx ∧ fy = sy)
    some fshlV
  let some keep := (tryOrder o0 o1).orElse (fun _ => tryOrder o1 o0) | return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) keep sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
def funnel_shift_or_shift_to_funnel_shift_right (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (o0, o1, _) := matchOr op rewriter.ctx | return rewriter
  -- Try (fshr = o0, lshr = o1) then (fshr = o1, lshr = o0).
  let tryOrder (fshrV lshrV : ValuePtr) : Option ValuePtr := do
    let some dFshr := getDefiningOp fshrV rewriter.ctx | none
    let some (_fz, fx, fy) := matchFshr dFshr rewriter.ctx | none
    let some dLshr := getDefiningOp lshrV rewriter.ctx | none
    let some (sx, sy, _) := matchLshr dLshr rewriter.ctx | none
    guard (fx = sx ∧ fy = sy)
    some fshrV
  let some keep := (tryOrder o0 o1).orElse (fun _ => tryOrder o1 o0) | return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) keep sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-! ### constant_fold_binop :  binop(C1, C2) → C

  Both operands constant: evaluate the binop at compile time and materialize the
  single result constant. Division/remainder by zero is left un-folded. -/

set_option warn.sorry false in
def constant_fold_binop (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let opType := op.getOpType! rewriter.ctx.raw
  let operands := op.getOperands! rewriter.ctx.raw
  if operands.size ≠ 2 then return rewriter
  let some c1 := matchConstantIntVal operands[0]! rewriter.ctx | return rewriter
  let some c2 := matchConstantIntVal operands[1]! rewriter.ctx | return rewriter
  let a := c1.value
  let b := c2.value
  -- Only opcodes whose result is well-defined over unbounded `Int` (no fixed-width
  -- wrapping / signedness ambiguity) are folded. The bitwise ops (`and/or/xor`),
  -- the shifts, and the div/rem family need width-dependent semantics and are
  -- deliberately omitted here.
  let folded : Option Int := match opType with
    | .llvm .add => some (a + b)
    | .llvm .sub => some (a - b)
    | .llvm .mul => some (a * b)
    | .llvm .intr__smin => some (min a b)
    | .llvm .intr__smax => some (max a b)
    | _ => none
  let some result := folded | return rewriter
  let .integerType rty := ((op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw).val | return rewriter
  let foldedProps := LLVMConstantProperties.mk (.integer (IntegerAttr.mk result rty))
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .mlir__constant) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[]
    #[] #[] foldedProps (some $ .before op)
  return rewriter.replaceOp! op newOp
