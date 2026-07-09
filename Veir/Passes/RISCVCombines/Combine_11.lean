import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir.RISCV

/-! ### APlusC1MinusC2 :  (A + C1) - C2 → A + (C1 - C2)   (C1, C2 constants) -/

set_option warn.sorry false in
def APlusC1MinusC2 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (addVal, c2v, _sp) := matchSub op rewriter.ctx | return rewriter
  let some c2 := matchConstantIntVal c2v rewriter.ctx | return rewriter
  let some dAdd := getDefiningOp addVal rewriter.ctx | return rewriter
  let some (a, c1v, ap) := matchAdd dAdd rewriter.ctx | return rewriter
  let some c1 := matchConstantIntVal c1v rewriter.ctx | return rewriter
  let .integerType aty := (a.getType! rewriter.ctx.raw).val | return rewriter
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c1.value - c2.value) aty))
  let (rewriter, cf) ← rewriter.createOp (.llvm .mlir__constant) #[a.getType! rewriter.ctx.raw] #[]
    #[] #[] folded (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .add) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[a, (cf.getResult 0)]
    #[] #[] ap (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### C2MinusAPlusC1 :  C2 - (A + C1) → (C2 - C1) - A   (C1, C2 constants) -/

set_option warn.sorry false in
def C2MinusAPlusC1 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (c2v, addVal, sp) := matchSub op rewriter.ctx | return rewriter
  let some c2 := matchConstantIntVal c2v rewriter.ctx | return rewriter
  let some dAdd := getDefiningOp addVal rewriter.ctx | return rewriter
  let some (a, c1v, _ap) := matchAdd dAdd rewriter.ctx | return rewriter
  let some c1 := matchConstantIntVal c1v rewriter.ctx | return rewriter
  let .integerType aty := (a.getType! rewriter.ctx.raw).val | return rewriter
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c2.value - c1.value) aty))
  let (rewriter, cf) ← rewriter.createOp (.llvm .mlir__constant) #[a.getType! rewriter.ctx.raw] #[]
    #[] #[] folded (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sub) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(cf.getResult 0), a]
    #[] #[] sp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### AMinusC1MinusC2 :  (A - C1) - C2 → A - (C1 + C2)   (C1, C2 constants) -/

set_option warn.sorry false in
def AMinusC1MinusC2 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (subVal, c2v, sp) := matchSub op rewriter.ctx | return rewriter
  let some c2 := matchConstantIntVal c2v rewriter.ctx | return rewriter
  let some dSub := getDefiningOp subVal rewriter.ctx | return rewriter
  let some (a, c1v, _sp2) := matchSub dSub rewriter.ctx | return rewriter
  let some c1 := matchConstantIntVal c1v rewriter.ctx | return rewriter
  let .integerType aty := (a.getType! rewriter.ctx.raw).val | return rewriter
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c1.value + c2.value) aty))
  let (rewriter, cf) ← rewriter.createOp (.llvm .mlir__constant) #[a.getType! rewriter.ctx.raw] #[]
    #[] #[] folded (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sub) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[a, (cf.getResult 0)]
    #[] #[] sp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### C1MinusAMinusC2 :  (C1 - A) - C2 → (C1 - C2) - A   (C1, C2 constants) -/

set_option warn.sorry false in
def C1MinusAMinusC2 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (subVal, c2v, sp) := matchSub op rewriter.ctx | return rewriter
  let some c2 := matchConstantIntVal c2v rewriter.ctx | return rewriter
  let some dSub := getDefiningOp subVal rewriter.ctx | return rewriter
  let some (c1v, a, _sp2) := matchSub dSub rewriter.ctx | return rewriter
  let some c1 := matchConstantIntVal c1v rewriter.ctx | return rewriter
  let .integerType aty := (a.getType! rewriter.ctx.raw).val | return rewriter
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c1.value - c2.value) aty))
  let (rewriter, cf) ← rewriter.createOp (.llvm .mlir__constant) #[a.getType! rewriter.ctx.raw] #[]
    #[] #[] folded (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .sub) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[(cf.getResult 0), a]
    #[] #[] sp (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### AMinusC1PlusC2 :  (A - C1) + C2 → A + (C2 - C1)   (C1, C2 constants) -/

set_option warn.sorry false in
def AMinusC1PlusC2 (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (subVal, c2v, ap) := matchAdd op rewriter.ctx | return rewriter
  let some c2 := matchConstantIntVal c2v rewriter.ctx | return rewriter
  let some dSub := getDefiningOp subVal rewriter.ctx | return rewriter
  let some (a, c1v, _sp) := matchSub dSub rewriter.ctx | return rewriter
  let some c1 := matchConstantIntVal c1v rewriter.ctx | return rewriter
  let .integerType aty := (a.getType! rewriter.ctx.raw).val | return rewriter
  let folded := LLVMConstantProperties.mk (.integer (IntegerAttr.mk (c2.value - c1.value) aty))
  let (rewriter, cf) ← rewriter.createOp (.llvm .mlir__constant) #[a.getType! rewriter.ctx.raw] #[]
    #[] #[] folded (some $ .before op) sorry sorry sorry sorry
  let (rewriter, newOp) ← rewriter.createOp (.llvm .add) #[(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw] #[a, (cf.getResult 0)]
    #[] #[] ap (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ### or_and_xor_to_xor_or :  (X & Y) | ~Y  →  X | ~Y -/
set_option warn.sorry false in
def or_and_xor_to_xor_or (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (andV, notV, oprops) := matchOr op rewriter.ctx | return rewriter
  let some dAnd := getDefiningOp andV rewriter.ctx | return rewriter
  let some (x, y, _aprops) := matchAnd dAnd rewriter.ctx | return rewriter
  let some dNot := getDefiningOp notV rewriter.ctx | return rewriter
  let some (y1, m1v, _xprops) := matchXor dNot rewriter.ctx | return rewriter
  if y1 != y then return rewriter
  let some cst := matchConstantIntVal m1v rewriter.ctx | return rewriter
  if cst.value ≠ -1 then return rewriter
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .or) #[andV.getType! rewriter.ctx.raw] #[x, notV]
    #[] #[] oprops (some $ .before op)
  return rewriter.replaceOp! op newOp

/-! ### and_xor_or_to_xor_and :  (X | Y) & ~Y  →  X & ~Y -/
set_option warn.sorry false in
def and_xor_or_to_xor_and (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (orV, notV, _aprops) := matchAnd op rewriter.ctx | return rewriter
  let some dOr := getDefiningOp orV rewriter.ctx | return rewriter
  let some (x, y, _oprops) := matchOr dOr rewriter.ctx | return rewriter
  let some dNot := getDefiningOp notV rewriter.ctx | return rewriter
  let some (y1, m1v, _xprops) := matchXor dNot rewriter.ctx | return rewriter
  if y1 != y then return rewriter
  let some cst := matchConstantIntVal m1v rewriter.ctx | return rewriter
  if cst.value ≠ -1 then return rewriter
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .and) #[orV.getType! rewriter.ctx.raw] #[x, notV]
    #[] #[] () (some $ .before op)
  return rewriter.replaceOp! op newOp

/-! ### combine_or_of_and :  or (and x, y), x  →  x -/

-- or (and x, y), x  →  x   (the `and` is the left OR operand)
set_option warn.sorry false in
def combine_or_of_and_l (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (andV, x, _oprops) := matchOr op rewriter.ctx | return rewriter
  let some dAnd := getDefiningOp andV rewriter.ctx | return rewriter
  let some (a0, a1, _aprops) := matchAnd dAnd rewriter.ctx | return rewriter
  if a0 != x && a1 != x then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) x sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

-- or x, (and x, y)  →  x   (the `and` is the right OR operand)
set_option warn.sorry false in
def combine_or_of_and_r (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (x, andV, _oprops) := matchOr op rewriter.ctx | return rewriter
  let some dAnd := getDefiningOp andV rewriter.ctx | return rewriter
  let some (a0, a1, _aprops) := matchAnd dAnd rewriter.ctx | return rewriter
  if a0 != x && a1 != x then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) x sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-! ### AMinusBMinusC :  A - (B - C)  →  A + (C - B) -/
set_option warn.sorry false in
def AMinusBMinusC (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (A, sub1, sprops) := matchSub op rewriter.ctx | return rewriter
  let some dSub := getDefiningOp sub1 rewriter.ctx | return rewriter
  let some (B, C, _sprops1) := matchSub dSub rewriter.ctx | return rewriter
  let (rewriter, cMinusB) ← rewriter.createOp! (.llvm .sub) #[sub1.getType! rewriter.ctx.raw] #[C, B]
    #[] #[] sprops (some $ .before op)
  let (rewriter, newOp) ← rewriter.createOp! (.llvm .add) #[A.getType! rewriter.ctx.raw] #[A, (cMinusB.getResult 0)]
    #[] #[] sprops (some $ .before op)
  return rewriter.replaceOp! op newOp

/-! ### binop_left_to_zero :  (0 op x)  →  0   for op ∈ {shl, lshr, ashr, mul} -/

set_option warn.sorry false in
def shl_left_to_zero (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (zero, _rhs, _props) := matchShl op rewriter.ctx | return rewriter
  let some cst := matchConstantIntVal zero rewriter.ctx | return rewriter
  if cst.value ≠ 0 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) zero sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
def lshr_left_to_zero (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (zero, _rhs, _props) := matchLshr op rewriter.ctx | return rewriter
  let some cst := matchConstantIntVal zero rewriter.ctx | return rewriter
  if cst.value ≠ 0 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) zero sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
def ashr_left_to_zero (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (zero, _rhs, _props) := matchAshr op rewriter.ctx | return rewriter
  let some cst := matchConstantIntVal zero rewriter.ctx | return rewriter
  if cst.value ≠ 0 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) zero sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
def mul_left_to_zero (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (zero, _rhs, _props) := matchMul op rewriter.ctx | return rewriter
  let some cst := matchConstantIntVal zero rewriter.ctx | return rewriter
  if cst.value ≠ 0 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) zero sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry
