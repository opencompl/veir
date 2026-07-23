module

public import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Properties

namespace Veir

/-!
  # ArithToLLVM pass

  Lowers every operation of the `arith` dialect into the `llvm` dialect, leaving no
  `arith` operation behind. This mirrors MLIR's `ArithToLLVM` conversion
  (`mlir/lib/Conversion/ArithToLLVM/ArithToLLVM.cpp`).

  Unlike MLIR, Veir has no `index` type and no separate LLVM integer type: both
  dialects operate on the same signless `IntegerType`. The type conversion is
  therefore the identity, and — unlike `ModArithToArith` — this pass needs no
  `unrealized_conversion_cast` plumbing at all. Result and operand types are
  carried over verbatim.

  Each lowering is a direct transcription of the corresponding `arith` interpreter
  case in `Veir/Interpreter/Basic.lean`, which defines the `arith` semantics in
  terms of the same `LLVM.Int.*` primitives the target `llvm` ops evaluate to. The
  three ops with no single LLVM target (`ceildiv*`, `floordivsi`) and the
  two-result "extended" ops are expanded exactly as those interpreter cases (and
  MLIR's `ExpandOps` / `MulIExtendedOpLowering`) prescribe.
-/

/-! ## Emission helpers -/

/-- Emit `llvm.mlir.constant value : i<width>`. -/
def emitLLVMIntConst (rewriter : PatternRewriter OpCode) (value : Int) (width : Nat)
    (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  let ty : IntegerType := IntegerType.mk width
  let props : LLVMConstantProperties := { value := .integer (IntegerAttr.mk value ty) }
  let (rewriter, op) ← rewriter.createOp! (.llvm .mlir__constant)
    #[(ty : TypeAttr)] #[] #[] #[] props (some ip)
  return (rewriter, (op.getResult 0 : ValuePtr))

/-- Emit a binary `llvm` op `lOp` with result type `resTy` on `a` and `b`. -/
def emitLLVMBin (rewriter : PatternRewriter OpCode) (lOp : Llvm)
    (props : propertiesOf (.llvm lOp)) (resTy : TypeAttr) (a b : ValuePtr)
    (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  let (rewriter, op) ← rewriter.createOp! (.llvm lOp) #[resTy] #[a, b] #[] #[] props (some ip)
  return (rewriter, (op.getResult 0 : ValuePtr))

/-- Emit a unary `llvm` op `lOp` (e.g. `sext`/`zext`/`trunc`) with result type `resTy`. -/
def emitLLVMUnary (rewriter : PatternRewriter OpCode) (lOp : Llvm)
    (props : propertiesOf (.llvm lOp)) (resTy : TypeAttr) (a : ValuePtr)
    (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  let (rewriter, op) ← rewriter.createOp! (.llvm lOp) #[resTy] #[a] #[] #[] props (some ip)
  return (rewriter, (op.getResult 0 : ValuePtr))

/-- Emit `llvm.select cond, t, f : resTy`. -/
def emitLLVMSelect (rewriter : PatternRewriter OpCode) (resTy : TypeAttr)
    (cond t f : ValuePtr) (ip : InsertPoint) :
    Option (PatternRewriter OpCode × ValuePtr) := do
  let (rewriter, op) ← rewriter.createOp! (.llvm .select) #[resTy] #[cond, t, f] #[] #[] ()
    (some ip)
  return (rewriter, (op.getResult 0 : ValuePtr))

/-- The integer bitwidth of value `v`, if it has an integer type. -/
def intBitwidth (rewriter : PatternRewriter OpCode) (v : ValuePtr) : Option Nat := do
  let .integerType intTy := (v.getType! rewriter.ctx.raw).val | none
  return intTy.bitwidth

/-! ## Generic 1:1 lowering -/

/--
  Lower a single-result `arith` op `aOp` (with `numOperands` operands) to the
  `llvm` op `lOp`, carrying over operands and result type unchanged and mapping
  the properties with `convert`.
-/
def lower1to1 (aOp : Arith) (lOp : Llvm)
    (convert : propertiesOf (.arith aOp) → propertiesOf (.llvm lOp)) (numOperands : Nat)
    (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operands, props) := matchOp op rewriter.ctx (.arith aOp) numOperands
    | return rewriter
  let ip := InsertPoint.before op
  let (rewriter, newOp) ← rewriter.createOp! (.llvm lOp)
    (op.getResultTypes! rewriter.ctx.raw) operands #[] #[] (convert props) (some ip)
  let rewriter := rewriter.replaceValue! (op.getResult 0 : ValuePtr) (newOp.getResult 0 : ValuePtr)
  return rewriter.eraseOp! op

/-- Translate `arith` integer-overflow flags to the `llvm` `nsw`/`nuw` properties. -/
def flagsToNswNuw (p : ArithIntegerOverflowFlagsProperties) : NswNuwProperties :=
  { nsw := p.attr.nsw, nuw := p.attr.nuw }

/-! ### The 1:1 patterns -/

def lowerConstant := lower1to1 .constant .mlir__constant
  (fun p => { value := .integer p.value }) 0

def lowerAddI := lower1to1 .addi .add flagsToNswNuw 2
def lowerSubI := lower1to1 .subi .sub flagsToNswNuw 2
def lowerMulI := lower1to1 .muli .mul flagsToNswNuw 2
def lowerShlI := lower1to1 .shli .shl flagsToNswNuw 2
def lowerTruncI := lower1to1 .trunci .trunc flagsToNswNuw 1

def lowerDivSI := lower1to1 .divsi .sdiv (fun p => p) 2
def lowerDivUI := lower1to1 .divui .udiv (fun p => p) 2
def lowerShrSI := lower1to1 .shrsi .ashr (fun p => p) 2
def lowerShrUI := lower1to1 .shrui .lshr (fun p => p) 2

def lowerRemSI := lower1to1 .remsi .srem (fun p => p) 2
def lowerRemUI := lower1to1 .remui .urem (fun p => p) 2
def lowerAndI := lower1to1 .andi .and (fun p => p) 2
def lowerXorI := lower1to1 .xori .xor (fun p => p) 2
def lowerOrI := lower1to1 .ori .or (fun p => p) 2

def lowerExtUI := lower1to1 .extui .zext (fun p => p) 1
def lowerExtSI := lower1to1 .extsi .sext (fun p => p) 1
def lowerCmpI := lower1to1 .cmpi .icmp (fun p => p) 2
def lowerSelect := lower1to1 .select .select (fun p => p) 3

def lowerMaxSI := lower1to1 .maxsi .intr__smax (fun p => p) 2
def lowerMinSI := lower1to1 .minsi .intr__smin (fun p => p) 2
def lowerMaxUI := lower1to1 .maxui .intr__umax (fun p => p) 2
def lowerMinUI := lower1to1 .minui .intr__umin (fun p => p) 2

/-! ## Expansions with no single LLVM target -/

/--
  `arith.ceildivui a, b` → `a == 0 ? 0 : ((a - 1) udiv b) + 1`.
  The `udiv` reproduces the divide-by-zero / poison-divisor UB unconditionally,
  matching the `ceildivui` interpreter case.
-/
def lowerCeilDivUI (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operands, _) := matchOp op rewriter.ctx (.arith .ceildivui) 2
    | return rewriter
  let a := operands[0]!
  let b := operands[1]!
  let some width := intBitwidth rewriter a | return rewriter
  let iN : TypeAttr := IntegerType.mk width
  let i1 : TypeAttr := IntegerType.mk 1
  let ip := InsertPoint.before op
  let (rewriter, zero) ← emitLLVMIntConst rewriter 0 width ip
  let (rewriter, one) ← emitLLVMIntConst rewriter 1 width ip
  let (rewriter, isZero) ← emitLLVMBin rewriter .icmp { predicate := .eq } i1 a zero ip
  let (rewriter, am1) ← emitLLVMBin rewriter .sub { nsw := false, nuw := false } iN a one ip
  let (rewriter, q) ← emitLLVMBin rewriter .udiv { exact := false } iN am1 b ip
  let (rewriter, qp1) ← emitLLVMBin rewriter .add { nsw := false, nuw := false } iN q one ip
  let (rewriter, res) ← emitLLVMSelect rewriter iN isZero zero qp1 ip
  let rewriter := rewriter.replaceValue! (op.getResult 0 : ValuePtr) res
  return rewriter.eraseOp! op

/--
  `arith.ceildivsi a, b` → `z = a sdiv b; (a != z*b) && (sign a == sign b) ? z+1 : z`.
  The intermediate `mul`/`add` wrap (no flags). The `sdiv` reproduces the
  divide-by-zero / `INT_MIN / -1` UB, matching the `ceildivsi` interpreter case.
-/
def lowerCeilDivSI (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operands, _) := matchOp op rewriter.ctx (.arith .ceildivsi) 2
    | return rewriter
  let a := operands[0]!
  let b := operands[1]!
  let some width := intBitwidth rewriter a | return rewriter
  let iN : TypeAttr := IntegerType.mk width
  let i1 : TypeAttr := IntegerType.mk 1
  let ip := InsertPoint.before op
  let (rewriter, zero) ← emitLLVMIntConst rewriter 0 width ip
  let (rewriter, one) ← emitLLVMIntConst rewriter 1 width ip
  let (rewriter, z) ← emitLLVMBin rewriter .sdiv { exact := false } iN a b ip
  let (rewriter, zb) ← emitLLVMBin rewriter .mul { nsw := false, nuw := false } iN z b ip
  let (rewriter, notExact) ← emitLLVMBin rewriter .icmp { predicate := .ne } i1 a zb ip
  let (rewriter, aNeg) ← emitLLVMBin rewriter .icmp { predicate := .slt } i1 a zero ip
  let (rewriter, bNeg) ← emitLLVMBin rewriter .icmp { predicate := .slt } i1 b zero ip
  let (rewriter, signEqual) ← emitLLVMBin rewriter .icmp { predicate := .eq } i1 aNeg bNeg ip
  let (rewriter, cond) ← emitLLVMBin rewriter .and () i1 notExact signEqual ip
  let (rewriter, zp1) ← emitLLVMBin rewriter .add { nsw := false, nuw := false } iN z one ip
  let (rewriter, res) ← emitLLVMSelect rewriter iN cond zp1 z ip
  let rewriter := rewriter.replaceValue! (op.getResult 0 : ValuePtr) res
  return rewriter.eraseOp! op

/--
  `arith.floordivsi a, b` → `z = a sdiv b; (a != z*b) && (sign a != sign b) ? z-1 : z`.
  Implemented with `add z, -1`. UB gating matches `arith.divsi`.
-/
def lowerFloorDivSI (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operands, _) := matchOp op rewriter.ctx (.arith .floordivsi) 2
    | return rewriter
  let a := operands[0]!
  let b := operands[1]!
  let some width := intBitwidth rewriter a | return rewriter
  let iN : TypeAttr := IntegerType.mk width
  let i1 : TypeAttr := IntegerType.mk 1
  let ip := InsertPoint.before op
  let (rewriter, zero) ← emitLLVMIntConst rewriter 0 width ip
  let (rewriter, negOne) ← emitLLVMIntConst rewriter (-1) width ip
  let (rewriter, z) ← emitLLVMBin rewriter .sdiv { exact := false } iN a b ip
  let (rewriter, zb) ← emitLLVMBin rewriter .mul { nsw := false, nuw := false } iN z b ip
  let (rewriter, notExact) ← emitLLVMBin rewriter .icmp { predicate := .ne } i1 a zb ip
  let (rewriter, aNeg) ← emitLLVMBin rewriter .icmp { predicate := .slt } i1 a zero ip
  let (rewriter, bNeg) ← emitLLVMBin rewriter .icmp { predicate := .slt } i1 b zero ip
  let (rewriter, signOpposite) ← emitLLVMBin rewriter .icmp { predicate := .ne } i1 aNeg bNeg ip
  let (rewriter, cond) ← emitLLVMBin rewriter .and () i1 notExact signOpposite ip
  let (rewriter, zm1) ← emitLLVMBin rewriter .add { nsw := false, nuw := false } iN z negOne ip
  let (rewriter, res) ← emitLLVMSelect rewriter iN cond zm1 z ip
  let rewriter := rewriter.replaceValue! (op.getResult 0 : ValuePtr) res
  return rewriter.eraseOp! op

/--
  `arith.addui_extended a, b` → two results: `sum = a + b` and the unsigned
  overflow flag `carry = icmp ult sum, a`. LLVM's `uadd.with.overflow` intrinsic is
  not available in Veir's `llvm` dialect, so the carry is computed directly.
-/
def lowerAddUIExtended (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let ctx : IRContext OpCode := rewriter.ctx
  if op.getOpType! ctx = .arith .addui_extended then
    if op.getNumOperands! ctx = 2 then
      let operands := op.getOperands! ctx
      let a := operands[0]!
      let b := operands[1]!
      let some width := intBitwidth rewriter a | return rewriter
      let iN : TypeAttr := IntegerType.mk width
      let i1 : TypeAttr := IntegerType.mk 1
      let ip := InsertPoint.before op
      let (rewriter, sum) ← emitLLVMBin rewriter .add { nsw := false, nuw := false } iN a b ip
      let (rewriter, carry) ← emitLLVMBin rewriter .icmp { predicate := .ult } i1 sum a ip
      let rewriter := rewriter.replaceValue! (op.getResult 0 : ValuePtr) sum
      let rewriter := rewriter.replaceValue! (op.getResult 1 : ValuePtr) carry
      return rewriter.eraseOp! op
    else return rewriter
  else return rewriter

/--
  Lower a two-result extended multiply (`arith.mulsi_extended` /
  `arith.mului_extended`). Both produce the low half `mul a, b` and a high half.
  Following MLIR's `MulIExtendedOpLowering`, the high half is computed by
  extending both operands to `2*N` bits (signed for `mulsi_extended`, unsigned for
  `mului_extended`), multiplying, shifting right by `N`, and truncating back.

  The `emitExt` closure supplies the concrete `sext`/`zext` extension so the two
  variants stay monomorphic in the (universe-polymorphic) op properties.
-/
def lowerMulExtended (theArithOp : Arith)
    (emitExt : PatternRewriter OpCode → TypeAttr → ValuePtr → InsertPoint →
      Option (PatternRewriter OpCode × ValuePtr))
    (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let ctx : IRContext OpCode := rewriter.ctx
  if op.getOpType! ctx = .arith theArithOp then
    if op.getNumOperands! ctx = 2 then
      let operands := op.getOperands! ctx
      let a := operands[0]!
      let b := operands[1]!
      let some width := intBitwidth rewriter a | return rewriter
      let iN : TypeAttr := IntegerType.mk width
      let i2N : TypeAttr := IntegerType.mk (2 * width)
      let ip := InsertPoint.before op
      let (rewriter, low) ← emitLLVMBin rewriter .mul { nsw := false, nuw := false } iN a b ip
      let (rewriter, aExt) ← emitExt rewriter i2N a ip
      let (rewriter, bExt) ← emitExt rewriter i2N b ip
      let (rewriter, wideMul) ← emitLLVMBin rewriter .mul { nsw := false, nuw := false } i2N aExt bExt ip
      let (rewriter, shiftAmt) ← emitLLVMIntConst rewriter (width : Int) (2 * width) ip
      let (rewriter, hiWide) ← emitLLVMBin rewriter .lshr { exact := false } i2N wideMul shiftAmt ip
      let (rewriter, high) ← emitLLVMUnary rewriter .trunc { nsw := false, nuw := false } iN hiWide ip
      let rewriter := rewriter.replaceValue! (op.getResult 0 : ValuePtr) low
      let rewriter := rewriter.replaceValue! (op.getResult 1 : ValuePtr) high
      return rewriter.eraseOp! op
    else return rewriter
  else return rewriter

def lowerMulSIExtended := lowerMulExtended .mulsi_extended
  (fun rw ty v ip => emitLLVMUnary rw .sext () ty v ip)
def lowerMulUIExtended := lowerMulExtended .mului_extended
  (fun rw ty v ip => emitLLVMUnary rw .zext { nneg := false } ty v ip)

/-! ## Pass implementation -/

def ArithToLLVMPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    lowerConstant,
    lowerAddI, lowerSubI, lowerMulI, lowerShlI, lowerTruncI,
    lowerDivSI, lowerDivUI, lowerShrSI, lowerShrUI,
    lowerRemSI, lowerRemUI, lowerAndI, lowerXorI, lowerOrI,
    lowerExtUI, lowerExtSI, lowerCmpI, lowerSelect,
    lowerMaxSI, lowerMinSI, lowerMaxUI, lowerMinUI,
    lowerCeilDivUI, lowerCeilDivSI, lowerFloorDivSI,
    lowerAddUIExtended, lowerMulSIExtended, lowerMulUIExtended
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying arith-to-llvm lowering"
  | some ctx => pure ctx

public def ArithToLLVMPass : Pass OpCode :=
  { name := "arith-to-llvm"
    description := "Lower arith operations to the llvm dialect."
    run := ArithToLLVMPass.impl }

end Veir
