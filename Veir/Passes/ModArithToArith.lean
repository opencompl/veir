module

public import Veir.Pass
import Veir.Passes.Matching

namespace Veir

/-!
  # ModArithToArith pass

  Lowers operations from the `mod_arith` dialect into operations in the `arith` dialect,
  translating `!mod_arith.int<q : iN>` values to their canonical representation in `[0, q)`.
  The current lowering is trivial, eagerly reducing at all times.

  Since Veir has no Dialect Conversion framework, this pass eagerly inserts `unrealized_conversion_casts`
  to handle the type conversions between `!mod_arith.int<q : iN>` and `iM` that are needed.
-/

/-! ## Unrealized Conversion Casts -/

/-- Emit `unrealized_conversion_cast v : !mod_arith.int<q:iN> → i(legalizeWidth N)`. -/
def castToStorage (legalizeWidth : Nat → Nat) (rewriter : PatternRewriter OpCode)
    (v : ValuePtr) (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  let .modArithType mt := (v.getType! rewriter.ctx.raw).val
    | none
  let storageType : TypeAttr := IntegerType.mk (legalizeWidth mt.bitwidth)
  let (rewriter, castOp) ← rewriter.createOp! (.builtin .unrealized_conversion_cast)
    #[storageType] #[v] #[] #[] () (some ip)
  return (rewriter, (castOp.getResult 0 : ValuePtr))

/-- Emit `unrealized_conversion_cast x : iN → ty`, where `ty` is a `mod_arith` type. -/
def castToModArith (rewriter : PatternRewriter OpCode) (x : ValuePtr) (ty : ModArithType)
    (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  let (rewriter, castOp) ← rewriter.createOp! (.builtin .unrealized_conversion_cast)
    #[ty] #[x] #[] #[] () (some ip)
  return (rewriter, (castOp.getResult 0 : ValuePtr))

/-! ## Unpack / Pack ModArithType -/

/--
  Unpack a `!mod_arith.int<q:iN>` value `v` into the IntegerType `intermediateType`
-/
def unpackValue (legalizeWidth : Nat → Nat) (rewriter : PatternRewriter OpCode) (v : ValuePtr)
    (intermediateType : IntegerType) (ip : InsertPoint) :
    Option (PatternRewriter OpCode × ValuePtr) := do
  let (rewriter, stored) ← castToStorage legalizeWidth rewriter v ip
  let .integerType storageType := (stored.getType! rewriter.ctx.raw).val
    | none
  if intermediateType.bitwidth > storageType.bitwidth then
    let (rewriter, ext) ← rewriter.createOp! (.arith .extui)
      #[intermediateType] #[stored] #[] #[] { nneg := false } (some ip)
    return (rewriter, (ext.getResult 0 : ValuePtr))
  else
    return (rewriter, stored)

/--
  Pack an IntegerType value `v` of IntegerType `intermediateType` into a value of `!mod_arith.int<q:iN>` type `ty`.
-/
def packValue (legalizeWidth : Nat → Nat) (rewriter : PatternRewriter OpCode) (v : ValuePtr)
    (ty : ModArithType) (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  let .integerType intermediateType := (v.getType! rewriter.ctx.raw).val
    | none
  let storageType := IntegerType.mk (legalizeWidth ty.bitwidth)
  if intermediateType.bitwidth > storageType.bitwidth then
    let (rewriter, narrowed) ← rewriter.createOp! (.arith .trunci)
      #[storageType] #[v] #[] #[] { attr := { nsw := false, nuw := true } }
      (some ip)
    castToModArith rewriter (narrowed.getResult 0 : ValuePtr) ty ip
  else
    castToModArith rewriter (v : ValuePtr) ty ip


/-! ## Arith Helpers -/

/-- Emit `arith.constant c : i<width>`. Requires `c` to fit into width (unsigned) -/
def emitArithConstant (rewriter : PatternRewriter OpCode) (c : Int) (width : Nat)
    (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  let ty : TypeAttr := IntegerType.mk width
  let props : ArithConstantProperties := { value := IntegerAttr.mk c (IntegerType.mk width) }
  let (rewriter, c) ← rewriter.createOp! (.arith .constant)
    #[ty] #[] #[] #[] props (some ip)
  return (rewriter, (c.getResult 0 : ValuePtr))

/-- Emit a binary Arith op `arithOp` on `a` and `b` -/
def emitArithBinOp (rewriter : PatternRewriter OpCode) (arithOp : Arith)
    (props : propertiesOf (.arith arithOp)) (a b : ValuePtr) (ip : InsertPoint) :
    Option (PatternRewriter OpCode × ValuePtr) := do
  let ty := a.getType! rewriter.ctx.raw
  let (rewriter, r) ← rewriter.createOp! (.arith arithOp)
    #[ty] #[a, b] #[] #[] props (some ip)
  return (rewriter, (r.getResult 0 : ValuePtr))


/-! ## Barrett Helper -/
/-- Barrett reduction: approximate `⌊r / modulus⌋` with a precomputed reciprocal
    `mu = ⌊2^(2*k) / modulus⌋` (`k = ceil(log2 modulus)`) via widen → multiply → shift → truncate,
    instead of emitting a runtime division. Note: this is the plain reciprocal-multiply approximation
    with a single correction step.

    func reduce(r uint) uint {
    reduced := (r * mu) >> k
    r := r - reduced * q
    if r >= q {
        r := r - q
    }
    return r
    }
-/

def emitBarrettReduction (legalizeWidth : Nat → Nat) (rewriter : PatternRewriter OpCode)
    (r : ValuePtr) (modulus : Int) (width : Nat) (ip : InsertPoint) :
    Option (PatternRewriter OpCode × ValuePtr) := do
  let k : Nat := (modulus - 1).toNat.log2 + 1     -- ceil(log2 modulus)
  let shift : Nat := 2 * k
  let mu : Int := (2 ^ shift) / modulus           -- floor(2^shift / modulus)
  let bw := legalizeWidth (max width (3 * k))     -- width required for r * mu
  let ty : TypeAttr := IntegerType.mk bw
  let ty_i1 : TypeAttr := IntegerType.mk 1

  -- extend if needed
  let (rewriter, r) ←
    if bw > width then
      let (rewriter, ext) ← rewriter.createOp! (.arith .extui)
        #[ty] #[r] #[] #[] { nneg := false } (some ip)
      pure (rewriter, (ext.getResult 0 : ValuePtr))
    else
      pure (rewriter, r)

  let (rewriter, q) ← emitArithConstant rewriter modulus bw ip
  let (rewriter, m) ← emitArithConstant rewriter mu bw ip
  let (rewriter, sh) ← emitArithConstant rewriter shift bw ip


  -- reduced := (r * m) >> shift // (r * m) should be at most 2^(2*bw) - 1, so we can safely truncate to width bits after the shift
  let (rewriter, product) ← rewriter.createOp! (.arith .muli)
    #[ty] #[r, m] #[] #[] { attr := { nsw := false, nuw := true } } (some ip)
  let (rewriter, reduced) ← rewriter.createOp! (.arith .shrui)
    #[ty] #[product.getResult 0, sh] #[] #[] { exact := false} (some ip)

  -- r := r - reduced * q
  let (rewriter, product) ← rewriter.createOp! (.arith .muli)
    #[ty] #[reduced.getResult 0, q] #[] #[] { attr := { nsw := false, nuw := true } } (some ip)
  let (rewriter, remainder) ← rewriter.createOp! (.arith .subi)
    #[ty] #[r, product.getResult 0] #[] #[] { attr := { nsw := false, nuw := true } }
    (some ip)

  -- if r >= q { r := r - q }
  let (rewriter, corr) ← rewriter.createOp! (.arith .cmpi)
    #[ty_i1] #[remainder.getResult 0, q] #[] #[] { predicate := .uge } (some ip)
  let (rewriter, sub) ← rewriter.createOp! (.arith .subi)
    #[ty] #[remainder.getResult 0, q] #[] #[] { attr := { nsw := false, nuw := true } }
    (some ip)

  -- result := select(cmp, r - q, r)
  let (rewriter, result) ← rewriter.createOp! (.arith .select)
    #[ty] #[corr.getResult 0, sub.getResult 0, remainder.getResult 0] #[] #[] ()
    (some ip)

  -- truncate if needed
  if bw > width then
    let (rewriter, narrowed) ← rewriter.createOp! (.arith .trunci)
      #[IntegerType.mk width] #[result.getResult 0] #[] #[]
      { attr := { nsw := false, nuw := true } } (some ip)
    return (rewriter, (narrowed.getResult 0 : ValuePtr))
  else
    return (rewriter, (result.getResult 0 : ValuePtr))

/-! ## Binary op lowering Template -/

abbrev Builder :=
  (rewriter : PatternRewriter OpCode) →
  (lhs rhs modulus : ValuePtr) →
  (ip : InsertPoint) →
  Option (PatternRewriter OpCode × ValuePtr)

/-- Lower a binary `mod_arith` op `modOp`,
    using intermediate Type iM given storage type iN, with M = `legalizeWidth` (`widen` N),
    and using Builder `build` to determine the exact `arith` operations to emit -/
def lowerModArithBinOp (modOp : Mod_Arith) (widen : Nat → Nat) (legalizeWidth : Nat → Nat)
    (build : Builder) (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  -- match op and extract operands:
  let some (operands, _) := matchOp op rewriter.ctx (.mod_arith modOp) 2
    | return rewriter
  let lhs := operands[0]!
  let rhs := operands[1]!
  -- type setup
  let .modArithType modArithType@⟨⟨modulus, storageType⟩⟩ := ((op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw).val
    | return rewriter
  let intermediateWidth := legalizeWidth (widen storageType.bitwidth)
  let intermediateType  := IntegerType.mk intermediateWidth
  -- actual lowering:
  let ip := InsertPoint.before op
  let (rewriter, a) ← unpackValue legalizeWidth rewriter lhs intermediateType ip
  let (rewriter, b) ← unpackValue legalizeWidth rewriter rhs intermediateType ip
  let (rewriter, q) ← emitArithConstant rewriter modulus intermediateWidth ip
  let (rewriter, r) ← build rewriter a b q ip
  let (rewriter, r) ← emitArithBinOp rewriter .remui () r q ip
  let (rewriter, r) ← packValue legalizeWidth rewriter r modArithType ip
  let rewriter := rewriter.replaceValue! (op.getResult 0) r
  return rewriter.eraseOp! op

/-! ## Binary op lowering Patterns -/

def buildAdd : Builder :=
  fun rewriter a b _ ip =>
  emitArithBinOp rewriter .addi { attr := { nsw := false, nuw := false } } a b ip

def lowerModArithAddOp (legalizeWidth : Nat → Nat) := lowerModArithBinOp .add (· + 1) legalizeWidth buildAdd

def buildMul : Builder :=
  fun rewriter a b _ ip =>
  emitArithBinOp rewriter .muli { attr := { nsw := false, nuw := false } } a b ip

def lowerModArithMulOp (legalizeWidth : Nat → Nat) := lowerModArithBinOp .mul (2 * ·) legalizeWidth buildMul

def buildSub : Builder :=
  fun (rewriter : PatternRewriter OpCode) (a b q : ValuePtr) (ip : InsertPoint) => do
    -- we compute a - b (mod q) as ((a+q) - b) % q to avoid unsigned underflow when a < b.
    let (rewriter, aq) ← emitArithBinOp rewriter .addi
      { attr := { nsw := false, nuw := false } } a q ip
    emitArithBinOp rewriter .subi { attr := { nsw := false, nuw := false } } aq b ip

def lowerModArithSubOp (legalizeWidth : Nat → Nat) := lowerModArithBinOp .sub (· + 1) legalizeWidth buildSub

/-! ## Constant lowering Pattern -/

/-- Lower `mod_arith.constant` to an `arith.constant`. -/
def lowerModArithConstantOp (legalizeWidth : Nat → Nat) (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (_opInBounds : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  -- match op and extract attribute:
  let some (_, props) := matchOp op rewriter.ctx (.mod_arith .constant) 0
    | return rewriter
  let c := props.value.value
  -- type setup
  let .modArithType modArithType@⟨⟨q, storageType⟩⟩ := ((op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw).val
    | return rewriter
  -- actual lowering:
  let ip := InsertPoint.before op
  let (rewriter, r) ← emitArithConstant rewriter (c % q) (legalizeWidth storageType.bitwidth) ip
  let (rewriter, out) ← castToModArith rewriter (r : ValuePtr) modArithType ip
  let rewriter := rewriter.replaceValue! (op.getResult 0) out
  return rewriter.eraseOp! op

/-! ## arith.remui rewriting pattern -/

/-- Rewrite `arith.remui r, q` to a Barrett reduction when `q` is a positive constant. -/
def remuiToBarrettReduction (legalizeWidth : Nat → Nat) (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (_opInBounds : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (r, q, _) := matchArithRemui op rewriter.ctx
    | return rewriter

  let some modulusAttr := matchArithConstantIntVal q rewriter.ctx.raw
    | return rewriter
  let modulus := modulusAttr.value

  if modulus <= 0 then
    return rewriter

  let .integerType resultType :=
      ((op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw).val
    | return rewriter

  let ip := InsertPoint.before op
  let (rewriter, reduced) ←
    emitBarrettReduction legalizeWidth rewriter r modulus resultType.bitwidth ip

  let rewriter :=
    rewriter.replaceValue! (op.getResult 0) reduced
  return rewriter.eraseOp! op

/-! ## Pass implementation -/

def ModArithToArithPass.impl (legalizeWidth : Nat → Nat) (ctx : WfIRContext OpCode)
    (op : OperationPtr) (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    lowerModArithConstantOp legalizeWidth,
    lowerModArithAddOp legalizeWidth,
    lowerModArithSubOp legalizeWidth,
    lowerModArithMulOp legalizeWidth
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying mod-arith-to-arith lowering"
  | some ctx => pure ctx

public def ModArithToArithPass : Pass OpCode :=
  { name := "mod-arith-to-arith"
    description := "Lower mod_arith operations to the arith dialect."
    run := ModArithToArithPass.impl id }

public def ModArithToArithPassPow2Width : Pass OpCode :=
  { name := "mod-arith-to-arith-pow2-width"
    description := "Lower mod_arith operations to the arith dialect, using power-of-two bitwidths."
    run := ModArithToArithPass.impl Nat.nextPowerOfTwo }

def RemuiToBarrettReductionPass.impl (legalizeWidth : Nat → Nat) (ctx : WfIRContext OpCode)
    (op : OperationPtr) (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    remuiToBarrettReduction legalizeWidth
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying remui-to-barrett-reduction rewrite"
  | some ctx => pure ctx

public def RemuiToBarrettReductionPass : Pass OpCode :=
  { name := "remui-to-barrett-reduction"
    description := "Rewrite arith.remui operations to Barrett reduction."
    run := RemuiToBarrettReductionPass.impl id }

public def RemuiToBarrettReductionPassPow2Width : Pass OpCode :=
  { name := "remui-to-barrett-reduction-pow2-width"
    description := "Rewrite arith.remui operations to Barrett reduction, using power-of-two bitwidths for intermediate types."
    run := RemuiToBarrettReductionPass.impl Nat.nextPowerOfTwo }
end Veir
