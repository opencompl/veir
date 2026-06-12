import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir

/-!
  # ModArithToArith pass

  Lowers operations from the `mod_arith` dialect into operations in the `arith` dialect,
  translating `!mod_arith.int<q : iN>` values to their canonical representation in `[0, q)`.
  The current lowering is trivial, eagerly reducing at all times.

  Since Veir has no Dialect Conversion framework, this pass eagerly inserts `unrealized_conversion_casts`
  to handle the type conversions between `!mod_arith.int<q : iN>` and `iN` that are needed.
-/

/-! ## Unrealized Conversion Casts -/

set_option warn.sorry false in
/-- Emit `unrealized_conversion_cast v : !mod_arith.int<q:iN> → iN`. -/
def castToStorage (rewriter : PatternRewriter OpCode) (v : ValuePtr) (ip : InsertPoint) :
    Option (PatternRewriter OpCode × ValuePtr) := do
  let .modArithType mt := (v.getType! rewriter.ctx.raw).val
    | none
  let storageType : TypeAttr := mt.modulus.type
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast)
    #[storageType] #[v] #[] #[] () (some ip) sorry (by simp) (by simp) sorry
  return (rewriter, (castOp.getResult 0 : ValuePtr))

set_option warn.sorry false in
/-- Emit `unrealized_conversion_cast x : iN → ty`, where `ty` is a `mod_arith` type. -/
def castToModArith (rewriter : PatternRewriter OpCode) (x : ValuePtr) (ty : ModArithType)
    (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast)
    #[ty] #[x] #[] #[] () (some ip) sorry (by simp) (by simp) sorry
  return (rewriter, (castOp.getResult 0 : ValuePtr))

/-! ## Unpack / Pack ModArithType -/

set_option warn.sorry false in
/--
  Unpack a `!mod_arith.int<q:iN>` value `v` into the IntegerType `intermediateType`
-/
def unpackValue (rewriter : PatternRewriter OpCode) (v : ValuePtr) (intermediateType : IntegerType)
    (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  let (rewriter, stored) ← castToStorage rewriter v ip
  let .integerType storageType := (stored.getType! rewriter.ctx.raw).val
    | none
  if intermediateType.bitwidth > storageType.bitwidth then
    let (rewriter, ext) ← rewriter.createOp (.arith .extui)
      #[intermediateType] #[stored] #[] #[] { nneg := false } (some ip) sorry (by simp) (by simp) sorry
    return (rewriter, (ext.getResult 0 : ValuePtr))
  else
    return (rewriter, stored)

set_option warn.sorry false in
/--
  Pack an IntegerType value `v` of IntegerType `intermediateType` into a value of `!mod_arith.int<q:iN>` type `ty`.
-/
def packValue (rewriter : PatternRewriter OpCode) (v : ValuePtr) (ty : ModArithType)
    (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  let .integerType intermediateType := (v.getType! rewriter.ctx.raw).val
    | none
  let storageType := ty.modulus.type
  if intermediateType.bitwidth > storageType.bitwidth then
    let (rewriter, narrowed) ← rewriter.createOp (.arith .trunci)
      #[storageType] #[v] #[] #[] { attr := { nsw := false, nuw := true } }
      (some ip) sorry (by simp) (by simp) sorry
    castToModArith rewriter (narrowed.getResult 0 : ValuePtr) ty ip
  else
    castToModArith rewriter (v : ValuePtr) ty ip


/-! ## Arith Helpers -/

set_option warn.sorry false in
/-- Emit `arith.constant c : i<width>`. Requires `c` to fit into width (unsigned) -/
def emitArithConstant (rewriter : PatternRewriter OpCode) (c : Int) (width : Nat)
    (ip : InsertPoint) : Option (PatternRewriter OpCode × ValuePtr) := do
  let ty : TypeAttr := IntegerType.mk width
  let props : ArithConstantProperties := { value := IntegerAttr.mk c (IntegerType.mk width) }
  let (rewriter, c) ← rewriter.createOp (.arith .constant)
    #[ty] #[] #[] #[] props (some ip) sorry (by simp) (by simp) sorry
  return (rewriter, (c.getResult 0 : ValuePtr))

set_option warn.sorry false in
/-- Emit a binary Arith op `arithOp` on `a` and `b` -/
def emitArithBinOp (rewriter : PatternRewriter OpCode) (arithOp : Arith)
    (props : propertiesOf (.arith arithOp)) (a b : ValuePtr) (ip : InsertPoint) :
    Option (PatternRewriter OpCode × ValuePtr) := do
  let ty := a.getType! rewriter.ctx.raw
  let (rewriter, r) ← rewriter.createOp (.arith arithOp)
    #[ty] #[a, b] #[] #[] props (some ip) sorry (by simp) (by simp) sorry
  return (rewriter, (r.getResult 0 : ValuePtr))


/-! ## Binary op lowering Template -/

abbrev Builder :=
  (rewriter : PatternRewriter OpCode) →
  (lhs rhs modulus : ValuePtr) →
  (ip : InsertPoint) →
  Option (PatternRewriter OpCode × ValuePtr)

set_option warn.sorry false in
/-- Lower a binary `mod_arith` op `modOp`,
    using intermediate Type iM given storage type iM, with M = `widen` N,
    and using Builder `build` to determine the exact `arith` operations to emit -/
def lowerModArithBinOp (modOp : Mod_Arith) (widen : Nat → Nat) (build : Builder)
    (rewriter : PatternRewriter OpCode) (op : OperationPtr) : Option (PatternRewriter OpCode) := do
  -- match op and extract operands:
  let some (operands, _) := matchOp op rewriter.ctx (.mod_arith modOp) 2
    | return rewriter
  let lhs := operands[0]!
  let rhs := operands[1]!
  -- type setup
  let .modArithType modArithType := ((op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw).val
    | return rewriter
  let intermediateWidth := widen modArithType.modulus.type.bitwidth
  let intermediateType  := IntegerType.mk intermediateWidth
  -- actual lowering:
  let ip := InsertPoint.before op
  let (rewriter, a) ← unpackValue rewriter lhs intermediateType ip
  let (rewriter, b) ← unpackValue rewriter rhs intermediateType ip
  let (rewriter, q) ← emitArithConstant rewriter modArithType.modulus.value intermediateWidth ip
  let (rewriter, r) ← build rewriter a b q ip
  let (rewriter, r) ← emitArithBinOp rewriter .remui () r q ip
  let (rewriter, r) ← packValue rewriter r modArithType ip
  let rewriter := rewriter.replaceValue (op.getResult 0) r sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-! ## Binary op lowering Patterns -/

def buildAdd : Builder :=
  fun rewriter a b _ ip =>
  emitArithBinOp rewriter .addi { attr := { nsw := false, nuw := false } } a b ip

def lowerModArithAddOp := lowerModArithBinOp .add (· + 1) buildAdd

def buildMul : Builder :=
  fun rewriter a b _ ip =>
  emitArithBinOp rewriter .muli { attr := { nsw := false, nuw := false } } a b ip

def lowerModArithMulOp := lowerModArithBinOp .mul (2 * ·) buildMul

def buildSub : Builder :=
  fun (rewriter : PatternRewriter OpCode) (a b q : ValuePtr) (ip : InsertPoint) => do
    -- we compute a - b (mod q) as ((a+q) - b) % q to avoid unsigned underflow when a < b.
    let (rewriter, aq) ← emitArithBinOp rewriter .addi
      { attr := { nsw := false, nuw := false } } a q ip
    emitArithBinOp rewriter .subi { attr := { nsw := false, nuw := false } } aq b ip

def lowerModArithSubOp := lowerModArithBinOp .sub (· + 1) buildSub

/-! ## Constant lowering Pattern -/

set_option warn.sorry false in
/-- Lower `mod_arith.constant` to an `arith.constant` (assumes value is in `[0, q)` already). -/
def lowerModArithConstant (rewriter : PatternRewriter OpCode) (op : OperationPtr) : Option (PatternRewriter OpCode) := do
  -- match op and extract attribute:
  let some (_, props) := matchOp op rewriter.ctx (.mod_arith .constant) 0
    | return rewriter
  let c := props.value.value
  -- type setup
  let .modArithType modArithType := ((op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw).val
    | return rewriter
  let storageType := modArithType.modulus.type
  -- actual lowering:
  let ip := InsertPoint.before op
  let (rewriter, r) ← emitArithConstant rewriter c storageType.bitwidth ip
  let (rewriter, out) ← castToModArith rewriter (r : ValuePtr) modArithType ip
  let rewriter := rewriter.replaceValue (op.getResult 0) out sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

/-! ## Pass implementation -/

def ModArithToArithPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    lowerModArithConstant,
    lowerModArithAddOp,
    lowerModArithSubOp,
    lowerModArithMulOp
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying mod-arith-to-arith lowering"
  | some ctx => pure ctx

public def ModArithToArithPass : Pass OpCode :=
  { name := "mod-arith-to-arith"
    description := "Lower mod_arith operations to the arith dialect."
    run := ModArithToArithPass.impl }

end Veir
