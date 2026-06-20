import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Passes.InstructionSelection.Common

namespace Veir

/-!
  This file replicates instruction selection patterns from LLVM's SelectionDAG instruction selector,
  to lower LLVM IR to RISC-V assembly (64 bits).
-/

/-! # SelectionDAG Lowering Patterns  -/

set_option warn.sorry false in
/--
  `and x (not y)` -> `riscv.andn x y`. The `not` may appear on either operand.
-/
def andn (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs) := matchAnd op rewriter.ctx | return rewriter
  if !allI64 #[lhs, rhs, op.getResult 0] rewriter.ctx.raw then return rewriter
  /- one operand must be `not y`; `x` is the other -/
  let some (x, y) :=
    (match matchNot rhs rewriter.ctx with
     | some y => some (lhs, y)
     | none => match matchNot lhs rewriter.ctx with
               | some y => some (rhs, y)
               | none => none) | return rewriter
  let (rewriter, xReg) ← castToReg rewriter op x
  let (rewriter, yReg) ← castToReg rewriter op y
  /- result = x & ~y -/
  let (rewriter, andnOp) ← rewriter.createOp (.riscv .andn) #[RegisterType.mk] #[xReg, yReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (andnOp.getResult 0)

set_option warn.sorry false in
/--
  `or x (not y)` -> `riscv.orn x y`. The `not` may appear on either operand.
-/
def orn (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchOr op rewriter.ctx | return rewriter
  if !allI64 #[lhs, rhs, op.getResult 0] rewriter.ctx.raw then return rewriter
  /- one operand must be `not y`; `x` is the other -/
  let some (x, y) :=
    (match matchNot rhs rewriter.ctx with
     | some y => some (lhs, y)
     | none => match matchNot lhs rewriter.ctx with
               | some y => some (rhs, y)
               | none => none) | return rewriter
  let (rewriter, xReg) ← castToReg rewriter op x
  let (rewriter, yReg) ← castToReg rewriter op y
  /- result = x | ~y -/
  let (rewriter, ornOp) ← rewriter.createOp (.riscv .orn) #[RegisterType.mk] #[xReg, yReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (ornOp.getResult 0)

set_option warn.sorry false in
/--
  `xor x (not y)` -> `riscv.xnor x y`. The `not` may appear on either operand.
-/
def xnor (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchXor op rewriter.ctx | return rewriter
  if !allI64 #[lhs, rhs, op.getResult 0] rewriter.ctx.raw then return rewriter
  /- one operand must be `not y`; `x` is the other -/
  let some (x, y) :=
    (match matchNot rhs rewriter.ctx with
     | some y => some (lhs, y)
     | none => match matchNot lhs rewriter.ctx with
               | some y => some (rhs, y)
               | none => none) | return rewriter
  let (rewriter, xReg) ← castToReg rewriter op x
  let (rewriter, yReg) ← castToReg rewriter op y
  /- result = ~(x ^ y) -/
  let (rewriter, xnorOp) ← rewriter.createOp (.riscv .xnor) #[RegisterType.mk] #[xReg, yReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (xnorOp.getResult 0)

set_option warn.sorry false in
/--
  `sub (shl M (8 - Y)) (lshr M Y)` -> `riscv.orcb M`,
  where `M = and Z (0x0101_0101_0101_0101 <<< Y)`
-/
def orcb (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (a, b, _) := matchSub op rewriter.ctx | return rewriter
  if !allI64 #[a, b, op.getResult 0] rewriter.ctx.raw then return rewriter
  /- left operand must be `shl M (8 - Y)` for some `0 ≤ Y < 8` -/
  let some aOp := getDefiningOp a rewriter.ctx | return rewriter
  let some (m, shamt, _) := matchShl aOp rewriter.ctx | return rewriter
  let some shc := matchConstantIntVal shamt rewriter.ctx | return rewriter
  if shc.value < 1 || 8 < shc.value then return rewriter
  let y : Nat := (8 - shc.value).toNat
  /- right operand must be `M` itself (when `Y = 0`) or `lshr M Y` -/
  let rightMatches : Bool :=
    if y == 0 then
      decide (b = m)
    else
      match getDefiningOp b rewriter.ctx with
      | none => false
      | some bOp =>
        match matchLshr bOp rewriter.ctx with
        | none => false
        | some (m', yShamt, _) =>
          match matchConstantIntVal yShamt rewriter.ctx with
          | none => false
          | some yc => yc.value == (y : Int) && decide (m' = m)
  if !rightMatches then return rewriter
  /- soundness gate: `M = and Z (0x0101_0101_0101_0101 <<< Y)` -/
  let some mOp := getDefiningOp m rewriter.ctx | return rewriter
  let some (mo0, mo1) := matchAnd mOp rewriter.ctx | return rewriter
  let maskBV : BitVec 64 := BitVec.ofNat 64 0x0101010101010101 <<< y
  let isMask : ValuePtr → Bool := fun v =>
    match matchConstantIntVal v rewriter.ctx with
    | some attr => BitVec.ofInt 64 attr.value == maskBV
    | none => false
  if !(isMask mo0 || isMask mo1) then return rewriter
  let (rewriter, mReg) ← castToReg rewriter op m
  /- actual `riscv.orcb` -/
  let (rewriter, orcbOp) ← rewriter.createOp (.riscv .orcb) #[RegisterType.mk] #[mReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (orcbOp.getResult 0)



/-! # Pass implementation -/

def IselSDAG.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[andn, orn, xnor, orcb]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying SDAG patterns"
  | some ctx => pure ctx

public def IselSDAG : Pass OpCode :=
  { name := "isel-sdag-riscv64"
    description :=
      "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := IselSDAG.impl }
