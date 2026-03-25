import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.InstCombine

namespace Veir

/-!
  This file replicates LLVM's GlobalISel instruction selector,
  to lower LLVM IR to RISC-V assembly (64 bits).
-/

/-! # Matching Helpers -/

def matchAdd (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf .llvm_add) := do
  let (op, properties) ← matchOp op ctx .llvm_add 2
  return (op[0]!, op[1]!, properties)

/-! # Lowering Patterns -/

set_option warn.sorry false in
/-- llvm.constant -> riscv.li -/
def constant (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some const := matchConstantOp op rewriter.ctx
      | return rewriter
  if const.type.bitwidth ≠ 64 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx).type
  let (rewriter, newOp) ← rewriter.createOp .riscv_li #[type] #[]
      #[] #[] {value := const} (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry

set_option warn.sorry false in
/-- llvm.add -> riscv.add -/
def add (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, properties) := matchAdd op rewriter.ctx
    | return rewriter
  let .integerType type := (lhs.getType! rewriter.ctx).val | return rewriter
  if type.bitwidth ≠ 64 then return rewriter
  let .integerType type := (rhs.getType! rewriter.ctx).val | return rewriter
  if type.bitwidth ≠ 64 then return rewriter
  /- the lowered instruction is `riscv_add`, regardless of the `nuw` and `nsw` flags -/
  let (rewriter, newOp) ← rewriter.createOp .riscv_add #[lhs.getType! rewriter.ctx] #[lhs, rhs]
    #[] #[] () (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry

/-! # Pass implementation -/

set_option warn.sorry false in
def ISelPass.impl (ctx : { ctx' : IRContext OpCode // ctx'.WellFormed }) (op : OperationPtr)
    (_ : op.InBounds ctx.val) :
    ExceptT String IO { ctx' : IRContext OpCode // ctx'.WellFormed } := do
  let pattern := RewritePattern.GreddyRewritePattern #[add, constant]
  match RewritePattern.applyInContext pattern ctx ctx.property.inBounds with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ⟨ctx, sorry⟩

public def IselRISCV64 : Pass OpCode :=
  { name := "isel-riscv64"
    description :=
      "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := ISelPass.impl }
