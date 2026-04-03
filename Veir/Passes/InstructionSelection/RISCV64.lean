import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir

/-!
  This file replicates LLVM's GlobalISel instruction selector,
  to lower LLVM IR to RISC-V assembly (64 bits).
-/

/-! # Lowering Patterns -/

set_option warn.sorry false in
/-- llvm.constant -> riscv.li -/
def constant (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some const := matchConstantOp op rewriter.ctx
      | return rewriter
  if const.type.bitwidth ≠ 64 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx).type
  let .integerType type' := type.val | rewriter
  if type'.bitwidth ≠ 64 then return rewriter
  let (rewriter, newOp) ← rewriter.createOp .riscv_li #[RegisterType.mk] #[]
      #[] #[] {value := const} (some $ .before op) (by simp) (by simp) (by simp) sorry
  let (rewriter, castOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[type]
      #[newOp.getResult 0] #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry

set_option warn.sorry false in
/-- llvm.add -> riscv.add -/
def add (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, properties) := matchAdd op rewriter.ctx | return rewriter
  /- only support `i64` -/
  let .integerType ltype := (lhs.getType! rewriter.ctx).val | return rewriter
  if ltype.bitwidth ≠ 64 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx).val | return rewriter
  if rtype.bitwidth ≠ 64 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx).type
  let .integerType type' := type.val | rewriter
  if type'.bitwidth ≠ 64 then return rewriter
  /- First, cast the operands to registers -/
  let (rewriter, lcastOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Actual `riscv.add` -/
  let (rewriter, addOp) ← rewriter.createOp .riscv_add #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castAddOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[type] #[addOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castAddOp sorry sorry sorry

set_option warn.sorry false in
/-- llvm.and -> riscv.and -/
def and (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs) := matchAnd op rewriter.ctx | return rewriter
  /- only support `i64` -/
  let .integerType ltype := (lhs.getType! rewriter.ctx).val | return rewriter
  if ltype.bitwidth ≠ 64 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx).val | return rewriter
  if rtype.bitwidth ≠ 64 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx).type
  let .integerType type' := type.val | rewriter
  if type'.bitwidth ≠ 64 then return rewriter
  /- First, cast the operands to registers -/
  let (rewriter, lcastOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Actual `riscv.and` -/
  let (rewriter, andOp) ← rewriter.createOp .riscv_and #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castAddOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[type] #[andOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castAddOp sorry sorry sorry

set_option warn.sorry false in
/-- llvm.ashr -> riscv.sra -/
def ashr (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, properties) := matchAshr op rewriter.ctx | return rewriter
  /- only support `i64` -/
  let .integerType ltype := (lhs.getType! rewriter.ctx).val | return rewriter
  if ltype.bitwidth ≠ 64 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx).val | return rewriter
  if rtype.bitwidth ≠ 64 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx).type
  let .integerType type' := type.val | rewriter
  if type'.bitwidth ≠ 64 then return rewriter
  /- First, cast the operands to registers -/
  let (rewriter, lcastOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Actual `riscv.sra` -/
  let (rewriter, sraOp) ← rewriter.createOp .riscv_sra #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castSraOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[type] #[sraOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castSraOp sorry sorry sorry

/-! # Pass implementation -/

set_option warn.sorry false in
def ISelPass.impl (ctx : { ctx' : IRContext OpCode // ctx'.WellFormed }) (op : OperationPtr)
    (_ : op.InBounds ctx.val) :
    ExceptT String IO { ctx' : IRContext OpCode // ctx'.WellFormed } := do
  let pattern := RewritePattern.GreedyRewritePattern #[constant, add, and, ashr]
  match RewritePattern.applyInContext pattern ctx ctx.property.inBounds with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ⟨ctx, sorry⟩

public def IselRISCV64 : Pass OpCode :=
  { name := "isel-riscv64"
    description :=
      "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := ISelPass.impl }
