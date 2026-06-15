import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir

/-!
  This file replicates instruction selection patterns from LLVM's SelectionDAG instruction selector,
  to lower LLVM IR to RISC-V assembly (64 bits).
-/

/-! # SelectionDAG Lowering Patterns  -/

set_option warn.sorry false in
/--
  `sub (shl M (8 - Y)) (lshr M Y)` -> `riscv.orcb M`,
  where `M = and Z (0x0101_0101_0101_0101 <<< Y)`
-/
def orcb (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (a, b, _) := matchSub op rewriter.ctx | return rewriter
  /- only support `i64` -/
  let .integerType atype := (a.getType! rewriter.ctx.raw).val | return rewriter
  if atype.bitwidth ≠ 64 then return rewriter
  let .integerType btype := (b.getType! rewriter.ctx.raw).val | return rewriter
  if btype.bitwidth ≠ 64 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let .integerType type' := type.val | rewriter
  if type'.bitwidth ≠ 64 then return rewriter
  /- match `shl M (8 - Y)` -/
  let some aOp := getDefiningOp a rewriter.ctx | return rewriter
  let some (m, shamt, _) := matchShl aOp rewriter.ctx | return rewriter
  let some shc := matchConstantIntVal shamt rewriter.ctx | return rewriter
  /- we do not match a subtraction `8 - Y`, but match the result directly
    for some `0 ≤ Y < 8` -/
  if shc.value < 1 || 8 < shc.value then return rewriter
  let y : Nat := (8 - shc.value).toNat
  /- check `M = and Z (0x0101_0101_0101_0101 <<< Y)` -/
  let some mOp := getDefiningOp m rewriter.ctx | return rewriter
  let some (z, mask) := matchAnd mOp rewriter.ctx | return rewriter
  let some maskBv := matchConstantIntVal mask rewriter.ctx | return rewriter
  let maskBV : BitVec 64 := BitVec.ofNat 64 0x0101010101010101 <<< y
  if BitVec.ofInt 64 maskBv.value ≠ maskBV then return rewriter
  /- right operand must be `M` itself (when `Y = 0`) or `lshr M Y` -/
  if y = 0 then
    /- b must be `M` -/
    if b = m then
      /- apply rewrite -/
      let (rewriter, mCastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[m]
          #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      /- actual `riscv.orcb` -/
      let (rewriter, orcbOp) ← rewriter.createOp (.riscv .orcb) #[RegisterType.mk] #[mCastOp.getResult 0]
          #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      /- cast back result for type consistency -/
      let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[orcbOp.getResult 0]
          #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
      rewriter.replaceOp op castOp sorry sorry sorry sorry sorry
    else return rewriter
  else
    /- match `lshr M Y` -/
    let some bOp := getDefiningOp b rewriter.ctx | return rewriter
    let some (m', y', _) := matchLshr bOp rewriter.ctx | return rewriter
    let some yVal := matchConstantIntVal y' rewriter.ctx | return rewriter
    if yVal.value = y ∧ m = m' then
      /- apply rewrite -/
      let (rewriter, mCastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[m]
          #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      /- actual `riscv.orcb` -/
      let (rewriter, orcbOp) ← rewriter.createOp (.riscv .orcb) #[RegisterType.mk] #[mCastOp.getResult 0]
          #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      /- cast back result for type consistency -/
      let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[orcbOp.getResult 0]
          #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
      rewriter.replaceOp op castOp sorry sorry sorry sorry sorry
    else return rewriter



/-! # Pass implementation -/

def IselSDAG.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[orcb]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying SDAG patterns"
  | some ctx => pure ctx

public def IselSDAG : Pass OpCode :=
  { name := "isel-sdag-riscv64"
    description :=
      "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := IselSDAG.impl }
