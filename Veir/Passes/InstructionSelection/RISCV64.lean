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

set_option warn.sorry false in
/--
    llvm.icmp eq lhs rhs  -> riscv.sltiu (riscv.xor lhs rhs) 1
    llvm.icmp ne lhs rhs  -> riscv.sltu 0 (riscv.xor lhs rhs)
    llvm.icmp slt lhs rhs -> riscv.slt lhs rhs
    llvm.icmp sle lhs rhs -> riscv.xori (riscv_slt rhs lhs) 1
    llvm.icmp sgt lhs rhs -> riscv.slt rhs lhs
    llvm.icmp sge lhs rhs -> riscv.xori (riscv_slt lhs rhs) 1
    llvm.icmp ult lhs rhs -> riscv.sltu lhs rhs
    llvm.icmp ule lhs rhs -> riscv.xori (riscv_sltu rhs lhs) 1
    llvm.icmp ugt lhs rhs -> riscv.sltu rhs lhs
    llvm.icmp uge lhs rhs -> riscv.xori (riscv_sltu lhs rhs) 1
-/
def icmp (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, property) := matchIcmp op rewriter.ctx | return rewriter
  /- only support `i64` -/
  let .integerType ltype := (lhs.getType! rewriter.ctx).val | return rewriter
  if ltype.bitwidth ≠ 64 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx).val | return rewriter
  if rtype.bitwidth ≠ 64 then return rewriter
  /- Return if the predicate is invalid. -/
  let p := property.value.value.toNat
  if 10 ≤ p then return rewriter
  /- Casting is necessary regardless of the predicate. -/
  let (rewriter, lcastOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Casting back result for type consistency is always necessary. -/
  let type := ((op.getResult 0).get! rewriter.ctx).type
  let .integerType type' := type.val | rewriter
  /- Match depending on the predicate and build correct lowering. -/
  let (rewriter, retOp) ← match p with
    | 0 =>
      /- llvm.icmp eq lhs rhs  -> riscv.sltiu (riscv.xor lhs rhs) 1 -/
      let (rewriter, xorOp) ← rewriter.createOp .riscv_xor #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (rewriter, retOp) ← rewriter.createOp .riscv_sltiu #[RegisterType.mk] #[xorOp.getResult 0]
        #[] #[] c1 (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 1 =>
      /- llvm.icmp ne lhs rhs  -> riscv.sltu 0 (riscv.xor lhs rhs) -/
      let (rewriter, xorOp) ← rewriter.createOp .riscv_xor #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c0 := RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64))
      let (rewriter, liOp) ← rewriter.createOp .riscv_li #[RegisterType.mk] #[]
        #[] #[] c0 (some $ .before op) sorry (by simp) (by simp) sorry
      let (rewriter, retOp) ← rewriter.createOp .riscv_sltu #[RegisterType.mk] #[liOp.getResult 0, xorOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 2 =>
      /- llvm.icmp slt lhs rhs -> riscv.slt lhs rhs  -/
      let (rewriter, retOp) ← rewriter.createOp .riscv_slt #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 3 =>
      /- llvm.icmp sle lhs rhs -> riscv.xori (riscv_slt rhs lhs) 1 -/
      let (rewriter, sltOp) ← rewriter.createOp .riscv_slt #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (rewriter, retOp) ← rewriter.createOp .riscv_xori #[RegisterType.mk] #[sltOp.getResult 0]
        #[] #[] c1 (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 4 =>
      /- llvm.icmp sgt lhs rhs -> riscv.slt rhs lhs -/
      let (rewriter, retOp) ← rewriter.createOp .riscv_slt #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 5 =>
      /- llvm.icmp sge lhs rhs -> riscv.xori (riscv_slt lhs rhs) 1 -/
      let (rewriter, sltOp) ← rewriter.createOp .riscv_slt #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (rewriter, retOp) ← rewriter.createOp .riscv_xori #[RegisterType.mk] #[sltOp.getResult 0]
        #[] #[] c1 (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 6 =>
      /- llvm.icmp ult lhs rhs -> riscv.sltu lhs rhs -/
      let (rewriter, retOp) ← rewriter.createOp .riscv_sltu #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 7 =>
      /- llvm.icmp ule lhs rhs -> riscv.xori (riscv_sltu rhs lhs) 1 -/
      let (rewriter, sltuOp) ← rewriter.createOp .riscv_sltu #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (rewriter, retOp) ← rewriter.createOp .riscv_xori #[RegisterType.mk] #[sltuOp.getResult 0]
        #[] #[] c1 (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 8 =>
      /- llvm.icmp ugt lhs rhs -> riscv.sltu rhs lhs -/
      let (rewriter, retOp) ← rewriter.createOp .riscv_sltu #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 9 =>
      /- llvm.icmp uge lhs rhs -> riscv.xori (riscv_sltu lhs rhs) 1 -/
      let (rewriter, sltuOp) ← rewriter.createOp .riscv_sltu #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (rewriter, retOp) ← rewriter.createOp .riscv_xori #[RegisterType.mk] #[sltuOp.getResult 0]
        #[] #[] c1 (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | _ =>
      return rewriter
  let (rewriter, castEqOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[type] #[retOp.getResult 0]
        #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castEqOp sorry sorry sorry

set_option warn.sorry false in
/-- llvm.or -> riscv.or -/
def or (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchOr op rewriter.ctx | return rewriter
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
  /- Actual `riscv.or` -/
  let (rewriter, orOp) ← rewriter.createOp .riscv_or #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castOrOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[type] #[orOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOrOp sorry sorry sorry

set_option warn.sorry false in
/-- llvm.xor -> riscv.xor -/
def xor (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchXor op rewriter.ctx | return rewriter
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
  /- Actual `riscv.xor` -/
  let (rewriter, xorOp) ← rewriter.createOp .riscv_xor #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castXorOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[type] #[xorOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castXorOp sorry sorry sorry

set_option warn.sorry false in
/-- llvm.mul -> riscv.mul -/
def mul (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchMul op rewriter.ctx | return rewriter
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
  /- Actual `riscv.mul` -/
  let (rewriter, mulOp) ← rewriter.createOp .riscv_mul #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[type] #[mulOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry

set_option warn.sorry false in
/-- llvm.sdiv -> riscv.div -/
def sdiv (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchSdiv op rewriter.ctx | return rewriter
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
  /- Actual `riscv.div` -/
  let (rewriter, divOp) ← rewriter.createOp .riscv_div #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[type] #[divOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry

set_option warn.sorry false in
/-- llvm.udiv -> riscv.divu -/
def udiv (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchUdiv op rewriter.ctx | return rewriter
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
  /- Actual `riscv.div` -/
  let (rewriter, divuOp) ← rewriter.createOp .riscv_divu #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[type] #[divuOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry

set_option warn.sorry false in
/-- llvm.srem -> riscv.rem -/
def srem (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchSrem op rewriter.ctx | return rewriter
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
  /- Actual `riscv.rem` -/
  let (rewriter, remOp) ← rewriter.createOp .riscv_rem #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[type] #[remOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry

set_option warn.sorry false in
/-- llvm.urem -> riscv.remu -/
def urem (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchUrem op rewriter.ctx | return rewriter
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
  /- Actual `riscv.remu` -/
  let (rewriter, remuOp) ← rewriter.createOp .riscv_remu #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp .builtin_unrealized_conversion_cast #[type] #[remuOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry

/-! # Pass implementation -/

set_option warn.sorry false in
def ISelPass.impl (ctx : { ctx' : IRContext OpCode // ctx'.WellFormed }) (op : OperationPtr)
    (_ : op.InBounds ctx.val) :
    ExceptT String IO { ctx' : IRContext OpCode // ctx'.WellFormed } := do
  let pattern := RewritePattern.GreedyRewritePattern #[constant, add, and, ashr, icmp, or, xor, mul,
    sdiv, udiv, srem, urem]
  match RewritePattern.applyInContext pattern ctx ctx.property.inBounds with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ⟨ctx, sorry⟩

public def IselRISCV64 : Pass OpCode :=
  { name := "isel-riscv64"
    description :=
      "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := ISelPass.impl }
