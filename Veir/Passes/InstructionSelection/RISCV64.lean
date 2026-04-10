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
  let (rewriter, newOp) ← rewriter.createOp (.riscv .li) #[RegisterType.mk] #[]
      #[] #[] {value := const} (some $ .before op) (by simp) (by simp) (by simp) sorry
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type]
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
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Actual `riscv.add` -/
  let (rewriter, addOp) ← rewriter.createOp (.riscv .add) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castAddOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[addOp.getResult 0]
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
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Actual `riscv.and` -/
  let (rewriter, andOp) ← rewriter.createOp (.riscv .and) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castAddOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[andOp.getResult 0]
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
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Actual `riscv.sra` -/
  let (rewriter, sraOp) ← rewriter.createOp (.riscv .sra) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castSraOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[sraOp.getResult 0]
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
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Casting back result for type consistency is always necessary. -/
  let type := ((op.getResult 0).get! rewriter.ctx).type
  let .integerType type' := type.val | rewriter
  /- Match depending on the predicate and build correct lowering. -/
  let (rewriter, retOp) ← match p with
    | 0 =>
      /- llvm.icmp eq lhs rhs  -> riscv.sltiu (riscv.xor lhs rhs) 1 -/
      let (rewriter, xorOp) ← rewriter.createOp (.riscv .xor) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (rewriter, retOp) ← rewriter.createOp (.riscv .sltiu) #[RegisterType.mk] #[xorOp.getResult 0]
        #[] #[] c1 (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 1 =>
      /- llvm.icmp ne lhs rhs  -> riscv.sltu 0 (riscv.xor lhs rhs) -/
      let (rewriter, xorOp) ← rewriter.createOp (.riscv .xor) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c0 := RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64))
      let (rewriter, liOp) ← rewriter.createOp (.riscv .li) #[RegisterType.mk] #[]
        #[] #[] c0 (some $ .before op) sorry (by simp) (by simp) sorry
      let (rewriter, retOp) ← rewriter.createOp (.riscv .sltu) #[RegisterType.mk] #[liOp.getResult 0, xorOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 2 =>
      /- llvm.icmp slt lhs rhs -> riscv.slt lhs rhs  -/
      let (rewriter, retOp) ← rewriter.createOp (.riscv .slt) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 3 =>
      /- llvm.icmp sle lhs rhs -> riscv.xori (riscv_slt rhs lhs) 1 -/
      let (rewriter, sltOp) ← rewriter.createOp (.riscv .slt) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (rewriter, retOp) ← rewriter.createOp (.riscv .xori) #[RegisterType.mk] #[sltOp.getResult 0]
        #[] #[] c1 (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 4 =>
      /- llvm.icmp sgt lhs rhs -> riscv.slt rhs lhs -/
      let (rewriter, retOp) ← rewriter.createOp (.riscv .slt) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 5 =>
      /- llvm.icmp sge lhs rhs -> riscv.xori (riscv_slt lhs rhs) 1 -/
      let (rewriter, sltOp) ← rewriter.createOp (.riscv .slt) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (rewriter, retOp) ← rewriter.createOp (.riscv .xori) #[RegisterType.mk] #[sltOp.getResult 0]
        #[] #[] c1 (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 6 =>
      /- llvm.icmp ult lhs rhs -> riscv.sltu lhs rhs -/
      let (rewriter, retOp) ← rewriter.createOp (.riscv .sltu) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 7 =>
      /- llvm.icmp ule lhs rhs -> riscv.xori (riscv_sltu rhs lhs) 1 -/
      let (rewriter, sltuOp) ← rewriter.createOp (.riscv .sltu) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (rewriter, retOp) ← rewriter.createOp (.riscv .xori) #[RegisterType.mk] #[sltuOp.getResult 0]
        #[] #[] c1 (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 8 =>
      /- llvm.icmp ugt lhs rhs -> riscv.sltu rhs lhs -/
      let (rewriter, retOp) ← rewriter.createOp (.riscv .sltu) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 9 =>
      /- llvm.icmp uge lhs rhs -> riscv.xori (riscv_sltu lhs rhs) 1 -/
      let (rewriter, sltuOp) ← rewriter.createOp (.riscv .sltu) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (rewriter, retOp) ← rewriter.createOp (.riscv .xori) #[RegisterType.mk] #[sltuOp.getResult 0]
        #[] #[] c1 (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | _ =>
      return rewriter
  let (rewriter, castEqOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[retOp.getResult 0]
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
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Actual `riscv.or` -/
  let (rewriter, orOp) ← rewriter.createOp (.riscv .or) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castOrOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[orOp.getResult 0]
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
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Actual `riscv.xor` -/
  let (rewriter, xorOp) ← rewriter.createOp (.riscv .xor) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castXorOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[xorOp.getResult 0]
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
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Actual `riscv.mul` -/
  let (rewriter, mulOp) ← rewriter.createOp (.riscv .mul) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[mulOp.getResult 0]
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
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Actual `riscv.div` -/
  let (rewriter, divOp) ← rewriter.createOp (.riscv .div) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[divOp.getResult 0]
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
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Actual `riscv.div` -/
  let (rewriter, divuOp) ← rewriter.createOp (.riscv .divu) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[divuOp.getResult 0]
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
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Actual `riscv.rem` -/
  let (rewriter, remOp) ← rewriter.createOp (.riscv .rem) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[remOp.getResult 0]
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
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Actual `riscv.remu` -/
  let (rewriter, remuOp) ← rewriter.createOp (.riscv .remu) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[remuOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry

set_option warn.sorry false in
/--
  llvm.sext %x i8  to iY -> riscv.sextb %x
  llvm.sext %x i16 to iY -> riscv.sexth %x
  llvm.sext %x i32 to iY -> riscv.sextw %x

  For every other width:
  llvm.sext %x iX to iY-> riscv.srai (riscv.slli %x (64 - X)) (64 - X)
-/
def sext (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (operand, _) := matchSext op rewriter.ctx | return rewriter
  /- Only support extensions fron `iX` to `iY` where both `X < 64` and `Y < 64`. -/
  let .integerType opType := (operand.getType! rewriter.ctx).val | return rewriter
  if 64 < opType.bitwidth then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx).type
  let .integerType retType := type.val | rewriter
  if 64 < retType.bitwidth then return rewriter
  /- First, cast the operand to registers -/
  let (rewriter, opCastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  dbg_trace "width = {opType.bitwidth}"
  let (rewriter, retOp) ← match opType.bitwidth with
    | 8 =>
      let (rewriter, retOp) ← rewriter.createOp (.riscv .sextb) #[RegisterType.mk] #[opCastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 16 =>
      let (rewriter, retOp) ← rewriter.createOp (.riscv .sexth) #[RegisterType.mk] #[opCastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 32 =>
      let (rewriter, retOp) ← rewriter.createOp (.riscv .sextw) #[RegisterType.mk] #[opCastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      dbg_trace "matched with width 32"
      pure (rewriter, retOp)
    | _ =>
      let c := RISCVImmediateProperties.mk (IntegerAttr.mk (64 - opType.bitwidth) (IntegerType.mk 64))
      let (rewriter, slliOp) ← rewriter.createOp (.riscv .slli) #[RegisterType.mk] #[opCastOp.getResult 0]
        #[] #[] c (some $ .before op) sorry (by simp) (by simp) sorry
      let (rewriter, retOp) ← rewriter.createOp (.riscv .srai) #[RegisterType.mk] #[slliOp.getResult 0]
        #[] #[] c (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[retOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry

set_option warn.sorry false in
/--
  llvm.zext %x iX  to iY where X ≤ 12 and X ≠ 8 -> riscv.andi %x (2 ^ X - 1)
  e.g. llvm.zext %x i2  to iY -> riscv.andi %x 3
       llvm.zext %x i3  to iY -> riscv.andi %x 7
       ...
       llvm.zext %x i11 to iY -> riscv.andi %x 2047

  llvm.zext %x i8  to iY -> riscv.sextb %x
  llvm.zext %x i16 to iY -> riscv.zexth %x
  llvm.zext %x i32 to iY -> riscv.zextw %x

  For every other width:
  llvm.zext %x iX to iY-> riscv.srli (riscv.slli %x (64 - X)) (64 - X)
-/
def zext (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (operand, _) := matchZext op rewriter.ctx | return rewriter
  /- Only support extensions fron `iX` to `iY` where both `X < 64` and `Y < 64`. -/
  let .integerType opType := (operand.getType! rewriter.ctx).val | return rewriter
  if 64 < opType.bitwidth then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx).type
  let .integerType retType := type.val | rewriter
  if 64 < retType.bitwidth then return rewriter
  /- First, cast the operand to registers -/
  let (rewriter, opCastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, retOp) ← match opType.bitwidth with
    | 8 =>
      let (rewriter, retOp) ← rewriter.createOp (.riscv .zextb) #[RegisterType.mk] #[opCastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 16 =>
      let (rewriter, retOp) ← rewriter.createOp (.riscv .zexth) #[RegisterType.mk] #[opCastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 32 =>
      let (rewriter, retOp) ← rewriter.createOp (.riscv .zextw) #[RegisterType.mk] #[opCastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | _ =>
      if opType.bitwidth < 12 then
        let c := RISCVImmediateProperties.mk (IntegerAttr.mk (2 ^ opType.bitwidth - 1) (IntegerType.mk 64))
        let (rewriter, retOp) ← rewriter.createOp (.riscv .andi) #[RegisterType.mk] #[opCastOp.getResult 0]
          #[] #[] c (some $ .before op) sorry (by simp) (by simp) sorry
        pure (rewriter, retOp)
      else
        let c := RISCVImmediateProperties.mk (IntegerAttr.mk (64 - opType.bitwidth) (IntegerType.mk 64))
        let (rewriter, slliOp) ← rewriter.createOp (.riscv .slli) #[RegisterType.mk] #[opCastOp.getResult 0]
          #[] #[] c (some $ .before op) sorry (by simp) (by simp) sorry
        let (rewriter, retOp) ← rewriter.createOp (.riscv .srli) #[RegisterType.mk] #[slliOp.getResult 0]
          #[] #[] c (some $ .before op) sorry (by simp) (by simp) sorry
        pure (rewriter, retOp)
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[retOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry

set_option warn.sorry false in
/--
  llvm.trunc %x iX to iY -> builtin_unrealized_conversion_cast (!reg) : iY
-/
def trunc (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some (operand, _) := matchTrunc op rewriter.ctx | return rewriter
  /- Only support extensions fron `iX` to `iY` where both `X < 64` and `Y < 64`. -/
  let .integerType opType := (operand.getType! rewriter.ctx).val | return rewriter
  if 64 < opType.bitwidth then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx).type
  let .integerType retType := type.val | rewriter
  if 64 < retType.bitwidth then return rewriter
  /- First, cast the operand to registers -/
  let (rewriter, opCastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Then, cast register to expected output width. -/
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[opCastOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry

/-! # Pass implementation -/

set_option warn.sorry false in
def ISelPass.impl (ctx : { ctx' : IRContext OpCode // ctx'.WellFormed }) (op : OperationPtr)
    (_ : op.InBounds ctx.val) :
    ExceptT String IO { ctx' : IRContext OpCode // ctx'.WellFormed } := do
  let pattern := RewritePattern.GreedyRewritePattern #[constant, add, and, ashr, icmp, or, xor, mul,
    sdiv, udiv, srem, urem, sext, zext, trunc]
  match RewritePattern.applyInContext pattern ctx ctx.property.inBounds with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ⟨ctx, sorry⟩

public def IselRISCV64 : Pass OpCode :=
  { name := "isel-riscv64"
    description :=
      "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := ISelPass.impl }
