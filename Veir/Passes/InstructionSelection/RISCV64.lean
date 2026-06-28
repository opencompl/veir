import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Passes.InstructionSelection.Common

namespace Veir

/-!
  This file replicates LLVM's GlobalISel instruction selector,
  to lower LLVM IR to RISC-V assembly (64 bits).
-/

/-! # Lowering Patterns -/

/-- Extension operations (`sext`/`zext`) in RISC-V 64 are legal from `i8`, `i16`, and
  `i32` source widths (`zext.b`/`zext.h`/`zext.w`, `sext.b`/`sext.h`/`sext.w`).
  See: https://github.com/llvm/llvm-project/blob/16a0a1042f7e4e5a0c667096fcdeb5803e06d120/llvm/lib/Target/RISCV/GISel/RISCVLegalizerInfo.cpp#L171-L179
-/
def isLegalExtOpWidth (w : Nat) : Bool :=
  w = 8 ∨ w = 16 ∨ w = 32

set_option warn.sorry false in
/--
  `llvm.intr.ctlz` -> `riscv.clz`.
-/
def ctlz (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operand, _) := matchCtlz op rewriter.ctx | return rewriter
  let .integerType opType := (operand.getType! rewriter.ctx.raw).val | return rewriter
  if opType.bitwidth ≠ 64 then return rewriter
  let (rewriter, opReg) ← castToReg rewriter op operand
  let (rewriter, retOp) ← rewriter.createOp (.riscv .clz) #[RegisterType.mk] #[opReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (retOp.getResult 0)

set_option warn.sorry false in
/--
  `llvm.intr.cttz` -> `riscv.ctz`.
-/
def cttz (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operand, _) := matchCttz op rewriter.ctx | return rewriter
  let .integerType opType := (operand.getType! rewriter.ctx.raw).val | return rewriter
  if opType.bitwidth ≠ 64 then return rewriter
  let (rewriter, opReg) ← castToReg rewriter op operand
  let (rewriter, retOp) ← rewriter.createOp (.riscv .ctz) #[RegisterType.mk] #[opReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (retOp.getResult 0)

set_option warn.sorry false in
/--
  `llvm.intr.ctpop` -> `riscv.cpop`.
-/
def ctpop (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some operand := matchCtpop op rewriter.ctx | return rewriter
  let .integerType opType := (operand.getType! rewriter.ctx.raw).val | return rewriter
  if opType.bitwidth ≠ 64 then return rewriter
  let (rewriter, opReg) ← castToReg rewriter op operand
  let (rewriter, retOp) ← rewriter.createOp (.riscv .cpop) #[RegisterType.mk] #[opReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (retOp.getResult 0)

set_option warn.sorry false in
/--
  `llvm.intr.bswap` -> `riscv.rev8`.
-/
def bswap (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some operand := matchBswap op rewriter.ctx | return rewriter
  let .integerType opType := (operand.getType! rewriter.ctx.raw).val | return rewriter
  if opType.bitwidth ≠ 64 then return rewriter
  let (rewriter, opReg) ← castToReg rewriter op operand
  let (rewriter, retOp) ← rewriter.createOp (.riscv .rev8) #[RegisterType.mk] #[opReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (retOp.getResult 0)

set_option warn.sorry false in
/--
  One SWAR bit-reversal stage:
  `((x & mask) << shamt) | ((x >> shamt) & mask)`.
-/
def bitreverseStage (mask shamt : Int) (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (input : ValuePtr) :
    Option (PatternRewriter OpCode × ValuePtr) := do
  let maskAttr := RISCVImmediateProperties.mk (IntegerAttr.mk mask (IntegerType.mk 64))
  let (rewriter, maskOp) ← rewriter.createOp (.riscv .li) #[RegisterType.mk] #[]
      #[] #[] maskAttr (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, lowOp) ← rewriter.createOp (.riscv .and) #[RegisterType.mk]
      #[maskOp.getResult 0, input] #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let shamtAttr := RISCVImmediateProperties.mk (IntegerAttr.mk shamt (IntegerType.mk 64))
  let (rewriter, lowShiftOp) ← rewriter.createOp (.riscv .slli) #[RegisterType.mk]
      #[lowOp.getResult 0] #[] #[] shamtAttr (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, highShiftOp) ← rewriter.createOp (.riscv .srli) #[RegisterType.mk]
      #[input] #[] #[] shamtAttr (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, highOp) ← rewriter.createOp (.riscv .and) #[RegisterType.mk]
      #[maskOp.getResult 0, highShiftOp.getResult 0] #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, orOp) ← rewriter.createOp (.riscv .or) #[RegisterType.mk]
      #[lowShiftOp.getResult 0, highOp.getResult 0] #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  return (rewriter, orOp.getResult 0)

set_option warn.sorry false in
/--
  `llvm.intr.bitreverse` -> mask/shift/or stages followed by `riscv.rev8`.
-/
def bitreverse (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some operand := matchBitreverse op rewriter.ctx | return rewriter
  let .integerType opType := (operand.getType! rewriter.ctx.raw).val | return rewriter
  if opType.bitwidth ≠ 64 then return rewriter
  let (rewriter, opReg) ← castToReg rewriter op operand
  let (rewriter, x1) ← bitreverseStage 0x5555555555555555 1 rewriter op opReg
  let (rewriter, x2) ← bitreverseStage 0x3333333333333333 2 rewriter op x1
  let (rewriter, x3) ← bitreverseStage 0x0f0f0f0f0f0f0f0f 4 rewriter op x2
  let (rewriter, retOp) ← rewriter.createOp (.riscv .rev8) #[RegisterType.mk] #[x3]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (retOp.getResult 0)

set_option warn.sorry false in
/-- llvm.constant -> riscv.li -/
def constant (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some const := matchConstantIntOp op rewriter.ctx
      | return rewriter
  if const.type.bitwidth ≠ 64 ∧ const.type.bitwidth ≠ 32 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let .integerType type' := type.val | rewriter
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.riscv .li) #[RegisterType.mk] #[]
      #[] #[] {value := const} (some $ .before op) (by simp) (by simp) (by simp) sorry
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type]
      #[newOp.getResult 0] #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- llvm.add -> riscv.add -/
def add (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, properties) := matchAdd op rewriter.ctx | return rewriter
  /- support `i64` and `i32` (experiment) -/
  let .integerType ltype := (lhs.getType! rewriter.ctx.raw).val | return rewriter
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx.raw).val | return rewriter
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let .integerType type' := type.val | rewriter
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return rewriter
  /- First, cast the operands to registers -/
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- 64-bit add, or its 32-bit `W` variant for i32 (keeps the result sign-extended) -/
  let (rewriter, addOp) ←
    if type'.bitwidth = 32 then
      rewriter.createOp (.riscv .addw) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
    else
      rewriter.createOp (.riscv .add) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castAddOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[addOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castAddOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- llvm.and -> riscv.and -/
def and (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchAnd op rewriter.ctx | return rewriter
  /- only support `i64` -/
  let .integerType ltype := (lhs.getType! rewriter.ctx.raw).val | return rewriter
  if ltype.bitwidth ≠ 64 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx.raw).val | return rewriter
  if rtype.bitwidth ≠ 64 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let .integerType type' := type.val | rewriter
  if type'.bitwidth ≠ 64 then return rewriter
  /- First, cast the operands to registers -/
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Actual `riscv.and` -/
  let (rewriter, andOp) ← rewriter.createOp (.riscv .and) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castAddOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[andOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castAddOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- llvm.ashr -> riscv.sra -/
def ashr (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, properties) := matchAshr op rewriter.ctx | return rewriter
  /- only support `i64` -/
  let .integerType ltype := (lhs.getType! rewriter.ctx.raw).val | return rewriter
  if ltype.bitwidth ≠ 64 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx.raw).val | return rewriter
  if rtype.bitwidth ≠ 64 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
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
  rewriter.replaceOp op castSraOp sorry sorry sorry sorry sorry

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
def icmp (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, property) := matchIcmp op rewriter.ctx | return rewriter
  /- only support `i64` -/
  let .integerType ltype := (lhs.getType! rewriter.ctx.raw).val | return rewriter
  if ltype.bitwidth ≠ 64 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx.raw).val | return rewriter
  if rtype.bitwidth ≠ 64 then return rewriter
  /- Casting is necessary regardless of the predicate. -/
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Casting back result for type consistency is always necessary. -/
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let .integerType type' := type.val | rewriter
  /- Match depending on the predicate and build correct lowering. -/
  let (rewriter, retOp) ← match property.predicate with
    | .eq =>
      /- llvm.icmp eq lhs rhs  -> riscv.sltiu (riscv.xor lhs rhs) 1 -/
      let (rewriter, xorOp) ← rewriter.createOp (.riscv .xor) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (rewriter, retOp) ← rewriter.createOp (.riscv .sltiu) #[RegisterType.mk] #[xorOp.getResult 0]
        #[] #[] c1 (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | .ne =>
      /- llvm.icmp ne lhs rhs  -> riscv.sltu 0 (riscv.xor lhs rhs) -/
      let (rewriter, xorOp) ← rewriter.createOp (.riscv .xor) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c0 := RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64))
      let (rewriter, liOp) ← rewriter.createOp (.riscv .li) #[RegisterType.mk] #[]
        #[] #[] c0 (some $ .before op) sorry (by simp) (by simp) sorry
      let (rewriter, retOp) ← rewriter.createOp (.riscv .sltu) #[RegisterType.mk] #[liOp.getResult 0, xorOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | .slt =>
      /- llvm.icmp slt lhs rhs -> riscv.slt lhs rhs  -/
      let (rewriter, retOp) ← rewriter.createOp (.riscv .slt) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | .sle =>
      /- llvm.icmp sle lhs rhs -> riscv.xori (riscv_slt rhs lhs) 1 -/
      let (rewriter, sltOp) ← rewriter.createOp (.riscv .slt) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (rewriter, retOp) ← rewriter.createOp (.riscv .xori) #[RegisterType.mk] #[sltOp.getResult 0]
        #[] #[] c1 (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | .sgt =>
      /- llvm.icmp sgt lhs rhs -> riscv.slt rhs lhs -/
      let (rewriter, retOp) ← rewriter.createOp (.riscv .slt) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | .sge =>
      /- llvm.icmp sge lhs rhs -> riscv.xori (riscv_slt lhs rhs) 1 -/
      let (rewriter, sltOp) ← rewriter.createOp (.riscv .slt) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (rewriter, retOp) ← rewriter.createOp (.riscv .xori) #[RegisterType.mk] #[sltOp.getResult 0]
        #[] #[] c1 (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | .ult =>
      /- llvm.icmp ult lhs rhs -> riscv.sltu lhs rhs -/
      let (rewriter, retOp) ← rewriter.createOp (.riscv .sltu) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | .ule =>
      /- llvm.icmp ule lhs rhs -> riscv.xori (riscv_sltu rhs lhs) 1 -/
      let (rewriter, sltuOp) ← rewriter.createOp (.riscv .sltu) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (rewriter, retOp) ← rewriter.createOp (.riscv .xori) #[RegisterType.mk] #[sltuOp.getResult 0]
        #[] #[] c1 (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | .ugt =>
      /- llvm.icmp ugt lhs rhs -> riscv.sltu rhs lhs -/
      let (rewriter, retOp) ← rewriter.createOp (.riscv .sltu) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | .uge =>
      /- llvm.icmp uge lhs rhs -> riscv.xori (riscv_sltu lhs rhs) 1 -/
      let (rewriter, sltuOp) ← rewriter.createOp (.riscv .sltu) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (rewriter, retOp) ← rewriter.createOp (.riscv .xori) #[RegisterType.mk] #[sltuOp.getResult 0]
        #[] #[] c1 (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
  let (rewriter, castEqOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[retOp.getResult 0]
        #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castEqOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- llvm.or -> riscv.or -/
def or (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchOr op rewriter.ctx | return rewriter
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! rewriter.ctx.raw).val | return rewriter
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx.raw).val | return rewriter
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let .integerType type' := type.val | rewriter
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return rewriter
  /- First, cast the operands to registers -/
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Actual `riscv.or` -/
  let (rewriter, orOp) ← rewriter.createOp (.riscv .or) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castOrOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[orOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOrOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- llvm.xor -> riscv.xor -/
def xor (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchXor op rewriter.ctx | return rewriter
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! rewriter.ctx.raw).val | return rewriter
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx.raw).val | return rewriter
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let .integerType type' := type.val | rewriter
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return rewriter
  /- First, cast the operands to registers -/
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Actual `riscv.xor` -/
  let (rewriter, xorOp) ← rewriter.createOp (.riscv .xor) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castXorOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[xorOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castXorOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- llvm.mul -> riscv.mul -/
def mul (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchMul op rewriter.ctx | return rewriter
  /- only support `i64` -/
  let .integerType ltype := (lhs.getType! rewriter.ctx.raw).val | return rewriter
  if ltype.bitwidth ≠ 64 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx.raw).val | return rewriter
  if rtype.bitwidth ≠ 64 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let .integerType type' := type.val | rewriter
  if type'.bitwidth ≠ 64 then return rewriter
  /- First, cast the operands to registers -/
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Actual `riscv.mul` -/
  let (rewriter, mulOp) ← rewriter.createOp (.riscv .mul) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[mulOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- llvm.sdiv -> riscv.div -/
def sdiv (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchSdiv op rewriter.ctx | return rewriter
  /- only support `i64` -/
  let .integerType ltype := (lhs.getType! rewriter.ctx.raw).val | return rewriter
  if ltype.bitwidth ≠ 64 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx.raw).val | return rewriter
  if rtype.bitwidth ≠ 64 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
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
  rewriter.replaceOp op castOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- llvm.udiv -> riscv.divu -/
def udiv (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchUdiv op rewriter.ctx | return rewriter
  /- only support `i64` -/
  let .integerType ltype := (lhs.getType! rewriter.ctx.raw).val | return rewriter
  if ltype.bitwidth ≠ 64 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx.raw).val | return rewriter
  if rtype.bitwidth ≠ 64 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
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
  rewriter.replaceOp op castOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- llvm.srem -> riscv.rem -/
def srem (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchSrem op rewriter.ctx | return rewriter
  /- only support `i64` -/
  let .integerType ltype := (lhs.getType! rewriter.ctx.raw).val | return rewriter
  if ltype.bitwidth ≠ 64 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx.raw).val | return rewriter
  if rtype.bitwidth ≠ 64 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
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
  rewriter.replaceOp op castOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- llvm.urem -> riscv.remu -/
def urem (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchUrem op rewriter.ctx | return rewriter
  /- only support `i64` -/
  let .integerType ltype := (lhs.getType! rewriter.ctx.raw).val | return rewriter
  if ltype.bitwidth ≠ 64 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx.raw).val | return rewriter
  if rtype.bitwidth ≠ 64 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
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
  rewriter.replaceOp op castOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- llvm.sub -> riscv.sub -/
def sub (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchSub op rewriter.ctx | return rewriter
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! rewriter.ctx.raw).val | return rewriter
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx.raw).val | return rewriter
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let .integerType type' := type.val | rewriter
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return rewriter
  /- First, cast the operands to registers -/
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- 64-bit sub, or its 32-bit `W` variant for i32 -/
  let (rewriter, subOp) ←
    if type'.bitwidth = 32 then
      rewriter.createOp (.riscv .subw) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
    else
      rewriter.createOp (.riscv .sub) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[subOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/--
  llvm.sext %x `i16` to `i64` -> riscv.sexth %x
  llvm.sext %x `i16` to `i32` -> riscv.sexth %x
  llvm.sext %x `i32` to `i64` -> riscv.sextw %x
-/
def sext (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (operand, _) := matchSext op rewriter.ctx | return rewriter
  let .integerType opType := (operand.getType! rewriter.ctx.raw).val | return rewriter
  if ¬ isLegalExtOpWidth (opType.bitwidth) then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let .integerType retType := type.val | rewriter
  if retType.bitwidth ≤ opType.bitwidth then return rewriter
  /- First, cast the operand to registers -/
  let (rewriter, opCastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, retOp) ← match opType.bitwidth with
    | 16 =>
      let (rewriter, retOp) ← rewriter.createOp (.riscv .sexth) #[RegisterType.mk] #[opCastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | 32 =>
      let (rewriter, retOp) ← rewriter.createOp (.riscv .sextw) #[RegisterType.mk] #[opCastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      pure (rewriter, retOp)
    | _ =>
      /- unreachable case -/
      return rewriter
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[retOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/--
  llvm.zext %x `i16` to `i64` -> riscv.zexth %x
  llvm.zext %x `i16` to `i32` -> riscv.zexth %x
  llvm.zext %x `i32` to `i64` -> riscv.zextw %x
-/
def zext (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (operand, _) := matchZext op rewriter.ctx | return rewriter
  let .integerType opType := (operand.getType! rewriter.ctx.raw).val | return rewriter
  if ¬ isLegalExtOpWidth (opType.bitwidth) then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let .integerType retType := type.val | rewriter
  if retType.bitwidth ≤ opType.bitwidth then return rewriter
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
      /- unreachable case -/
      return rewriter
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[retOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/--
  llvm.trunc %x iX to iY -> builtin_unrealized_conversion_cast (!riscv.reg) : iY
  where `iY`'s width is smaller than `iX`'s.
-/
def trunc (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (operand, _) := matchTrunc op rewriter.ctx | return rewriter
  let .integerType opType := (operand.getType! rewriter.ctx.raw).val | return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let .integerType retType := type.val | rewriter
  if opType.bitwidth ≤ retType.bitwidth then return rewriter
  /- First, cast the operand to registers -/
  let (rewriter, opCastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Then, cast register to expected output width. -/
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[opCastOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- llvm.shl -> riscv.sll -/
def shl (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchShl op rewriter.ctx | return rewriter
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! rewriter.ctx.raw).val | return rewriter
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx.raw).val | return rewriter
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let .integerType type' := type.val | rewriter
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return rewriter
  /- First, cast the operands to registers -/
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- 64-bit shift-left, or its 32-bit `W` variant for i32 -/
  let (rewriter, mulOp) ←
    if type'.bitwidth = 32 then
      rewriter.createOp (.riscv .sllw) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
    else
      rewriter.createOp (.riscv .sll) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[mulOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- llvm.shl -> riscv.srl -/
def lshr (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchLshr op rewriter.ctx | return rewriter
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! rewriter.ctx.raw).val | return rewriter
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return rewriter
  let .integerType rtype := (rhs.getType! rewriter.ctx.raw).val | return rewriter
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let .integerType type' := type.val | rewriter
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return rewriter
  /- First, cast the operands to registers -/
  let (rewriter, lcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, rcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- 64-bit logical shift-right, or its 32-bit `W` variant for i32 -/
  let (rewriter, mulOp) ←
    if type'.bitwidth = 32 then
      rewriter.createOp (.riscv .srlw) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
    else
      rewriter.createOp (.riscv .srl) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast back result for type consistency-/
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[mulOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- llvm.load -> riscv.ld -/
def load (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (ptr, _) := matchLoad op rewriter.ctx | return rewriter
  /- only support `i64` (the loaded value type) -/
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let .integerType type' := type.val | return rewriter
  if type'.bitwidth ≠ 64 then return rewriter
  /- cast ptr (!llvm.ptr) -> register -/
  let (rewriter, pcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[ptr]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- `riscv.ld` with offset zero -/
  let zero := RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64))
  let (rewriter, ldOp) ← rewriter.createOp (.riscv .ld) #[RegisterType.mk] #[pcastOp.getResult 0]
      #[] #[] zero (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[ldOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/-- llvm.store -> riscv.sd -/
def store (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (arg, ptr, _) := matchStore op rewriter.ctx | return rewriter
  /- only support `i64` (the stored value type) -/
  let type := arg.getType! rewriter.ctx.raw
  let .integerType type' := type.val | return rewriter
  if type'.bitwidth ≠ 64 then return rewriter
  /- cast ptr (!llvm.ptr) -> register -/
  let (rewriter, pcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[ptr]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- cast value (i64) -> register -/
  let (rewriter, valcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[arg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- `riscv.sd` with offset zero: operands are (addr, val), no results -/
  let zero := RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64))
  let (rewriter, sdOp) ← rewriter.createOp (.riscv .sd) #[] #[pcastOp.getResult 0, valcastOp.getResult 0]
      #[] #[] zero (some $ .before op) sorry (by simp) (by simp) sorry
  rewriter.replaceOp op sdOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/--
  Lower a single-dynamic-index `llvm.getelementptr` computing `ptr + idx * scale`,
  where `scale` is the byte size of the element type.
-/
def getelementptr (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (ptr, idx, properties) := matchGetelementptr op rewriter.ctx | return rewriter
  /- Bail unless it's a single dynamic index with no trailing constant indices. -/
  if properties.rawConstantIndices.values ≠ #[(-2147483648 : Int)] then return rewriter
  /- The index must be `i64`. -/
  let .integerType itype := (idx.getType! rewriter.ctx.raw).val | return rewriter
  if itype.bitwidth ≠ 64 then return rewriter
  let some scale := Attribute.sizeOfType properties.elem_type.val | return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let (rewriter, pcastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[ptr]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, icastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[idx]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let pReg := pcastOp.getResult 0
  let iReg := icastOp.getResult 0
  let (rewriter, retOp) ← match scale with
    | 1 =>
      /- ptr + idx -/
      rewriter.createOp (.riscv .add) #[RegisterType.mk] #[pReg, iReg]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
    | 2 =>
      /- (idx << 1) + ptr -/
      rewriter.createOp (.riscv .sh1add) #[RegisterType.mk] #[iReg, pReg]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
    | 4 =>
      /- (idx << 2) + ptr -/
      rewriter.createOp (.riscv .sh2add) #[RegisterType.mk] #[iReg, pReg]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
    | 8 =>
      /- (idx << 3) + ptr -/
      rewriter.createOp (.riscv .sh3add) #[RegisterType.mk] #[iReg, pReg]
        #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
    | _ =>
      if scale &&& (scale - 1) == 0 then
        /- scale is a power of two: ptr + (idx << log2 scale) -/
        let k := RISCVImmediateProperties.mk (IntegerAttr.mk (Nat.log2 scale) (IntegerType.mk 64))
        let (rewriter, slliOp) ← rewriter.createOp (.riscv .slli) #[RegisterType.mk] #[iReg]
          #[] #[] k (some $ .before op) sorry (by simp) (by simp) sorry
        rewriter.createOp (.riscv .add) #[RegisterType.mk] #[pReg, slliOp.getResult 0]
          #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
      else
        /- arbitrary scale: ptr + idx * scale -/
        let s := RISCVImmediateProperties.mk (IntegerAttr.mk scale (IntegerType.mk 64))
        let (rewriter, liOp) ← rewriter.createOp (.riscv .li) #[RegisterType.mk] #[]
          #[] #[] s (some $ .before op) sorry (by simp) (by simp) sorry
        let (rewriter, mulOp) ← rewriter.createOp (.riscv .mul) #[RegisterType.mk] #[iReg, liOp.getResult 0]
          #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
        rewriter.createOp (.riscv .add) #[RegisterType.mk] #[pReg, mulOp.getResult 0]
          #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Cast the resulting register back to `!llvm.ptr`. -/
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[retOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry sorry sorry

/-! ## Zicond branchless `select` lowering

  The Zicond extension lowers `llvm.select` branchlessly (mirroring LLVM's
  SelectionDAG lowering of `ISD::SELECT` when `Zicond` is available):
  ```
    (select c, t, 0) -> (czero.eqz t, c)
    (select c, 0, f) -> (czero.nez f, c)
    (select c, t, f) -> (or (czero.eqz t, c), (czero.nez f, c))
  ```
  The single-instruction zero-arm cases take priority over the general form;
  the greedy driver tries patterns in array order, so `selectCzeroeqz` and
  `selectCzeronez` are registered before `selectGeneral`.
-/

set_option warn.sorry false in
/--
  `select c t 0` -> `riscv.czeroeqz t c`.
-/
def selectCzeroeqz (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, tval, fval) := matchSelect op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let some _ := matchConstantZero fval rewriter.ctx | return rewriter
  let (rewriter, tReg) ← castToReg rewriter op tval
  let (rewriter, condReg) ← castToReg rewriter op cond
  let (rewriter, czOp) ← rewriter.createOp (.riscv .czeroeqz) #[RegisterType.mk] #[tReg, condReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (czOp.getResult 0)

set_option warn.sorry false in
/--
  `select c 0 f` -> `riscv.czeronez f c`.
-/
def selectCzeronez (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, tval, fval) := matchSelect op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let some _ := matchConstantZero tval rewriter.ctx | return rewriter
  let (rewriter, fReg) ← castToReg rewriter op fval
  let (rewriter, condReg) ← castToReg rewriter op cond
  let (rewriter, czOp) ← rewriter.createOp (.riscv .czeronez) #[RegisterType.mk] #[fReg, condReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (czOp.getResult 0)

set_option warn.sorry false in
/--
  General branchless select:
  `select c t f` -> `or (czero.eqz t c) (czero.nez f c)`.
-/
def selectGeneral (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (cond, tval, fval) := matchSelect op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let (rewriter, tReg) ← castToReg rewriter op tval
  let (rewriter, fReg) ← castToReg rewriter op fval
  let (rewriter, condReg) ← castToReg rewriter op cond
  let (rewriter, eqzOp) ← rewriter.createOp (.riscv .czeroeqz) #[RegisterType.mk] #[tReg, condReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, nezOp) ← rewriter.createOp (.riscv .czeronez) #[RegisterType.mk] #[fReg, condReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  let (rewriter, orOp) ← rewriter.createOp (.riscv .or) #[RegisterType.mk]
      #[eqzOp.getResult 0, nezOp.getResult 0]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (orOp.getResult 0)

/-! ## Zbb min/max and rotate intrinsics

  These mirror the simple one-to-one patterns in LLVM's RISC-V backend
  (`RISCVInstrInfoZb.td`): `smin/smax/umin/umax` select to `MIN/MAX/MINU/MAXU`,
  and a funnel shift whose two data operands are identical is a rotate, which
  selects to `ROL`/`ROR`. The general (distinct-operand) funnel shift needs a
  multi-instruction expansion and is intentionally left unselected.
-/

set_option warn.sorry false in
/-- llvm.intr.smax -> riscv.max -/
def smax (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs) := matchSmax op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let (rewriter, lReg) ← castToReg rewriter op lhs
  let (rewriter, rReg) ← castToReg rewriter op rhs
  let (rewriter, maxOp) ← rewriter.createOp (.riscv .max) #[RegisterType.mk] #[lReg, rReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (maxOp.getResult 0)

set_option warn.sorry false in
/-- llvm.intr.smin -> riscv.min -/
def smin (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs) := matchSmin op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let (rewriter, lReg) ← castToReg rewriter op lhs
  let (rewriter, rReg) ← castToReg rewriter op rhs
  let (rewriter, minOp) ← rewriter.createOp (.riscv .min) #[RegisterType.mk] #[lReg, rReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (minOp.getResult 0)

set_option warn.sorry false in
/-- llvm.intr.umax -> riscv.maxu -/
def umax (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs) := matchUmax op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let (rewriter, lReg) ← castToReg rewriter op lhs
  let (rewriter, rReg) ← castToReg rewriter op rhs
  let (rewriter, maxuOp) ← rewriter.createOp (.riscv .maxu) #[RegisterType.mk] #[lReg, rReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (maxuOp.getResult 0)

set_option warn.sorry false in
/-- llvm.intr.umin -> riscv.minu -/
def umin (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs) := matchUmin op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let (rewriter, lReg) ← castToReg rewriter op lhs
  let (rewriter, rReg) ← castToReg rewriter op rhs
  let (rewriter, minuOp) ← rewriter.createOp (.riscv .minu) #[RegisterType.mk] #[lReg, rReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (minuOp.getResult 0)

set_option warn.sorry false in
/-- llvm.intr.fshl with identical data operands is a rotate-left: -> riscv.rol.
    The general (distinct-operand) funnel shift is left unselected. -/
def fshl (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (a, b, amt) := matchFshl op rewriter.ctx | return rewriter
  if a ≠ b then return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let (rewriter, valReg) ← castToReg rewriter op a
  let (rewriter, amtReg) ← castToReg rewriter op amt
  let (rewriter, rolOp) ← rewriter.createOp (.riscv .rol) #[RegisterType.mk] #[valReg, amtReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (rolOp.getResult 0)

set_option warn.sorry false in
/-- llvm.intr.fshr with identical data operands is a rotate-right: -> riscv.ror.
    The general (distinct-operand) funnel shift is left unselected. -/
def fshr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (a, b, amt) := matchFshr op rewriter.ctx | return rewriter
  if a ≠ b then return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let (rewriter, valReg) ← castToReg rewriter op a
  let (rewriter, amtReg) ← castToReg rewriter op amt
  let (rewriter, rorOp) ← rewriter.createOp (.riscv .ror) #[RegisterType.mk] #[valReg, amtReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (rorOp.getResult 0)

set_option warn.sorry false in
/-- llvm.intr.fshr with identical data operands and a constant shift amount is a
    constant rotate-right: -> riscv.rori (mirrors `PatGprImm<rotr, RORI>`). -/
def fshrConst (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (a, b, amt) := matchFshr op rewriter.ctx | return rewriter
  if a ≠ b then return rewriter
  let some amtAttr := matchConstantIntVal amt rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  /- The funnel-shift amount is taken modulo the bit width. -/
  let sh : Int := ((amtAttr.value % 64) + 64) % 64
  let (rewriter, valReg) ← castToReg rewriter op a
  let imm := RISCVImmediateProperties.mk (IntegerAttr.mk sh (IntegerType.mk 64))
  let (rewriter, roriOp) ← rewriter.createOp (.riscv .rori) #[RegisterType.mk] #[valReg]
      #[] #[] imm (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (roriOp.getResult 0)

set_option warn.sorry false in
/-- llvm.intr.fshl with identical data operands and a constant shift amount is a
    constant rotate-left. There is no `roli`, so (like LLVM) it lowers to
    `riscv.rori` with the negated immediate `(64 - amt) mod 64`. -/
def fshlConst (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (a, b, amt) := matchFshl op rewriter.ctx | return rewriter
  if a ≠ b then return rewriter
  let some amtAttr := matchConstantIntVal amt rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  /- rotate-left by `sh` == rotate-right by `64 - sh` (mod 64). -/
  let sh : Int := ((amtAttr.value % 64) + 64) % 64
  let imm : Int := (64 - sh) % 64
  let (rewriter, valReg) ← castToReg rewriter op a
  let immProps := RISCVImmediateProperties.mk (IntegerAttr.mk imm (IntegerType.mk 64))
  let (rewriter, roriOp) ← rewriter.createOp (.riscv .rori) #[RegisterType.mk] #[valReg]
      #[] #[] immProps (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (roriOp.getResult 0)


set_option warn.sorry false in
/-- llvm.mlir.poison -> riscv.li 0 -/
def poisonConst (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some _ := matchPoison op rewriter.ctx | return rewriter
  let imm := RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64))
  let (rewriter, liOp) ← rewriter.createOp (.riscv .li) #[RegisterType.mk] #[]
      #[] #[] imm (some $ .before op) (by simp) (by simp) (by simp) sorry
  replaceWithReg rewriter op (liOp.getResult 0)

set_option warn.sorry false in
/-- llvm.freeze arg : Int w ->
  unrealized_conversion_cast (unrealized_conversion_cast arg : Int w -> Reg) : Reg -> Int w -/
def freeze (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some operand := matchFreeze op rewriter.ctx | return rewriter
  let .integerType opType := (operand.getType! rewriter.ctx.raw).val | return rewriter
  let type := ((op.getResult 0).get! rewriter.ctx.raw).type
  let .integerType retType := type.val | rewriter
  if opType.bitwidth ≠ 64 ∨ retType.bitwidth ≠ 64 then return rewriter
  /- First, cast the operand to registers -/
  let (rewriter, opCastOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
  /- Then, cast register to expected output width. -/
  let (rewriter, castOp) ← rewriter.createOp (.builtin .unrealized_conversion_cast) #[type] #[opCastOp.getResult 0]
      #[] #[] () (some $ .before op) (by sorry) (by simp) (by simp) sorry
  rewriter.replaceOp op castOp sorry sorry sorry sorry sorry

/-! # Pass implementation -/

def ISelPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  /- Early loop: multi-instruction fusion patterns that must run before the
     per-op lowerings consume their operands. -/
  /- Main loop: the existing per-op lowerings. -/
  let pattern := RewritePattern.GreedyRewritePattern #[selectCzeroeqz, selectCzeronez, selectGeneral, ctlz, cttz, ctpop, bswap, bitreverse, constant, add, and, ashr, icmp, or, xor, mul,
    sdiv, udiv, srem, urem, sext, zext, trunc, shl, lshr, sub, load, getelementptr, store,
    smax, smin, umax, umin, fshlConst, fshrConst, fshl, fshr, poisonConst, freeze]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def IselRISCV64 : Pass OpCode :=
  { name := "isel-riscv64"
    description :=
      "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := ISelPass.impl }
