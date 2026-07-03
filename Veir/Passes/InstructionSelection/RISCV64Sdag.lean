import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Passes.InstructionSelection.Common

namespace Veir

/-!
  This file replicates instruction selection patterns from LLVM's SelectionDAG instruction selector,
  to lower LLVM IR to RISC-V assembly (64 bits).
-/

/-- The index of the single set bit of `x`, or `none` when `x` is zero or has more
    than one bit set (`u &&& (u - 1)` clears the lowest set bit; if that leaves `0`,
    there was at most one). Used for Zbs single-bit immediate selection. -/
def singleSetBit (x : BitVec 64) : Option Int :=
  let u := x.toNat
  if u == 0 || (u &&& (u - 1)) != 0 then none else some (Nat.log2 u)

/-! # SelectionDAG Lowering Patterns  -/

/--
  `and x (not y)` -> `riscv.andn x y`. The `not` may appear on either operand.
-/
def andn (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchAnd op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let some (x, y) :=
    (match matchNot rhs rewriter.ctx with
     | some y => some (lhs, y)
     | none => match matchNot lhs rewriter.ctx with
               | some y => some (rhs, y)
               | none => none) | return rewriter
  let (rewriter, xReg) ← castToReg rewriter op x
  let (rewriter, yReg) ← castToReg rewriter op y
  let (rewriter, andnOp) := rewriter.createOp! (.riscv .andn) #[RegisterType.mk] #[xReg, yReg]
      #[] #[] () (some $ .before op)
  replaceWithReg rewriter op (andnOp.getResult 0)

/--
  `or x (not y)` -> `riscv.orn x y`. The `not` may appear on either operand.
-/
def orn (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchOr op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let some (x, y) :=
    (match matchNot rhs rewriter.ctx with
     | some y => some (lhs, y)
     | none => match matchNot lhs rewriter.ctx with
               | some y => some (rhs, y)
               | none => none) | return rewriter
  let (rewriter, xReg) ← castToReg rewriter op x
  let (rewriter, yReg) ← castToReg rewriter op y
  let (rewriter, ornOp) := rewriter.createOp! (.riscv .orn) #[RegisterType.mk] #[xReg, yReg]
      #[] #[] () (some $ .before op)
  replaceWithReg rewriter op (ornOp.getResult 0)

/--
  `xor x (not y)` -> `riscv.xnor x y`. The `not` may appear on either operand.
-/
def xnor (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchXor op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let some (x, y) :=
    (match matchNot rhs rewriter.ctx with
     | some y => some (lhs, y)
     | none => match matchNot lhs rewriter.ctx with
               | some y => some (rhs, y)
               | none => none) | return rewriter
  let (rewriter, xReg) ← castToReg rewriter op x
  let (rewriter, yReg) ← castToReg rewriter op y
  let (rewriter, xnorOp) := rewriter.createOp! (.riscv .xnor) #[RegisterType.mk] #[xReg, yReg]
      #[] #[] () (some $ .before op)
  replaceWithReg rewriter op (xnorOp.getResult 0)

/--
  `sub (shl M (8 - Y)) (lshr M Y)` -> `riscv.orcb M`,
  where `M = and Z (0x0101_0101_0101_0101 <<< Y)`
-/
def orcb (rewriter: PatternRewriter OpCode) (op: OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (a, b, _) := matchSub op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
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
  let some (mo0, mo1, _) := matchAnd mOp rewriter.ctx | return rewriter
  let maskBV : BitVec 64 := BitVec.ofNat 64 0x0101010101010101 <<< y
  let isMask : ValuePtr → Bool := fun v =>
    match matchConstantIntVal v rewriter.ctx with
    | some attr => BitVec.ofInt 64 attr.value == maskBV
    | none => false
  if !(isMask mo0 || isMask mo1) then return rewriter
  let (rewriter, mReg) ← castToReg rewriter op m
  /- actual `riscv.orcb` -/
  let (rewriter, orcbOp) := rewriter.createOp! (.riscv .orcb) #[RegisterType.mk] #[mReg]
      #[] #[] () (some $ .before op)
  replaceWithReg rewriter op (orcbOp.getResult 0)



/-! ## Immediate selection

  These rules replicate LLVM's `PatGprImm` family from `RISCVInstrInfo.td` /
  `RISCVInstrInfoZb.td`: an arithmetic/logic node with a constant operand selects
  directly to the immediate form of the instruction, rather than materializing the
  constant into a register first. Each rule matches the LLVM op with an
  `llvm.mlir.constant` operand and, when the immediate fits the instruction's field,
  emits the immediate-form RISC-V op. The constant is matched only on the right
  operand, since the canonicalizer (run before isel) places it there — mirroring
  `PatGprImm`'s `(OpNode GPR:$rs1, imm)` shape. The reg-reg fallback (non-constant
  operand, or out-of-range immediate) is handled by the generic `isel-riscv64` pass.

  See the `PatGprImm`/`PatGprSimm12`/`PatGprUimmLog2XLen` classes:
  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfo.td#L1386-L1393
-/

/--
  `OP x (const imm)` -> `OPi x imm`, when the op's result has width `width` and the
  immediate lies in `[lo, hi]`. Mirrors `PatGprImm<OpNode, Inst, ImmType>`. The
  matcher's trailing properties component (`α`) is ignored.
-/
def selectBinopImm {α} (matchPair : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × α))
    (dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties) (width : Nat) (lo hi : Int)
    (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchPair op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ width then return rewriter
  let some imm := matchConstantIntVal rhs rewriter.ctx | return rewriter
  if imm.value < lo || imm.value > hi then return rewriter
  let (rewriter, xReg) ← castToReg rewriter op lhs
  let immProps := RISCVImmediateProperties.mk (IntegerAttr.mk imm.value (IntegerType.mk 64))
  let (rewriter, newOp) := rewriter.createOp! (.riscv dst) #[RegisterType.mk] #[xReg]
      #[] #[] (cast h.symm immProps) (some $ .before op)
  replaceWithReg rewriter op (newOp.getResult 0)

/-- imm12 binops on i64: `add/or/and/xor x (const ∈ [-2048, 2047])` -> `addi/ori/andi/xori`.
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfo.td#L1467-L1474 -/
def addi := selectBinopImm matchAdd .addi rfl 64 (-2048) 2047
def ori  := selectBinopImm matchOr  .ori  rfl 64 (-2048) 2047
def andi := selectBinopImm matchAnd .andi rfl 64 (-2048) 2047
def xori := selectBinopImm matchXor .xori rfl 64 (-2048) 2047

/-- uimm6 shifts on i64: `shl/lshr/ashr x (const ∈ [0, 63])` -> `slli/srli/srai`.
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfo.td#L1475-L1477 -/
def slli := selectBinopImm matchShl  .slli rfl 64 0 63
def srli := selectBinopImm matchLshr .srli rfl 64 0 63
def srai := selectBinopImm matchAshr .srai rfl 64 0 63

/-- Word `*w` immediate forms (best-effort: gated on an i32 result as a proxy for
    LLVM's `binop_allwusers`, which we lack the demanded-bits analysis to model).
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfo.td#L2249-L2254 -/
def addiw := selectBinopImm matchAdd  .addiw rfl 32 (-2048) 2047
def slliw := selectBinopImm matchShl  .slliw rfl 32 0 31
def srliw := selectBinopImm matchLshr .srliw rfl 32 0 31
def sraiw := selectBinopImm matchAshr .sraiw rfl 32 0 31

/--
  `icmp slt x (const imm12)` -> `riscv.slti x imm`;
  `icmp ult x (const imm12)` -> `riscv.sltiu x imm`.
  Mirrors `PatGprSimm12<setlt, SLTI>` / `PatGprSimm12<setult, SLTIU>`; preempts the
  general `icmp` lowering in `isel-riscv64` for these two predicate/constant cases.
  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfo.td#L1636-L1638
-/
def slti (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, prop) := matchIcmp op rewriter.ctx | return rewriter
  let .integerType lt := (lhs.getType! rewriter.ctx.raw).val | return rewriter
  if lt.bitwidth ≠ 64 then return rewriter
  let some imm := matchConstantIntVal rhs rewriter.ctx | return rewriter
  if imm.value < -2048 || imm.value > 2047 then return rewriter
  let immProps := RISCVImmediateProperties.mk (IntegerAttr.mk imm.value (IntegerType.mk 64))
  match prop.predicate with
  | .slt =>
    let (rewriter, xReg) ← castToReg rewriter op lhs
    let (rewriter, newOp) := rewriter.createOp! (.riscv .slti) #[RegisterType.mk] #[xReg]
        #[] #[] immProps (some $ .before op)
    replaceWithReg rewriter op (newOp.getResult 0)
  | .ult =>
    let (rewriter, xReg) ← castToReg rewriter op lhs
    let (rewriter, newOp) := rewriter.createOp! (.riscv .sltiu) #[RegisterType.mk] #[xReg]
        #[] #[] immProps (some $ .before op)
    replaceWithReg rewriter op (newOp.getResult 0)
  | _ => return rewriter

/-! ## Zbs single-bit immediate selection

  These mirror the Zbs mask patterns in `RISCVInstrInfoZb.td`: `bseti`/`binvi`/`bclri`
  recognize an `or`/`xor`/`and` against a constant whose (complemented, for `bclri`)
  value is a single set bit, and emit the bit *index*. The `!isInt<12>` guard matches
  the `SingleBitSetMask`/`BCLRMask` `ImmLeaf` predicates, so the plain `andi`/`ori`/`xori`
  forms win whenever the immediate already fits a signed 12-bit field.

  `BCLRMask`/`SingleBitSetMask` predicates:
  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L69-L80
  `bclri`/`bseti`/`binvi` select patterns:
  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L529-L534
-/

/--
  Single-bit immediate selection. `complement = false` for `bseti`/`binvi` (the
  immediate itself is a single set bit); `complement = true` for `bclri` (the
  *complement* of the immediate is a single set bit). The emitted immediate is the
  bit index. Only fires when the immediate does not fit a signed 12-bit field.
-/
def selectSingleBit {α} (matchPair : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × α))
    (dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties) (complement : Bool)
    (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchPair op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let some imm := matchConstantIntVal rhs rewriter.ctx | return rewriter
  /- ANDI/ORI/XORI handle the simm12 cases; only fire when the immediate doesn't fit. -/
  if !(imm.value < -2048 || imm.value > 2047) then return rewriter
  let bv := BitVec.ofInt 64 imm.value
  let some n := singleSetBit (if complement then ~~~ bv else bv) | return rewriter
  let (rewriter, xReg) ← castToReg rewriter op lhs
  let immProps := RISCVImmediateProperties.mk (IntegerAttr.mk n (IntegerType.mk 64))
  let (rewriter, newOp) := rewriter.createOp! (.riscv dst) #[RegisterType.mk] #[xReg]
      #[] #[] (cast h.symm immProps) (some $ .before op)
  replaceWithReg rewriter op (newOp.getResult 0)

def bseti := selectSingleBit matchOr  .bseti rfl false
def binvi := selectSingleBit matchXor .binvi rfl false
def bclri := selectSingleBit matchAnd .bclri rfl true

/-- `and (lshr x n) 1` -> `riscv.bexti x n` (`PatGprImm`-style single-bit extract).
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L536-L537 -/
def bexti (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchAnd op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let some one := matchConstantIntVal rhs rewriter.ctx | return rewriter
  if one.value ≠ 1 then return rewriter
  let some shrOp := getDefiningOp lhs rewriter.ctx | return rewriter
  let some (x, shamt, _) := matchLshr shrOp rewriter.ctx | return rewriter
  let some sh := matchConstantIntVal shamt rewriter.ctx | return rewriter
  if sh.value < 0 || sh.value > 63 then return rewriter
  let (rewriter, xReg) ← castToReg rewriter op x
  let immProps := RISCVImmediateProperties.mk (IntegerAttr.mk sh.value (IntegerType.mk 64))
  let (rewriter, newOp) := rewriter.createOp! (.riscv .bexti) #[RegisterType.mk] #[xReg]
      #[] #[] immProps (some $ .before op)
  replaceWithReg rewriter op (newOp.getResult 0)

/-- `fshr x x (const)` on i32 is a constant word rotate-right -> `riscv.roriw`
    (i32 analogue of `fshrConst` -> `rori`; mirrors `PatGprImm<riscv_rorw, RORIW, uimm5>`).
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L504 -/
def roriw (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (a, b, amt) := matchFshr op rewriter.ctx | return rewriter
  if a ≠ b then return rewriter
  let some amtAttr := matchConstantIntVal amt rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 32 then return rewriter
  let sh : Int := ((amtAttr.value % 32) + 32) % 32
  let (rewriter, valReg) ← castToReg rewriter op a
  let immProps := RISCVImmediateProperties.mk (IntegerAttr.mk sh (IntegerType.mk 64))
  let (rewriter, newOp) := rewriter.createOp! (.riscv .roriw) #[RegisterType.mk] #[valReg]
      #[] #[] immProps (some $ .before op)
  replaceWithReg rewriter op (newOp.getResult 0)

/-- `fshl x x (const)` on i32 is a constant word rotate-left. There is no `roliw`,
    so (like `fshlConst` at i64) it lowers to `riscv.roriw` with the negated immediate
    `(32 - amt) mod 32` (i32 analogue of `fshlConst`). -/
def roliw (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (a, b, amt) := matchFshl op rewriter.ctx | return rewriter
  if a ≠ b then return rewriter
  let some amtAttr := matchConstantIntVal amt rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 32 then return rewriter
  /- rotate-left by `sh` == rotate-right by `32 - sh` (mod 32). -/
  let sh : Int := ((amtAttr.value % 32) + 32) % 32
  let imm : Int := (32 - sh) % 32
  let (rewriter, valReg) ← castToReg rewriter op a
  let immProps := RISCVImmediateProperties.mk (IntegerAttr.mk imm (IntegerType.mk 64))
  let (rewriter, newOp) := rewriter.createOp! (.riscv .roriw) #[RegisterType.mk] #[valReg]
      #[] #[] immProps (some $ .before op)
  replaceWithReg rewriter op (newOp.getResult 0)

/-- `shl (zext i32->i64 x) (const ∈ [0,31])` -> `riscv.slliuw x shamt`
    (Zba: `(i64 (shl (and GPR, 0xFFFFFFFF), uimm5)) -> SLLI_UW`; our `zext` is the mask).
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L821-L822 -/
def slliuw (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (base, shamt, _) := matchShl op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let some sh := matchConstantIntVal shamt rewriter.ctx | return rewriter
  if sh.value < 0 || sh.value > 31 then return rewriter
  let some baseOp := getDefiningOp base rewriter.ctx | return rewriter
  let some (x, _) := matchZext baseOp rewriter.ctx | return rewriter
  let .integerType srcT := (x.getType! rewriter.ctx.raw).val | return rewriter
  if srcT.bitwidth ≠ 32 then return rewriter
  let (rewriter, xReg) ← castToReg rewriter op x
  let immProps := RISCVImmediateProperties.mk (IntegerAttr.mk sh.value (IntegerType.mk 64))
  let (rewriter, newOp) := rewriter.createOp! (.riscv .slliuw) #[RegisterType.mk] #[xReg]
      #[] #[] immProps (some $ .before op)
  replaceWithReg rewriter op (newOp.getResult 0)

/-- llvm.zext x i1 to i64 -> and x 1 -/
def zext_1 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operand, _) := matchZext op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let .integerType opType := (operand.getType! rewriter.ctx.raw).val | return rewriter
  if opType.bitwidth ≠ 1 then return rewriter
  /- First, cast the operand to registers -/
  let (rewriter, opCastOp) := rewriter.createOp! (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand]
      #[] #[] () (some $ .before op)
  let imm := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
  let (rewriter, andiOp) := rewriter.createOp! (.riscv .andi) #[RegisterType.mk] #[opCastOp.getResult 0]
      #[] #[] imm (some $ .before op)
  let (rewriter, castOp) := rewriter.createOp! (.builtin .unrealized_conversion_cast) #[t] #[andiOp.getResult 0]
      #[] #[] () (some $ .before op)
  return rewriter.replaceOp! op castOp

/-- llvm.sext x i1 to i64 -> srai (slli x 63) 1 -/
def sext_1 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operand, _) := matchSext op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let .integerType opType := (operand.getType! rewriter.ctx.raw).val | return rewriter
  if opType.bitwidth ≠ 1 then return rewriter
  /- First, cast the operand to registers -/
  let (rewriter, opCastOp) := rewriter.createOp! (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand]
      #[] #[] () (some $ .before op)
  let imm := RISCVImmediateProperties.mk (IntegerAttr.mk 63 (IntegerType.mk 64))
  let (rewriter, slliOp) := rewriter.createOp! (.riscv .slli) #[RegisterType.mk] #[opCastOp.getResult 0]
      #[] #[] imm (some $ .before op)
  let (rewriter, sraiOp) := rewriter.createOp! (.riscv .srai) #[RegisterType.mk] #[slliOp.getResult 0]
      #[] #[] imm (some $ .before op)
  let (rewriter, castOp) := rewriter.createOp! (.builtin .unrealized_conversion_cast) #[t] #[sraiOp.getResult 0]
      #[] #[] () (some $ .before op)
  return rewriter.replaceOp! op castOp

/-! ## Division by a constant power of two

  RISC-V has no divide-by-constant strength reduction in hardware, so a `udiv`/`sdiv`
  by a constant power of two is turned into shifts here. This mirrors the
  target-independent `DAGCombiner::visitUDIVLike` / `DAGCombiner::visitSDIVLike`:
  RISC-V does not override this generic lowering with something target-specific
  unless the `short-forward-branch-ialu` tuning feature is set (in which case
  `RISCVTargetLowering::BuildSDIVPow2` instead emits a branchy `cmov` form), which we
  do not model, so the sequences below are what a plain `-mtriple=riscv64` emits.
  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L5270-L5285

  The Veir target has Zicond, but that does not change this analysis:
  `BuildSDIVPow2`'s branchy form is gated purely on `short-forward-branch-ialu`
  (real conditional branches, profitable only on cores where a short forward
  branch is nearly free), not on Zicond's `czero.eqz`/`czero.nez`. Checked against
  upstream `llc`: `-mattr=+zicond` alone produces byte-identical output to no
  Zicond at all, and `-mattr=+short-forward-branch-ialu,+zicond` together still
  emits a real `bgez`/`addi` branch, never `czero`. This makes sense instruction-
  count-wise too: `czero.eqz`/`czero.nez` take only register operands (see
  `Veir.Verifier`, `verifyPlainOpCounts _ _ 2 1`), so a `czero`-based correction
  would need an extra instruction to materialize the mask `2^k - 1` into a
  register (and only fits a single `li`/`addi` when `k ≤ 11`, matching
  `BuildSDIVPow2`'s own `2**k-1 < 2048` guard) -- whereas the shift-derived
  correction below (`sign`/`corr`) gets that same mask for free, for any `k`, by
  reusing the shift already needed to read the sign bit. So a Zicond rewrite
  would be strictly more instructions, not fewer.
-/

/-- The `w`-bit unsigned magnitude of `v`, i.e. `v`'s bit pattern reduced mod `2^w`.
    Needed because a `udiv` divisor whose top bit is set is decoded as a negative
    `Int` (integer attributes carry no signedness), even though `udiv` treats the
    bit pattern as unsigned. -/
def unsignedMod (w : Nat) (v : Int) : Nat := (v % ((2 : Int) ^ w)).toNat

/-- If `m` is a nonzero power of two, return its base-2 logarithm. -/
def log2IfPow2 (m : Nat) : Option Nat :=
  if m == 0 || (m &&& (m - 1)) != 0 then none else some (Nat.log2 m)

/-- If `|v|` is a nonzero power of two, return its base-2 logarithm together with
    whether `v` is negative. Used for `sdiv`, whose divisor is signed, so `v` (as
    decoded) already carries the correct sign. Mirrors `isDivisorPowerOfTwo`.
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L5270-L5285 -/
def matchSignedPow2Divisor (v : Int) : Option (Nat × Bool) := do
  let k ← log2IfPow2 v.natAbs
  return (k, decide (v < 0))

/-- If the `w`-bit unsigned magnitude of `v` is a nonzero power of two, return its
    base-2 logarithm. Used for `udiv`. -/
def matchUnsignedPow2Divisor (w : Nat) (v : Int) : Option Nat :=
  log2IfPow2 (unsignedMod w v)

/-- `udiv x, 2^k` -> `riscv.srli x, k`. Mirrors `DAGCombiner::visitUDIVLike`'s
    `fold (udiv x, (1 << c)) -> x >>u c` (via `BuildLogBase2`).
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L5430-L5440 -/
def udivPow2 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchUdiv op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let some imm := matchConstantIntVal rhs rewriter.ctx | return rewriter
  let some k := matchUnsignedPow2Divisor 64 imm.value | return rewriter
  let (rewriter, xReg) ← castToReg rewriter op lhs
  let shamt := RISCVImmediateProperties.mk (IntegerAttr.mk k (IntegerType.mk 64))
  let (rewriter, srliOp) := rewriter.createOp! (.riscv .srli) #[RegisterType.mk] #[xReg]
      #[] #[] shamt (some $ .before op)
  replaceWithReg rewriter op (srliOp.getResult 0)

/-- `udiv x, 2^k` -> `riscv.srliw x, k`, the `i32` analogue of `udivPow2`.
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L5430-L5440 -/
def udivwPow2 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, _) := matchUdiv op rewriter.ctx | return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 32 then return rewriter
  let some imm := matchConstantIntVal rhs rewriter.ctx | return rewriter
  let some k := matchUnsignedPow2Divisor 32 imm.value | return rewriter
  let (rewriter, xReg) ← castToReg rewriter op lhs
  let shamt := RISCVImmediateProperties.mk (IntegerAttr.mk k (IntegerType.mk 64))
  let (rewriter, srliwOp) := rewriter.createOp! (.riscv .srliw) #[RegisterType.mk] #[xReg]
      #[] #[] shamt (some $ .before op)
  replaceWithReg rewriter op (srliwOp.getResult 0)

/-- `sdiv exact x, 2^k` -> `riscv.srai x, k`; when the divisor is negative, negate
    the shifted result: `sdiv exact x, -2^k` -> `riscv.sub 0, (riscv.srai x, k)`.
    Mirrors `TargetLowering::BuildExactSDIV` (a plain arithmetic shift by the
    trailing-zero count, times a ±1 "magic factor" that the surrounding combines
    fold into a no-op or a negation). `DAGCombiner::visitSDIVLike` takes this path
    instead of the general correction sequence below whenever the `exact` flag is
    set, since it is cheaper.
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L5294-L5301
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/TargetLowering.cpp#L6454-L6510 -/
def sdivPow2Exact (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, props) := matchSdiv op rewriter.ctx | return rewriter
  if ¬ props.exact then return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let some imm := matchConstantIntVal rhs rewriter.ctx | return rewriter
  let some (k, isNeg) := matchSignedPow2Divisor imm.value | return rewriter
  let (rewriter, xReg) ← castToReg rewriter op lhs
  let shamt := RISCVImmediateProperties.mk (IntegerAttr.mk k (IntegerType.mk 64))
  let (rewriter, sraiOp) := rewriter.createOp! (.riscv .srai) #[RegisterType.mk] #[xReg]
      #[] #[] shamt (some $ .before op)
  if ¬ isNeg then replaceWithReg rewriter op (sraiOp.getResult 0)
  else
    let zero := RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64))
    let (rewriter, zeroOp) := rewriter.createOp! (.riscv .li) #[RegisterType.mk] #[]
        #[] #[] zero (some $ .before op)
    let (rewriter, negOp) := rewriter.createOp! (.riscv .sub) #[RegisterType.mk]
        #[zeroOp.getResult 0, sraiOp.getResult 0] #[] #[] () (some $ .before op)
    replaceWithReg rewriter op (negOp.getResult 0)

/-- `i32` analogue of `sdivPow2Exact`: `sdiv exact x, 2^k` -> `riscv.sraiw x, k`,
    negated via `riscv.subw` when the divisor is negative.
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L5294-L5301
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/TargetLowering.cpp#L6454-L6510 -/
def sdivwPow2Exact (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, props) := matchSdiv op rewriter.ctx | return rewriter
  if ¬ props.exact then return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 32 then return rewriter
  let some imm := matchConstantIntVal rhs rewriter.ctx | return rewriter
  let some (k, isNeg) := matchSignedPow2Divisor imm.value | return rewriter
  let (rewriter, xReg) ← castToReg rewriter op lhs
  let shamt := RISCVImmediateProperties.mk (IntegerAttr.mk k (IntegerType.mk 64))
  let (rewriter, sraiwOp) := rewriter.createOp! (.riscv .sraiw) #[RegisterType.mk] #[xReg]
      #[] #[] shamt (some $ .before op)
  if ¬ isNeg then replaceWithReg rewriter op (sraiwOp.getResult 0)
  else
    let zero := RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64))
    let (rewriter, zeroOp) := rewriter.createOp! (.riscv .li) #[RegisterType.mk] #[]
        #[] #[] zero (some $ .before op)
    let (rewriter, negOp) := rewriter.createOp! (.riscv .subw) #[RegisterType.mk]
        #[zeroOp.getResult 0, sraiwOp.getResult 0] #[] #[] () (some $ .before op)
    replaceWithReg rewriter op (negOp.getResult 0)

/-- General `sdiv x, 2^k` (`exact` not set): bias negative dividends before
    shifting so truncation rounds toward zero, then negate for a negative divisor:
    ```
    sign   := riscv.srai x, 63          -- splat the sign bit
    corr   := riscv.srli sign, (64 - k) -- 2^k - 1 if x < 0, else 0
    biased := riscv.add x, corr
    q      := riscv.srai biased, k
    ```
    then `riscv.sub 0, q` when the divisor is negative. Mirrors the generic
    `sra`/`srl`/`add` sequence built by `DAGCombiner::visitSDIVLike` when the
    `exact` bit isn't set (Hacker's Delight §10-1); RISC-V's `BuildSDIVPow2` only
    replaces this with a branchy `cmov` form under `short-forward-branch-ialu`
    tuning, which we do not model, so this generic sequence is what RV64 emits by
    default.
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L5294-L5345
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVISelLowering.cpp#L27055-L27074 -/
def sdivPow2 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, props) := matchSdiv op rewriter.ctx | return rewriter
  if props.exact then return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 64 then return rewriter
  let some imm := matchConstantIntVal rhs rewriter.ctx | return rewriter
  let some (k, isNeg) := matchSignedPow2Divisor imm.value | return rewriter
  /- `k = 0` (divisor ±1) would need a shift by the full 64-bit width, which has no
     legal immediate encoding; middle-end optimizations always turn `sdiv x, ±1`
     into `x`/`-x` well before instruction selection, so this case does not arise. -/
  if k = 0 then return rewriter
  let (rewriter, xReg) ← castToReg rewriter op lhs
  let sh63 := RISCVImmediateProperties.mk (IntegerAttr.mk 63 (IntegerType.mk 64))
  let (rewriter, signOp) := rewriter.createOp! (.riscv .srai) #[RegisterType.mk] #[xReg]
      #[] #[] sh63 (some $ .before op)
  let shCorr := RISCVImmediateProperties.mk (IntegerAttr.mk (64 - k) (IntegerType.mk 64))
  let (rewriter, corrOp) := rewriter.createOp! (.riscv .srli) #[RegisterType.mk] #[signOp.getResult 0]
      #[] #[] shCorr (some $ .before op)
  let (rewriter, biasedOp) := rewriter.createOp! (.riscv .add) #[RegisterType.mk]
      #[xReg, corrOp.getResult 0] #[] #[] () (some $ .before op)
  let shQ := RISCVImmediateProperties.mk (IntegerAttr.mk k (IntegerType.mk 64))
  let (rewriter, qOp) := rewriter.createOp! (.riscv .srai) #[RegisterType.mk] #[biasedOp.getResult 0]
      #[] #[] shQ (some $ .before op)
  if ¬ isNeg then replaceWithReg rewriter op (qOp.getResult 0)
  else
    let zero := RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64))
    let (rewriter, zeroOp) := rewriter.createOp! (.riscv .li) #[RegisterType.mk] #[]
        #[] #[] zero (some $ .before op)
    let (rewriter, negOp) := rewriter.createOp! (.riscv .sub) #[RegisterType.mk]
        #[zeroOp.getResult 0, qOp.getResult 0] #[] #[] () (some $ .before op)
    replaceWithReg rewriter op (negOp.getResult 0)

/-- `i32` analogue of `sdivPow2`, using the `w`-suffixed 32-bit shift/add/sub forms
    so intermediate values stay correctly sign-extended in the 64-bit register.
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/CodeGen/SelectionDAG/DAGCombiner.cpp#L5294-L5345
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVISelLowering.cpp#L27055-L27074 -/
def sdivwPow2 (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs, props) := matchSdiv op rewriter.ctx | return rewriter
  if props.exact then return rewriter
  let .integerType t := ((op.getResult 0).get! rewriter.ctx.raw).type.val | return rewriter
  if t.bitwidth ≠ 32 then return rewriter
  let some imm := matchConstantIntVal rhs rewriter.ctx | return rewriter
  let some (k, isNeg) := matchSignedPow2Divisor imm.value | return rewriter
  if k = 0 then return rewriter
  let (rewriter, xReg) ← castToReg rewriter op lhs
  let sh31 := RISCVImmediateProperties.mk (IntegerAttr.mk 31 (IntegerType.mk 64))
  let (rewriter, signOp) := rewriter.createOp! (.riscv .sraiw) #[RegisterType.mk] #[xReg]
      #[] #[] sh31 (some $ .before op)
  let shCorr := RISCVImmediateProperties.mk (IntegerAttr.mk (32 - k) (IntegerType.mk 64))
  let (rewriter, corrOp) := rewriter.createOp! (.riscv .srliw) #[RegisterType.mk] #[signOp.getResult 0]
      #[] #[] shCorr (some $ .before op)
  let (rewriter, biasedOp) := rewriter.createOp! (.riscv .addw) #[RegisterType.mk]
      #[xReg, corrOp.getResult 0] #[] #[] () (some $ .before op)
  let shQ := RISCVImmediateProperties.mk (IntegerAttr.mk k (IntegerType.mk 64))
  let (rewriter, qOp) := rewriter.createOp! (.riscv .sraiw) #[RegisterType.mk] #[biasedOp.getResult 0]
      #[] #[] shQ (some $ .before op)
  if ¬ isNeg then replaceWithReg rewriter op (qOp.getResult 0)
  else
    let zero := RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64))
    let (rewriter, zeroOp) := rewriter.createOp! (.riscv .li) #[RegisterType.mk] #[]
        #[] #[] zero (some $ .before op)
    let (rewriter, negOp) := rewriter.createOp! (.riscv .subw) #[RegisterType.mk]
        #[zeroOp.getResult 0, qOp.getResult 0] #[] #[] () (some $ .before op)
    replaceWithReg rewriter op (negOp.getResult 0)

/-! # Pass implementation -/

def IselSDAG.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  /- Order matters where patterns overlap: the more specific Zbs/Zba rules (`bexti`,
     `slliuw`) must precede the generic `andi`/`slli` forms they would otherwise be
     shadowed by. The `bseti`/`bclri`/`binvi` rules are mutually exclusive with
     `ori`/`andi`/`xori` via their `!isInt<12>` guard, so their order is immaterial.
     `sdivPow2Exact`/`sdivwPow2Exact` are listed before `sdivPow2`/`sdivwPow2` to
     mirror the priority LLVM gives the `exact`-flag fast path, though both sides
     already guard on `exact`, so the two pairs are in fact mutually exclusive. -/
  let pattern := RewritePattern.GreedyRewritePattern #[andn, orn, xnor, orcb,
    bexti, bseti, bclri, binvi, slliuw,
    addi, ori, andi, xori, slli, srli, srai, slti,
    addiw, slliw, srliw, sraiw, roriw, roliw, zext_1, sext_1,
    udivPow2, udivwPow2, sdivPow2Exact, sdivwPow2Exact, sdivPow2, sdivwPow2]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying SDAG patterns"
  | some ctx => pure ctx

public def IselSDAG : Pass OpCode :=
  { name := "isel-sdag-riscv64"
    description :=
      "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := IselSDAG.impl }
