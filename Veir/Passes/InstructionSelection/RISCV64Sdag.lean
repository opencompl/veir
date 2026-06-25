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

set_option warn.sorry false in
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
  let (rewriter, orcbOp) ← rewriter.createOp (.riscv .orcb) #[RegisterType.mk] #[mReg]
      #[] #[] () (some $ .before op) sorry (by simp) (by simp) sorry
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

set_option warn.sorry false in
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
  let (rewriter, newOp) ← rewriter.createOp (.riscv dst) #[RegisterType.mk] #[xReg]
      #[] #[] (cast h.symm immProps) (some $ .before op) sorry (by simp) (by simp) sorry
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

set_option warn.sorry false in
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
    let (rewriter, newOp) ← rewriter.createOp (.riscv .slti) #[RegisterType.mk] #[xReg]
        #[] #[] immProps (some $ .before op) sorry (by simp) (by simp) sorry
    replaceWithReg rewriter op (newOp.getResult 0)
  | .ult =>
    let (rewriter, xReg) ← castToReg rewriter op lhs
    let (rewriter, newOp) ← rewriter.createOp (.riscv .sltiu) #[RegisterType.mk] #[xReg]
        #[] #[] immProps (some $ .before op) sorry (by simp) (by simp) sorry
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

set_option warn.sorry false in
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
  let (rewriter, newOp) ← rewriter.createOp (.riscv dst) #[RegisterType.mk] #[xReg]
      #[] #[] (cast h.symm immProps) (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (newOp.getResult 0)

def bseti := selectSingleBit matchOr  .bseti rfl false
def binvi := selectSingleBit matchXor .binvi rfl false
def bclri := selectSingleBit matchAnd .bclri rfl true

set_option warn.sorry false in
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
  let (rewriter, newOp) ← rewriter.createOp (.riscv .bexti) #[RegisterType.mk] #[xReg]
      #[] #[] immProps (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (newOp.getResult 0)

set_option warn.sorry false in
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
  let (rewriter, newOp) ← rewriter.createOp (.riscv .roriw) #[RegisterType.mk] #[valReg]
      #[] #[] immProps (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (newOp.getResult 0)

set_option warn.sorry false in
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
  let (rewriter, newOp) ← rewriter.createOp (.riscv .roriw) #[RegisterType.mk] #[valReg]
      #[] #[] immProps (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (newOp.getResult 0)

set_option warn.sorry false in
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
  let (rewriter, newOp) ← rewriter.createOp (.riscv .slliuw) #[RegisterType.mk] #[xReg]
      #[] #[] immProps (some $ .before op) sorry (by simp) (by simp) sorry
  replaceWithReg rewriter op (newOp.getResult 0)

/-! # Pass implementation -/

def IselSDAG.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  /- Order matters where patterns overlap: the more specific Zbs/Zba rules (`bexti`,
     `slliuw`) must precede the generic `andi`/`slli` forms they would otherwise be
     shadowed by. The `bseti`/`bclri`/`binvi` rules are mutually exclusive with
     `ori`/`andi`/`xori` via their `!isInt<12>` guard, so their order is immaterial. -/
  let pattern := RewritePattern.GreedyRewritePattern #[andn, orn, xnor, orcb,
    bexti, bseti, bclri, binvi, slliuw,
    addi, ori, andi, xori, slli, srli, srai, slti,
    addiw, slliw, srliw, sraiw, roriw, roliw]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying SDAG patterns"
  | some ctx => pure ctx

public def IselSDAG : Pass OpCode :=
  { name := "isel-sdag-riscv64"
    description :=
      "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := IselSDAG.impl }
