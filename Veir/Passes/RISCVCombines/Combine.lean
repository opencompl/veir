import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.RISCVMatching

namespace Veir.RISCV

/-!
  This file replicates LLVM's pre- and post-legalization GlobalISel combines.
-/

/-! # Lowering Patterns -/

set_option warn.sorry false in
/-- riscv.add x 0 -> x -/
def right_identity_zero_add (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs) := matchAdd op rewriter.ctx | return rewriter
  let some cst := matchLi rhs rewriter.ctx | return rewriter
  if cst.value.value ≠ 0 then return rewriter
  let rewriter := rewriter.replaceValue (op.getResult 0) lhs sorry sorry sorry
  rewriter.eraseOp op sorry sorry sorry

set_option warn.sorry false in
/--
  Introduce commutative imm12 instructions:
  riscv.OP x (riscv.li imm) -> riscv.OPi x imm
  riscv.OP (riscv.li imm) x -> riscv.OPi x imm
  Only when `imm` fits into a signed 12-bit immediate field.
  Covers: add→addi, or→ori, and→andi, xor→xori, addw→addiw.
-/
def fold_commutative_binop_li (src dst : Riscv)
    (h : Riscv.propertiesOf dst = RISCVImmediateProperties) :
    LocalRewritePattern OpCode := fun ctx op =>
  match matchRiscvBinop src op ctx with
  | none => some (ctx, none)
  | some (lhs, rhs) =>
    match (Prod.mk lhs <$> matchLi rhs ctx) <|> (Prod.mk rhs <$> matchLi lhs ctx) with
    | none => some (ctx, none)
    | some (reg, imm) =>
      if imm.value.value < -2048 || imm.value.value > 2047 then some (ctx, none)
      else do
        let (ctx, newOp) ← WfRewriter.createOp ctx (.riscv dst) #[RegisterType.mk] #[reg]
            #[] #[] (cast h.symm imm) none sorry
        return (ctx, some (#[newOp], #[newOp.getResult 0]))

def fold_add_li_to_addi   := fold_commutative_binop_li .add  .addi  rfl
def fold_or_li_to_ori     := fold_commutative_binop_li .or   .ori   rfl
def fold_and_li_to_andi   := fold_commutative_binop_li .and  .andi  rfl
def fold_xor_li_to_xori   := fold_commutative_binop_li .xor  .xori  rfl
def fold_addw_li_to_addiw := fold_commutative_binop_li .addw .addiw rfl

set_option warn.sorry false in
/--
  riscv.src rs1 (riscv.li imm) -> riscv.dst rs1 imm, only when the immediate lies
  in `[lo, hi]`. Shifts, rotates, and single-bit operations are not commutative,
  so the immediate is only matched on the second operand.
-/
def fold_binop_li (src dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties)
    (lo hi : Int) : LocalRewritePattern OpCode := fun ctx op =>
  match matchRiscvBinop src op ctx with
  | none => some (ctx, none)
  | some (reg, rhs) =>
    match matchLi rhs ctx with
    | none => some (ctx, none)
    | some imm =>
      if imm.value.value < lo || imm.value.value > hi then some (ctx, none)
      else do
        let (ctx, newOp) ← WfRewriter.createOp ctx (.riscv dst) #[RegisterType.mk] #[reg]
            #[] #[] (cast h.symm imm) none sorry
        return (ctx, some (#[newOp], #[newOp.getResult 0]))

/-- imm5 word shifts/rotates: `src rs1 (li imm) -> dst rs1 imm` for `imm ∈ [0,31]`. -/
def fold_shift5_li (src dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties) :
    LocalRewritePattern OpCode := fold_binop_li src dst h 0 31

/-- imm6 shifts/rotates and single-bit operations: `imm ∈ [0,63]`. -/
def fold_shift6_li (src dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties) :
    LocalRewritePattern OpCode := fold_binop_li src dst h 0 63

/-- Non-commutative signed imm12 operations: `imm ∈ [-2048, 2047]`. -/
def fold_imm12_li (src dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties) :
    LocalRewritePattern OpCode := fold_binop_li src dst h (-2048) 2047

def fold_sllw_li_to_slliw := fold_shift5_li .sllw .slliw rfl
def fold_srlw_li_to_srliw := fold_shift5_li .srlw .srliw rfl
def fold_sraw_li_to_sraiw := fold_shift5_li .sraw .sraiw rfl
def fold_rorw_li_to_roriw := fold_shift5_li .rorw .roriw rfl

def fold_sll_li_to_slli   := fold_shift6_li .sll  .slli  rfl
def fold_srl_li_to_srli   := fold_shift6_li .srl  .srli  rfl
def fold_sra_li_to_srai   := fold_shift6_li .sra  .srai  rfl
def fold_ror_li_to_rori   := fold_shift6_li .ror  .rori  rfl
def fold_bclr_li_to_bclri := fold_shift6_li .bclr .bclri rfl
def fold_bext_li_to_bexti := fold_shift6_li .bext .bexti rfl
def fold_binv_li_to_binvi := fold_shift6_li .binv .binvi rfl
def fold_bset_li_to_bseti := fold_shift6_li .bset .bseti rfl

def fold_slt_li_to_slti   := fold_imm12_li .slt  .slti  rfl
def fold_sltu_li_to_sltiu := fold_imm12_li .sltu .sltiu rfl

set_option warn.sorry false in
/-- riscv.slli (riscv.zextw x) shamt -> riscv.slliuw x shamt -/
def fold_zextw_slli_to_slliuw : LocalRewritePattern OpCode := fun ctx op =>
  match matchOp op ctx (.riscv .slli) 1 with
  | none => some (ctx, none)
  | some (operands, shamt) =>
    match matchZextw operands[0]! ctx with
    | none => some (ctx, none)
    | some x => do
        let (ctx, newOp) ← WfRewriter.createOp ctx (.riscv .slliuw) #[RegisterType.mk] #[x]
            #[] #[] shamt none sorry
        return (ctx, some (#[newOp], #[newOp.getResult 0]))

/-! # Pass implementation -/

def Combine.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[right_identity_zero_add,
      RewritePattern.fromLocalRewrite fold_add_li_to_addi,
      RewritePattern.fromLocalRewrite fold_or_li_to_ori,
      RewritePattern.fromLocalRewrite fold_and_li_to_andi,
      RewritePattern.fromLocalRewrite fold_xor_li_to_xori,
      RewritePattern.fromLocalRewrite fold_addw_li_to_addiw,
      RewritePattern.fromLocalRewrite fold_sllw_li_to_slliw,
      RewritePattern.fromLocalRewrite fold_srlw_li_to_srliw,
      RewritePattern.fromLocalRewrite fold_sraw_li_to_sraiw,
      RewritePattern.fromLocalRewrite fold_rorw_li_to_roriw,
      RewritePattern.fromLocalRewrite fold_sll_li_to_slli,
      RewritePattern.fromLocalRewrite fold_srl_li_to_srli,
      RewritePattern.fromLocalRewrite fold_sra_li_to_srai,
      RewritePattern.fromLocalRewrite fold_ror_li_to_rori,
      RewritePattern.fromLocalRewrite fold_bclr_li_to_bclri,
      RewritePattern.fromLocalRewrite fold_bext_li_to_bexti,
      RewritePattern.fromLocalRewrite fold_binv_li_to_binvi,
      RewritePattern.fromLocalRewrite fold_bset_li_to_bseti,
      RewritePattern.fromLocalRewrite fold_slt_li_to_slti,
      RewritePattern.fromLocalRewrite fold_sltu_li_to_sltiu,
      RewritePattern.fromLocalRewrite fold_zextw_slli_to_slliuw]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def Combine : Pass OpCode :=
  { name := "riscv-combine"
    description := "GlobalISel RISCV combines"
    run := Combine.impl }
