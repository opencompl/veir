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
  riscv.add x (riscv.li imm) -> riscv.addi x imm
  riscv.add (riscv.li imm) x -> riscv.addi x imm
  But only when `imm` fits into a signed 12-bit immediate field.
-/
def fold_add_li_to_addi (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (lhs, rhs) := matchAdd op rewriter.ctx | return rewriter
  let some (reg, imm) :=
      (Prod.mk lhs <$> matchLi rhs rewriter.ctx) <|>
      (Prod.mk rhs <$> matchLi lhs rewriter.ctx)
    | return rewriter
  if imm.value.value < -2048 || imm.value.value > 2047 then return rewriter
  let (rewriter, addiOp) ← rewriter.createOp (.riscv .addi) #[RegisterType.mk] #[reg]
      #[] #[] imm (some $ .before op) sorry (by simp) (by simp) sorry
  rewriter.replaceOp op addiOp sorry sorry sorry sorry sorry

set_option warn.sorry false in
/--
  Introduce shift-by-immediate instructions with a 5-bit shift amount:
  riscv.OP x (riscv.li imm) -> riscv.OPi x imm
  Only when `imm` fits into an unsigned 5-bit shift-amount field (0..31).
  Unlike the commutative integer ops, shifts/rotates are not commutative,
  so the immediate is only matched on the second operand (the shift amount).
  Covers: sllw→slliw, srlw→srliw, sraw→sraiw, rorw→roriw.
-/
def fold_shift5_li (src dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties)
    (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (reg, rhs) := matchRiscvBinop src op rewriter.ctx | return rewriter
  let some imm := matchLi rhs rewriter.ctx | return rewriter
  if imm.value.value < 0 || imm.value.value > 31 then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.riscv dst) #[RegisterType.mk] #[reg]
      #[] #[] (cast h.symm imm) (some $ .before op) sorry (by simp) (by simp) sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

def fold_sllw_li_to_slliw := fold_shift5_li .sllw .slliw rfl
def fold_srlw_li_to_srliw := fold_shift5_li .srlw .srliw rfl
def fold_sraw_li_to_sraiw := fold_shift5_li .sraw .sraiw rfl
def fold_rorw_li_to_roriw := fold_shift5_li .rorw .roriw rfl

set_option warn.sorry false in
/--
  Introduce immediate instructions with a 6-bit shift-amount / bit-index field:
  riscv.OP x (riscv.li imm) -> riscv.OPi x imm
  Only when `imm` fits into an unsigned 6-bit field (0..63).
  These ops are not commutative, so the immediate is only matched on the second
  operand (the shift amount / bit index).
  Covers shifts/rotates: sll→slli, srl→srli, sra→srai, ror→rori; and the
  single-bit ops: bclr→bclri, bext→bexti, binv→binvi, bset→bseti.
-/
def fold_shift6_li (src dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties)
    (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some (reg, rhs) := matchRiscvBinop src op rewriter.ctx | return rewriter
  let some imm := matchLi rhs rewriter.ctx | return rewriter
  if imm.value.value < 0 || imm.value.value > 63 then return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.riscv dst) #[RegisterType.mk] #[reg]
      #[] #[] (cast h.symm imm) (some $ .before op) sorry (by simp) (by simp) sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

def fold_sll_li_to_slli   := fold_shift6_li .sll  .slli  rfl
def fold_srl_li_to_srli   := fold_shift6_li .srl  .srli  rfl
def fold_sra_li_to_srai   := fold_shift6_li .sra  .srai  rfl
def fold_ror_li_to_rori   := fold_shift6_li .ror  .rori  rfl
def fold_bclr_li_to_bclri := fold_shift6_li .bclr .bclri rfl
def fold_bext_li_to_bexti := fold_shift6_li .bext .bexti rfl
def fold_binv_li_to_binvi := fold_shift6_li .binv .binvi rfl
def fold_bset_li_to_bseti := fold_shift6_li .bset .bseti rfl

set_option warn.sorry false in
/--
  Contract a zero-extend-word feeding a shift-left-immediate into slli.uw:
  riscv.slli (riscv.zextw x) shamt -> riscv.slliuw x shamt
  Both compute `zeroExtend64(low32(x)) <<< shamt`, so this is an exact rewrite.
  `slli` and `slliuw` share the same unsigned 6-bit shift-amount field, so the
  immediate is already in range and is carried over unchanged.
-/
def fold_zextw_slli_to_slliuw (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some (operands, shamt) := matchOp op rewriter.ctx (.riscv .slli) 1 | return rewriter
  let some x := matchZextw operands[0]! rewriter.ctx | return rewriter
  let (rewriter, newOp) ← rewriter.createOp (.riscv .slliuw) #[RegisterType.mk] #[x]
      #[] #[] shamt (some $ .before op) sorry (by simp) (by simp) sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! # Pass implementation -/

def Combine.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[right_identity_zero_add,
      fold_add_li_to_addi, fold_sllw_li_to_slliw, fold_srlw_li_to_srliw,
      fold_sraw_li_to_sraiw, fold_rorw_li_to_roriw,
      fold_sll_li_to_slli, fold_srl_li_to_srli, fold_sra_li_to_srai,
      fold_ror_li_to_rori, fold_bclr_li_to_bclri, fold_bext_li_to_bexti,
      fold_binv_li_to_binvi, fold_bset_li_to_bseti, fold_zextw_slli_to_slliuw]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def Combine : Pass OpCode :=
  { name := "riscv-combine"
    description := "GlobalISel RISCV combines"
    run := Combine.impl }
