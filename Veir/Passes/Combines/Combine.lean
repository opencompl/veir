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

/--
  Introduce a non-commutative immediate instruction, written as a parameterized
  `LocalRewritePattern` so it can be connected to the
  `LocalRewritePattern.PreservesSemantics` framework.

  `riscv.src rs1 (riscv.li imm) -> riscv.dst rs1 imm`, only when the immediate
  lies in `[lo, hi]`. Shifts/rotates/single-bit ops are not commutative, so the
  immediate is only matched on the second operand. `dst`'s properties must be
  `RISCVImmediateProperties` (proof `h`), used to carry the matched immediate over.

  The `match hbinop : … with` binds the match equation so that
  `matchRiscvBinop_reg_inBounds` discharges `createOp`'s operand-in-bounds
  obligation — no `sorry`. The generic `RewritePattern.fromLocalRewrite` driver
  performs the insertion, result replacement, and erasure.

  The shift-amount/bit-index width is just the `[lo, hi]` range, so the imm5 and
  imm6 families are the same rewrite at different bounds (`fold_shift5_li`,
  `fold_shift6_li` below).
-/
def fold_binop_li (src dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties)
    (lo hi : Int) : LocalRewritePattern OpCode := fun ctx op =>
  match hbinop : matchRiscvBinop src op ctx with
  | none => some (ctx, none)
  | some (reg, rhs) =>
    match matchLi rhs ctx with
    | none => some (ctx, none)
    | some imm =>
      if imm.value.value < lo || imm.value.value > hi then some (ctx, none)
      else do
        let (ctx, newOp) ← WfRewriter.createOp ctx (.riscv dst) #[RegisterType.mk] #[reg]
            #[] #[] (cast h.symm imm) none
            (by intro oper hmem
                simp only [Array.mem_singleton] at hmem
                subst hmem
                exact matchRiscvBinop_reg_inBounds hbinop)
        return (ctx, some (#[newOp], #[newOp.getResult 0]))

/-- imm5 (word shifts/rotates): `src rs1 (li imm) -> dst rs1 imm` for `imm ∈ [0,31]`.
    Covers: sllw→slliw, srlw→srliw, sraw→sraiw, rorw→roriw. -/
def fold_shift5_li (src dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties) :
    LocalRewritePattern OpCode := fold_binop_li src dst h 0 31

/-- imm6 (full-width shifts/rotates and single-bit ops): `imm ∈ [0,63]`.
    Covers: sll→slli, srl→srli, sra→srai, ror→rori, bclr→bclri, bext→bexti,
    binv→binvi, bset→bseti. -/
def fold_shift6_li (src dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties) :
    LocalRewritePattern OpCode := fold_binop_li src dst h 0 63

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
      fold_add_li_to_addi,
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
      fold_zextw_slli_to_slliuw]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def Combine : Pass OpCode :=
  { name := "riscv-combine"
    description := "GlobalISel RISCV combines"
    run := Combine.impl }
