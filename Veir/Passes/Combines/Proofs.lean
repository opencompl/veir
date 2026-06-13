import Veir.Data.RISCV.Reg.Basic
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Passes.Combines.Combine
import Veir.PatternRewriter.Semantics

/-!
  In this file we prove the correctness of the RISCV combines.
-/

namespace Veir

namespace RISCV

variable (src dst : Riscv) (hd : Riscv.propertiesOf dst = RISCVImmediateProperties) (lo hi : Int)

/--
  Characterizes a successful firing of `fold_binop_li`: it must have matched
  `src`/`li`, passed the range check, and created a single `dst` op, returning
  that op and its result. The bound `[lo, hi]` plays no role in the structural
  facts, so all of the predicate proofs below hold uniformly — which is exactly
  what lets the imm5 and imm6 families share this work.
-/
theorem fold_binop_li_spec
    {ctx newCtx : WfIRContext OpCode} {op : OperationPtr}
    {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    (h : fold_binop_li src dst hd lo hi ctx op = some (newCtx, some (newOps, newValues))) :
    ∃ reg rhs imm hoper newOp,
      matchRiscvBinop src op ctx = some (reg, rhs) ∧
      matchLi rhs ctx = some imm ∧
      WfRewriter.createOp ctx (.riscv dst) #[RegisterType.mk] #[reg] #[] #[]
          (cast hd.symm imm) none hoper = some (newCtx, newOp) ∧
      newOps = #[newOp] ∧ newValues = #[(newOp.getResult 0 : ValuePtr)] := by
  unfold fold_binop_li at h
  repeat' split at h
  all_goals try (exfalso; simp_all; done)
  rename_i reg rhs hbinop _x imm hmatchli _hbound
  obtain ⟨⟨c, newOp⟩, hcreate, hval⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hval
  obtain ⟨rfl, hops, hvals⟩ := hval
  exact ⟨reg, rhs, imm, _, newOp, hbinop, hmatchli, hcreate, hops.symm, hvals.symm⟩

/-- `fold_binop_li` only ever modifies the context by creating new operations. -/
theorem fold_binop_li_ReturnCtxChanges :
    (fold_binop_li src dst hd lo hi).ReturnCtxChanges := by
  intro ctx op newCtx newOps newValues hpat
  obtain ⟨reg, rhs, imm, hoper, newOp, hbinop, hmatchli, hcreate, hops, hvals⟩ :=
    fold_binop_li_spec src dst hd lo hi hpat
  exact WfIRContext.WithCreatedOps.CreatedOp ctx ctx newCtx (.Nil ctx)
    ⟨_, _, _, _, _, _, _, _, _, _, hcreate⟩

/-- `fold_binop_li` returns exactly as many values as the matched op has results. -/
theorem fold_binop_li_ReturnValues :
    (fold_binop_li src dst hd lo hi).ReturnValues := by
  intro ctx op _hin newCtx newOps newValues hpat
  obtain ⟨reg, rhs, imm, hoper, newOp, hbinop, hmatchli, hcreate, hops, hvals⟩ :=
    fold_binop_li_spec src dst hd lo hi hpat
  subst hvals
  rw [matchRiscvBinop_getNumResults hbinop]
  rfl

/-- Every value `fold_binop_li` returns is in bounds of the new context. -/
theorem fold_binop_li_ReturnValuesInBounds :
    (fold_binop_li src dst hd lo hi).ReturnValuesInBounds := by
  intro ctx op newCtx newOps newValues hpat v hv
  obtain ⟨reg, rhs, imm, hoper, newOp, hbinop, hmatchli, hcreate, hops, hvals⟩ :=
    fold_binop_li_spec src dst hd lo hi hpat
  subst hvals
  simp only [Array.mem_singleton] at hv
  subst hv
  grind [WfRewriter.createOp, Rewriter.createOp_inBounds,
    OperationPtr.getResult_op, OperationPtr.getResult_index]

/-- The operations `fold_binop_li` returns are exactly the newly-created ones. -/
theorem fold_binop_li_ReturnOps :
    (fold_binop_li src dst hd lo hi).ReturnOps := by
  intro ctx op newCtx newOps newValues hpat newOp'
  obtain ⟨reg, rhs, imm, hoper, newOp, hbinop, hmatchli, hcreate, hops, hvals⟩ :=
    fold_binop_li_spec src dst hd lo hi hpat
  subst hops
  simp only [Array.mem_singleton]
  constructor
  · rintro rfl
    exact ⟨WfRewriter.createOp_new_inBounds _ hcreate,
           WfRewriter.createOp_new_not_inBounds _ hcreate⟩
  · rintro ⟨hin, hnin⟩
    grind [WfRewriter.createOp, Rewriter.createOp_inBounds]

/-! ### imm5 / imm6 specializations — the same proofs at different bounds. -/

theorem fold_shift5_li_ReturnCtxChanges : (fold_shift5_li src dst hd).ReturnCtxChanges :=
  fold_binop_li_ReturnCtxChanges src dst hd 0 31
theorem fold_shift5_li_ReturnValues : (fold_shift5_li src dst hd).ReturnValues :=
  fold_binop_li_ReturnValues src dst hd 0 31
theorem fold_shift5_li_ReturnValuesInBounds : (fold_shift5_li src dst hd).ReturnValuesInBounds :=
  fold_binop_li_ReturnValuesInBounds src dst hd 0 31
theorem fold_shift5_li_ReturnOps : (fold_shift5_li src dst hd).ReturnOps :=
  fold_binop_li_ReturnOps src dst hd 0 31

theorem fold_shift6_li_ReturnCtxChanges : (fold_shift6_li src dst hd).ReturnCtxChanges :=
  fold_binop_li_ReturnCtxChanges src dst hd 0 63
theorem fold_shift6_li_ReturnValues : (fold_shift6_li src dst hd).ReturnValues :=
  fold_binop_li_ReturnValues src dst hd 0 63
theorem fold_shift6_li_ReturnValuesInBounds : (fold_shift6_li src dst hd).ReturnValuesInBounds :=
  fold_binop_li_ReturnValuesInBounds src dst hd 0 63
theorem fold_shift6_li_ReturnOps : (fold_shift6_li src dst hd).ReturnOps :=
  fold_binop_li_ReturnOps src dst hd 0 63

end RISCV

end Veir

namespace Veir.Data.RISCV


/--
  Prove the correctness of the `right_identity_zero_add` combine.
-/
theorem right_identity_zero_add:
    (RISCV.add lhs (Data.RISCV.li (BitVec.ofInt 64 0))) = lhs := by
  simp [reg_toBitVec]

/--
  Encoding fact: re-encoding an `Int` immediate at width 5 agrees with
  truncating its width-64 encoding to 5 bits. This connects how the Veir
  interpreter materializes the same `properties.value.value` for `riscv.li`
  (via `BitVec.ofInt 64`) and for `riscv.slliw` (via `BitVec.ofInt 5`).
-/
theorem ofInt5_eq_setWidth_ofInt64 (i : Int) :
    BitVec.ofInt 5 i = (BitVec.ofInt 64 i).setWidth 5 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  omega

/--
  Correctness of the `fold_sllw_li_to_slliw` combine.

  The Veir interpreter evaluates the source `riscv.sllw rs1 (riscv.li i)` as
  `RISCV.sllw (RISCV.li (BitVec.ofInt 64 i)) rs1` and the rewritten
  `riscv.slliw rs1 i` as `RISCV.slliw (BitVec.ofInt 5 i) rs1`, where `i` is the
  shared immediate `properties.value.value`. We prove these denote the same
  register value for every register `rs1` and every immediate `i` — i.e. the new
  `slliw` refines (in fact, equals) the original `sllw`/`li` pair. Note this holds
  unconditionally: both instructions only consult the low 5 bits of the shift
  amount, so the combine's `0 ≤ i ≤ 31` guard is needed only for encodability,
  not for value correctness.
-/
theorem fold_sllw_li_to_slliw (rs1 : Reg) (i : Int) :
    RISCV.sllw (RISCV.li (BitVec.ofInt 64 i)) rs1
      = RISCV.slliw (BitVec.ofInt 5 i) rs1 := by
  rw [ofInt5_eq_setWidth_ofInt64]
  simp only [reg_toBitVec]
  bv_decide
