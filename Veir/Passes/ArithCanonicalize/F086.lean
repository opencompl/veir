import Veir.Passes.ArithCanonicalize.SelectSupport

/-! Pinned cmpi constant-to-RHS fold, including all ten predicates. -/
namespace Veir.ArithCanonicalize.F086

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize.SelectSupport

def swapOrder : LLVM.IntPred → LLVM.IntPred
  | .eq => .eq | .ne => .ne
  | .slt => .sgt | .sle => .sge | .sgt => .slt | .sge => .sle
  | .ult => .ugt | .ule => .uge | .ugt => .ult | .uge => .ule

private theorem eval_swapOrder (p : LLVM.IntPred) (x y : BitVec w) :
    LLVM.IntPred.eval p x y = LLVM.IntPred.eval (swapOrder p) y x := by
  cases p <;> simp [swapOrder, LLVM.IntPred.eval, Bool.beq_comm, bne_comm]

private theorem icmp_swapOrder (p : LLVM.IntPred) (x y : LLVM.Int w) :
    LLVM.Int.icmp x y p = LLVM.Int.icmp y x (swapOrder p) := by
  cases x with
  | poison => cases y <;> rfl
  | val a =>
    cases y with
    | poison => rfl
    | val b =>
      simp only [LLVM.Int.icmp, Id.run]
      rw [eval_swapOrder]

def pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType)
        (fun t => t == IntegerType.signless 1)
      let c ← MatchProg.operation (.arith .constant) #[] #[ty]
      let x ← MatchProg.value ty
      let root ← MatchProg.root (.arith .cmpi) #[c.res[0]!, x] #[boolTy]
      let () ← MatchProg.inspectOperation (Outputs := Unit) root.op (fun ctx matched => do
        match matched.getOperand! ctx 1 with
        | .blockArgument _ => some ()
        | .opResult result =>
          let owner := result.getOwner! ctx
          guard (!(owner.getOpType! ctx).isConstantLike)
          some ())
      return (boolTy, x, c.res[0]!, root.properties))
    (fun (boolTy, x, c, props) => do
      let swapped ← CreateProg.applyNative
        (Outputs := Handle OpCode (.prop (.arith .cmpi))) props
        (fun p => some { predicate := swapOrder p.predicate })
      CreateProg.operation (.arith .cmpi) #[x, c] #[boolTy] swapped)
    (fun result => result)

theorem valid : Pattern.Valid pattern := by
  simp only [pattern]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, s⟩ boolTy ⟨bw, bs⟩ hBoolTy hBool cp cv hc x p v hv _
  cases hBoolTy
  cases hBool
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain rfl := (cmpi_iff _ _ _ _ _).mp hv
  refine ⟨.int 1 (LLVM.Int.icmp x (.val (BitVec.ofInt w cp.value.value))
    (swapOrder p.predicate)), ?_, ?_⟩
  · exact (cmpi_iff _ _ _ _ _).mpr rfl
  · rw [icmp_swapOrder]
    exact RuntimeValue.isRefinedBy_refl _

end Veir.ArithCanonicalize.F086
