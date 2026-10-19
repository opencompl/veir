import Veir.Passes.ArithCanonicalize.CommutativeSupport
import Veir.Passes.ArithCanonicalize.SelectSupport
import Veir.Passes.ArithCanonicalize.ExtendedSupport

namespace Veir.ArithCanonicalize.G001

open Veir Veir.Puddle Veir.Data

/-- Scalar integer binary instances of MLIR's commutative constant-to-RHS
    canonicalization. -/
inductive ScalarOp where
  | addi | muli | andi | ori | xori
  | maxsi | maxui | minsi | minui
deriving DecidableEq, Repr

def ScalarOp.opcode : ScalarOp → OpCode
  | .addi => .arith .addi
  | .muli => .arith .muli
  | .andi => .arith .andi
  | .ori => .arith .ori
  | .xori => .arith .xori
  | .maxsi => .arith .maxsi
  | .maxui => .arith .maxui
  | .minsi => .arith .minsi
  | .minui => .arith .minui

/-- Moves a scalar integer constant from the first to the second operand,
    forwarding the original operation's properties unchanged. -/
def pattern (op : ScalarOp) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let c ← MatchProg.operation (.arith .constant) #[] #[ty]
      let x ← MatchProg.value ty
      let root ← MatchProg.root op.opcode #[c.res[0]!, x] #[ty]
      let () ← MatchProg.inspectOperation (Outputs := Unit) root.op (fun ctx matched => do
        match matched.getOperand! ctx 1 with
        | .blockArgument _ => some ()
        | .opResult result =>
          let owner := result.getOwner! ctx
          guard (!(owner.getOpType! ctx).isConstantLike)
          some ())
      return (ty, c.res[0]!, x, root.properties))
    (fun (ty, c, x, props) => do
      let replacement ← CreateProg.operation op.opcode #[x, c] #[ty] props
      return replacement)
    (fun result => result)

open Veir.ArithPuddle
open Veir.ArithCanonicalize.CommutativeSupport
open Veir.ArithCanonicalize.SelectSupport
open Veir.ArithCanonicalize.ExtendedSupport

theorem pattern_valid_addi : Pattern.Valid (pattern .addi) := by
  unfold pattern ScalarOp.opcode
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, sign⟩ cp cv hc x p v hv _
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain rfl := (addi_iff _ _ _ _ _).mp hv
  refine ⟨.int w (LLVM.Int.add x (.val (BitVec.ofInt w cp.value.value))
    p.attr.nsw p.attr.nuw), ?_, ?_⟩
  · exact (addi_iff _ _ _ _ _).mpr rfl
  · rw [add_comm_flags]
    exact RuntimeValue.isRefinedBy_refl _

theorem pattern_valid_muli : Pattern.Valid (pattern .muli) := by
  unfold pattern ScalarOp.opcode
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, sign⟩ cp cv hc x p v hv _
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain rfl := (muli_iff _ _ _ _ _).mp hv
  refine ⟨.int w (LLVM.Int.mul x (.val (BitVec.ofInt w cp.value.value)) p.attr.nsw p.attr.nuw), ?_, ?_⟩
  · exact (muli_iff _ _ _ _ _).mpr rfl
  · rw [mul_comm_flags]
    exact RuntimeValue.isRefinedBy_refl _

theorem pattern_valid_andi : Pattern.Valid (pattern .andi) := by
  unfold pattern ScalarOp.opcode
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, sign⟩ cp cv hc x p v hv _
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain rfl := (andi_iff _ _ _ _).mp hv
  refine ⟨.int w (LLVM.Int.and x (.val (BitVec.ofInt w cp.value.value))), ?_, ?_⟩
  · exact (andi_iff _ _ _ _).mpr rfl
  · rw [CommutativeSupport.and_comm]
    exact RuntimeValue.isRefinedBy_refl _

theorem pattern_valid_ori : Pattern.Valid (pattern .ori) := by
  unfold pattern ScalarOp.opcode
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, sign⟩ cp cv hc x p v hv _
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain rfl := (ori_iff _ _ _ _ _).mp hv
  refine ⟨.int w (LLVM.Int.or x (.val (BitVec.ofInt w cp.value.value)) p.disjoint), ?_, ?_⟩
  · exact (ori_iff _ _ _ _ _).mpr rfl
  · rw [or_comm_flags]
    exact RuntimeValue.isRefinedBy_refl _

theorem pattern_valid_xori : Pattern.Valid (pattern .xori) := by
  unfold pattern ScalarOp.opcode
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, sign⟩ cp cv hc x p v hv _
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain rfl := (xori_iff _ _ _ _).mp hv
  refine ⟨.int w (LLVM.Int.xor x (.val (BitVec.ofInt w cp.value.value))), ?_, ?_⟩
  · exact (xori_iff _ _ _ _).mpr rfl
  · rw [xor_comm]
    exact RuntimeValue.isRefinedBy_refl _

theorem pattern_valid_maxsi : Pattern.Valid (pattern .maxsi) := by
  unfold pattern ScalarOp.opcode
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, sign⟩ cp cv hc x p v hv _
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain rfl := (maxsi_iff _ _ _ _).mp hv
  refine ⟨.int w (LLVM.Int.smax x (.val (BitVec.ofInt w cp.value.value))), ?_, ?_⟩
  · exact (maxsi_iff _ _ _ _).mpr rfl
  · rw [smax_comm]
    exact RuntimeValue.isRefinedBy_refl _

theorem pattern_valid_maxui : Pattern.Valid (pattern .maxui) := by
  unfold pattern ScalarOp.opcode
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, sign⟩ cp cv hc x p v hv _
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain rfl := (maxui_iff _ _ _ _).mp hv
  refine ⟨.int w (LLVM.Int.umax x (.val (BitVec.ofInt w cp.value.value))), ?_, ?_⟩
  · exact (maxui_iff _ _ _ _).mpr rfl
  · rw [umax_comm]
    exact RuntimeValue.isRefinedBy_refl _

theorem pattern_valid_minsi : Pattern.Valid (pattern .minsi) := by
  unfold pattern ScalarOp.opcode
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, sign⟩ cp cv hc x p v hv _
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain rfl := (minsi_iff _ _ _ _).mp hv
  refine ⟨.int w (LLVM.Int.smin x (.val (BitVec.ofInt w cp.value.value))), ?_, ?_⟩
  · exact (minsi_iff _ _ _ _).mpr rfl
  · rw [smin_comm]
    exact RuntimeValue.isRefinedBy_refl _

theorem pattern_valid_minui : Pattern.Valid (pattern .minui) := by
  unfold pattern ScalarOp.opcode
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, sign⟩ cp cv hc x p v hv _
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain rfl := (minui_iff _ _ _ _).mp hv
  refine ⟨.int w (LLVM.Int.umin x (.val (BitVec.ofInt w cp.value.value))), ?_, ?_⟩
  · exact (minui_iff _ _ _ _).mpr rfl
  · rw [umin_comm]
    exact RuntimeValue.isRefinedBy_refl _

theorem pattern_valid (op : ScalarOp) : Pattern.Valid (pattern op) := by
  cases op
  · exact pattern_valid_addi
  · exact pattern_valid_muli
  · exact pattern_valid_andi
  · exact pattern_valid_ori
  · exact pattern_valid_xori
  · exact pattern_valid_maxsi
  · exact pattern_valid_maxui
  · exact pattern_valid_minsi
  · exact pattern_valid_minui

/-- The two-result unsigned-add instance of the commutative constant ordering
    trait. Both sum and carry results are retained. -/
def pattern_addui_extended : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let carryTy ← MatchProg.type (Attr := IntegerType)
        (fun t => t == IntegerType.signless 1)
      let c ← MatchProg.operation (.arith .constant) #[] #[ty]
      let x ← MatchProg.value ty
      let root ← MatchProg.root (.arith .addui_extended)
        #[c.res[0]!, x] #[ty, carryTy]
      let () ← MatchProg.inspectOperation (Outputs := Unit) root.op (fun ctx matched => do
        match matched.getOperand! ctx 1 with
        | .blockArgument _ => some ()
        | .opResult result =>
          let owner := result.getOwner! ctx
          guard (!(owner.getOpType! ctx).isConstantLike)
          some ())
      return (ty, carryTy, c.res[0]!, x, root.properties))
    (fun (ty, carryTy, c, x, props) =>
      CreateProg.operation (.arith .addui_extended)
        #[x, c] #[ty, carryTy] props)
    (fun result => result)

theorem pattern_addui_extended_valid : Pattern.Valid pattern_addui_extended := by
  unfold pattern_addui_extended
  provePuddleValid
  rintro ⟨w, s⟩ ty ⟨cw, t⟩ hTy hSign cp cv hc x hx p v0 v1 hi _
  cases hTy
  cases hSign
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain ⟨rfl, rfl⟩ := (addui_extended_iff _ _ _ _ _).mp hi
  refine ⟨.int w (LLVM.Int.add x (.val (BitVec.ofInt w cp.value.value))),
    .int 1 (LLVM.Int.uaddOverflowFlag x (.val (BitVec.ofInt w cp.value.value))),
    ?_, ?_, ?_⟩
  · exact (addui_extended_iff _ _ _ _ _).mpr ⟨rfl, rfl⟩
  · rw [add_comm_flags]
    exact RuntimeValue.isRefinedBy_refl _
  · rw [uaddOverflowFlag_comm]
    exact RuntimeValue.isRefinedBy_refl _

/-- The two-result signed-multiply instance, preserving low and high halves. -/
def pattern_mulsi_extended : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let c ← MatchProg.operation (.arith .constant) #[] #[ty]
      let x ← MatchProg.value ty
      let root ← MatchProg.root (.arith .mulsi_extended)
        #[c.res[0]!, x] #[ty, ty]
      let () ← MatchProg.inspectOperation (Outputs := Unit) root.op (fun ctx matched => do
        match matched.getOperand! ctx 1 with
        | .blockArgument _ => some ()
        | .opResult result =>
          let owner := result.getOwner! ctx
          guard (!(owner.getOpType! ctx).isConstantLike)
          some ())
      return (ty, c.res[0]!, x, root.properties))
    (fun (ty, c, x, props) =>
      CreateProg.operation (.arith .mulsi_extended) #[x, c] #[ty, ty] props)
    (fun result => result)

theorem pattern_mulsi_extended_valid : Pattern.Valid pattern_mulsi_extended := by
  unfold pattern_mulsi_extended
  provePuddleValid
  rintro ⟨w, s⟩ cp cv hc x hx p v0 v1 hi _
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain ⟨rfl, rfl⟩ := (mulsi_extended_iff _ _ _ _ _).mp hi
  refine ⟨.int w (LLVM.Int.mul x (.val (BitVec.ofInt w cp.value.value))),
    .int w (LLVM.Int.smulHigh x (.val (BitVec.ofInt w cp.value.value))),
    ?_, ?_, ?_⟩
  · exact (mulsi_extended_iff _ _ _ _ _).mpr ⟨rfl, rfl⟩
  · rw [LLVM.Int.mul_comm]
    exact RuntimeValue.isRefinedBy_refl _
  · rw [smulHigh_comm]
    exact RuntimeValue.isRefinedBy_refl _

/-- The two-result unsigned-multiply instance, preserving low and high halves. -/
def pattern_mului_extended : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let c ← MatchProg.operation (.arith .constant) #[] #[ty]
      let x ← MatchProg.value ty
      let root ← MatchProg.root (.arith .mului_extended)
        #[c.res[0]!, x] #[ty, ty]
      let () ← MatchProg.inspectOperation (Outputs := Unit) root.op (fun ctx matched => do
        match matched.getOperand! ctx 1 with
        | .blockArgument _ => some ()
        | .opResult result =>
          let owner := result.getOwner! ctx
          guard (!(owner.getOpType! ctx).isConstantLike)
          some ())
      return (ty, c.res[0]!, x, root.properties))
    (fun (ty, c, x, props) =>
      CreateProg.operation (.arith .mului_extended) #[x, c] #[ty, ty] props)
    (fun result => result)

theorem pattern_mului_extended_valid : Pattern.Valid pattern_mului_extended := by
  unfold pattern_mului_extended
  provePuddleValid
  rintro ⟨w, s⟩ cp cv hc x hx p v0 v1 hi _
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  obtain rfl := (constant_iff _ _ _).mp hc
  obtain ⟨rfl, rfl⟩ := (mului_extended_iff _ _ _ _ _).mp hi
  refine ⟨.int w (LLVM.Int.mul x (.val (BitVec.ofInt w cp.value.value))),
    .int w (LLVM.Int.umulHigh x (.val (BitVec.ofInt w cp.value.value))),
    ?_, ?_, ?_⟩
  · exact (mului_extended_iff _ _ _ _ _).mpr ⟨rfl, rfl⟩
  · rw [LLVM.Int.mul_comm]
    exact RuntimeValue.isRefinedBy_refl _
  · rw [umulHigh_comm]
    exact RuntimeValue.isRefinedBy_refl _

end Veir.ArithCanonicalize.G001
