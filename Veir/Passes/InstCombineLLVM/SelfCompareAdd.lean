module
public import Veir.Passes.InstCombineLLVM.CompareSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
namespace Veir.Passes.InstCombineLLVM.SelfCompareAdd
open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by cases ‹Decidable p› <;> rfl
@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t
private inductive EqNe | eq | ne
private def EqNe.pred : EqNe → LLVM.IntPred | .eq => .eq | .ne => .ne
private def zeroProperty (type : TypeAttr) : Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt 0 intType))
private def pattern (kind : EqNe) (commuted : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let a ← MatchProg.value ty; let d ← MatchProg.value ty
    let sum ← MatchProg.operation (.llvm .add) (match commuted with
      | false => #[a, d] | true => #[d, a]) #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .icmp) #[a, sum.res[0]!] #[bt]
      (fun p => p.predicate = kind.pred)
    return (ty, bt, d))
  (fun (ty, bt, d) => do
    let zp ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.llvm .mlir__constant))) ty zeroProperty
    let zero ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] zp
    let cp ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk kind.pred)
    CreateProg.operation (.llvm .icmp) #[zero.res[0]!, d] #[bt] cp)
  (fun r => r.res[0]!)
private theorem pattern_valid (kind : EqNe) (commuted : Bool) : Pattern.Valid (pattern kind commuted) := by
  cases kind <;> cases commuted <;> simp only [pattern, EqNe.pred] <;> unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
        HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
        HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpPuddleSemantics
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ bt ⟨bw, bs⟩ hbt hbw; subst bt; change bw = 1 at hbw; subst bw
    rintro a d addProps sum hsum; obtain rfl := (add_iff _ _ _ _ _).mp hsum
    rintro cp cv hp hc; obtain rfl := (icmp_iff _ cp _ _ _).mp hc
    have hp' := of_decide_eq_true hp; rw [hp']
    simp [zeroProperty, IsTypeAttr.cast?_of]
    refine ⟨.int w (.val (BitVec.ofInt w 0)), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg (fun z => RuntimeValue.int w (.val z))
        (ofInt_normalizeValue { bitwidth := w, signedness := s } 0).symm
  · refine ⟨.int 1 (LLVM.Int.icmp (.val 0) d .eq), (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl,
      ⟨rfl, ?_⟩⟩
    simpa only [LLVM.Int.cast_self] using icmp_self_add_eq_zero_flags a d addProps.nsw addProps.nuw
  · refine ⟨.int 1 (LLVM.Int.icmp (.val 0) d .eq), (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl,
      ⟨rfl, ?_⟩⟩
    rw [llvm_add_comm_flags d a]
    simpa only [LLVM.Int.cast_self] using icmp_self_add_eq_zero_flags a d addProps.nsw addProps.nuw
  · refine ⟨.int 1 (LLVM.Int.icmp (.val 0) d .ne), (icmp_iff _ (IcmpProperties.mk .ne) _ _ _).mpr rfl,
      ⟨rfl, ?_⟩⟩
    simpa only [LLVM.Int.cast_self] using icmp_self_add_ne_zero_flags a d addProps.nsw addProps.nuw
  · refine ⟨.int 1 (LLVM.Int.icmp (.val 0) d .ne), (icmp_iff _ (IcmpProperties.mk .ne) _ _ _).mpr rfl,
      ⟨rfl, ?_⟩⟩
    rw [llvm_add_comm_flags d a]
    simpa only [LLVM.Int.cast_self] using icmp_self_add_ne_zero_flags a d addProps.nsw addProps.nuw
public def selfCompareAddEq : Pattern OpCode := pattern .eq false
public theorem selfCompareAddEq_valid : Pattern.Valid selfCompareAddEq := pattern_valid .eq false
public def selfCompareAddEqCommuted : Pattern OpCode := pattern .eq true
public theorem selfCompareAddEqCommuted_valid : Pattern.Valid selfCompareAddEqCommuted := pattern_valid .eq true
public def selfCompareAddNe : Pattern OpCode := pattern .ne false
public theorem selfCompareAddNe_valid : Pattern.Valid selfCompareAddNe := pattern_valid .ne false
public def selfCompareAddNeCommuted : Pattern OpCode := pattern .ne true
public theorem selfCompareAddNeCommuted_valid : Pattern.Valid selfCompareAddNeCommuted := pattern_valid .ne true

private def guardedPattern (signed commuted : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let a ← MatchProg.value ty; let d ← MatchProg.value ty
    let sum ← MatchProg.operation (.llvm .add) (if commuted then #[d, a] else #[a, d]) #[ty]
      (fun p => if signed then p.nsw else p.nuw)
    let root ← MatchProg.root (.llvm .icmp) #[a, sum.res[0]!] #[bt]
      (fun p => if signed then isSignedPredicate p.predicate else isUnsignedPredicate p.predicate)
    return (ty, bt, d, root))
  (fun (ty, bt, d, root) => do
    let zp ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.llvm .mlir__constant))) ty zeroProperty
    let zero ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] zp
    CreateProg.operation (.llvm .icmp) #[zero.res[0]!, d] #[bt] root.properties)
  (fun r => r.res[0]!)

private theorem guardedPattern_valid (signed commuted : Bool) :
    Pattern.Valid (guardedPattern signed commuted) := by
  cases signed <;> cases commuted <;>
    simp only [guardedPattern, Bool.false_eq_true, ite_false, ite_true] <;> unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
        HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
        HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpPuddleSemantics
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ bt ⟨bw, bs⟩ hbt hbw; subst bt; change bw = 1 at hbw; subst bw
    rintro a d addProps sum hflag hsum; obtain rfl := (add_iff _ _ _ _ _).mp hsum
    rintro cp cv hp hc; obtain rfl := (icmp_iff _ cp _ _ _).mp hc
    have hallowed : compareCancellationAllowed cp.predicate addProps.nsw addProps.nuw = true := by
      cases hpred : cp.predicate <;> simp_all [isSignedPredicate, isUnsignedPredicate,
        compareCancellationAllowed]
    simp [zeroProperty, IsTypeAttr.cast?_of]
    refine ⟨.int w (.val (BitVec.ofInt w 0)), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg (fun z => RuntimeValue.int w (.val z))
        (ofInt_normalizeValue { bitwidth := w, signedness := s } 0).symm
    · refine ⟨.int 1 (LLVM.Int.icmp (.val 0) d cp.predicate),
        (icmp_iff _ cp _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
      first
      | exact (by simpa only [LLVM.Int.cast_self] using
          icmp_self_add_pred_flags cp.predicate a d addProps.nsw addProps.nuw hallowed)
      | (rw [llvm_add_comm_flags d a]
         exact (by simpa only [LLVM.Int.cast_self] using
           icmp_self_add_pred_flags cp.predicate a d addProps.nsw addProps.nuw hallowed))

public def selfCompareAddUnsigned : Pattern OpCode := guardedPattern false false
public theorem selfCompareAddUnsigned_valid : Pattern.Valid selfCompareAddUnsigned := guardedPattern_valid false false
public def selfCompareAddUnsignedCommuted : Pattern OpCode := guardedPattern false true
public theorem selfCompareAddUnsignedCommuted_valid : Pattern.Valid selfCompareAddUnsignedCommuted := guardedPattern_valid false true
public def selfCompareAddSigned : Pattern OpCode := guardedPattern true false
public theorem selfCompareAddSigned_valid : Pattern.Valid selfCompareAddSigned := guardedPattern_valid true false
public def selfCompareAddSignedCommuted : Pattern OpCode := guardedPattern true true
public theorem selfCompareAddSignedCommuted_valid : Pattern.Valid selfCompareAddSignedCommuted := guardedPattern_valid true true

private def disjointOrPattern (commuted : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let a ← MatchProg.value ty; let d ← MatchProg.value ty
    let sum ← MatchProg.operation (.llvm .or) (if commuted then #[d, a] else #[a, d]) #[ty]
      (fun p => p.disjoint)
    let root ← MatchProg.root (.llvm .icmp) #[a, sum.res[0]!] #[bt]
    return (ty, bt, a, d, root))
  (fun (ty, bt, _a, d, root) => do
    let zp ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      ty zeroProperty
    let zero ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] zp
    CreateProg.operation (.llvm .icmp) #[zero.res[0]!, d] #[bt] root.properties)
  (fun r => r.res[0]!)

private theorem disjointOrPattern_valid (commuted : Bool) :
    Pattern.Valid (disjointOrPattern commuted) := by
  cases commuted <;> simp only [disjointOrPattern, Bool.false_eq_true, ite_false, ite_true] <;>
    unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
        HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
        HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
        Replacement.checkBindings]
    simpPuddleSemantics
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ bt ⟨bw, bs⟩ hbt hbw; subst bt; change bw = 1 at hbw; subst bw
    rintro a d op rv hd hr; obtain rfl := (or_iff _ op _ _ _).mp hr
    rintro (cp : IcmpProperties) cv hc; obtain rfl := (icmp_iff _ cp _ _ _).mp hc
    have hd' : op.disjoint = true := hd
    rw [hd']
    simp [zeroProperty, IsTypeAttr.cast?_of]
    refine ⟨.int w (.val (BitVec.ofInt w 0)), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg (fun z => RuntimeValue.int w (.val z))
        (ofInt_normalizeValue {bitwidth := w, signedness := s} 0).symm
    · refine ⟨.int 1 (LLVM.Int.icmp (.val 0) d cp.predicate),
        (icmp_iff _ cp _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
      first
      | exact (by simpa only [LLVM.Int.cast_self] using (isRefinedBy_trans
          (icmp_refine_mono cp.predicate (isRefinedBy_refl a) (disjoint_or_refines_add a d))
          (icmp_self_add_pred_flags cp.predicate a d true true (by cases cp.predicate <;> rfl))))
      | (rw [llvm_or_comm d a true]
         exact (by simpa only [LLVM.Int.cast_self] using (isRefinedBy_trans
           (icmp_refine_mono cp.predicate (isRefinedBy_refl a) (disjoint_or_refines_add a d))
           (icmp_self_add_pred_flags cp.predicate a d true true (by cases cp.predicate <;> rfl)))))

public def selfCompareOrDisjoint : Pattern OpCode := disjointOrPattern false
public theorem selfCompareOrDisjoint_valid : Pattern.Valid selfCompareOrDisjoint :=
  disjointOrPattern_valid false
public def selfCompareOrDisjointCommuted : Pattern OpCode := disjointOrPattern true
public theorem selfCompareOrDisjointCommuted_valid : Pattern.Valid selfCompareOrDisjointCommuted :=
  disjointOrPattern_valid true
end Veir.Passes.InstCombineLLVM.SelfCompareAdd
