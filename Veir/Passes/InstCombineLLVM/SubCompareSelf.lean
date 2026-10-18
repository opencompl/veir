module
public import Veir.Passes.InstCombineLLVM.CompareSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
namespace Veir.Passes.InstCombineLLVM.SubCompareSelf
open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by cases ‹Decidable p› <;> rfl
@[local cbv_eval] theorem integerType_cast (t : IntegerType) :
    (TypeAttr.of IntegerType t).cast? IntegerType = some t := IsTypeAttr.cast?_of t
private def zeroProperty (type : TypeAttr) : Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt 0 intType))
private def pattern (pred : LLVM.IntPred) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType); let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth=1)
    let a ← MatchProg.value ty; let b ← MatchProg.value ty
    let diff ← MatchProg.operation (.llvm .sub) #[a,b] #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .icmp) #[diff.res[0]!,a] #[bt] (fun p => p.predicate=pred)
    return (ty,bt,b))
  (fun (ty,bt,b) => do
    let zp ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.llvm .mlir__constant))) ty zeroProperty
    let z ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] zp
    let cp ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk pred)
    CreateProg.operation (.llvm .icmp) #[z.res[0]!,b] #[bt] cp)
  (fun r => r.res[0]!)
private theorem valid (pred : LLVM.IntPred) (hp : pred=.eq ∨ pred=.ne) : Pattern.Valid (pattern pred) := by
  rcases hp with rfl | rfl <;> simp only [pattern] <;> unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpPuddleSemantics
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w,s⟩ bt ⟨bw,bs⟩ hbt hbw; subst bt; change bw=1 at hbw; subst bw
    rintro a b sp sv hs; obtain rfl := (sub_iff _ _ _ _ _).mp hs
    rintro cp cv hm hc; obtain rfl := (icmp_iff _ cp _ _ _).mp hc; rw [hm]
    simp [zeroProperty, IsTypeAttr.cast?_of]
    refine ⟨.int w (.val (BitVec.ofInt w 0)), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg (fun z => RuntimeValue.int w (.val z))
        (ofInt_normalizeValue {bitwidth:=w,signedness:=s} 0).symm
  · refine ⟨.int 1 (LLVM.Int.icmp (.val 0) b .eq), (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    simpa only [LLVM.Int.cast_self] using icmp_sub_self_eq_zero_flags a b sp.nsw sp.nuw
  · refine ⟨.int 1 (LLVM.Int.icmp (.val 0) b .ne), (icmp_iff _ (IcmpProperties.mk .ne) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    simpa only [LLVM.Int.cast_self] using icmp_sub_self_ne_zero_flags a b sp.nsw sp.nuw
public def subCompareSelfEq : Pattern OpCode := pattern .eq
public theorem subCompareSelfEq_valid : Pattern.Valid subCompareSelfEq := valid .eq (Or.inl rfl)
public def subCompareSelfNe : Pattern OpCode := pattern .ne
public theorem subCompareSelfNe_valid : Pattern.Valid subCompareSelfNe := valid .ne (Or.inr rfl)

private def relationalPattern : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let diff ← MatchProg.operation (.llvm .sub) #[a, b] #[ty] (fun _ => true)
    let root ← MatchProg.root (.llvm .icmp) #[diff.res[0]!, a] #[bt]
    MatchProg.matchNative (root.properties, diff.properties) fun (cp, sp) =>
      compareCancellationAllowed cp.predicate sp.nsw sp.nuw
    return (ty, bt, b, root))
  (fun (ty, bt, b, root) => do
    let zp ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.llvm .mlir__constant)))
      ty zeroProperty
    let z ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] zp
    CreateProg.operation (.llvm .icmp) #[z.res[0]!, b] #[bt] root.properties)
  (fun r => r.res[0]!)

private theorem relationalPattern_valid : Pattern.Valid relationalPattern := by
  simp only [relationalPattern]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, MatchProg.collectBindings,
      MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
      HandleContext.forbidMany, HandleContext.lookup, HandleContext.lookupBindings,
      HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
      HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
      MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
      CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w, s⟩ bt ⟨bw, bs⟩ hbt hbw; subst bt; change bw = 1 at hbw; subst bw
  rintro a b sp sv hs; obtain rfl := (sub_iff _ _ _ _ _).mp hs
  rintro cp cv hc; obtain rfl := (icmp_iff _ cp _ _ _).mp hc
  rintro hallowed
  simp [zeroProperty, IsTypeAttr.cast?_of]
  refine ⟨.int w (.val (BitVec.ofInt w 0)), ?_, ?_⟩
  · apply (constant_iff _ _ _).mpr
    simpa [IntegerAttr.ofInt] using congrArg (fun z => RuntimeValue.int w (.val z))
      (ofInt_normalizeValue {bitwidth := w, signedness := s} 0).symm
  · refine ⟨.int 1 (LLVM.Int.icmp (.val 0) b cp.predicate),
      (icmp_iff _ cp _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    simpa only [LLVM.Int.cast_self] using
      icmp_sub_self_pred_flags cp.predicate a b sp.nsw sp.nuw hallowed

public def subCompareSelfRelational : Pattern OpCode := relationalPattern
public theorem subCompareSelfRelational_valid : Pattern.Valid subCompareSelfRelational :=
  relationalPattern_valid
end Veir.Passes.InstCombineLLVM.SubCompareSelf
