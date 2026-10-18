module
public import Veir.Passes.InstCombineLLVM.CompareSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
namespace Veir.Passes.InstCombineLLVM.XorCompareSelf
open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by cases ‹Decidable p› <;> rfl
private inductive EqNe | eq | ne
private def EqNe.pred : EqNe → LLVM.IntPred | .eq => .eq | .ne => .ne
private def pattern (kind : EqNe) (xorCommuted compareSwapped : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType); let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth=1)
    let a ← MatchProg.value ty; let b ← MatchProg.value ty
    let x ← MatchProg.operation (.llvm .xor) (match xorCommuted with | false => #[a,b] | true => #[b,a]) #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .icmp) (match compareSwapped with
      | false => #[x.res[0]!,a] | true => #[a,x.res[0]!]) #[bt] (fun p => p.predicate=kind.pred)
    return (ty,bt,b))
  (fun (ty,bt,b) => do
    let zp ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.llvm .mlir__constant))) ty
      (fun type => do let some it := type.cast? IntegerType | none
                      return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt 0 it)))
    let z ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] zp
    let cp ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk kind.pred)
    CreateProg.operation (.llvm .icmp) #[b,z.res[0]!] #[bt] cp)
  (fun r => r.res[0]!)
private theorem valid (kind : EqNe) (xc cs : Bool) : Pattern.Valid (pattern kind xc cs) := by
  cases kind <;> cases xc <;> cases cs <;> simp only [pattern, EqNe.pred] <;> unfoldPuddleBuilder
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
    rintro a b ⟨⟩ xv hx; obtain rfl := (xor_iff _ _ _ _).mp hx
    rintro cp cv hm hc; obtain rfl := (icmp_iff _ cp _ _ _).mp hc; have hm' := of_decide_eq_true hm; rw [hm']
    simp [IsTypeAttr.cast?_of]
    refine ⟨.int w (.val (BitVec.ofInt w 0)), ?_, ?_⟩
    · apply (constant_iff _ _ _).mpr
      simpa [IntegerAttr.ofInt] using congrArg (fun z => RuntimeValue.int w (.val z))
        (ofInt_normalizeValue {bitwidth:=w,signedness:=s} 0).symm
  all_goals
    first
    | refine ⟨.int 1 (LLVM.Int.icmp b (.val 0) .eq), (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    | refine ⟨.int 1 (LLVM.Int.icmp b (.val 0) .ne), (icmp_iff _ (IcmpProperties.mk .ne) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
  · simpa only [LLVM.Int.cast_self] using icmp_xor_self_eq_zero a b
  · simpa only [LLVM.Int.cast_self] using icmp_self_xor_eq_zero a b
  · rw [llvm_xor_comm b a]; simpa only [LLVM.Int.cast_self] using icmp_xor_self_eq_zero a b
  · rw [llvm_xor_comm b a]
    simpa only [LLVM.Int.cast_self] using icmp_self_xor_eq_zero a b
  · simpa only [LLVM.Int.cast_self] using icmp_xor_self_ne_zero a b
  · simpa only [LLVM.Int.cast_self] using icmp_self_xor_ne_zero a b
  · rw [llvm_xor_comm b a]; simpa only [LLVM.Int.cast_self] using icmp_xor_self_ne_zero a b
  · rw [llvm_xor_comm b a]
    simpa only [LLVM.Int.cast_self] using icmp_self_xor_ne_zero a b
public def xorCompareSelfEq : Pattern OpCode := pattern .eq false false
public theorem xorCompareSelfEq_valid : Pattern.Valid xorCompareSelfEq := valid .eq false false
public def xorCompareSelfEqSwapped : Pattern OpCode := pattern .eq false true
public theorem xorCompareSelfEqSwapped_valid : Pattern.Valid xorCompareSelfEqSwapped := valid .eq false true
public def xorCompareSelfEqCommuted : Pattern OpCode := pattern .eq true false
public theorem xorCompareSelfEqCommuted_valid : Pattern.Valid xorCompareSelfEqCommuted := valid .eq true false
public def xorCompareSelfEqCommutedSwapped : Pattern OpCode := pattern .eq true true
public theorem xorCompareSelfEqCommutedSwapped_valid : Pattern.Valid xorCompareSelfEqCommutedSwapped := valid .eq true true
public def xorCompareSelfNe : Pattern OpCode := pattern .ne false false
public theorem xorCompareSelfNe_valid : Pattern.Valid xorCompareSelfNe := valid .ne false false
public def xorCompareSelfNeSwapped : Pattern OpCode := pattern .ne false true
public theorem xorCompareSelfNeSwapped_valid : Pattern.Valid xorCompareSelfNeSwapped := valid .ne false true
public def xorCompareSelfNeCommuted : Pattern OpCode := pattern .ne true false
public theorem xorCompareSelfNeCommuted_valid : Pattern.Valid xorCompareSelfNeCommuted := valid .ne true false
public def xorCompareSelfNeCommutedSwapped : Pattern OpCode := pattern .ne true true
public theorem xorCompareSelfNeCommutedSwapped_valid : Pattern.Valid xorCompareSelfNeCommutedSwapped := valid .ne true true
end Veir.Passes.InstCombineLLVM.XorCompareSelf
