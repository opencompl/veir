module

public import Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics
import Veir.Passes.InstCombineLLVM.CompareSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.FlaggedXorTruncToICmp

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics

@[local cbv_eval]
theorem guard_eq_cond_punit {condition : Prop} [Decidable condition] :
    (guard condition : Option PUnit) = cond (decide condition) (some ⟨⟩) none := by
  cases ‹Decidable condition› <;> rfl

/-- InstCombineCasts.cpp:1163-1169 for arbitrary scalar integer widths:
    flagged `trunc (x xor y) to i1` becomes `x != y`. -/
public def flaggedXorTruncToICmpNe : Pattern OpCode :=
  Pattern.Builder
    (do
      let wideTy ← MatchProg.type (Attr := IntegerType)
      let boolTy ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
      let x ← MatchProg.value wideTy
      let y ← MatchProg.value wideTy
      let xored ← MatchProg.operation (.llvm .xor) #[x, y] #[wideTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .trunc) #[xored.res[0]!] #[boolTy]
        (fun props => props.nsw || props.nuw)
      return (boolTy, x, y))
    (fun (boolTy, x, y) => do
      let cmpProps ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk .ne)
      CreateProg.operation (.llvm .icmp) #[x, y] #[boolTy] cmpProps)
    (fun result => result.res[0]!)

public theorem flaggedXorTruncToICmpNe_valid : Pattern.Valid flaggedXorTruncToICmpNe := by
  simp only [flaggedXorTruncToICmpNe]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;>
      simp [properties_of, guard_eq_cond_punit, MatchProg.collectBindings,
        MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
        HandleContext.forbidMany, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
        MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
        CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨w, signedness⟩ boolType ⟨boolW, boolSignedness⟩ hBool hBoolW
  subst boolType; change boolW = 1 at hBoolW; subst boolW
  rintro x hX y hY
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  obtain ⟨y, rfl⟩ := RuntimeValue.Conforms.integerType.mp hY
  rintro _ xored hXored
  obtain rfl := (xor_iff w x y xored).mp hXored
  rintro truncProps source hFlags hSource
  obtain ⟨h1w, rfl⟩ := (trunc_iff w 1 truncProps _ source).mp hSource
  have hFlag : truncProps.nsw = true ∨ truncProps.nuw = true := by
    exact Bool.or_eq_true_iff.mp hFlags
  refine ⟨.int 1 (LLVM.Int.icmp x y .ne), ?_, ?_⟩
  · exact (icmp_iff _ (IcmpProperties.mk .ne) _ _ _).mpr rfl
  refine ⟨rfl, ?_⟩
  simpa only [LLVM.Int.cast_self] using
    trunc_xor_flags_refines_icmp_ne h1w x y truncProps.nsw truncProps.nuw hFlag

end Veir.Passes.InstCombineLLVM.FlaggedXorTruncToICmp

#print axioms Veir.Passes.InstCombineLLVM.FlaggedXorTruncToICmp.flaggedXorTruncToICmpNe_valid
