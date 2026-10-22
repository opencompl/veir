import Veir.InstSimplify.CastLogicSupport
set_option maxHeartbeats 0
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS2334

def matchLogicalAnd (select commute : Bool) (ty : Handle OpCode .type)
    (a b z : Handle OpCode .value) : MatchProg.Builder (Handle OpCode .value) := do
  match select with
  | false =>
    let op ← MatchProg.operation (.llvm .and) (cond commute #[b,a] #[a,b]) #[ty]
    return op.res[0]!
  | true =>
    let op ← MatchProg.operation (.llvm .select) (cond commute #[b,a,z] #[a,b,z]) #[ty]
    return op.res[0]!

def matchLogicalOr (select commute : Bool) (ty : Handle OpCode .type)
    (a b o : Handle OpCode .value) : MatchProg.Builder (Handle OpCode .value) := do
  match select with
  | false =>
    let op ← MatchProg.operation (.llvm .or) (cond commute #[b,a] #[a,b]) #[ty]
    return op.res[0]!
  | true =>
    let op ← MatchProg.operation (.llvm .select) (cond commute #[b,o,a] #[a,o,b]) #[ty]
    return op.res[0]!

/-- Both logical operators may independently be bitwise operations or poison-masking selects. -/
def pattern (selectAnd selectOr swapAnd swapOr swapRoot swapNotA swapNotOr : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let ones ← matchBitConstant ty (-1)
    let zero ← match selectAnd with
      | true => matchBitConstant ty 0
      | false => pure ones
    let na ← MatchProg.operation (.llvm .xor) (cond swapNotA #[ones,a] #[a,ones]) #[ty]
    let x ← matchLogicalAnd selectAnd swapAnd ty na.res[0]! b zero
    let y ← matchLogicalOr selectOr swapOr ty a b ones
    let ny ← MatchProg.operation (.llvm .xor) (cond swapNotOr #[ones,y] #[y,ones]) #[ty]
    let _ ← MatchProg.root (.llvm .or) (cond swapRoot #[ny.res[0]!,x] #[x,ny.res[0]!]) #[ty]
    MatchProg.matchNative ty (fun ty => match ty.val with | .integerType t => t.bitwidth == 1 | _ => false)
    return na.res[0]!) pure (fun x => x)

theorem valid (selectAnd selectOr swapAnd swapOr swapRoot swapNotA swapNotOr : Bool) :
    Pattern.Valid (pattern selectAnd selectOr swapAnd swapOr swapRoot swapNotA swapNotOr) := by
  cases selectAnd <;> cases selectOr <;> cases swapAnd <;> cases swapOr <;> cases swapRoot <;> cases swapNotA <;> cases swapNotOr
  all_goals
    simp only [pattern,matchLogicalAnd,matchLogicalOr,matchBitConstant]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType,forall_exists_index,forall_eq_apply_imp_iff]
    first
    | rintro ⟨w,s⟩ a b op ov hoi zp zv hzi np nv hni xp xv hxi yp yv hyi nyp nyv hnyi rp rv hri ho hz hw
    | rintro ⟨w,s⟩ a b op ov hoi np nv hni xp xv hxi yp yv hyi nyp nyv hnyi rp rv hri ho hw
    have hw : w = 1 := by simpa [TypeAttr.of_val,Attribute.of,-Attribute.integerType_eq_of] using hw
    subst w
    obtain rfl := matched_bit_constant_eq _ _ (-1) _ hoi ho
    try obtain rfl := matched_bit_constant_eq _ _ 0 _ hzi hz
    obtain rfl := (xor_iff _ _ _ _ _).mp hni
    first
    | obtain rfl := (and_iff _ _ _ _ _).mp hxi
    | obtain rfl := (select_iff _ _ _ _ _ _).mp hxi
    first
    | obtain rfl := (or_iff _ _ _ _ _).mp hyi
    | obtain rfl := (select_iff _ _ _ _ _ _).mp hyi
    obtain rfl := (xor_iff _ _ _ _ _).mp hnyi
    obtain rfl := (or_iff _ _ _ _ _).mp hri
    rcases int1_cases a with rfl | rfl | rfl <;>
      rcases int1_cases b with rfl | rfl | rfl
    all_goals first | cases hy : yp.disjoint | skip
    all_goals cases hr : rp.disjoint
    all_goals simp [LLVM.Int.and,LLVM.Int.or,LLVM.Int.xor,LLVM.Int.select,RuntimeValue.isRefinedBy,isRefinedBy,Id.run, pure, *]
end Veir.InstSimplify.IS2334
