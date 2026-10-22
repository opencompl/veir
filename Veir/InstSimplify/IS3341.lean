import Veir.InstSimplify.CmpNumericExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 8000000
/-- Three scalar scaled-quotient bounds, preserving all overflow and exact flags. -/
def IS3341_mulUdiv (a b : Int) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t =>
      let av := BitVec.ofInt t.bitwidth a
      let bv := BitVec.ofInt t.bitwidth b
      av.ule bv)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let ca ← matchIntConstant ty a
    let cb ← matchIntConstant ty b
    let inner ← MatchProg.operation (.llvm .mul) #[x,ca] #[ty]
    let outer ← MatchProg.operation (.llvm .udiv) #[inner.res[0]!,cb] #[ty]
    let _ ← MatchProg.root (.llvm .icmp) #[outer.res[0]!,x] #[cty] (fun p => p.predicate == .ugt)
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3341_mulUdiv_valid (a b : Int) : Pattern.Valid (IS3341_mulUdiv a b) := by
  simp only [IS3341_mulUdiv, matchIntConstant]
  provePuddleValid
  rintro _ ⟨w,s⟩ rfl hc _ ⟨cw,cs⟩ rfl hw
  have : cw = 1 := by simpa using hw
  subst cw
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x ap av ah ai
  obtain rfl := (matched_constant_iff _ _ _ ah _).mp ai
  intro bp bv bh bi
  obtain rfl := (matched_constant_iff _ _ _ bh _).mp bi
  intro ip iv ii
  obtain rfl := (mul_iff _ _ _ _ _).mp ii
  intro dp dv di
  obtain ⟨_,rfl⟩ := (udiv_iff _ _ _ _ _).mp di
  intro cp cv ch ci
  obtain rfl := (icmp_iff _ _ _ _ _).mp ci
  refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
  have hp : cp.predicate = .ugt := by simpa using ch
  rcases mul_udiv_scalar_bound x (BitVec.ofInt w a) (BitVec.ofInt w b) ip.nsw ip.nuw dp.exact (by simpa using hc) with hz | ⟨v,r,hx,hr,hbound⟩
  · simp [hz, LLVM.Int.icmp, hp, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · rw [hr, hx]
    have hu : r.ule v = true := by simpa only [BitVec.ule, decide_eq_true_eq] using hbound
    have hl : v.ult r = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not]
      omega
    simp [LLVM.Int.icmp, LLVM.IntPred.eval, hp, hu, hl, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
/-- Three scalar scaled-quotient bounds, preserving all overflow and exact flags. -/
def IS3341_mulLshr (a b : Int) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t =>
      let av := BitVec.ofInt t.bitwidth a
      let bv := BitVec.ofInt t.bitwidth b
      av.ule (BitVec.twoPow t.bitwidth bv.toNat))
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let ca ← matchIntConstant ty a
    let cb ← matchIntConstant ty b
    let inner ← MatchProg.operation (.llvm .mul) #[x,ca] #[ty]
    let outer ← MatchProg.operation (.llvm .lshr) #[inner.res[0]!,cb] #[ty]
    let _ ← MatchProg.root (.llvm .icmp) #[outer.res[0]!,x] #[cty] (fun p => p.predicate == .ugt)
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3341_mulLshr_valid (a b : Int) : Pattern.Valid (IS3341_mulLshr a b) := by
  simp only [IS3341_mulLshr, matchIntConstant]
  provePuddleValid
  rintro _ ⟨w,s⟩ rfl hc _ ⟨cw,cs⟩ rfl hw
  have : cw = 1 := by simpa using hw
  subst cw
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x ap av ah ai
  obtain rfl := (matched_constant_iff _ _ _ ah _).mp ai
  intro bp bv bh bi
  obtain rfl := (matched_constant_iff _ _ _ bh _).mp bi
  intro ip iv ii
  obtain rfl := (mul_iff _ _ _ _ _).mp ii
  intro dp dv di
  obtain rfl := (lshr_iff _ _ _ _ _).mp di
  intro cp cv ch ci
  obtain rfl := (icmp_iff _ _ _ _ _).mp ci
  refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
  have hp : cp.predicate = .ugt := by simpa using ch
  rcases mul_lshr_scalar_bound x (BitVec.ofInt w a) (BitVec.ofInt w b) ip.nsw ip.nuw dp.exact (by simpa using hc) with hz | ⟨v,r,hx,hr,hbound⟩
  · simp [hz, LLVM.Int.icmp, hp, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · rw [hr, hx]
    have hu : r.ule v = true := by simpa only [BitVec.ule, decide_eq_true_eq] using hbound
    have hl : v.ult r = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not]
      omega
    simp [LLVM.Int.icmp, LLVM.IntPred.eval, hp, hu, hl, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
/-- Three scalar scaled-quotient bounds, preserving all overflow and exact flags. -/
def IS3341_shlUdiv (a b : Int) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t =>
      let av := BitVec.ofInt t.bitwidth a
      let bv := BitVec.ofInt t.bitwidth b
      (BitVec.twoPow t.bitwidth av.toNat).ule bv)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let ca ← matchIntConstant ty a
    let cb ← matchIntConstant ty b
    let inner ← MatchProg.operation (.llvm .shl) #[x,ca] #[ty]
    let outer ← MatchProg.operation (.llvm .udiv) #[inner.res[0]!,cb] #[ty]
    let _ ← MatchProg.root (.llvm .icmp) #[outer.res[0]!,x] #[cty] (fun p => p.predicate == .ugt)
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 0 (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3341_shlUdiv_valid (a b : Int) : Pattern.Valid (IS3341_shlUdiv a b) := by
  simp only [IS3341_shlUdiv, matchIntConstant]
  provePuddleValid
  rintro _ ⟨w,s⟩ rfl hc _ ⟨cw,cs⟩ rfl hw
  have : cw = 1 := by simpa using hw
  subst cw
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x ap av ah ai
  obtain rfl := (matched_constant_iff _ _ _ ah _).mp ai
  intro bp bv bh bi
  obtain rfl := (matched_constant_iff _ _ _ bh _).mp bi
  intro ip iv ii
  obtain rfl := (shl_iff _ _ _ _ _).mp ii
  intro dp dv di
  obtain ⟨_,rfl⟩ := (udiv_iff _ _ _ _ _).mp di
  intro cp cv ch ci
  obtain rfl := (icmp_iff _ _ _ _ _).mp ci
  refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
  have hp : cp.predicate = .ugt := by simpa using ch
  rcases shl_udiv_scalar_bound x (BitVec.ofInt w a) (BitVec.ofInt w b) ip.nsw ip.nuw dp.exact (by simpa using hc) with hz | ⟨v,r,hx,hr,hbound⟩
  · simp [hz, LLVM.Int.icmp, hp, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · rw [hr, hx]
    have hu : r.ule v = true := by simpa only [BitVec.ule, decide_eq_true_eq] using hbound
    have hl : v.ult r = false := by
      simp only [BitVec.ult, decide_eq_false_iff_not]
      omega
    simp [LLVM.Int.icmp, LLVM.IntPred.eval, hp, hu, hl, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def IS3341 (shape : ScaledCmpShape) (a b : Int) : Pattern OpCode :=
  match shape with
  | .mulUdiv => IS3341_mulUdiv a b
  | .mulLshr => IS3341_mulLshr a b
  | .shlUdiv => IS3341_shlUdiv a b

theorem IS3341_valid (shape : ScaledCmpShape) (a b : Int) : Pattern.Valid (IS3341 shape a b) := by
  cases shape
  · exact IS3341_mulUdiv_valid a b
  · exact IS3341_mulLshr_valid a b
  · exact IS3341_shlUdiv_valid a b
end Veir.InstSimplify
