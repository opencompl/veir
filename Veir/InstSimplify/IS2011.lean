import Veir.InstSimplify.LogicExtra
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS2011

def pattern_and (c : Int) (commute : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let c0 ← matchBitConstant ty c
    let c1 ← matchBitConstant ty (-c-1)
    let x ← MatchProg.operation (.llvm .add) #[a,c0] #[ty]
    let y ← MatchProg.operation (.llvm .sub) #[c1,a] #[ty]
    let _ ← MatchProg.root (.llvm .and) (cond commute #[y.res[0]!,x.res[0]!] #[x.res[0]!,y.res[0]!]) #[ty]
    return ty)
  (fun ty => do
    let p ← CreateProg.applyNative ty (fun ty => match ty.val with
      | .integerType t => some ({value := .integer (IntegerAttr.ofInt (0) t)} : propertiesOf (.llvm .mlir__constant : OpCode))
      | _ => none)
    let c ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p
    return c.res[0]!) (fun x => x)

theorem semantic_and (w : Nat) (a : LLVM.Int w) (c : BitVec w) (nswa nuwa nsws nuws d : Bool) :
    RuntimeValue.int w (LLVM.Int.and (LLVM.Int.add a (.val c) nswa nuwa)
      (LLVM.Int.sub (.val (~~~c)) a nsws nuws)) ⊒ .int w (.val (BitVec.ofInt w (0))) := by
  cases a with
  | poison => simp [LLVM.Int.add, LLVM.Int.sub, LLVM.Int.and, Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy]
  | val a =>
    rcases add_outcomes a c nswa nuwa with ha | ha <;>
      rcases sub_outcomes (~~~c) a nsws nuws with hs | hs <;>
      simp [ha,hs,LLVM.Int.and,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy,const_negOne,complement_sub, ← BitVec.not_xor_right]

theorem valid_and (c : Int) (commute : Bool) : Pattern.Valid (pattern_and c commute) := by
  cases commute <;> (all_goals
    simp only [pattern_and,matchBitConstant]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType,forall_exists_index,forall_eq_apply_imp_iff]
    rintro ⟨w,s⟩ a p0 v0 hi0 p1 v1 hi1 xp xv hxi yp yv hyi rp rv hri hc0 hc1
    obtain rfl := matched_bit_constant_eq _ _ c _ hi0 hc0
    obtain rfl := matched_bit_constant_eq _ _ (-c-1) _ hi1 hc1
    obtain rfl := (add_iff _ _ _ _ _).mp hxi
    obtain rfl := (sub_iff _ _ _ _ _).mp hyi
    obtain rfl := (and_iff _ _ _ _ _).mp hri
    refine ⟨.int w (.val (BitVec.ofInt w (0))), ?_, ?_⟩
    · apply (constant_iff _ _ _ rfl _).mpr
      exact congrArg (fun b => RuntimeValue.int w (.val b)) (integerAttr_bits ⟨w,s⟩ (0)).symm
    · simpa only [ofInt_complement,logic_and_comm,logic_or_comm,logic_xor_comm] using semantic_and w a (BitVec.ofInt w c) xp.nsw xp.nuw yp.nsw yp.nuw false)

def pattern_or (c : Int) (commute : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let c0 ← matchBitConstant ty c
    let c1 ← matchBitConstant ty (-c-1)
    let x ← MatchProg.operation (.llvm .add) #[a,c0] #[ty]
    let y ← MatchProg.operation (.llvm .sub) #[c1,a] #[ty]
    let _ ← MatchProg.root (.llvm .or) (cond commute #[y.res[0]!,x.res[0]!] #[x.res[0]!,y.res[0]!]) #[ty]
    return ty)
  (fun ty => do
    let p ← CreateProg.applyNative ty (fun ty => match ty.val with
      | .integerType t => some ({value := .integer (IntegerAttr.ofInt (-1) t)} : propertiesOf (.llvm .mlir__constant : OpCode))
      | _ => none)
    let c ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p
    return c.res[0]!) (fun x => x)

theorem semantic_or (w : Nat) (a : LLVM.Int w) (c : BitVec w) (nswa nuwa nsws nuws d : Bool) :
    RuntimeValue.int w (LLVM.Int.or (LLVM.Int.add a (.val c) nswa nuwa)
      (LLVM.Int.sub (.val (~~~c)) a nsws nuws) d) ⊒ .int w (.val (BitVec.ofInt w (-1))) := by
  cases a with
  | poison => simp [LLVM.Int.add, LLVM.Int.sub, LLVM.Int.or, Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy]
  | val a =>
    rcases add_outcomes a c nswa nuwa with ha | ha <;>
      rcases sub_outcomes (~~~c) a nsws nuws with hs | hs <;>
      simp [ha,hs,LLVM.Int.or,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy,const_negOne,complement_sub, ← BitVec.not_xor_right]

theorem valid_or (c : Int) (commute : Bool) : Pattern.Valid (pattern_or c commute) := by
  cases commute <;> (all_goals
    simp only [pattern_or,matchBitConstant]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType,forall_exists_index,forall_eq_apply_imp_iff]
    rintro ⟨w,s⟩ a p0 v0 hi0 p1 v1 hi1 xp xv hxi yp yv hyi rp rv hri hc0 hc1
    obtain rfl := matched_bit_constant_eq _ _ c _ hi0 hc0
    obtain rfl := matched_bit_constant_eq _ _ (-c-1) _ hi1 hc1
    obtain rfl := (add_iff _ _ _ _ _).mp hxi
    obtain rfl := (sub_iff _ _ _ _ _).mp hyi
    obtain rfl := (or_iff _ _ _ _ _).mp hri
    refine ⟨.int w (.val (BitVec.ofInt w (-1))), ?_, ?_⟩
    · apply (constant_iff _ _ _ rfl _).mpr
      exact congrArg (fun b => RuntimeValue.int w (.val b)) (integerAttr_bits ⟨w,s⟩ (-1)).symm
    · simpa only [ofInt_complement,logic_and_comm,logic_or_comm,logic_xor_comm] using semantic_or w a (BitVec.ofInt w c) xp.nsw xp.nuw yp.nsw yp.nuw rp.disjoint)

def pattern_xor (c : Int) (commute : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let a ← MatchProg.value ty
    let c0 ← matchBitConstant ty c
    let c1 ← matchBitConstant ty (-c-1)
    let x ← MatchProg.operation (.llvm .add) #[a,c0] #[ty]
    let y ← MatchProg.operation (.llvm .sub) #[c1,a] #[ty]
    let _ ← MatchProg.root (.llvm .xor) (cond commute #[y.res[0]!,x.res[0]!] #[x.res[0]!,y.res[0]!]) #[ty]
    return ty)
  (fun ty => do
    let p ← CreateProg.applyNative ty (fun ty => match ty.val with
      | .integerType t => some ({value := .integer (IntegerAttr.ofInt (-1) t)} : propertiesOf (.llvm .mlir__constant : OpCode))
      | _ => none)
    let c ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p
    return c.res[0]!) (fun x => x)

theorem semantic_xor (w : Nat) (a : LLVM.Int w) (c : BitVec w) (nswa nuwa nsws nuws d : Bool) :
    RuntimeValue.int w (LLVM.Int.xor (LLVM.Int.add a (.val c) nswa nuwa)
      (LLVM.Int.sub (.val (~~~c)) a nsws nuws)) ⊒ .int w (.val (BitVec.ofInt w (-1))) := by
  cases a with
  | poison => simp [LLVM.Int.add, LLVM.Int.sub, LLVM.Int.xor, Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy]
  | val a =>
    rcases add_outcomes a c nswa nuwa with ha | ha <;>
      rcases sub_outcomes (~~~c) a nsws nuws with hs | hs <;>
      simp [ha,hs,LLVM.Int.xor,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy,const_negOne,complement_sub, ← BitVec.not_xor_right]

theorem valid_xor (c : Int) (commute : Bool) : Pattern.Valid (pattern_xor c commute) := by
  cases commute <;> (all_goals
    simp only [pattern_xor,matchBitConstant]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType,forall_exists_index,forall_eq_apply_imp_iff]
    rintro ⟨w,s⟩ a p0 v0 hi0 p1 v1 hi1 xp xv hxi yp yv hyi rp rv hri hc0 hc1
    obtain rfl := matched_bit_constant_eq _ _ c _ hi0 hc0
    obtain rfl := matched_bit_constant_eq _ _ (-c-1) _ hi1 hc1
    obtain rfl := (add_iff _ _ _ _ _).mp hxi
    obtain rfl := (sub_iff _ _ _ _ _).mp hyi
    obtain rfl := (xor_iff _ _ _ _ _).mp hri
    refine ⟨.int w (.val (BitVec.ofInt w (-1))), ?_, ?_⟩
    · apply (constant_iff _ _ _ rfl _).mpr
      exact congrArg (fun b => RuntimeValue.int w (.val b)) (integerAttr_bits ⟨w,s⟩ (-1)).symm
    · simpa only [ofInt_complement,logic_and_comm,logic_or_comm,logic_xor_comm] using semantic_xor w a (BitVec.ofInt w c) xp.nsw xp.nuw yp.nsw yp.nuw false)
end Veir.InstSimplify.IS2011
