import Veir.InstSimplify.ArithmeticExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1322

/-- Scalar LLVM shl simplification with 0 on the right; all widths and flags. -/
def pattern_shl_right : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty 0
      let _ ← MatchProg.root (.llvm .shl) #[x,c] #[ty]
      return x)
    pure (fun x => x)

theorem pattern_shl_right_valid : Pattern.Valid pattern_shl_right := by
  simp only [pattern_shl_right, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hi hz
  obtain rfl := matched_bit_constant_eq _ cp 0 cv hc hz
  obtain rfl := (shl_iff w p x _ v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.shl, isRefinedBy, Id.run, pure]
  all_goals grind

/-- Scalar LLVM lshr simplification with 0 on the right; all widths and flags. -/
def pattern_lshr_right : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty 0
      let _ ← MatchProg.root (.llvm .lshr) #[x,c] #[ty]
      return x)
    pure (fun x => x)

theorem pattern_lshr_right_valid : Pattern.Valid pattern_lshr_right := by
  simp only [pattern_lshr_right, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hi hz
  obtain rfl := matched_bit_constant_eq _ cp 0 cv hc hz
  obtain rfl := (lshr_iff w p x _ v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.lshr, isRefinedBy, Id.run, pure]
  all_goals grind

/-- Scalar LLVM ashr simplification with 0 on the right; all widths and flags. -/
def pattern_ashr_right : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let c ← matchBitConstant ty 0
      let _ ← MatchProg.root (.llvm .ashr) #[x,c] #[ty]
      return x)
    pure (fun x => x)

theorem pattern_ashr_right_valid : Pattern.Valid pattern_ashr_right := by
  simp only [pattern_ashr_right, matchBitConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ x cp cv hc p v hi hz
  obtain rfl := matched_bit_constant_eq _ cp 0 cv hc hz
  obtain rfl := (ashr_iff w p x _ v).mp hi
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.ashr, isRefinedBy, Id.run, pure]
  all_goals grind

private theorem sext_one (w : Nat) (h : 1 < w) : BitVec.signExtend w (1#1) = BitVec.allOnes w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_signExtend]
private theorem sext_shl_refines (b : LLVM.Int 1) (x : LLVM.Int w) (h : 1 < w) (ns nu : Bool) :
    RuntimeValue.int w (LLVM.Int.shl x (LLVM.Int.sext b w h) ns nu) ⊒ .int w x := by
  cases b with
  | poison => cases x <;> simp [LLVM.Int.sext, LLVM.Int.shl, sext_one w h, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  | val b =>
    rcases BitVec.eq_zero_or_eq_one b with rfl | rfl
    · cases x <;> simp [LLVM.Int.sext, LLVM.Int.shl, sext_one w h, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
      grind
    · cases x <;> simp [LLVM.Int.sext, LLVM.Int.shl, sext_one w h, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
      grind

def pattern_sext_shl : Pattern OpCode :=
  Pattern.Builder
    (do
      let sty ← MatchProg.type (Attr := IntegerType)
      let ty ← MatchProg.type (Attr := IntegerType)
      let b ← MatchProg.value sty
      let x ← MatchProg.value ty
      let sh ← MatchProg.operation (.llvm .sext) #[b] #[ty]
      let _ ← MatchProg.root (.llvm .shl) #[x,sh.res[0]!] #[ty]
      MatchProg.matchNative sty (fun t => match t.val with
        | .integerType it => it.bitwidth == 1
        | _ => false)
      return x)
    pure (fun x => x)

theorem pattern_sext_shl_valid : Pattern.Valid pattern_sext_shl := by
  simp only [pattern_sext_shl]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨sw,ss⟩ ⟨w,s⟩ b x sp sv hs p v hi hw
  have hsw : sw = 1 := by
    change (sw == 1) = true at hw
    simpa using hw
  subst sw
  have hlt := sext_width_lt _ _ sp b sv hs
  obtain rfl := (sext_iff _ _ sp b sv hlt).mp hs
  obtain rfl := (shl_iff w p x _ v).mp hi
  exact sext_shl_refines _ _ _ _ _
private theorem sext_lshr_refines (b : LLVM.Int 1) (x : LLVM.Int w) (h : 1 < w) (ex : Bool) :
    RuntimeValue.int w (LLVM.Int.lshr x (LLVM.Int.sext b w h) ex) ⊒ .int w x := by
  cases b with
  | poison => cases x <;> simp [LLVM.Int.sext, LLVM.Int.lshr, sext_one w h, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  | val b =>
    rcases BitVec.eq_zero_or_eq_one b with rfl | rfl
    · cases x <;> simp [LLVM.Int.sext, LLVM.Int.lshr, sext_one w h, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
      grind
    · cases x <;> simp [LLVM.Int.sext, LLVM.Int.lshr, sext_one w h, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
      grind

def pattern_sext_lshr : Pattern OpCode :=
  Pattern.Builder
    (do
      let sty ← MatchProg.type (Attr := IntegerType)
      let ty ← MatchProg.type (Attr := IntegerType)
      let b ← MatchProg.value sty
      let x ← MatchProg.value ty
      let sh ← MatchProg.operation (.llvm .sext) #[b] #[ty]
      let _ ← MatchProg.root (.llvm .lshr) #[x,sh.res[0]!] #[ty]
      MatchProg.matchNative sty (fun t => match t.val with
        | .integerType it => it.bitwidth == 1
        | _ => false)
      return x)
    pure (fun x => x)

theorem pattern_sext_lshr_valid : Pattern.Valid pattern_sext_lshr := by
  simp only [pattern_sext_lshr]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨sw,ss⟩ ⟨w,s⟩ b x sp sv hs p v hi hw
  have hsw : sw = 1 := by
    change (sw == 1) = true at hw
    simpa using hw
  subst sw
  have hlt := sext_width_lt _ _ sp b sv hs
  obtain rfl := (sext_iff _ _ sp b sv hlt).mp hs
  obtain rfl := (lshr_iff w p x _ v).mp hi
  exact sext_lshr_refines _ _ _ _
private theorem sext_ashr_refines (b : LLVM.Int 1) (x : LLVM.Int w) (h : 1 < w) (ex : Bool) :
    RuntimeValue.int w (LLVM.Int.ashr x (LLVM.Int.sext b w h) ex) ⊒ .int w x := by
  cases b with
  | poison => cases x <;> simp [LLVM.Int.sext, LLVM.Int.ashr, sext_one w h, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
  | val b =>
    rcases BitVec.eq_zero_or_eq_one b with rfl | rfl
    · cases x <;> simp [LLVM.Int.sext, LLVM.Int.ashr, sext_one w h, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
      grind
    · cases x <;> simp [LLVM.Int.sext, LLVM.Int.ashr, sext_one w h, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
      grind

def pattern_sext_ashr : Pattern OpCode :=
  Pattern.Builder
    (do
      let sty ← MatchProg.type (Attr := IntegerType)
      let ty ← MatchProg.type (Attr := IntegerType)
      let b ← MatchProg.value sty
      let x ← MatchProg.value ty
      let sh ← MatchProg.operation (.llvm .sext) #[b] #[ty]
      let _ ← MatchProg.root (.llvm .ashr) #[x,sh.res[0]!] #[ty]
      MatchProg.matchNative sty (fun t => match t.val with
        | .integerType it => it.bitwidth == 1
        | _ => false)
      return x)
    pure (fun x => x)

theorem pattern_sext_ashr_valid : Pattern.Valid pattern_sext_ashr := by
  simp only [pattern_sext_ashr]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨sw,ss⟩ ⟨w,s⟩ b x sp sv hs p v hi hw
  have hsw : sw = 1 := by
    change (sw == 1) = true at hw
    simpa using hw
  subst sw
  have hlt := sext_width_lt _ _ sp b sv hs
  obtain rfl := (sext_iff _ _ sp b sv hlt).mp hs
  obtain rfl := (ashr_iff w p x _ v).mp hi
  exact sext_ashr_refines _ _ _ _
end Veir.InstSimplify.IS1322
