import Veir.InstSimplify.CmpNumericExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 8000000

/-- Scalar power-of-two shift versus a non-power-of-two literal, noSignedWrap safety branch. -/
def IS3514_noSignedWrap (base constant : Int) (bit : Nat) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t =>
      bit < t.bitwidth && BitVec.ofInt t.bitwidth base == BitVec.twoPow t.bitwidth bit &&
      !decide (BitVec.ofInt t.bitwidth constant).toNat.isPowerOfTwo)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let a ← matchIntConstant ty base
    let c ← matchIntConstant ty constant
    let shifted ← MatchProg.operation (.llvm .shl) #[a,x] #[ty] (fun p => p.nsw)
    let _ ← MatchProg.root (.llvm .icmp) #[shifted.res[0]!,c] #[cty] (fun p => p.predicate == .ne)
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 1 (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3514_noSignedWrap_valid (base constant : Int) (bit : Nat) : Pattern.Valid (IS3514_noSignedWrap base constant bit) := by
  simp only [IS3514_noSignedWrap, matchIntConstant]
  provePuddleValid
  rintro _ ⟨w,s⟩ rfl hg hb hc _ ⟨cw,cs⟩ rfl hw
  have : cw = 1 := by simpa using hw
  subst cw
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x ap av ah ai
  obtain rfl := (matched_constant_iff _ _ _ ah _).mp ai
  intro bp bv bh bi
  obtain rfl := (matched_constant_iff _ _ _ bh _).mp bi
  intro ip iv hi ii
  obtain rfl := (shl_iff _ _ _ _ _).mp ii
  intro cp cv ch ci
  obtain rfl := (icmp_iff _ _ _ _ _).mp ci
  refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
  have hp : cp.predicate = .ne := by simpa using ch
  have hbase : BitVec.ofInt w base = BitVec.twoPow w bit := by simpa using hb
  have hbit : bit < w := hg
  have hconst : ¬(BitVec.ofInt w constant).toNat.isPowerOfTwo := by simpa using hc
  have hsafe' : ip.nsw = true ∨ ip.nuw = true ∨ BitVec.twoPow w bit = 1#w ∨ BitVec.ofInt w constant ≠ 0#w := by
    exact Or.inl hi
  cases x with
  | poison => simp [LLVM.Int.shl, LLVM.Int.icmp, Id.run, RuntimeValue.isRefinedBy, isRefinedBy]
  | val x =>
    rw [hbase]
    rcases power_shift_ne_nonPower bit x (BitVec.ofInt w constant) ip.nsw ip.nuw hbit hconst hsafe' with hz | ⟨r,hr,hn⟩
    · simp [hz, LLVM.Int.icmp, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    · rw [hr]
      have he : (r == BitVec.ofInt w constant) = false := beq_eq_false_iff_ne.mpr hn
      simp [LLVM.Int.icmp, LLVM.IntPred.eval, hp, he, bne, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

/-- Scalar power-of-two shift versus a non-power-of-two literal, noUnsignedWrap safety branch. -/
def IS3514_noUnsignedWrap (base constant : Int) (bit : Nat) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t =>
      bit < t.bitwidth && BitVec.ofInt t.bitwidth base == BitVec.twoPow t.bitwidth bit &&
      !decide (BitVec.ofInt t.bitwidth constant).toNat.isPowerOfTwo)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let a ← matchIntConstant ty base
    let c ← matchIntConstant ty constant
    let shifted ← MatchProg.operation (.llvm .shl) #[a,x] #[ty] (fun p => p.nuw)
    let _ ← MatchProg.root (.llvm .icmp) #[shifted.res[0]!,c] #[cty] (fun p => p.predicate == .ne)
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 1 (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3514_noUnsignedWrap_valid (base constant : Int) (bit : Nat) : Pattern.Valid (IS3514_noUnsignedWrap base constant bit) := by
  simp only [IS3514_noUnsignedWrap, matchIntConstant]
  provePuddleValid
  rintro _ ⟨w,s⟩ rfl hg hb hc _ ⟨cw,cs⟩ rfl hw
  have : cw = 1 := by simpa using hw
  subst cw
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x ap av ah ai
  obtain rfl := (matched_constant_iff _ _ _ ah _).mp ai
  intro bp bv bh bi
  obtain rfl := (matched_constant_iff _ _ _ bh _).mp bi
  intro ip iv hi ii
  obtain rfl := (shl_iff _ _ _ _ _).mp ii
  intro cp cv ch ci
  obtain rfl := (icmp_iff _ _ _ _ _).mp ci
  refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
  have hp : cp.predicate = .ne := by simpa using ch
  have hbase : BitVec.ofInt w base = BitVec.twoPow w bit := by simpa using hb
  have hbit : bit < w := hg
  have hconst : ¬(BitVec.ofInt w constant).toNat.isPowerOfTwo := by simpa using hc
  have hsafe' : ip.nsw = true ∨ ip.nuw = true ∨ BitVec.twoPow w bit = 1#w ∨ BitVec.ofInt w constant ≠ 0#w := by
    exact Or.inr (Or.inl hi)
  cases x with
  | poison => simp [LLVM.Int.shl, LLVM.Int.icmp, Id.run, RuntimeValue.isRefinedBy, isRefinedBy]
  | val x =>
    rw [hbase]
    rcases power_shift_ne_nonPower bit x (BitVec.ofInt w constant) ip.nsw ip.nuw hbit hconst hsafe' with hz | ⟨r,hr,hn⟩
    · simp [hz, LLVM.Int.icmp, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    · rw [hr]
      have he : (r == BitVec.ofInt w constant) = false := beq_eq_false_iff_ne.mpr hn
      simp [LLVM.Int.icmp, LLVM.IntPred.eval, hp, he, bne, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

/-- Scalar power-of-two shift versus a non-power-of-two literal, baseOne safety branch. -/
def IS3514_baseOne (base constant : Int) (bit : Nat) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t =>
      bit < t.bitwidth && BitVec.ofInt t.bitwidth base == BitVec.twoPow t.bitwidth bit &&
      !decide (BitVec.ofInt t.bitwidth constant).toNat.isPowerOfTwo && BitVec.ofInt t.bitwidth base == 1)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let a ← matchIntConstant ty base
    let c ← matchIntConstant ty constant
    let shifted ← MatchProg.operation (.llvm .shl) #[a,x] #[ty]
    let _ ← MatchProg.root (.llvm .icmp) #[shifted.res[0]!,c] #[cty] (fun p => p.predicate == .ne)
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 1 (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3514_baseOne_valid (base constant : Int) (bit : Nat) : Pattern.Valid (IS3514_baseOne base constant bit) := by
  simp only [IS3514_baseOne, matchIntConstant]
  provePuddleValid
  rintro _ ⟨w,s⟩ rfl hg hb hc hsafe _ ⟨cw,cs⟩ rfl hw
  have : cw = 1 := by simpa using hw
  subst cw
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x ap av ah ai
  obtain rfl := (matched_constant_iff _ _ _ ah _).mp ai
  intro bp bv bh bi
  obtain rfl := (matched_constant_iff _ _ _ bh _).mp bi
  intro ip iv ii
  obtain rfl := (shl_iff _ _ _ _ _).mp ii
  intro cp cv ch ci
  obtain rfl := (icmp_iff _ _ _ _ _).mp ci
  refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
  have hp : cp.predicate = .ne := by simpa using ch
  have hbase : BitVec.ofInt w base = BitVec.twoPow w bit := by simpa using hb
  have hbit : bit < w := hg
  have hconst : ¬(BitVec.ofInt w constant).toNat.isPowerOfTwo := by simpa using hc
  have hsafe' : ip.nsw = true ∨ ip.nuw = true ∨ BitVec.twoPow w bit = 1#w ∨ BitVec.ofInt w constant ≠ 0#w := by
    exact Or.inr (Or.inr (Or.inl (hbase.symm.trans hsafe)))
  cases x with
  | poison => simp [LLVM.Int.shl, LLVM.Int.icmp, Id.run, RuntimeValue.isRefinedBy, isRefinedBy]
  | val x =>
    rw [hbase]
    rcases power_shift_ne_nonPower bit x (BitVec.ofInt w constant) ip.nsw ip.nuw hbit hconst hsafe' with hz | ⟨r,hr,hn⟩
    · simp [hz, LLVM.Int.icmp, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    · rw [hr]
      have he : (r == BitVec.ofInt w constant) = false := beq_eq_false_iff_ne.mpr hn
      simp [LLVM.Int.icmp, LLVM.IntPred.eval, hp, he, bne, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

/-- Scalar power-of-two shift versus a non-power-of-two literal, nonzeroRHS safety branch. -/
def IS3514_nonzeroRHS (base constant : Int) (bit : Nat) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t =>
      bit < t.bitwidth && BitVec.ofInt t.bitwidth base == BitVec.twoPow t.bitwidth bit &&
      !decide (BitVec.ofInt t.bitwidth constant).toNat.isPowerOfTwo && BitVec.ofInt t.bitwidth constant != 0)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let a ← matchIntConstant ty base
    let c ← matchIntConstant ty constant
    let shifted ← MatchProg.operation (.llvm .shl) #[a,x] #[ty]
    let _ ← MatchProg.root (.llvm .icmp) #[shifted.res[0]!,c] #[cty] (fun p => p.predicate == .ne)
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 1 (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3514_nonzeroRHS_valid (base constant : Int) (bit : Nat) : Pattern.Valid (IS3514_nonzeroRHS base constant bit) := by
  simp only [IS3514_nonzeroRHS, matchIntConstant]
  provePuddleValid
  rintro _ ⟨w,s⟩ rfl hg hb hc hsafe _ ⟨cw,cs⟩ rfl hw
  have : cw = 1 := by simpa using hw
  subst cw
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x ap av ah ai
  obtain rfl := (matched_constant_iff _ _ _ ah _).mp ai
  intro bp bv bh bi
  obtain rfl := (matched_constant_iff _ _ _ bh _).mp bi
  intro ip iv ii
  obtain rfl := (shl_iff _ _ _ _ _).mp ii
  intro cp cv ch ci
  obtain rfl := (icmp_iff _ _ _ _ _).mp ci
  refine ⟨_, (constant_iff _ _ _ rfl _).mpr rfl, ?_⟩
  have hp : cp.predicate = .ne := by simpa using ch
  have hbase : BitVec.ofInt w base = BitVec.twoPow w bit := by simpa using hb
  have hbit : bit < w := hg
  have hconst : ¬(BitVec.ofInt w constant).toNat.isPowerOfTwo := by simpa using hc
  have hsafe' : ip.nsw = true ∨ ip.nuw = true ∨ BitVec.twoPow w bit = 1#w ∨ BitVec.ofInt w constant ≠ 0#w := by
    exact Or.inr (Or.inr (Or.inr (by simpa using hsafe)))
  cases x with
  | poison => simp [LLVM.Int.shl, LLVM.Int.icmp, Id.run, RuntimeValue.isRefinedBy, isRefinedBy]
  | val x =>
    rw [hbase]
    rcases power_shift_ne_nonPower bit x (BitVec.ofInt w constant) ip.nsw ip.nuw hbit hconst hsafe' with hz | ⟨r,hr,hn⟩
    · simp [hz, LLVM.Int.icmp, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
    · rw [hr]
      have he : (r == BitVec.ofInt w constant) = false := beq_eq_false_iff_ne.mpr hn
      simp [LLVM.Int.icmp, LLVM.IntPred.eval, hp, he, bne, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def IS3514 (safety : PowerShiftSafety) (base constant : Int) (bit : Nat) : Pattern OpCode :=
  match safety with
  | .noSignedWrap => IS3514_noSignedWrap base constant bit
  | .noUnsignedWrap => IS3514_noUnsignedWrap base constant bit
  | .baseOne => IS3514_baseOne base constant bit
  | .nonzeroRHS => IS3514_nonzeroRHS base constant bit

theorem IS3514_valid (safety : PowerShiftSafety) (base constant : Int) (bit : Nat) : Pattern.Valid (IS3514 safety base constant bit) := by
  cases safety
  · exact IS3514_noSignedWrap_valid base constant bit
  · exact IS3514_noUnsignedWrap_valid base constant bit
  · exact IS3514_baseOne_valid base constant bit
  · exact IS3514_nonzeroRHS_valid base constant bit
end Veir.InstSimplify
