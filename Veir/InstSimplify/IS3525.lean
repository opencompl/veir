import Veir.InstSimplify.CmpNumericExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 8000000
/-- A shifted power of two cannot exceed the unsigned sign mask, at any scalar width. -/
def IS3525 (base mask : Int) (bit : Nat) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t =>
      bit < t.bitwidth && BitVec.ofInt t.bitwidth base == BitVec.twoPow t.bitwidth bit &&
      BitVec.ofInt t.bitwidth mask == BitVec.intMin t.bitwidth)
    let cty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
    let x ← MatchProg.value ty
    let ca ← matchIntConstant ty base
    let cb ← matchIntConstant ty mask
    let shifted ← MatchProg.operation (.llvm .shl) #[ca,x] #[ty]
    let _ ← MatchProg.root (.llvm .icmp) #[shifted.res[0]!,cb] #[cty] (fun p => p.predicate == .ule)
    return cty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__constant)
      (LLVMConstantProperties.mk (.integer (IntegerAttr.mk 1 (IntegerType.signless 1))))
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun x => x)

theorem IS3525_valid (base mask : Int) (bit : Nat) : Pattern.Valid (IS3525 base mask bit) := by
  simp only [IS3525, matchIntConstant]
  provePuddleValid
  rintro _ ⟨w,s⟩ rfl hg hb hm _ ⟨cw,cs⟩ rfl hw
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
  have hp : cp.predicate = .ule := by simpa using ch
  have hbase : BitVec.ofInt w base = BitVec.twoPow w bit := by simpa using hb
  have hmask : BitVec.ofInt w mask = BitVec.intMin w := by simpa using hm
  cases x with
  | poison => simp [LLVM.Int.shl, LLVM.Int.icmp, Id.run, RuntimeValue.isRefinedBy, isRefinedBy]
  | val x =>
    rcases shl_scalar_cases (.val (BitVec.ofInt w base)) x ip.nsw ip.nuw with hz | ⟨v,hv,hw,hs⟩
    · simp [hz, LLVM.Int.icmp, Id.run, RuntimeValue.isRefinedBy, isRefinedBy]
    · cases hv
      have hbnd := twoPow_le_signmask (w := w) (bit + x.toNat)
      have hu : (BitVec.twoPow w (bit + x.toNat)).ule (BitVec.intMin w) = true := by
        simpa only [BitVec.ule, decide_eq_true_eq] using hbnd
      have hl : (BitVec.intMin w).ult (BitVec.twoPow w (bit + x.toNat)) = false := by
        simp only [BitVec.ult, decide_eq_false_iff_not]
        omega
      rw [hs, hbase, hmask, shift_twoPow]
      simp [ LLVM.Int.icmp, LLVM.IntPred.eval, hp, hu, hl,
        Id.run, RuntimeValue.isRefinedBy, isRefinedBy]
end Veir.InstSimplify
