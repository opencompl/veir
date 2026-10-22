import Veir.InstSimplify.LogicSupport
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS1643
def contains (w : Nat) (p0 p1 : LLVM.IntPred) (c0 c1 : Int) : Bool :=
  decide (∀ x : BitVec w, (LLVM.IntPred.eval p0 x (BitVec.ofInt w c0) ||
    LLVM.IntPred.eval p1 x (BitVec.ofInt w c1)) = true)

def pattern (p0 p1 : LLVM.IntPred) (k0 k1 : Int) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let k0v ← matchIntConstant ty k0
    let k1v ← matchIntConstant ty k1
    let c0 ← MatchProg.operation (.llvm .icmp) #[x,k0v] #[bt]
      (fun p => p.predicate == p0)
    let c1 ← MatchProg.operation (.llvm .icmp) #[x,k1v] #[bt]
      (fun p => p.predicate == p1)
    let _ ← MatchProg.root (.llvm .or) #[c0.res[0]!,c1.res[0]!] #[bt]
    MatchProg.matchNative (ty,bt) (fun (ty,bt) =>
      match ty.val,bt.val with
      | .integerType t, .integerType b => b.bitwidth == 1 && contains t.bitwidth p0 p1 k0 k1
      | _,_ => false)
    return bt)
  (fun bt => do
    let p ← CreateProg.applyNative bt (fun bt => match bt.val with
      | .integerType t => some ({value := .integer (IntegerAttr.ofInt 1 t)} : propertiesOf (.llvm .mlir__constant : OpCode))
      | _ => none)
    let c ← CreateProg.operation (.llvm .mlir__constant) #[] #[bt] p
    return c.res[0]!) (fun x => x)

theorem semantic (w : Nat) (x : LLVM.Int w) (p0 p1 : LLVM.IntPred) (k0 k1 : Int) (d : Bool)
    (hc : contains w p0 p1 k0 k1 = true) :
    RuntimeValue.int 1 (LLVM.Int.or
      (LLVM.Int.icmp x (.val (BitVec.ofInt w k0)) p0)
      (LLVM.Int.icmp x (.val (BitVec.ofInt w k1)) p1) d) ⊒
    .int 1 (.val (BitVec.ofInt 1 1)) := by
  have hc := of_decide_eq_true hc
  cases x with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.or, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
  | val x =>
    have hx := hc x
    cases h0 : LLVM.IntPred.eval p0 x (BitVec.ofInt w k0) <;>
      cases h1 : LLVM.IntPred.eval p1 x (BitVec.ofInt w k1) <;>
      cases d <;>
      simp_all [LLVM.Int.icmp, LLVM.Int.or, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure, BitVec.ofBool]

theorem valid (p0 p1 : LLVM.IntPred) (k0 k1 : Int) : Pattern.Valid (pattern p0 p1 k0 k1) := by
  simp only [pattern, matchIntConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w,s⟩ ⟨bw,bs⟩ x
  intro kp0 kv0 hk0 hi0
  obtain rfl := matched_constant_eq _ _ k0 _ hk0 hi0
  intro kp1 kv1 hk1 hi1
  obtain rfl := matched_constant_eq _ _ k1 _ hk1 hi1
  intro cp0 cv0 hp0 hi0
  have hp0 : cp0.predicate = p0 := by simpa using hp0
  intro cp1 cv1 hp1 hi1
  have hp1 : cp1.predicate = p1 := by simpa using hp1
  intro rp rv hir hc
  have hc : bw = 1 ∧ contains w p0 p1 k0 k1 = true := by simpa [TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of] using hc
  obtain ⟨rfl,hc⟩ := hc
  obtain rfl := (logic_icmp_iff _ _ _ _ _).mp hi0
  obtain rfl := (logic_icmp_iff _ _ _ _ _).mp hi1
  obtain rfl := (or_iff _ _ _ _ _).mp hir
  refine ⟨.int 1 (.val (BitVec.ofInt 1 1)), ?_, ?_⟩
  · exact (constant_iff _ _ _ rfl _).mpr (by cases bs <;> decide)
  · simpa [hp0,hp1] using semantic w x p0 p1 k0 k1 rp.disjoint hc
end Veir.InstSimplify.IS1643
