module
public import Veir.Passes.InstCombineLLVM.CompareSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
import all Veir.Interfaces.ConstantLikeInterfaces
namespace Veir.Passes.InstCombineLLVM.XorMoveConstant
open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by cases ‹Decidable p› <;> rfl
private def pattern (pred : LLVM.IntPred) (swapped : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType); let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth=1)
    let a ← MatchProg.value ty; let b ← MatchProg.value ty
    let k ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] (fun p => match p.value with | .integer _ => true | _ => false)
    let x ← MatchProg.operation (.llvm .xor) #[a,k.res[0]!] #[ty] (fun _ => true)
    let root ← MatchProg.root (.llvm .icmp)
      (if swapped then #[b,x.res[0]!] else #[x.res[0]!,b]) #[bt]
      (fun p => p.predicate=pred)
    let () ← MatchProg.inspectOperation (Outputs := Unit) root.op (fun ctx op => do
      let operands := op.getOperands! ctx
      guard (operands.size = 2)
      let xorValue := operands[(if swapped then 1 else 0)]!
      let otherValue := operands[(if swapped then 0 else 1)]!
      let some firstUse := xorValue.getFirstUse! ctx | none
      guard ((firstUse.getNextUse! ctx).isNone)
      match otherValue.definingOp? with
      | none => pure ()
      | some otherOp => guard (!otherOp.isConstantLike ctx))
    return (ty,bt,a,b,k.res[0]!))
  (fun (ty,bt,a,b,k) => do
    let xp ← CreateProg.property (.llvm .xor) ()
    let x ← CreateProg.operation (.llvm .xor) #[a,b] #[ty] xp
    let cp ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk pred)
    CreateProg.operation (.llvm .icmp) #[x.res[0]!,k] #[bt] cp)
  (fun r => r.res[0]!)
private theorem xorMoveSemantics {w : Nat} (pred : LLVM.IntPred) (swapped : Bool)
    (hp : pred = .eq ∨ pred = .ne) (a b k : LLVM.Int w) :
    (if swapped then LLVM.Int.icmp b (LLVM.Int.xor a k) pred
      else LLVM.Int.icmp (LLVM.Int.xor a k) b pred) ⊒
      LLVM.Int.icmp (LLVM.Int.xor a b) k pred := by
  rcases hp with rfl | rfl <;> cases swapped
  · exact icmp_xor_move_eq a b k
  · rw [llvm_icmp_eq_comm b (LLVM.Int.xor a k)]
    exact icmp_xor_move_eq a b k
  · exact icmp_xor_move_ne a b k
  · rw [llvm_icmp_ne_comm b (LLVM.Int.xor a k)]
    exact icmp_xor_move_ne a b k

private theorem valid (pred : LLVM.IntPred) (swapped : Bool) (hp : pred=.eq ∨ pred=.ne) :
    Pattern.Valid (pattern pred swapped) := by
  cases swapped <;>
    simp only [pattern, Bool.false_eq_true, decide_false, decide_true, ite_false, ite_true] <;>
    unfoldPuddleBuilder
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
    rintro a b ⟨cv⟩ k hk hik
    cases cv with
    | float _ | dense _ | string _ => simp at hk
    | integer ka =>
      obtain rfl := (constant_iff _ ka _).mp hik
      rintro ⟨⟩ xv hx; obtain rfl := (xor_iff _ _ _ _).mp hx
      rintro cp source hm hs; obtain rfl := (icmp_iff _ cp _ _ _).mp hs
      rintro ⟨⟩
      rw [hm]
      refine ⟨.int w (LLVM.Int.xor a b), (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int 1 (LLVM.Int.icmp (LLVM.Int.xor a b) (.val (BitVec.ofInt w ka.value)) pred),
        (icmp_iff _ (IcmpProperties.mk pred) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
      first
      | exact (by simpa only [LLVM.Int.cast_self, Bool.false_eq_true, ite_false] using
          xorMoveSemantics pred false hp a b (.val (BitVec.ofInt w ka.value)))
      | exact (by simpa only [LLVM.Int.cast_self, ite_true] using
          xorMoveSemantics pred true hp a b (.val (BitVec.ofInt w ka.value)))
public def xorMoveConstantEq : Pattern OpCode := pattern .eq false
public theorem xorMoveConstantEq_valid : Pattern.Valid xorMoveConstantEq := valid .eq false (Or.inl rfl)
public def xorMoveConstantEqSwapped : Pattern OpCode := pattern .eq true
public theorem xorMoveConstantEqSwapped_valid : Pattern.Valid xorMoveConstantEqSwapped :=
  valid .eq true (Or.inl rfl)
public def xorMoveConstantNe : Pattern OpCode := pattern .ne false
public theorem xorMoveConstantNe_valid : Pattern.Valid xorMoveConstantNe := valid .ne false (Or.inr rfl)
public def xorMoveConstantNeSwapped : Pattern OpCode := pattern .ne true
public theorem xorMoveConstantNeSwapped_valid : Pattern.Valid xorMoveConstantNeSwapped :=
  valid .ne true (Or.inr rfl)
end Veir.Passes.InstCombineLLVM.XorMoveConstant
