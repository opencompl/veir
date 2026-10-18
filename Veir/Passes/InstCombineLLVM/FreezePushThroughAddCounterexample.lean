module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.FreezePushThroughAddCounterexample

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

/-- The scalar, unflagged specialization of `pushFreezeToPreventPoisonFromPropagating`:
    `freeze (X + 1) -> freeze X + 1`. The contextual guard enforces the source one-use
    condition, but `Pattern.Valid` deliberately cannot rely on contextual inspection. -/
public def freezePushThroughAdd : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let one ← matchIntConstant ty 1
    let sum ← MatchProg.operation (.llvm .add) #[x, one] #[ty]
      (fun p => !p.nsw && !p.nuw)
    let root ← MatchProg.root (.llvm .freeze) #[sum.res[0]!] #[ty]
      (fun _ => true)
    let () ← MatchProg.inspectOperation (Outputs := Unit) root.op (fun ctx op => do
      let operands := op.getOperands! ctx
      guard (operands.size = 1)
      let sumValue := operands[0]!
      let some firstUse := sumValue.getFirstUse! ctx | none
      guard ((firstUse.getNextUse! ctx).isNone))
    return (ty, x, one))
  (fun (ty, x, one) => do
    let freezeProps ← CreateProg.property (.llvm .freeze) ()
    let frozen ← CreateProg.operation (.llvm .freeze) #[x] #[ty] freezeProps
    let addProps ← CreateProg.property (.llvm .add) (NswNuwProperties.mk false false)
    CreateProg.operation (.llvm .add) #[frozen.res[0]!, one] #[ty] addProps)
  (fun result => result.res[0]!)

private theorem freeze_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .freeze) () #[IntegerType.mk w signedness]
      #[.int w x] #[v] ↔ v = .int w x.freeze := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_one_iff,
    RuntimeValue.Conforms, List.getElem!_toArray, List.getElem!_eq_getElem?_getD,
    forall_eq, Nat.lt_add_one, getElem?_pos, List.getElem_cons_zero,
    Option.getD_some, true_and, interpretOp', Llvm.interpretOp', Interp.pure_eq,
    Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true,
    TypeAttr.of_val]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

private theorem freezePushThroughAdd_not_preserves :
    ¬ freezePushThroughAdd.PreservesSemantics := by
  simp only [freezePushThroughAdd, matchIntConstant]
  unfoldPuddleBuilder
  simpPuddleSemantics
  refine ⟨({ bitwidth := 2, signedness := .signless } : IntegerType),
    .int 2 .poison, ?_, ?_⟩
  · exact RuntimeValue.Conforms.integerType.mpr ⟨.poison, rfl⟩
  let oneAttr : IntegerAttr :=
    ⟨1, ({ bitwidth := 2, signedness := .signless } : IntegerType)⟩
  refine ⟨LLVMConstantProperties.mk (.integer oneAttr), rfl, ?_⟩
  refine ⟨.int 2 (.val (BitVec.ofInt 2 1)),
    (constant_iff ({ bitwidth := 2, signedness := .signless }) oneAttr _).mpr
      (by dsimp [oneAttr]), ?_⟩
  refine ⟨(default : NswNuwProperties), rfl, rfl, ?_⟩
  refine ⟨.int 2 .poison,
    (add_iff (signedness := .signless) 2 default .poison
      (.val (BitVec.ofInt 2 1)) _).mpr ?_, ?_⟩
  · simp [LLVM.Int.add, Id.run]
  refine ⟨(default : propertiesOf (.llvm .freeze : OpCode)), .int 2 (.val 0),
    (freeze_iff (signedness := .signless) 2 .poison _).mpr
      (by simp [LLVM.Int.freeze, Id.run]), ?_⟩
  refine ⟨(), ?_⟩
  intro frozen hFrozen target hTarget
  obtain rfl := (freeze_iff (signedness := .signless) 2 .poison frozen).mp hFrozen
  obtain rfl := (add_iff (signedness := .signless) 2
    (NswNuwProperties.mk false false) (.val 0)
    (.val (BitVec.ofInt 2 1)) target).mp hTarget
  simp [LLVM.Int.add, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

/-- Puddle's deterministic `freeze poison = 0` makes this eligible LLVM
    specialization invalid in the Puddle model: the source is `0`, while the
    replacement is `1`. This is a model counterexample, not an LLVM bug. -/
public theorem freezePushThroughAdd_not_valid :
    ¬ Pattern.Valid freezePushThroughAdd := by
  intro h
  exact freezePushThroughAdd_not_preserves h.refines

end Veir.Passes.InstCombineLLVM.FreezePushThroughAddCounterexample
