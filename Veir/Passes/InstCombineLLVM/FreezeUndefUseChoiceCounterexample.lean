module

public import Veir.Passes.InstCombineLLVM.Semantics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.FreezeUndefUseChoiceCounterexample

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

private def allOnesProperty (type : TypeAttr) :
    Option (propertiesOf (OpCode.llvm .mlir__constant)) := do
  let some intType := type.cast? IntegerType | none
  return LLVMConstantProperties.mk (.integer (IntegerAttr.ofInt (-1) intType))

/-- One-use scalar OR specialization of `getUndefReplacement`:
    `or (freeze poison), Y -> or -1, Y`. Upstream replaces the freeze in every use;
    rooting this pattern at its sole OR user makes that use graph explicit. -/
public def freezePoisonOrAllOnes : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value ty
    let y ← MatchProg.value ty
    let frozen ← MatchProg.operation (.llvm .freeze) #[x] #[ty]
    let root ← MatchProg.root (.llvm .or) #[frozen.res[0]!, y] #[ty]
    let () ← MatchProg.inspectOperation (Outputs := Unit) root.op (fun ctx op => do
      let operands := op.getOperands! ctx
      guard (operands.size = 2)
      let frozenValue := operands[0]!
      let some frozenOp := frozenValue.definingOp? | none
      let freezeOperands := frozenOp.getOperands! ctx
      guard (freezeOperands.size = 1)
      let some poisonOp := freezeOperands[0]!.definingOp? | none
      guard (poisonOp.getOpType! ctx = (.llvm .mlir__poison : OpCode))
      let some firstUse := frozenValue.getFirstUse! ctx | none
      guard ((firstUse.getNextUse! ctx).isNone))
    return (ty, y, root.properties))
  (fun (ty, y, orProperties) => do
    let cp ← CreateProg.applyNative
      (Outputs := Handle OpCode (.prop (.llvm .mlir__constant))) ty allOnesProperty
    let minusOne ← CreateProg.operation (.llvm .mlir__constant) #[] #[ty] cp
    CreateProg.operation (.llvm .or) #[minusOne.res[0]!, y] #[ty] orProperties)
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

private theorem freezePoisonOrAllOnes_not_preserves :
    ¬ freezePoisonOrAllOnes.PreservesSemantics := by
  simp only [freezePoisonOrAllOnes]
  unfoldPuddleBuilder
  simpPuddleSemantics
  refine ⟨({ bitwidth := 2, signedness := .signless } : IntegerType),
    .int 2 .poison, ?_, .int 2 (.val 0), ?_, (), .int 2 (.val 0), ?_,
    (default : DisjointProperties), .int 2 (.val 0), ?_, (), ?_⟩
  · exact RuntimeValue.Conforms.integerType.mpr ⟨.poison, rfl⟩
  · exact RuntimeValue.Conforms.integerType.mpr ⟨.val 0, rfl⟩
  · exact (freeze_iff (signedness := .signless) 2 .poison _).mpr
      (by simp [LLVM.Int.freeze, Id.run])
  · exact (or_iff (signedness := .signless) 2 default (.val 0) (.val 0) _).mpr
      (by simp [LLVM.Int.or, Id.run])
  · simp [allOnesProperty, IsTypeAttr.cast?_of]
    intro target hTarget
    obtain rfl := (constant_iff
      ({ bitwidth := 2, signedness := .signless } : IntegerType)
      (IntegerAttr.ofInt (-1) ({ bitwidth := 2, signedness := .signless } : IntegerType))
      _).mp hTarget
    intro targetOr hTargetOr
    change InterpretsTo (.llvm .or) default
      #[IntegerType.mk 2 .signless]
      #[.int 2 (.val (BitVec.ofInt 2
        (IntegerAttr.normalizeValue
          ({ bitwidth := 2, signedness := .signless } : IntegerType) (-1)))),
        .int 2 (.val 0)] #[targetOr] at hTargetOr
    have hnorm : BitVec.ofInt 2
        (IntegerAttr.normalizeValue
          ({ bitwidth := 2, signedness := .signless } : IntegerType) (-1)) =
        BitVec.ofInt 2 (-1) :=
      ofInt_normalizeValue
        ({ bitwidth := 2, signedness := .signless } : IntegerType) (-1)
    rw [hnorm] at hTargetOr
    have hTargetOr' :
        targetOr = .int 2 (LLVM.Int.or (.val (BitVec.ofInt 2 (-1))) (.val 0) false) :=
      (or_iff (signedness := .signless) 2 default
        (.val (BitVec.ofInt 2 (-1))) (.val 0) targetOr).mp hTargetOr
    subst targetOr
    simp [LLVM.Int.or, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

/-- Puddle deterministically chooses zero for `freeze poison`, while this LLVM
    use-based choice selects all ones for an OR-only use. Thus the eligible
    scalar specialization is invalid in the Puddle model, not in LLVM. -/
public theorem freezePoisonOrAllOnes_not_valid :
    ¬ Pattern.Valid freezePoisonOrAllOnes := by
  intro h
  exact freezePoisonOrAllOnes_not_preserves h.refines

end Veir.Passes.InstCombineLLVM.FreezeUndefUseChoiceCounterexample
