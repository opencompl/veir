import Veir.PatternRewriter.Puddle.CTreeValidity

open Veir Veir.Puddle

namespace Veir.Puddle.CTree

/-- Integer freeze preserves concrete inputs and replaces poison by any concrete bitvector. -/
@[simp, grind =]
theorem CanInterpretTo.freeze_int {ty : IntegerType} (property : propertiesOf (OpCode.llvm .freeze))
    (value : Data.LLVM.Int ty.bitwidth) (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .freeze) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth value] results ↔
    ∃ v : BitVec ty.bitwidth, (value = .poison ∨ value = .val v) ∧
      results = .ok #[.int ty.bitwidth (.val v)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree, bind_pure_comp, Functor.map]
  cases value <;> cases results <;> simp [PureOrErr.CanInterpretTo.bind_iff]

/-- Integer addition has a single outcome, including poison from overflow flags. -/
@[simp, grind =]
theorem CanInterpretTo.add_int {ty : IntegerType} (property : propertiesOf (OpCode.llvm .add))
    (x y : Data.LLVM.Int ty.bitwidth) (results : Interp (Array RuntimeValue)) :
    CanInterpretTo (.llvm .add) property #[TypeAttr.of IntegerType ty]
      #[.int ty.bitwidth x, .int ty.bitwidth y] results ↔
    results = .ok #[.int ty.bitwidth (Data.LLVM.Int.add x y property.nsw property.nuw)] := by
  simp only [CanInterpretTo, interpretOpCTree, Llvm.interpretOpCTree]
  cases results <;> simp

end Veir.Puddle.CTree

namespace CTreePuddleTest

/-- Recreating a nondeterministic operation must allow the source choice to depend on the target. -/
private def recreateFreeze : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let root ← MatchProg.root (.llvm .freeze) #[x] #[ty]
      return (ty, x, root.properties))
    (fun (ty, x, prop) => CreateProg.operation (.llvm .freeze) #[x] #[ty] prop)
    (fun result => result)

example : CTree.Pattern.Valid recreateFreeze := by
  unfold recreateFreeze
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff,
    CTree.CanInterpretTo.freeze_int, Interp.ok.injEq, and_imp, CTree.CreationM.forall_result_eq,
    List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, implies_true, reduceCtorEq,
    and_false, exists_const, false_and, or_self, or_false, Nat.lt_add_one, getElem!_pos,
    List.getElem_toArray, List.getElem_cons_zero, true_and, forall_const]
  grind

/--
Rewrite `freeze (add x y)` to `add (freeze x) (freeze y)` for wrapping addition.
Match two operations and create three, with independent choices for the two new freezes.
-/
private def freezeAdd : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let y ← MatchProg.value ty
      let add ← MatchProg.operation (.llvm .add) #[x, y] #[ty]
        (fun properties => !properties.nsw && !properties.nuw)
      let root ← MatchProg.root (.llvm .freeze) #[add.res[0]!] #[ty]
      return (ty, x, y, add.properties, root.properties))
    (fun (ty, x, y, addProp, freezeProp) => do
      let fx ← CreateProg.operation (.llvm .freeze) #[x] #[ty] freezeProp
      let fy ← CreateProg.operation (.llvm .freeze) #[y] #[ty] freezeProp
      CreateProg.operation (.llvm .add) #[fx.res[0]!, fy.res[0]!] #[ty] addProp)
    (fun result => result)

theorem freezeAdd_valid : CTree.Pattern.Valid freezeAdd := by
  unfold freezeAdd
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff,
    CTree.CanInterpretTo.freeze_int, Interp.foldProp_ok, Interp.foldProp_ub, Interp.foldProp_fail, Interp.ok.injEq, and_imp, CTree.CreationM.forall_result_eq,
    List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.lt_add_one,
    getElem!_pos, List.getElem_toArray, List.getElem_cons_zero, true_and, reduceCtorEq, and_false,
    exists_const, false_and, or_self, or_false, CTree.CanInterpretTo.add_int, Array.mk.injEq,
    List.cons.injEq, and_true, forall_eq, implies_true, and_self, exists_eq_left, forall_const]
  -- After specializing operation outcomes, inspect implicit types too: no assignments or
  -- per-operation outcome folds should remain.
  run_tac
    let target ← Lean.Elab.Tactic.getMainTarget
    let leftover := target.find? fun
      | .const name _ =>
        (``SemanticAssignment).isPrefixOf name || (``SemanticBinding).isPrefixOf name ||
          name == ``Interp.foldProp
      | _ => false
    if leftover.isSome then
      throwError "provePuddleValid left assignments or per-operation outcome folds in the goal"
  rintro ty x y addProp hnsw hnuw fx hx fy hy
  simp only [Data.LLVM.Int.add, hnsw, Bool.false_eq_true, false_and, ↓reduceIte, hnuw, Id.run]
  cases x <;> cases y <;> grind

end CTreePuddleTest
