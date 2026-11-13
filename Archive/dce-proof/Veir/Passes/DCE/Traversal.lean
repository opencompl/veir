module

public import Veir.Passes.DCE.Structure
import all Veir.IR.Basic

public section

namespace Veir.DCE

/-- A finite path in the original next-operation graph whose internal
operations have all been deleted from the final context. -/
inductive Skips (source target : WfIRContext OpCode) :
    Option OperationPtr → Option OperationPtr → Prop where
  | refl (operation) : Skips source target operation operation
  | step (operation : OperationPtr) (original : operation.InBounds source.raw)
      (deleted : ¬operation.InBounds target.raw) {finish}
      (rest : Skips source target (operation.getNextOp! source.raw) finish) :
      Skips source target (some operation) finish

theorem Skips.trans {source target : WfIRContext OpCode} {start middle finish}
    (first : Skips source target start middle) (second : Skips source target middle finish) :
    Skips source target start finish := by
  induction first with
  | refl => exact second
  | step operation original deleted rest ih => exact .step operation original deleted (ih second)

theorem Skips.weaken {source middle target : WfIRContext OpCode} {start finish}
    (path : Skips source middle start finish) (erases : Erasures middle target) :
    Skips source target start finish := by
  induction path with
  | refl operation => exact .refl operation
  | step operation original deleted rest ih =>
    exact .step operation original
      (fun survivor => deleted (erases.operation_inBounds operation survivor)) ih

private theorem erase_next (ctx : WfIRContext OpCode) (removed operation : OperationPtr)
    (removedIn : removed.InBounds ctx.raw) (dead : removed.isTriviallyDead ctx.raw)
    (survivor : operation.InBounds (WfRewriter.eraseOp ctx removed dead.1 dead.2.1 removedIn).raw) :
    operation.getNextOp! (WfRewriter.eraseOp ctx removed dead.1 dead.2.1 removedIn).raw =
      if operation.getNextOp! ctx.raw = some removed then removed.getNextOp! ctx.raw
      else operation.getNextOp! ctx.raw := by
  have different := (eraseOp_inBounds_iff ctx removed operation removedIn dead).mp survivor
  have changed := OperationPtr.getNextOp!_wfRewriter_eraseOp survivor
  have forward : operation.getNextOp! ctx.raw = some removed →
      removed.getPrevOp! ctx.raw = some operation :=
    IRContext.WellFormed.OperationPtr_prev!_eq_some_of_next!_eq_some different.1 ctx.wellFormed
  have backward : removed.getPrevOp! ctx.raw = some operation →
      operation.getNextOp! ctx.raw = some removed :=
    IRContext.WellFormed.OperationPtr_next!_eq_some_of_prev!_eq_some removedIn ctx.wellFormed
  grind

/-- A final successor is reached from the original successor by skipping a
finite chain of deleted operations. All edges are edges of the original IR. -/
theorem Erasures.next_skips {source target : WfIRContext OpCode}
    (erases : Erasures source target) (operation : OperationPtr)
    (survivor : operation.InBounds target.raw) :
    Skips source target (operation.getNextOp! source.raw) (operation.getNextOp! target.raw) := by
  induction erases generalizing operation with
  | refl => exact .refl _
  | @tail middle final previous step ih =>
    cases step with
    | erase removed removedIn dead =>
      have single : Erasures middle (WfRewriter.eraseOp middle removed dead.1 dead.2.1 removedIn) :=
        .single (.erase middle removed removedIn dead)
      have earlier := ((eraseOp_inBounds_iff middle removed operation removedIn dead).mp survivor).1
      have beforePath := (ih operation earlier).weaken single
      rw [erase_next middle removed operation removedIn dead survivor]
      split
      next adjacent =>
        rw [adjacent] at beforePath
        have suffix := (ih removed removedIn).weaken single
        have removedFinal : ¬removed.InBounds (WfRewriter.eraseOp middle removed dead.1 dead.2.1 removedIn).raw := by
          intro impossible
          exact ((eraseOp_inBounds_iff middle removed removed removedIn dead).mp impossible).2 rfl
        exact beforePath.trans (.step removed (previous.operation_inBounds removed removedIn) removedFinal suffix)
      next separate => exact beforePath

/-- The final block entry similarly skips only a finite deleted prefix of the
original operation chain. Blocks themselves are never removed by DCE. -/
theorem Erasures.firstOp_skips {source target : WfIRContext OpCode}
    (erases : Erasures source target) (block : BlockPtr) (original : block.InBounds source.raw) :
    Skips source target (block.getFirstOp! source.raw) (block.getFirstOp! target.raw) := by
  induction erases with
  | refl => exact .refl _
  | @tail middle final previous step ih =>
    cases step with
    | erase removed removedIn dead =>
      have single : Erasures middle (WfRewriter.eraseOp middle removed dead.1 dead.2.1 removedIn) :=
        .single (.erase middle removed removedIn dead)
      have beforePath := ih.weaken single
      have blockBounds := (previous.block_inBounds_iff block).mpr original
      rw [BlockPtr.getFirstOp!_wfRewriter_eraseOp]
      split
      next first =>
        rw [first.1] at beforePath
        have suffix := (previous.next_skips removed removedIn).weaken single
        have removedFinal : ¬removed.InBounds (WfRewriter.eraseOp middle removed dead.1 dead.2.1 removedIn).raw := by
          intro impossible
          exact ((eraseOp_inBounds_iff middle removed removed removedIn dead).mp impossible).2 rfl
        exact beforePath.trans (.step removed (previous.operation_inBounds removed removedIn) removedFinal suffix)
      next separate => exact beforePath

end Veir.DCE
