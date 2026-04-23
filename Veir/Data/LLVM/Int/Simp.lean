module

public import Lean

register_simp_attr llvm_toBitVec

open Lean Elab Tactic Meta Term
/-- Cases on every local hypothesis of a given type, then call `bv_decide` on all goals. -/
elab "cases_bv_decide" t:term : tactic => do
  let targetTy ← elabType t
  let ctx ← getLCtx
  -- Collect all hypotheses whose type is definitionally equal to `targetTy`
  let hyps := ctx.decls.toList.filterMap (·)
               |>.filter fun decl =>
                  !decl.isImplementationDetail &&
                  !decl.isLet
  for decl in hyps do
    let declTy ← instantiateMVars decl.type
    if ← isDefEq declTy targetTy then
      let goals ← getGoals
      if goals.isEmpty then break
      setGoals goals
      evalTactic (← `(tactic| cases $(mkIdent decl.userName):ident))
  evalTactic (← `(tactic| all_goals bv_decide))
