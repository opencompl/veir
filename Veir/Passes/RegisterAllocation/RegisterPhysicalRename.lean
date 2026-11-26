module

public import Veir.Passes.RegisterAllocation.Helper
public import Veir.Rewriter.WfRewriter
import Std.Data.HashMap

namespace Veir

/-!
The physical assignment maps virtual registers to physical registers. For each function:

1. Initialize a pool of allocatable physical register.
2. Every physical register already used in the function (precoloured arguments and return values,
   `x0`, ...) is removed from the pool.
3. Walking the function forward, each virtual register gets the next register of the pool.

There is no spiller yet, so a function needing more registers than the pool holds is rejected.
Excluding every precoloured register for the whole function is conservative, so expect worse
code than llc until copies are coalesced.

Assignment uses the values collected during backward allocation, without walking the IR again.
-/

structure Assignment (cls: RegisterClass) where
  /-- Physical registers not handed out yet in allocation order. -/
  pool : List Nat
  /-- Mapping from virtual register to its assigned physical register. -/
  assigned : Std.HashMap Int Nat := {}
deriving Inhabited, Repr

namespace Assignment

def assign {cls : RegisterClass} (a : Assignment cls) (v : Int) : Option (Nat × Assignment cls) :=
  match a.assigned[v]? with
  | some p => some (p, a)
  | none =>
    match a.pool with
    | p :: rest => some (p, { pool := rest, assigned := a.assigned.insert v p })
    | [] => none

end Assignment

/-- Map the virtual registers in the function's collected values to physical registers. -/
public def renameToPhysicalRegisters (ctx : WfIRContext OpCode) (values : List ValuePtr) :
    Except String (WfIRContext OpCode) := do
  -- Remove the physical registers already used in the function from the pool.
  let used := values.filterMap fun v =>
    match (v.getType! ctx.raw).val with
    | .registerType { cls := .int, index := some n } => if n ≥ 0 then some n.toNat else none
    | _ => none
  let mut assignment : Assignment .int :=
    { pool := (RegisterInfo.allocOrder .int).toList.filter (!used.contains ·) }
  let available := assignment.pool.length
  let mut ctx := ctx
  for v in values do
    match (v.getType! ctx.raw).val with
    | .registerType { cls := .int, index := some n } =>
      if n < 0 then
        let some (p, a) := assignment.assign n
          | throw s!"register assignment ran out of physical registers: needs more than \
              the {available} available"
        assignment := a
        ctx := WfRewriter.setType! ctx v ({ cls := .int, index := some p } : RegisterType)
    | .registerType { cls := .int, index := none } =>
      throw "register assignment found an unallocated register"
    | _ => throw "register assignment expects only integer register values"
  return ctx

end Veir
