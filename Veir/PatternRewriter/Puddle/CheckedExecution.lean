module

public import Veir.PatternRewriter.Puddle.Execution
public import Veir.IRNesting.RootedAtCheck
public import Veir.Interfaces.RegionKindInterfaces
import all Veir.IRNesting

namespace Veir.Puddle
public section

/-- Eligibility for the module-scoped checked driver. This is checked once per worklist pop,
before either automatic dead-code erasure or pattern execution. -/
def rootEligible {OpInfo : Type} [HasOpInfo OpInfo] (moduleOp : OperationPtr)
    (ctx : WfIRContext OpInfo) (op : OperationPtr) : Bool :=
  op.rootedAt? moduleOp ctx &&
    (op.getNumRegions! ctx.raw == 0) &&
    match op.getParentRegion! ctx.raw with
    | none => false
    | some region => region.hasSSADominance ctx

/-- Apply validatable Puddle rules to eligible operations in the given module, skipping
unsupported placements before automatic cleanup and matching. -/
def applyInModule (rules : Array (Pattern OpCode)) (ctx : WfIRContext OpCode)
    (moduleOp : OperationPtr) (maxRounds : Nat := 10) : Option (WfIRContext OpCode) :=
  (RewritePattern.GreedyRewritePattern (rules.map (fun rule => rule.compile.run))).applyInContextIf
    (rootEligible moduleOp) ctx moduleOp maxRounds

/-- Function-wise version of the same module-scoped eligibility policy. -/
def applyToFunctionsInModule (rules : Array (Pattern OpCode)) (ctx : WfIRContext OpCode)
    (moduleOp : OperationPtr) (maxRounds : Nat := 10) : Option (WfIRContext OpCode) :=
  (RewritePattern.GreedyRewritePattern (rules.map (fun rule => rule.compile.run))).applyToFunctionsIf
    (rootEligible moduleOp) ctx moduleOp maxRounds

end
end Veir.Puddle
