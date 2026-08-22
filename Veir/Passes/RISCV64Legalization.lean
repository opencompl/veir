module

public import Veir.Pass
import Veir.Passes.Legalization

namespace Veir

def riscv64LegalizerInfo : LegalizerInfo :=
  let info : LegalizerInfo := {}
  let info := info.defineRuleSet #[.llvm .add, .llvm .sub] #[
    legalFor #[64],
    -- customFor #[32] (not yet implemented)
    widenScalarToNextPow2 0,
    clampScalar 0 64 64,
  ]
  info

def LegalizeRISCV64Pass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    .fromLocalRewrite (legalizeInstrStep riscv64LegalizerInfo)
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying RISC-V legalization"
  | some ctx => pure ctx

public def LegalizeRISCV64Pass : Pass OpCode :=
  { name := "legalize-riscv64"
    description := "Legalize types for RISC-V 64."
    run := fun _ => LegalizeRISCV64Pass.impl }

end Veir
