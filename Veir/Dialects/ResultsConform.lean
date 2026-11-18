module

public import Veir.Dialects.Builtin.ResultsConform
public import Veir.Dialects.Cf.ResultsConform
public import Veir.Dialects.Func.ResultsConform
public import Veir.Dialects.LLVM.CTreeResultsConform
public import Veir.Dialects.LLVM.ResultsConform
public import Veir.Dialects.GMIR.CTreeResultsConform
public import Veir.Dialects.GMIR.ResultsConform
public import Veir.Dialects.GMIR_RISCV.ResultsConform
public import Veir.Dialects.RISCV.CTreeResultsConform
public import Veir.Dialects.RISCV.ResultsConform
public import Veir.Dialects.RISCV_Cf.ResultsConform
public import Veir.Dialects.RISCV_Stack.ResultsConform
public import Veir.Dialects.Test.ResultsConform

public section

/-!
# Ensure that the results of every op conform with the verifier

Either an op code proves conformance or we assume conformance via an axiom.
-/

namespace Veir

/--

Assume that the CTree of every opcode yields conforming results.

This axiom makes it easy to identify proofs that depend on opcodes for
which conformance was not yet established.
-/
axiom OpCode.resultsConform_assumed (opType : OpCode) : opType.ResultsConform

instance (priority := low) (opType : OpCode) : ResultsConform opType := by
  cases opType <;> rename_i op <;> cases op <;>
    first
      | infer_instance
      | exact ⟨OpCode.resultsConform_assumed _⟩

end Veir

end
