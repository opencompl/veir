module

public import Veir.Interpreter.RuntimeValue
public import Veir.Interpreter.Memory
public import Veir.Interpreter.VariableState
public import Veir.Interpreter.CTree
public import Veir.DataLayout.RISCV64
public import Veir.Dialects.GMIR.OpInfo

public section

open CTree
open Veir.Data

/-!
  # CTree-based GMIR Interpreter

  This file contains a simple CTree interpreter for nondeterministic GMIR operations.
  The deterministic operations are delegated to the basic interpreter.
-/

namespace Veir

def GMIR.interpretOpCTree (opType : Veir.GMIR) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState)
    : CTree (ErrorE ⊕ₑ UBE) FreezeC (((Array RuntimeValue) × MemoryState × Option ControlFlowAction)) :=
  let run := GMIR.interpretOp' opType properties resultTypes operands blockOperands mem
  match opType with
  | .g_anyext => do
      let [.int w val] := operands.toList | fail
      let some resType := resultTypes[0]? | fail
      let .integerType resBw := resType.val | fail
      if h : resBw.bitwidth <= w then fail else
      .tau (.mk (resBw.bitwidth - w))
        (fun msb => .ret (#[.int resBw.bitwidth (val.ext resBw.bitwidth msb (_h := by omega))], mem, none))
  | .g_addw | .g_subw | .g_mulw | .g_sdivw | .g_udivw | .g_uremw
  | .g_shlw | .g_lshrw | .g_ashrw => do
      -- Reuse the deterministic low-word calculation and its poison/UB checks, then choose
      -- the unspecified upper word. The deterministic interpreter's zero extension is only
      -- one possible result; hardware word instructions choose the sign extension instead.
      let (values, mem, action) ← monadLift run
      let [.int 64 val] := values.toList | fail
      let word := val.trunc 32 false false (by decide)
      .tau (.mk 32)
        (fun msb => .ret (#[.int 64 (word.ext 64 msb (by decide))], mem, action))
  | _ => monadLift run

end Veir

