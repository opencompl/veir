module

public import Veir.Interpreter.RuntimeValue
public import Veir.Interpreter.Memory
public import Veir.Interpreter.VariableState
public import Veir.Interpreter.CTree
public import Veir.DataLayout.RISCV64
public import Veir.Dialects.LLVM.OpInfo

public section

open CTree
open Veir.Data
/-!
  # CTree-based LLVM Interpreter

  This file contains relevant effects and
  a simple CTree interpreter for a subset of LLVM operations.
-/

namespace Veir

/-- Use explicit choices for `freeze` and lift the deterministic interpreter for all
other operations, preserving its results, memory, control flow, UB, and failure. -/
def Llvm.interpretOpCTree (opType : Veir.Llvm) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState) (layout : DataLayout := .riscv64)
    : CTree (ErrorE ⊕ₑ UBE) FreezeC (((Array RuntimeValue) × MemoryState × Option ControlFlowAction)) :=
  match opType with
  | .freeze => do
    let [val] := operands.toList | fail
    match val with
    | .int w val =>
        if let .val _ := val then
          return (#[.int w val], mem, none)
        else
          let (bv : FreezeC (.mk w)) ← CTree.choose (FreezeCIn.mk w)
          return (#[.int w (LLVM.Int.val bv)], mem, none)
    | .byte w val =>
        let bv : FreezeC (.mk w) ← CTree.choose (FreezeCIn.mk w)
        return (#[.byte w (.fromBitVec (val.val ||| (val.poison &&& bv)))], mem, none)
    | .addr .poison =>
        let pointer : FreezeC .pointer ← CTree.choose FreezeCIn.pointer
        return (#[.addr (.val pointer)], mem, none)
    | .addr (.val p) => return (#[.addr (.val p)], mem, none)
    | _ => fail
  | other =>
    monadLift (Llvm.interpretOp' other properties resultTypes operands blockOperands mem layout)

end Veir
