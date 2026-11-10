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

/--
Interprets an LLVM operation using CTrees.
Fallback to the `Interp` based interpreter for operations that do not rely on non-determinism.
-/
def Llvm.interpretOpCTree {EIn : Type} {E : EIn → Type}
    [ErrorE -< E] [UBE -< E] (opType : Veir.Llvm) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState) (layout : DataLayout := .riscv64)
    : CTree E FreezeC (((Array RuntimeValue) × MemoryState × Option ControlFlowAction)) :=
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
        let p : FreezeC .pointer ← CTree.choose FreezeCIn.pointer
        return (#[.addr (.val p)], mem, none)
    | .addr (.val p) => return (#[.addr (.val p)], mem, none)
    | _ => fail
  | other =>
    monadLift (Llvm.interpretOp' other properties resultTypes operands blockOperands mem layout)

end Veir
