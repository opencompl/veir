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

def GMIR.interpretOpCTree {EIn : Type} {E : EIn → Type}
    [ErrorE -< E] [UBE -< E] (opType : Veir.GMIR) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState)
    : CTree E FreezeC (((Array RuntimeValue) × MemoryState × Option ControlFlowAction)) :=
  match opType with
  | .g_anyext => do
      let [.int w val] := operands.toList | fail
      let some resType := resultTypes[0]? | fail
      let .integerType resBw := resType.val | fail
      if h : resBw.bitwidth <= w then fail else
      .tau (.mk (resBw.bitwidth - w))
        (fun msb => .ret (#[.int resBw.bitwidth (val.ext resBw.bitwidth msb (_h := by omega))], mem, none))
  | .g_freeze => do
      match operands.toList with
      | [.int w (.val v)] => return (#[.int w (.val v)], mem, none)
      | [.int w .poison] =>
          let (bv : FreezeC (.mk w)) ← CTree.choose (FreezeCIn.mk w)
          return (#[.int w (LLVM.Int.val bv)], mem, none)
      | _ => fail
  | .g_load => do
      let (results, mem, action) ←
        monadLift $ GMIR.interpretOp' .g_load properties resultTypes operands blockOperands mem
      let size := properties.size.toNat
      let [.int w val] := results.toList | return (results, mem, action)
      if h : size < w then
        -- The high bits are unspecified, as for `g_anyext`.
        .tau (.mk (w - size)) fun msb =>
          .ret (#[.int w ((val.trunc size false false h).ext w msb h)], mem, action)
      else return (results, mem, action)
  | opType => do
      monadLift $ GMIR.interpretOp' opType properties resultTypes operands blockOperands mem

end Veir

