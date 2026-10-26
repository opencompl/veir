module

public import Veir.Interpreter.Basic
public import Veir.Interpreter.CTree

public section

open CTree
open Veir.Data

namespace Veir

/-- Interpret builtin casts with explicit choices when poison becomes concrete.
Other builtin operations and deterministic cast cases retain the outcome-monad semantics. -/
def Builtin.interpretOpCTree (opType : Builtin) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState) (layout : DataLayout := .riscv64)
    : Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
  let deterministic : Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
    monadLift (Veir.interpretOp' (.builtin opType) properties
      resultTypes operands blockOperands mem layout)
  match opType with
  | .unrealized_conversion_cast => do
    let some resType := resultTypes[0]? | fail
    match resType.val, operands.toList with
    | .registerType _, [.int width .poison] =>
      let bits : FreezeC (.mk width) ← CTree.choose (FreezeCIn.mk width)
      return (#[.reg ⟨bits.zeroExtend 64⟩], mem, none)
    | .registerType _, [.addr .poison] =>
      let bits : FreezeC (.mk 64) ← CTree.choose (FreezeCIn.mk 64)
      return (#[.reg ⟨bits⟩], mem, none)
    | .registerType _, [.byte width value] =>
      if value.poison = 0 then
        deterministic
      else
        let bits : FreezeC (.mk width) ← CTree.choose (FreezeCIn.mk width)
        let frozen := value.val ||| (value.poison &&& bits)
        return (#[.reg ⟨frozen.zeroExtend 64⟩], mem, none)
    | .integerType resultWidth, [.byte width value] =>
      if resultWidth.bitwidth ≠ width then fail else
      if value.poison = 0 ∨ value.poison = BitVec.allOnes width then
        deterministic
      else
        let bits : FreezeC (.mk width) ← CTree.choose (FreezeCIn.mk width)
        return (#[.int width (.val (value.val ||| (value.poison &&& bits)))], mem, none)
    | _, _ => deterministic
  | _ => deterministic

end Veir
