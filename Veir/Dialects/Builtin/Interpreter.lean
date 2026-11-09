module

public import Veir.Interpreter.Basic
public import Veir.Interpreter.CTree

public section

open CTree

namespace Veir

/-- Cast a byte to an integer without fixing partially poisoned bits to zero.
All-poison bytes retain integer poison; each partially poisoned bit is chosen independently. -/
def Builtin.byteToIntCTree {EIn : Type} {E : EIn → Type} {width : Nat}
    (value : Data.LLVM.Byte width) : CTree E FreezeC (Data.LLVM.Int width) :=
  if value.poison = BitVec.allOnes width then pure .poison
  else if value.poison = 0 then pure (.val value.val)
  else do
    let bits : FreezeC (.mk width) ← CTree.choose (FreezeCIn.mk width)
    pure (.val (value.val ||| (value.poison &&& bits)))

/-- Interpret an unrealized conversion cast using CTrees. -/
def Builtin.interpretUnrealizedConversionCastCTree {EIn : Type} {E : EIn → Type}
    [ErrorE -< E] [UBE -< E]
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (mem : MemoryState)
    : CTree E FreezeC (Array RuntimeValue × MemoryState × Option ControlFlowAction) := do
  let some resType := resultTypes[0]? | fail
  match resType.val, operands.toList with
  | .registerType _, [.int _ (.val value)] =>
    return (#[.reg ⟨value.zeroExtend 64⟩], mem, none)
  | .registerType _, [.int _ .poison] =>
    -- Registers cannot carry poison, so any register value is possible.
    let bits : FreezeC (.mk 64) ← CTree.choose (FreezeCIn.mk 64)
    return (#[.reg ⟨bits⟩], mem, none)
  | .registerType _, [.byte width value] =>
    if value.poison = 0 then
      return (#[.reg (LLVM.Byte.toReg value)], mem, none)
    else
      -- Resolve only poisoned bits before resizing to the register width.
      let bits : FreezeC (.mk width) ← CTree.choose (FreezeCIn.mk width)
      return (#[.reg ⟨(value.val ||| (value.poison &&& bits)).zeroExtend 64⟩], mem, none)
  | .registerType _, [.addr value] =>
    match value.toInt with
    | .val bits => return (#[.reg ⟨bits⟩], mem, none)
    | .poison =>
      let bits : FreezeC (.mk 64) ← CTree.choose (FreezeCIn.mk 64)
      return (#[.reg ⟨bits⟩], mem, none)
  | .integerType width, [.reg value] =>
    return (#[.int width.bitwidth (RISCV.Reg.toInt value width.bitwidth)], mem, none)
  | .byteType width, [.reg value] =>
    return (#[.byte width.bitwidth (RISCV.Reg.toByte value width.bitwidth)], mem, none)
  | .llvmPointerType _, [.reg value] =>
    return (#[.addr (mem.ptrFromInt (.val value.val))], mem, none)
  | .integerType resWidth, [.byte width value] =>
    if resWidth.bitwidth ≠ width then fail
    return (#[.int width (← Builtin.byteToIntCTree value)], mem, none)
  | .byteType resWidth, [.int width value] =>
    if resWidth.bitwidth ≠ width then fail
    return (#[.byte width (Data.LLVM.Byte.fromInt value)], mem, none)
  | _, _ => fail

/-- Interpret a builtin operation using CTrees. -/
def Builtin.interpretOpCTree {EIn : Type} {E : EIn → Type}
    [ErrorE -< E] [UBE -< E] (opType : Veir.Builtin) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    (mem : MemoryState)
    : CTree E FreezeC (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .unrealized_conversion_cast =>
    Builtin.interpretUnrealizedConversionCastCTree resultTypes operands mem
  | _ => fail

end Veir
