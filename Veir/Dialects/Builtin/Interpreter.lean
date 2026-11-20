module

public import Veir.Interpreter.Basic
public import Veir.Interpreter.CTree

public section

open CTree

namespace Veir

/--
Cast a byte to an integer and use a ctree effect to choose the bits that are poison.
-/
def Builtin.byteToIntCTree {EIn : Type} {E : EIn → Type} {width : Nat}
    (value : Data.LLVM.Byte width) : CTree E FreezeC (Data.LLVM.Int width) :=
  if value.poison = BitVec.allOnes width then pure .poison
  else do
    let bits : FreezeC (.mk width) ← CTree.choose (FreezeCIn.mk width)
    pure (.val (value.fillPoison bits))

/-- Cast an integer to a register. Poison is cast to a non-deterministic register value. -/
def Builtin.intToRegCTree {EIn : Type} {E : EIn → Type} {width : Nat}
    (value : Data.LLVM.Int width) : CTree E FreezeC (Data.RISCV.Reg) :=
  match value with
  | .val bits => return ⟨bits.setWidth 64⟩
  | .poison => do
    let bits : FreezeC (.mk 64) ← CTree.choose (FreezeCIn.mk 64)
    return ⟨bits⟩

/-- Cast a byte to a register. Poison bits are chosen non-deterministically. -/
def Builtin.byteToRegCTree {EIn : Type} {E : EIn → Type} {width : Nat}
    (value : Data.LLVM.Byte width) : CTree E FreezeC (Data.RISCV.Reg) :=
  if value.poison = 0#width then
    return ⟨value.val.setWidth 64⟩
  else do
    let bits : FreezeC (.mk width) ← CTree.choose (FreezeCIn.mk width)
    return ⟨(value.fillPoison bits).setWidth 64⟩

/-- Interpret an unrealized conversion cast using CTrees. -/
def Builtin.interpretUnrealizedConversionCastCTree {EIn : Type} {E : EIn → Type}
    [ErrorE -< E] [UBE -< E]
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (mem : MemoryState)
    : CTree E FreezeC (Array RuntimeValue × MemoryState × Option ControlFlowAction) := do
  let some resType := resultTypes[0]? | fail
  match resType.val, operands.toList with
  | .registerType _, [.int _ value] =>
    return (#[.reg (← Builtin.intToRegCTree value)], mem, none)
  | .registerType _, [.byte _ value] =>
    return (#[.reg (← Builtin.byteToRegCTree value)], mem, none)
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
