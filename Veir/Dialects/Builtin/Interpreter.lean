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

/-! ## The casts between values and registers -/

section Casts

variable {EIn : Type} {E : EIn → Type} [ErrorE -< E] [UBE -< E]
  {properties : propertiesOf Builtin.unrealized_conversion_cast} {resultTypes : Array TypeAttr}
  {type : TypeAttr} {blockOperands : Array BlockPtr} {mem : MemoryState}

/-- An integer that is not poison is cast to the register that holds its bits. -/
theorem Builtin.interpretOpCTree_cast_int_val (hType : resultTypes[0]? = some type)
    {registerType : RegisterType} (hRegister : type.val = .registerType registerType)
    {w : Nat} {x : BitVec w} :
    Builtin.interpretOpCTree (E := E) .unrealized_conversion_cast properties resultTypes
      #[.int w (.val x)] blockOperands mem = pure (#[.reg ⟨x.zeroExtend 64⟩], mem, none) := by
  unfold interpretOpCTree
  simp only [hType, hRegister]

/-- A poison integer is cast to any register. -/
theorem Builtin.interpretOpCTree_cast_int_poison (hType : resultTypes[0]? = some type)
    {registerType : RegisterType} (hRegister : type.val = .registerType registerType)
    {w : Nat} :
    Builtin.interpretOpCTree (E := E) .unrealized_conversion_cast properties resultTypes
      #[.int w .poison] blockOperands mem =
      CTree.choose (SubC := FreezeC) (FreezeCIn.mk 64) >>= fun (bits : FreezeC (.mk 64)) => pure (#[.reg ⟨bits⟩], mem, none) := by
  unfold interpretOpCTree
  simp only [hType, hRegister]

/-- A byte is cast to a register that holds its bits, with any bits for its poison bits. -/
theorem Builtin.interpretOpCTree_cast_byte (hType : resultTypes[0]? = some type)
    {registerType : RegisterType} (hRegister : type.val = .registerType registerType)
    {w : Nat} {b : Data.LLVM.Byte w} :
    Builtin.interpretOpCTree (E := E) .unrealized_conversion_cast properties resultTypes
      #[.byte w b] blockOperands mem =
      if b.poison = 0 then pure (#[.reg (LLVM.Byte.toReg b)], mem, none) else
        CTree.choose (SubC := FreezeC) (FreezeCIn.mk w) >>= fun (bits : FreezeC (.mk w)) =>
          pure (#[.reg ⟨(b.val ||| (b.poison &&& bits)).zeroExtend 64⟩], mem, none) := by
  unfold interpretOpCTree
  simp only [hType, hRegister]

/-- A register is cast to the integer of its low bits. -/
theorem Builtin.interpretOpCTree_cast_toInt (hType : resultTypes[0]? = some type)
    {integerType : IntegerType} (hInteger : type.val = .integerType integerType)
    {reg : Data.RISCV.Reg} :
    Builtin.interpretOpCTree (E := E) .unrealized_conversion_cast properties resultTypes
      #[.reg reg] blockOperands mem =
      pure (#[.int integerType.bitwidth (RISCV.Reg.toInt reg integerType.bitwidth)], mem, none) := by
  unfold interpretOpCTree
  simp only [hType, hInteger]

/-- A register is cast to the byte of its low bits. -/
theorem Builtin.interpretOpCTree_cast_toByte (hType : resultTypes[0]? = some type)
    {byteType : LLVM.ByteType} (hByte : type.val = .byteType byteType)
    {reg : Data.RISCV.Reg} :
    Builtin.interpretOpCTree (E := E) .unrealized_conversion_cast properties resultTypes
      #[.reg reg] blockOperands mem =
      pure (#[.byte byteType.bitwidth (RISCV.Reg.toByte reg byteType.bitwidth)], mem, none) := by
  unfold interpretOpCTree
  simp only [hType, hByte]

/-- A pointer that is not poison is cast to the register that holds its address. -/
theorem Builtin.interpretOpCTree_cast_addr_val (hType : resultTypes[0]? = some type)
    {registerType : RegisterType} (hRegister : type.val = .registerType registerType)
    {p : Data.Pointer} :
    Builtin.interpretOpCTree (E := E) .unrealized_conversion_cast properties resultTypes
      #[.addr (.val p)] blockOperands mem = pure (#[.reg ⟨p.address.toBitVec⟩], mem, none) := by
  unfold interpretOpCTree
  simp only [hType, hRegister, Data.LLVM.Ptr.toInt_val]

/-- A poison pointer is cast to any register. -/
theorem Builtin.interpretOpCTree_cast_addr_poison (hType : resultTypes[0]? = some type)
    {registerType : RegisterType} (hRegister : type.val = .registerType registerType) :
    Builtin.interpretOpCTree (E := E) .unrealized_conversion_cast properties resultTypes
      #[.addr .poison] blockOperands mem =
      CTree.choose (SubC := FreezeC) (FreezeCIn.mk 64) >>= fun (bits : FreezeC (.mk 64)) =>
        pure (#[.reg ⟨bits⟩], mem, none) := by
  unfold interpretOpCTree
  simp only [hType, hRegister, Data.LLVM.Ptr.toInt_poison]

/-- A register is cast to the pointer to its address. -/
theorem Builtin.interpretOpCTree_cast_toPtr (hType : resultTypes[0]? = some type)
    {pointerType : LLVM.PointerType} (hPointer : type.val = .llvmPointerType pointerType)
    {reg : Data.RISCV.Reg} :
    Builtin.interpretOpCTree (E := E) .unrealized_conversion_cast properties resultTypes
      #[.reg reg] blockOperands mem =
      pure (#[.addr (.val ⟨UInt64.ofBitVec reg.val⟩)], mem, none) := by
  unfold interpretOpCTree
  simp only [hType, hPointer, MemoryState.ptrFromInt_val]

end Casts

end Veir
