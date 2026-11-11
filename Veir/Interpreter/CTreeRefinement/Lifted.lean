module

public import Veir.Interpreter.CTreeRefinement.Monotone
public import Veir.Dialects.LLVM.CTreeMonotonicity
public import Veir.Dialects.GMIR.CTreeMonotonicity
public import Veir.Dialects.RISCV.CTreeMonotonicity
public import Veir.Interpreter.CTreeRefinement.Embedding
public import Veir.Dialects.GMIR.Lemmas
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Interpreter.Basic
import all Veir.Dialects.LLVM.Interpreter
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.RISCV.Interpreter
import all Veir.Dialects.Builtin.Interpreter
import all Veir.Interpreter.CTreeRefinement.ClosedCFG

public section

/-!
# Operations whose CTree semantics is their `Interp` semantics

Most opcodes have no CTree interpreter of their own: `Veir.CTree.interpretOp'` lifts their
`Interp` semantics. Facts about such an opcode transfer from `Interp` to CTrees, in particular
monotonicity in the operands.
-/

open CTree

namespace Veir

/-- Whether the CTree semantics of an opcode is the lift of its `Interp` semantics. -/
@[expose]
def OpCode.isLifted : OpCode → Bool
  | .llvm .freeze => false
  | .gmir .g_anyext => false
  | .gmir .g_load => false
  | .riscv op => !op.isLoad
  | .builtin _ => false
  | _ => true

namespace CTree

@[simp]
theorem ub_bind (k : α → Tree β) : (ub : Tree α) >>= k = ub := by
  rw [tree_bind_eq, bind_ub]

/-- A builtin opcode runs its CTree semantics. -/
theorem interpretOp'_builtin {op : Veir.Builtin} (properties : propertiesOf (OpCode.builtin op))
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState) :
    interpretOp' (.builtin op) properties resultTypes operands blockOperands mem =
      Builtin.interpretOpCTree op properties resultTypes operands blockOperands mem := by
  simp [interpretOp']

section Casts

variable {properties : propertiesOf (OpCode.builtin .unrealized_conversion_cast)}
  {resultTypes : Array TypeAttr} {type : TypeAttr} {blockOperands : Array BlockPtr}
  {mem : MemoryState}

/-- An integer that is not poison is cast to the register that holds its bits. -/
theorem interpretOp'_cast_int_val (hType : resultTypes[0]? = some type)
    {registerType : RegisterType} (hRegister : type.val = .registerType registerType)
    {w : Nat} {x : BitVec w} :
    interpretOp' (.builtin .unrealized_conversion_cast) properties resultTypes
      #[.int w (.val x)] blockOperands mem = pure (#[.reg ⟨x.zeroExtend 64⟩], mem, none) :=
  Builtin.interpretOpCTree_cast_int_val (properties := properties) (blockOperands := blockOperands) hType hRegister

/-- A poison integer is cast to any register. -/
theorem interpretOp'_cast_int_poison (hType : resultTypes[0]? = some type)
    {registerType : RegisterType} (hRegister : type.val = .registerType registerType)
    {w : Nat} :
    interpretOp' (.builtin .unrealized_conversion_cast) properties resultTypes
      #[.int w .poison] blockOperands mem =
      CTree.choose (SubC := FreezeC.{0}) (FreezeCIn.mk 64) >>= fun (bits : FreezeC.{0} (.mk 64)) =>
        pure (#[.reg ⟨bits⟩], mem, none) :=
  Builtin.interpretOpCTree_cast_int_poison.{0, 0} (properties := properties) (blockOperands := blockOperands) hType hRegister

/-- A byte is cast to a register that holds its bits, with any bits for its poison bits. -/
theorem interpretOp'_cast_byte (hType : resultTypes[0]? = some type)
    {registerType : RegisterType} (hRegister : type.val = .registerType registerType)
    {w : Nat} {b : Data.LLVM.Byte w} :
    interpretOp' (.builtin .unrealized_conversion_cast) properties resultTypes
      #[.byte w b] blockOperands mem =
      if b.poison = 0 then pure (#[.reg (LLVM.Byte.toReg b)], mem, none) else
        CTree.choose (SubC := FreezeC.{0}) (FreezeCIn.mk w) >>= fun (bits : FreezeC.{0} (.mk w)) =>
          pure (#[.reg ⟨(b.val ||| (b.poison &&& bits)).zeroExtend 64⟩], mem, none) :=
  Builtin.interpretOpCTree_cast_byte.{0, 0} (properties := properties) (blockOperands := blockOperands) hType hRegister

/-- A register is cast to the integer of its low bits. -/
theorem interpretOp'_cast_toInt (hType : resultTypes[0]? = some type)
    {integerType : IntegerType} (hInteger : type.val = .integerType integerType)
    {reg : Data.RISCV.Reg} :
    interpretOp' (.builtin .unrealized_conversion_cast) properties resultTypes
      #[.reg reg] blockOperands mem =
      pure (#[.int integerType.bitwidth (RISCV.Reg.toInt reg integerType.bitwidth)], mem, none) :=
  Builtin.interpretOpCTree_cast_toInt (properties := properties) (blockOperands := blockOperands) hType hInteger

/-- A register is cast to the byte of its low bits. -/
theorem interpretOp'_cast_toByte (hType : resultTypes[0]? = some type)
    {byteType : LLVM.ByteType} (hByte : type.val = .byteType byteType)
    {reg : Data.RISCV.Reg} :
    interpretOp' (.builtin .unrealized_conversion_cast) properties resultTypes
      #[.reg reg] blockOperands mem =
      pure (#[.byte byteType.bitwidth (RISCV.Reg.toByte reg byteType.bitwidth)], mem, none) :=
  Builtin.interpretOpCTree_cast_toByte (properties := properties) (blockOperands := blockOperands) hType hByte

/-- A pointer that is not poison is cast to the register that holds its address. -/
theorem interpretOp'_cast_addr_val (hType : resultTypes[0]? = some type)
    {registerType : RegisterType} (hRegister : type.val = .registerType registerType)
    {p : Data.Pointer} :
    interpretOp' (.builtin .unrealized_conversion_cast) properties resultTypes
      #[.addr (.val p)] blockOperands mem = pure (#[.reg ⟨p.address.toBitVec⟩], mem, none) :=
  Builtin.interpretOpCTree_cast_addr_val (properties := properties)
    (blockOperands := blockOperands) hType hRegister

/-- A poison pointer is cast to any register. -/
theorem interpretOp'_cast_addr_poison (hType : resultTypes[0]? = some type)
    {registerType : RegisterType} (hRegister : type.val = .registerType registerType) :
    interpretOp' (.builtin .unrealized_conversion_cast) properties resultTypes
      #[.addr .poison] blockOperands mem =
      CTree.choose (SubC := FreezeC.{0}) (FreezeCIn.mk 64) >>= fun (bits : FreezeC.{0} (.mk 64)) =>
        pure (#[.reg ⟨bits⟩], mem, none) :=
  Builtin.interpretOpCTree_cast_addr_poison.{0, 0} (properties := properties)
    (blockOperands := blockOperands) hType hRegister

/-- A register is cast to the pointer to its address. -/
theorem interpretOp'_cast_toPtr (hType : resultTypes[0]? = some type)
    {pointerType : LLVM.PointerType} (hPointer : type.val = .llvmPointerType pointerType)
    {reg : Data.RISCV.Reg} :
    interpretOp' (.builtin .unrealized_conversion_cast) properties resultTypes
      #[.reg reg] blockOperands mem =
      pure (#[.addr (.val ⟨UInt64.ofBitVec reg.val⟩)], mem, none) :=
  Builtin.interpretOpCTree_cast_toPtr (properties := properties)
    (blockOperands := blockOperands) hType hPointer

end Casts

theorem interpretOp'_eq_monadLift {opType : OpCode} (hLifted : opType.isLifted)
    (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (blockOperands : Array BlockPtr) (mem : MemoryState)
    (regions : Array RegionPtr) :
    interpretOp' opType properties resultTypes operands blockOperands mem regions =
      monadLift (Veir.interpretOp' opType properties resultTypes operands blockOperands mem) := by
  cases opType with
  | llvm op =>
    exact interpretOp'_llvm_of_ne_freeze (by rintro rfl; simp [OpCode.isLifted] at hLifted) ..
  | gmir op =>
    exact interpretOp'_gmir_of_lift (by rintro rfl; simp [OpCode.isLifted] at hLifted)
      (by rintro rfl; simp [OpCode.isLifted] at hLifted) ..
  | riscv op => exact interpretOp'_riscv (by simpa [OpCode.isLifted] using hLifted) ..
  | builtin op => simp [OpCode.isLifted] at hLifted
  | _ => rfl

/-- A lifted opcode is monotone in CTrees if it is monotone in `Interp`. -/
theorem InterpretOpTreeMonotone.of_lifted {opType : OpCode} (hLifted : opType.isLifted)
    [InterpretOp'ContextuallyMonotone opType] : InterpretOpTreeMonotone opType :=
  .of_lift fun properties resultTypes operands blockOperands mem regions =>
    interpretOp'_eq_monadLift hLifted properties resultTypes operands blockOperands mem regions

/-- The CTree semantics of an operation, with the getters that `interpretOp` uses. -/
theorem _root_.Veir.OperationPtr.interpretCTree_eq {op : OperationPtr} {ctx : WfIRContext OpCode}
    (opIn : op.InBounds ctx.raw) (operands : Array RuntimeValue) (mem : MemoryState) :
    op.interpretCTree opIn operands mem =
      interpretOp' (op.getOpType! ctx.raw) (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) operands (op.getSuccessors! ctx.raw) mem := by
  simp only [OperationPtr.interpretCTree]
  rw [interpretOp'_regions]
  congr 1 <;> grind

/-- The closed tree of an operation with a lifted opcode is the lift of its `Interp` run. -/
theorem interpretOperationTree_eq_monadLift {op : OperationPtr} {ctx : WfIRContext OpCode}
    (state : InterpreterState ctx) (opIn : op.InBounds ctx.raw)
    (hLifted : (op.getOpType! ctx.raw).isLifted) :
    interpretOperationTree op state opIn = monadLift (Veir.interpretOp op state opIn) := by
  have hOp : ∀ operands, interpretOp' (op.getOpType ctx.raw opIn)
      (op.getProperties ctx.raw (op.getOpType ctx.raw opIn)) (op.getResultTypes ctx.raw) operands
      (op.getSuccessors ctx.raw) state.memory (op.getRegions ctx.raw) =
      monadLift (op.interpret ctx.raw operands state.memory) := by
    intro operands
    rw [OperationPtr.getOpType!_eq_getOpType opIn] at hLifted
    rw [interpretOp'_eq_monadLift hLifted]
    congr 2 <;> grind
  simp only [interpretOperationTree, Veir.interpretOp]
  cases hOperands : state.variables.getOperandValues op with
  | none => simp [monadLift, MonadLift.monadLift, liftM, Interp.withBlame]
  | some operands =>
    simp only [hOp, inflate_monadLift]
    cases op.interpret ctx.raw operands state.memory with
    | ok result =>
      simp only [monadLift, MonadLift.monadLift, Interp.bind_ok]
      rcases hSet : state.variables.setResultValues? op result.fst opIn with _ | variables <;>
        simp [hSet, liftM, Interp.withBlame, monadLift, MonadLift.monadLift]
    | ub blame =>
      cases blame <;> simp [monadLift, MonadLift.monadLift, Interp.withBlame, Bind.bind]
    | fail blame =>
      cases blame <;> simp [monadLift, MonadLift.monadLift, Interp.withBlame, Bind.bind]

/-- Forget the control-flow action of an outcome. -/
abbrev dropAction (r : Array RuntimeValue × MemoryState × Option ControlFlowAction) :
    Tree (Array RuntimeValue × MemoryState × Option ControlFlowAction) :=
  pure (r.1, r.2.1, none)

/-- An opcode with CTree semantics of its own does not branch or return. -/
theorem interpretOp'_bind_dropAction {opType : OpCode} (hLifted : opType.isLifted = false)
    (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (blockOperands : Array BlockPtr) (mem : MemoryState) :
    interpretOp' opType properties resultTypes operands blockOperands mem >>= dropAction =
      interpretOp' opType properties resultTypes operands blockOperands mem := by
  cases opType with
  | llvm op =>
    cases op <;> simp [OpCode.isLifted] at hLifted
    simp only [interpretOp', Llvm.interpretOpCTree]
    repeat' split
    all_goals simp [dropAction, -bind_pure_comp]
  | gmir op =>
    cases op <;> simp [OpCode.isLifted] at hLifted
    · simp only [interpretOp', GMIR.interpretOpCTree]
      repeat' split
      all_goals simp [dropAction, -bind_pure_comp, CTree.tau_def]
    · simp only [interpretOp', GMIR.interpretOpCTree]
      rcases h : GMIR.interpretOp' .g_load properties resultTypes operands blockOperands mem with
        _ | _ | ⟨results, mem', action⟩
      · simp [monadLift, MonadLift.monadLift, tree_bind_eq]
      · simp [monadLift, MonadLift.monadLift, tree_bind_eq]
      obtain rfl : action = none := gmir_g_load_action h
      simp only [monadLift, MonadLift.monadLift, pure_bind]
      repeat' split
      all_goals simp [dropAction, -bind_pure_comp, CTree.tau_def]
  | riscv op =>
    have hLoad : op.isLoad := by simpa [OpCode.isLifted] using hLifted
    rw [Riscv.isLoad_iff] at hLoad
    cases op <;> simp at hLoad
    all_goals
      simp only [interpretOp', Riscv.interpretOpCTree, riscvLoadCTree]
      repeat' split
      all_goals simp [dropAction, -bind_pure_comp]
  | builtin op =>
    cases op <;> simp only [interpretOp', Builtin.interpretOpCTree]
    repeat' split
    all_goals simp [dropAction, -bind_pure_comp, Builtin.byteToIntCTree]
  | _ => simp [OpCode.isLifted] at hLifted

end CTree

end Veir
