module

public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Interpreter.RuntimeValue.Basic
public import Veir.Interpreter.Interp
public import Veir.Dialects.GMIR.OpInfo
public import Veir.Dialects.GMIR_RISCV.Semantics
meta import Veir.Meta.OpCode

namespace Veir

public section

/--
The RISC-V generic operations, LLVM's `RISCV::G_*`, which the legalizer creates and treats as legal.
Each has the semantics of its RISC-V instruction: its gMIR operation (`GMIR_RISCV.base`) on the low
32 bits, sign-extended, where a shift reads only the low 5 bits of its amount. LLVM has no
`G_ADDW`/`G_SUBW`/`G_MULW`: it selects `addw` etc. when every user reads only the low 32 bits.
-/
@[opcodes]
inductive GMIR_RISCV where
| g_addw
| g_subw
| g_mulw
| g_divw
| g_divuw
| g_remuw
| g_sllw
| g_srlw
| g_sraw
| g_clzw
| g_ctzw
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, implicit_reducible, properties_of]
def GMIR_RISCV.propertiesOf (op : GMIR_RISCV) : Type :=
match op with
| _ => Unit

def GMIR_RISCV.fromAttrDict
    (op : GMIR_RISCV) (_attrDict : Std.HashMap ByteArray Attribute) :
    Except String (GMIR_RISCV.propertiesOf op) := by
  cases op <;> exact .ok ()

def GMIR_RISCV.toAttrDict
    (_op : GMIR_RISCV) (_props : GMIR_RISCV.propertiesOf _op) :
    Std.HashMap ByteArray Attribute :=
  Std.HashMap.emptyWithCapacity 0

@[get_effects]
def GMIR_RISCV.getEffects
    (_op : GMIR_RISCV) (_props : GMIR_RISCV.propertiesOf _op) : MemoryEffects :=
  .none

def GMIR_RISCV.isConstantLike (_op : GMIR_RISCV) : Bool :=
  false

def GMIR_RISCV.isCommutative : GMIR_RISCV → Bool
  | .g_addw | .g_mulw => true
  | _ => false

def GMIR_RISCV.hasSSADominance (_op : GMIR_RISCV) (_index : Nat) : Bool :=
  true

def GMIR_RISCV.propagatesPoison (_op : GMIR_RISCV) : Bool :=
  true

#generate_dialect GMIR_RISCV

instance : IsOpCode GMIR_RISCV where
  fromName := GMIR_RISCV.fromName
  name := GMIR_RISCV.name
  propertiesOf := GMIR_RISCV.propertiesOf
  fromAttrDict := GMIR_RISCV.fromAttrDict
  toAttrDict := GMIR_RISCV.toAttrDict

/--
Verify the local invariants of a `gmir_riscv` operation in any operation-info type containing the
`gmir_riscv` dialect.
-/
def GMIR_RISCV.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo GMIR_RISCV] (opType : GMIR_RISCV) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  match opType with
  | .g_clzw | .g_ctzw => let _ ← op.verifyIntegerUnop ctx opIn
  | _ => op.verifyIntegerBinop ctx opIn
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  -- `verifyIntegerUnop` and `verifyIntegerBinop` make the operands the same type as the result.
  ((op.getResult 0).getType! ctx.raw).verifyI64
    s!"{instrName}: Expected i64 operands and result"

/-- The gMIR operation that a word operation applies to the low 32 bits of its operands. -/
def GMIR_RISCV.base : GMIR_RISCV → GMIR
  | .g_addw => .g_add
  | .g_subw => .g_sub
  | .g_mulw => .g_mul
  | .g_divw => .g_sdiv
  | .g_divuw => .g_udiv
  | .g_remuw => .g_urem
  | .g_sllw => .g_shl
  | .g_srlw => .g_lshr
  | .g_sraw => .g_ashr
  | .g_clzw => .g_ctlz
  | .g_ctzw => .g_cttz

def GMIR_RISCV.interpretOp' (opType : Veir.GMIR_RISCV) (_properties : propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    (_blockOperands : Array BlockPtr) (mem : MemoryState)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) := do
  let low (x : Data.LLVM.Int 64) := Data.LLVM.Int.trunc x 32 false false (by decide)
  let operands ← match operands.toList with
    | [.int 64 x] => pure #[.int 32 (low x)]
    | [.int 64 lhs, .int 64 rhs] =>
      let rhs := if opType matches .g_sllw | .g_srlw | .g_sraw then wordShiftAmount (low rhs)
        else low rhs
      pure #[.int 32 (low lhs), .int 32 rhs]
    | _ => none
  -- The default properties have no flags.
  let base := opType.base
  let (results, mem, _) ← GMIR.interpretOp' base (@IsOpCode.propertiesDefault GMIR _ base).default
      #[IntegerType.signless 32] operands #[] mem
  let [.int 32 result] := results.toList | none
  return (#[.int 64 (Data.LLVM.Int.sext result 64 (by decide))], mem, none)

instance : HasOpInfo GMIR_RISCV where
  verifyLocalInvariants := GMIR_RISCV.verifyLocalInvariants
  propagatesPoison := GMIR_RISCV.propagatesPoison
  getEffects := GMIR_RISCV.getEffects
  isConstantLike := GMIR_RISCV.isConstantLike
  isCommutative := GMIR_RISCV.isCommutative
  hasSSADominance := GMIR_RISCV.hasSSADominance

end

end Veir
