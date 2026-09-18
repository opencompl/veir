module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.RISCV.Properties
public import Veir.ConstantMaterialization
import Veir.Dialects.Builtin.Properties
meta import Veir.Meta.OpCode
public import Veir.Interpreter.RuntimeValue.Basic
public import Veir.Interpreter.Interp
public import Veir.Interpreter.Memory
import Veir.Data.RISCV.Reg.Basic

open Veir.Data

namespace Veir

public section

@[opcodes]
inductive Riscv where
| li
| lui
| auipc
| addi
| slti
| sltiu
| andi
| ori
| xori
| addiw
| slli
| srli
| srai
| add
| sub
| sll
| slt
| sltu
| xor
| srl
| sra
| or
| and
| slliw
| srliw
| sraiw
| addw
| subw
| sllw
| srlw
| sraw
| rem
| remu
| remw
| remuw
| mul
| mulh
| mulhu
| mulhsu
| mulw
| div
| divw
| divu
| divuw
| adduw
| sh1adduw
| sh2adduw
| sh3adduw
| sh1add
| sh2add
| sh3add
| slliuw
| andn
| orn
| xnor
| max
| maxu
| min
| minu
| rol
| ror
| rolw
| rorw
| sextb
| sexth
| zexth
| clz
| clzw
| ctz
| ctzw
| cpop
| cpopw
| orcb
| rev8
| roriw
| rori
| bclr
| bext
| binv
| bset
| bclri
| bexti
| binvi
| bseti
| pack
| packh
| packw
| czeroeqz
| czeronez
/- memory -/
| ld
| lw
| lwu
| lh
| lhu
| lb
| lbu
| sd
| sw
| sh
| sb

/- pseudooperations -/
| mv
| not
| neg
| negw
| sextw
| zextb
| zextw
| seqz
| snez
| sltz
| sgtz
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def Riscv.propertiesOf (op : Riscv) : Type :=
match op with
| .li => RISCVImmediateProperties
| .lui => RISCVImmediateProperties
| .auipc => RISCVImmediateProperties
| .andi => RISCVImmediateProperties
| .ori => RISCVImmediateProperties
| .xori => RISCVImmediateProperties
| .addi => RISCVImmediateProperties
| .slti => RISCVImmediateProperties
| .sltiu => RISCVImmediateProperties
| .addiw => RISCVImmediateProperties
| .slli => RISCVImmediateProperties
| .srli => RISCVImmediateProperties
| .srai => RISCVImmediateProperties
| .slliw => RISCVImmediateProperties
| .srliw => RISCVImmediateProperties
| .sraiw => RISCVImmediateProperties
| .slliuw => RISCVImmediateProperties
| .rori => RISCVImmediateProperties
| .roriw => RISCVImmediateProperties
| .bclri => RISCVImmediateProperties
| .bexti => RISCVImmediateProperties
| .binvi => RISCVImmediateProperties
| .bseti => RISCVImmediateProperties
/- The memory ops carry an offset immediate plus a volatile flag. -/
| .ld => RISCVMemProperties
| .lw => RISCVMemProperties
| .lwu => RISCVMemProperties
| .lh => RISCVMemProperties
| .lhu => RISCVMemProperties
| .lb => RISCVMemProperties
| .lbu => RISCVMemProperties
| .sd => RISCVMemProperties
| .sw => RISCVMemProperties
| .sh => RISCVMemProperties
| .sb => RISCVMemProperties
| _ => Unit

def Riscv.fromAttrDict
    (op : Riscv) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (Riscv.propertiesOf op) := by
  cases op
  case li | lui | auipc | andi | ori | xori | addi | slti | sltiu
      | addiw | slli | srli | srai | slliw | srliw | sraiw | slliuw
      | rori | roriw | bclri | bexti | binvi | bseti =>
    exact RISCVImmediateProperties.fromAttrDict attrDict
  case ld | lw | lwu | lh | lhu | lb | lbu | sd | sw | sh | sb =>
    exact RISCVMemProperties.fromAttrDict attrDict
  all_goals exact .ok ()

def Riscv.toAttrDict
    (op : Riscv) (props : Riscv.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .li | .lui | .auipc | .andi | .ori | .xori
  | .addi | .slti | .sltiu | .addiw | .slli | .srli | .srai
  | .slliw | .srliw | .sraiw | .rori | .roriw | .slliuw
  | .bclri | .bexti | .binvi | .bseti =>
    (Std.HashMap.emptyWithCapacity 2).insert
      "value".toUTF8 (i64Attr props.value)
  -- The memory ops additionally carry a volatile flag, printed only when set.
  | .ld | .lw | .lwu | .lh | .lhu | .lb | .lbu
  | .sd | .sw | .sh | .sb => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    dict := dict.insert "value".toUTF8 (i64Attr props.value)
    if props.volatile_ then
      dict := dict.insert "volatile_".toUTF8 (.unitAttr UnitAttr.mk)
    dict
  | _ => Std.HashMap.emptyWithCapacity 0

@[get_effects]
def Riscv.getEffects (op : Riscv) (props : Riscv.propertiesOf op) : MemoryEffects :=
  match op, props with
  | .ld, props | .lw, props | .lwu, props
  | .lh, props | .lhu, props
  | .lb, props | .lbu, props =>
    if props.volatile_ then .readWrite else .read
  | .sd, props | .sw, props
  | .sh, props | .sb, props =>
    if props.volatile_ then .readWrite else .write
  | .li, _ | .lui, _ | .auipc, _
  | .addi, _ | .slti, _ | .sltiu, _
  | .andi, _ | .ori, _ | .xori, _
  | .addiw, _ | .slli, _ | .srli, _ | .srai, _
  | .add, _ | .sub, _ | .sll, _ | .slt, _ | .sltu, _
  | .xor, _ | .srl, _ | .sra, _ | .or, _ | .and, _
  | .slliw, _ | .srliw, _ | .sraiw, _
  | .addw, _ | .subw, _ | .sllw, _ | .srlw, _ | .sraw, _
  | .rem, _ | .remu, _ | .remw, _ | .remuw, _
  | .mul, _ | .mulh, _ | .mulhu, _ | .mulhsu, _ | .mulw, _
  | .div, _ | .divw, _ | .divu, _ | .divuw, _
  | .adduw, _ | .sh1adduw, _ | .sh2adduw, _ | .sh3adduw, _
  | .sh1add, _ | .sh2add, _ | .sh3add, _ | .slliuw, _
  | .andn, _ | .orn, _ | .xnor, _
  | .max, _ | .maxu, _ | .min, _ | .minu, _
  | .rol, _ | .ror, _ | .rolw, _ | .rorw, _
  | .sextb, _ | .sexth, _ | .zexth, _
  | .clz, _ | .clzw, _ | .ctz, _ | .ctzw, _
  | .cpop, _ | .cpopw, _ | .orcb, _ | .rev8, _
  | .rori, _ | .roriw, _
  | .bclr, _ | .bext, _ | .binv, _ | .bset, _
  | .bclri, _ | .bexti, _ | .binvi, _ | .bseti, _
  | .pack, _ | .packh, _ | .packw, _
  | .czeroeqz, _ | .czeronez, _
  | .mv, _ | .not, _ | .neg, _ | .negw, _
  | .sextw, _ | .zextb, _ | .zextw, _
  | .seqz, _ | .snez, _ | .sltz, _ | .sgtz, _ => .none

def Riscv.isConstantLike (op : Riscv) : Bool :=
  match op with
  | .li | .lui => true
  | _ => false

def Riscv.hasSSADominance (_op : Riscv) (_index : Nat) : Bool :=
  true

#generate_dialect Riscv

def Riscv.tryFold (op : Riscv) (properties : Riscv.propertiesOf op)
    (_resultTypes : Array TypeAttr) (constantOperands : Array (Option RuntimeValue)) :
    Option (Array FoldDecision) :=
  match op, constantOperands.toList with
  | .andi, [_] =>
    if properties.value == 0 then some #[.useConstant (.reg ⟨0⟩)] else none
  | _, _ => none

instance : IsOpCode Riscv where
  fromName := Riscv.fromName
  name := Riscv.name
  propertiesOf := Riscv.propertiesOf
  fromAttrDict := Riscv.fromAttrDict
  toAttrDict := Riscv.toAttrDict

/--
Materialize register-valued fold results as `riscv.li`. A register always holds
64 bits and so does a RISC-V immediate, so the register value *is* the immediate:
there is no width to reconcile.
-/
def Riscv.materializeConstant {OpInfo : Type} [HasOpInfo OpInfo] [HasDialect OpInfo Riscv]
    (_op : Riscv) (value : RuntimeValue) (type : TypeAttr) : Option (Materialized OpInfo) :=
  match value, type.val with
  | .reg value, .registerType _ =>
    some (.of Riscv.li (RISCVImmediateProperties.mk value.val))
  | _, _ => none

def OperationPtr.verifyRISCVimm12 {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw)
    (operands results : Nat) (imm : BitVec 64) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn operands results
  if imm.toInt < -2048 ∨ imm.toInt > 2047 then
    let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
    throw s!"{instrName} immediate out of bounds: must fit in a signed 12-bit field [-2048, 2047]"
  else
    pure ()

/--
Check that a shift-amount/bit-index immediate fits in an unsigned 5-bit field
`[0, 31]`.
-/
def OperationPtr.verifyRISCVuimm5 {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw)
    (imm : BitVec 64) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  if imm > 31#64 then
    let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
    throw s!"{instrName} immediate out of bounds: must fit in an unsigned 5-bit field [0, 31]"
  else
    pure ()

/--
Check that a shift-amount/bit-index immediate fits in an unsigned 6-bit field
`[0, 63]`.
-/
def OperationPtr.verifyRISCVuimm6 {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw)
    (imm : BitVec 64) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn 1 1
  if imm > 63#64 then
    let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
    throw s!"{instrName} immediate out of bounds: must fit in an unsigned 6-bit field [0, 63]"
  else
    pure ()

def OperationPtr.verifyRISCVneg {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw)
    (operands results : Nat) (imm : BitVec 64) : Except String PUnit := do
  op.verifyPlainOpCounts ctx opIn operands results
  if imm > 1048575#64 then
    let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
    throw s!"{instrName} immediate out of bounds: must fit in an unsigned 20-bit field."
  else
    pure ()

/-- Ensure that every operand and result has type `!riscv.reg`. -/
def OperationPtr.verifyRISCVRegisterTypes {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let opTypes := op.getOperandTypes! ctx.raw
  for i in [0:opTypes.size] do
    match (opTypes[i]!).val with
    | .registerType _ => pure ()
    | _ => throw s!"{instrName}: Expected operand {i} to have !riscv.reg type"
  for i in [0:op.getNumResults ctx.raw opIn] do
    match ((op.getResult i).get! ctx.raw).type.val with
    | .registerType _ => pure ()
    | _ => throw s!"{instrName}: Expected result {i} to have !riscv.reg type"

/--
Verify the local invariants of a `riscv` operation in any operation-info type
containing the `riscv` dialect.
-/
def Riscv.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo Riscv] (opType : Riscv) (op : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  op.verifyRISCVRegisterTypes ctx opIn
  match opType with
  | .li => do
    op.verifyPlainOpCounts ctx opIn 0 1
    pure ()
  | .lui => do
    op.verifyRISCVneg ctx opIn 0 1 (op.getProperties! ctx.raw Riscv.lui).value
    pure ()
  | .auipc => do
    op.verifyRISCVneg ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.auipc).value
    pure ()
  | .addi => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.addi).value
    pure ()
  | .slti => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.slti).value
    pure ()
  | .sltiu => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.sltiu).value
    pure ()
  | .andi => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.andi).value
    pure ()
  | .ori => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.ori).value
    pure ()
  | .xori => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.xori).value
    pure ()
  | .addiw => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.addiw).value
    pure ()
  | .slli => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.slli).value
    pure ()
  | .srli => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.srli).value
    pure ()
  | .srai => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.srai).value
    pure ()
  | .add | .sub | .sll | .slt | .sltu
  | .xor | .srl | .sra | .or | .and => do
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .slliw => do
    op.verifyRISCVuimm5 ctx opIn (op.getProperties! ctx.raw Riscv.slliw).value
    pure ()
  | .srliw => do
    op.verifyRISCVuimm5 ctx opIn (op.getProperties! ctx.raw Riscv.srliw).value
    pure ()
  | .sraiw => do
    op.verifyRISCVuimm5 ctx opIn (op.getProperties! ctx.raw Riscv.sraiw).value
    pure ()
  | .addw | .subw | .sllw | .srlw | .sraw
  | .rem | .remu | .remw | .remuw
  | .mul | .mulh | .mulhu | .mulhsu | .mulw
  | .div | .divw | .divu | .divuw
  | .adduw | .sh1adduw | .sh2adduw | .sh3adduw
  | .sh1add | .sh2add | .sh3add => do
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .slliuw => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.slliuw).value
    pure ()
  | .andn | .orn | .xnor
  | .max | .maxu | .min | .minu
  | .rol | .ror | .rolw | .rorw => do
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .sextb | .sexth | .zexth
  | .clz | .clzw | .ctz | .ctzw
  | .cpop | .cpopw | .orcb | .rev8 => do
    op.verifyPlainOpCounts ctx opIn 1 1
    pure ()
  | .roriw => do
    op.verifyRISCVuimm5 ctx opIn (op.getProperties! ctx.raw Riscv.roriw).value
    pure ()
  | .rori => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.rori).value
    pure ()
  | .bclr | .bext | .binv | .bset => do
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .bclri => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.bclri).value
    pure ()
  | .bexti => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.bexti).value
    pure ()
  | .binvi => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.binvi).value
    pure ()
  | .bseti => do
    op.verifyRISCVuimm6 ctx opIn (op.getProperties! ctx.raw Riscv.bseti).value
    pure ()
  | .pack | .packh | .packw
  | .czeroeqz | .czeronez => do
    op.verifyPlainOpCounts ctx opIn 2 1
    pure ()
  | .ld => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.ld).value
    pure ()
  | .lw => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.lw).value
    pure ()
  | .lwu => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.lwu).value
    pure ()
  | .lh => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.lh).value
    pure ()
  | .lhu => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.lhu).value
    pure ()
  | .lb => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.lb).value
    pure ()
  | .lbu => do
    op.verifyRISCVimm12 ctx opIn 1 1 (op.getProperties! ctx.raw Riscv.lbu).value
    pure ()
  | .sd => do
    op.verifyRISCVimm12 ctx opIn 2 0 (op.getProperties! ctx.raw Riscv.sd).value
    pure ()
  | .sw => do
    op.verifyRISCVimm12 ctx opIn 2 0 (op.getProperties! ctx.raw Riscv.sw).value
    pure ()
  | .sh => do
    op.verifyRISCVimm12 ctx opIn 2 0 (op.getProperties! ctx.raw Riscv.sh).value
    pure ()
  | .sb => do
    op.verifyRISCVimm12 ctx opIn 2 0 (op.getProperties! ctx.raw Riscv.sb).value
    pure ()
  | .mv | .not | .neg | .negw | .sextw
  | .zextb | .zextw | .seqz | .snez
  | .sltz | .sgtz => do
    op.verifyPlainOpCounts ctx opIn 1 1
    pure ()

/-- Effective address of a RISC-V load/store: the base register value plus the
    sign-extended 12-bit immediate offset. -/
def riscvEffectiveAddr (base : BitVec 64) (offset : BitVec 12) : BitVec 64 :=
  base + offset.signExtend 64

/-- For RISC-V sub-register loads. -/
inductive LoadExtension
  | signExt
  | zeroExt

/-- Read `bytes` of little-endian data from memory starting at
    `eaddr` and extend it to 64 bits according to `ext`. Memory is
    grown so that the access is in bounds and cannot raise UB. -/
def riscvLoad (mem : MemoryState) (eaddr : BitVec 64) (bytes : Nat) (ext : LoadExtension) :
    Interp (BitVec 64 × MemoryState) := do
  let mem := mem.ensureSize (eaddr.toNat + bytes)
  let ba ← mem.load eaddr.toNat.toUInt64 bytes.toUInt64
  let val := ba.toBitVecLE bytes
  let extended := match ext with
    | .signExt => val.signExtend 64
    | .zeroExt => val.setWidth 64
  return (extended, mem)

def Riscv.interpretOp' (opType : Veir.Riscv) (properties : propertiesOf opType)
    (_resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
    (mem : MemoryState)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .li => do
    let imm := properties.value
    return (#[.reg (RISCV.li imm)], mem, none)
  | .lui => do
    let imm := properties.immField 20
    return (#[.reg (RISCV.lui imm)], mem, none)
  | .auipc => do
    let [.reg op] := operands.toList | none
    let imm := properties.immField 20
    return (#[.reg (RISCV.auipc imm op)], mem, none)
  | .addi => do
    let [.reg op] := operands.toList | none
    let imm := properties.immField 12
    return (#[.reg (RISCV.addi imm op)], mem, none)
  | .slti => do
    let [.reg op] := operands.toList | none
    let imm := properties.immField 12
    return (#[.reg (RISCV.slti imm op)], mem, none)
  | .sltiu => do
    let [.reg op] := operands.toList | none
    let imm := properties.immField 12
    return (#[.reg (RISCV.sltiu imm op)], mem, none)
  | .andi => do
    let [.reg op] := operands.toList | none
    let imm := properties.immField 12
    return (#[.reg (RISCV.andi imm op)], mem, none)
  | .ori => do
    let [.reg op] := operands.toList | none
    let imm := properties.immField 12
    return (#[.reg (RISCV.ori imm op)], mem, none)
  | .xori => do
    let [.reg op] := operands.toList | none
    let imm := properties.immField 12
    return (#[.reg (RISCV.xori imm op)], mem, none)
  | .addiw => do
    let [.reg op] := operands.toList | none
    let imm := properties.immField 12
    return (#[.reg (RISCV.addiw imm op)], mem, none)
  | .slli => do
    let [.reg op] := operands.toList | none
    let imm := properties.immField 6
    return (#[.reg (RISCV.slli imm op)], mem, none)
  | .srli => do
    let [.reg op] := operands.toList | none
    let imm := properties.immField 6
    return (#[.reg (RISCV.srli imm op)], mem, none)
  | .srai => do
    let [.reg op] := operands.toList | none
    let imm := properties.immField 6
    return (#[.reg (RISCV.srai imm op)], mem, none)
  | .add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.add op2 op1)], mem, none)
  | .sub => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sub op2 op1)], mem, none)
  | .sll => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sll op2 op1)], mem, none)
  | .slt => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.slt op2 op1)], mem, none)
  | .sltu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sltu op2 op1)], mem, none)
  | .xor => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.xor op2 op1)], mem, none)
  | .srl => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.srl op2 op1)], mem, none)
  | .sra => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sra op2 op1)], mem, none)
  | .or => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.or op2 op1)], mem, none)
  | .and => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.and op2 op1)], mem, none)
  | .slliw => do
    let [.reg op1] := operands.toList | none
    let imm := properties.immField 5
    return (#[.reg (RISCV.slliw imm op1)], mem, none)
  | .srliw => do
    let [.reg op1] := operands.toList | none
    let imm := properties.immField 5
    return (#[.reg (RISCV.srliw imm op1)], mem, none)
  | .sraiw => do
    let [.reg op1] := operands.toList | none
    let imm := properties.immField 5
    return (#[.reg (RISCV.sraiw imm op1)], mem, none)
  | .addw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.addw op2 op1)], mem, none)
  | .subw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.subw op2 op1)], mem, none)
  | .sllw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sllw op2 op1)], mem, none)
  | .srlw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.srlw op2 op1)], mem, none)
  | .sraw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sraw op2 op1)], mem, none)
  | .rem => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.rem op2 op1)], mem, none)
  | .remu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.remu op2 op1)], mem, none)
  | .remw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.remw op2 op1)], mem, none)
  | .remuw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.remuw op2 op1)], mem, none)
  | .mul => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mul op2 op1)], mem, none)
  | .mulh => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulh op2 op1)], mem, none)
  | .mulhu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulhu op2 op1)], mem, none)
  | .mulhsu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulhsu op2 op1)], mem, none)
  | .mulw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.mulw op2 op1)], mem, none)
  | .div => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.div op2 op1)], mem, none)
  | .divw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.divw op2 op1)], mem, none)
  | .divu => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.divu op2 op1)], mem, none)
  | .divuw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.divuw op2 op1)], mem, none)
  | .adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.adduw op2 op1)], mem, none)
  | .sh1adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh1adduw op2 op1)], mem, none)
  | .sh2adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh2adduw op2 op1)], mem, none)
  | .sh3adduw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh3adduw op2 op1)], mem, none)
  | .sh1add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh1add op2 op1)], mem, none)
  | .sh2add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh2add op2 op1)], mem, none)
  | .sh3add => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.sh3add op2 op1)], mem, none)
  | .slliuw => do
    let [.reg op1] := operands.toList | none
    let imm := properties.immField 6
    return (#[.reg (RISCV.slliuw imm op1)], mem, none)
  | .andn => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.andn op2 op1)], mem, none)
  | .orn => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.orn op2 op1)], mem, none)
  | .xnor => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.xnor op2 op1)], mem, none)
  | .max => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.max op2 op1)], mem, none)
  | .maxu => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.maxu op2 op1)], mem, none)
  | .min => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.min op2 op1)], mem, none)
  | .minu => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.minu op2 op1)], mem, none)
  | .rol => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.rol op2 op1)], mem, none)
  | .ror => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.ror op2 op1)], mem, none)
  | .rolw => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.rolw op2 op1)], mem, none)
  | .rorw => do
    let [.reg op1, .reg op2,] := operands.toList | none
    return (#[.reg (RISCV.rorw op2 op1)], mem, none)
  | .sextb => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sextb op)], mem, none)
  | .sexth => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sexth op)], mem, none)
  | .zexth => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.zexth op)], mem, none)
  | .clz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.clz op)], mem, none)
  | .clzw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.clzw op)], mem, none)
  | .ctz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.ctz op)], mem, none)
  | .ctzw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.ctzw op)], mem, none)
  | .cpop => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.cpop op)], mem, none)
  | .cpopw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.cpopw op)], mem, none)
  | .orcb => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.orcb op)], mem, none)
  | .rev8 => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.rev8 op)], mem, none)
  | .roriw => do
    let [.reg op1] := operands.toList | none
    let imm := properties.immField 5
    return (#[.reg (RISCV.roriw imm op1)], mem, none)
  | .rori => do
    let [.reg op1] := operands.toList | none
    let imm := properties.immField 6
    return (#[.reg (RISCV.rori imm op1)], mem, none)
  | .bclr => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.bclr op2 op1)], mem, none)
  | .bext => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.bext op2 op1)], mem, none)
  | .binv => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.binv op2 op1)], mem, none)
  | .bset => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.bset op2 op1)], mem, none)
  | .bclri => do
    let [.reg op] := operands.toList | none
    let imm := properties.immField 6
    return (#[.reg (RISCV.bclri imm op)], mem, none)
  | .bexti => do
    let [.reg op] := operands.toList | none
    let imm := properties.immField 6
    return (#[.reg (RISCV.bexti imm op)], mem, none)
  | .binvi => do
    let [.reg op] := operands.toList | none
    let imm := properties.immField 6
    return (#[.reg (RISCV.binvi imm op)], mem, none)
  | .bseti => do
    let [.reg op] := operands.toList | none
    let imm := properties.immField 6
    return (#[.reg (RISCV.bseti imm op)], mem, none)
  | .pack => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.pack op2 op1)], mem, none)
  | .packh => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.packh op2 op1)], mem, none)
  | .packw => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.packw op2 op1)], mem, none)
  | .czeroeqz => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.czeroeqz op2 op1)], mem, none)
  | .czeronez => do
    let [.reg op1, .reg op2] := operands.toList | none
    return (#[.reg (RISCV.czeronez op2 op1)], mem, none)
  | .mv => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.mv op)], mem, none)
  | .not => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.not op)], mem, none)
  | .neg => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.neg op)], mem, none)
  | .negw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.negw op)], mem, none)
  | .sextw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sextw op)], mem, none)
  | .zextb => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.zextb op)], mem, none)
  | .zextw => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.zextw op)], mem, none)
  | .seqz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.seqz op)], mem, none)
  | .snez => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.snez op)], mem, none)
  | .sltz=> do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sltz op)], mem, none)
  | .sgtz => do
    let [.reg op] := operands.toList | none
    return (#[.reg (RISCV.sgtz op)], mem, none)
  | .ld => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.imm12
    let (val, mem) ← riscvLoad mem eaddr 8 .zeroExt
    return (#[.reg $ .mk val], mem, none)
  | .lw => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.imm12
    let (val, mem) ← riscvLoad mem eaddr 4 .signExt
    return (#[.reg $ .mk val], mem, none)
  | .lwu => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.imm12
    let (val, mem) ← riscvLoad mem eaddr 4 .zeroExt
    return (#[.reg $ .mk val], mem, none)
  | .lh => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.imm12
    let (val, mem) ← riscvLoad mem eaddr 2 .signExt
    return (#[.reg $ .mk val], mem, none)
  | .lhu => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.imm12
    let (val, mem) ← riscvLoad mem eaddr 2 .zeroExt
    return (#[.reg $ .mk val], mem, none)
  | .lb => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.imm12
    let (val, mem) ← riscvLoad mem eaddr 1 .signExt
    return (#[.reg $ .mk val], mem, none)
  | .lbu => do
    let [.reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.imm12
    let (val, mem) ← riscvLoad mem eaddr 1 .zeroExt
    return (#[.reg $ .mk val], mem, none)
  | .sd => do
    let [.reg { val }, .reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.imm12
    let mem := mem.ensureSize (eaddr.toNat + 8)
    let mem ← mem.store eaddr.toNat.toUInt64 (UInt64.ofBitVec val).toByteArrayLE
    return (#[], mem, none)
  | .sw => do
    let [.reg { val }, .reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.imm12
    let mem := mem.ensureSize (eaddr.toNat + 4)
    -- store only the low 4 bytes of the register
    let mem ← mem.store eaddr.toNat.toUInt64 ((UInt64.ofBitVec val).toByteArrayLE.extract 0 4)
    return (#[], mem, none)
  | .sh => do
    let [.reg { val }, .reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.imm12
    let mem := mem.ensureSize (eaddr.toNat + 2)
    -- store only the low 2 bytes of the register
    let mem ← mem.store eaddr.toNat.toUInt64 ((UInt64.ofBitVec val).toByteArrayLE.extract 0 2)
    return (#[], mem, none)
  | .sb => do
    let [.reg { val }, .reg addr] := operands.toList | none
    let eaddr := riscvEffectiveAddr addr.val properties.imm12
    let mem := mem.ensureSize (eaddr.toNat + 1)
    -- store only the low byte of the register
    let mem ← mem.store eaddr.toNat.toUInt64 ((UInt64.ofBitVec val).toByteArrayLE.extract 0 1)
    return (#[], mem, none)

instance : HasOpInfo Riscv where
  verifyLocalInvariants := Riscv.verifyLocalInvariants
  tryFold := Riscv.tryFold
  getEffects := Riscv.getEffects
  isConstantLike := Riscv.isConstantLike
  hasSSADominance := Riscv.hasSSADominance

end

end Veir
