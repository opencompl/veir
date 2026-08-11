module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.RISCV.Properties
meta import Veir.Meta.OpCode

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
      "value".toUTF8 (Attribute.integerAttr props.value)
  -- The memory ops additionally carry a volatile flag, printed only when set.
  | .ld | .lw | .lwu | .lh | .lhu | .lb | .lbu
  | .sd | .sw | .sh | .sb => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 2
    dict := dict.insert "value".toUTF8 (Attribute.integerAttr props.value)
    if props.volatile_ then
      dict := dict.insert "volatile_".toUTF8 (.unitAttr UnitAttr.mk)
    dict
  | _ => Std.HashMap.emptyWithCapacity 0

def Riscv.hasSideEffects (op : Riscv) (props : Riscv.propertiesOf op) : Bool :=
  match op, props with
  -- Volatile loads are definitionally side-effecting.
  | .ld, props
  | .lw, props
  | .lwu, props
  | .lh, props
  | .lhu, props
  | .lb, props
  | .lbu, props => props.volatile_
  | op, _ =>
    match op with
    | .li | .lui | .auipc
    | .addi | .slti | .sltiu
    | .andi | .ori | .xori
    | .addiw | .slli | .srli | .srai
    | .add | .sub | .sll | .slt | .sltu
    | .xor | .srl | .sra | .or | .and
    | .slliw | .srliw | .sraiw
    | .addw | .subw | .sllw | .srlw | .sraw
    | .rem | .remu | .remw | .remuw
    | .mul | .mulh | .mulhu | .mulhsu | .mulw
    | .div | .divw | .divu | .divuw
    | .adduw | .sh1adduw | .sh2adduw | .sh3adduw
    | .sh1add | .sh2add | .sh3add | .slliuw
    | .andn | .orn | .xnor
    | .max | .maxu | .min | .minu
    | .rol | .ror | .rolw | .rorw
    | .sextb | .sexth | .zexth
    | .clz | .clzw | .ctz | .ctzw
    | .cpop | .cpopw | .orcb | .rev8
    | .rori | .roriw
    | .bclr | .bext | .binv | .bset
    | .bclri | .bexti | .binvi | .bseti
    | .pack | .packh | .packw
    | .czeroeqz | .czeronez
    -- RISC-V pseudo-operations
    | .mv | .not | .neg | .negw
    | .sextw | .zextb | .zextw
    | .seqz | .snez | .sltz | .sgtz => false
    -- For everything else: be conservative!
    | _ => true

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

instance : HasOpInfo Riscv where
  fromName := Riscv.fromName
  name := Riscv.name
  propertiesOf := Riscv.propertiesOf
  fromAttrDict := Riscv.fromAttrDict
  toAttrDict := Riscv.toAttrDict
  hasSideEffects := Riscv.hasSideEffects
  getEffects := Riscv.getEffects
  isConstantLike := Riscv.isConstantLike
  hasSSADominance := Riscv.hasSSADominance

end

end Veir
