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

def Riscv.readsMemory (op : Riscv) : Bool :=
  match op with
  | .ld | .lw | .lwu
  | .lh | .lhu
  | .lb | .lbu => true
  | _ => false

def Riscv.isConstantLike (op : Riscv) : Bool :=
  match op with
  | .li => true
  | _ => false

def Riscv.hasSSADominance (_op : Riscv) (_index : Nat) : Bool :=
  true

#generate_dialect Riscv

instance : HasDialectOpInfo Riscv where
  fromName := Riscv.fromName
  name := Riscv.name
  propertiesOf := Riscv.propertiesOf
  fromAttrDict := Riscv.fromAttrDict
  toAttrDict := Riscv.toAttrDict
  hasSideEffects := Riscv.hasSideEffects
  readsMemory := Riscv.readsMemory
  isConstantLike := Riscv.isConstantLike
  hasSSADominance := Riscv.hasSSADominance

end

end Veir
