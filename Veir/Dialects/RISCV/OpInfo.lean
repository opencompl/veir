module

public import Veir.IR.Simp
public import Veir.IR.OpInfo
public import Veir.Dialects.RISCV.Properties
meta import Veir.Meta.Attrs

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

instance : HasDialectOpInfo Riscv where
  propertiesOf := Riscv.propertiesOf
  hasSideEffects := Riscv.hasSideEffects
  readsMemory := Riscv.readsMemory

end

end Veir
