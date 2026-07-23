module

public import Veir.Passes.Matching.Basic

public section

/-! This file contains helper functions to match operations when defining a rewrite. -/

namespace Veir

def matchRVLi (op : OperationPtr) (ctx : IRContext OpCode) : Option (propertiesOf (.riscv .li)) := do
  let (_, cst) ← matchOp op ctx (.riscv .li) 0
  return cst

def matchRVLui (op : OperationPtr) (ctx : IRContext OpCode) : Option (propertiesOf (.riscv .lui)) := do
  let (_, cst) ← matchOp op ctx (.riscv .lui) 0
  return cst

def matchRVAuipc (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .auipc)) := do
  let (op, properties) ← matchOp op ctx (.riscv .auipc) 1
  return (op[0]!,  properties)

def matchRVAddi (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .addi)) := do
  let (op, properties) ← matchOp op ctx (.riscv .addi) 1
  return (op[0]!,  properties)

def matchRVSlti (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .slti)) := do
  let (op, properties) ← matchOp op ctx (.riscv .slti) 1
  return (op[0]!,  properties)

def matchRVSltiu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .sltiu)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sltiu) 1
  return (op[0]!,  properties)

def matchRVAndi (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .andi)) := do
  let (op, properties) ← matchOp op ctx (.riscv .andi) 1
  return (op[0]!,  properties)

def matchRVOri (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .ori)) := do
  let (op, properties) ← matchOp op ctx (.riscv .ori) 1
  return (op[0]!,  properties)

def matchRVXori (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .xori)) := do
  let (op, properties) ← matchOp op ctx (.riscv .xori) 1
  return (op[0]!,  properties)

def matchRVAddiw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .addiw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .addiw) 1
  return (op[0]!,  properties)

def matchRVSlli (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .slli)) := do
  let (op, properties) ← matchOp op ctx (.riscv .slli) 1
  return (op[0]!,  properties)

def matchRVSrli (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .srli)) := do
  let (op, properties) ← matchOp op ctx (.riscv .srli) 1
  return (op[0]!,  properties)

def matchRVSrai (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .srai)) := do
  let (op, properties) ← matchOp op ctx (.riscv .srai) 1
  return (op[0]!,  properties)

def matchRVAdd (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .add)) := do
  let (op, properties) ← matchOp op ctx (.riscv .add) 2
  return (op[0]!, op[1]!, properties)

def matchRVSub (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .sub)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sub) 2
  return (op[0]!, op[1]!, properties)

def matchRVSll (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .sll)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sll) 2
  return (op[0]!, op[1]!, properties)

def matchRVSlt (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .slt)) := do
  let (op, properties) ← matchOp op ctx (.riscv .slt) 2
  return (op[0]!, op[1]!, properties)

def matchRVSltu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .sltu)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sltu) 2
  return (op[0]!, op[1]!, properties)

def matchRVXor (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .xor)) := do
  let (op, properties) ← matchOp op ctx (.riscv .xor) 2
  return (op[0]!, op[1]!, properties)

def matchRVSrl (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .srl)) := do
  let (op, properties) ← matchOp op ctx (.riscv .srl) 2
  return (op[0]!, op[1]!, properties)

def matchRVSra (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .sra)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sra) 2
  return (op[0]!, op[1]!, properties)

def matchRVOr (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .or)) := do
  let (op, properties) ← matchOp op ctx (.riscv .or) 2
  return (op[0]!, op[1]!, properties)

def matchRVAnd (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .and)) := do
  let (op, properties) ← matchOp op ctx (.riscv .and) 2
  return (op[0]!, op[1]!, properties)

def matchRVSlliw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .slliw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .slliw) 1
  return (op[0]!,  properties)

def matchRVSrliw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .srliw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .srliw) 1
  return (op[0]!,  properties)

def matchRVSraiw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .sraiw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sraiw) 1
  return (op[0]!,  properties)

def matchRVAddw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .addw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .addw) 2
  return (op[0]!, op[1]!, properties)

def matchRVSubw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .subw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .subw) 2
  return (op[0]!, op[1]!, properties)

def matchRVSllw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .sllw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sllw) 2
  return (op[0]!, op[1]!, properties)

def matchRVSrlw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .srlw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .srlw) 2
  return (op[0]!, op[1]!, properties)

def matchRVSraw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .sraw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sraw) 2
  return (op[0]!, op[1]!, properties)

def matchRVRem (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .rem)) := do
  let (op, properties) ← matchOp op ctx (.riscv .rem) 2
  return (op[0]!, op[1]!, properties)

def matchRVRemu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .remu)) := do
  let (op, properties) ← matchOp op ctx (.riscv .remu) 2
  return (op[0]!, op[1]!, properties)

def matchRVRemw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .remw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .remw) 2
  return (op[0]!, op[1]!, properties)

def matchRVRemuw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .remuw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .remuw) 2
  return (op[0]!, op[1]!, properties)

def matchRVMul (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .mul)) := do
  let (op, properties) ← matchOp op ctx (.riscv .mul) 2
  return (op[0]!, op[1]!, properties)

def matchRVMulh (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .mulh)) := do
  let (op, properties) ← matchOp op ctx (.riscv .mulh) 2
  return (op[0]!, op[1]!, properties)

def matchRVMulhu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .mulhu)) := do
  let (op, properties) ← matchOp op ctx (.riscv .mulhu) 2
  return (op[0]!, op[1]!, properties)

def matchRVMulhsu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .mulhsu)) := do
  let (op, properties) ← matchOp op ctx (.riscv .mulhsu) 2
  return (op[0]!, op[1]!, properties)

def matchRVMulw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .mulw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .mulw) 2
  return (op[0]!, op[1]!, properties)

def matchRVDiv (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .div)) := do
  let (op, properties) ← matchOp op ctx (.riscv .div) 2
  return (op[0]!, op[1]!, properties)

def matchRVDivw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .divw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .divw) 2
  return (op[0]!, op[1]!, properties)

def matchRVDivu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .divu)) := do
  let (op, properties) ← matchOp op ctx (.riscv .divu) 2
  return (op[0]!, op[1]!, properties)

def matchRVDivuw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .divuw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .divuw) 2
  return (op[0]!, op[1]!, properties)

def matchRVAdduw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .adduw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .adduw) 2
  return (op[0]!, op[1]!, properties)

def matchRVSh1adduw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .sh1adduw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sh1adduw) 2
  return (op[0]!, op[1]!, properties)

def matchRVSh2adduw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .sh2adduw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sh2adduw) 2
  return (op[0]!, op[1]!, properties)

def matchRVSh3adduw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .sh3adduw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sh3adduw) 2
  return (op[0]!, op[1]!, properties)

def matchRVSh1add (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .sh1add)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sh1add) 2
  return (op[0]!, op[1]!, properties)

def matchRVSh2add (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .sh2add)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sh2add) 2
  return (op[0]!, op[1]!, properties)

def matchRVSh3add (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .sh3add)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sh3add) 2
  return (op[0]!, op[1]!, properties)

def matchRVSlliuw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .slliuw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .slliuw) 1
  return (op[0]!,  properties)

def matchRVAndn (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .andn)) := do
  let (op, properties) ← matchOp op ctx (.riscv .andn) 2
  return (op[0]!, op[1]!, properties)

def matchRVOrn (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .orn)) := do
  let (op, properties) ← matchOp op ctx (.riscv .orn) 2
  return (op[0]!, op[1]!, properties)

def matchRVXnor (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .xnor)) := do
  let (op, properties) ← matchOp op ctx (.riscv .xnor) 2
  return (op[0]!, op[1]!, properties)

def matchRVMax (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .max)) := do
  let (op, properties) ← matchOp op ctx (.riscv .max) 2
  return (op[0]!, op[1]!, properties)

def matchRVMaxu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .maxu)) := do
  let (op, properties) ← matchOp op ctx (.riscv .maxu) 2
  return (op[0]!, op[1]!, properties)

def matchRVMin (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .min)) := do
  let (op, properties) ← matchOp op ctx (.riscv .min) 2
  return (op[0]!, op[1]!, properties)

def matchRVMinu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .minu)) := do
  let (op, properties) ← matchOp op ctx (.riscv .minu) 2
  return (op[0]!, op[1]!, properties)

def matchRVRol (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .rol)) := do
  let (op, properties) ← matchOp op ctx (.riscv .rol) 2
  return (op[0]!, op[1]!, properties)

def matchRVRor (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .ror)) := do
  let (op, properties) ← matchOp op ctx (.riscv .ror) 2
  return (op[0]!, op[1]!, properties)

def matchRVRolw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .rolw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .rolw) 2
  return (op[0]!, op[1]!, properties)

def matchRVRorw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .rorw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .rorw) 2
  return (op[0]!, op[1]!, properties)

def matchRVSextb (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .sextb)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sextb) 1
  return (op[0]!,  properties)

def matchRVSexth (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .sexth)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sexth) 1
  return (op[0]!,  properties)

def matchRVZexth (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .zexth)) := do
  let (op, properties) ← matchOp op ctx (.riscv .zexth) 1
  return (op[0]!,  properties)

def matchRVClz (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .clz)) := do
  let (op, properties) ← matchOp op ctx (.riscv .clz) 1
  return (op[0]!,  properties)

def matchRVClzw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .clzw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .clzw) 1
  return (op[0]!,  properties)

def matchRVCtz (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .ctz)) := do
  let (op, properties) ← matchOp op ctx (.riscv .ctz) 1
  return (op[0]!,  properties)

def matchRVCtzw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .ctzw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .ctzw) 1
  return (op[0]!,  properties)

def matchRVCpop (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .cpop)) := do
  let (op, properties) ← matchOp op ctx (.riscv .cpop) 1
  return (op[0]!,  properties)

def matchRVCpopw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .cpopw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .cpopw) 1
  return (op[0]!,  properties)

def matchRVOrcb (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .orcb)) := do
  let (op, properties) ← matchOp op ctx (.riscv .orcb) 1
  return (op[0]!,  properties)

def matchRVRev8 (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .rev8)) := do
  let (op, properties) ← matchOp op ctx (.riscv .rev8) 1
  return (op[0]!,  properties)

def matchRVRoriw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .roriw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .roriw) 1
  return (op[0]!,  properties)

def matchRVRori (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .rori)) := do
  let (op, properties) ← matchOp op ctx (.riscv .rori) 1
  return (op[0]!,  properties)

def matchRVBclr (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .bclr)) := do
  let (op, properties) ← matchOp op ctx (.riscv .bclr) 2
  return (op[0]!, op[1]!, properties)

def matchRVBext (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .bext)) := do
  let (op, properties) ← matchOp op ctx (.riscv .bext) 2
  return (op[0]!, op[1]!, properties)

def matchRVBinv (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .binv)) := do
  let (op, properties) ← matchOp op ctx (.riscv .binv) 2
  return (op[0]!, op[1]!, properties)

def matchRVBset (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .bset)) := do
  let (op, properties) ← matchOp op ctx (.riscv .bset) 2
  return (op[0]!, op[1]!, properties)

def matchRVBclri (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .bclri)) := do
  let (op, properties) ← matchOp op ctx (.riscv .bclri) 1
  return (op[0]!,  properties)

def matchRVBexti (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .bexti)) := do
  let (op, properties) ← matchOp op ctx (.riscv .bexti) 1
  return (op[0]!,  properties)

def matchRVBinvi (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .binvi)) := do
  let (op, properties) ← matchOp op ctx (.riscv .binvi) 1
  return (op[0]!,  properties)

def matchRVBseti (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .bseti)) := do
  let (op, properties) ← matchOp op ctx (.riscv .bseti) 1
  return (op[0]!,  properties)

def matchRVPack (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .pack)) := do
  let (op, properties) ← matchOp op ctx (.riscv .pack) 2
  return (op[0]!, op[1]!, properties)

def matchRVPackh (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .packh)) := do
  let (op, properties) ← matchOp op ctx (.riscv .packh) 2
  return (op[0]!, op[1]!, properties)

def matchRVPackw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .packw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .packw) 2
  return (op[0]!, op[1]!, properties)

def matchRVCzeroeqz (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .czeroeqz)) := do
  let (op, properties) ← matchOp op ctx (.riscv .czeroeqz) 2
  return (op[0]!, op[1]!, properties)

def matchRVCzeronez (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .czeronez)) := do
  let (op, properties) ← matchOp op ctx (.riscv .czeronez) 2
  return (op[0]!, op[1]!, properties)

def matchRVLd (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .ld)) := do
  let (op, properties) ← matchOp op ctx (.riscv .ld) 1
  return (op[0]!,  properties)

def matchRVLw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .lw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .lw) 1
  return (op[0]!,  properties)

def matchRVLwu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .lwu)) := do
  let (op, properties) ← matchOp op ctx (.riscv .lwu) 1
  return (op[0]!,  properties)

def matchRVLh (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .lh)) := do
  let (op, properties) ← matchOp op ctx (.riscv .lh) 1
  return (op[0]!,  properties)

def matchRVLhu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .lhu)) := do
  let (op, properties) ← matchOp op ctx (.riscv .lhu) 1
  return (op[0]!,  properties)

def matchRVLb (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .lb)) := do
  let (op, properties) ← matchOp op ctx (.riscv .lb) 1
  return (op[0]!,  properties)

def matchRVLbu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .lbu)) := do
  let (op, properties) ← matchOp op ctx (.riscv .lbu) 1
  return (op[0]!,  properties)

def matchRVSd (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .sd)) := do
  guard (op.getOpType! ctx = .riscv .sd)
  guard (op.getNumOperands! ctx = 2)
  let operands := op.getOperands! ctx
  let properties := op.getProperties! ctx (.riscv .sd)
  return (operands[0]!, operands[1]!, properties)

def matchRVSw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .sw)) := do
  guard (op.getOpType! ctx = .riscv .sw)
  guard (op.getNumOperands! ctx = 2)
  let operands := op.getOperands! ctx
  let properties := op.getProperties! ctx (.riscv .sw)
  return (operands[0]!, operands[1]!, properties)

def matchRVSh (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .sh)) := do
  guard (op.getOpType! ctx = .riscv .sh)
  guard (op.getNumOperands! ctx = 2)
  let operands := op.getOperands! ctx
  let properties := op.getProperties! ctx (.riscv .sh)
  return (operands[0]!, operands[1]!, properties)

def matchRVSb (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf (.riscv .sb)) := do
  guard (op.getOpType! ctx = .riscv .sb)
  guard (op.getNumOperands! ctx = 2)
  let operands := op.getOperands! ctx
  let properties := op.getProperties! ctx (.riscv .sb)
  return (operands[0]!, operands[1]!, properties)

def matchRVMv (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .mv)) := do
  let (op, properties) ← matchOp op ctx (.riscv .mv) 1
  return (op[0]!,  properties)

def matchRVNot (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .not)) := do
  let (op, properties) ← matchOp op ctx (.riscv .not) 1
  return (op[0]!,  properties)

def matchRVNeg (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .neg)) := do
  let (op, properties) ← matchOp op ctx (.riscv .neg) 1
  return (op[0]!,  properties)

def matchRVNegw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .negw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .negw) 1
  return (op[0]!,  properties)

def matchRVSextw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .sextw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sextw) 1
  return (op[0]!,  properties)

def matchRVZextb (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .zextb)) := do
  let (op, properties) ← matchOp op ctx (.riscv .zextb) 1
  return (op[0]!,  properties)

def matchRVZextw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .zextw)) := do
  let (op, properties) ← matchOp op ctx (.riscv .zextw) 1
  return (op[0]!,  properties)

def matchRVSeqz (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .seqz)) := do
  let (op, properties) ← matchOp op ctx (.riscv .seqz) 1
  return (op[0]!,  properties)

def matchRVSnez (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .snez)) := do
  let (op, properties) ← matchOp op ctx (.riscv .snez) 1
  return (op[0]!,  properties)

def matchRVSltz (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .sltz)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sltz) 1
  return (op[0]!,  properties)

def matchRVSgtz (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf (.riscv .sgtz)) := do
  let (op, properties) ← matchOp op ctx (.riscv .sgtz) 1
  return (op[0]!,  properties)
