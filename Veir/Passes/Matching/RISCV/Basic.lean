module

public import Veir.Passes.Matching.Basic
public import Veir.Dialects.RISCV.OpInfo

public section

/-! This file contains helper functions to match operations when defining a rewrite. -/

namespace Veir

variable {OpCode : Type} [HasOpInfo OpCode] [HasDialect OpCode Riscv]

def matchRVLi (op : OperationPtr) (ctx : IRContext OpCode) : Option (propertiesOf Riscv.li) := do
  let (_, cst) ← matchOp op ctx Riscv.li 0
  return cst

def matchRVLui (op : OperationPtr) (ctx : IRContext OpCode) : Option (propertiesOf Riscv.lui) := do
  let (_, cst) ← matchOp op ctx Riscv.lui 0
  return cst

def matchRVAuipc (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.auipc) := do
  let (op, properties) ← matchOp op ctx Riscv.auipc 1
  return (op[0]!,  properties)

def matchRVAddi (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.addi) := do
  let (op, properties) ← matchOp op ctx Riscv.addi 1
  return (op[0]!,  properties)

def matchRVSlti (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.slti) := do
  let (op, properties) ← matchOp op ctx Riscv.slti 1
  return (op[0]!,  properties)

def matchRVSltiu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.sltiu) := do
  let (op, properties) ← matchOp op ctx Riscv.sltiu 1
  return (op[0]!,  properties)

def matchRVAndi (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.andi) := do
  let (op, properties) ← matchOp op ctx Riscv.andi 1
  return (op[0]!,  properties)

def matchRVOri (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.ori) := do
  let (op, properties) ← matchOp op ctx Riscv.ori 1
  return (op[0]!,  properties)

def matchRVXori (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.xori) := do
  let (op, properties) ← matchOp op ctx Riscv.xori 1
  return (op[0]!,  properties)

def matchRVAddiw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.addiw) := do
  let (op, properties) ← matchOp op ctx Riscv.addiw 1
  return (op[0]!,  properties)

def matchRVSlli (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.slli) := do
  let (op, properties) ← matchOp op ctx Riscv.slli 1
  return (op[0]!,  properties)

def matchRVSrli (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.srli) := do
  let (op, properties) ← matchOp op ctx Riscv.srli 1
  return (op[0]!,  properties)

def matchRVSrai (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.srai) := do
  let (op, properties) ← matchOp op ctx Riscv.srai 1
  return (op[0]!,  properties)

def matchRVAdd (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.add) := do
  let (op, properties) ← matchOp op ctx Riscv.add 2
  return (op[0]!, op[1]!, properties)

def matchRVSub (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.sub) := do
  let (op, properties) ← matchOp op ctx Riscv.sub 2
  return (op[0]!, op[1]!, properties)

def matchRVSll (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.sll) := do
  let (op, properties) ← matchOp op ctx Riscv.sll 2
  return (op[0]!, op[1]!, properties)

def matchRVSlt (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.slt) := do
  let (op, properties) ← matchOp op ctx Riscv.slt 2
  return (op[0]!, op[1]!, properties)

def matchRVSltu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.sltu) := do
  let (op, properties) ← matchOp op ctx Riscv.sltu 2
  return (op[0]!, op[1]!, properties)

def matchRVXor (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.xor) := do
  let (op, properties) ← matchOp op ctx Riscv.xor 2
  return (op[0]!, op[1]!, properties)

def matchRVSrl (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.srl) := do
  let (op, properties) ← matchOp op ctx Riscv.srl 2
  return (op[0]!, op[1]!, properties)

def matchRVSra (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.sra) := do
  let (op, properties) ← matchOp op ctx Riscv.sra 2
  return (op[0]!, op[1]!, properties)

def matchRVOr (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.or) := do
  let (op, properties) ← matchOp op ctx Riscv.or 2
  return (op[0]!, op[1]!, properties)

def matchRVAnd (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.and) := do
  let (op, properties) ← matchOp op ctx Riscv.and 2
  return (op[0]!, op[1]!, properties)

def matchRVSlliw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.slliw) := do
  let (op, properties) ← matchOp op ctx Riscv.slliw 1
  return (op[0]!,  properties)

def matchRVSrliw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.srliw) := do
  let (op, properties) ← matchOp op ctx Riscv.srliw 1
  return (op[0]!,  properties)

def matchRVSraiw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.sraiw) := do
  let (op, properties) ← matchOp op ctx Riscv.sraiw 1
  return (op[0]!,  properties)

def matchRVAddw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.addw) := do
  let (op, properties) ← matchOp op ctx Riscv.addw 2
  return (op[0]!, op[1]!, properties)

def matchRVSubw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.subw) := do
  let (op, properties) ← matchOp op ctx Riscv.subw 2
  return (op[0]!, op[1]!, properties)

def matchRVSllw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.sllw) := do
  let (op, properties) ← matchOp op ctx Riscv.sllw 2
  return (op[0]!, op[1]!, properties)

def matchRVSrlw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.srlw) := do
  let (op, properties) ← matchOp op ctx Riscv.srlw 2
  return (op[0]!, op[1]!, properties)

def matchRVSraw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.sraw) := do
  let (op, properties) ← matchOp op ctx Riscv.sraw 2
  return (op[0]!, op[1]!, properties)

def matchRVRem (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.rem) := do
  let (op, properties) ← matchOp op ctx Riscv.rem 2
  return (op[0]!, op[1]!, properties)

def matchRVRemu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.remu) := do
  let (op, properties) ← matchOp op ctx Riscv.remu 2
  return (op[0]!, op[1]!, properties)

def matchRVRemw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.remw) := do
  let (op, properties) ← matchOp op ctx Riscv.remw 2
  return (op[0]!, op[1]!, properties)

def matchRVRemuw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.remuw) := do
  let (op, properties) ← matchOp op ctx Riscv.remuw 2
  return (op[0]!, op[1]!, properties)

def matchRVMul (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.mul) := do
  let (op, properties) ← matchOp op ctx Riscv.mul 2
  return (op[0]!, op[1]!, properties)

def matchRVMulh (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.mulh) := do
  let (op, properties) ← matchOp op ctx Riscv.mulh 2
  return (op[0]!, op[1]!, properties)

def matchRVMulhu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.mulhu) := do
  let (op, properties) ← matchOp op ctx Riscv.mulhu 2
  return (op[0]!, op[1]!, properties)

def matchRVMulhsu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.mulhsu) := do
  let (op, properties) ← matchOp op ctx Riscv.mulhsu 2
  return (op[0]!, op[1]!, properties)

def matchRVMulw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.mulw) := do
  let (op, properties) ← matchOp op ctx Riscv.mulw 2
  return (op[0]!, op[1]!, properties)

def matchRVDiv (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.div) := do
  let (op, properties) ← matchOp op ctx Riscv.div 2
  return (op[0]!, op[1]!, properties)

def matchRVDivw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.divw) := do
  let (op, properties) ← matchOp op ctx Riscv.divw 2
  return (op[0]!, op[1]!, properties)

def matchRVDivu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.divu) := do
  let (op, properties) ← matchOp op ctx Riscv.divu 2
  return (op[0]!, op[1]!, properties)

def matchRVDivuw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.divuw) := do
  let (op, properties) ← matchOp op ctx Riscv.divuw 2
  return (op[0]!, op[1]!, properties)

def matchRVAdduw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.adduw) := do
  let (op, properties) ← matchOp op ctx Riscv.adduw 2
  return (op[0]!, op[1]!, properties)

def matchRVSh1adduw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.sh1adduw) := do
  let (op, properties) ← matchOp op ctx Riscv.sh1adduw 2
  return (op[0]!, op[1]!, properties)

def matchRVSh2adduw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.sh2adduw) := do
  let (op, properties) ← matchOp op ctx Riscv.sh2adduw 2
  return (op[0]!, op[1]!, properties)

def matchRVSh3adduw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.sh3adduw) := do
  let (op, properties) ← matchOp op ctx Riscv.sh3adduw 2
  return (op[0]!, op[1]!, properties)

def matchRVSh1add (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.sh1add) := do
  let (op, properties) ← matchOp op ctx Riscv.sh1add 2
  return (op[0]!, op[1]!, properties)

def matchRVSh2add (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.sh2add) := do
  let (op, properties) ← matchOp op ctx Riscv.sh2add 2
  return (op[0]!, op[1]!, properties)

def matchRVSh3add (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.sh3add) := do
  let (op, properties) ← matchOp op ctx Riscv.sh3add 2
  return (op[0]!, op[1]!, properties)

def matchRVSlliuw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.slliuw) := do
  let (op, properties) ← matchOp op ctx Riscv.slliuw 1
  return (op[0]!,  properties)

def matchRVAndn (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.andn) := do
  let (op, properties) ← matchOp op ctx Riscv.andn 2
  return (op[0]!, op[1]!, properties)

def matchRVOrn (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.orn) := do
  let (op, properties) ← matchOp op ctx Riscv.orn 2
  return (op[0]!, op[1]!, properties)

def matchRVXnor (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.xnor) := do
  let (op, properties) ← matchOp op ctx Riscv.xnor 2
  return (op[0]!, op[1]!, properties)

def matchRVMax (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.max) := do
  let (op, properties) ← matchOp op ctx Riscv.max 2
  return (op[0]!, op[1]!, properties)

def matchRVMaxu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.maxu) := do
  let (op, properties) ← matchOp op ctx Riscv.maxu 2
  return (op[0]!, op[1]!, properties)

def matchRVMin (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.min) := do
  let (op, properties) ← matchOp op ctx Riscv.min 2
  return (op[0]!, op[1]!, properties)

def matchRVMinu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.minu) := do
  let (op, properties) ← matchOp op ctx Riscv.minu 2
  return (op[0]!, op[1]!, properties)

def matchRVRol (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.rol) := do
  let (op, properties) ← matchOp op ctx Riscv.rol 2
  return (op[0]!, op[1]!, properties)

def matchRVRor (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.ror) := do
  let (op, properties) ← matchOp op ctx Riscv.ror 2
  return (op[0]!, op[1]!, properties)

def matchRVRolw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.rolw) := do
  let (op, properties) ← matchOp op ctx Riscv.rolw 2
  return (op[0]!, op[1]!, properties)

def matchRVRorw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.rorw) := do
  let (op, properties) ← matchOp op ctx Riscv.rorw 2
  return (op[0]!, op[1]!, properties)

def matchRVSextb (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.sextb) := do
  let (op, properties) ← matchOp op ctx Riscv.sextb 1
  return (op[0]!,  properties)

def matchRVSexth (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.sexth) := do
  let (op, properties) ← matchOp op ctx Riscv.sexth 1
  return (op[0]!,  properties)

def matchRVZexth (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.zexth) := do
  let (op, properties) ← matchOp op ctx Riscv.zexth 1
  return (op[0]!,  properties)

def matchRVClz (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.clz) := do
  let (op, properties) ← matchOp op ctx Riscv.clz 1
  return (op[0]!,  properties)

def matchRVClzw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.clzw) := do
  let (op, properties) ← matchOp op ctx Riscv.clzw 1
  return (op[0]!,  properties)

def matchRVCtz (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.ctz) := do
  let (op, properties) ← matchOp op ctx Riscv.ctz 1
  return (op[0]!,  properties)

def matchRVCtzw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.ctzw) := do
  let (op, properties) ← matchOp op ctx Riscv.ctzw 1
  return (op[0]!,  properties)

def matchRVCpop (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.cpop) := do
  let (op, properties) ← matchOp op ctx Riscv.cpop 1
  return (op[0]!,  properties)

def matchRVCpopw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.cpopw) := do
  let (op, properties) ← matchOp op ctx Riscv.cpopw 1
  return (op[0]!,  properties)

def matchRVOrcb (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.orcb) := do
  let (op, properties) ← matchOp op ctx Riscv.orcb 1
  return (op[0]!,  properties)

def matchRVRev8 (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.rev8) := do
  let (op, properties) ← matchOp op ctx Riscv.rev8 1
  return (op[0]!,  properties)

def matchRVRoriw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.roriw) := do
  let (op, properties) ← matchOp op ctx Riscv.roriw 1
  return (op[0]!,  properties)

def matchRVRori (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.rori) := do
  let (op, properties) ← matchOp op ctx Riscv.rori 1
  return (op[0]!,  properties)

def matchRVBclr (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.bclr) := do
  let (op, properties) ← matchOp op ctx Riscv.bclr 2
  return (op[0]!, op[1]!, properties)

def matchRVBext (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.bext) := do
  let (op, properties) ← matchOp op ctx Riscv.bext 2
  return (op[0]!, op[1]!, properties)

def matchRVBinv (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.binv) := do
  let (op, properties) ← matchOp op ctx Riscv.binv 2
  return (op[0]!, op[1]!, properties)

def matchRVBset (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.bset) := do
  let (op, properties) ← matchOp op ctx Riscv.bset 2
  return (op[0]!, op[1]!, properties)

def matchRVBclri (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.bclri) := do
  let (op, properties) ← matchOp op ctx Riscv.bclri 1
  return (op[0]!,  properties)

def matchRVBexti (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.bexti) := do
  let (op, properties) ← matchOp op ctx Riscv.bexti 1
  return (op[0]!,  properties)

def matchRVBinvi (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.binvi) := do
  let (op, properties) ← matchOp op ctx Riscv.binvi 1
  return (op[0]!,  properties)

def matchRVBseti (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.bseti) := do
  let (op, properties) ← matchOp op ctx Riscv.bseti 1
  return (op[0]!,  properties)

def matchRVPack (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.pack) := do
  let (op, properties) ← matchOp op ctx Riscv.pack 2
  return (op[0]!, op[1]!, properties)

def matchRVPackh (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.packh) := do
  let (op, properties) ← matchOp op ctx Riscv.packh 2
  return (op[0]!, op[1]!, properties)

def matchRVPackw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.packw) := do
  let (op, properties) ← matchOp op ctx Riscv.packw 2
  return (op[0]!, op[1]!, properties)

def matchRVCzeroeqz (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.czeroeqz) := do
  let (op, properties) ← matchOp op ctx Riscv.czeroeqz 2
  return (op[0]!, op[1]!, properties)

def matchRVCzeronez (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.czeronez) := do
  let (op, properties) ← matchOp op ctx Riscv.czeronez 2
  return (op[0]!, op[1]!, properties)

def matchRVLd (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.ld) := do
  let (op, properties) ← matchOp op ctx Riscv.ld 1
  return (op[0]!,  properties)

def matchRVLw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.lw) := do
  let (op, properties) ← matchOp op ctx Riscv.lw 1
  return (op[0]!,  properties)

def matchRVLwu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.lwu) := do
  let (op, properties) ← matchOp op ctx Riscv.lwu 1
  return (op[0]!,  properties)

def matchRVLh (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.lh) := do
  let (op, properties) ← matchOp op ctx Riscv.lh 1
  return (op[0]!,  properties)

def matchRVLhu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.lhu) := do
  let (op, properties) ← matchOp op ctx Riscv.lhu 1
  return (op[0]!,  properties)

def matchRVLb (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.lb) := do
  let (op, properties) ← matchOp op ctx Riscv.lb 1
  return (op[0]!,  properties)

def matchRVLbu (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.lbu) := do
  let (op, properties) ← matchOp op ctx Riscv.lbu 1
  return (op[0]!,  properties)

def matchRVSd (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.sd) := do
  guard (op.getOpType! ctx = Riscv.sd)
  guard (op.getNumOperands! ctx = 2)
  let operands := op.getOperands! ctx
  let properties := op.getProperties! ctx Riscv.sd
  return (operands[0]!, operands[1]!, properties)

def matchRVSw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.sw) := do
  guard (op.getOpType! ctx = Riscv.sw)
  guard (op.getNumOperands! ctx = 2)
  let operands := op.getOperands! ctx
  let properties := op.getProperties! ctx Riscv.sw
  return (operands[0]!, operands[1]!, properties)

def matchRVSh (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.sh) := do
  guard (op.getOpType! ctx = Riscv.sh)
  guard (op.getNumOperands! ctx = 2)
  let operands := op.getOperands! ctx
  let properties := op.getProperties! ctx Riscv.sh
  return (operands[0]!, operands[1]!, properties)

def matchRVSb (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × ValuePtr × propertiesOf Riscv.sb) := do
  guard (op.getOpType! ctx = Riscv.sb)
  guard (op.getNumOperands! ctx = 2)
  let operands := op.getOperands! ctx
  let properties := op.getProperties! ctx Riscv.sb
  return (operands[0]!, operands[1]!, properties)

def matchRVMv (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.mv) := do
  let (op, properties) ← matchOp op ctx Riscv.mv 1
  return (op[0]!,  properties)

def matchRVNot (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.not) := do
  let (op, properties) ← matchOp op ctx Riscv.not 1
  return (op[0]!,  properties)

def matchRVNeg (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.neg) := do
  let (op, properties) ← matchOp op ctx Riscv.neg 1
  return (op[0]!,  properties)

def matchRVNegw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.negw) := do
  let (op, properties) ← matchOp op ctx Riscv.negw 1
  return (op[0]!,  properties)

def matchRVSextw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.sextw) := do
  let (op, properties) ← matchOp op ctx Riscv.sextw 1
  return (op[0]!,  properties)

def matchRVZextb (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.zextb) := do
  let (op, properties) ← matchOp op ctx Riscv.zextb 1
  return (op[0]!,  properties)

def matchRVZextw (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.zextw) := do
  let (op, properties) ← matchOp op ctx Riscv.zextw 1
  return (op[0]!,  properties)

def matchRVSeqz (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.seqz) := do
  let (op, properties) ← matchOp op ctx Riscv.seqz 1
  return (op[0]!,  properties)

def matchRVSnez (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.snez) := do
  let (op, properties) ← matchOp op ctx Riscv.snez 1
  return (op[0]!,  properties)

def matchRVSltz (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.sltz) := do
  let (op, properties) ← matchOp op ctx Riscv.sltz 1
  return (op[0]!,  properties)

def matchRVSgtz (op : OperationPtr) (ctx : IRContext OpCode) : Option (ValuePtr × propertiesOf Riscv.sgtz) := do
  let (op, properties) ← matchOp op ctx Riscv.sgtz 1
  return (op[0]!,  properties)
