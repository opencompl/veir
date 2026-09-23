module

import all Veir.Passes.InstructionSelection.RISCV64
import Veir.PatternRewriter.Puddle.Builders
import Veir.Passes.Matching.LLVM.Basic

/-!
Pattern definitions used by the existing CTree validity proofs. The production selector uses
main's Puddle rewrites in `RISCV64`; these earlier formulations are retained here so the proof
work remains available while its certificates are migrated to those production definitions.
Only definitions used by certificates are kept here; pass registration lives in `RISCV64`.
-/

namespace Veir.InstructionSelection.ProofPatterns

open Puddle

/-! ## Puddle creation helpers -/

private abbrev ValueHandle := Handle OpCode .value
private abbrev TypeHandle := Handle OpCode .type

/-- Cast a matched value into an unallocated RISC-V register. -/
def castToReg (value : ValueHandle) : CreateProg.Builder ValueHandle := do
  let regType ← CreateProg.type (RegisterType.mk none)
  let props ← CreateProg.property (.builtin .unrealized_conversion_cast) ()
  let op ← CreateProg.operation (.builtin .unrealized_conversion_cast) #[value] #[regType] props
  return op.res[0]!

/-- Cast the selected register back to the matched LLVM result type. -/
def castFromReg (value : ValueHandle) (type : TypeHandle) : CreateProg.Builder CreatedOpHandle := do
  let props ← CreateProg.property (.builtin .unrealized_conversion_cast) ()
  CreateProg.operation (.builtin .unrealized_conversion_cast) #[value] #[type] props

/-- Emit a register-result instruction with concrete properties. -/
def emitRISCV (op : Riscv) (operands : Array ValueHandle) (props : Riscv.propertiesOf op) :
    CreateProg.Builder ValueHandle := do
  let regType ← CreateProg.type (RegisterType.mk none)
  let props ← CreateProg.property (.riscv op) props
  let result ← CreateProg.operation (.riscv op) operands #[regType] props
  return result.res[0]!

def emitUnit (op : Riscv) (h : Riscv.propertiesOf op = Unit) (operands : Array ValueHandle) :
    CreateProg.Builder ValueHandle := emitRISCV op operands (cast h.symm ())

def emitImm (op : Riscv) (h : Riscv.propertiesOf op = RISCVImmediateProperties)
    (operands : Array ValueHandle) (value : Int) : CreateProg.Builder ValueHandle :=
  emitRISCV op operands (cast h.symm (RISCVImmediateProperties.mk (BitVec.ofInt 64 value)))

/-! ## Retained LLVM extension and binary patterns -/

/-- Retained unary lowering with a shared operand and result type. -/
def lowerUnary (llvmOp : Llvm) (bw : Nat) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp)) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = bw)
      let x ← MatchProg.value type
      let _ ← MatchProg.root (.llvm llvmOp) #[x] #[type]
      return (type, x))
    (fun (type, x) => do
      let reg ← castToReg x
      let result ← emitRISCV riscvOp #[reg] riscvProps
      castFromReg result type)
    (fun result => result)

def ctlz32_pattern : Pattern OpCode := lowerUnary .intr__ctlz 32 .clzw ()
def ctlz64_pattern : Pattern OpCode := lowerUnary .intr__ctlz 64 .clz ()
def cttz32_pattern : Pattern OpCode := lowerUnary .intr__cttz 32 .ctzw ()
def cttz64_pattern : Pattern OpCode := lowerUnary .intr__cttz 64 .ctz ()
def ctpop32_pattern : Pattern OpCode := lowerUnary .intr__ctpop 32 .cpopw ()
def ctpop64_pattern : Pattern OpCode := lowerUnary .intr__ctpop 64 .cpop ()

def lowerExt (llvmOp : Llvm) (opBw : Nat) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp)) : Pattern OpCode :=
  Pattern.Builder
    (do
      let opType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = opBw)
      let resType ← MatchProg.type (Attr := IntegerType)
          (fun t => opBw < t.bitwidth ∧ t.bitwidth ≤ 64)
      let x ← MatchProg.value opType
      let _ ← MatchProg.root (.llvm llvmOp) #[x] #[resType]
      return (resType, x))
    (fun (resType, x) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let castProps ← CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[x] #[regType] castProps
      let riscvOpProps ← CreateProg.property (.riscv riscvOp) riscvProps
      let riscvResOp ← CreateProg.operation (.riscv riscvOp)
          #[castOp.res[0]!] #[regType] riscvOpProps
      let castBackProps ← CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[riscvResOp.res[0]!] #[resType] castBackProps
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- `llvm.sext` (`i8` operand) -> `riscv.sextb`. -/
def sext8_pattern : Pattern OpCode := lowerExt .sext 8 .sextb ()

/-- `llvm.sext` (`i16` operand) -> `riscv.sexth`. -/
def sext16_pattern : Pattern OpCode := lowerExt .sext 16 .sexth ()

/-- `llvm.sext` (`i32` operand) -> `riscv.sextw`. -/
def sext32_pattern : Pattern OpCode := lowerExt .sext 32 .sextw ()

/-- `llvm.zext` (`i8` operand) -> `riscv.zextb`. -/
def zext8_pattern : Pattern OpCode := lowerExt .zext 8 .zextb ()

/-- `llvm.zext` (`i16` operand) -> `riscv.zexth`. -/
def zext16_pattern : Pattern OpCode := lowerExt .zext 16 .zexth ()

/-- `llvm.zext` (`i32` operand) -> `riscv.zextw`. -/
def zext32_pattern : Pattern OpCode := lowerExt .zext 32 .zextw ()

def lowerBinary (llvmOp : Llvm) (typeMatcher : IntegerType → Bool) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp))
    (extend : Option (Σ extOp : Riscv, propertiesOf (OpCode.riscv extOp)) := none) :
    Pattern OpCode :=
  Pattern.Builder
    (do
      let opType ← MatchProg.type (Attr := IntegerType) typeMatcher
      let lhs ← MatchProg.value opType
      let rhs ← MatchProg.value opType
      let _ ← MatchProg.root (.llvm llvmOp) #[lhs, rhs] #[opType]
      return (opType, lhs, rhs))
    (fun (opType, lhs, rhs) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let lcastProps ← CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let lcastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[lhs] #[regType] lcastProps
      let rcastProps ← CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let rcastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[rhs] #[regType] rcastProps
      let (lval, rval) ← match extend with
        | some ⟨extOp, extProps'⟩ => do
          let extProps ← CreateProg.property (.riscv extOp) extProps'
          let lextOp ← CreateProg.operation (.riscv extOp) #[lcastOp.res[0]!] #[regType] extProps
          let rextOp ← CreateProg.operation (.riscv extOp) #[rcastOp.res[0]!] #[regType] extProps
          pure (lextOp.res[0]!, rextOp.res[0]!)
        | none => pure (lcastOp.res[0]!, rcastOp.res[0]!)
      let riscvOpProps ← CreateProg.property (.riscv riscvOp) riscvProps
      let riscvResOp ← CreateProg.operation (.riscv riscvOp)
          #[lval, rval] #[regType] riscvOpProps
      let castBackProps ← CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[riscvResOp.res[0]!] #[opType] castBackProps
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- Retained signed maximum lowering for `i64`. -/
def smax64_pattern : Pattern OpCode := lowerBinary .intr__smax (fun t => t.bitwidth = 64) .max ()
def smax32_pattern : Pattern OpCode :=
  lowerBinary .intr__smax (fun t => t.bitwidth = 32) .max () (extend := some ⟨.sextw, ()⟩)
def smin64_pattern : Pattern OpCode := lowerBinary .intr__smin (fun t => t.bitwidth = 64) .min ()
def smin32_pattern : Pattern OpCode :=
  lowerBinary .intr__smin (fun t => t.bitwidth = 32) .min () (extend := some ⟨.sextw, ()⟩)
def umax_pattern : Pattern OpCode :=
  lowerBinary .intr__umax (fun t => t.bitwidth = 64 ∨ t.bitwidth = 32) .maxu ()
def umin_pattern : Pattern OpCode :=
  lowerBinary .intr__umin (fun t => t.bitwidth = 64 ∨ t.bitwidth = 32) .minu ()

/-- `llvm.add` (`i64`) -> `riscv.add`. -/
def add64_pattern : Pattern OpCode := lowerBinary .add (fun t => t.bitwidth = 64) .add ()

/-- `llvm.add` (`i32`) -> `riscv.addw` (keeps the result sign-extended). -/
def add32_pattern : Pattern OpCode := lowerBinary .add (fun t => t.bitwidth = 32) .addw ()

/-- `llvm.sub` (`i64`) -> `riscv.sub`. -/
def sub64_pattern : Pattern OpCode := lowerBinary .sub (fun t => t.bitwidth = 64) .sub ()

/-- `llvm.sub` (`i32`) -> `riscv.subw`. -/
def sub32_pattern : Pattern OpCode := lowerBinary .sub (fun t => t.bitwidth = 32) .subw ()

/-- `llvm.mul` (`i64`) -> `riscv.mul`. -/
def mul64_pattern : Pattern OpCode := lowerBinary .mul (fun t => t.bitwidth = 64) .mul ()

/-- `llvm.mul` (`i32`) -> `riscv.mulw` (sign-extends the result). -/
def mul32_pattern : Pattern OpCode := lowerBinary .mul (fun t => t.bitwidth = 32) .mulw ()

/-- `llvm.sdiv` (`i64`) -> `riscv.div`. -/
def sdiv64_pattern : Pattern OpCode := lowerBinary .sdiv (fun t => t.bitwidth = 64) .div ()

/-- `llvm.sdiv` (`i32`) -> `riscv.divw`. -/
def sdiv32_pattern : Pattern OpCode := lowerBinary .sdiv (fun t => t.bitwidth = 32) .divw ()

/-- `llvm.udiv` (`i64`) -> `riscv.divu`. -/
def udiv64_pattern : Pattern OpCode := lowerBinary .udiv (fun t => t.bitwidth = 64) .divu ()

/-- `llvm.udiv` (`i32`) -> `riscv.divuw`. -/
def udiv32_pattern : Pattern OpCode := lowerBinary .udiv (fun t => t.bitwidth = 32) .divuw ()

/-- `llvm.srem` (`i64`) -> `riscv.rem`. -/
def srem64_pattern : Pattern OpCode := lowerBinary .srem (fun t => t.bitwidth = 64) .rem ()

/-- `llvm.srem` (`i32`) -> `riscv.remw`. -/
def srem32_pattern : Pattern OpCode := lowerBinary .srem (fun t => t.bitwidth = 32) .remw ()

/-- `llvm.urem` (`i64`) -> `riscv.remu`. -/
def urem64_pattern : Pattern OpCode := lowerBinary .urem (fun t => t.bitwidth = 64) .remu ()

/-- `llvm.urem` (`i32`) -> `riscv.remuw`. -/
def urem32_pattern : Pattern OpCode := lowerBinary .urem (fun t => t.bitwidth = 32) .remuw ()

/-- `llvm.xor` (`i64`) -> `riscv.xor`. -/
def xor64_pattern : Pattern OpCode := lowerBinary .xor (fun t => t.bitwidth = 64) .xor ()

/-- `llvm.xor` (`i32`) -> `riscv.xor` (no `W` variant needed: xor is bitwise). -/
def xor32_pattern : Pattern OpCode := lowerBinary .xor (fun t => t.bitwidth = 32) .xor ()

/-- `llvm.and` -> `riscv.and` (bitwise, so one instruction for every legal width). -/
def and_pattern : Pattern OpCode :=
  lowerBinary .and (fun t => t.bitwidth = 64 ∨ t.bitwidth = 32 ∨ t.bitwidth = 8 ∨ t.bitwidth = 1) .and ()

/-- `llvm.or` -> `riscv.or` (bitwise, so one instruction for every legal width). -/
def or_pattern : Pattern OpCode :=
  lowerBinary .or (fun t => t.bitwidth = 64 ∨ t.bitwidth = 32 ∨ t.bitwidth = 8 ∨ t.bitwidth = 1) .or ()

/-- Lower an integer operation through a register instruction sequence. -/
def lowerIntSequence (op : Llvm) (bw arity : Nat)
    (emit : Array ValueHandle → CreateProg.Builder ValueHandle) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == bw)
      let args ← (Array.range arity).mapM (fun _ => MatchProg.value type)
      let _ ← MatchProg.root (.llvm op) args #[type]
      return (type, args))
    (fun (type, args) => do
      let regs ← args.mapM castToReg
      let result ← emit regs
      castFromReg result type)
    (fun result => result)

/-- The integer decoder used by the retained proof formulations. -/
def decodeLLVMIntegerConstant (attr : IntegerAttr) : Int :=
  if attr.type.bitwidth = 1 then (BitVec.ofInt 1 attr.value).toNat
  else (BitVec.ofInt attr.type.bitwidth attr.value).toInt

/-- Decode a constant using its SSA result width, including signed attribute encodings. -/
def constantIntValue (type : TypeAttr) (props : LLVMConstantProperties) : Option Int := do
  let .integerType t := type.val | none
  let .integer attr := props.value | none
  return (BitVec.ofInt t.bitwidth (decodeLLVMIntegerConstant attr)).toInt

/-- A structural LLVM integer constant matcher, optionally restricted to zero. -/
def matchIntConstant (type : TypeHandle) (zero : Bool := false) :
    MatchProg.Builder (OpHandle (.llvm .mlir__constant)) := do
  let op ← MatchProg.operation (.llvm .mlir__constant) #[] #[type]
      (fun props => match props.value with | .integer _ => true | _ => false)
  if zero then
    MatchProg.matchNative (type, op.properties)
      (fun (type, props) => constantIntValue type props == some 0)
  return op

/-! ## Bit permutations and constants -/

/-- One SWAR bit-reversal stage: `((x & mask) << shamt) | ((x >> shamt) & mask)`. -/
def bitreverseStage (mask shamt : Int) (input : ValueHandle) : CreateProg.Builder ValueHandle := do
  let maskReg ← emitImm .li rfl #[] mask
  let low ← emitUnit .and rfl #[maskReg, input]
  let lowShift ← emitImm .slli rfl #[low] shamt
  let highShift ← emitImm .srli rfl #[input] shamt
  let high ← emitUnit .and rfl #[maskReg, highShift]
  emitUnit .or rfl #[lowShift, high]

/-- `rev8` reverses eight bytes; shift the i32 result down from the upper half. -/
def bswap_pattern (bw : Nat) : Pattern OpCode :=
  lowerIntSequence .intr__bswap bw 1 fun regs => do
    let result ← emitUnit .rev8 rfl #[regs[0]!]
    if bw == 32 then emitImm .srli rfl #[result] 32 else pure result

/-- Reverse bits within bytes with SWAR, then reverse their byte order. -/
def bitreverse_pattern (bw : Nat) : Pattern OpCode :=
  lowerIntSequence .intr__bitreverse bw 1 fun regs => do
    let x1 ← bitreverseStage (if bw == 32 then 0x55555555 else 0x5555555555555555) 1 regs[0]!
    let x2 ← bitreverseStage (if bw == 32 then 0x33333333 else 0x3333333333333333) 2 x1
    let x3 ← bitreverseStage (if bw == 32 then 0x0f0f0f0f else 0x0f0f0f0f0f0f0f0f) 4 x2
    let result ← emitUnit .rev8 rfl #[x3]
    if bw == 32 then emitImm .srli rfl #[result] 32 else pure result

/-- Materialize an LLVM integer constant of at most 64 bits in one register. -/
def constant_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth ≤ 64)
      let root ← MatchProg.root (.llvm .mlir__constant) #[] #[type]
        (fun props => match props.value with | .integer attr => attr.type.bitwidth ≤ 64 | _ => false)
      return (type, root.properties))
    (fun (type, props) => do
      let imm : Handle OpCode (.prop (.riscv .li)) ← CreateProg.applyNative (type, props)
        (fun (type, props) => do
          let value ← constantIntValue type props
          return RISCVImmediateProperties.mk (BitVec.ofInt 64 value))
      let regType ← CreateProg.type (RegisterType.mk none)
      let result ← CreateProg.operation (.riscv .li) #[] #[regType] imm
      castFromReg result.res[0]! type)
    (fun result => result)

/-! ## Shifts and comparisons -/

/-- Shifts accept both integer and byte values of width 32 or 64. -/
def lowerByteShift (llvmOp : Llvm) (bw : Nat) (riscvOp : Riscv)
    (h : Riscv.propertiesOf riscvOp = Unit) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := TypeAttr)
        (fun t => getIntByteTypeBitwidth t == some bw)
      let rhsType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == bw)
      let lhs ← MatchProg.value type
      let rhs ← MatchProg.value rhsType
      let _ ← MatchProg.root (.llvm llvmOp) #[lhs, rhs] #[type]
      return (type, lhs, rhs))
    (fun (type, lhs, rhs) => do
      let lhs ← castToReg lhs
      let rhs ← castToReg rhs
      let result ← emitUnit riscvOp h #[lhs, rhs]
      castFromReg result type)
    (fun result => result)

/-- Sign-extend i8 before `sra`; i32 uses `sraw`. -/
def ashr_pattern (bw : Nat) : Pattern OpCode :=
  lowerIntSequence .ashr bw 2 fun regs => do
    let lhs ← if bw == 8 then emitUnit .sextb rfl #[regs[0]!] else pure regs[0]!
    if bw == 32 then emitUnit .sraw rfl #[lhs, regs[1]!]
    else emitUnit .sra rfl #[lhs, regs[1]!]

/-- Narrow comparisons sign-extend both operands, preserving signed and unsigned order. -/
def icmpExtend (bw : Nat) (value : ValueHandle) : CreateProg.Builder ValueHandle :=
  if bw == 32 then emitUnit .sextw rfl #[value]
  else if bw == 8 then emitUnit .sextb rfl #[value]
  else pure value

/-- The ten LLVM comparison predicates, with zero-RHS eq/ne peepholes tried first. -/
def icmp_pattern (bw : Nat) (pred : Data.LLVM.IntPred) (zero : Bool := false) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == bw)
      let resultType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let lhs ← MatchProg.value type
      let rhs ← if zero then do
          let constant ← matchIntConstant type true
          pure constant.res[0]!
        else MatchProg.value type
      let _ ← MatchProg.root (.llvm .icmp) #[lhs, rhs] #[resultType]
        (fun props => props.predicate == pred)
      return (resultType, lhs, rhs))
    (fun (resultType, lhs, rhs) => do
      let lhs ← castToReg lhs
      let rhs ← castToReg rhs
      let lhs ← icmpExtend bw lhs
      let rhs ← icmpExtend bw rhs
      let result ← match pred with
        | .eq => do
          let diff ← if zero then pure lhs else emitUnit .xor rfl #[rhs, lhs]
          emitImm .sltiu rfl #[diff] 1
        | .ne => do
          let diff ← if zero then pure lhs else emitUnit .xor rfl #[rhs, lhs]
          let zero ← emitImm .li rfl #[] 0
          emitUnit .sltu rfl #[zero, diff]
        | .slt => emitUnit .slt rfl #[lhs, rhs]
        | .sgt => emitUnit .slt rfl #[rhs, lhs]
        | .ult => emitUnit .sltu rfl #[lhs, rhs]
        | .ugt => emitUnit .sltu rfl #[rhs, lhs]
        | .sge => do
          let cmp ← emitUnit .slt rfl #[lhs, rhs]
          emitImm .xori rfl #[cmp] 1
        | .sle => do
          let cmp ← emitUnit .slt rfl #[rhs, lhs]
          emitImm .xori rfl #[cmp] 1
        | .uge => do
          let cmp ← emitUnit .sltu rfl #[lhs, rhs]
          emitImm .xori rfl #[cmp] 1
        | .ule => do
          let cmp ← emitUnit .sltu rfl #[rhs, lhs]
          emitImm .xori rfl #[cmp] 1
      castFromReg result resultType)
    (fun result => result)

/-! ## Casts -/

/-- Lower a unary operation by a register round trip, retaining the source/result type guards. -/
def lowerCast (llvmOp : Llvm) (typeMatcher : TypeAttr → Bool)
    (guardTypes : TypeAttr × TypeAttr → Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let opType ← MatchProg.type (Attr := TypeAttr) typeMatcher
      let resType ← MatchProg.type (Attr := TypeAttr) typeMatcher
      let operand ← MatchProg.value opType
      let _ ← MatchProg.root (.llvm llvmOp) #[operand] #[resType]
      MatchProg.matchNative (opType, resType) guardTypes
      return (operand, resType))
    (fun (operand, resType) => do
      let reg ← castToReg operand
      castFromReg reg resType)
    (fun result => result)

/-- Truncate integer-to-integer or byte-to-byte, with source width at most 64. -/
def trunc_pattern : Pattern OpCode :=
  lowerCast .trunc (fun t => (getIntByteTypeBitwidth t).isSome) fun (src, dst) =>
    let sameKind := match src.val, dst.val with
      | .integerType _, .integerType _ | .byteType _, .byteType _ => true
      | _, _ => false
    match getIntByteTypeBitwidth src, getIntByteTypeBitwidth dst with
    | some srcBw, some dstBw => sameKind && decide (dstBw < srcBw ∧ srcBw ≤ 64)
    | _, _ => false

def isBitcastByteToPtr (opType resType : TypeAttr) : Bool :=
  match opType.val, resType.val with
  | .byteType _, .llvmPointerType _ => true
  | _, _ => false

def freeze_pattern : Pattern OpCode :=
  lowerCast .freeze (fun t => match t.val with
    | .integerType t => t.bitwidth = 32 ∨ t.bitwidth = 64
    | _ => false) (fun (src, dst) => src == dst)

/-- Poison may be refined to zero; retain its original result type. -/
def poisonConst_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := TypeAttr)
      let _ ← MatchProg.root (.llvm .mlir__poison) #[] #[type]
      return type)
    (fun type => do
      let reg ← emitImm .li rfl #[] 0
      castFromReg reg type)
    (fun result => result)

/-! ## Zicond selects -/

/-- Zero-arm forms precede the general branchless select. -/
def select_pattern (zeroTrue zeroFalse : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (fun t =>
        t.bitwidth = 64 ∨ t.bitwidth = 32 ∨ (t.bitwidth = 1 ∧ !zeroTrue ∧ !zeroFalse))
      let condType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let cond ← MatchProg.value condType
      let tval ← if zeroTrue then do
          let constant ← matchIntConstant type true
          pure constant.res[0]!
        else MatchProg.value type
      let fval ← if zeroFalse then do
          let constant ← matchIntConstant type true
          pure constant.res[0]!
        else MatchProg.value type
      let _ ← MatchProg.root (.llvm .select) #[cond, tval, fval] #[type]
      return (type, cond, tval, fval))
    (fun (type, cond, tval, fval) => do
      let result ← if zeroFalse then do
          let tval ← castToReg tval
          let cond ← castToReg cond
          emitUnit .czeroeqz rfl #[tval, cond]
        else if zeroTrue then do
          let fval ← castToReg fval
          let cond ← castToReg cond
          emitUnit .czeronez rfl #[fval, cond]
        else do
          let tval ← castToReg tval
          let fval ← castToReg fval
          let cond ← castToReg cond
          let eqz ← emitUnit .czeroeqz rfl #[tval, cond]
          let nez ← emitUnit .czeronez rfl #[fval, cond]
          emitUnit .or rfl #[eqz, nez]
      castFromReg result type)
    (fun result => result)

/-! ## Saturating i64 arithmetic -/

/-- Select the saturation endpoint when overflow is nonzero. -/
def signedSatSelect (wrapped overflow sat : ValueHandle) : CreateProg.Builder ValueHandle := do
  let wrappedOrZero ← emitUnit .czeronez rfl #[wrapped, overflow]
  let satOrZero ← emitUnit .czeroeqz rfl #[sat, overflow]
  emitUnit .or rfl #[satOrZero, wrappedOrZero]

/-- llvm.intr.sadd.sat.i64 -> LLVM's RV64+Zicond signed saturating-add sequence.
    Wrapped `add` + SADDO overflow `(rhs >>u 63) ^ (sum <s lhs)`
    (TargetLowering.cpp:12432 `expandAddSubSat`, overflow at 13072
    `expandSADDSUBO` add branch; sat endpoint `(sum >>s 63) ^ INT_MIN` at 12554). -/
def saddSat_pattern : Pattern OpCode :=
  lowerIntSequence .intr__sadd__sat 64 2 fun regs => do
    let lReg := regs[0]!
    let rReg := regs[1]!
    let minusOne ← emitImm .li rfl #[] (-1)
    let sum ← emitUnit .add rfl #[lReg, rReg]
    let rhsSign ← emitImm .srli rfl #[rReg] 63
    let carryLike ← emitUnit .slt rfl #[sum, lReg]
    let sumSign ← emitImm .srai rfl #[sum] 63
    let intMin ← emitImm .slli rfl #[minusOne] 63
    let overflow ← emitUnit .xor rfl #[rhsSign, carryLike]
    let sat ← emitUnit .xor rfl #[sumSign, intMin]
    signedSatSelect (sum) (overflow) (sat)

/-- llvm.intr.ssub.sat.i64 -> LLVM's RV64+Zicond signed saturating-sub sequence.
    Wrapped `sub` + SSUBO overflow `(lhs <s rhs) ^ (diff >>u 63)`
    (TargetLowering.cpp:12432 `expandAddSubSat`, overflow at 13082
    `expandSADDSUBO` sub branch; sat endpoint `(diff >>s 63) ^ INT_MIN` at 12554). -/
def ssubSat_pattern : Pattern OpCode :=
  lowerIntSequence .intr__ssub__sat 64 2 fun regs => do
    let lReg := regs[0]!
    let rReg := regs[1]!
    let minusOne ← emitImm .li rfl #[] (-1)
    let diff ← emitUnit .sub rfl #[lReg, rReg]
    let cmp ← emitUnit .slt rfl #[lReg, rReg]
    let diffSignBit ← emitImm .srli rfl #[diff] 63
    let diffSign ← emitImm .srai rfl #[diff] 63
    let intMin ← emitImm .slli rfl #[minusOne] 63
    let overflow ← emitUnit .xor rfl #[cmp, diffSignBit]
    let sat ← emitUnit .xor rfl #[diffSign, intMin]
    signedSatSelect (diff) (overflow) (sat)

/-- llvm.intr.uadd.sat.i64 -> not rhs; minu lhs, not-rhs; add rhs.
    `uadd.sat(a,b) -> umin(a, ~b) + b` (TargetLowering.cpp:12462
    `expandAddSubSat`, UADDSAT/UMIN idiom). -/
def uaddSat_pattern : Pattern OpCode :=
  lowerIntSequence .intr__uadd__sat 64 2 fun regs => do
    let lReg := regs[0]!
    let rReg := regs[1]!
    let notRhs ← emitImm .xori rfl #[rReg] (-1)
    let minuOp ← emitUnit .minu rfl #[lReg, notRhs]
    let addOp ← emitUnit .add rfl #[minuOp, rReg]
    return (addOp)

/-- llvm.intr.usub.sat.i64 -> maxu lhs, rhs; sub rhs.
    `usub.sat(a,b) -> umax(a, b) - b` (TargetLowering.cpp:12442
    `expandAddSubSat`, USUBSAT/UMAX idiom). -/
def usubSat_pattern : Pattern OpCode :=
  lowerIntSequence .intr__usub__sat 64 2 fun regs => do
    let lReg := regs[0]!
    let rReg := regs[1]!
    let maxuOp ← emitUnit .maxu rfl #[lReg, rReg]
    let subOp ← emitUnit .sub rfl #[maxuOp, rReg]
    return (subOp)

/-- llvm.intr.sshl.sat.i64 -> LLVM's RV64+Zicond signed saturating-shl sequence.
    `overflow = lhs != (lhs << rhs) >>s rhs`, saturate to
    `select(lhs<0, INT_MIN, INT_MAX)` folded to `(lhs >>s 63) ^ INT_MAX`
    (TargetLowering.cpp:12598 `expandShlSat`, signed branch at 12626-12632). -/
def sshlSat_pattern : Pattern OpCode :=
  lowerIntSequence .intr__sshl__sat 64 2 fun regs => do
    let lReg := regs[0]!
    let rReg := regs[1]!
    let shifted ← emitUnit .sll rfl #[lReg, rReg]
    let minusOne ← emitImm .li rfl #[] (-1)
    let unshifted ← emitUnit .sra rfl #[shifted, rReg]
    let sign ← emitImm .srai rfl #[lReg] 63
    let intMax ← emitImm .srli rfl #[minusOne] 1
    let overflow ← emitUnit .xor rfl #[lReg, unshifted]
    let sat ← emitUnit .xor rfl #[sign, intMax]
    signedSatSelect (shifted) (overflow) (sat)

/-- llvm.intr.ushl.sat.i64 -> LLVM's RV64 unsigned saturating-shl sequence.
    `overflow = lhs != (lhs << rhs) >>u rhs`, saturate to all-ones;
    the `select(overflow, ~0, shifted)` becomes the `sltiu`/`addi`/`or`
    mask idiom (TargetLowering.cpp:12598 `expandShlSat`, unsigned branch
    at 12630-12633). -/
def ushlSat_pattern : Pattern OpCode :=
  lowerIntSequence .intr__ushl__sat 64 2 fun regs => do
    let lReg := regs[0]!
    let rReg := regs[1]!
    let shifted ← emitUnit .sll rfl #[lReg, rReg]
    let unshifted ← emitUnit .srl rfl #[shifted, rReg]
    let lostBits ← emitUnit .xor rfl #[lReg, unshifted]
    let noOverflow ← emitImm .sltiu rfl #[lostBits] 1
    let overflowMask ← emitImm .addi rfl #[noOverflow] (-1)
    let orOp ← emitUnit .or rfl #[overflowMask, shifted]
    return (orOp)

/-- llvm.intr.abs.i64 -> `max(x, -x)` via Zbb `neg`/`max`.
    LLVM's RV64+Zbb lowering (`neg a1, a0; max a0, a0, a1`). The `neg` wraps
    `intMin` back to `intMin`, so this is correct for both the
    `is_int_min_poison` and non-poison forms of the intrinsic. -/
def abs_pattern : Pattern OpCode :=
  lowerIntSequence .intr__abs 64 1 fun regs => do
    let xReg := regs[0]!
    let negOp ← emitUnit .neg rfl #[xReg]
    let maxOp ← emitUnit .max rfl #[xReg, negOp]
    return (maxOp)

/-! ## Constant rotates and general funnel shifts -/

/-- Constant rotate-left uses rotate-right with the negated amount modulo the width. -/
def lowerConstRotate (left : Bool) (bw : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == bw)
      let val ← MatchProg.value type
      let amt ← matchIntConstant type
      let _ ← MatchProg.root (.llvm (if left then .intr__fshl else .intr__fshr))
        #[val, val, amt.res[0]!] #[type]
      return (type, val, amt.properties))
    (fun (type, val, amtProps) => do
      let val ← castToReg val
      let imm : Handle OpCode (.prop (.riscv .rori)) ← CreateProg.applyNative (type, amtProps)
        (fun (type, props) => do
          let amt ← constantIntValue type props
          let sh := ((amt % (bw : Int)) + bw) % bw
          let imm := if left then ((bw : Int) - sh) % bw else sh
          return RISCVImmediateProperties.mk (BitVec.ofInt 64 imm))
      let regType ← CreateProg.type (RegisterType.mk none)
      let result ← if bw == 32 then do
          let imm32 : Handle OpCode (.prop (.riscv .roriw)) ←
            CreateProg.applyNative imm (fun props => some props)
          CreateProg.operation (.riscv .roriw) #[val] #[regType] imm32
        else CreateProg.operation (.riscv .rori) #[val] #[regType] imm
      castFromReg result.res[0]! type)
    (fun result => result)

/-- General fshl: `(x << z) | ((y >> 1) >> ~z)`; general fshr:
  `((x << 1) << ~z) | (y >> z)`. The pre-shift handles a zero shift amount.
  i32 uses word shifts; hardware masks each variable shift amount modulo the width. -/
def lowerFunnelShift (left : Bool) (bw : Nat) : Pattern OpCode :=
  lowerIntSequence (if left then .intr__fshl else .intr__fshr) bw 3 fun regs => do
    let x := regs[0]!
    let y := regs[1]!
    let z := regs[2]!
    let notz ← emitImm .xori rfl #[z] (-1)
    let (shx, shy) ← if left then do
        let shx ← if bw == 32 then emitUnit .sllw rfl #[x, z] else emitUnit .sll rfl #[x, z]
        let y1 ← if bw == 32 then emitImm .srliw rfl #[y] 1 else emitImm .srli rfl #[y] 1
        let shy ← if bw == 32 then emitUnit .srlw rfl #[y1, notz] else emitUnit .srl rfl #[y1, notz]
        pure (shx, shy)
      else do
        let x1 ← if bw == 32 then emitImm .slliw rfl #[x] 1 else emitImm .slli rfl #[x] 1
        let shx ← if bw == 32 then emitUnit .sllw rfl #[x1, notz] else emitUnit .sll rfl #[x1, notz]
        let shy ← if bw == 32 then emitUnit .srlw rfl #[y, z] else emitUnit .srl rfl #[y, z]
        pure (shx, shy)
    emitUnit .or rfl #[shx, shy]

end Veir.InstructionSelection.ProofPatterns
