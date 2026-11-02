module

public import Veir.IR.OpInfo
public import Veir.Interfaces.ControlFlowInterfaces
public import Veir.Verifier.Basic
public import Veir.Dialects.LLVM.Properties
public import Veir.Dialects.GMIR.Properties
public import Veir.ConstantMaterialization
public import Veir.Interpreter.RuntimeValue.Basic
public import Veir.Interpreter.Interp
public import Veir.Interpreter.Memory
public import Veir.Data.LLVM.Int.Basic
public import Veir.Dialects.GMIR.Semantics
import Veir.Dialects.Builtin.Properties
meta import Veir.Meta.OpCode

namespace Veir

public section

@[opcodes]
inductive GMIR where
| g_add
| g_sub
| g_mul
| g_and
| g_or
| g_xor
| g_sdiv
| g_udiv
| g_srem
| g_urem
| g_shl
| g_lshr
| g_ashr
| g_icmp
| g_select
| g_anyext
| g_sext
| g_zext
| g_trunc
| g_sext_inreg
| g_constant
| g_inttoptr
| g_ptrtoint
| g_bswap
| g_bitreverse
| g_brev8
| g_saddsat
| g_uaddsat
| g_ssubsat
| g_usubsat
| g_sshlsat
| g_ushlsat
| g_smin
| g_smax
| g_umin
| g_umax
| g_abs
| g_ctlz
| g_cttz
| g_ctlz_zero_poison
| g_cttz_zero_poison
| g_ctpop
| g_load
| g_store
| g_merge_values
| g_unmerge_values
| g_br
| g_brcond
| g_uaddo
| g_uadde
| g_usubo
| g_usube
| g_saddo
| g_ssubo
| g_fshl
| g_fshr
| g_rotl
| g_rotr
deriving Inhabited, Repr, Hashable, DecidableEq

@[expose, properties_of]
def GMIR.propertiesOf : GMIR → Type
  | .g_add | .g_sub | .g_mul | .g_shl | .g_trunc => NswNuwProperties
  | .g_sdiv | .g_udiv | .g_lshr | .g_ashr => ExactProperties
  | .g_or => DisjointProperties
  | .g_icmp => IcmpProperties
  | .g_zext => NnegProperties
  | .g_sext_inreg => SextInRegProperties
  | .g_constant => GMIRConstantProperties
  | .g_load | .g_store => MachineMemOperand
  | .g_brcond => GMIRBrCondProperties
  | .g_select | .g_anyext | .g_sext
  | .g_and | .g_xor | .g_srem | .g_urem
  | .g_inttoptr | .g_ptrtoint | .g_bswap | .g_bitreverse | .g_brev8
  | .g_saddsat | .g_uaddsat | .g_ssubsat | .g_usubsat | .g_sshlsat | .g_ushlsat
  | .g_smin | .g_smax | .g_umin | .g_umax | .g_abs
  | .g_merge_values | .g_unmerge_values | .g_br
  | .g_uaddo | .g_uadde | .g_usubo | .g_usube
  | .g_saddo | .g_ssubo
  | .g_ctlz | .g_cttz | .g_ctlz_zero_poison | .g_cttz_zero_poison | .g_ctpop
  | .g_fshl | .g_fshr | .g_rotl | .g_rotr => Unit

def GMIR.fromAttrDict
    (op : GMIR) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (GMIR.propertiesOf op) := by
  cases op
  case g_add | g_sub | g_mul | g_shl | g_trunc => exact NswNuwProperties.fromAttrDict attrDict
  case g_sdiv | g_udiv | g_lshr | g_ashr => exact ExactProperties.fromAttrDict attrDict
  case g_or => exact DisjointProperties.fromAttrDict attrDict
  case g_icmp => exact IcmpProperties.fromAttrDictFor "gmir.g_icmp" attrDict
  case g_zext => exact NnegProperties.fromAttrDict attrDict
  case g_sext_inreg => exact SextInRegProperties.fromAttrDict attrDict
  case g_constant => exact GMIRConstantProperties.fromAttrDict attrDict
  case g_load => exact MachineMemOperand.fromAttrDict "gmir.g_load" attrDict
  case g_store => exact MachineMemOperand.fromAttrDict "gmir.g_store" attrDict
  case g_brcond => exact GMIRBrCondProperties.fromAttrDict attrDict
  case g_select | g_anyext | g_sext
     | g_and | g_xor | g_srem | g_urem
     | g_inttoptr | g_ptrtoint | g_bswap | g_bitreverse | g_brev8
     | g_saddsat | g_uaddsat | g_ssubsat | g_usubsat | g_sshlsat | g_ushlsat
     | g_smin | g_smax | g_umin | g_umax | g_abs
     | g_merge_values | g_unmerge_values | g_br
     | g_uaddo | g_uadde | g_usubo | g_usube
     | g_saddo | g_ssubo
     | g_ctlz | g_cttz | g_ctlz_zero_poison | g_cttz_zero_poison | g_ctpop
     | g_fshl | g_fshr | g_rotl | g_rotr => exact .ok ()

def GMIR.toAttrDict
    (op : GMIR) (props : GMIR.propertiesOf op) :
    Std.HashMap ByteArray Attribute :=
  match op with
  | .g_add | .g_sub | .g_mul | .g_shl | .g_trunc => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    let val := (if props.nsw then 1 else 0) + (if props.nuw then 2 else 0)
    if val > 0 then
      dict := dict.insert "overflowFlags".toUTF8
        (.integerAttr (IntegerAttr.mk (Int.ofNat val) (IntegerType.signless 32)))
    dict
  | .g_icmp =>
    let value := IntegerAttr.mk (Int.ofNat props.predicate.toNat) (IntegerType.signless 64)
    (Std.HashMap.emptyWithCapacity 1).insert
      "predicate".toUTF8 (Attribute.integerAttr value)
  | .g_sdiv | .g_udiv | .g_lshr | .g_ashr => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    if props.exact then
      dict := dict.insert "isExact".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .g_or => Id.run do
    let mut dict := Std.HashMap.emptyWithCapacity 1
    if props.disjoint then
      dict := dict.insert "isDisjoint".toUTF8 (Attribute.unitAttr UnitAttr.mk)
    dict
  | .g_zext => props.toAttrDict
  | .g_sext_inreg => (Std.HashMap.emptyWithCapacity 1).insert "sz".toUTF8 (i64Attr props.sz)
  | .g_constant => (Std.HashMap.emptyWithCapacity 1).insert "value".toUTF8 (.integerAttr props.value)
  | .g_load | .g_store => props.toAttrDict
  | .g_brcond => (Std.HashMap.emptyWithCapacity 1).insert
      "operandSegmentSizes".toUTF8 (.denseArrayAttr props.operandSegmentSizes)
  | .g_select | .g_anyext | .g_sext
  | .g_and | .g_xor | .g_srem | .g_urem
  | .g_inttoptr | .g_ptrtoint | .g_bswap | .g_bitreverse | .g_brev8
  | .g_saddsat | .g_uaddsat | .g_ssubsat | .g_usubsat | .g_sshlsat | .g_ushlsat
  | .g_smin | .g_smax | .g_umin | .g_umax | .g_abs
  | .g_ctlz | .g_cttz | .g_ctpop
  | .g_merge_values | .g_unmerge_values | .g_br
  | .g_uaddo | .g_uadde | .g_usubo | .g_usube
  | .g_saddo | .g_ssubo
  | .g_ctlz_zero_poison | .g_cttz_zero_poison
  | .g_fshl | .g_fshr | .g_rotl | .g_rotr => {}

#generate_dialect GMIR

instance : IsOpCode GMIR where
  fromName := GMIR.fromName
  name := GMIR.name
  propertiesOf := GMIR.propertiesOf
  fromAttrDict := GMIR.fromAttrDict
  toAttrDict := GMIR.toAttrDict

/--
This replicates the type-group information in LLVM's `GenericOpcodes.td`
(llvm/include/llvm/Target/GenericOpcodes.td).

Immediate operands and operands with LLVM's `unknown` (special) type are omitted and represented
as operation properties instead.

Operands/results of the same type group must have the same concrete type.
Different type groups are unconstrained relative to each other, so they may share a type.
The meaning of a type group is local to a single operation
-/
inductive TypeGroup where
| type (group_id : Nat)
deriving Inhabited, Repr, BEq, DecidableEq, Hashable

structure GenericOpInfo where
  outOperandList : Array TypeGroup
  inOperandList : Array TypeGroup
deriving Inhabited, Repr

def GMIR.genericOpInfo : GMIR → GenericOpInfo
  | .g_add | .g_sub | .g_mul | .g_and | .g_or | .g_xor
  | .g_sdiv | .g_udiv | .g_srem | .g_urem
  | .g_saddsat | .g_uaddsat | .g_ssubsat | .g_usubsat
  | .g_smin | .g_smax | .g_umin | .g_umax =>
    { outOperandList := #[.type 0]
      inOperandList := #[.type 0, .type 0] }
  | .g_shl | .g_lshr | .g_ashr | .g_sshlsat | .g_ushlsat | .g_rotl | .g_rotr =>
    { outOperandList := #[.type 0]
      inOperandList := #[.type 0, .type 1] }
  | .g_fshl | .g_fshr =>
    { outOperandList := #[.type 0]
      inOperandList := #[.type 0, .type 0, .type 1] }
  | .g_icmp =>
    { outOperandList := #[.type 0]
      inOperandList := #[.type 1, .type 1] }
  | .g_select =>
    { outOperandList := #[.type 0]
      inOperandList := #[.type 1, .type 0, .type 0] }
  | .g_anyext | .g_sext | .g_zext | .g_trunc
  | .g_inttoptr | .g_ptrtoint | .g_ctlz | .g_cttz | .g_ctlz_zero_poison | .g_cttz_zero_poison
  | .g_ctpop =>
    { outOperandList := #[.type 0]
      inOperandList := #[.type 1] }
  | .g_bswap | .g_bitreverse | .g_brev8 | .g_abs | .g_sext_inreg =>
    { outOperandList := #[.type 0]
      inOperandList := #[.type 0] }
  | .g_constant =>
    { outOperandList := #[.type 0]
      inOperandList := #[] }
  | .g_load =>
    { outOperandList := #[.type 0]
      inOperandList := #[.type 1] }
  | .g_store =>
    { outOperandList := #[]
      inOperandList := #[.type 0, .type 1] }
  -- Unlike in LLVM, these are not variadic: they only split a value into two halves.
  -- TODO: Support variadic ops in `GMIR.genericOpInfo`.
  | .g_merge_values =>
    { outOperandList := #[.type 0]
      inOperandList := #[.type 1, .type 1] }
  | .g_unmerge_values =>
    { outOperandList := #[.type 0, .type 0]
      inOperandList := #[.type 1] }
  | .g_br =>
    { outOperandList := #[]
      inOperandList := #[] }
  | .g_brcond =>
    { outOperandList := #[]
      inOperandList := #[.type 0] }
  | .g_uaddo | .g_usubo | .g_saddo | .g_ssubo =>
    { outOperandList := #[.type 0, .type 1]
      inOperandList := #[.type 0, .type 0] }
  | .g_uadde | .g_usube =>
    { outOperandList := #[.type 0, .type 1]
      inOperandList := #[.type 0, .type 0, .type 1] }

/-- The number of distinct type groups of `opCode`. -/
def GMIR.numTypeGroups (opCode : GMIR) : Nat :=
  let info := opCode.genericOpInfo
  (info.outOperandList ++ info.inOperandList).toList.eraseDups.length

/-- Each result and operand type of `op`, paired with its type group in `opCode`. -/
def GMIR.getTypedGroups! {OpInfo : Type} [IsOpCode OpInfo] (opCode : GMIR) (op : OperationPtr)
    (ctx : IRContext OpInfo) : Array (TypeGroup × TypeAttr) :=
  let info := opCode.genericOpInfo
  info.outOperandList.zip (op.getResultTypes! ctx) ++
    info.inOperandList.zip (op.getOperandTypes! ctx)

private def OperationPtr.verifyGMIRICmp {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  -- `gmir.icmp` also compares pointers.
  for i in [0, 1]  do
    ((op.getOperand! ctx.raw i).getType! ctx.raw).verifyIntegerOrPointerType
      s!"{instrName}: Expected operand {i} to have integer or pointer type"
  let resultType := (op.getResult 0).getType! ctx.raw
  resultType.verifyIntegerType s!"{instrName}: Expected result to have integer type"

/--
Converts a shift amount (type group 1) to the width `w` of the shifted value (type group 0).
An amount that does not fit in `w` bits is out of range, so it is replaced by the all-ones value,
which is also out of range and hence yields the same (poison) result.
-/
private def shiftAmount {w' : Nat} (w : Nat) : Data.LLVM.Int w' → Data.LLVM.Int w
  | .val v => .val (if v.toNat < w then BitVec.ofNat w v.toNat else BitVec.allOnes w)
  | .poison => .poison

/--
Zero-extends or truncates `x` to width `w`, as LLVM's `zextOrTrunc`. This converts the bit counts of
`g_ctlz`/`g_cttz`/`g_ctpop` and the carries of `g_uaddo`/`g_uadde`/`g_usubo`/`g_usube`.
-/
private def zextOrTrunc {w' : Nat} (w : Nat) : Data.LLVM.Int w' → Data.LLVM.Int w
  | .val v => .val (BitVec.ofNat w v.toNat)
  | .poison => .poison

/--
The `2 * w`-bit value whose low half is `lo` and whose high half is `hi`, as produced by gMIR's
`g_merge_values`. If either half is poison, the result is poison.
-/
-- TODO: A poison half should not make the other half poison, so that a half padded with
-- `g_implicit_def` (as LLVM does when narrowing `g_anyext`) keeps the defined half.
private def mergeValues {w : Nat} (lo hi : Data.LLVM.Int w) : Data.LLVM.Int (w + w) :=
  match lo, hi with
  | .val lo, .val hi => .val (hi ++ lo)
  | _, _ => .poison

/--
The low and the high half of the `2 * w`-bit `x`, as produced by gMIR's `g_unmerge_values`.
If `x` is poison, both halves are poison.
-/
private def unmergeValues {w : Nat} (x : Data.LLVM.Int (w + w)) :
    Data.LLVM.Int w × Data.LLVM.Int w :=
  match x with
  | .val x => (.val (x.truncate w), .val (x.extractLsb' w w))
  | .poison => (.poison, .poison)

/--
The sum of `x`, `y` and the carry `c`, and the carry out, as produced by gMIR's `g_uadde`. The sum
is taken modulo `2^w`, and the carry out is `1` if it does not fit in `w` bits. If any operand is
poison, both results are poison.
-/
private def uaddWithCarry {w : Nat} (x y : Data.LLVM.Int w) (c : Data.LLVM.Int 1) :
    Data.LLVM.Int w × Data.LLVM.Int 1 :=
  match x, y, c with
  | .val x, .val y, .val c =>
    let sum := x + y + c.zeroExtend w
    -- `BitVec.carry w` is the carry out of a `w`-bit add, i.e. whether `x + y + c ≥ 2^w`.
    (.val sum, .val (BitVec.ofBool (BitVec.carry w x y (c.getLsbD 0))))
  | _, _, _ => (.poison, .poison)

/--
The difference of `x`, `y` and the borrow `b`, and the borrow out, as produced by gMIR's `g_usube`.
The difference is taken modulo `2^w`, and the borrow out is `1` if `x < y + b` as unsigned integers.
If any operand is poison, both results are poison.
-/
private def usubWithBorrow {w : Nat} (x y : Data.LLVM.Int w) (b : Data.LLVM.Int 1) :
    Data.LLVM.Int w × Data.LLVM.Int 1 :=
  match x, y, b with
  | .val x, .val y, .val b =>
    -- `y + b` is at most `2^w`, so it fits in `w + 1` bits.
    let borrow := (x.zeroExtend (w + 1)).ult (y.zeroExtend (w + 1) + b.zeroExtend (w + 1))
    (.val (x - y - b.zeroExtend w), .val (BitVec.ofBool borrow))
  | _, _, _ => (.poison, .poison)

/--
Reverses the bits within each byte of `x`, as RISC-V's `brev8` (LLVM's `RISCV::G_BREV8`).
Reversing all bits also reverses the byte order, which `bswap` undoes. The verifier only accepts
widths of 8, 16, 32 and 64 bits.
-/
def brev8 {w : Nat} (x : Data.LLVM.Int w) : Data.LLVM.Int w :=
  if w = 8 then Data.LLVM.Int.bitreverse x else Data.LLVM.Int.bitreverse (Data.LLVM.Int.bswap x)

def GMIR.interpretOp' (opType : Veir.GMIR) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) :=
  match opType with
  | .g_anyext => do
    /- TODO: the semantics need to be updated once we support nondeterminism. -/
    let [.int w val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h : resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (val.zext resBw.bitwidth (_h := by omega))], mem, none)
  | .g_add => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.add lhs rhs properties.nsw properties.nuw)], mem, none)
  | .g_icmp => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simpa using h)
    let cmp := Data.LLVM.Int.icmp lhs rhs properties.predicate
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    /- LLVM leaves the value of true in a wider result to the target; it is 1, as on RISC-V. -/
    if h : 1 < resBw.bitwidth then return (#[.int resBw.bitwidth (cmp.zext _ false h)], mem, none)
    return (#[.int 1 cmp], mem, none)
  | .g_select => do
    let [.int _ cond, .int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (GMIR.selectNonzero cond lhs rhs)], mem, none)
  | .g_sub => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.sub lhs rhs properties.nsw properties.nuw)], mem, none)
  | .g_zext => do
    let [.int w val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h : resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (Data.LLVM.Int.zext val resBw.bitwidth properties.nneg (by omega))], mem, none)
  | .g_sext => do
    let [.int w val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h : resBw.bitwidth <= w then none else
    return (#[.int resBw.bitwidth (Data.LLVM.Int.sext val resBw.bitwidth (by omega))], mem, none)
  | .g_trunc => do
    let [.int w val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h : resBw.bitwidth >= w then none else
    return (#[.int resBw.bitwidth (Data.LLVM.Int.trunc val resBw.bitwidth properties.nsw properties.nuw (by omega))], mem, none)
  | .g_sext_inreg => do
    let [.int w val] := operands.toList | none
    let sz := properties.sz.toNat
    if h : w ≤ sz then none else
    let low := Data.LLVM.Int.trunc val sz false false (by omega)
    return (#[.int w (Data.LLVM.Int.sext low w (by omega))], mem, none)
  | .g_constant => do
    let some resType := resultTypes[0]? | none
    let .integerType bw := resType.val | none
    return (#[.int bw.bitwidth (.val (BitVec.ofInt bw.bitwidth properties.value.value))], mem, none)
  | .g_mul => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.mul lhs rhs properties.nsw properties.nuw)], mem, none)
  | .g_and => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.and lhs rhs)], mem, none)
  | .g_or => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.or lhs rhs properties.disjoint)], mem, none)
  | .g_xor => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.xor lhs rhs)], mem, none)
  | .g_sdiv => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    if Data.LLVM.Int.isSignedDivisionUB lhs rhs then Interp.ub none
    return (#[.int bw (Data.LLVM.Int.sdiv lhs rhs properties.exact)], mem, none)
  | .g_udiv => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    if Data.LLVM.Int.isUnsignedDivisionUB rhs then Interp.ub none
    return (#[.int bw (Data.LLVM.Int.udiv lhs rhs properties.exact)], mem, none)
  | .g_srem => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    if Data.LLVM.Int.isSignedDivisionUB lhs rhs then Interp.ub none
    return (#[.int bw (Data.LLVM.Int.srem lhs rhs)], mem, none)
  | .g_urem => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    if Data.LLVM.Int.isUnsignedDivisionUB rhs then Interp.ub none
    return (#[.int bw (Data.LLVM.Int.urem lhs rhs)], mem, none)
  | .g_shl => do
    let [.int bw lhs, .int _ rhs] := operands.toList | none
    let rhs := shiftAmount bw rhs
    return (#[.int bw (Data.LLVM.Int.shl lhs rhs properties.nsw properties.nuw)], mem, none)
  | .g_lshr => do
    let [.int bw lhs, .int _ rhs] := operands.toList | none
    let rhs := shiftAmount bw rhs
    return (#[.int bw (Data.LLVM.Int.lshr lhs rhs properties.exact)], mem, none)
  | .g_ashr => do
    let [.int bw lhs, .int _ rhs] := operands.toList | none
    let rhs := shiftAmount bw rhs
    return (#[.int bw (Data.LLVM.Int.ashr lhs rhs properties.exact)], mem, none)
  | .g_sshlsat => do
    let [.int bw lhs, .int _ rhs] := operands.toList | none
    let rhs := shiftAmount bw rhs
    return (#[.int bw (Data.LLVM.Int.sshlSat lhs rhs)], mem, none)
  | .g_ushlsat => do
    let [.int bw lhs, .int _ rhs] := operands.toList | none
    let rhs := shiftAmount bw rhs
    return (#[.int bw (Data.LLVM.Int.ushlSat lhs rhs)], mem, none)
  | .g_saddsat => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.saddSat lhs rhs)], mem, none)
  | .g_uaddsat => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.uaddSat lhs rhs)], mem, none)
  | .g_ssubsat => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.ssubSat lhs rhs)], mem, none)
  | .g_usubsat => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.usubSat lhs rhs)], mem, none)
  | .g_smin => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.smin lhs rhs)], mem, none)
  | .g_smax => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.smax lhs rhs)], mem, none)
  | .g_umin => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.umin lhs rhs)], mem, none)
  | .g_umax => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.umax lhs rhs)], mem, none)
  | .g_abs => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (Data.LLVM.Int.abs x false)], mem, none)
  | .g_bswap => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (Data.LLVM.Int.bswap x)], mem, none)
  | .g_bitreverse => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (Data.LLVM.Int.bitreverse x)], mem, none)
  | .g_brev8 => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (brev8 x)], mem, none)
  | .g_ctlz => do
    let [.int _ x] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    return (#[.int resBw.bitwidth (zextOrTrunc resBw.bitwidth (Data.LLVM.Int.ctlz x false))], mem, none)
  | .g_cttz => do
    let [.int _ x] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    return (#[.int resBw.bitwidth (zextOrTrunc resBw.bitwidth (Data.LLVM.Int.cttz x false))], mem, none)
  | .g_ctlz_zero_poison => do
    let [.int _ x] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    return (#[.int resBw.bitwidth (zextOrTrunc resBw.bitwidth (Data.LLVM.Int.ctlz x true))], mem, none)
  | .g_cttz_zero_poison => do
    let [.int _ x] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    return (#[.int resBw.bitwidth (zextOrTrunc resBw.bitwidth (Data.LLVM.Int.cttz x true))], mem, none)
  | .g_ctpop => do
    let [.int _ x] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    return (#[.int resBw.bitwidth (zextOrTrunc resBw.bitwidth (Data.LLVM.Int.ctpop x))], mem, none)
  | .g_inttoptr => do
    let [.int bw val] := operands.toList | none
    if h : bw = 64 then return (#[.addr (mem.ptrFromInt (val.cast h))], mem, none) else .fail none
  | .g_ptrtoint => do
    let [.addr val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if resBw.bitwidth = 64 then return (#[.int 64 val.toInt], mem, none) else .fail none
  | .g_load => do
    let [.addr addr] := operands.toList | none
    let [type] := resultTypes.toList | none
    let .val addr := addr | Interp.ub none
    addr.checkAlignment properties.alignment.toNat
    let .integerType ⟨w, _⟩ := type.val
      | return (#[← mem.llvmLoad addr type], mem, none)
    let size := properties.size.toNat
    -- gMIR has no byte type, so a byte load is converted to an integer load of the same size.
    let val ← mem.frozenLoad addr size
    /- TODO: The high bits of a wider result are undefined and should have the same semantic
       like `g_anyext`. Support nondeterminisim once CTrees have landed. -/
    if h : size < w then return (#[.int w (val.zext w (_h := h))], mem, none)
    if h : size = w then return (#[.int w (val.cast h)], mem, none)
    none
  | .g_store => do
    let [val, .addr addr] := operands.toList | none
    let .val addr := addr | Interp.ub none
    addr.checkAlignment properties.alignment.toNat
    -- A wider value is truncated to the stored size.
    let size := properties.size.toNat
    let val ← match val with
      | .int w v =>
        if h : size < w then pure (.int size (v.trunc size (_h := h)))
        else if size = w then pure val else none
      | _ => pure val
    return (#[], ← mem.llvmStore addr val, none)
  | .g_merge_values => do
    let [.int w lo, .int w' hi] := operands.toList | none
    if h : w' ≠ w then none else
    let hi := hi.cast (by simp at h; exact h)
    return (#[.int (w + w) (mergeValues lo hi)], mem, none)
  | .g_unmerge_values => do
    let [.int w x] := operands.toList | none
    let half := w / 2
    if h : w ≠ half + half then none else
    let (lo, hi) := unmergeValues (w := half) (x.cast (by simp at h; exact h))
    return (#[.int half lo, .int half hi], mem, none)
  | .g_br => do
    let [dest] := blockOperands.toList | none
    return (#[], mem, some (.branch operands dest))
  | .g_brcond => do
    let [destTrue, destFalse] := blockOperands.toList | none
    let some (trueSizeInt : Int) := properties.operandSegmentSizes.values[1]? | none
    let trueSize := trueSizeInt.toNat
    /- As for `llvm.cond_br`, but the condition may be wider than `i1`, as legalization widens it
       with a `g_zext`. Any nonzero value takes the first successor. -/
    match operands[0]? with
    | some (RuntimeValue.int _ (.val cond)) =>
      if cond ≠ 0 then
        return (#[], mem, some (.branch (operands.extract 1 (trueSize + 1)) destTrue))
      else
        return (#[], mem, some (.branch (operands.extract (trueSize + 1) operands.size) destFalse))
    | some (RuntimeValue.int _ .poison) => Interp.ub none
    | _ => none
  -- TODO: As for `g_icmp`, a wider carry is assumed to be `0` or `1`, i.e. the target's booleans are
  -- `ZeroOrOneBooleanContent`, as on RISC-V. LLVM leaves the high bits of a wider carry to the target.
  | .g_uaddo => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    let some carryType := resultTypes[1]? | none
    let .integerType carryBw := carryType.val | none
    return (#[.int bw (Data.LLVM.Int.add lhs rhs),
      .int carryBw.bitwidth (zextOrTrunc _ (Data.LLVM.Int.uaddOverflowFlag lhs rhs))], mem, none)
  | .g_uadde => do
    let [.int bw lhs, .int bw' rhs, .int carryBw carry] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    let (sum, carry) := uaddWithCarry lhs rhs (zextOrTrunc 1 carry)
    return (#[.int bw sum, .int carryBw (zextOrTrunc _ carry)], mem, none)
  | .g_usubo => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    let some borrowType := resultTypes[1]? | none
    let .integerType borrowBw := borrowType.val | none
    return (#[.int bw (Data.LLVM.Int.sub lhs rhs),
      .int borrowBw.bitwidth (zextOrTrunc _ (Data.LLVM.Int.usubOverflowFlag lhs rhs))], mem, none)
  | .g_usube => do
    let [.int bw lhs, .int bw' rhs, .int borrowBw borrow] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    let (diff, borrow) := usubWithBorrow lhs rhs (zextOrTrunc 1 borrow)
    return (#[.int bw diff, .int borrowBw (zextOrTrunc _ borrow)], mem, none)
  | .g_saddo => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    let some overflowType := resultTypes[1]? | none
    let .integerType overflowBw := overflowType.val | none
    return (#[.int bw (Data.LLVM.Int.add lhs rhs),
      .int overflowBw.bitwidth (zextOrTrunc _ (Data.LLVM.Int.saddOverflowFlag lhs rhs))], mem, none)
  | .g_ssubo => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | none
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    let some overflowType := resultTypes[1]? | none
    let .integerType overflowBw := overflowType.val | none
    return (#[.int bw (Data.LLVM.Int.sub lhs rhs),
      .int overflowBw.bitwidth (zextOrTrunc _ (Data.LLVM.Int.ssubOverflowFlag lhs rhs))], mem, none)
  | .g_fshl => do
    let [.int bw x, .int bw' y, .int _ z] := operands.toList | none
    if h : bw' ≠ bw then none else
    let y := y.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.fshl x y (GMIR.funnelShiftAmount bw z))], mem, none)
  | .g_fshr => do
    let [.int bw x, .int bw' y, .int _ z] := operands.toList | none
    if h : bw' ≠ bw then none else
    let y := y.cast (by simp at h; exact h)
    return (#[.int bw (Data.LLVM.Int.fshr x y (GMIR.funnelShiftAmount bw z))], mem, none)
  | .g_rotl => do
    let [.int bw x, .int _ z] := operands.toList | none
    return (#[.int bw (GMIR.rotl x z)], mem, none)
  | .g_rotr => do
    let [.int bw x, .int _ z] := operands.toList | none
    return (#[.int bw (GMIR.rotr x z)], mem, none)

private def OperationPtr.verifyGMIRIntegerTypes {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  for i in [0:op.getNumOperands ctx.raw opIn] do
    ((op.getOperand! ctx.raw i).getType! ctx.raw).verifyIntegerType
      s!"{instrName}: Expected operand {i} to have integer type"
  for i in [0:op.getNumResults ctx.raw opIn] do
    ((op.getResult i).getType! ctx.raw).verifyIntegerType
      s!"{instrName}: Expected result {i} to have integer type"

/-- Verifies that `sz` is at least 1 and smaller than the bitwidth of the operand. -/
private def OperationPtr.verifyGMIRSextInReg {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo GMIR] (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let .integerType ⟨width, _⟩ := ((op.getOperand! ctx.raw 0).getType! ctx.raw).val
    | throw s!"{instrName}: Expected operand 0 to have integer type"
  let sz := (op.getProperties! ctx.raw GMIR.g_sext_inreg).sz.toInt
  if sz < 1 then
    throw s!"{instrName}: Expected 'sz' to be at least 1, but got {sz}"
  if width ≤ sz then
    throw s!"{instrName}: Expected 'sz' to be smaller than the operand width {width}, but got {sz}"

/--
Verifies that the memory operand of a `g_load` or `g_store` of a value of type `type` has a
power-of-two alignment, and a `size` that is a positive multiple of 8 and at most the width of the
value, or equal to it for a pointer.
-/
private def MachineMemOperand.verify (mmo : MachineMemOperand) (type : TypeAttr)
    (instrName : String) : Except String PUnit := do
  let alignment := mmo.alignment.toNat
  if alignment = 0 ∨ alignment &&& (alignment - 1) ≠ 0 then
    throw s!"{instrName}: Expected 'alignment' to be a power of two, but got {alignment}"
  let some width := Attribute.bitwidthOfType type.val | pure ()
  let size := mmo.size.toNat
  if size = 0 ∨ size % 8 ≠ 0 then
    throw s!"{instrName}: Expected 'size' to be a positive multiple of 8, but got {size}"
  if width < size then
    throw s!"{instrName}: Expected 'size' to be at most the value width {width}, but got {size}"
  if type.val matches .llvmPointerType _ then
    if size ≠ width then
      throw s!"{instrName}: Expected 'size' to be the pointer width {width}, but got {size}"

/--
Verifies that the operands and the results of `op` have the same total width.
This is used to verify `g_merge_values` and `g_unmerge_values`.
-/
private def OperationPtr.verifyGMIRTotalWidth {OpInfo : Type} [IsOpCode OpInfo]
    (op : OperationPtr) (ctx : WfIRContext OpInfo)
    (opIn : op.InBounds ctx.raw) : Except String PUnit := do
  let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
  let totalWidth (types : Array TypeAttr) :=
    types.foldl (fun width type => width + (Attribute.bitwidthOfType type.val).getD 0) 0
  let operandWidth := totalWidth (op.getOperandTypes! ctx.raw)
  let resultWidth := totalWidth (op.getResultTypes! ctx.raw)
  if resultWidth ≠ operandWidth then
    throw s!"{instrName}: Expected the results to be {operandWidth} bits wide in total, but got \
      {resultWidth}"

/--
Verify the local invariants of a `gmir` operation in any operation-info type
containing the `gmir` dialect.
-/
def GMIR.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo GMIR] (opCode : GMIR) (opPtr : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : opPtr.InBounds ctx.raw) :
    Except String PUnit := do
  let info := opCode.genericOpInfo
  -- Verify operand and result counts. Branches forward a variable number of operands, which their
  -- own checks below verify.
  if !(opCode matches .g_br | .g_brcond) then
    opPtr.verifyPlainOpCounts ctx opIn info.inOperandList.size info.outOperandList.size
  -- Verify that every member of a type group has the same concrete type.
  let typedGroups := opCode.getTypedGroups! opPtr ctx.raw
  let canon : Std.HashMap TypeGroup TypeAttr :=
    typedGroups.foldl (init := {}) fun canon (slot, ty) => canon.insertIfNew slot ty
  for (group, type) in typedGroups do
    let expected := canon[group]!
    if expected != type then
      let instrName := String.fromUTF8! (IsOpCode.name (opPtr.getOpType ctx.raw opIn))
      throw s!"{instrName}: type mismatch: expected {expected}, got {type}"
  -- Verify opcode-specific type invariants
  match opCode with
  | .g_icmp =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyGMIRICmp ctx opIn
  | .g_anyext | .g_sext | .g_zext =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyIntegerExtTypes ctx opIn
  | .g_trunc =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyTruncTypes ctx opIn (allowByte := false)
  | .g_add | .g_sub | .g_mul | .g_and | .g_or | .g_xor | .g_sdiv | .g_udiv | .g_srem | .g_urem
  | .g_shl | .g_lshr | .g_ashr
  | .g_saddsat | .g_uaddsat | .g_ssubsat | .g_usubsat | .g_sshlsat | .g_ushlsat
  | .g_smin | .g_smax | .g_umin | .g_umax | .g_abs | .g_bitreverse
  -- TODO: Also accept a `g_select` of pointers, as LLVM does.
  | .g_select | .g_ctlz | .g_cttz | .g_ctlz_zero_poison | .g_cttz_zero_poison | .g_ctpop
  | .g_fshl | .g_fshr | .g_rotl | .g_rotr =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyGMIRIntegerTypes ctx opIn
  | .g_bswap =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyGMIRIntegerTypes ctx opIn
    let .integerType intType := ((opPtr.getResult 0).getType! ctx.raw).val
      | throw "gmir.g_bswap: Expected result to have integer type"
    if intType.bitwidth ∉ [16, 32, 64] then
      throw "gmir.g_bswap: bitwidth must be 16, 32, or 64"
  | .g_brev8 =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyGMIRIntegerTypes ctx opIn
    let .integerType intType := ((opPtr.getResult 0).getType! ctx.raw).val
      | throw "gmir.g_brev8: Expected result to have integer type"
    if intType.bitwidth ∉ [8, 16, 32, 64] then
      throw "gmir.g_brev8: bitwidth must be 8, 16, 32, or 64"
  | .g_inttoptr =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    ((opPtr.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerType
      "gmir.g_inttoptr: Expected operand 0 to have integer type"
    ((opPtr.getResult 0).getType! ctx.raw).verifyLlvmPointerType
      "gmir.g_inttoptr: Expected result to have !llvm.ptr type"
  | .g_ptrtoint =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    ((opPtr.getOperand! ctx.raw 0).getType! ctx.raw).verifyLlvmPointerType
      "gmir.g_ptrtoint: Expected operand 0 to have !llvm.ptr type"
    ((opPtr.getResult 0).getType! ctx.raw).verifyIntegerType
      "gmir.g_ptrtoint: Expected result to have integer type"
  | .g_sext_inreg =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyGMIRIntegerTypes ctx opIn
    opPtr.verifyGMIRSextInReg ctx opIn
  | .g_constant =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyGMIRIntegerTypes ctx opIn
    let props := opPtr.getProperties! ctx.raw GMIR.g_constant
    if props.value.type ≠ ((opPtr.getResult 0).getType! ctx.raw).val then
      throw "gmir.g_constant: Expected result type to be equal to the constant's type"
    opPtr.verifyNormalizedIntegerAttr ctx opIn props.value
  | .g_load =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    let resultType := (opPtr.getResult 0).getType! ctx.raw
    ((opPtr.getOperand! ctx.raw 0).getType! ctx.raw).verifyLlvmPointerType
      "gmir.g_load: Expected operand 0 to have !llvm.ptr type"
    resultType.verifyIntegerOrPointerType
      "gmir.g_load: Expected result to have integer or !llvm.ptr type"
    (opPtr.getProperties! ctx.raw GMIR.g_load).verify resultType "gmir.g_load"
  | .g_store =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    let valueType := (opPtr.getOperand! ctx.raw 0).getType! ctx.raw
    valueType.verifyIntegerOrPointerType
      "gmir.g_store: Expected operand 0 to have integer or !llvm.ptr type"
    ((opPtr.getOperand! ctx.raw 1).getType! ctx.raw).verifyLlvmPointerType
      "gmir.g_store: Expected operand 1 to have !llvm.ptr type"
    (opPtr.getProperties! ctx.raw GMIR.g_store).verify valueType "gmir.g_store"
  | .g_merge_values | .g_unmerge_values =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyGMIRIntegerTypes ctx opIn
    opPtr.verifyGMIRTotalWidth ctx opIn
  | .g_br =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyUnconditionalBranch ctx opIn
  | .g_brcond =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyTerminatorCounts ctx opIn 2
    if opPtr.getNumOperands ctx.raw opIn = 0 then
      throw "gmir.g_brcond: Expected a condition operand"
    ((opPtr.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerType
      "gmir.g_brcond: Expected the condition to have integer type"
    let sizes := (opPtr.getProperties! ctx.raw GMIR.g_brcond).operandSegmentSizes
    opPtr.verifyCondBranchOperandSegmentSizes ctx opIn sizes 1
  | .g_uaddo | .g_uadde | .g_usubo | .g_usube | .g_saddo | .g_ssubo =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyGMIRIntegerTypes ctx opIn

def GMIR.propagatesPoison : GMIR → Bool
  | .g_add | .g_sub | .g_icmp | .g_anyext | .g_sext | .g_zext | .g_trunc
  | .g_mul | .g_and | .g_or | .g_xor | .g_sdiv | .g_udiv | .g_srem | .g_urem
  | .g_shl | .g_lshr | .g_ashr
  | .g_inttoptr | .g_ptrtoint | .g_bswap | .g_bitreverse | .g_brev8
  | .g_saddsat | .g_uaddsat | .g_ssubsat | .g_usubsat | .g_sshlsat | .g_ushlsat
  | .g_smin | .g_smax | .g_umin | .g_umax | .g_abs
  | .g_ctlz | .g_cttz | .g_ctlz_zero_poison | .g_cttz_zero_poison | .g_ctpop | .g_sext_inreg
  | .g_merge_values | .g_unmerge_values
  | .g_uaddo | .g_uadde | .g_usubo | .g_usube | .g_saddo | .g_ssubo
  | .g_fshl | .g_fshr | .g_rotl | .g_rotr => true
  -- Poison on the arm that `g_select` does not select does not reach its result.
  | .g_select | .g_constant | .g_load | .g_store | .g_br | .g_brcond => false

/--
`g_load` reads and `g_store` writes memory; a volatile access does both, as for `llvm.load` and
`llvm.store`. Other operations have no effects.
-/
def GMIR.getEffects (op : GMIR) (props : GMIR.propertiesOf op) : MemoryEffects :=
  match op, props with
  | .g_load, props => if props.volatile_ then .readWrite else .read
  | .g_store, props => if props.volatile_ then .readWrite else .write
  | _, _ => .none

def GMIR.isCommutative : GMIR → Bool
  | .g_add | .g_mul | .g_and | .g_or | .g_xor
  | .g_smin | .g_smax | .g_umin | .g_umax
  | .g_uaddsat | .g_saddsat | .g_uaddo | .g_saddo => true
  | _ => false

def GMIR.isConstantLike : GMIR → Bool
  | .g_constant => true
  | _ => false

/-- Materialize constants produced by folding GMIR operations. -/
def GMIR.materializeConstant {OpInfo : Type} [HasOpInfo OpInfo] [HasDialect OpInfo GMIR]
    (_op : GMIR) (value : RuntimeValue) (type : TypeAttr) : Option (Materialized OpInfo) :=
  match value, type.val with
  | .int _ (.val value), .integerType intType =>
    some (.of GMIR.g_constant (GMIRConstantProperties.mk (IntegerAttr.ofInt value.toInt intType)))
  | _, _ => none

def GMIR.hasSSADominance (_op : GMIR) (_index : Nat) : Bool :=
  true

def GMIR.isTerminator : GMIR → Bool
  | .g_br | .g_brcond => true
  | _ => false

def GMIR.unconditionalBranch? (op : GMIR) (_props : GMIR.propertiesOf op) :
    Option (OpKind GMIR) :=
  match op with
  | .g_br | .g_brcond => some ⟨.g_br, ()⟩
  | _ => none

def GMIR.branchOpInterface? (op : GMIR) : Option (BranchOpInterface (GMIR.propertiesOf op)) :=
  match op with
  | .g_br =>
    some {
      getSuccessorOperandsImpl? := fun _ operands successorIndex => do
        guard (successorIndex = 0)
        some { forwardedOperands := operands }
      getSuccessorIndexForOperandsImpl? := fun _ _ => some 0
    }
  | .g_brcond =>
    some {
      getSuccessorOperandsImpl? := fun props operands successorIndex =>
        BranchOpInterface.getSegmentedSuccessorOperands?
          1 props.operandSegmentSizes.values operands successorIndex
      getSuccessorIndexForOperandsImpl? := fun _ operands => do
        let some (.int _ (.val condition)) ← operands[0]? | none
        some (BranchOpInterface.getConditionalSuccessorIndex (condition ≠ 0))
    }
  | _ => none

instance : HasOpInfo GMIR where
  verifyLocalInvariants := GMIR.verifyLocalInvariants
  propagatesPoison := GMIR.propagatesPoison
  getEffects := GMIR.getEffects
  isConstantLike := GMIR.isConstantLike
  isCommutative := GMIR.isCommutative
  hasSSADominance := GMIR.hasSSADominance
  isTerminator := GMIR.isTerminator
  unconditionalBranch? := GMIR.unconditionalBranch?
  branchOpInterface? := GMIR.branchOpInterface?

end

end Veir
