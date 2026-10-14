module

public import Veir.IR.OpInfo
public import Veir.Verifier.Basic
public import Veir.Dialects.LLVM.Properties
public import Veir.Interpreter.RuntimeValue.Basic
public import Veir.Interpreter.Interp
public import Veir.Interpreter.Memory
public import Veir.Data.LLVM.Int.Basic
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
| g_rotr
| g_rotl
| g_icmp
| g_anyext
| g_sext
| g_zext
| g_trunc
| g_inttoptr
| g_ptrtoint
| g_ptr_add
| g_bitcast
| g_bswap
| g_bitreverse
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
| g_uaddo
| g_saddo
| g_usubo
| g_ssubo
| g_smulo
| g_umulo
| g_umulh
| g_smulh
| g_ctlz
| g_cttz
| g_ctpop
deriving Inhabited, Repr, Hashable, DecidableEq

/--
Properties of `g_ptr_add`. Each `G_PTR_ADD` that the IRTranslator builds for a GEP inherits the
GEP's `nuw`, `nusw` and `inbounds` flags (`MachineInstr::NoUWrap`, `NoUSWrap` and `InBounds`).

They are stored in the `noWrapFlags` attribute, with the same encoding as MLIR's `GEPNoWrapFlags`:
`inbounds_flag = 1`, `nusw = 2`, `nuw = 4`.
-/
structure PtrAddProperties where
  inbounds : Bool
  nusw : Bool
  nuw : Bool
deriving Inhabited, Repr, Hashable, DecidableEq

def PtrAddProperties.fromAttrDict (attrDict : Std.HashMap ByteArray Attribute) :
    Except String PtrAddProperties := do
  let value ← match attrDict["noWrapFlags".toUTF8]? with
    | some (.integerAttr flags) =>
      if flags.type.bitwidth ≠ 32 then
        .error s!"expected 'noWrapFlags' to be an integer attribute of bitwidth 32, but got i{flags.type.bitwidth}"
      else
        .ok flags.value
    | some attr => .error s!"expected 'noWrapFlags' to be an optional integer attribute, but got {attr}"
    | none => .ok 0
  return { inbounds := (value.toNat &&& 1) ≠ 0
           nusw := (value.toNat &&& 2) ≠ 0
           nuw := (value.toNat &&& 4) ≠ 0 }

def PtrAddProperties.toAttrDict (props : PtrAddProperties) : Std.HashMap ByteArray Attribute :=
  let val := (if props.inbounds then 1 else 0) + (if props.nusw then 2 else 0) +
    (if props.nuw then 4 else 0)
  if val > 0 then
    (Std.HashMap.emptyWithCapacity 1).insert "noWrapFlags".toUTF8
      (.integerAttr (IntegerAttr.mk (Int.ofNat val) (IntegerType.signless 32)))
  else
    Std.HashMap.emptyWithCapacity 0

@[expose, properties_of]
def GMIR.propertiesOf : GMIR → Type
  | .g_add | .g_sub | .g_mul | .g_shl | .g_trunc => NswNuwProperties
  | .g_sdiv | .g_udiv | .g_lshr | .g_ashr => ExactProperties
  | .g_or => DisjointProperties
  | .g_ptr_add => PtrAddProperties
  | .g_icmp => IcmpProperties
  | .g_zext => NnegProperties
  | .g_anyext | .g_sext
  | .g_and | .g_xor | .g_srem | .g_urem | .g_rotr | .g_rotl
  | .g_inttoptr | .g_ptrtoint | .g_bitcast | .g_bswap | .g_bitreverse
  | .g_saddsat | .g_uaddsat | .g_ssubsat | .g_usubsat | .g_sshlsat | .g_ushlsat
  | .g_smin | .g_smax | .g_umin | .g_umax | .g_abs
  | .g_uaddo | .g_saddo | .g_usubo | .g_ssubo | .g_smulo | .g_umulo
  | .g_umulh | .g_smulh | .g_ctlz | .g_cttz | .g_ctpop => Unit

def GMIR.fromAttrDict
    (op : GMIR) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (GMIR.propertiesOf op) := by
  cases op
  case g_add | g_sub | g_mul | g_shl | g_trunc => exact NswNuwProperties.fromAttrDict attrDict
  case g_sdiv | g_udiv | g_lshr | g_ashr => exact ExactProperties.fromAttrDict attrDict
  case g_or => exact DisjointProperties.fromAttrDict attrDict
  case g_ptr_add => exact PtrAddProperties.fromAttrDict attrDict
  case g_icmp => exact IcmpProperties.fromAttrDictFor "gmir.g_icmp" attrDict
  case g_zext => exact NnegProperties.fromAttrDict attrDict
  case g_anyext | g_sext
     | g_and | g_xor | g_srem | g_urem | g_rotr | g_rotl
     | g_inttoptr | g_ptrtoint | g_bitcast | g_bswap | g_bitreverse
     | g_saddsat | g_uaddsat | g_ssubsat | g_usubsat | g_sshlsat | g_ushlsat
     | g_smin | g_smax | g_umin | g_umax | g_abs
     | g_uaddo | g_saddo | g_usubo | g_ssubo | g_smulo | g_umulo
     | g_umulh | g_smulh | g_ctlz | g_cttz | g_ctpop => exact .ok ()

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
  | .g_zext | .g_ptr_add => props.toAttrDict
  | .g_anyext | .g_sext
  | .g_and | .g_xor | .g_srem | .g_urem | .g_rotr | .g_rotl
  | .g_inttoptr | .g_ptrtoint | .g_bitcast | .g_bswap | .g_bitreverse
  | .g_saddsat | .g_uaddsat | .g_ssubsat | .g_usubsat | .g_sshlsat | .g_ushlsat
  | .g_smin | .g_smax | .g_umin | .g_umax | .g_abs
  | .g_uaddo | .g_saddo | .g_usubo | .g_ssubo | .g_smulo | .g_umulo
  | .g_umulh | .g_smulh | .g_ctlz | .g_cttz | .g_ctpop => {}

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
  | .g_smin | .g_smax | .g_umin | .g_umax | .g_umulh | .g_smulh =>
    { outOperandList := #[.type 0]
      inOperandList := #[.type 0, .type 0] }
  | .g_shl | .g_lshr | .g_ashr | .g_rotr | .g_rotl | .g_sshlsat | .g_ushlsat | .g_ptr_add =>
    { outOperandList := #[.type 0]
      inOperandList := #[.type 0, .type 1] }
  | .g_icmp =>
    { outOperandList := #[.type 0]
      inOperandList := #[.type 1, .type 1] }
  | .g_anyext | .g_sext | .g_zext | .g_trunc
  | .g_inttoptr | .g_ptrtoint | .g_bitcast | .g_ctlz | .g_cttz | .g_ctpop =>
    { outOperandList := #[.type 0]
      inOperandList := #[.type 1] }
  | .g_bswap | .g_bitreverse | .g_abs =>
    { outOperandList := #[.type 0]
      inOperandList := #[.type 0] }
  | .g_uaddo | .g_saddo | .g_usubo | .g_ssubo | .g_smulo | .g_umulo =>
    { outOperandList := #[.type 0, .type 1]
      inOperandList := #[.type 0, .type 0] }

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


/-- Interprets a binary operation whose operands and result all have the same integer type. -/
private def interpretIntBinop (operands : Array RuntimeValue) (mem : MemoryState)
    (f : {w : Nat} → Data.LLVM.Int w → Data.LLVM.Int w → Data.LLVM.Int w)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) := do
  let [.int bw lhs, .int bw' rhs] := operands.toList | none
  if h : bw' ≠ bw then none else
  let rhs := rhs.cast (by simp at h; exact h)
  return (#[.int bw (f lhs rhs)], mem, none)

/--
Converts a shift amount (type group 1) to the width `w` of the shifted value (type group 0).
An amount that does not fit in `w` bits is out of range, so it is replaced by the all-ones value,
which is also out of range and hence yields the same (poison) result.
-/
private def shiftAmount {w' : Nat} (w : Nat) : Data.LLVM.Int w' → Data.LLVM.Int w
  | .val v => .val (if v.toNat < w then BitVec.ofNat w v.toNat else BitVec.allOnes w)
  | .poison => .poison

/-- Interprets a shift-like operation `type0 <- type0, type1`. -/
private def interpretIntShift (operands : Array RuntimeValue) (mem : MemoryState)
    (f : {w : Nat} → Data.LLVM.Int w → Data.LLVM.Int w → Data.LLVM.Int w)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) := do
  let [.int bw lhs, .int _ rhs] := operands.toList | none
  return (#[.int bw (f lhs (shiftAmount bw rhs))], mem, none)

/--
Interprets `g_rotl`/`g_rotr` as a funnel shift of the value with itself. The rotate amount is
taken modulo the bit width, so it never produces poison on its own.
-/
private def interpretIntRotate (operands : Array RuntimeValue) (mem : MemoryState)
    (f : {w : Nat} → Data.LLVM.Int w → Data.LLVM.Int w → Data.LLVM.Int w → Data.LLVM.Int w)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) := do
  let [.int bw x, .int _ amt] := operands.toList | none
  let amt : Data.LLVM.Int bw := match amt with
    | .val v => .val (BitVec.ofNat bw (v.toNat % bw))
    | .poison => .poison
  return (#[.int bw (f x x amt)], mem, none)

/-- Converts a bit count to the width `w` of the result (type group 0) of `g_ctlz`/`g_cttz`/`g_ctpop`. -/
private def resizeCount {w' : Nat} (w : Nat) : Data.LLVM.Int w' → Data.LLVM.Int w
  | .val v => .val (BitVec.ofNat w v.toNat)
  | .poison => .poison

/-- Interprets a unary bit-counting operation `type0 <- type1`. -/
private def interpretIntCount (operands : Array RuntimeValue) (resultTypes : Array TypeAttr)
    (mem : MemoryState) (f : {w : Nat} → Data.LLVM.Int w → Data.LLVM.Int w)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) := do
  let [.int _ x] := operands.toList | none
  let some resType := resultTypes[0]? | none
  let .integerType resBw := resType.val | none
  return (#[.int resBw.bitwidth (resizeCount resBw.bitwidth (f x))], mem, none)

/--
Interprets an operation with an overflow (carry) result, `type0, type1 <- type0, type0`.
The carry is `1` when `overflows` holds, zero-extended to the carry width. If either operand is
poison, both results are poison.
-/
private def interpretIntOverflowOp (operands : Array RuntimeValue) (resultTypes : Array TypeAttr)
    (mem : MemoryState) (f : {w : Nat} → BitVec w → BitVec w → BitVec w)
    (overflows : {w : Nat} → BitVec w → BitVec w → Bool)
    : Interp ((Array RuntimeValue) × MemoryState × Option ControlFlowAction) := do
  let [.int bw lhs, .int bw' rhs] := operands.toList | none
  if h : bw' ≠ bw then none else
  let rhs := rhs.cast (by simp at h; exact h)
  let some carryType := resultTypes[1]? | none
  let .integerType carryBw := carryType.val | none
  let carryW := carryBw.bitwidth
  match lhs, rhs with
  | .val x, .val y =>
    let carry := (BitVec.ofBool (overflows x y)).zeroExtend carryW
    return (#[.int bw (.val (f x y)), .int carryW (.val carry)], mem, none)
  | _, _ => return (#[.int bw .poison, .int carryW .poison], mem, none)

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

def GMIR.interpretOp' (opType : Veir.GMIR) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (_blockOperands : Array BlockPtr)
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
    return (#[.int 1 (Data.LLVM.Int.icmp lhs rhs properties.predicate)], mem, none)
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
  | .g_mul => interpretIntBinop operands mem (Data.LLVM.Int.mul · · properties.nsw properties.nuw)
  | .g_and => interpretIntBinop operands mem Data.LLVM.Int.and
  | .g_or => interpretIntBinop operands mem (Data.LLVM.Int.or · · properties.disjoint)
  | .g_xor => interpretIntBinop operands mem Data.LLVM.Int.xor
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
  | .g_shl => interpretIntShift operands mem (Data.LLVM.Int.shl · · properties.nsw properties.nuw)
  | .g_lshr => interpretIntShift operands mem (Data.LLVM.Int.lshr · · properties.exact)
  | .g_ashr => interpretIntShift operands mem (Data.LLVM.Int.ashr · · properties.exact)
  | .g_sshlsat => interpretIntShift operands mem Data.LLVM.Int.sshlSat
  | .g_ushlsat => interpretIntShift operands mem Data.LLVM.Int.ushlSat
  | .g_rotl => interpretIntRotate operands mem Data.LLVM.Int.fshl
  | .g_rotr => interpretIntRotate operands mem Data.LLVM.Int.fshr
  | .g_saddsat => interpretIntBinop operands mem Data.LLVM.Int.saddSat
  | .g_uaddsat => interpretIntBinop operands mem Data.LLVM.Int.uaddSat
  | .g_ssubsat => interpretIntBinop operands mem Data.LLVM.Int.ssubSat
  | .g_usubsat => interpretIntBinop operands mem Data.LLVM.Int.usubSat
  | .g_smin => interpretIntBinop operands mem Data.LLVM.Int.smin
  | .g_smax => interpretIntBinop operands mem Data.LLVM.Int.smax
  | .g_umin => interpretIntBinop operands mem Data.LLVM.Int.umin
  | .g_umax => interpretIntBinop operands mem Data.LLVM.Int.umax
  | .g_umulh => interpretIntBinop operands mem Data.LLVM.Int.umulHigh
  | .g_smulh => interpretIntBinop operands mem Data.LLVM.Int.smulHigh
  | .g_uaddo => interpretIntOverflowOp operands resultTypes mem (· + ·) BitVec.uaddOverflow
  | .g_saddo => interpretIntOverflowOp operands resultTypes mem (· + ·) BitVec.saddOverflow
  | .g_usubo => interpretIntOverflowOp operands resultTypes mem (· - ·) BitVec.usubOverflow
  | .g_ssubo => interpretIntOverflowOp operands resultTypes mem (· - ·) BitVec.ssubOverflow
  | .g_umulo => interpretIntOverflowOp operands resultTypes mem (· * ·) BitVec.umulOverflow
  | .g_smulo => interpretIntOverflowOp operands resultTypes mem (· * ·) BitVec.smulOverflow
  -- `G_ABS` has no "int min is poison" flag: `abs(INT_MIN) = INT_MIN`.
  | .g_abs => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (Data.LLVM.Int.abs x false)], mem, none)
  | .g_bswap => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (Data.LLVM.Int.bswap x)], mem, none)
  | .g_bitreverse => do
    let [.int bw x] := operands.toList | none
    return (#[.int bw (Data.LLVM.Int.bitreverse x)], mem, none)
  -- `G_CTLZ`/`G_CTTZ` are defined at zero; the zero-is-poison forms are separate opcodes.
  | .g_ctlz => interpretIntCount operands resultTypes mem (Data.LLVM.Int.ctlz · false)
  | .g_cttz => interpretIntCount operands resultTypes mem (Data.LLVM.Int.cttz · false)
  | .g_ctpop => interpretIntCount operands resultTypes mem Data.LLVM.Int.ctpop
  | .g_bitcast => do
    let [.int bw x] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if h : bw = resBw.bitwidth then return (#[.int resBw.bitwidth (x.cast h)], mem, none) else none
  | .g_inttoptr => do
    let [.int bw val] := operands.toList | none
    if h : bw = 64 then return (#[.addr (mem.ptrFromInt (val.cast h))], mem, none) else .fail none
  | .g_ptrtoint => do
    let [.addr val] := operands.toList | none
    let some resType := resultTypes[0]? | none
    let .integerType resBw := resType.val | none
    if resBw.bitwidth = 64 then return (#[.int 64 val.toInt], mem, none) else .fail none
  /- The offset is sign-extended to the pointer width. `nuw` and `nusw` make an unsigned or
     signed wrap of the address poison. `inbounds` is not checked. -/
  | .g_ptr_add => do
    let [.addr ptr, .int _ off] := operands.toList | none
    match ptr, off with
    | .val ptr, .val off =>
      let addr := ptr.address.toBitVec
      let off := off.signExtend 64
      let unsignedWrap := (addr.toNat + off.toInt) < 0 || (addr.toNat + off.toInt) ≥ 2 ^ 64
      if properties.nuw && unsignedWrap then return (#[.addr .poison], mem, none)
      if properties.nusw && BitVec.saddOverflow addr off then return (#[.addr .poison], mem, none)
      return (#[.addr (.val ⟨ptr.object, UInt64.ofBitVec (addr + off)⟩)], mem, none)
    | _, _ => return (#[.addr .poison], mem, none)

/--
Verify the local invariants of a `gmir` operation in any operation-info type
containing the `gmir` dialect.
-/
def GMIR.verifyLocalInvariants {OpInfo : Type} [IsOpCode OpInfo]
    [HasDialect OpInfo GMIR] (opCode : GMIR) (opPtr : OperationPtr)
    (ctx : WfIRContext OpInfo) (opIn : opPtr.InBounds ctx.raw) :
    Except String PUnit := do
  let info := opCode.genericOpInfo
  -- Verify operand and result counts.
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
  | .g_add | .g_sub =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyIntegerBinop ctx opIn
  | .g_icmp =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyGMIRICmp ctx opIn
  | .g_anyext | .g_sext | .g_zext =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyIntegerExtTypes ctx opIn
  | .g_trunc =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyTruncTypes ctx opIn (allowByte := false)
  | .g_mul | .g_and | .g_or | .g_xor | .g_sdiv | .g_udiv | .g_srem | .g_urem
  | .g_shl | .g_lshr | .g_ashr | .g_rotr | .g_rotl
  | .g_saddsat | .g_uaddsat | .g_ssubsat | .g_usubsat | .g_sshlsat | .g_ushlsat
  | .g_smin | .g_smax | .g_umin | .g_umax | .g_abs | .g_bitreverse
  | .g_uaddo | .g_saddo | .g_usubo | .g_ssubo | .g_smulo | .g_umulo
  | .g_umulh | .g_smulh | .g_ctlz | .g_cttz | .g_ctpop =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyGMIRIntegerTypes ctx opIn
  | .g_bswap =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyGMIRIntegerTypes ctx opIn
    let .integerType intType := ((opPtr.getResult 0).getType! ctx.raw).val
      | throw "gmir.g_bswap: Expected result to have integer type"
    if intType.bitwidth ∉ [16, 32, 64] then
      throw "gmir.g_bswap: bitwidth must be 16, 32, or 64"
  | .g_bitcast =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    opPtr.verifyGMIRIntegerTypes ctx opIn
    let .integerType fromType := ((opPtr.getOperand! ctx.raw 0).getType! ctx.raw).val
      | throw "gmir.g_bitcast: Expected operand 0 to have integer type"
    let .integerType toType := ((opPtr.getResult 0).getType! ctx.raw).val
      | throw "gmir.g_bitcast: Expected result to have integer type"
    if fromType.bitwidth ≠ toType.bitwidth then
      throw "gmir.g_bitcast: Expected operand and result to have the same bitwidth"
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
  | .g_ptr_add =>
    opPtr.checkIsNonNullIntegerType ctx opIn
    ((opPtr.getOperand! ctx.raw 0).getType! ctx.raw).verifyLlvmPointerType
      "gmir.g_ptr_add: Expected operand 0 to have !llvm.ptr type"
    ((opPtr.getOperand! ctx.raw 1).getType! ctx.raw).verifyIntegerType
      "gmir.g_ptr_add: Expected operand 1 to have integer type"

def GMIR.propagatesPoison : GMIR → Bool
  | .g_add | .g_sub | .g_icmp | .g_anyext | .g_sext | .g_zext | .g_trunc
  | .g_mul | .g_and | .g_or | .g_xor | .g_sdiv | .g_udiv | .g_srem | .g_urem
  | .g_shl | .g_lshr | .g_ashr | .g_rotr | .g_rotl
  | .g_inttoptr | .g_ptrtoint | .g_ptr_add | .g_bitcast | .g_bswap | .g_bitreverse
  | .g_saddsat | .g_uaddsat | .g_ssubsat | .g_usubsat | .g_sshlsat | .g_ushlsat
  | .g_smin | .g_smax | .g_umin | .g_umax | .g_abs
  | .g_uaddo | .g_saddo | .g_usubo | .g_ssubo | .g_smulo | .g_umulo
  | .g_umulh | .g_smulh | .g_ctlz | .g_cttz | .g_ctpop => true

def GMIR.getEffects (_op : GMIR) (_props : GMIR.propertiesOf _op) : MemoryEffects :=
  .none

def GMIR.isConstantLike (_op : GMIR) : Bool :=
  false

def GMIR.hasSSADominance (_op : GMIR) (_index : Nat) : Bool :=
  true

def GMIR.isTerminator (_op : GMIR) : Bool :=
  false

instance : HasOpInfo GMIR where
  verifyLocalInvariants := GMIR.verifyLocalInvariants
  propagatesPoison := GMIR.propagatesPoison
  getEffects := GMIR.getEffects
  isConstantLike := GMIR.isConstantLike
  hasSSADominance := GMIR.hasSSADominance
  isTerminator := GMIR.isTerminator

end

end Veir
