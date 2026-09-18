module

public import Veir.RuntimeValue
public import Veir.Interpreter.Memory
public import Veir.Interpreter.Util
public import Veir.Interpreter.CTree
public import Veir.DataLayout.RISCV64

public section

open CTree
open Veir.Data
/-!
  # CTree-based LLVM Interpreter

  This file contains relevant effects and
  a simple CTree interpreter for a subset of LLVM operations.
-/

namespace Veir

/-- Choice of a bitvector of a given bitwidth (input type) -/
structure FreezeCIn : Type u where
  bw : Nat

/-- Choice of a bitvector of a given bitwidth (output type) -/
abbrev FreezeC (c : FreezeCIn.{u}) : Type :=
  match c with
  | .mk bw => BitVec bw

def Llvm.interpretOpCTree (opType : Veir.Llvm) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue) (blockOperands : Array BlockPtr)
    (mem : MemoryState) (layout : DataLayout := .riscv64)
    : CTree (ErrorE ⊕ₑ UBE) FreezeC (((Array RuntimeValue) × MemoryState × Option ControlFlowAction)) :=
  match opType with
  | .mlir__constant => do
    let some resType := resultTypes[0]? | fail
    match properties.value with
    | .integer intAttr =>
      let .integerType bw := resType.val
        | fail
      let origbw := intAttr.type.bitwidth
      let rawbits := BitVec.ofInt origbw intAttr.value
      let extended := match origbw with
        | 1 => rawbits.zeroExtend bw.bitwidth
        | _ => rawbits.signExtend bw.bitwidth
      return (#[.int bw.bitwidth (LLVM.Int.val extended)], mem, none)
    | .float floatAttr =>
      let .floatType bw := resType.val
        | fail
      return (#[.float floatAttr.type floatAttr.value], mem, none)
    | .dense denseAttr =>
      fail
    | .string _ =>
      fail
  | .mlir__poison => do
    let some resType := resultTypes[0]? | fail
    match resType.val with
    | .integerType bw => return (#[.int bw.bitwidth (LLVM.Int.mlir_poison bw.bitwidth)], mem, none)
    | .llvmPointerType _ => return (#[.addr .poison], mem, none)
    | _ => fail
  | .mlir__zero => do
    let some resType := resultTypes[0]? | fail
    match resType.val with
    | .integerType bw =>
      return (#[.int bw.bitwidth (LLVM.Int.val (BitVec.ofNat bw.bitwidth 0))], mem, none)
    | .llvmPointerType _ => return (#[.addr LLVM.Ptr.null], mem, none)
    | _ => fail
  | .add => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.add lhs rhs properties.nsw properties.nuw)], mem, none)
  | .sub => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.sub lhs rhs properties.nsw properties.nuw)], mem, none)
  | .mul => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.mul lhs rhs properties.nsw properties.nuw)], mem, none)
  | .sdiv => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    monadLift $ Interp.checkSignedDivision lhs rhs
    return (#[.int bw (LLVM.Int.sdiv lhs rhs properties.exact)], mem, none)
  | .udiv => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    monadLift $ Interp.checkUnsignedDivision rhs
    return (#[.int bw (LLVM.Int.udiv lhs rhs properties.exact)], mem, none)
  | .srem => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    monadLift $ Interp.checkSignedDivision lhs rhs
    return (#[.int bw (LLVM.Int.srem lhs rhs)], mem, none)
  | .urem => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    monadLift $ Interp.checkUnsignedDivision rhs
    return (#[.int bw (LLVM.Int.urem lhs rhs)], mem, none)
  | .shl => do
    let [lhs, .int bw' rhs] := operands.toList | fail
    match lhs with
    | .int bw lhs =>
      if h: bw' ≠ bw then fail else
      let rhs := rhs.cast (by simp at h; exact h)
      return (#[.int bw (LLVM.Int.shl lhs rhs properties.nsw properties.nuw)], mem, none)
    | .byte bw lhs =>
      if h: bw' ≠ bw then fail else
      if properties.nsw then fail else
      let rhs := rhs.cast (by simp at h; exact h)
      return (#[.byte bw (LLVM.Byte.shl lhs rhs properties.nuw)], mem, none)
    | _ => fail
  | .lshr => do
    let [lhs, .int bw' rhs] := operands.toList | fail
    match lhs with
    | .int bw lhs =>
      if h: bw' ≠ bw then fail else
      let rhs := rhs.cast (by simp at h; exact h)
      return (#[.int bw (LLVM.Int.lshr lhs rhs properties.exact)], mem, none)
    | .byte bw lhs =>
      if h: bw' ≠ bw then fail else
      let rhs := rhs.cast (by simp at h; exact h)
      return (#[.byte bw (LLVM.Byte.lshr lhs rhs properties.exact)], mem, none)
    | _ => fail
  | .ashr => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.ashr lhs rhs properties.exact)], mem, none)
  | .intr__fshl => do
    let [.int bw a, .int bw' b, .int bw'' c] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    if h'': bw'' ≠ bw then fail else
    let b := b.cast (by simp at h; exact h)
    let c := c.cast (by simp at h''; exact h'')
    return (#[.int bw (LLVM.Int.fshl a b c)], mem, none)
  | .intr__fshr => do
    let [.int bw a, .int bw' b, .int bw'' c] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    if h'': bw'' ≠ bw then fail else
    let b := b.cast (by simp at h; exact h)
    let c := c.cast (by simp at h''; exact h'')
    return (#[.int bw (LLVM.Int.fshr a b c)], mem, none)
  | .intr__ctlz => do
    let [.int bw x] := operands.toList | fail
    return (#[.int bw (LLVM.Int.ctlz x properties.is_zero_poison)], mem, none)
  | .intr__cttz => do
    let [.int bw x] := operands.toList | fail
    return (#[.int bw (LLVM.Int.cttz x properties.is_zero_poison)], mem, none)
  | .intr__ctpop => do
    let [.int bw x] := operands.toList | fail
    return (#[.int bw (LLVM.Int.ctpop x)], mem, none)
  | .intr__bswap => do
    let [.int bw x] := operands.toList | fail
    return (#[.int bw (LLVM.Int.bswap x)], mem, none)
  | .intr__bitreverse => do
    let [.int bw x] := operands.toList | fail
    return (#[.int bw (LLVM.Int.bitreverse x)], mem, none)
  | .and => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.and lhs rhs)], mem, none)
  | .or => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.or lhs rhs properties.disjoint)], mem, none)
  | .xor => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.xor lhs rhs)], mem, none)
  | .intr__smax => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.smax lhs rhs)], mem, none)
  | .intr__smin => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.smin lhs rhs)], mem, none)
  | .intr__umax => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.umax lhs rhs)], mem, none)
  | .intr__umin => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.umin lhs rhs)], mem, none)
  | .intr__abs => do
    let [.int bw x] := operands.toList | fail
    return (#[.int bw (LLVM.Int.abs x properties.is_int_min_poison)], mem, none)
  | .intr__sadd__sat => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.saddSat lhs rhs)], mem, none)
  | .intr__uadd__sat => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.uaddSat lhs rhs)], mem, none)
  | .intr__ssub__sat => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.ssubSat lhs rhs)], mem, none)
  | .intr__usub__sat => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.usubSat lhs rhs)], mem, none)
  | .intr__sshl__sat => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.sshlSat lhs rhs)], mem, none)
  | .intr__ushl__sat => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simp at h; exact h)
    return (#[.int bw (LLVM.Int.ushlSat lhs rhs)], mem, none)
  | .trunc => do
    let [val] := operands.toList | fail
    let some resType := resultTypes[0]? | fail
    match val with
    | .int w val =>
        let .integerType resBw := resType.val | fail
        if h: resBw.bitwidth >= w then fail else
        return (#[.int resBw.bitwidth (LLVM.Int.trunc val resBw.bitwidth properties.nsw properties.nuw (by omega))], mem, none)
    | .byte w val =>
        let .byteType resBw := resType.val | fail
        if h: resBw.bitwidth >= w then fail else
        return (#[.byte resBw.bitwidth (LLVM.Byte.trunc val resBw.bitwidth)], mem, none)
    | _ => fail
  | .zext => do
    let [.int w val] := operands.toList | fail
    let some resType := resultTypes[0]? | fail
    let .integerType resBw := resType.val | fail
    if h: resBw.bitwidth <= w then fail else
    return (#[.int resBw.bitwidth (LLVM.Int.zext val resBw.bitwidth properties.nneg (by omega))], mem, none)
  | .sext => do
    let [.int w val] := operands.toList | fail
    let some resType := resultTypes[0]? | fail
    let .integerType resBw := resType.val | fail
    if h: resBw.bitwidth <= w then fail else
    return (#[.int resBw.bitwidth (LLVM.Int.sext val resBw.bitwidth (by omega))], mem, none)
  | .icmp => do
    let [.int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simpa using h)
    return (#[.int 1 (LLVM.Int.icmp lhs rhs properties.predicate)], mem, none)
  | .select => do
    let [.int 1 cond, .int bw lhs, .int bw' rhs] := operands.toList | fail
    if h: bw' ≠ bw then fail else
    let rhs := rhs.cast (by simpa using h)
    return (#[.int bw (LLVM.Int.select cond lhs rhs)], mem, none)
  | .return => do
    return (#[], mem, some (.return operands))
  | .unreachable =>
    ub
  | .br => do
    let [dest] := blockOperands.toList | fail
    return (#[], mem, some (.branch operands dest))
  | .cond_br => do
    let [destTrue, destFalse] := blockOperands.toList | fail
    let some condVal := operands[0]? | fail
    let some (trueSizeInt : Int) := properties.operandSegmentSizes.values[1]? | fail
    let trueSize := trueSizeInt.toNat
    match condVal with
    | .int 1 (.val cond) =>
      if cond = 1#1 then
        return (#[], mem, some (.branch (operands.extract 1 (trueSize + 1)) destTrue))
      else
        return (#[], mem, some (.branch (operands.extract (trueSize + 1) operands.size) destFalse))
    | .int 1 .poison => ub
    | _ => fail
  | .switch => do
    let some destDefault := blockOperands[0]? | fail
    let some value := operands[0]? | fail
    let some (defaultSizeInt : Int) := properties.operandSegmentSizes.values[1]? | fail
    let defaultSize := defaultSizeInt.toNat
    let caseSegments := properties.case_operand_segments.values
    let some caseValues := properties.caseValues? | fail
    /- A case value per case, or the switch cannot be read. -/
    if caseValues.size ≠ caseSegments.size then fail else
    match value with
    | .int bw (.val v) =>
      let mut base := 1 + defaultSize
      for i in [0:caseSegments.size] do
        let some (countInt : Int) := caseSegments[i]? | fail
        let count := countInt.toNat
        if v = BitVec.ofInt bw caseValues[i]! then
          let some dest := blockOperands[i + 1]? | fail
          return (#[], mem, some (.branch (operands.extract base (base + count)) dest))
        base := base + count
      return (#[], mem, some (.branch (operands.extract 1 (1 + defaultSize)) destDefault))
    | .int _ .poison => ub
    | _ => fail
  | .alloca => do
    let [.int _ (.val count)] := operands.toList | fail
    /- `alloca T, N` reserves `N` strides of `T`, as in LLVM. -/
    let size ← monadLift $ layout.getTypeAllocSize properties.elem_type.val
    let totalSize := (size * count.toNat).toUInt64
    let (mem, addr) := mem.alloc totalSize
    return (#[.addr (.val addr)], mem, none)
  | .load => do
    let [.addr addr] := operands.toList | fail
    let .val addr := addr | ub
    let [type] := resultTypes.toList | fail
    let val ← monadLift $ mem.llvmLoad addr type
    return (#[val], mem, none)
  | .store => do
    let [val, .addr addr] := operands.toList | fail
    let .val addr := addr | ub
    let mem ← monadLift $ mem.llvmStore addr val
    return (#[], mem, none)
  | .getelementptr => do
    /- only supports exactly one dynamic index for now -/
    let [.addr ptr, .int _ idx] := operands.toList | fail
    /- The index scales by the element's stride, matching the `getTypeAllocSize`
       that `isel-riscv64` uses to lower this operation. -/
    let size ← monadLift $ layout.getTypeAllocSize properties.elem_type.val
    match ptr, idx with
    | .val ptr, .val idx => return (#[.addr (.val (ptr.toNat + idx.toNat * size).toUInt64)], mem, none)
    | _, _ => return (#[.addr .poison], mem, none)
  | .freeze => do
    let [val] := operands.toList | fail
    match val with
    | .int w val =>
        if let .val _ := val then
          return (#[.int w val], mem, none)
        else
          let (bv : FreezeC (.mk w)) ← CTree.choose (FreezeCIn.mk w)
          return (#[.int w (LLVM.Int.freeze val bv)], mem, none)
    | .byte w val =>
        let bv : FreezeC (.mk w) ← CTree.choose (FreezeCIn.mk w)
        return (#[.byte w (val.freeze bv)], mem, none)
    | .addr .poison => return (#[.addr LLVM.Ptr.null], mem, none)
    | .addr (.val p) => return (#[.addr (.val p)], mem, none)
    | _ => fail
  | .bitcast => do
    let [val] := operands.toList | fail
    let [⟨type, _⟩] := resultTypes.toList | fail
    let result ← monadLift $ do match val, type with
      | .int bw1 val', .integerType ⟨bw2⟩ =>
          if bw1 ≠ bw2 then Interp.fail else .ok (val)
      | .int bw1 val', .byteType ⟨bw2⟩ =>
          if bw1 ≠ bw2 then .fail else .ok ((.byte bw1 $ LLVM.Byte.fromInt val'))
      | .byte bw1 val', .byteType ⟨bw2⟩ =>
          if bw1 ≠ bw2 then .fail else .ok (val)
      | .byte bw1 val', .integerType ⟨bw2⟩ =>
          if bw1 ≠ bw2 then .fail else .ok ((.int bw1 $ val'.toInt))
      | .byte bw val', .llvmPointerType _ =>
          if h : bw = 64 then .ok (.addr (LLVM.Ptr.ofByte (val'.cast h))) else .fail
      | .addr val', .llvmPointerType _ => .ok (val)
      | .addr val', .byteType ⟨bw⟩ =>
          if bw = 64 then .ok (.byte 64 val'.toByte) else .fail
      | .addr val', .integerType ⟨bw⟩ =>
          if bw = 64 then .ok (.int 64 val'.toInt) else .fail
      | _, _ => none
    return (#[result], mem, none)
  | _ => fail

end Veir
