module

public import Veir.Pass
public import Veir.PatternRewriter.Basic
import Veir.DataLayout.RISCV64
import Veir.IR.SymbolRef
import Veir.Passes.Matching.GMIR.Basic
import Veir.Passes.Matching.LLVM.Basic
import Veir.Passes.InstructionSelection.Common
import Veir.Passes.Legalization.RISCV64LegalizerInfo
import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution

namespace Veir

open Veir.Puddle

/-!
  This file replicates LLVM's GlobalISel instruction selector,
  to lower LLVM IR to RISC-V assembly (64 bits).
-/

/-! # Lowering Patterns -/

/--
  Returns the bitwidth of the given type if it is either an LLVM integer or byte type.
-/
def getIntByteTypeBitwidth (t : TypeAttr) : Option Nat :=
  match t.val with
  | .integerType ⟨bw, _⟩ => some bw
  | .byteType ⟨bw⟩ => some bw
  | _ => none

/--
  RISC-V lowerings for funnel-shift rotates (`fshl`/`fshr` whose two data operands are
  identical).
-/
def lowerRotate (llvmOp : Llvm) (bw : Nat) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp)) : Pattern OpCode :=
  Pattern.Builder
    (do
      let opType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = bw)
      let a ← MatchProg.value opType
      let amt ← MatchProg.value opType
      let _ ← MatchProg.root (.llvm llvmOp) #[a, a, amt] #[opType]
      return (opType, a, amt))
    (fun (opType, a, amt) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let aCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[a] #[regType]
      let amtCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[amt] #[regType]
      let rotOp ← CreateProg.operation (.riscv riscvOp)
          #[aCastOp.res[0]!, amtCastOp.res[0]!] #[regType] riscvProps
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[rotOp.res[0]!] #[opType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- `llvm.intr.fshl` with identical data operands (`i64`) -> `riscv.rol`. -/
def fshl64_pattern : Pattern OpCode := lowerRotate .intr__fshl 64 .rol ()

/-- `llvm.intr.fshl` with identical data operands (`i32`) -> `riscv.rolw`. -/
def fshl32_pattern : Pattern OpCode := lowerRotate .intr__fshl 32 .rolw ()

/-- `llvm.intr.fshr` with identical data operands (`i64`) -> `riscv.ror`. -/
def fshr64_pattern : Pattern OpCode := lowerRotate .intr__fshr 64 .ror ()

/-- `llvm.intr.fshr` with identical data operands (`i32`) -> `riscv.rorw`. -/
def fshr32_pattern : Pattern OpCode := lowerRotate .intr__fshr 32 .rorw ()


/-- llvm.constant -> riscv.li. Any width up to 64 fits in one register: the constant is
  sign-extended to the 64-bit immediate (see `constant_refinement_le64`). -/
def constant_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth ≤ 64)
      let root ← MatchProg.root (.llvm .mlir__constant) #[] #[type]
          (fun props => props.value matches .integer _)
      return (type, root.properties))
    (fun (type, constProps) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let liProps ← CreateProg.applyNative
          (Outputs := Handle OpCode (.prop (.riscv .li))) (type, constProps)
          fun (type, constProps) => do
            let .integerType type' := type.val | none
            let .integer const := constProps.value | none
            return RISCVImmediateProperties.mk
                ((BitVec.ofInt type'.bitwidth const.value).signExtend 64)
      let liOp ← CreateProg.operation (.riscv .li) #[] #[regType] liProps
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[liOp.res[0]!] #[type]
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- llvm.constant -> riscv.li -/
def constant : Puddle.CompiledPattern OpCode := constant_pattern.compile

/-- The width of an `icmp` operand of type `t` once it is in a register: integers keep their
    width, and an `!llvm.ptr` is a full 64-bit register, compared exactly like an `i64`. -/
def icmpTypeWidth? (t : TypeAttr) : Option Nat :=
  match t.val with
  | .integerType t => some t.bitwidth
  | .llvmPointerType _ => some 64
  | _ => none

/-- Whether a `gmir.g_constant` with properties `props` is the integer `0`. -/
def isGMIRConstantZero (props : GMIRConstantProperties) : Bool :=
  BitVec.ofInt props.value.type.bitwidth props.value.value = 0

/--
  Whether `llvm.trunc` from `opType` to `resType` is lowered: both are integer types or both are
  byte types, and the result is strictly narrower than the operand.

  The operand is held in a 64-bit register, so an operand wider than 64 bits would lose bits in
  the round trip. Every narrower pair of widths is sound (see `trunc_refinement_le64`), including
  odd ones such as `i1`: the result's upper register bits are whatever the operand left there,
  and `reconcile-cast` zero-extends the value wherever it is used as a register again.
-/
def isLegalTrunc (opType resType : TypeAttr) : Bool :=
  let shouldTruncate := match opType.val, resType.val with
    | .integerType _, .integerType _ => true
    | .byteType _, .byteType _ => true
    | _, _ => false
  match getIntByteTypeBitwidth opType, getIntByteTypeBitwidth resType with
  | some opBw, some resBw => shouldTruncate && resBw < opBw && opBw ≤ 64
  | _, _ => false

/--
  Shared shape of the lowerings of single-operand ops that are no-ops on registers
  (`trunc`/`bitcast`/`freeze`): when `legal` accepts the operand and result types, cast the operand to a
  register, then cast the register to the result type.
-/
def lowerRegCast (srcOp : OpCode) (legal : TypeAttr → TypeAttr → propertiesOf srcOp → Bool) :
    Pattern OpCode :=
  Pattern.Builder
    (do
      let opType ← MatchProg.type (Attr := TypeAttr)
      let resType ← MatchProg.type (Attr := TypeAttr)
      let x ← MatchProg.value opType
      let root ← MatchProg.root srcOp #[x] #[resType]
      MatchProg.matchNative (opType, resType, root.properties)
          fun (opType, resType, props) => legal opType resType props
      return (resType, x))
    (fun (resType, x) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      /- First, cast the operand to registers -/
      let castOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[x] #[regType]
      /- Then, cast register to expected output type. -/
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[castOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/--
  llvm.trunc %x iX to iY -> builtin_unrealized_conversion_cast (!riscv.reg) : iY
  where `iY`'s width is smaller than `iX`'s (see `isLegalTrunc`).
  Also accepts the byte type.
-/
def trunc_pattern : Pattern OpCode :=
  lowerRegCast (.llvm .trunc) fun opType resType _ => isLegalTrunc opType resType

/--
  llvm.trunc -> builtin_unrealized_conversion_cast (see `trunc_pattern`).
-/
def trunc : Puddle.CompiledPattern OpCode := trunc_pattern.compile

def checkBitcastType (t : TypeAttr) : Bool :=
  match t.val with
  | .llvmPointerType _
  | .integerType _
  | .byteType _ => true
  | _ => false

/-- Is this a `byte -> ptr` bitcast? -/
def isBitcastByteToPtr (opType resType : TypeAttr) : Bool :=
  match opType.val, resType.val with
  | .byteType _, .llvmPointerType _ => true
  | _, _ => false

/-- Whether `llvm.bitcast` from `opType` to `resType` is lowered: both are integer, byte, or
    pointer types of width 8, 16, 32, or 64, and it is not a `byte -> ptr` bitcast. -/
def isLegalBitcast (opType resType : TypeAttr) : Bool :=
  checkBitcastType opType && checkBitcastType resType && !isBitcastByteToPtr opType resType &&
    match Attribute.bitwidthOfType opType, Attribute.bitwidthOfType resType with
    | some opBw, some resBw => opBw ∈ [8, 16, 32, 64] && resBw ∈ [8, 16, 32, 64]
    | _, _ => false

/--
  llvm.bitcast t1 %x to t2 -> builtin_unrealized_conversion_cast
  Integers, bytes, and pointers are all lowered to !riscv.reg, making this basically a no-op.
  The `byte -> ptr` case is excluded (see `isLegalBitcast`).
-/
def bitcast_pattern : Pattern OpCode :=
  lowerRegCast (.llvm .bitcast) fun opType resType _ => isLegalBitcast opType resType

/-- llvm.bitcast -> builtin_unrealized_conversion_cast (see `bitcast_pattern`). -/
def bitcast : Puddle.CompiledPattern OpCode := bitcast_pattern.compile

/--
  Lower LLVM lifetime instructions to nothing. This is a refinement that we can
  revisit later if we want to perform certain stack slot optimizations.
-/
def lowerLifetime (llvmOp : Llvm) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ptrType ← MatchProg.type (Attr := TypeAttr)
      let ptr ← MatchProg.value ptrType
      let _ ← MatchProg.root (.llvm llvmOp) #[ptr] #[]
      return ())
    pure
    (fun () => ⟨#[]⟩)

/-- Erase `llvm.intr.lifetime.start`. -/
def lifetimeStart : Puddle.CompiledPattern OpCode := (lowerLifetime .intr__lifetime__start).compile

/-- Erase `llvm.intr.lifetime.end`. -/
def lifetimeEnd : Puddle.CompiledPattern OpCode := (lowerLifetime .intr__lifetime__end).compile

/-- Resolve a global in the nearest enclosing module, without entering nested modules. -/
private partial def lookupGlobal? (ctx : IRContext OpCode) (op : OperationPtr)
    (name : ByteArray) : Option LLVMGlobalProperties := do
  let parent ← op.getParentOp! ctx
  if parent.getOpType! ctx != .builtin .module then
    return ← lookupGlobal? ctx parent name
  let body := parent.getRegion! ctx 0
  let block ← body.getFirstBlock! ctx
  let mut candidate := block.getFirstOp! ctx
  while let some target := candidate do
    if target.getOpType! ctx = .llvm .mlir__global then
      let props := target.getProperties! ctx Llvm.mlir__global
      if props.sym_name.value = name then return props
    candidate := target.getNextOp! ctx
  none

/-- Whether the `llvm.mlir.addressof` `op` names a global that `riscv.la` can address: one that
  is not thread-local or external weak, or one that cannot be resolved in an enclosing module. -/
private def isLaAddressable (ctx : IRContext OpCode) (op : OperationPtr) : Option Unit := do
  let properties := op.getProperties! ctx Llvm.mlir__addressof
  let some name := properties.global_name.getName? | none
  if let some global := lookupGlobal? ctx op name then
    -- An undefined weak symbol resolves to zero, which a PC-relative `la`
    -- cannot always reach. Leave it until GOT-based address lowering is supported.
    if global.isThreadLocal || global.linkage.value = "extern_weak" then none
  return ()

/-- `llvm.mlir.addressof` -> `riscv.la` and a cast back to the pointer type, except for TLS and
  external weak globals. -/
def addressof_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let resType ← MatchProg.type (Attr := TypeAttr)
      let root ← MatchProg.root (.llvm .mlir__addressof) #[] #[resType]
      let () ← MatchProg.inspectOperation (Outputs := Unit) root.op isLaAddressable
      return (resType, root.properties))
    (fun (resType, props) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let laProps ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.riscv .la))) props
          fun props => some (RISCVSymbolProperties.mk props.global_name)
      let laOp ← CreateProg.operation (.riscv .la) #[] #[regType] (.inr laProps)
      CreateProg.operation (.builtin .unrealized_conversion_cast) #[laOp.res[0]!] #[resType])
    (fun castBackOp => castBackOp)

/-- `llvm.mlir.addressof` -> `riscv.la` and a cast back to the pointer type. -/
def addressof : Puddle.CompiledPattern OpCode := addressof_pattern.compile

/--
  The signed 12-bit immediate offset of a load/store address `getelementptr base, c*`, with
  properties `gep` and constant `i64` dynamic indices `c*` with properties `idxs`, when it can
  be folded into the access, mirroring the `isBaseWithConstantOffset` case of LLVM's
  [`RISCVDAGToDAGISel::SelectAddrRegImm`](https://github.com/llvm/llvm-project/blob/llvmorg-22.1.8/llvm/lib/Target/RISCV/RISCVISelDAGToDAG.cpp#L3175-L3206).
-/
def selectAddrRegImm (gep : GetelementptrProperties) (idxs : Array GMIRConstantProperties) :
    Option Int := do
  let idxs := idxs.map fun idx => (BitVec.ofInt 64 idx.value.value).toInt
  let indices := GEPIndex.decode gep.rawConstantIndices.values idxs
  let (offset, dynamic) ← DataLayout.riscv64.gepOffsets gep.elem_type.val indices
  let offset := dynamic.foldl (init := offset) fun offset (c, stride) => offset + c * stride
  guard (-2048 ≤ offset ∧ offset ≤ 2047)
  return offset

inductive AddrMode where
  | reg
  | gepIndex
  | gepConst

/-- The width in bytes of a load or store of a value of `type`, for the integers
  and pointers whose data-layout size fits one `l*`/`s*` instruction. An integer
  must fill its bytes exactly, since `getTypeSize` rounds an odd width up. -/
def memAccessWidth? (type : TypeAttr) : Option Nat := do
  match type.val with
  | .integerType t => guard (t.bitwidth % 8 = 0)
  | .llvmPointerType _ => pure ()
  | _ => none
  let width ← DataLayout.riscv64.getTypeSize type.val
  guard (width ∈ [1, 2, 4, 8])
  return width

/-- `riscv.lb` / `riscv.lh` / `riscv.lw` / `riscv.ld`, for a `width`-byte load. -/
def createLoadLocal (ctx : WfIRContext OpCode) (width : Nat) (addr : ValuePtr)
    (props : RISCVMemProperties) : Option (WfIRContext OpCode × OperationPtr) :=
  match width with
  | 1 => WfRewriter.createOp! ctx Riscv.lb #[RegisterType.mk] #[addr] #[] #[] props none
  | 2 => WfRewriter.createOp! ctx Riscv.lh #[RegisterType.mk] #[addr] #[] #[] props none
  | 4 => WfRewriter.createOp! ctx Riscv.lw #[RegisterType.mk] #[addr] #[] #[] props none
  | _ => WfRewriter.createOp! ctx Riscv.ld #[RegisterType.mk] #[addr] #[] #[] props none

/-- `riscv.sb` / `riscv.sh` / `riscv.sw` / `riscv.sd`, for a `width`-byte store. -/
def createStoreLocal (ctx : WfIRContext OpCode) (width : Nat) (val addr : ValuePtr)
    (props : RISCVMemProperties) : Option (WfIRContext OpCode × OperationPtr) :=
  match width with
  | 1 => WfRewriter.createOp! ctx Riscv.sb #[] #[val, addr] #[] #[] props none
  | 2 => WfRewriter.createOp! ctx Riscv.sh #[] #[val, addr] #[] #[] props none
  | 4 => WfRewriter.createOp! ctx Riscv.sw #[] #[val, addr] #[] #[] props none
  | _ => WfRewriter.createOp! ctx Riscv.sd #[] #[val, addr] #[] #[] props none

abbrev FoldedGEPProperties :=
  Handle OpCode (.prop (.llvm .getelementptr)) ×
    Option (Handle OpCode (.prop (.gmir .g_constant)))

/-- Match the address of a load or store of `base`, split into a base register and a signed
  12-bit offset as `mode` says (see `AddrMode`). -/
def matchAddr (mode : AddrMode) (base : Handle OpCode .value) :
    MatchProg.Builder (Handle OpCode .value × Option FoldedGEPProperties) :=
  match mode with
  | .reg => pure (base, none)
  | .gepIndex => do
    let idxType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 64)
    let idxOp ← MatchProg.operation (.gmir .g_constant) #[] #[idxType]
    let addrType ← MatchProg.type (Attr := TypeAttr)
    let gepOp ← MatchProg.operation (.llvm .getelementptr) #[base, idxOp.res[0]!] #[addrType]
    MatchProg.matchNative (gepOp.properties, idxOp.properties)
        fun (gep, idx) => (selectAddrRegImm gep #[idx]).isSome
    pure (gepOp.res[0]!, some (gepOp.properties, some idxOp.properties))
  | .gepConst => do
    let addrType ← MatchProg.type (Attr := TypeAttr)
    let gepOp ← MatchProg.operation (.llvm .getelementptr) #[base] #[addrType]
    MatchProg.matchNative gepOp.properties fun gep => (selectAddrRegImm gep #[]).isSome
    pure (gepOp.res[0]!, some (gepOp.properties, none))

/-- The `riscvOp` properties of a load or store with properties `access` at an address
  matched by `matchAddr`: the folded offset, and the access's volatility. Volatility carries
  over since, although the riscv op encodes the same access, the flag keeps later passes
  from deleting or duplicating it. -/
def addrMemProps (riscvOp : Riscv) (h : propertiesOf (OpCode.riscv riscvOp) = RISCVMemProperties)
    {accessOp : OpCode} (volatile : propertiesOf accessOp → Bool) (gep? : Option FoldedGEPProperties)
    (access : Handle OpCode (.prop accessOp)) :
    CreateProg.Builder (Handle OpCode (.prop (.riscv riscvOp))) :=
  let memProps (offset? : Option Int) (props : propertiesOf accessOp) :=
    offset?.map fun offset =>
      cast h.symm (RISCVMemProperties.mk (BitVec.ofInt 64 offset) (volatile props))
  match gep? with
  | some (gepProps, some idxProps) =>
    CreateProg.applyNative (gepProps, idxProps, access)
      fun (gep, idx, props) => memProps (selectAddrRegImm gep #[idx]) props
  | some (gepProps, none) =>
    CreateProg.applyNative (gepProps, access)
      fun (gep, props) => memProps (selectAddrRegImm gep #[]) props
  | none => CreateProg.applyNative access fun props => memProps (some 0) props

/--
  llvm.load -> riscv.ld (i64, ptr) / riscv.lw (i32) / riscv.lh (i16) / riscv.lb (i8), for a
  `width`-byte load with `riscvOp`, its address split as `mode` says (see `AddrMode`).
-/
def lowerLoad (mode : AddrMode) (width : Nat) (riscvOp : Riscv)
    (h : propertiesOf (OpCode.riscv riscvOp) = RISCVMemProperties := by rfl) :
    Pattern OpCode :=
  Pattern.Builder
    (do
      let baseType ← MatchProg.type (Attr := TypeAttr)
      let base ← MatchProg.value baseType
      let (addr, gep?) ← matchAddr mode base
      /- support `i64`, `i32`, `i16`, `i8` and `!llvm.ptr` (the loaded value type) -/
      let resType ← MatchProg.type (Attr := TypeAttr)
          (fun t => memAccessWidth? t = some width)
      let root ← MatchProg.root (.llvm .load) #[addr] #[resType]
      return (resType, base, gep?, root.properties))
    (fun (resType, base, gep?, loadProps) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      /- cast base (!llvm.ptr) -> register -/
      let baseCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[base] #[regType]
      let memProps ←
        addrMemProps riscvOp h (accessOp := .llvm .load) (·.volatile_) gep? loadProps
      let ldOp ← CreateProg.operation (.riscv riscvOp)
          #[baseCastOp.res[0]!] #[regType] memProps
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[ldOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/--
  llvm.load -> riscv.ld (i64, ptr) / riscv.lw (i32) / riscv.lh (i16) / riscv.lb (i8).
  The patterns folding a constant `getelementptr` offset into the immediate come first.
-/
def load : Array (Puddle.CompiledPattern OpCode) :=
  #[AddrMode.gepIndex, .gepConst, .reg].flatMap fun mode =>
    #[lowerLoad mode 1 .lb, lowerLoad mode 2 .lh, lowerLoad mode 4 .lw,
      lowerLoad mode 8 .ld].map (·.compile)

/--
  llvm.store -> riscv.sd (i64, ptr) / riscv.sw (i32) / riscv.sh (i16) / riscv.sb (i8), for a
  `width`-byte store with `riscvOp`. The address is split as in `lowerLoad`.
-/
def lowerStore (mode : AddrMode) (width : Nat) (riscvOp : Riscv)
    (h : propertiesOf (OpCode.riscv riscvOp) = RISCVMemProperties := by rfl) :
    Pattern OpCode :=
  Pattern.Builder
    (do
      /- support `i64`, `i32`, `i16`, `i8` and `!llvm.ptr` (the stored value type) -/
      let valType ← MatchProg.type (Attr := TypeAttr)
          (fun t => memAccessWidth? t = some width)
      let val ← MatchProg.value valType
      let baseType ← MatchProg.type (Attr := TypeAttr)
      let base ← MatchProg.value baseType
      let (addr, gep?) ← matchAddr mode base
      let root ← MatchProg.root (.llvm .store) #[val, addr] #[]
      return (val, base, gep?, root.properties))
    (fun (val, base, gep?, storeProps) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      /- cast base (!llvm.ptr) -> register -/
      let baseCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[base] #[regType]
      /- cast value (i64/i32/i16/i8/ptr) -> register -/
      let valCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[val] #[regType]
      /- The store writes the low `width` bytes of the value register. -/
      let memProps ←
        addrMemProps riscvOp h (accessOp := .llvm .store) (·.volatile_) gep? storeProps
      let _ ← CreateProg.operation (.riscv riscvOp)
          #[valCastOp.res[0]!, baseCastOp.res[0]!] #[] memProps
      return ())
    (fun () => ⟨#[]⟩)

/--
  llvm.store -> riscv.sd (i64, ptr) / riscv.sw (i32) / riscv.sh (i16) / riscv.sb (i8).
  The patterns folding a constant `getelementptr` offset into the immediate come first.
-/
def store : Array (Puddle.CompiledPattern OpCode) :=
  #[AddrMode.gepIndex, .gepConst, .reg].flatMap fun mode =>
    #[lowerStore mode 1 .sb, lowerStore mode 2 .sh, lowerStore mode 4 .sw,
      lowerStore mode 8 .sd].map (·.compile)

/--
  Create the detached ops computing `pReg + iReg * scale`, returning them and the
  register holding the sum.
-/
def addScaledLocal (ctx : WfIRContext OpCode) (pReg iReg : ValuePtr) (scale : Nat) :
    Option (WfIRContext OpCode × Array OperationPtr × ValuePtr) := do
  match scale with
  | 1 =>
    /- ptr + idx -/
    let (ctx, addOp) ← createRISCVUnitLocal ctx .add rfl #[pReg, iReg]
    pure (ctx, #[addOp], addOp.getResult 0)
  | 2 =>
    /- (idx << 1) + ptr -/
    let (ctx, addOp) ← createRISCVUnitLocal ctx .sh1add rfl #[iReg, pReg]
    pure (ctx, #[addOp], addOp.getResult 0)
  | 4 =>
    /- (idx << 2) + ptr -/
    let (ctx, addOp) ← createRISCVUnitLocal ctx .sh2add rfl #[iReg, pReg]
    pure (ctx, #[addOp], addOp.getResult 0)
  | 8 =>
    /- (idx << 3) + ptr -/
    let (ctx, addOp) ← createRISCVUnitLocal ctx .sh3add rfl #[iReg, pReg]
    pure (ctx, #[addOp], addOp.getResult 0)
  | _ =>
    /- `0 < scale` excludes zero-sized element types, for which `Nat.log2 0 = 0` would give
       `ptr + idx`, and `Nat.log2 scale < 64` excludes shifts that do not fit the 6-bit
       immediate. Both take the `li`/`mul` form, which truncates modulo `2^64` exactly as the
       source does. -/
    if 0 < scale ∧ scale &&& (scale - 1) = 0 ∧ Nat.log2 scale < 64 then
      /- scale is a power of two: ptr + (idx << log2 scale) -/
      let (ctx, slliOp) ← createRISCVImmLocal ctx .slli rfl #[iReg] (Nat.log2 scale)
      let (ctx, addOp) ← createRISCVUnitLocal ctx .add rfl #[pReg, slliOp.getResult 0]
      pure (ctx, #[slliOp, addOp], addOp.getResult 0)
    else
      /- arbitrary scale: ptr + idx * scale -/
      let (ctx, liOp) ← createRISCVImmLocal ctx .li rfl #[] scale
      let (ctx, mulOp) ← createRISCVUnitLocal ctx .mul rfl #[iReg, liOp.getResult 0]
      let (ctx, addOp) ← createRISCVUnitLocal ctx .add rfl #[pReg, mulOp.getResult 0]
      pure (ctx, #[liOp, mulOp, addOp], addOp.getResult 0)

/--
  Lower a `llvm.getelementptr` to the address `gepOffsets` decomposes it into:
  the base, plus `idx * stride` for each dynamic index, plus a constant offset.
  Dynamic indices must have been normalized to `i64` by LLVM-to-GMIR.
-/
def getelementptr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (ptr, idxs, properties) := matchGetelementptrIndices op ctx.raw | return (ctx, none)
  let indices := GEPIndex.decode properties.rawConstantIndices.values idxs
  let some (offset, dynamic) := DataLayout.riscv64.gepOffsets properties.elem_type.val indices
    | return (ctx, none)
  for (idx, _) in dynamic do
    let .integerType itype := (idx.getType! ctx.raw).val | return (ctx, none)
    if itype.bitwidth ≠ 64 then return (ctx, none)
  let (ctx, pcastOp) ← castToRegLocal ctx ptr
  let mut ctx := ctx
  let mut ops := #[pcastOp]
  let mut addr : ValuePtr := pcastOp.getResult 0
  for (idx, stride) in dynamic do
    let (ctx', icastOp) ← castToRegLocal ctx idx
    ops := ops.push icastOp
    ctx := ctx'
    let (ctx', addOps, sum) ← addScaledLocal ctx addr (icastOp.getResult 0) stride
    ops := ops ++ addOps
    addr := sum
    ctx := ctx'
  if offset ≠ 0 then
    if -2048 ≤ offset ∧ offset ≤ 2047 then
      let (ctx', addiOp) ← createRISCVImmLocal ctx .addi rfl #[addr] offset
      ops := ops.push addiOp
      addr := addiOp.getResult 0
      ctx := ctx'
    else
      let (ctx', liOp) ← createRISCVImmLocal ctx .li rfl #[] offset
      let (ctx', addOp) ← createRISCVUnitLocal ctx' .add rfl #[addr, liOp.getResult 0]
      ops := ops ++ #[liOp, addOp]
      addr := addOp.getResult 0
      ctx := ctx'
  /- Cast the resulting register back to `!llvm.ptr`. -/
  let (ctx', castOp) ← replaceWithRegLocal ctx op addr
  some (ctx', some (ops.push castOp, #[castOp.getResult 0]))

/--
  Lower a `llvm.getelementptr` to the address `gepOffsets` decomposes it into
  (see `getelementptr_local`).
-/
def getelementptrGeneral (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite getelementptr_local rewriter op opInBounds

/-! ## Zbb min/max and rotate intrinsics

  These mirror the simple one-to-one patterns in LLVM's RISC-V backend
  (`RISCVInstrInfoZb.td`): `smin/smax/umin/umax` select to `MIN/MAX/MINU/MAXU`,
  and a funnel shift whose two data operands are identical is a rotate, which
  selects to `ROL`/`ROR`. The general (distinct-operand) funnel shift needs a
  multi-instruction expansion and is intentionally left unselected.
-/


/-- llvm.intr.fshl with identical data operands is a rotate-left: -> riscv.rol (riscv.rolw for i32).
    The general (distinct-operand) funnel shift is left unselected. -/
def fshl64 : Puddle.CompiledPattern OpCode := fshl64_pattern.compile

def fshl32 : Puddle.CompiledPattern OpCode := fshl32_pattern.compile

/-- llvm.intr.fshr with identical data operands is a rotate-right: -> riscv.ror (riscv.rorw for i32).
    The general (distinct-operand) funnel shift is left unselected. -/
def fshr64 : Puddle.CompiledPattern OpCode := fshr64_pattern.compile

def fshr32 : Puddle.CompiledPattern OpCode := fshr32_pattern.compile
/--
  `llvm.intr.fshl`/`llvm.intr.fshr` (`rotateLeft` set/unset) on `bw`-bit values with identical
  data operands and a constant shift amount is a constant rotate: -> `riscv.rori` (`riscv.roriw`
  for `i32`), mirroring `PatGprImm<rotr, RORI>`. There is no `roli`, so (like LLVM) a rotate-left
  lowers to `rori` with the negated immediate `(bw - amt) mod bw`.
-/
def lowerFshConst (rotateLeft : Bool) (bw : Nat) (throughTrunc : Bool := false) :
    Pattern OpCode :=
  Pattern.Builder
    (do
      let valType ← MatchProg.type (Attr := TypeAttr)
      let amtType ← MatchProg.type (Attr := IntegerType)
      let resType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = bw)
      let val ← MatchProg.value valType
      let amtOp ← MatchProg.operation (.gmir .g_constant) #[] #[amtType]
      /- Legalization widens a narrow constant to `g_trunc (g_constant i64)`. Truncation keeps
         the low bits, so the amount modulo `bw` is unchanged when read from the wide constant. -/
      let amt ← if throughTrunc then do
          let truncType ← MatchProg.type (Attr := IntegerType)
          let truncOp ← MatchProg.operation (.gmir .g_trunc) #[amtOp.res[0]!] #[truncType]
          pure truncOp.res[0]!
        else pure amtOp.res[0]!
      let _ ← MatchProg.root
          (.llvm (if rotateLeft then .intr__fshl else .intr__fshr))
          #[val, val, amt] #[resType]
      return (resType, val, amtType, amtOp.properties))
    (fun (resType, val, amtType, amtProps) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let valCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[val] #[regType]
      let imm := fun (type : TypeAttr) (props : GMIRConstantProperties) => do
        let .integerType t := type.val | none
        let amt := props.value
        /- The funnel-shift amount is taken modulo the bit width. -/
        let sh : Int := (((BitVec.ofInt t.bitwidth amt.value).toInt % bw) + bw) % bw
        /- rotate-left by `sh` = rotate-right by `bw - sh` (mod bw). -/
        let imm : Int := if rotateLeft then (bw - sh) % bw else sh
        some (RISCVImmediateProperties.mk (BitVec.ofInt 64 imm))
      let roriOp ← if bw = 32 then do
          let roriProps ← CreateProg.applyNative
              (Outputs := Handle OpCode (.prop (.riscv .roriw))) (amtType, amtProps)
              fun (type, props) => imm type props
          CreateProg.operation (.riscv .roriw)
              #[valCastOp.res[0]!] #[regType] roriProps
        else do
          let roriProps ← CreateProg.applyNative
              (Outputs := Handle OpCode (.prop (.riscv .rori))) (amtType, amtProps)
              fun (type, props) => imm type props
          CreateProg.operation (.riscv .rori)
              #[valCastOp.res[0]!] #[regType] roriProps
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[roriOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- llvm.intr.fshr with identical data operands and a constant shift amount is a
    constant rotate-right: -> riscv.rori (mirrors `PatGprImm<rotr, RORI>`). -/
def fshrConst64 : Puddle.CompiledPattern OpCode := (lowerFshConst false 64).compile

def fshrConst32 : Puddle.CompiledPattern OpCode := (lowerFshConst false 32).compile

def fshrConst32Trunc : Puddle.CompiledPattern OpCode := (lowerFshConst false 32 true).compile

/-- llvm.intr.fshl with identical data operands and a constant shift amount is a
    constant rotate-left. There is no `roli`, so (like LLVM) it lowers to
    `riscv.rori` with the negated immediate `(64 - amt) mod 64`. -/
def fshlConst64 : Puddle.CompiledPattern OpCode := (lowerFshConst true 64).compile

def fshlConst32 : Puddle.CompiledPattern OpCode := (lowerFshConst true 32).compile

def fshlConst32Trunc : Puddle.CompiledPattern OpCode := (lowerFshConst true 32 true).compile

/-! ## General (distinct-operand) funnel shift

  A funnel shift whose two data operands differ is a true funnel shift, not a
  rotate, so there is no single Zbb instruction for it. We mirror LLVM's generic
  `TargetLowering::expandFunnelShift` (`SelectionDAG/TargetLowering.cpp`), which
  is the path RV64 baseline takes since `FSHL`/`FSHR` are marked `Expand`. For a
  power-of-two bit width `w` and a variable shift amount `z` (the case a register
  operand always lands in), the expansion is

    fshl x y z = (x << (z % w)) | ((y >> 1) >> ((w-1) - (z % w)))
    fshr x y z = ((x << 1) << ((w-1) - (z % w))) | (y >> (z % w))

  The RISC-V shifts already reduce their amount modulo the register width, so
  `z % w` is just `z` and `(w-1) - (z % w)` is `~z` (both masked by the hardware).
  The `>> 1` / `<< 1` pre-shifts keep the `z % w = 0` case correct (they push the
  inverse shift to a full-width shift-out of zero). i32 uses the `w`-suffixed
  shifts; only the low `w` bits of the `or` matter, so their sign-extension is
  harmless.

  These run after the rotate/const-rotate matchers, so the identical-operand and
  constant-amount special cases still select the cheaper `rol`/`ror`/`rori`. -/

/-- General `llvm.intr.fshl x y z` -> `(x << z) | ((y >> 1) >> ~z)` (see the
    section comment), for `bw`-bit values. The i32 form uses the `w` shifts. -/
def lowerFshlGeneral (bw : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let xType ← MatchProg.type (Attr := TypeAttr)
      let yType ← MatchProg.type (Attr := TypeAttr)
      let zType ← MatchProg.type (Attr := TypeAttr)
      let resType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = bw)
      let x ← MatchProg.value xType
      let y ← MatchProg.value yType
      let z ← MatchProg.value zType
      let _ ← MatchProg.root (.llvm .intr__fshl) #[x, y, z] #[resType]
      return (resType, x, y, z))
    (fun (resType, x, y, z) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let xCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[x] #[regType]
      let yCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[y] #[regType]
      let zCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[z] #[regType]
      /- ~z, the inverse shift amount; the shift instruction masks it modulo `w`. -/
      let notzProps ← CreateProg.property (.riscv .xori)
          (RISCVImmediateProperties.mk (-1#64))
      let notzOp ← CreateProg.operation (.riscv .xori)
          #[zCastOp.res[0]!] #[regType] notzProps
      /- shx = x << z ; shy = (y >> 1) >> ~z ; result = shx | shy. The i32 form uses
         the `w` shifts (only the low 32 bits of the `or` are observed). -/
      let (shxOp, shyOp) ← if bw = 32 then do
          let shxProps ← CreateProg.property (.riscv .sllw) ()
          let shxOp ← CreateProg.operation (.riscv .sllw)
              #[xCastOp.res[0]!, zCastOp.res[0]!] #[regType] shxProps
          let y1Props ← CreateProg.property (.riscv .srliw) (RISCVImmediateProperties.mk 1#64)
          let y1Op ← CreateProg.operation (.riscv .srliw)
              #[yCastOp.res[0]!] #[regType] y1Props
          let shyProps ← CreateProg.property (.riscv .srlw) ()
          let shyOp ← CreateProg.operation (.riscv .srlw)
              #[y1Op.res[0]!, notzOp.res[0]!] #[regType] shyProps
          pure (shxOp, shyOp)
        else do
          let shxProps ← CreateProg.property (.riscv .sll) ()
          let shxOp ← CreateProg.operation (.riscv .sll)
              #[xCastOp.res[0]!, zCastOp.res[0]!] #[regType] shxProps
          let y1Props ← CreateProg.property (.riscv .srli) (RISCVImmediateProperties.mk 1#64)
          let y1Op ← CreateProg.operation (.riscv .srli)
              #[yCastOp.res[0]!] #[regType] y1Props
          let shyProps ← CreateProg.property (.riscv .srl) ()
          let shyOp ← CreateProg.operation (.riscv .srl)
              #[y1Op.res[0]!, notzOp.res[0]!] #[regType] shyProps
          pure (shxOp, shyOp)
      let orProps ← CreateProg.property (.riscv .or) ()
      let orOp ← CreateProg.operation (.riscv .or)
          #[shxOp.res[0]!, shyOp.res[0]!] #[regType] orProps
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[orOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- General `llvm.intr.fshl` (`i64`) -> shift/or expansion (see `lowerFshlGeneral`). -/
def fshlGeneral64 : Puddle.CompiledPattern OpCode := (lowerFshlGeneral 64).compile

/-- General `llvm.intr.fshl` (`i32`) -> shift/or expansion (see `lowerFshlGeneral`). -/
def fshlGeneral32 : Puddle.CompiledPattern OpCode := (lowerFshlGeneral 32).compile

/-- General `llvm.intr.fshr x y z` -> `((x << 1) << ~z) | (y >> z)` (see the
    section comment), for `bw`-bit values. The i32 form uses the `w` shifts. -/
def lowerFshrGeneral (bw : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let xType ← MatchProg.type (Attr := TypeAttr)
      let yType ← MatchProg.type (Attr := TypeAttr)
      let zType ← MatchProg.type (Attr := TypeAttr)
      let resType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = bw)
      let x ← MatchProg.value xType
      let y ← MatchProg.value yType
      let z ← MatchProg.value zType
      let _ ← MatchProg.root (.llvm .intr__fshr) #[x, y, z] #[resType]
      return (resType, x, y, z))
    (fun (resType, x, y, z) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let xCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[x] #[regType]
      let yCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[y] #[regType]
      let zCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[z] #[regType]
      /- ~z, the inverse shift amount; the shift instruction masks it modulo `w`. -/
      let notzProps ← CreateProg.property (.riscv .xori)
          (RISCVImmediateProperties.mk (-1#64))
      let notzOp ← CreateProg.operation (.riscv .xori)
          #[zCastOp.res[0]!] #[regType] notzProps
      /- shx = (x << 1) << ~z ; shy = y >> z ; result = shx | shy. The i32 form uses
         the `w` shifts (only the low 32 bits of the `or` are observed). -/
      let (shxOp, shyOp) ← if bw = 32 then do
          let x1Props ← CreateProg.property (.riscv .slliw) (RISCVImmediateProperties.mk 1#64)
          let x1Op ← CreateProg.operation (.riscv .slliw)
              #[xCastOp.res[0]!] #[regType] x1Props
          let shxProps ← CreateProg.property (.riscv .sllw) ()
          let shxOp ← CreateProg.operation (.riscv .sllw)
              #[x1Op.res[0]!, notzOp.res[0]!] #[regType] shxProps
          let shyProps ← CreateProg.property (.riscv .srlw) ()
          let shyOp ← CreateProg.operation (.riscv .srlw)
              #[yCastOp.res[0]!, zCastOp.res[0]!] #[regType] shyProps
          pure (shxOp, shyOp)
        else do
          let x1Props ← CreateProg.property (.riscv .slli) (RISCVImmediateProperties.mk 1#64)
          let x1Op ← CreateProg.operation (.riscv .slli)
              #[xCastOp.res[0]!] #[regType] x1Props
          let shxProps ← CreateProg.property (.riscv .sll) ()
          let shxOp ← CreateProg.operation (.riscv .sll)
              #[x1Op.res[0]!, notzOp.res[0]!] #[regType] shxProps
          let shyProps ← CreateProg.property (.riscv .srl) ()
          let shyOp ← CreateProg.operation (.riscv .srl)
              #[yCastOp.res[0]!, zCastOp.res[0]!] #[regType] shyProps
          pure (shxOp, shyOp)
      let orProps ← CreateProg.property (.riscv .or) ()
      let orOp ← CreateProg.operation (.riscv .or)
          #[shxOp.res[0]!, shyOp.res[0]!] #[regType] orProps
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[orOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- General `llvm.intr.fshr` (`i64`) -> shift/or expansion (see `lowerFshrGeneral`). -/
def fshrGeneral64 : Puddle.CompiledPattern OpCode := (lowerFshrGeneral 64).compile

/-- General `llvm.intr.fshr` (`i32`) -> shift/or expansion (see `lowerFshrGeneral`). -/
def fshrGeneral32 : Puddle.CompiledPattern OpCode := (lowerFshrGeneral 32).compile


/-- llvm.mlir.poison -> riscv.li 0 -/
def poisonConst_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let resType ← MatchProg.type (Attr := TypeAttr)
      let _ ← MatchProg.root (.llvm .mlir__poison) #[] #[resType]
      return resType)
    (fun resType => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let liProps ← CreateProg.property (.riscv .li) (RISCVImmediateProperties.mk 0#64)
      let liOp ← CreateProg.operation (.riscv .li) #[] #[regType] liProps
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[liOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- llvm.mlir.zero of an integer up to 64 bits or a pointer -> riscv.li 0 -/
def zeroConst_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let resType ← MatchProg.type (Attr := TypeAttr)
          (fun t => (icmpTypeWidth? t).any (· ≤ 64))
      let _ ← MatchProg.root (.llvm .mlir__zero) #[] #[resType]
      return resType)
    (fun resType => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let liProps ← CreateProg.property (.riscv .li) (RISCVImmediateProperties.mk 0#64)
      let liOp ← CreateProg.operation (.riscv .li) #[] #[regType] liProps
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[liOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- llvm.mlir.zero of an integer up to 64 bits or a pointer -> riscv.li 0 -/
def zeroConst : Puddle.CompiledPattern OpCode := zeroConst_pattern.compile

/-- llvm.mlir.poison -> riscv.li 0 -/
def poisonConst : Puddle.CompiledPattern OpCode := poisonConst_pattern.compile

/-- llvm.freeze arg : Int w ->
  unrealized_conversion_cast (unrealized_conversion_cast arg : Int w -> Reg) : Reg -> Int w -/
def freeze_pattern : Pattern OpCode :=
  lowerRegCast (.llvm .freeze) fun opType resType _ =>
    match opType.val, resType.val with
    | .integerType opType, .integerType resType =>
      (opType.bitwidth = 64 ∨ opType.bitwidth = 32) ∧ (resType.bitwidth = 64 ∨ resType.bitwidth = 32)
    | _, _ => false

/-- llvm.freeze arg : Int w ->
  unrealized_conversion_cast (unrealized_conversion_cast arg : Int w -> Reg) : Reg -> Int w -/
def freeze : Puddle.CompiledPattern OpCode := freeze_pattern.compile

/-! # Memory intrinsics -/

/-- A constant-length `memcpy`/`memset` is expanded inline only if it takes at most this
  many stores, as with LLVM's RISC-V `MaxStoresPerMemcpy`/`MaxStoresPerMemset`. -/
def memMaxStores : Nat := 8

/-- The `llvm.align` attribute of argument `i` of a memory intrinsic, or 1 if absent. -/
def memArgAlign (props : LLVMMemIntrinsicProperties) (i : Nat) : Nat := Id.run do
  let some attrs := props.arg_attrs | return 1
  let some (.dictionaryAttr dict) := attrs.value[i]? | return 1
  let some (_, .integerAttr align) := dict.entries.find? (·.1 = "llvm.align".toUTF8) | return 1
  return align.value.toNat

/-- The `(offset, width)` accesses covering `len` bytes, widest first, each at most 8 bytes
  wide and no wider than `align`. Since the widths are decreasing powers of two starting at
  offset 0, every access is naturally aligned. -/
def memAccesses (len align : Nat) : Array (Nat × Nat) := Id.run do
  let mut accesses := #[]
  let mut offset := 0
  for width in [8, 4, 2, 1] do
    if width ≤ align then
      for _ in [0:(len - offset) / width] do
        accesses := accesses.push (offset, width)
        offset := offset + width
  return accesses

/-- The accesses for an inline expansion, or none when the intrinsic needs a libcall. -/
def memIntrinsicAccesses? (ctx : IRContext OpCode) (isMemset : Bool)
    (props : LLVMMemIntrinsicProperties) (len : ValuePtr) : Option (Array (Nat × Nat)) := do
  let align := if isMemset then memArgAlign props 0
    else min (memArgAlign props 0) (memArgAlign props 1)
  let len ← matchGConstantIntVal len ctx
  guard (0 ≤ len ∧ len ≤ 8 * memMaxStores)
  let accesses := memAccesses len.toNat align
  guard (accesses.size ≤ memMaxStores)
  return accesses

/-- Lower a memcpy/memset that cannot be expanded inline to its C library call. -/
def memIntrinsicCallPattern (isMemset : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let dst ← MatchProg.value (← MatchProg.type (Attr := TypeAttr))
      let src ← MatchProg.value (← MatchProg.type (Attr := TypeAttr))
      let len ← MatchProg.value (← MatchProg.type (Attr := TypeAttr))
      let root ← MatchProg.root
          (.llvm (if isMemset then .intr__memset else .intr__memcpy)) #[dst, src, len] #[]
      let () ← MatchProg.inspectOperation (Outputs := Unit) root.op fun ctx op => do
        let props : LLVMMemIntrinsicProperties :=
          if isMemset then op.getProperties! ctx Llvm.intr__memset
          else op.getProperties! ctx Llvm.intr__memcpy
        guard (memIntrinsicAccesses? ctx isMemset props (op.getOperand! ctx 2)).isNone
      return (dst, src, len))
    (fun (dst, src, len) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let dstCast ← CreateProg.operation (.builtin .unrealized_conversion_cast) #[dst] #[regType]
      let srcCast ← CreateProg.operation (.builtin .unrealized_conversion_cast) #[src] #[regType]
      -- memset takes its fill byte as an int, so zero-extend the i8.
      let srcReg ← if isMemset then do
          let ext ← CreateProg.operation (.riscv .zextb) #[srcCast.res[0]!] #[regType]
          pure ext.res[0]!
        else pure srcCast.res[0]!
      let lenCast ← CreateProg.operation (.builtin .unrealized_conversion_cast) #[len] #[regType]
      let callee : FlatSymbolRefAttr := ⟨if isMemset then "@memset" else "@memcpy"⟩
      CreateProg.operation (.riscv_cf .call) #[dstCast.res[0]!, srcReg, lenCast.res[0]!] #[]
        (.inl (RISCVCallProperties.mk (some callee))))
    (fun call => call)

def memIntrinsicCalls : Array (CompiledPattern OpCode) :=
  #[memIntrinsicCallPattern false, memIntrinsicCallPattern true].map (·.compile)

/-- Expand a constant-length memcpy/memset into at most memMaxStores aligned accesses. -/
def memIntrinsicInline_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let isMemset := op.getOpType! ctx.raw = Llvm.intr__memset
  if !isMemset && op.getOpType! ctx.raw ≠ Llvm.intr__memcpy then return (ctx, none)
  let props : LLVMMemIntrinsicProperties :=
    if isMemset then op.getProperties! ctx.raw Llvm.intr__memset
    else op.getProperties! ctx.raw Llvm.intr__memcpy
  let operands := op.getOperands! ctx.raw
  /- src is the source pointer of a memcpy and the fill byte of a memset. -/
  let (dst, src, len) := (operands[0]!, operands[1]!, operands[2]!)
  let some accesses := memIntrinsicAccesses? ctx.raw isMemset props len | return (ctx, none)
  let (ctx, dstCast) ← castToRegLocal ctx dst
  let dstReg := dstCast.getResult 0
  let mut ctx := ctx
  let mut ops := #[dstCast]
  /- The source register of a `memcpy`; the value to store for a `memset`. Narrower stores
     take the low bits of the 64-bit splat of the fill byte. -/
  let mut srcReg := dstReg
  if isMemset && !accesses.all (·.2 = 1) then
    match matchGConstantIntVal src ctx.raw with
    | some c =>
      let (ctx', li) ← createRISCVImmLocal ctx .li rfl #[] ((c % 256) * 0x0101010101010101)
      ctx := ctx'; ops := ops.push li; srcReg := li.getResult 0
    | none =>
      let (ctx', srcCast) ← castToRegLocal ctx src
      let (ctx', ext) ← createRISCVUnitLocal ctx' .zextb rfl #[srcCast.getResult 0]
      let (ctx', ones) ← createRISCVImmLocal ctx' .li rfl #[] 0x0101010101010101
      let (ctx', splat) ← createRISCVUnitLocal ctx' .mul rfl
          #[ext.getResult 0, ones.getResult 0]
      ctx := ctx'; ops := ops ++ #[srcCast, ext, ones, splat]; srcReg := splat.getResult 0
  else
    let (ctx', srcCast) ← castToRegLocal ctx src
    ctx := ctx'; ops := ops.push srcCast; srcReg := srcCast.getResult 0
  for (offset, width) in accesses do
    let memProps := RISCVMemProperties.mk (BitVec.ofNat 64 offset) props.isVolatile
    let mut val := srcReg
    if !isMemset then
      let (ctx', ld) ← createLoadLocal ctx width srcReg memProps
      ctx := ctx'; ops := ops.push ld; val := ld.getResult 0
    let (ctx', st) ← createStoreLocal ctx width val dstReg memProps
    ctx := ctx'; ops := ops.push st
  return (ctx, some (ops, #[]))

/-- llvm.intr.memcpy / llvm.intr.memset -> loads and stores, or a libcall. -/
def memIntrinsic : RewritePattern OpCode :=
  .GreedyRewritePattern <| memIntrinsicCalls.map (·.run) ++
    #[.fromLocalRewrite memIntrinsicInline_local]

/--
An integer of 3, 5, 6 or 7 bytes fits no single `l*`/`s*` instruction, so it is accessed in
power-of-two pieces, as in LLVM's `LegalizerHelper::lowerLoad`/`lowerStore`.
-/

/-- The `(offset, width)` pieces of a load or store of a value of `type`, if it needs splitting. -/
def splitAccesses? (type : TypeAttr) : Option (Array (Nat × Nat)) := do
  let .integerType t := type.val | none
  guard (t.bitwidth % 8 = 0 ∧ t.bitwidth / 8 ∈ [3, 5, 6, 7])
  return memAccesses (t.bitwidth / 8) 8

/-- `riscv.lbu` / `riscv.lhu` / `riscv.lwu`, for a `width`-byte zero-extending load. -/
def createZextLoadLocal (ctx : WfIRContext OpCode) (width : Nat) (addr : ValuePtr)
    (props : RISCVMemProperties) : Option (WfIRContext OpCode × OperationPtr) :=
  match width with
  | 1 => WfRewriter.createOp! ctx Riscv.lbu #[RegisterType.mk] #[addr] #[] #[] props none
  | 2 => WfRewriter.createOp! ctx Riscv.lhu #[RegisterType.mk] #[addr] #[] #[] props none
  | _ => WfRewriter.createOp! ctx Riscv.lwu #[RegisterType.mk] #[addr] #[] #[] props none

/-- llvm.load -> zero-extending loads of the pieces, shifted into place and or-ed together. -/
def splitLoad_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  if op.getOpType! ctx.raw ≠ Llvm.load then return (ctx, none)
  let some accesses := splitAccesses? ((op.getResult 0).getType! ctx.raw) | return (ctx, none)
  let props : LoadProperties := op.getProperties! ctx.raw Llvm.load
  let (ctx, addrCast) ← castToRegLocal ctx (op.getOperand! ctx.raw 0)
  let addr := addrCast.getResult 0
  let mut ctx := ctx
  let mut ops := #[addrCast]
  /- Replaced by the piece at offset 0, which comes first. -/
  let mut result := addr
  for (offset, width) in accesses do
    let memProps := RISCVMemProperties.mk (BitVec.ofNat 64 offset) props.volatile_
    let (ctx', ld) ← createZextLoadLocal ctx width addr memProps
    ctx := ctx'; ops := ops.push ld
    if offset = 0 then
      result := ld.getResult 0
    else
      let (ctx', shifted) ← createRISCVImmLocal ctx .slli rfl #[ld.getResult 0] (8 * offset)
      let (ctx', merged) ← createRISCVUnitLocal ctx' .or rfl #[result, shifted.getResult 0]
      ctx := ctx'; ops := ops ++ #[shifted, merged]; result := merged.getResult 0
  let (ctx', castBack) ← replaceWithRegLocal ctx op result
  return (ctx', some (ops.push castBack, #[castBack.getResult 0]))

/-- llvm.store -> a store of each piece, shifted down to the low bits of a register. -/
def splitStore_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  if op.getOpType! ctx.raw ≠ Llvm.store then return (ctx, none)
  let operands := op.getOperands! ctx.raw
  let some accesses := splitAccesses? (operands[0]!.getType! ctx.raw) | return (ctx, none)
  let props : StoreProperties := op.getProperties! ctx.raw Llvm.store
  let (ctx, valCast) ← castToRegLocal ctx operands[0]!
  let (ctx, addrCast) ← castToRegLocal ctx operands[1]!
  let addr := addrCast.getResult 0
  let mut ctx := ctx
  let mut ops := #[valCast, addrCast]
  for (offset, width) in accesses do
    let mut piece := valCast.getResult 0
    if offset ≠ 0 then
      let (ctx', shifted) ← createRISCVImmLocal ctx .srli rfl #[piece] (8 * offset)
      ctx := ctx'; ops := ops.push shifted; piece := shifted.getResult 0
    let memProps := RISCVMemProperties.mk (BitVec.ofNat 64 offset) props.volatile_
    let (ctx', st) ← createStoreLocal ctx width piece addr memProps
    ctx := ctx'; ops := ops.push st
  return (ctx, some (ops, #[]))

/-! # gMIR Lowering Patterns

  The gMIR patterns only select operations that `riscv64LegalizerInfo` considers legal, since
  LLVM's instruction selector only sees legalized gMIR.
-/

/--
  Matches only if an `opcode` operation whose type groups all have type `type`, with `properties`,
  is legal. Opcodes with a second type index of another type (e.g. `g_icmp`'s operand type) pass it
  as `type₁`.
-/
def matchLegal (opcode : GMIR) (type : Handle OpCode .type)
    (properties : Handle OpCode (.prop (.gmir opcode)))
    (type₁ : Option (Handle OpCode .type) := none) : MatchProg.Builder Unit :=
  match type₁ with
  | none =>
    MatchProg.matchNative (type, properties) fun (type, properties) =>
      riscv64LegalizerInfo.isLegal opcode (.replicate opcode.numTypeGroups type) properties
  | some type₁ =>
    MatchProg.matchNative (type, type₁, properties) fun (type, type₁, properties) =>
      riscv64LegalizerInfo.isLegal opcode #[type, type₁] properties

/-! ## Zicond branchless `g_select` lowering

  The Zicond extension lowers `gmir.g_select` branchlessly, mirroring LLVM's SelectionDAG
  lowering of `ISD::SELECT` when `Zicond` is available (LLVM's GlobalISel selects `G_SELECT` with
  a branch instead):
  ```
    (select c, t, 0) -> (czero.eqz t, c)
    (select c, 0, f) -> (czero.nez f, c)
    (select c, t, f) -> (or (czero.eqz t, c), (czero.nez f, c))
  ```
  A legal `g_select` selects `i64` values with an `i64` condition, which is true when it is
  nonzero, as `czero.eqz` and `czero.nez` test it. The zero-arm patterns inspect the `g_constant`,
  so they run in the early loop, before `gmirConstant` lowers it.
-/

/--
  `gmir.g_select c t 0` -> `riscv.czeroeqz t c` when `zeroFalse` is set, and
  `gmir.g_select c 0 f` -> `riscv.czeronez f c` otherwise.
-/
def gmirSelectZero_pattern (zeroFalse : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let condType ← MatchProg.type (Attr := IntegerType)
      let cond ← MatchProg.value condType
      let val ← MatchProg.value type
      let zeroOp ← MatchProg.operation (.gmir .g_constant) #[] #[type]
      MatchProg.matchNative zeroOp.properties isGMIRConstantZero
      let operands :=
        if zeroFalse then #[cond, val, zeroOp.res[0]!] else #[cond, zeroOp.res[0]!, val]
      let root ← MatchProg.root (.gmir .g_select) operands #[type]
      matchLegal .g_select type root.properties (type₁ := condType)
      return (type, cond, val))
    (fun (type, cond, val) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let valCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[val] #[regType]
      let condCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[cond] #[regType]
      let czOp ← if zeroFalse then do
          let czProps ← CreateProg.property (.riscv .czeroeqz) ()
          CreateProg.operation (.riscv .czeroeqz)
            #[valCastOp.res[0]!, condCastOp.res[0]!] #[regType] czProps
        else do
          let czProps ← CreateProg.property (.riscv .czeronez) ()
          CreateProg.operation (.riscv .czeronez)
            #[valCastOp.res[0]!, condCastOp.res[0]!] #[regType] czProps
      CreateProg.operation (.builtin .unrealized_conversion_cast) #[czOp.res[0]!] #[type])
    (fun castBackOp => castBackOp)

/-- The zero-arm `gmir.g_select` patterns (see `gmirSelectZero_pattern`). -/
def gmirSelectZero : Array (Puddle.CompiledPattern OpCode) :=
  #[true, false].map (gmirSelectZero_pattern · |>.compile)

/--
  General branchless select:
  `gmir.g_select c t f` -> `or (czero.eqz t c) (czero.nez f c)`.
-/
def gmirSelect_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let condType ← MatchProg.type (Attr := IntegerType)
      let cond ← MatchProg.value condType
      let tval ← MatchProg.value type
      let fval ← MatchProg.value type
      let root ← MatchProg.root (.gmir .g_select) #[cond, tval, fval] #[type]
      matchLegal .g_select type root.properties (type₁ := condType)
      return (type, cond, tval, fval))
    (fun (type, cond, tval, fval) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let tCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[tval] #[regType]
      let fCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[fval] #[regType]
      let condCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[cond] #[regType]
      let eqzProps ← CreateProg.property (.riscv .czeroeqz) ()
      let eqzOp ← CreateProg.operation (.riscv .czeroeqz)
          #[tCastOp.res[0]!, condCastOp.res[0]!] #[regType] eqzProps
      let nezProps ← CreateProg.property (.riscv .czeronez) ()
      let nezOp ← CreateProg.operation (.riscv .czeronez)
          #[fCastOp.res[0]!, condCastOp.res[0]!] #[regType] nezProps
      let orProps ← CreateProg.property (.riscv .or) ()
      let orOp ← CreateProg.operation (.riscv .or)
          #[eqzOp.res[0]!, nezOp.res[0]!] #[regType] orProps
      CreateProg.operation (.builtin .unrealized_conversion_cast) #[orOp.res[0]!] #[type])
    (fun castBackOp => castBackOp)

def gmirSelect : Puddle.CompiledPattern OpCode := gmirSelect_pattern.compile

/-- `gmir.g_add` (`i64`) -> `riscv.add`. -/
def gmirAdd_pattern : Pattern OpCode :=
  lowerBinary (.gmir .g_add) (·.bitwidth = 64) .add () (guard := matchLegal .g_add)

/-- `gmir.g_sub` (`i64`) -> `riscv.sub`. -/
def gmirSub_pattern : Pattern OpCode :=
  lowerBinary (.gmir .g_sub) (·.bitwidth = 64) .sub () (guard := matchLegal .g_sub)

/-- `gmir.g_shl` (`i64`) -> `riscv.sll`. -/
def gmirShl_pattern : Pattern OpCode :=
  lowerBinary (.gmir .g_shl) (·.bitwidth = 64) .sll () (guard := matchLegal .g_shl)

/-- `gmir.g_lshr` (`i64`) -> `riscv.srl`. -/
def gmirLshr_pattern : Pattern OpCode :=
  lowerBinary (.gmir .g_lshr) (·.bitwidth = 64) .srl () (guard := matchLegal .g_lshr)

/-- `gmir.g_ashr` (`i64`) -> `riscv.sra`. -/
def gmirAshr_pattern : Pattern OpCode :=
  lowerBinary (.gmir .g_ashr) (·.bitwidth = 64) .sra () (guard := matchLegal .g_ashr)

/-- `gmir.g_trunc` -> a cast through `!riscv.reg`, since LLVM selects it as a copy. -/
def gmirTrunc_pattern : Pattern OpCode :=
  lowerRegCast (.gmir .g_trunc) fun opType resType properties =>
    riscv64LegalizerInfo.isLegal .g_trunc #[resType, opType] properties

/-- `gmir.g_anyext` -> a cast through `!riscv.reg`, since LLVM selects it as a copy. -/
def gmirAnyext_pattern : Pattern OpCode :=
  lowerRegCast (.gmir .g_anyext) fun opType resType properties =>
    riscv64LegalizerInfo.isLegal .g_anyext #[resType, opType] properties

/--
  `gmir.g_anyext` of a cast from `!riscv.reg` -> a cast of that register to the result type.
  `g_anyext` leaves the high bits unspecified, so they may be the register's own high bits: this
  avoids the `!riscv.reg -> iN -> !riscv.reg` round trip of `gmirAnyext`, which reconciles to a
  zero-extension (see `anyext_of_reg_refinement`).
-/
def gmirAnyextOfReg_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let regType ← MatchProg.type (Attr := RegisterType)
      let r ← MatchProg.value regType
      let opType ← MatchProg.type (Attr := TypeAttr)
      let castOp ← MatchProg.operation (.builtin .unrealized_conversion_cast) #[r] #[opType]
      let resType ← MatchProg.type (Attr := TypeAttr)
      let root ← MatchProg.root (.gmir .g_anyext) #[castOp.res[0]!] #[resType]
      MatchProg.matchNative (opType, resType, root.properties)
          fun (opType, resType, props) =>
            riscv64LegalizerInfo.isLegal .g_anyext #[resType, opType] props
      return (r, resType))
    (fun (r, resType) =>
      CreateProg.operation (.builtin .unrealized_conversion_cast) #[r] #[resType])
    (fun castOp => castOp)

def gmirAdd : Puddle.CompiledPattern OpCode := gmirAdd_pattern.compile
def gmirSub : Puddle.CompiledPattern OpCode := gmirSub_pattern.compile
def gmirTrunc : Puddle.CompiledPattern OpCode := gmirTrunc_pattern.compile
def gmirAnyext : Puddle.CompiledPattern OpCode := gmirAnyext_pattern.compile
def gmirAnyextOfReg : Puddle.CompiledPattern OpCode := gmirAnyextOfReg_pattern.compile
def gmirShl : Puddle.CompiledPattern OpCode := gmirShl_pattern.compile
def gmirLshr : Puddle.CompiledPattern OpCode := gmirLshr_pattern.compile
def gmirAshr : Puddle.CompiledPattern OpCode := gmirAshr_pattern.compile

/--
  RISC-V lowerings with Puddle for the integer-extension operations (`sext`/`zext`): match a
  single-operand extension op whose operand has a fixed legal integer width `opBw` (`16` or `32`)
  and whose result is a strictly wider integer type of width at most 64 (a 64-bit register cannot
  represent wider results, so e.g. `sext i16 to i128` is left unselected; unlike `opBw`, the result
  width is matched generically rather than enumerated), cast the operand to a register, apply the
  halfword/word extension op matching `opBw`, and cast the result back to the (generically-matched)
  result type. Only extensions that `riscv64LegalizerInfo` considers legal are selected.
-/
def lowerExt (srcOp : GMIR) (opBw : Nat) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp)) : Pattern OpCode :=
  lowerUnary (.gmir srcOp) opBw riscvOp riscvProps fun opType resType properties => do
    -- A 64-bit register cannot hold a wider result.
    MatchProg.matchNative resType fun t => (t.val.bitwidthOfType).any (· ≤ 64)
    matchLegal srcOp resType properties (type₁ := opType)

/-- `gmir.g_sext` (`i16` operand) -> `riscv.sexth`. -/
def sext16_pattern : Pattern OpCode := lowerExt .g_sext 16 .sexth ()

/-- `gmir.g_sext` (`i32` operand) -> `riscv.sextw`. -/
def sext32_pattern : Pattern OpCode := lowerExt .g_sext 32 .sextw ()

/--
  `gmir.g_sext_inreg` (`i64`) -> `riscv.sextb` / `riscv.sexth` / `riscv.sextw` for `sz` of
  `8`, `16`, or `32`, and otherwise `riscv.slli` + `riscv.srai`, shifting bit `sz - 1` to bit 63
  and back arithmetically, as LLVM's RISC-V `sext_inreg` patterns do.

  Matches a legal `i64` `gmir.g_sext_inreg` whose `sz` satisfies `szMatches`, returning its result
  type, operand and properties.
-/
def matchSextInReg (szMatches : Nat → Bool) :
    MatchProg.Builder (Handle OpCode .type × Handle OpCode .value ×
      Handle OpCode (.prop (.gmir .g_sext_inreg))) := do
  let srcType ← MatchProg.type (Attr := TypeAttr)
  let resType ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 64)
  let src ← MatchProg.value srcType
  let root ← MatchProg.root (.gmir .g_sext_inreg) #[src] #[resType]
      fun props => szMatches props.sz.toNat
  matchLegal .g_sext_inreg resType root.properties
  return (resType, src, root.properties)

/-- `gmir.g_sext_inreg` (`i64`) with `sz` of `sz` -> `riscvOp` (`riscv.sextb` / `riscv.sexth` /
  `riscv.sextw`). -/
def sextInRegExt_pattern (sz : Nat) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp)) : Pattern OpCode :=
  Pattern.Builder
    (matchSextInReg (· = sz))
    (fun (resType, src, _) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let castOp ← CreateProg.operation (.builtin .unrealized_conversion_cast) #[src] #[regType]
      let extOp ← CreateProg.operation (.riscv riscvOp) #[castOp.res[0]!] #[regType] riscvProps
      CreateProg.operation (.builtin .unrealized_conversion_cast) #[extOp.res[0]!] #[resType])
    (fun castBackOp => castBackOp)

/-- `gmir.g_sext_inreg` (`i64`) with any other `sz` -> `riscv.slli` + `riscv.srai` by `64 - sz`. -/
def sextInRegShift_pattern : Pattern OpCode :=
  Pattern.Builder
    (matchSextInReg fun sz => sz ≠ 8 && sz ≠ 16 && sz ≠ 32)
    (fun (resType, src, props) => do
      let shiftProps (props : SextInRegProperties) : RISCVImmediateProperties :=
        let sz := props.sz.toNat
        let shift : Int := 64 - sz
        mkRISCVImm shift
      let regType ← CreateProg.type (RegisterType.mk none)
      let castOp ← CreateProg.operation (.builtin .unrealized_conversion_cast) #[src] #[regType]
      let leftProps ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.riscv .slli)))
          props fun props => some (shiftProps props)
      let left ← CreateProg.operation (.riscv .slli) #[castOp.res[0]!] #[regType] (.inr leftProps)
      let rightProps ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.riscv .srai)))
          props fun props => some (shiftProps props)
      let right ← CreateProg.operation (.riscv .srai) #[left.res[0]!] #[regType] (.inr rightProps)
      CreateProg.operation (.builtin .unrealized_conversion_cast) #[right.res[0]!] #[resType])
    (fun castBackOp => castBackOp)

def sextInReg8 : Puddle.CompiledPattern OpCode := (sextInRegExt_pattern 8 .sextb ()).compile
def sextInReg16 : Puddle.CompiledPattern OpCode := (sextInRegExt_pattern 16 .sexth ()).compile
def sextInReg32 : Puddle.CompiledPattern OpCode := (sextInRegExt_pattern 32 .sextw ()).compile
def sextInRegShift : Puddle.CompiledPattern OpCode := sextInRegShift_pattern.compile

/-- `gmir.g_zext` (`i16` operand) -> `riscv.zexth`. -/
def zext16_pattern : Pattern OpCode := lowerExt .g_zext 16 .zexth ()

/-- `gmir.g_zext` (`i32` operand) -> `riscv.zextw`. -/
def zext32_pattern : Pattern OpCode := lowerExt .g_zext 32 .zextw ()

/--
  gmir.g_sext %x `i16` to `i64` -> riscv.sexth %x
  gmir.g_sext %x `i16` to `i32` -> riscv.sexth %x
  gmir.g_sext %x `i32` to `i64` -> riscv.sextw %x
-/
def sext16 : Puddle.CompiledPattern OpCode := sext16_pattern.compile

def sext32 : Puddle.CompiledPattern OpCode := sext32_pattern.compile

/--
  gmir.g_zext %x `i16` to `i64` -> riscv.zexth %x
  gmir.g_zext %x `i16` to `i32` -> riscv.zexth %x
  gmir.g_zext %x `i32` to `i64` -> riscv.zextw %x
-/
def zext16 : Puddle.CompiledPattern OpCode := zext16_pattern.compile

def zext32 : Puddle.CompiledPattern OpCode := zext32_pattern.compile

/-- `gmir.g_and` (`i64`) -> `riscv.and`. -/
def gmirAnd_pattern : Pattern OpCode :=
  lowerBinary (.gmir .g_and) (·.bitwidth = 64) .and () (guard := matchLegal .g_and)

/-- `gmir.g_or` (`i64`) -> `riscv.or`. -/
def gmirOr_pattern : Pattern OpCode :=
  lowerBinary (.gmir .g_or) (·.bitwidth = 64) .or () (guard := matchLegal .g_or)

/-- `gmir.g_xor` (`i64`) -> `riscv.xor`. -/
def gmirXor_pattern : Pattern OpCode :=
  lowerBinary (.gmir .g_xor) (·.bitwidth = 64) .xor () (guard := matchLegal .g_xor)

def gmirAnd : Puddle.CompiledPattern OpCode := gmirAnd_pattern.compile
def gmirOr : Puddle.CompiledPattern OpCode := gmirOr_pattern.compile
def gmirXor : Puddle.CompiledPattern OpCode := gmirXor_pattern.compile

/-- Cast `operands` to registers, apply `riscvOp`, and cast its result back to `type`. -/
def createRegOp (type : Handle OpCode .type) (operands : Array (Handle OpCode .value))
    (riscvOp : Riscv) (props : PropertiesOrHandle (OpCode.riscv riscvOp)) :
    CreateProg.Builder CreatedOpHandle := do
  let regType ← CreateProg.type (RegisterType.mk none)
  let castOps ← operands.mapM fun operand =>
    CreateProg.operation (.builtin .unrealized_conversion_cast) #[operand] #[regType]
  let riscvOp ← CreateProg.operation (.riscv riscvOp) (castOps.map (·.res[0]!)) #[regType] props
  CreateProg.operation (.builtin .unrealized_conversion_cast) #[riscvOp.res[0]!] #[type]

/--
  `srcOp` (`i64`) whose rhs is a `gmir.g_constant` in `[lo, hi]` -> the immediate form `riscvOp`.
  Mirrors `PatGprImm`. The constant is only matched on the rhs, where the post-legalizer combiner
  places it. `guard` adds conditions on the matched type and on the properties of `srcOp`.

  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfo.td#L1467-L1477
-/
def lowerBinaryImm (srcOp : OpCode) (riscvOp : Riscv)
    (h : Riscv.propertiesOf riscvOp = RISCVImmediateProperties) (lo hi : Int)
    (guard : Handle OpCode .type → Handle OpCode (.prop srcOp) → MatchProg.Builder Unit :=
      fun _ _ => pure ()) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 64)
      let lhs ← MatchProg.value type
      let constant ← MatchProg.operation (.gmir .g_constant) #[] #[type]
      let root ← MatchProg.root srcOp #[lhs, constant.res[0]!] #[type]
      guard type root.properties
      MatchProg.matchNative constant.properties fun ⟨const⟩ =>
        let imm := (BitVec.ofInt 64 const.value).toInt
        lo ≤ imm && imm ≤ hi
      return (type, lhs, constant.properties))
    (fun (type, lhs, constProps) => do
      let immProps ← CreateProg.applyNative
          (Outputs := Handle OpCode (.prop (.riscv riscvOp))) constProps fun ⟨const⟩ =>
        some (cast h.symm (mkRISCVImm const.value))
      createRegOp type #[lhs] riscvOp (.inr immProps))
    (fun castBackOp => castBackOp)

/-- `gmir.g_add` (`i64`) with a simm12 constant rhs -> `riscv.addi`. -/
def gmirAddi_pattern : Pattern OpCode :=
  lowerBinaryImm (.gmir .g_add) .addi rfl (-2048) 2047 (guard := matchLegal .g_add)

/-- `gmir.g_and` (`i64`) with a simm12 constant rhs -> `riscv.andi`. -/
def gmirAndi_pattern : Pattern OpCode :=
  lowerBinaryImm (.gmir .g_and) .andi rfl (-2048) 2047 (guard := matchLegal .g_and)

/-- `gmir.g_or` (`i64`) with a simm12 constant rhs -> `riscv.ori`. -/
def gmirOri_pattern : Pattern OpCode :=
  lowerBinaryImm (.gmir .g_or) .ori rfl (-2048) 2047 (guard := matchLegal .g_or)

/-- `gmir.g_xor` (`i64`) with a simm12 constant rhs -> `riscv.xori`. -/
def gmirXori_pattern : Pattern OpCode :=
  lowerBinaryImm (.gmir .g_xor) .xori rfl (-2048) 2047 (guard := matchLegal .g_xor)

/-- `gmir.g_shl` (`i64`) with a uimm6 constant rhs -> `riscv.slli`. -/
def gmirSlli_pattern : Pattern OpCode :=
  lowerBinaryImm (.gmir .g_shl) .slli rfl 0 63 (guard := matchLegal .g_shl)

/-- `gmir.g_lshr` (`i64`) with a uimm6 constant rhs -> `riscv.srli`. -/
def gmirSrli_pattern : Pattern OpCode :=
  lowerBinaryImm (.gmir .g_lshr) .srli rfl 0 63 (guard := matchLegal .g_lshr)

/-- `gmir.g_ashr` (`i64`) with a uimm6 constant rhs -> `riscv.srai`. -/
def gmirSrai_pattern : Pattern OpCode :=
  lowerBinaryImm (.gmir .g_ashr) .srai rfl 0 63 (guard := matchLegal .g_ashr)

/-- `gmir_riscv.g_addw` (`i64`) with a simm12 constant rhs -> `riscv.addiw`. -/
def gmirRiscvAddiw_pattern : Pattern OpCode :=
  lowerBinaryImm (.gmir_riscv .g_addw) .addiw rfl (-2048) 2047

/-- `gmir_riscv.g_sllw` (`i64`) with a uimm5 constant rhs -> `riscv.slliw`. -/
def gmirRiscvSlliw_pattern : Pattern OpCode :=
  lowerBinaryImm (.gmir_riscv .g_sllw) .slliw rfl 0 31

/-- `gmir_riscv.g_srlw` (`i64`) with a uimm5 constant rhs -> `riscv.srliw`. -/
def gmirRiscvSrliw_pattern : Pattern OpCode :=
  lowerBinaryImm (.gmir_riscv .g_srlw) .srliw rfl 0 31

/-- `gmir_riscv.g_sraw` (`i64`) with a uimm5 constant rhs -> `riscv.sraiw`. -/
def gmirRiscvSraiw_pattern : Pattern OpCode :=
  lowerBinaryImm (.gmir_riscv .g_sraw) .sraiw rfl 0 31

def gmirAddi : Puddle.CompiledPattern OpCode := gmirAddi_pattern.compile
def gmirAndi : Puddle.CompiledPattern OpCode := gmirAndi_pattern.compile
def gmirOri : Puddle.CompiledPattern OpCode := gmirOri_pattern.compile
def gmirXori : Puddle.CompiledPattern OpCode := gmirXori_pattern.compile
def gmirSlli : Puddle.CompiledPattern OpCode := gmirSlli_pattern.compile
def gmirSrli : Puddle.CompiledPattern OpCode := gmirSrli_pattern.compile
def gmirSrai : Puddle.CompiledPattern OpCode := gmirSrai_pattern.compile
def gmirRiscvAddiw : Puddle.CompiledPattern OpCode := gmirRiscvAddiw_pattern.compile
def gmirRiscvSlliw : Puddle.CompiledPattern OpCode := gmirRiscvSlliw_pattern.compile
def gmirRiscvSrliw : Puddle.CompiledPattern OpCode := gmirRiscvSrliw_pattern.compile
def gmirRiscvSraiw : Puddle.CompiledPattern OpCode := gmirRiscvSraiw_pattern.compile

/-! ## Zbs single-bit immediate selection

  These mirror the Zbs mask patterns in `RISCVInstrInfoZb.td`: `bseti`/`binvi`/`bclri`
  recognize an `or`/`xor`/`and` against a constant whose (complemented, for `bclri`)
  value is a single set bit, and emit the bit *index*. The `!isInt<12>` guard matches
  the `SingleBitSetMask`/`BCLRMask` `ImmLeaf` predicates, so the plain `andi`/`ori`/`xori`
  forms win whenever the immediate already fits a signed 12-bit field.

  `BCLRMask`/`SingleBitSetMask` predicates:
  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L69-L80
  `bclri`/`bseti`/`binvi` select patterns:
  https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L529-L534
-/

/-- The index of the single set bit of `x`, or `none` when `x` is zero or has more
    than one bit set (`u &&& (u - 1)` clears the lowest set bit; if that leaves `0`,
    there was at most one). Used for Zbs single-bit immediate selection. -/
def singleSetBit (x : BitVec 64) : Option Int :=
  let u := x.toNat
  if u == 0 || (u &&& (u - 1)) != 0 then none else some (Nat.log2 u)

/-- The bit index that `gmirSingleBit_pattern` emits for the constant `c`, if any. -/
def singleBitImm? (complement : Bool) (c : Int) : Option Int :=
  let imm := (BitVec.ofInt 64 c).toInt
  /- ANDI/ORI/XORI handle the simm12 cases; only fire when the immediate doesn't fit. -/
  if !(imm < -2048 || imm > 2047) then none
  else
    let bv := BitVec.ofInt 64 imm
    singleSetBit (if complement then ~~~ bv else bv)

/--
  Single-bit immediate selection. `complement = false` for `bseti`/`binvi` (the
  immediate itself is a single set bit); `complement = true` for `bclri` (the
  *complement* of the immediate is a single set bit). The emitted immediate is the
  bit index. Only fires when the immediate does not fit a signed 12-bit field.
-/
def gmirSingleBit_pattern (opcode : GMIR) (riscvOp : Riscv)
    (h : Riscv.propertiesOf riscvOp = RISCVImmediateProperties) (complement : Bool) :
    Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 64)
      let lhs ← MatchProg.value type
      let constant ← MatchProg.operation (.gmir .g_constant) #[] #[type]
          fun ⟨const⟩ => (singleBitImm? complement const.value).isSome
      let root ← MatchProg.root (.gmir opcode) #[lhs, constant.res[0]!] #[type]
      matchLegal opcode type root.properties
      return (type, lhs, constant.properties))
    (fun (type, lhs, constProps) => do
      let immProps ← CreateProg.applyNative
          (Outputs := Handle OpCode (.prop (.riscv riscvOp))) constProps fun ⟨const⟩ =>
        (singleBitImm? complement const.value).map fun n => cast h.symm (mkRISCVImm n)
      createRegOp type #[lhs] riscvOp (.inr immProps))
    (fun castBackOp => castBackOp)

/-- `gmir.g_or` (`i64`) with a single-bit constant rhs -> `riscv.bseti`. -/
def gmirBseti_pattern : Pattern OpCode := gmirSingleBit_pattern .g_or .bseti rfl false

/-- `gmir.g_xor` (`i64`) with a single-bit constant rhs -> `riscv.binvi`. -/
def gmirBinvi_pattern : Pattern OpCode := gmirSingleBit_pattern .g_xor .binvi rfl false

/-- `gmir.g_and` (`i64`) with a single-cleared-bit constant rhs -> `riscv.bclri`. -/
def gmirBclri_pattern : Pattern OpCode := gmirSingleBit_pattern .g_and .bclri rfl true

def gmirBseti : Puddle.CompiledPattern OpCode := gmirBseti_pattern.compile
def gmirBinvi : Puddle.CompiledPattern OpCode := gmirBinvi_pattern.compile
def gmirBclri : Puddle.CompiledPattern OpCode := gmirBclri_pattern.compile

/-! ## Composed patterns

  Patterns of several gMIR operations, which run before the other phases select the inner operations.
-/

/-- Match a `gmir.g_constant` of `type` whose value, read as a 64-bit integer, is `value`. -/
def matchConstant64 (type : Handle OpCode .type) (value : BitVec 64) :
    MatchProg.Builder (OpHandle (.gmir .g_constant)) :=
  MatchProg.operation (.gmir .g_constant) #[] #[type] fun ⟨const⟩ =>
    BitVec.ofInt 64 const.value = value

/--
  Shared shape of the Zbb negated-operand lowerings (`andn`/`orn`/`xnor`): match a binary gMIR
  op on `i64` one of whose operands is a `not` (`xor _, -1`), cast the plain operand `x` and the
  `not`'s operand `y` to registers, apply the binary reg-reg riscv op `riscvOp`, and cast the result
  back to `i64`. `notLhs` selects the operand that is the `not`.
-/
def gmirBinopNot_pattern (opcode : GMIR) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp)) (notLhs : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 64)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let allOnes ← matchConstant64 type (-1)
      let notOp ← MatchProg.operation (.gmir .g_xor) #[y, allOnes.res[0]!] #[type]
      let root ← MatchProg.root (.gmir opcode)
          (if notLhs then #[notOp.res[0]!, x] else #[x, notOp.res[0]!]) #[type]
      matchLegal opcode type root.properties
      return (type, x, y))
    (fun (type, x, y) => createRegOp type #[x, y] riscvOp (.inl riscvProps))
    (fun castBackOp => castBackOp)

/-- The mask `gmirOrcb_pattern`'s soundness gate looks for: `0x0101_0101_0101_0101 <<< Y`, whose only
    set bit in each byte is bit `Y`. -/
def orcbMaskBV (y : Nat) : BitVec 64 := BitVec.ofNat 64 0x0101010101010101 <<< y

/--
  `sub (shl M (8 - Y)) (lshr M Y)` -> `riscv.orcb M`,
  where `M = and Z (0x0101_0101_0101_0101 <<< Y)`
-/
def gmirOrcb_pattern (y : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 64)
      let z ← MatchProg.value type
      let mask ← matchConstant64 type (orcbMaskBV y)
      let m ← MatchProg.operation (.gmir .g_and) #[z, mask.res[0]!] #[type]
      let shlAmount ← matchConstant64 type (BitVec.ofNat 64 (8 - y))
      let shl ← MatchProg.operation (.gmir .g_shl) #[m.res[0]!, shlAmount.res[0]!] #[type]
      /- right operand must be `M` itself (when `Y = 0`) or `lshr M Y` -/
      let rhs ← if y = 0 then pure m.res[0]! else do
        let lshrAmount ← matchConstant64 type (BitVec.ofNat 64 y)
        let lshr ← MatchProg.operation (.gmir .g_lshr) #[m.res[0]!, lshrAmount.res[0]!] #[type]
        pure lshr.res[0]!
      let root ← MatchProg.root (.gmir .g_sub) #[shl.res[0]!, rhs] #[type]
      matchLegal .g_sub type root.properties
      return (type, m.res[0]!))
    (fun (type, m) => createRegOp type #[m] .orcb (.inl ()))
    (fun castBackOp => castBackOp)

/-- `and (lshr x n) 1` -> `riscv.bexti x n` (`PatGprImm`-style single-bit extract).
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L536-L537 -/
def gmirBexti_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 64)
      let x ← MatchProg.value type
      let shamt ← MatchProg.operation (.gmir .g_constant) #[] #[type] fun ⟨const⟩ =>
        let sh := (BitVec.ofInt 64 const.value).toInt
        0 ≤ sh && sh ≤ 63
      let lshr ← MatchProg.operation (.gmir .g_lshr) #[x, shamt.res[0]!] #[type]
      let one ← matchConstant64 type 1
      let root ← MatchProg.root (.gmir .g_and) #[lshr.res[0]!, one.res[0]!] #[type]
      matchLegal .g_and type root.properties
      return (type, x, shamt.properties))
    (fun (type, x, shamtProps) => do
      let immProps ← CreateProg.applyNative
          (Outputs := Handle OpCode (.prop (.riscv .bexti))) shamtProps fun ⟨const⟩ =>
        some (mkRISCVImm const.value)
      createRegOp type #[x] .bexti (.inr immProps))
    (fun castBackOp => castBackOp)

/-- `shl (zext i32->i64 x) (const ∈ [0,31])` -> `riscv.slliuw x shamt`
    (Zba: `(i64 (shl (and GPR, 0xFFFFFFFF), uimm5)) -> SLLI_UW`; our `zext` is the mask).
    https://github.com/llvm/llvm-project/blob/2e87cf8c2b8ec6453ccfa7e448d5b33f1d71a2ca/llvm/lib/Target/RISCV/RISCVInstrInfoZb.td#L821-L822 -/
def gmirSlliuw_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 64)
      let srcType ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 32)
      let x ← MatchProg.value srcType
      let zext ← MatchProg.operation (.gmir .g_zext) #[x] #[type]
      let shamt ← MatchProg.operation (.gmir .g_constant) #[] #[type] fun ⟨const⟩ =>
        let sh := (BitVec.ofInt 64 const.value).toInt
        0 ≤ sh && sh ≤ 31
      let root ← MatchProg.root (.gmir .g_shl) #[zext.res[0]!, shamt.res[0]!] #[type]
      matchLegal .g_shl type root.properties
      return (type, x, shamt.properties))
    (fun (type, x, shamtProps) => do
      let immProps ← CreateProg.applyNative
          (Outputs := Handle OpCode (.prop (.riscv .slliuw))) shamtProps fun ⟨const⟩ =>
        some (mkRISCVImm const.value)
      createRegOp type #[x] .slliuw (.inr immProps))
    (fun castBackOp => castBackOp)

/-- The composed patterns, in the order they are tried. -/
def gmirComposed : Array (Puddle.CompiledPattern OpCode) :=
  let binopNot := #[false, true].flatMap fun notLhs =>
    #[gmirBinopNot_pattern .g_and .andn () notLhs, gmirBinopNot_pattern .g_or .orn () notLhs,
      gmirBinopNot_pattern .g_xor .xnor () notLhs]
  (binopNot ++ (List.range 8).toArray.map gmirOrcb_pattern ++
    #[gmirBexti_pattern, gmirSlliuw_pattern]).map (·.compile)

/-- `gmir.g_mul` (`i64`) -> `riscv.mul`. -/
def gmirMul_pattern : Pattern OpCode :=
  lowerBinary (.gmir .g_mul) (·.bitwidth = 64) .mul () (guard := matchLegal .g_mul)

/-- `gmir.g_sdiv` (`i64`) -> `riscv.div`. -/
def gmirSdiv_pattern : Pattern OpCode :=
  lowerBinary (.gmir .g_sdiv) (·.bitwidth = 64) .div () (guard := matchLegal .g_sdiv)

/-- `gmir.g_udiv` (`i64`) -> `riscv.divu`. -/
def gmirUdiv_pattern : Pattern OpCode :=
  lowerBinary (.gmir .g_udiv) (·.bitwidth = 64) .divu () (guard := matchLegal .g_udiv)

/-- `gmir.g_srem` (`i64`) -> `riscv.rem`. -/
def gmirSrem_pattern : Pattern OpCode :=
  lowerBinary (.gmir .g_srem) (·.bitwidth = 64) .rem () (guard := matchLegal .g_srem)

/-- `gmir.g_urem` (`i64`) -> `riscv.remu`. -/
def gmirUrem_pattern : Pattern OpCode :=
  lowerBinary (.gmir .g_urem) (·.bitwidth = 64) .remu () (guard := matchLegal .g_urem)

def gmirMul : Puddle.CompiledPattern OpCode := gmirMul_pattern.compile
def gmirSdiv : Puddle.CompiledPattern OpCode := gmirSdiv_pattern.compile
def gmirUdiv : Puddle.CompiledPattern OpCode := gmirUdiv_pattern.compile
def gmirSrem : Puddle.CompiledPattern OpCode := gmirSrem_pattern.compile
def gmirUrem : Puddle.CompiledPattern OpCode := gmirUrem_pattern.compile

/-- `gmir_riscv.g_addw` (`i64`) -> `riscv.addw`. -/
def gmirRiscvAddw_pattern : Pattern OpCode :=
  lowerBinary (.gmir_riscv .g_addw) (·.bitwidth = 64) .addw ()

/-- `gmir_riscv.g_subw` (`i64`) -> `riscv.subw`. -/
def gmirRiscvSubw_pattern : Pattern OpCode :=
  lowerBinary (.gmir_riscv .g_subw) (·.bitwidth = 64) .subw ()

/-- `gmir_riscv.g_mulw` (`i64`) -> `riscv.mulw`. -/
def gmirRiscvMulw_pattern : Pattern OpCode :=
  lowerBinary (.gmir_riscv .g_mulw) (·.bitwidth = 64) .mulw ()

/-- `gmir_riscv.g_divw` (`i64`) -> `riscv.divw`. -/
def gmirRiscvDivw_pattern : Pattern OpCode :=
  lowerBinary (.gmir_riscv .g_divw) (·.bitwidth = 64) .divw ()

/-- `gmir_riscv.g_divuw` (`i64`) -> `riscv.divuw`. -/
def gmirRiscvDivuw_pattern : Pattern OpCode :=
  lowerBinary (.gmir_riscv .g_divuw) (·.bitwidth = 64) .divuw ()

/-- `gmir_riscv.g_remuw` (`i64`) -> `riscv.remuw`. -/
def gmirRiscvRemuw_pattern : Pattern OpCode :=
  lowerBinary (.gmir_riscv .g_remuw) (·.bitwidth = 64) .remuw ()

/-- `gmir_riscv.g_sllw` (`i64`) -> `riscv.sllw`. -/
def gmirRiscvSllw_pattern : Pattern OpCode :=
  lowerBinary (.gmir_riscv .g_sllw) (·.bitwidth = 64) .sllw ()

/-- `gmir_riscv.g_srlw` (`i64`) -> `riscv.srlw`. -/
def gmirRiscvSrlw_pattern : Pattern OpCode :=
  lowerBinary (.gmir_riscv .g_srlw) (·.bitwidth = 64) .srlw ()

/-- `gmir_riscv.g_sraw` (`i64`) -> `riscv.sraw`. -/
def gmirRiscvSraw_pattern : Pattern OpCode :=
  lowerBinary (.gmir_riscv .g_sraw) (·.bitwidth = 64) .sraw ()

/-- `gmir_riscv.g_clzw` (`i64`) -> `riscv.clzw`. -/
def gmirRiscvClzw_pattern : Pattern OpCode :=
  lowerUnary (.gmir_riscv .g_clzw) 64 .clzw ()

/-- `gmir_riscv.g_ctzw` (`i64`) -> `riscv.ctzw`. -/
def gmirRiscvCtzw_pattern : Pattern OpCode :=
  lowerUnary (.gmir_riscv .g_ctzw) 64 .ctzw ()

def gmirRiscvAddw : Puddle.CompiledPattern OpCode := gmirRiscvAddw_pattern.compile
def gmirRiscvSubw : Puddle.CompiledPattern OpCode := gmirRiscvSubw_pattern.compile
def gmirRiscvMulw : Puddle.CompiledPattern OpCode := gmirRiscvMulw_pattern.compile
def gmirRiscvDivw : Puddle.CompiledPattern OpCode := gmirRiscvDivw_pattern.compile
def gmirRiscvDivuw : Puddle.CompiledPattern OpCode := gmirRiscvDivuw_pattern.compile
def gmirRiscvRemuw : Puddle.CompiledPattern OpCode := gmirRiscvRemuw_pattern.compile
def gmirRiscvSllw : Puddle.CompiledPattern OpCode := gmirRiscvSllw_pattern.compile
def gmirRiscvSrlw : Puddle.CompiledPattern OpCode := gmirRiscvSrlw_pattern.compile
def gmirRiscvSraw : Puddle.CompiledPattern OpCode := gmirRiscvSraw_pattern.compile
def gmirRiscvClzw : Puddle.CompiledPattern OpCode := gmirRiscvClzw_pattern.compile
def gmirRiscvCtzw : Puddle.CompiledPattern OpCode := gmirRiscvCtzw_pattern.compile

/-- `gmir.g_constant` (`i64`) -> `riscv.li`. -/
def gmirConstant_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let root ← MatchProg.root (.gmir .g_constant) #[] #[type]
      matchLegal .g_constant type root.properties
      return (type, root.properties))
    (fun (type, constProps) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let liProps ← CreateProg.applyNative constProps fun ⟨const⟩ =>
        some (RISCVImmediateProperties.mk (BitVec.ofInt 64 const.value))
      let liOp ← CreateProg.operation (.riscv .li) #[] #[regType] (.inr liProps)
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[liOp.res[0]!] #[type]
      return castBackOp)
    (fun castBackOp => castBackOp)

def gmirConstant : Puddle.CompiledPattern OpCode := gmirConstant_pattern.compile

/-- `gmir.g_ctlz` (`i64`) -> `riscv.clz`. -/
def gmirCtlz_pattern : Pattern OpCode :=
  lowerUnary (.gmir .g_ctlz) 64 .clz () fun opType resType props =>
    matchLegal .g_ctlz resType props (type₁ := opType)

/-- `gmir.g_cttz` (`i64`) -> `riscv.ctz`. -/
def gmirCttz_pattern : Pattern OpCode :=
  lowerUnary (.gmir .g_cttz) 64 .ctz () fun opType resType props =>
    matchLegal .g_cttz resType props (type₁ := opType)

/-- `gmir.g_ctpop` (`i64`) -> `riscv.cpop`. -/
def gmirCtpop_pattern : Pattern OpCode :=
  lowerUnary (.gmir .g_ctpop) 64 .cpop () fun opType resType props =>
    matchLegal .g_ctpop resType props (type₁ := opType)

/--
  `gmir.g_ctpop` (`i64`) of a `gmir.g_zext` from `i32` -> `riscv.cpopw`, as LLVM's
  `(ctpop (zexti32 x)) -> CPOPW`.
-/
def gmirCpopw_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let srcType ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 32)
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 64)
      let x ← MatchProg.value srcType
      let zext ← MatchProg.operation (.gmir .g_zext) #[x] #[type]
      let root ← MatchProg.root (.gmir .g_ctpop) #[zext.res[0]!] #[type]
      matchLegal .g_ctpop type root.properties
      return (type, x))
    (fun (type, x) => createRegOp type #[x] .cpopw (.inl ()))
    (fun castBackOp => castBackOp)

/-- `gmir.g_bswap` (`i64`) -> `riscv.rev8`. -/
def gmirBswap_pattern : Pattern OpCode :=
  lowerUnary (.gmir .g_bswap) 64 .rev8 () fun _ resType props => matchLegal .g_bswap resType props

/-- `gmir.g_brev8` (`i64`) -> `riscv.brev8`. -/
def gmirBrev8_pattern : Pattern OpCode :=
  lowerUnary (.gmir .g_brev8) 64 .brev8 () fun _ resType props => matchLegal .g_brev8 resType props

/--
  `gmir.g_bitreverse` (`i64`) -> `riscv.brev8` + `riscv.rev8`: reverse the bits within each byte
  with Zbkb's `brev8`, then reverse the byte order.
-/
def gmirBitreverse_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 64)
      let x ← MatchProg.value type
      let root ← MatchProg.root (.gmir .g_bitreverse) #[x] #[type]
      matchLegal .g_bitreverse type root.properties
      return (type, x))
    (fun (type, x) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let castOp ← CreateProg.operation (.builtin .unrealized_conversion_cast) #[x] #[regType]
      let brev8Op ← CreateProg.operation (.riscv .brev8) #[castOp.res[0]!] #[regType]
      let rev8Op ← CreateProg.operation (.riscv .rev8) #[brev8Op.res[0]!] #[regType]
      CreateProg.operation (.builtin .unrealized_conversion_cast) #[rev8Op.res[0]!] #[type])
    (fun castBackOp => castBackOp)

/-- `gmir.g_smax` (`i64`) -> `riscv.max`. -/
def gmirSmax_pattern : Pattern OpCode :=
  lowerBinary (.gmir .g_smax) (·.bitwidth = 64) .max () (guard := matchLegal .g_smax)

/-- `gmir.g_smin` (`i64`) -> `riscv.min`. -/
def gmirSmin_pattern : Pattern OpCode :=
  lowerBinary (.gmir .g_smin) (·.bitwidth = 64) .min () (guard := matchLegal .g_smin)

/-- `gmir.g_umax` (`i64`) -> `riscv.maxu`. -/
def gmirUmax_pattern : Pattern OpCode :=
  lowerBinary (.gmir .g_umax) (·.bitwidth = 64) .maxu () (guard := matchLegal .g_umax)

/-- `gmir.g_umin` (`i64`) -> `riscv.minu`. -/
def gmirUmin_pattern : Pattern OpCode :=
  lowerBinary (.gmir .g_umin) (·.bitwidth = 64) .minu () (guard := matchLegal .g_umin)

def gmirSmax : Puddle.CompiledPattern OpCode := gmirSmax_pattern.compile
def gmirSmin : Puddle.CompiledPattern OpCode := gmirSmin_pattern.compile
def gmirUmax : Puddle.CompiledPattern OpCode := gmirUmax_pattern.compile
def gmirUmin : Puddle.CompiledPattern OpCode := gmirUmin_pattern.compile

def gmirCtlz : Puddle.CompiledPattern OpCode := gmirCtlz_pattern.compile
def gmirCttz : Puddle.CompiledPattern OpCode := gmirCttz_pattern.compile
def gmirCtpop : Puddle.CompiledPattern OpCode := gmirCtpop_pattern.compile
def gmirCpopw : Puddle.CompiledPattern OpCode := gmirCpopw_pattern.compile
def gmirBswap : Puddle.CompiledPattern OpCode := gmirBswap_pattern.compile
def gmirBrev8 : Puddle.CompiledPattern OpCode := gmirBrev8_pattern.compile
def gmirBitreverse : Puddle.CompiledPattern OpCode := gmirBitreverse_pattern.compile

/-! ### `gmir.icmp` lowering

    gmir.icmp eq lhs rhs  -> riscv.sltiu (riscv.xor lhs rhs) 1
    gmir.icmp ne lhs rhs  -> riscv.sltu 0 (riscv.xor lhs rhs)
    gmir.icmp slt lhs rhs -> riscv.slt lhs rhs
    gmir.icmp sle lhs rhs -> riscv.xori (riscv_slt rhs lhs) 1
    gmir.icmp sgt lhs rhs -> riscv.slt rhs lhs
    gmir.icmp sge lhs rhs -> riscv.xori (riscv_slt lhs rhs) 1
    gmir.icmp ult lhs rhs -> riscv.sltu lhs rhs
    gmir.icmp ule lhs rhs -> riscv.xori (riscv_sltu rhs lhs) 1
    gmir.icmp ugt lhs rhs -> riscv.sltu rhs lhs
    gmir.icmp uge lhs rhs -> riscv.xori (riscv_sltu lhs rhs) 1
-/

/--
  `icmp` arm emitting a register-register comparison `rop` (`slt`/`sltu`/`xor`), whose operands
  are the two comparison registers, swapped when `swap` is set, optionally followed by the
  immediate op `ropImm` applied to its result with the immediate `1`.
  - `slt`/`sgt`/`ult`/`ugt`: just the comparison.
  - `sle`/`sge`/`ule`/`uge`: `slt`/`sltu` then `xori _ 1`.
  - the generic `eq`: `xor` then `sltiu _ 1`.
-/
def icmpEmitCmp (regType : Handle OpCode .type) (a b : Handle OpCode .value)
    (rop : Riscv) (ropProps : propertiesOf (OpCode.riscv rop)) (swap : Bool)
    (ropImm : Option (Σ immOp : Riscv, propertiesOf (OpCode.riscv immOp)) := none) :
    CreateProg.Builder CreatedOpHandle := do
  let (u, v) := if swap then (b, a) else (a, b)
  let cmpProps ← CreateProg.property (.riscv rop) ropProps
  let cmpOp ← CreateProg.operation (.riscv rop) #[u, v] #[regType] cmpProps
  match ropImm with
  | none => pure cmpOp
  | some ⟨immOp, immProps'⟩ => do
    let immProps ← CreateProg.property (.riscv immOp) immProps'
    CreateProg.operation (.riscv immOp) #[cmpOp.res[0]!] #[regType] immProps

/-- The comparison sequence of the `icmp` arm for `pred` on the comparison registers `a` and `b`.
    `zeroRhs` selects the `eq`/`ne`-against-zero peepholes, which only use `a`. -/
def icmpEmit (regType : Handle OpCode .type) (pred : Data.LLVM.IntPred)
    (zeroRhs : Bool) (a b : Handle OpCode .value) :
    CreateProg.Builder CreatedOpHandle :=
  match pred, zeroRhs with
  /- `seqz`: `sltiu a 1`, the `eq`-against-zero peephole. -/
  | .eq, true => do
    let sltiuProps ← CreateProg.property (.riscv .sltiu) (mkRISCVImm 1)
    CreateProg.operation (.riscv .sltiu) #[a] #[regType] sltiuProps
  | .eq, false => icmpEmitCmp regType a b .xor () true (some ⟨.sltiu, mkRISCVImm 1⟩)
  /- `snez`: `sltu 0 a`, the `ne`-against-zero peephole. The `riscv.li 0` becomes `x0` under
     `riscv-combine` (see `li_zero_to_x0`). -/
  | .ne, true => do
    let liProps ← CreateProg.property (.riscv .li) (mkRISCVImm 0)
    let liOp ← CreateProg.operation (.riscv .li) #[] #[regType] liProps
    let sltuProps ← CreateProg.property (.riscv .sltu) ()
    CreateProg.operation (.riscv .sltu) #[liOp.res[0]!, a] #[regType] sltuProps
  /- `sltu 0 (xor b a)` (`snez` of the difference): the generic `ne`. -/
  | .ne, false => do
    let xorProps ← CreateProg.property (.riscv .xor) ()
    let xorOp ← CreateProg.operation (.riscv .xor) #[b, a] #[regType] xorProps
    let liProps ← CreateProg.property (.riscv .li) (mkRISCVImm 0)
    let liOp ← CreateProg.operation (.riscv .li) #[] #[regType] liProps
    let sltuProps ← CreateProg.property (.riscv .sltu) ()
    CreateProg.operation (.riscv .sltu)
        #[liOp.res[0]!, xorOp.res[0]!] #[regType] sltuProps
  | .slt, _ => icmpEmitCmp regType a b .slt () false
  | .sgt, _ => icmpEmitCmp regType a b .slt () true
  | .ult, _ => icmpEmitCmp regType a b .sltu () false
  | .ugt, _ => icmpEmitCmp regType a b .sltu () true
  | .sge, _ => icmpEmitCmp regType a b .slt () false (some ⟨.xori, mkRISCVImm 1⟩)
  | .sle, _ => icmpEmitCmp regType a b .slt () true (some ⟨.xori, mkRISCVImm 1⟩)
  | .uge, _ => icmpEmitCmp regType a b .sltu () false (some ⟨.xori, mkRISCVImm 1⟩)
  | .ule, _ => icmpEmitCmp regType a b .sltu () true (some ⟨.xori, mkRISCVImm 1⟩)

/--
  `gmir.g_icmp pred` -> the comparison sequence of the `gmir.icmp` arm for `pred` (see
  `icmpEmit`). Legal operands are `i64` or `!llvm.ptr`, so they fill a register and need no
  sign-extension. When `zeroRhs` is set, the rhs must be the `gmir.g_constant` `0`.
-/
def gmirIcmp_pattern (pred : Data.LLVM.IntPred) (zeroRhs : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let opType ← MatchProg.type (Attr := TypeAttr)
      let resType ← MatchProg.type (Attr := TypeAttr)
      let lhs ← MatchProg.value opType
      let rhs ← if zeroRhs then do
          let zeroOp ← MatchProg.operation (.gmir .g_constant) #[] #[opType]
          MatchProg.matchNative zeroOp.properties isGMIRConstantZero
          pure zeroOp.res[0]!
        else
          MatchProg.value opType
      let root ← MatchProg.root (.gmir .g_icmp) #[lhs, rhs] #[resType]
          (fun props => props.predicate = pred)
      matchLegal .g_icmp resType root.properties (type₁ := opType)
      return (resType, lhs, rhs))
    (fun (resType, lhs, rhs) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let lcastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[lhs] #[regType]
      let rcastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[rhs] #[regType]
      let cmpOp ← icmpEmit regType pred zeroRhs lcastOp.res[0]! rcastOp.res[0]!
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[cmpOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/--
  `gmir.g_icmp` -> riscv comparison sequence. The `eq`/`ne`-against-zero
  peepholes come first so they take priority over the generic arms.
-/
def gmirIcmp : Array (Puddle.CompiledPattern OpCode) :=
  let preds : Array Data.LLVM.IntPred :=
    #[.eq, .ne, .slt, .sgt, .ult, .ugt, .sge, .sle, .uge, .ule]
  let peepholes := #[Data.LLVM.IntPred.eq, .ne].map (gmirIcmp_pattern · true)
  let generic := preds.map (gmirIcmp_pattern · false)
  (peepholes ++ generic).map (·.compile)

/--
  The immediate of the `riscv.slti`/`riscv.sltiu` that `gmir.g_icmp pred x, c` (`i64`) is lowered
  to:
  `gmir.g_icmp slt x, c` -> `riscv.slti x, c`
  `gmir.g_icmp ult x, c` -> `riscv.sltiu x, c`
  `gmir.g_icmp sge x, c` -> `riscv.slti x, c` + `riscv.xori _, 1`
  `gmir.g_icmp uge x, c` -> `riscv.sltiu x, c` + `riscv.xori _, 1`
  `gmir.g_icmp sle x, c` -> `riscv.slti x, c + 1`
  `gmir.g_icmp ule x, c` -> `riscv.sltiu x, c + 1`
  The immediate must fit in 12 bits, and `ule` excludes `c = -1`, where `c + 1` wraps. This is as
  in LLVM's `PatGprSimm12` (`RISCVInstrInfo.td`), `TargetLowering::SimplifySetCC`
  (`TargetLowering.cpp`) and the expansion of `SETGE`/`SETUGE` (`RISCVISelLowering.cpp`).
-/
def sltiImm? (pred : Data.LLVM.IntPred) (c : Int) : Option Int :=
  let value := (BitVec.ofInt 64 c).toInt
  let imm? : Option Int := match pred with
    | .slt | .ult | .sge | .uge => some value
    | .sle => some (value + 1)
    | .ule => if value = -1 then none else some (value + 1)
    | _ => none
  imm?.filter fun imm => -2048 ≤ imm && imm ≤ 2047

/-- `gmir.g_icmp pred x, c` (`i64`) -> `slti`/`sltiu` with the immediate `sltiImm? pred c`,
    inverted with `xori _ 1` for `sge`/`uge` (see `sltiImm?`). -/
def gmirSlti_pattern (pred : Data.LLVM.IntPred) : Pattern OpCode :=
  let unsigned := pred matches .ult | .uge | .ule
  let invert := pred matches .sge | .uge
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 64)
      let resType ← MatchProg.type (Attr := TypeAttr)
      let lhs ← MatchProg.value type
      let constant ← MatchProg.operation (.gmir .g_constant) #[] #[type]
          fun ⟨const⟩ => (sltiImm? pred const.value).isSome
      let root ← MatchProg.root (.gmir .g_icmp) #[lhs, constant.res[0]!] #[resType]
          (fun props => props.predicate = pred)
      matchLegal .g_icmp resType root.properties (type₁ := type)
      return (resType, lhs, constant.properties))
    (fun (resType, lhs, constProps) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let castOp ← CreateProg.operation (.builtin .unrealized_conversion_cast) #[lhs] #[regType]
      let cmpOp ← if unsigned then do
          let props ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.riscv .sltiu)))
              constProps fun ⟨const⟩ => (sltiImm? pred const.value).map mkRISCVImm
          CreateProg.operation (.riscv .sltiu) #[castOp.res[0]!] #[regType] props
        else do
          let props ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.riscv .slti)))
              constProps fun ⟨const⟩ => (sltiImm? pred const.value).map mkRISCVImm
          CreateProg.operation (.riscv .slti) #[castOp.res[0]!] #[regType] props
      let resOp ← if invert then do
          let xoriProps ← CreateProg.property (.riscv .xori) (mkRISCVImm 1)
          CreateProg.operation (.riscv .xori) #[cmpOp.res[0]!] #[regType] xoriProps
        else pure cmpOp
      CreateProg.operation (.builtin .unrealized_conversion_cast) #[resOp.res[0]!] #[resType])
    (fun castBackOp => castBackOp)

/-- The `slti`/`sltiu` selections of `gmir.g_icmp` (see `gmirSlti_pattern`). -/
def gmirSlti : Array (Puddle.CompiledPattern OpCode) :=
  #[Data.LLVM.IntPred.slt, .ult, .sge, .uge, .sle, .ule].map (gmirSlti_pattern · |>.compile)

/-! # Pass implementation -/

def ISelPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  /- Composed loop: select expressions of several gMIR operations into one instruction, before
     the later loops select their inner operations. -/
  let composed := RewritePattern.GreedyRewritePattern <| gmirComposed.map (·.run)
  let ctx ← match RewritePattern.applyToFunctions composed ctx op with
  | none => throw "Error while applying composed instruction-selection patterns"
  | some ctx => pure ctx
  /- Early loop: fold composed intrinsics and inspect constants before the per-op
     lowerings consume them. -/
  let early := RewritePattern.GreedyRewritePattern <|
    #[lifetimeStart.run, lifetimeEnd.run, memIntrinsic, .fromLocalRewrite splitLoad_local,
    .fromLocalRewrite splitStore_local] ++ load.map (·.run) ++
    store.map (·.run) ++ gmirSelectZero.map (·.run) ++ #[
    fshlConst64.run, fshlConst32.run, fshrConst64.run, fshrConst32.run,
    fshlConst32Trunc.run, fshrConst32Trunc.run,
    gmirAddi.run, gmirAndi.run, gmirOri.run, gmirXori.run, gmirSlli.run, gmirSrli.run, gmirSrai.run,
    gmirRiscvAddiw.run, gmirRiscvSlliw.run, gmirRiscvSrliw.run, gmirRiscvSraiw.run,
    gmirCpopw.run, gmirBseti.run, gmirBinvi.run, gmirBclri.run] ++ gmirSlti.map (·.run)
  let ctx ← match RewritePattern.applyToFunctions early ctx op with
  | none => throw "Error while applying early memory-lowering patterns"
  | some ctx => pure ctx
  /- Main loop: the existing per-op lowerings. -/
  let pattern := RewritePattern.GreedyRewritePattern <|
    #[gmirSelect.run,
    constant.run, addressof.run] ++
    #[
    sext32.run, sext16.run, sextInReg8.run, sextInReg16.run, sextInReg32.run, sextInRegShift.run,
    zext32.run, zext16.run, trunc.run,
    bitcast.run] ++
    load.map (·.run) ++ #[getelementptrGeneral] ++ store.map (·.run) ++ #[
    fshl64.run, fshl32.run, fshr64.run, fshr32.run, fshlGeneral64.run, fshlGeneral32.run, fshrGeneral64.run, fshrGeneral32.run,
    poisonConst.run, zeroConst.run, freeze.run,
    gmirAdd.run, gmirSub.run, gmirTrunc.run, gmirAnyextOfReg.run, gmirAnyext.run, gmirShl.run, gmirLshr.run, gmirAshr.run,
    gmirAnd.run, gmirOr.run, gmirXor.run,
    gmirMul.run, gmirSdiv.run, gmirUdiv.run, gmirSrem.run, gmirUrem.run,
    gmirRiscvAddw.run, gmirRiscvSubw.run, gmirRiscvMulw.run,
    gmirRiscvDivw.run, gmirRiscvDivuw.run, gmirRiscvRemuw.run, gmirRiscvSllw.run, gmirRiscvSrlw.run,
    gmirRiscvSraw.run, gmirRiscvClzw.run, gmirRiscvCtzw.run,
    gmirConstant.run,
    gmirCtlz.run, gmirCttz.run, gmirCtpop.run, gmirBswap.run, gmirBrev8.run, gmirBitreverse.run,
    gmirSmax.run, gmirSmin.run, gmirUmax.run, gmirUmin.run] ++
    gmirIcmp.map (·.run)
  match RewritePattern.applyToFunctions pattern ctx op with
  | none => throw "Error while applying main instruction-selection patterns"
  | some ctx => pure ctx

public def IselRISCV64 : Pass OpCode :=
  { name := "isel-riscv64"
    description :=
      "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := fun _ => ISelPass.impl }
