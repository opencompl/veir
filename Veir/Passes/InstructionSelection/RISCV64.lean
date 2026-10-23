module

public import Veir.Pass
public import Veir.PatternRewriter.Basic
import Veir.DataLayout.RISCV64
import Veir.IR.SymbolRef
import Veir.Interfaces.ConstantLikeInterfaces
import Veir.Interfaces.FunctionInterfaces
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

/-- `llvm.intr.ctlz` (`i32`) -> `riscv.clzw`. -/
def ctlz32_pattern : Pattern OpCode := lowerUnary (.llvm .intr__ctlz) 32 .clzw ()

/-- `llvm.intr.ctlz` (`i64`) -> `riscv.clz`. -/
def ctlz64_pattern : Pattern OpCode := lowerUnary (.llvm .intr__ctlz) 64 .clz ()

/-- `llvm.intr.cttz` (`i32`) -> `riscv.ctzw`. -/
def cttz32_pattern : Pattern OpCode := lowerUnary (.llvm .intr__cttz) 32 .ctzw ()

/-- `llvm.intr.cttz` (`i64`) -> `riscv.ctz`. -/
def cttz64_pattern : Pattern OpCode := lowerUnary (.llvm .intr__cttz) 64 .ctz ()

/-- `llvm.intr.ctpop` (`i32`) -> `riscv.cpopw`. -/
def ctpop32_pattern : Pattern OpCode := lowerUnary (.llvm .intr__ctpop) 32 .cpopw ()

/-- `llvm.intr.ctpop` (`i64`) -> `riscv.cpop`. -/
def ctpop64_pattern : Pattern OpCode := lowerUnary (.llvm .intr__ctpop) 64 .cpop ()

/-- `llvm.intr.umax` -> `riscv.maxu`. Width-agnostic: unlike `add`/`sub`/…, the same instruction
    is used at both bitwidths, since the register already holds the correctly-represented value. -/
def umax_pattern : Pattern OpCode :=
  lowerBinary (.llvm .intr__umax) (fun t => t.bitwidth = 64 ∨ t.bitwidth = 32) .maxu ()

/-- `llvm.intr.umin` -> `riscv.minu`. -/
def umin_pattern : Pattern OpCode :=
  lowerBinary (.llvm .intr__umin) (fun t => t.bitwidth = 64 ∨ t.bitwidth = 32) .minu ()

/-- `llvm.intr.smax` (`i64`) -> `riscv.max`. -/
def smax64_pattern : Pattern OpCode :=
  lowerBinary (.llvm .intr__smax) (fun t => t.bitwidth = 64) .max ()

/-- `llvm.intr.smax` (`i32`) -> sign-extend (so negative values order correctly, since
    `castToRegLocal` zero-extends) then `riscv.max`. -/
def smax32_pattern : Pattern OpCode :=
  lowerBinary (.llvm .intr__smax) (fun t => t.bitwidth = 32) .max () (extend := some ⟨.sextw, ()⟩)

/-- `llvm.intr.smin` (`i64`) -> `riscv.min`. -/
def smin64_pattern : Pattern OpCode :=
  lowerBinary (.llvm .intr__smin) (fun t => t.bitwidth = 64) .min ()

/-- `llvm.intr.smin` (`i32`) -> sign-extend (so negative values order correctly, since
    `castToRegLocal` zero-extends) then `riscv.min`. -/
def smin32_pattern : Pattern OpCode :=
  lowerBinary (.llvm .intr__smin) (fun t => t.bitwidth = 32) .min () (extend := some ⟨.sextw, ()⟩)

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

/--
  `llvm.intr.ctlz` -> `riscv.clz`.
-/
def ctlz32 : Puddle.CompiledPattern OpCode := ctlz32_pattern.compile
def ctlz64 : Puddle.CompiledPattern OpCode := ctlz64_pattern.compile

/--
  `llvm.intr.cttz` -> `riscv.ctz`.
-/
def cttz32 : Puddle.CompiledPattern OpCode := cttz32_pattern.compile
def cttz64 : Puddle.CompiledPattern OpCode := cttz64_pattern.compile

/--
  `llvm.intr.ctpop` -> `riscv.cpop`.
-/
def ctpop32 : Puddle.CompiledPattern OpCode := ctpop32_pattern.compile
def ctpop64 : Puddle.CompiledPattern OpCode := ctpop64_pattern.compile

/--
  `llvm.intr.bswap` -> `riscv.rev8`. `rev8` reverses all 8 bytes; for `i32` the wanted bytes end
  up in the high 32 bits, so shift them down with `srli 32`.
-/
def lowerBswap (bw : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let opType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = bw)
      let resType ← MatchProg.type (Attr := TypeAttr)
      let x ← MatchProg.value opType
      let _ ← MatchProg.root (.llvm .intr__bswap) #[x] #[resType]
      return (resType, x))
    (fun (resType, x) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let castOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[x] #[regType]
      let rev8Op ← CreateProg.operation (.riscv .rev8)
          #[castOp.res[0]!] #[regType]
      let resOp ← if bw = 32 then do
          let srliProps ← CreateProg.property (.riscv .srli)
              (RISCVImmediateProperties.mk 32#64)
          CreateProg.operation (.riscv .srli) #[rev8Op.res[0]!] #[regType] srliProps
        else
          pure rev8Op
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[resOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- `llvm.intr.bswap` (`i64`) -> `riscv.rev8`. -/
def bswap64 : Puddle.CompiledPattern OpCode := (lowerBswap 64).compile

/-- `llvm.intr.bswap` (`i32`) -> `riscv.rev8` + `riscv.srli 32`. -/
def bswap32 : Puddle.CompiledPattern OpCode := (lowerBswap 32).compile

/--
  One SWAR bit-reversal stage:
  `((x & mask) << shamt) | ((x >> shamt) & mask)`.
-/
def bitreverseStage (regType : Handle OpCode .type) (mask shamt : Int)
    (input : Handle OpCode .value) :
    CreateProg.Builder (Handle OpCode .value) := do
  let maskOp ← CreateProg.operation (.riscv .li)
      #[] #[regType] (.inl $ .mk (.ofInt 64 mask))
  let lowOp ← CreateProg.operation (.riscv .and)
      #[maskOp.res[0]!, input] #[regType]
  let lowShiftOp ← CreateProg.operation (.riscv .slli)
      #[lowOp.res[0]!] #[regType] (.inl $ .mk (BitVec.ofInt 64 shamt))
  let highShiftOp ← CreateProg.operation (.riscv .srli)
      #[input] #[regType] (.inl $ .mk (BitVec.ofInt 64 shamt))
  let highOp ← CreateProg.operation (.riscv .and)
      #[maskOp.res[0]!, highShiftOp.res[0]!] #[regType]
  let orOp ← CreateProg.operation (.riscv .or)
      #[lowShiftOp.res[0]!, highOp.res[0]!] #[regType]
  return orOp.res[0]!

/--
  `llvm.intr.bitreverse` -> mask/shift/or stages followed by `riscv.rev8`.
-/
def lowerBitreverse (bw : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let opType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = bw)
      let resType ← MatchProg.type (Attr := TypeAttr)
      let x ← MatchProg.value opType
      let _ ← MatchProg.root (.llvm .intr__bitreverse) #[x] #[resType]
      return (resType, x))
    (fun (resType, x) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let castOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[x] #[regType]
      let resOp ← if bw = 32 then do
          /- Use 32-bit masks so SWAR stages stay within the low 32 bits.
             rev8 brings bits to high 32; srli 32 moves them back down. -/
          let x1 ← bitreverseStage regType 0x55555555 1 castOp.res[0]!
          let x2 ← bitreverseStage regType 0x33333333 2 x1
          let x3 ← bitreverseStage regType 0x0f0f0f0f 4 x2
          let rev8Props ← CreateProg.property (.riscv .rev8) ()
          let rev8Op ← CreateProg.operation (.riscv .rev8) #[x3] #[regType] rev8Props
          let srliProps ← CreateProg.property (.riscv .srli)
              (RISCVImmediateProperties.mk 32#64)
          CreateProg.operation (.riscv .srli) #[rev8Op.res[0]!] #[regType] srliProps
        else do
          let x1 ← bitreverseStage regType 0x5555555555555555 1 castOp.res[0]!
          let x2 ← bitreverseStage regType 0x3333333333333333 2 x1
          let x3 ← bitreverseStage regType 0x0f0f0f0f0f0f0f0f 4 x2
          let rev8Props ← CreateProg.property (.riscv .rev8) ()
          CreateProg.operation (.riscv .rev8) #[x3] #[regType] rev8Props
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[resOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- `llvm.intr.bitreverse` (`i64`) -> mask/shift/or stages followed by `riscv.rev8`. -/
def bitreverse64 : Puddle.CompiledPattern OpCode := (lowerBitreverse 64).compile

/-- `llvm.intr.bitreverse` (`i32`) -> mask/shift/or stages, `riscv.rev8` and `riscv.srli 32`. -/
def bitreverse32 : Puddle.CompiledPattern OpCode := (lowerBitreverse 32).compile

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

/--
  Lower a constant-count entry-block allocation to a fixed RISC-V stack object.
  Dynamic allocations and `inalloca` need additional stack-lifetime support in the backend.
  Run before constant selection so the count still has an integer runtime value.
-/
def alloca_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operands, properties) := matchOp op ctx.raw Llvm.alloca 1 | return (ctx, none)
  if properties.inalloca then return (ctx, none)
  let .llvmPointerType _ := ((op.getResult 0).getType! ctx.raw).val | return (ctx, none)
  let some parentOp := op.getParentOp! ctx.raw | return (ctx, none)
  let some funcOp := FunctionOp.of? parentOp ctx.raw | return (ctx, none)
  let some entry := funcOp.getEntryBlock? | return (ctx, none)
  if (op.getParent! ctx.raw) != some entry then return (ctx, none)
  let some (.int _ (.val count)) := operands[0]!.constantValue ctx.raw | return (ctx, none)
  let some layout := DataLayout.riscv64.query properties.elem_type.val | return (ctx, none)
  let size := count.toNat * layout.allocSize
  /- Do not silently wrap the fixed object's size to a signed 64-bit value. -/
  if size >= 2 ^ 63 then return (ctx, none)
  let alignment : Int := if properties.alignment.value = 0 then layout.abiAlignment
    else properties.alignment.value
  if !isValidLLVMAlignment alignment || alignment >= 2 ^ 63 then
    return (ctx, none)
  let props : RISCVStackAllocaProperties :=
    { size := BitVec.ofNat 64 size
      alignment := BitVec.ofInt 64 alignment }
  let (ctx, stackOp) ← WfRewriter.createOp! ctx Riscv_Stack.alloca #[RegisterType.mk]
      #[] #[] #[] props none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (stackOp.getResult 0)
  some (ctx, some (#[stackOp, castBackOp], #[castBackOp.getResult 0]))

/-- `llvm.alloca` -> `riscv_stack.alloca` and a cast back to the pointer type. -/
def alloca (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite alloca_local rewriter op opInBounds

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

/-- `llvm.mlir.addressof` -> `riscv.la`, except for TLS and external weak globals. -/
def addressof_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (_, properties) := matchOp op ctx.raw Llvm.mlir__addressof 0 | return (ctx, none)
  let some name := properties.global_name.getName? | return (ctx, none)
  if let some global := lookupGlobal? ctx.raw op name then
    -- An undefined weak symbol resolves to zero, which a PC-relative `la`
    -- cannot always reach. Leave it until GOT-based address lowering is supported.
    if global.isThreadLocal || global.linkage.value = "extern_weak" then return (ctx, none)
  let (ctx, laOp) ← WfRewriter.createOp! ctx Riscv.la #[RegisterType.mk]
      #[] #[] #[] (RISCVSymbolProperties.mk properties.global_name) none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (laOp.getResult 0)
  some (ctx, some (#[laOp, castBackOp], #[castBackOp.getResult 0]))

/-- `llvm.mlir.addressof` -> `riscv.la` and a cast back to the pointer type. -/
def addressof (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite addressof_local rewriter op opInBounds

/--
  The signed 12-bit immediate offset of a load/store address `getelementptr base, c`, with
  properties `gep` and a constant `i64` index `c` with properties `idx`, when it can be folded
  into the access, mirroring the `isBaseWithConstantOffset` case of LLVM's
  [`RISCVDAGToDAGISel::SelectAddrRegImm`](https://github.com/llvm/llvm-project/blob/llvmorg-22.1.8/llvm/lib/Target/RISCV/RISCVISelDAGToDAG.cpp#L3175-L3206).
-/
def selectAddrRegImm (gep : GetelementptrProperties) (idx : GMIRConstantProperties) :
    Option Int := do
  /- A single dynamic index with no trailing constant indices, as in `getelementptr`. -/
  guard (gep.rawConstantIndices.values = #[(-2147483648 : Int)])
  let c := idx.value
  let scale ← DataLayout.riscv64.getTypeAllocSize gep.elem_type.val
  let offset := (BitVec.ofInt 64 c.value).toInt * (scale : Int)
  guard (-2048 ≤ offset ∧ offset ≤ 2047)
  return offset

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

/--
  llvm.load -> riscv.ld (i64, ptr) / riscv.lw (i32) / riscv.lh (i16) / riscv.lb (i8), for a
  `width`-byte load with `riscvOp`. When `folded` is set, the address must be a
  `getelementptr base, c` whose constant offset folds into the immediate (see
  `selectAddrRegImm`); otherwise the address itself is the base, at offset `0`.
-/
def lowerLoad (folded : Bool) (width : Nat) (riscvOp : Riscv)
    (h : propertiesOf (OpCode.riscv riscvOp) = RISCVMemProperties := by rfl) :
    Pattern OpCode :=
  Pattern.Builder
    (do
      let baseType ← MatchProg.type (Attr := TypeAttr)
      let base ← MatchProg.value baseType
      /- Split the address into a base register and a signed 12-bit offset. -/
      let (addr, gep?) ← if folded then do
          let idxType ← MatchProg.type (Attr := IntegerType)
              (fun t => t.bitwidth = 64)
          let idxOp ← MatchProg.operation (.gmir .g_constant) #[] #[idxType]
          let addrType ← MatchProg.type (Attr := TypeAttr)
          let gepOp ← MatchProg.operation (.llvm .getelementptr)
              #[base, idxOp.res[0]!] #[addrType]
          MatchProg.matchNative (gepOp.properties, idxOp.properties)
              fun (gep, idx) => (selectAddrRegImm gep idx).isSome
          pure (gepOp.res[0]!, some (gepOp.properties, idxOp.properties))
        else
          pure (base, none)
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
      /- Volatility carries over from the `llvm.load`: the riscv op encodes the same, but the
         flag keeps later passes from deleting or duplicating the access. -/
      let memProps ← match gep? with
        | some (gepProps, idxProps) =>
          CreateProg.applyNative
              (Outputs := Handle OpCode (.prop (.riscv riscvOp)))
              (gepProps, idxProps, loadProps)
              fun (gep, idx, load) => (selectAddrRegImm gep idx).map fun offset =>
                cast h.symm (RISCVMemProperties.mk (BitVec.ofInt 64 offset) load.volatile_)
        | none =>
          CreateProg.applyNative
              (Outputs := Handle OpCode (.prop (.riscv riscvOp))) loadProps
              fun load => some (cast h.symm (RISCVMemProperties.mk 0 load.volatile_))
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
  #[true, false].flatMap fun folded =>
    #[lowerLoad folded 1 .lb, lowerLoad folded 2 .lh, lowerLoad folded 4 .lw,
      lowerLoad folded 8 .ld].map (·.compile)

/--
  llvm.store -> riscv.sd (i64, ptr) / riscv.sw (i32) / riscv.sh (i16) / riscv.sb (i8), for a
  `width`-byte store with `riscvOp`. The address is split as in `lowerLoad`.
-/
def lowerStore (folded : Bool) (width : Nat) (riscvOp : Riscv)
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
      /- Split the address into a base register and a signed 12-bit offset. -/
      let (addr, gep?) ← if folded then do
          let idxType ← MatchProg.type (Attr := IntegerType)
              (fun t => t.bitwidth = 64)
          let idxOp ← MatchProg.operation (.gmir .g_constant) #[] #[idxType]
          let addrType ← MatchProg.type (Attr := TypeAttr)
          let gepOp ← MatchProg.operation (.llvm .getelementptr)
              #[base, idxOp.res[0]!] #[addrType]
          MatchProg.matchNative (gepOp.properties, idxOp.properties)
              fun (gep, idx) => (selectAddrRegImm gep idx).isSome
          pure (gepOp.res[0]!, some (gepOp.properties, idxOp.properties))
        else
          pure (base, none)
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
      /- The store writes the low `width` bytes of the value register. Volatility carries over
         from the `llvm.store`, as in `lowerLoad`. -/
      let memProps ← match gep? with
        | some (gepProps, idxProps) =>
          CreateProg.applyNative
              (Outputs := Handle OpCode (.prop (.riscv riscvOp)))
              (gepProps, idxProps, storeProps)
              fun (gep, idx, store) => (selectAddrRegImm gep idx).map fun offset =>
                cast h.symm (RISCVMemProperties.mk (BitVec.ofInt 64 offset) store.volatile_)
        | none =>
          CreateProg.applyNative
              (Outputs := Handle OpCode (.prop (.riscv riscvOp))) storeProps
              fun store => some (cast h.symm (RISCVMemProperties.mk 0 store.volatile_))
      let _ ← CreateProg.operation (.riscv riscvOp)
          #[valCastOp.res[0]!, baseCastOp.res[0]!] #[] memProps
      return ())
    (fun () => ⟨#[]⟩)

/--
  llvm.store -> riscv.sd (i64, ptr) / riscv.sw (i32) / riscv.sh (i16) / riscv.sb (i8).
  The patterns folding a constant `getelementptr` offset into the immediate come first.
-/
def store : Array (Puddle.CompiledPattern OpCode) :=
  #[true, false].flatMap fun folded =>
    #[lowerStore folded 1 .sb, lowerStore folded 2 .sh, lowerStore folded 4 .sw,
      lowerStore folded 8 .sd].map (·.compile)

/--
  Lower a single-dynamic-index `llvm.getelementptr` computing `ptr + idx * scale`, where `scale`
  is the allocation size (ABI stride) of the element type, for a `scale` of 1, 2, 4, or 8:
  `ptr + idx` or `(idx << log2 scale) + ptr` with `riscv.sh{1,2,3}add`.
-/
def lowerGetelementptr (scale : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ptrType ← MatchProg.type (Attr := TypeAttr)
      /- The index must be `i64`. -/
      let idxType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 64)
      let resType ← MatchProg.type (Attr := TypeAttr)
      let ptr ← MatchProg.value ptrType
      let idx ← MatchProg.value idxType
      /- Bail unless it's a single dynamic index with no trailing constant indices. -/
      let root ← MatchProg.root (.llvm .getelementptr) #[ptr, idx] #[resType]
          (fun props => props.rawConstantIndices.values = #[(-2147483648 : Int)])
      MatchProg.matchNative root.properties fun gep =>
        (DataLayout.riscv64.getTypeAllocSize gep.elem_type.val).any (· = scale)
      return (resType, ptr, idx, root.properties))
    (fun (resType, ptr, idx, _) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let ptrCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[ptr] #[regType]
      let idxCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[idx] #[regType]
      let addOp ←
        if scale = 1 then do
          /- ptr + idx -/
          CreateProg.operation (.riscv .add)
              #[ptrCastOp.res[0]!, idxCastOp.res[0]!] #[regType]
        else if scale = 2 then do
          /- (idx << 1) + ptr -/
          CreateProg.operation (.riscv .sh1add)
              #[idxCastOp.res[0]!, ptrCastOp.res[0]!] #[regType]
        else if scale = 4 then do
          /- (idx << 2) + ptr -/
          CreateProg.operation (.riscv .sh2add)
              #[idxCastOp.res[0]!, ptrCastOp.res[0]!] #[regType]
        else do
          /- (idx << 3) + ptr -/
          CreateProg.operation (.riscv .sh3add)
              #[idxCastOp.res[0]!, ptrCastOp.res[0]!] #[regType]
      /- Cast the resulting register back to `!llvm.ptr`. -/
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[addOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/--
  `getelementptr` whose `scale` is any other power of two: `ptr + (idx << log2 scale)`.

  `0 < scale` excludes zero-sized element types (`i0`, `!llvm.array<0 x _>`), for which
  `scale &&& (scale - 1) = 0` also holds but `Nat.log2 0 = 0` would emit `idx << 0`, i.e.
  `ptr + idx` rather than `ptr`. `Nat.log2 scale < 64` excludes element sizes of `2^64` and
  beyond, whose shift amount does not fit the 6-bit immediate. Both fall through to the
  `li`/`mul` form of `getelementptrMul_pattern`, which truncates modulo `2^64` exactly as the
  source does.
-/
def getelementptrShift_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ptrType ← MatchProg.type (Attr := TypeAttr)
      /- The index must be `i64`. -/
      let idxType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 64)
      let resType ← MatchProg.type (Attr := TypeAttr)
      let ptr ← MatchProg.value ptrType
      let idx ← MatchProg.value idxType
      /- Bail unless it's a single dynamic index with no trailing constant indices. -/
      let root ← MatchProg.root (.llvm .getelementptr) #[ptr, idx] #[resType]
          (fun props => props.rawConstantIndices.values = #[(-2147483648 : Int)])
      MatchProg.matchNative root.properties fun gep =>
        (DataLayout.riscv64.getTypeAllocSize gep.elem_type.val).any fun scale =>
          scale ∉ [1, 2, 4, 8] ∧ 0 < scale ∧ scale &&& (scale - 1) = 0 ∧ Nat.log2 scale < 64
      return (resType, ptr, idx, root.properties))
    (fun (resType, ptr, idx, gepProps) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let ptrCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[ptr] #[regType]
      let idxCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[idx] #[regType]
      let slliProps ← CreateProg.applyNative
          (Outputs := Handle OpCode (.prop (.riscv .slli))) gepProps
          fun gep => (DataLayout.riscv64.getTypeAllocSize gep.elem_type.val).map fun scale =>
            RISCVImmediateProperties.mk (BitVec.ofInt 64 (Nat.log2 scale))
      let slliOp ← CreateProg.operation (.riscv .slli)
          #[idxCastOp.res[0]!] #[regType] slliProps
      let addOp ← CreateProg.operation (.riscv .add)
          #[ptrCastOp.res[0]!, slliOp.res[0]!] #[regType]
      /- Cast the resulting register back to `!llvm.ptr`. -/
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[addOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/--
  `getelementptr` with an arbitrary `scale` (see `getelementptrShift_pattern`):
  `ptr + idx * scale`.
-/
def getelementptrMul_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let ptrType ← MatchProg.type (Attr := TypeAttr)
      /- The index must be `i64`. -/
      let idxType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 64)
      let resType ← MatchProg.type (Attr := TypeAttr)
      let ptr ← MatchProg.value ptrType
      let idx ← MatchProg.value idxType
      /- Bail unless it's a single dynamic index with no trailing constant indices. -/
      let root ← MatchProg.root (.llvm .getelementptr) #[ptr, idx] #[resType]
          (fun props => props.rawConstantIndices.values = #[(-2147483648 : Int)])
      MatchProg.matchNative root.properties fun gep =>
        (DataLayout.riscv64.getTypeAllocSize gep.elem_type.val).any fun scale =>
          scale ∉ [1, 2, 4, 8] ∧ ¬ (0 < scale ∧ scale &&& (scale - 1) = 0 ∧ Nat.log2 scale < 64)
      return (resType, ptr, idx, root.properties))
    (fun (resType, ptr, idx, gepProps) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let ptrCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[ptr] #[regType]
      let idxCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[idx] #[regType]
      let liProps ← CreateProg.applyNative
          (Outputs := Handle OpCode (.prop (.riscv .li))) gepProps
          fun gep => (DataLayout.riscv64.getTypeAllocSize gep.elem_type.val).map fun scale =>
            RISCVImmediateProperties.mk (BitVec.ofInt 64 scale)
      let liOp ← CreateProg.operation (.riscv .li) #[] #[regType] liProps
      let mulOp ← CreateProg.operation (.riscv .mul)
          #[idxCastOp.res[0]!, liOp.res[0]!] #[regType]
      let addOp ← CreateProg.operation (.riscv .add)
          #[ptrCastOp.res[0]!, mulOp.res[0]!] #[regType]
      /- Cast the resulting register back to `!llvm.ptr`. -/
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[addOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/--
  Lower a single-dynamic-index `llvm.getelementptr` computing `ptr + idx * scale`,
  where `scale` is the allocation size (ABI stride) of the element type.
-/
def getelementptr : Array (Puddle.CompiledPattern OpCode) :=
  #[lowerGetelementptr 1, lowerGetelementptr 2, lowerGetelementptr 4, lowerGetelementptr 8,
    getelementptrShift_pattern, getelementptrMul_pattern].map (·.compile)

/-! ## Zicond branchless `select` lowering

  The Zicond extension lowers `llvm.select` branchlessly (mirroring LLVM's
  SelectionDAG lowering of `ISD::SELECT` when `Zicond` is available):
  ```
    (select c, t, 0) -> (czero.eqz t, c)
    (select c, 0, f) -> (czero.nez f, c)
    (select c, t, f) -> (or (czero.eqz t, c), (czero.nez f, c))
  ```
  The single-instruction zero-arm cases take priority over the general form;
  the greedy driver tries patterns in array order, so `selectCzeroeqz` and
  `selectCzeronez` are registered before `selectGeneral`.
-/

/--
  `select c t 0` -> `riscv.czeroeqz t c`.
-/
def selectCzeroeqz_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let condType ← MatchProg.type (Attr := TypeAttr)
      let valType ← MatchProg.type (Attr := TypeAttr)
      let zeroType ← MatchProg.type (Attr := TypeAttr)
      let resType ← MatchProg.type (Attr := IntegerType)
          (fun t => t.bitwidth = 64 ∨ t.bitwidth = 32)
      let cond ← MatchProg.value condType
      let val ← MatchProg.value valType
      let zeroOp ← MatchProg.operation (.gmir .g_constant) #[] #[zeroType]
      MatchProg.matchNative zeroOp.properties isGMIRConstantZero
      let _ ← MatchProg.root (.llvm .select) #[cond, val, zeroOp.res[0]!] #[resType]
      return (resType, cond, val))
    (fun (resType, cond, val) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let valCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[val] #[regType]
      let condCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[cond] #[regType]
      let czOp ← CreateProg.operation (.riscv .czeroeqz)
          #[valCastOp.res[0]!, condCastOp.res[0]!] #[regType]
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[czOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/--
  `select c t 0` -> `riscv.czeroeqz t c`.
-/
def selectCzeroeqz : Puddle.CompiledPattern OpCode := selectCzeroeqz_pattern.compile

/--
  `select c 0 f` -> `riscv.czeronez f c`.
-/
def selectCzeronez_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let condType ← MatchProg.type (Attr := TypeAttr)
      let valType ← MatchProg.type (Attr := TypeAttr)
      let zeroType ← MatchProg.type (Attr := TypeAttr)
      let resType ← MatchProg.type (Attr := IntegerType)
          (fun t => t.bitwidth = 64 ∨ t.bitwidth = 32)
      let cond ← MatchProg.value condType
      let val ← MatchProg.value valType
      let zeroOp ← MatchProg.operation (.gmir .g_constant) #[] #[zeroType]
      MatchProg.matchNative zeroOp.properties isGMIRConstantZero
      let _ ← MatchProg.root (.llvm .select) #[cond, zeroOp.res[0]!, val] #[resType]
      return (resType, cond, val))
    (fun (resType, cond, val) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let valCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[val] #[regType]
      let condCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[cond] #[regType]
      let czProps ← CreateProg.property (.riscv .czeronez) ()
      let czOp ← CreateProg.operation (.riscv .czeronez)
          #[valCastOp.res[0]!, condCastOp.res[0]!] #[regType] czProps
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[czOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/--
  `select c 0 f` -> `riscv.czeronez f c`.
-/
def selectCzeronez : Puddle.CompiledPattern OpCode := selectCzeronez_pattern.compile

/--
  General branchless select:
  `select c t f` -> `or (czero.eqz t c) (czero.nez f c)`.
-/
def selectGeneral_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let condType ← MatchProg.type (Attr := TypeAttr)
      let tType ← MatchProg.type (Attr := TypeAttr)
      let fType ← MatchProg.type (Attr := TypeAttr)
      let resType ← MatchProg.type (Attr := IntegerType)
          (fun t => t.bitwidth = 64 ∨ t.bitwidth = 32 ∨ t.bitwidth = 1)
      let cond ← MatchProg.value condType
      let tval ← MatchProg.value tType
      let fval ← MatchProg.value fType
      let _ ← MatchProg.root (.llvm .select) #[cond, tval, fval] #[resType]
      return (resType, cond, tval, fval))
    (fun (resType, cond, tval, fval) => do
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
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[orOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/--
  General branchless select:
  `select c t f` -> `or (czero.eqz t c) (czero.nez f c)`.
-/
def selectGeneral : Puddle.CompiledPattern OpCode := selectGeneral_pattern.compile

/-! ## Zbb min/max and rotate intrinsics

  These mirror the simple one-to-one patterns in LLVM's RISC-V backend
  (`RISCVInstrInfoZb.td`): `smin/smax/umin/umax` select to `MIN/MAX/MINU/MAXU`,
  and a funnel shift whose two data operands are identical is a rotate, which
  selects to `ROL`/`ROR`. The general (distinct-operand) funnel shift needs a
  multi-instruction expansion and is intentionally left unselected.
-/

/-- llvm.intr.smax -> riscv.max -/
def smax64 : Puddle.CompiledPattern OpCode := smax64_pattern.compile

def smax32 : Puddle.CompiledPattern OpCode := smax32_pattern.compile

/-- llvm.intr.smin -> riscv.min -/
def smin64 : Puddle.CompiledPattern OpCode := smin64_pattern.compile

def smin32 : Puddle.CompiledPattern OpCode := smin32_pattern.compile

/-- llvm.intr.umax -> riscv.maxu -/
def umax : Puddle.CompiledPattern OpCode := umax_pattern.compile

/-- llvm.intr.umin -> riscv.minu -/
def umin : Puddle.CompiledPattern OpCode := umin_pattern.compile

/-- llvm.intr.fshl with identical data operands is a rotate-left: -> riscv.rol (riscv.rolw for i32).
    The general (distinct-operand) funnel shift is left unselected. -/
def fshl64 : Puddle.CompiledPattern OpCode := fshl64_pattern.compile

def fshl32 : Puddle.CompiledPattern OpCode := fshl32_pattern.compile

/-! ## Saturating integer intrinsics

  These mirror LLVM's RV64+Zbb+Zicond lowering for scalar i64 saturating
  arithmetic. The signed cases compute the wrapped result and an overflow
  predicate, build the signed saturation endpoint, then select with Zicond:

    `or (czero.eqz saturated overflow) (czero.nez wrapped overflow)`

  Unsigned add/sub use the compact Zbb min/max idioms selected by LLVM.

  The generic DAG expansions live in
  `llvm/lib/CodeGen/SelectionDAG/TargetLowering.cpp`:
    * `TargetLowering::expandAddSubSat`  (add/sub sat)      @ line 12432
    * `TargetLowering::expandShlSat`     (shl sat)          @ line 12598
    * `TargetLowering::expandSADDSUBO`   (signed overflow)  @ line 13046
  The signed `select`s become Zicond `czero.{eqz,nez}`/`or`, and the signed
  saturation constant `select(x<0, INT_MIN, INT_MAX)` folds to `(x >>s 63) ^
  INT_MAX`. Each sequence below was confirmed identical, instruction for
  instruction, to `llc -mtriple=riscv64 -mattr=+zbb,+zicond`
  (LLVM commit d9906882fc61).
-/

/-- The Zicond select `or (czero.eqz sat overflow) (czero.nez wrapped overflow)` of the signed
    saturating lowerings, returning the `or`. -/
def signedSatSelect (regType : Handle OpCode .type)
    (wrapped overflow sat : Handle OpCode .value) :
    CreateProg.Builder CreatedOpHandle := do
  let wrappedOrZeroProps ← CreateProg.property (.riscv .czeronez) ()
  let wrappedOrZeroOp ← CreateProg.operation (.riscv .czeronez)
      #[wrapped, overflow] #[regType] wrappedOrZeroProps
  let satOrZeroProps ← CreateProg.property (.riscv .czeroeqz) ()
  let satOrZeroOp ← CreateProg.operation (.riscv .czeroeqz)
      #[sat, overflow] #[regType] satOrZeroProps
  let selectProps ← CreateProg.property (.riscv .or) ()
  CreateProg.operation (.riscv .or)
      #[satOrZeroOp.res[0]!, wrappedOrZeroOp.res[0]!] #[regType] selectProps

/-- llvm.intr.sadd.sat.i64 -> LLVM's RV64+Zicond signed saturating-add sequence.
    Wrapped `add` + SADDO overflow `(rhs >>u 63) ^ (sum <s lhs)`
    (TargetLowering.cpp:12432 `expandAddSubSat`, overflow at 13072
    `expandSADDSUBO` add branch; sat endpoint `(sum >>s 63) ^ INT_MIN` at 12554). -/
def saddSat_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let lhsType ← MatchProg.type (Attr := TypeAttr)
      let rhsType ← MatchProg.type (Attr := TypeAttr)
      let resType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 64)
      let lhs ← MatchProg.value lhsType
      let rhs ← MatchProg.value rhsType
      let _ ← MatchProg.root (.llvm .intr__sadd__sat) #[lhs, rhs] #[resType]
      return (resType, lhs, rhs))
    (fun (resType, lhs, rhs) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let lCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[lhs] #[regType]
      let rCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[rhs] #[regType]
      let minusOneProps ← CreateProg.property (.riscv .li) (mkRISCVImm (-1))
      let minusOneOp ← CreateProg.operation (.riscv .li)
          #[] #[regType] minusOneProps
      let sumProps ← CreateProg.property (.riscv .add) ()
      let sumOp ← CreateProg.operation (.riscv .add)
          #[lCastOp.res[0]!, rCastOp.res[0]!] #[regType] sumProps
      let rhsSignProps ← CreateProg.property (.riscv .srli) (mkRISCVImm 63)
      let rhsSignOp ← CreateProg.operation (.riscv .srli)
          #[rCastOp.res[0]!] #[regType] rhsSignProps
      let carryLikeProps ← CreateProg.property (.riscv .slt) ()
      let carryLikeOp ← CreateProg.operation (.riscv .slt)
          #[sumOp.res[0]!, lCastOp.res[0]!] #[regType] carryLikeProps
      let sumSignProps ← CreateProg.property (.riscv .srai) (mkRISCVImm 63)
      let sumSignOp ← CreateProg.operation (.riscv .srai)
          #[sumOp.res[0]!] #[regType] sumSignProps
      let intMinProps ← CreateProg.property (.riscv .slli) (mkRISCVImm 63)
      let intMinOp ← CreateProg.operation (.riscv .slli)
          #[minusOneOp.res[0]!] #[regType] intMinProps
      let overflowProps ← CreateProg.property (.riscv .xor) ()
      let overflowOp ← CreateProg.operation (.riscv .xor)
          #[rhsSignOp.res[0]!, carryLikeOp.res[0]!] #[regType] overflowProps
      let satProps ← CreateProg.property (.riscv .xor) ()
      let satOp ← CreateProg.operation (.riscv .xor)
          #[sumSignOp.res[0]!, intMinOp.res[0]!] #[regType] satProps
      let selectOp ← signedSatSelect regType sumOp.res[0]! overflowOp.res[0]! satOp.res[0]!
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[selectOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- llvm.intr.sadd.sat.i64 -> LLVM's RV64+Zicond signed saturating-add sequence.
    Wrapped `add` + SADDO overflow `(rhs >>u 63) ^ (sum <s lhs)`
    (TargetLowering.cpp:12432 `expandAddSubSat`, overflow at 13072
    `expandSADDSUBO` add branch; sat endpoint `(sum >>s 63) ^ INT_MIN` at 12554). -/
def saddSat : Puddle.CompiledPattern OpCode := saddSat_pattern.compile

/-- llvm.intr.ssub.sat.i64 -> LLVM's RV64+Zicond signed saturating-sub sequence.
    Wrapped `sub` + SSUBO overflow `(lhs <s rhs) ^ (diff >>u 63)`
    (TargetLowering.cpp:12432 `expandAddSubSat`, overflow at 13082
    `expandSADDSUBO` sub branch; sat endpoint `(diff >>s 63) ^ INT_MIN` at 12554). -/
def ssubSat_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let lhsType ← MatchProg.type (Attr := TypeAttr)
      let rhsType ← MatchProg.type (Attr := TypeAttr)
      let resType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 64)
      let lhs ← MatchProg.value lhsType
      let rhs ← MatchProg.value rhsType
      let _ ← MatchProg.root (.llvm .intr__ssub__sat) #[lhs, rhs] #[resType]
      return (resType, lhs, rhs))
    (fun (resType, lhs, rhs) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let lCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[lhs] #[regType]
      let rCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[rhs] #[regType]
      let minusOneProps ← CreateProg.property (.riscv .li) (mkRISCVImm (-1))
      let minusOneOp ← CreateProg.operation (.riscv .li)
          #[] #[regType] minusOneProps
      let diffProps ← CreateProg.property (.riscv .sub) ()
      let diffOp ← CreateProg.operation (.riscv .sub)
          #[lCastOp.res[0]!, rCastOp.res[0]!] #[regType] diffProps
      let cmpProps ← CreateProg.property (.riscv .slt) ()
      let cmpOp ← CreateProg.operation (.riscv .slt)
          #[lCastOp.res[0]!, rCastOp.res[0]!] #[regType] cmpProps
      let diffSignBitProps ← CreateProg.property (.riscv .srli) (mkRISCVImm 63)
      let diffSignBitOp ← CreateProg.operation (.riscv .srli)
          #[diffOp.res[0]!] #[regType] diffSignBitProps
      let diffSignProps ← CreateProg.property (.riscv .srai) (mkRISCVImm 63)
      let diffSignOp ← CreateProg.operation (.riscv .srai)
          #[diffOp.res[0]!] #[regType] diffSignProps
      let intMinProps ← CreateProg.property (.riscv .slli) (mkRISCVImm 63)
      let intMinOp ← CreateProg.operation (.riscv .slli)
          #[minusOneOp.res[0]!] #[regType] intMinProps
      let overflowProps ← CreateProg.property (.riscv .xor) ()
      let overflowOp ← CreateProg.operation (.riscv .xor)
          #[cmpOp.res[0]!, diffSignBitOp.res[0]!] #[regType] overflowProps
      let satProps ← CreateProg.property (.riscv .xor) ()
      let satOp ← CreateProg.operation (.riscv .xor)
          #[diffSignOp.res[0]!, intMinOp.res[0]!] #[regType] satProps
      let selectOp ← signedSatSelect regType diffOp.res[0]! overflowOp.res[0]! satOp.res[0]!
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[selectOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- llvm.intr.ssub.sat.i64 -> LLVM's RV64+Zicond signed saturating-sub sequence.
    Wrapped `sub` + SSUBO overflow `(lhs <s rhs) ^ (diff >>u 63)`
    (TargetLowering.cpp:12432 `expandAddSubSat`, overflow at 13082
    `expandSADDSUBO` sub branch; sat endpoint `(diff >>s 63) ^ INT_MIN` at 12554). -/
def ssubSat : Puddle.CompiledPattern OpCode := ssubSat_pattern.compile

/-- llvm.intr.uadd.sat.i64 -> not rhs; minu lhs, not-rhs; add rhs.
    `uadd.sat(a,b) -> umin(a, ~b) + b` (TargetLowering.cpp:12462
    `expandAddSubSat`, UADDSAT/UMIN idiom). -/
def uaddSat_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let lhsType ← MatchProg.type (Attr := TypeAttr)
      let rhsType ← MatchProg.type (Attr := TypeAttr)
      let resType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 64)
      let lhs ← MatchProg.value lhsType
      let rhs ← MatchProg.value rhsType
      let _ ← MatchProg.root (.llvm .intr__uadd__sat) #[lhs, rhs] #[resType]
      return (resType, lhs, rhs))
    (fun (resType, lhs, rhs) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let lCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[lhs] #[regType]
      let rCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[rhs] #[regType]
      let notRhsProps ← CreateProg.property (.riscv .xori) (mkRISCVImm (-1))
      let notRhsOp ← CreateProg.operation (.riscv .xori)
          #[rCastOp.res[0]!] #[regType] notRhsProps
      let minuProps ← CreateProg.property (.riscv .minu) ()
      let minuOp ← CreateProg.operation (.riscv .minu)
          #[lCastOp.res[0]!, notRhsOp.res[0]!] #[regType] minuProps
      let addProps ← CreateProg.property (.riscv .add) ()
      let addOp ← CreateProg.operation (.riscv .add)
          #[minuOp.res[0]!, rCastOp.res[0]!] #[regType] addProps
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[addOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- llvm.intr.uadd.sat.i64 -> not rhs; minu lhs, not-rhs; add rhs.
    `uadd.sat(a,b) -> umin(a, ~b) + b` (TargetLowering.cpp:12462
    `expandAddSubSat`, UADDSAT/UMIN idiom). -/
def uaddSat : Puddle.CompiledPattern OpCode := uaddSat_pattern.compile

/-- llvm.intr.usub.sat.i64 -> maxu lhs, rhs; sub rhs.
    `usub.sat(a,b) -> umax(a, b) - b` (TargetLowering.cpp:12442
    `expandAddSubSat`, USUBSAT/UMAX idiom). -/
def usubSat_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let lhsType ← MatchProg.type (Attr := TypeAttr)
      let rhsType ← MatchProg.type (Attr := TypeAttr)
      let resType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 64)
      let lhs ← MatchProg.value lhsType
      let rhs ← MatchProg.value rhsType
      let _ ← MatchProg.root (.llvm .intr__usub__sat) #[lhs, rhs] #[resType]
      return (resType, lhs, rhs))
    (fun (resType, lhs, rhs) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let lCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[lhs] #[regType]
      let rCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[rhs] #[regType]
      let maxuProps ← CreateProg.property (.riscv .maxu) ()
      let maxuOp ← CreateProg.operation (.riscv .maxu)
          #[lCastOp.res[0]!, rCastOp.res[0]!] #[regType] maxuProps
      let subProps ← CreateProg.property (.riscv .sub) ()
      let subOp ← CreateProg.operation (.riscv .sub)
          #[maxuOp.res[0]!, rCastOp.res[0]!] #[regType] subProps
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[subOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- llvm.intr.usub.sat.i64 -> maxu lhs, rhs; sub rhs.
    `usub.sat(a,b) -> umax(a, b) - b` (TargetLowering.cpp:12442
    `expandAddSubSat`, USUBSAT/UMAX idiom). -/
def usubSat : Puddle.CompiledPattern OpCode := usubSat_pattern.compile

/-- llvm.intr.sshl.sat.i64 -> LLVM's RV64+Zicond signed saturating-shl sequence.
    `overflow = lhs != (lhs << rhs) >>s rhs`, saturate to
    `select(lhs<0, INT_MIN, INT_MAX)` folded to `(lhs >>s 63) ^ INT_MAX`
    (TargetLowering.cpp:12598 `expandShlSat`, signed branch at 12626-12632). -/
def sshlSat_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let lhsType ← MatchProg.type (Attr := TypeAttr)
      let rhsType ← MatchProg.type (Attr := TypeAttr)
      let resType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 64)
      let lhs ← MatchProg.value lhsType
      let rhs ← MatchProg.value rhsType
      let _ ← MatchProg.root (.llvm .intr__sshl__sat) #[lhs, rhs] #[resType]
      return (resType, lhs, rhs))
    (fun (resType, lhs, rhs) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let lCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[lhs] #[regType]
      let rCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[rhs] #[regType]
      let shiftedProps ← CreateProg.property (.riscv .sll) ()
      let shiftedOp ← CreateProg.operation (.riscv .sll)
          #[lCastOp.res[0]!, rCastOp.res[0]!] #[regType] shiftedProps
      let minusOneProps ← CreateProg.property (.riscv .li) (mkRISCVImm (-1))
      let minusOneOp ← CreateProg.operation (.riscv .li)
          #[] #[regType] minusOneProps
      let unshiftedProps ← CreateProg.property (.riscv .sra) ()
      let unshiftedOp ← CreateProg.operation (.riscv .sra)
          #[shiftedOp.res[0]!, rCastOp.res[0]!] #[regType] unshiftedProps
      let signProps ← CreateProg.property (.riscv .srai) (mkRISCVImm 63)
      let signOp ← CreateProg.operation (.riscv .srai)
          #[lCastOp.res[0]!] #[regType] signProps
      let intMaxProps ← CreateProg.property (.riscv .srli) (mkRISCVImm 1)
      let intMaxOp ← CreateProg.operation (.riscv .srli)
          #[minusOneOp.res[0]!] #[regType] intMaxProps
      let overflowProps ← CreateProg.property (.riscv .xor) ()
      let overflowOp ← CreateProg.operation (.riscv .xor)
          #[lCastOp.res[0]!, unshiftedOp.res[0]!] #[regType] overflowProps
      let satProps ← CreateProg.property (.riscv .xor) ()
      let satOp ← CreateProg.operation (.riscv .xor)
          #[signOp.res[0]!, intMaxOp.res[0]!] #[regType] satProps
      let selectOp ← signedSatSelect regType shiftedOp.res[0]! overflowOp.res[0]! satOp.res[0]!
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[selectOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- llvm.intr.sshl.sat.i64 -> LLVM's RV64+Zicond signed saturating-shl sequence.
    `overflow = lhs != (lhs << rhs) >>s rhs`, saturate to
    `select(lhs<0, INT_MIN, INT_MAX)` folded to `(lhs >>s 63) ^ INT_MAX`
    (TargetLowering.cpp:12598 `expandShlSat`, signed branch at 12626-12632). -/
def sshlSat : Puddle.CompiledPattern OpCode := sshlSat_pattern.compile

/-- llvm.intr.ushl.sat.i64 -> LLVM's RV64 unsigned saturating-shl sequence.
    `overflow = lhs != (lhs << rhs) >>u rhs`, saturate to all-ones;
    the `select(overflow, ~0, shifted)` becomes the `sltiu`/`addi`/`or`
    mask idiom (TargetLowering.cpp:12598 `expandShlSat`, unsigned branch
    at 12630-12633). -/
def ushlSat_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let lhsType ← MatchProg.type (Attr := TypeAttr)
      let rhsType ← MatchProg.type (Attr := TypeAttr)
      let resType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 64)
      let lhs ← MatchProg.value lhsType
      let rhs ← MatchProg.value rhsType
      let _ ← MatchProg.root (.llvm .intr__ushl__sat) #[lhs, rhs] #[resType]
      return (resType, lhs, rhs))
    (fun (resType, lhs, rhs) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let lCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[lhs] #[regType]
      let rCastOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[rhs] #[regType]
      let shiftedProps ← CreateProg.property (.riscv .sll) ()
      let shiftedOp ← CreateProg.operation (.riscv .sll)
          #[lCastOp.res[0]!, rCastOp.res[0]!] #[regType] shiftedProps
      let unshiftedProps ← CreateProg.property (.riscv .srl) ()
      let unshiftedOp ← CreateProg.operation (.riscv .srl)
          #[shiftedOp.res[0]!, rCastOp.res[0]!] #[regType] unshiftedProps
      let lostBitsProps ← CreateProg.property (.riscv .xor) ()
      let lostBitsOp ← CreateProg.operation (.riscv .xor)
          #[lCastOp.res[0]!, unshiftedOp.res[0]!] #[regType] lostBitsProps
      let noOverflowProps ← CreateProg.property (.riscv .sltiu) (mkRISCVImm 1)
      let noOverflowOp ← CreateProg.operation (.riscv .sltiu)
          #[lostBitsOp.res[0]!] #[regType] noOverflowProps
      let overflowMaskProps ← CreateProg.property (.riscv .addi) (mkRISCVImm (-1))
      let overflowMaskOp ← CreateProg.operation (.riscv .addi)
          #[noOverflowOp.res[0]!] #[regType] overflowMaskProps
      let orProps ← CreateProg.property (.riscv .or) ()
      let orOp ← CreateProg.operation (.riscv .or)
          #[overflowMaskOp.res[0]!, shiftedOp.res[0]!] #[regType] orProps
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[orOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- llvm.intr.ushl.sat.i64 -> LLVM's RV64 unsigned saturating-shl sequence.
    `overflow = lhs != (lhs << rhs) >>u rhs`, saturate to all-ones;
    the `select(overflow, ~0, shifted)` becomes the `sltiu`/`addi`/`or`
    mask idiom (TargetLowering.cpp:12598 `expandShlSat`, unsigned branch
    at 12630-12633). -/
def ushlSat : Puddle.CompiledPattern OpCode := ushlSat_pattern.compile

/-- llvm.intr.abs.i64 -> `max(x, -x)` via Zbb `neg`/`max`.
    LLVM's RV64+Zbb lowering (`neg a1, a0; max a0, a0, a1`). The `neg` wraps
    `intMin` back to `intMin`, so this is correct for both the
    `is_int_min_poison` and non-poison forms of the intrinsic. -/
def abs_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let valType ← MatchProg.type (Attr := TypeAttr)
      let resType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 64)
      let val ← MatchProg.value valType
      let _ ← MatchProg.root (.llvm .intr__abs) #[val] #[resType]
      return (resType, val))
    (fun (resType, val) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let castOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[val] #[regType]
      let negProps ← CreateProg.property (.riscv .neg) ()
      let negOp ← CreateProg.operation (.riscv .neg)
          #[castOp.res[0]!] #[regType] negProps
      let maxProps ← CreateProg.property (.riscv .max) ()
      let maxOp ← CreateProg.operation (.riscv .max)
          #[castOp.res[0]!, negOp.res[0]!] #[regType] maxProps
      let castBackOp ← CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[maxOp.res[0]!] #[resType]
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- llvm.intr.abs.i64 -> `max(x, -x)` via Zbb `neg`/`max` (see `abs_pattern`). -/
def abs : Puddle.CompiledPattern OpCode := abs_pattern.compile

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
def lowerFshConst (rotateLeft : Bool) (bw : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let valType ← MatchProg.type (Attr := TypeAttr)
      let amtType ← MatchProg.type (Attr := IntegerType)
      let resType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = bw)
      let val ← MatchProg.value valType
      let amtOp ← MatchProg.operation (.gmir .g_constant) #[] #[amtType]
      let _ ← MatchProg.root
          (.llvm (if rotateLeft then .intr__fshl else .intr__fshr))
          #[val, val, amtOp.res[0]!] #[resType]
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

/-- llvm.intr.fshl with identical data operands and a constant shift amount is a
    constant rotate-left. There is no `roli`, so (like LLVM) it lowers to
    `riscv.rori` with the negated immediate `(64 - amt) mod 64`. -/
def fshlConst64 : Puddle.CompiledPattern OpCode := (lowerFshConst true 64).compile

def fshlConst32 : Puddle.CompiledPattern OpCode := (lowerFshConst true 32).compile

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

/--
  Lower `llvm.intr.memcpy` and `llvm.intr.memset`. A constant length that takes at most
  `memMaxStores` accesses is expanded into loads and stores; anything else becomes a
  `riscv_cf.call` to the C library function. Accesses are never wider than the known
  alignment, so the expansion never introduces a misaligned access.
-/
def memIntrinsic_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let isMemset := op.getOpType! ctx.raw = Llvm.intr__memset
  if !isMemset && op.getOpType! ctx.raw ≠ Llvm.intr__memcpy then return (ctx, none)
  let props : LLVMMemIntrinsicProperties :=
    if isMemset then op.getProperties! ctx.raw Llvm.intr__memset
    else op.getProperties! ctx.raw Llvm.intr__memcpy
  let operands := op.getOperands! ctx.raw
  /- `src` is the source pointer of a `memcpy` and the fill byte of a `memset`. -/
  let (dst, src, len) := (operands[0]!, operands[1]!, operands[2]!)
  let align := if isMemset then memArgAlign props 0
    else min (memArgAlign props 0) (memArgAlign props 1)
  let accesses? : Option (Array (Nat × Nat)) := do
    let len ← matchGConstantIntVal len ctx.raw
    guard (0 ≤ len ∧ len ≤ 8 * memMaxStores)
    let accesses := memAccesses len.toNat align
    guard (accesses.size ≤ memMaxStores)
    return accesses
  let (ctx, dstCast) ← castToRegLocal ctx dst
  let dstReg := dstCast.getResult 0
  match accesses? with
  | none =>
    let (ctx, srcCast) ← castToRegLocal ctx src
    let (ctx, lenCast) ← castToRegLocal ctx len
    /- `memset` takes its fill byte as an `int`, so zero-extend the `i8`. -/
    let (ctx, argOps) ← if isMemset then do
        let (ctx, ext) ← createRISCVUnitLocal ctx .zextb rfl #[srcCast.getResult 0]
        pure (ctx, #[srcCast, ext])
      else pure (ctx, #[srcCast])
    let callee : FlatSymbolRefAttr := ⟨if isMemset then "@memset" else "@memcpy"⟩
    let (ctx, callOp) ← WfRewriter.createOp! ctx Riscv_Cf.call #[]
        #[dstReg, argOps.back!.getResult 0, lenCast.getResult 0] #[] #[]
        (RISCVCallProperties.mk (some callee)) none
    return (ctx, some (#[dstCast] ++ argOps ++ #[lenCast, callOp], #[]))
  | some accesses =>
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

/-- `llvm.intr.memcpy` / `llvm.intr.memset` -> loads and stores, or a libcall. -/
def memIntrinsic (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite memIntrinsic_local rewriter op opInBounds

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

def gmirAdd : Puddle.CompiledPattern OpCode := gmirAdd_pattern.compile
def gmirSub : Puddle.CompiledPattern OpCode := gmirSub_pattern.compile
def gmirTrunc : Puddle.CompiledPattern OpCode := gmirTrunc_pattern.compile
def gmirAnyext : Puddle.CompiledPattern OpCode := gmirAnyext_pattern.compile
def gmirShl : Puddle.CompiledPattern OpCode := gmirShl_pattern.compile
def gmirLshr : Puddle.CompiledPattern OpCode := gmirLshr_pattern.compile
def gmirAshr : Puddle.CompiledPattern OpCode := gmirAshr_pattern.compile

/--
  RISC-V lowerings with Puddle for the integer-extension operations (`sext`/`zext`): match a
  single-operand extension op whose operand has a fixed legal integer width `opBw` (`8`, `16`,
  or `32`, see `isLegalExtOpWidth`) and whose result is a strictly wider integer type of width at
  most 64 (a 64-bit register cannot represent wider results, so e.g. `sext i8 to i128` is left
  unselected; unlike `opBw`, the result width is matched generically rather than enumerated), cast
  the operand to a register, apply the byte/halfword/word extension op matching `opBw`, and cast the
  result back to the (generically-matched) result type. Only extensions that
  `riscv64LegalizerInfo` considers legal are selected.
-/
def lowerExt (srcOp : GMIR) (opBw : Nat) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp)) : Pattern OpCode :=
  lowerUnary (.gmir srcOp) opBw riscvOp riscvProps fun opType resType properties => do
    -- A 64-bit register cannot hold a wider result.
    MatchProg.matchNative resType fun t => (t.val.bitwidthOfType).any (· ≤ 64)
    matchLegal srcOp resType properties (type₁ := opType)

/-- `gmir.g_sext` (`i8` operand) -> `riscv.sextb`. -/
def sext8_pattern : Pattern OpCode := lowerExt .g_sext 8 .sextb ()

/-- `gmir.g_sext` (`i16` operand) -> `riscv.sexth`. -/
def sext16_pattern : Pattern OpCode := lowerExt .g_sext 16 .sexth ()

/-- `gmir.g_sext` (`i32` operand) -> `riscv.sextw`. -/
def sext32_pattern : Pattern OpCode := lowerExt .g_sext 32 .sextw ()

/-- `gmir.g_zext` (`i8` operand) -> `riscv.zextb`. -/
def zext8_pattern : Pattern OpCode := lowerExt .g_zext 8 .zextb ()

/-- `gmir.g_zext` (`i16` operand) -> `riscv.zexth`. -/
def zext16_pattern : Pattern OpCode := lowerExt .g_zext 16 .zexth ()

/-- `gmir.g_zext` (`i32` operand) -> `riscv.zextw`. -/
def zext32_pattern : Pattern OpCode := lowerExt .g_zext 32 .zextw ()

/--
  gmir.g_sext %x `i8`  to `i32` -> riscv.sextb %x
  gmir.g_sext %x `i8`  to `i64` -> riscv.sextb %x
  gmir.g_sext %x `i16` to `i64` -> riscv.sexth %x
  gmir.g_sext %x `i16` to `i32` -> riscv.sexth %x
  gmir.g_sext %x `i32` to `i64` -> riscv.sextw %x
-/
def sext8 : Puddle.CompiledPattern OpCode := sext8_pattern.compile

def sext16 : Puddle.CompiledPattern OpCode := sext16_pattern.compile

def sext32 : Puddle.CompiledPattern OpCode := sext32_pattern.compile

/--
  gmir.g_zext %x `i8`  to `i32` -> riscv.zextb %x
  gmir.g_zext %x `i8`  to `i64` -> riscv.zextb %x
  gmir.g_zext %x `i16` to `i64` -> riscv.zexth %x
  gmir.g_zext %x `i16` to `i32` -> riscv.zexth %x
  gmir.g_zext %x `i32` to `i64` -> riscv.zextw %x
-/
def zext8 : Puddle.CompiledPattern OpCode := zext8_pattern.compile

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

/-! # Pass implementation -/

def ISelPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  /- Early loop: address folding, fixed stack allocations and memory intrinsic
     expansion must inspect constants before the per-op lowerings consume them. -/
  let early := RewritePattern.GreedyRewritePattern <|
    #[lifetimeStart.run, lifetimeEnd.run, alloca, memIntrinsic] ++ load.map (·.run) ++
    store.map (·.run) ++ #[selectCzeroeqz.run, selectCzeronez.run,
    fshlConst64.run, fshlConst32.run, fshrConst64.run, fshrConst32.run]
  let ctx ← match RewritePattern.applyInContext early ctx with
  | none => throw "Error while applying early memory-lowering patterns"
  | some ctx => pure ctx
  /- Main loop: the existing per-op lowerings. -/
  let pattern := RewritePattern.GreedyRewritePattern <|
    #[selectGeneral.run,
    ctlz32.run, ctlz64.run, cttz32.run, cttz64.run, ctpop32.run, ctpop64.run, bswap64.run, bswap32.run, bitreverse64.run, bitreverse32.run,
    constant.run, addressof] ++
    #[
    sext32.run, sext16.run, sext8.run, zext32.run, zext16.run, zext8.run, trunc.run,
    bitcast.run] ++
    load.map (·.run) ++ getelementptr.map (·.run) ++ store.map (·.run) ++ #[
    smax64.run, smax32.run, smin64.run, smin32.run, umax.run, umin.run, saddSat.run, ssubSat.run, uaddSat.run, usubSat.run, sshlSat.run, ushlSat.run, abs.run,
    fshl64.run, fshl32.run, fshr64.run, fshr32.run, fshlGeneral64.run, fshlGeneral32.run, fshrGeneral64.run, fshrGeneral32.run,
    poisonConst.run, zeroConst.run, freeze.run,
    gmirAdd.run, gmirSub.run, gmirTrunc.run, gmirAnyext.run, gmirShl.run, gmirLshr.run, gmirAshr.run,
    gmirAnd.run, gmirOr.run, gmirXor.run,
    gmirMul.run, gmirSdiv.run, gmirUdiv.run, gmirSrem.run, gmirUrem.run,
    gmirConstant.run] ++
    gmirIcmp.map (·.run)
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying main instruction-selection patterns"
  | some ctx => pure ctx

public def IselRISCV64 : Pass OpCode :=
  { name := "isel-riscv64"
    description :=
      "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := fun _ => ISelPass.impl }
