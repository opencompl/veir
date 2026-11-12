module

public import Veir.Pass
public import Veir.PatternRewriter.Puddle.Definitions
public import Veir.Passes.StrictDriver
import Veir.Passes.Legalization.LegalizerInfo
import Veir.DataLayout.RISCV64
import Veir.Interfaces.ConstantLikeInterfaces
import Veir.Interfaces.FunctionInterfaces
import Veir.Passes.InstructionSelection.Common
import Veir.Passes.LLVMToGMIR.Branches
import Veir.Passes.Matching
import Veir.Passes.CastsReconciliation.Reconciliation
import Veir.Passes.DCE.dce
import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution

namespace Veir

/-!
  # LLVMToGMIR pass

  This file replicates LLVM's GlobalISel IRTranslator pass.

  All properties on LLVM IR operations are carried over to gMIR, similar to
  upstream's `MachineInstr::copyFlagsFromInstruction`

  This lowering differs from the upstream implementation in the following ways:
  - Upstream converts all poison values to undef values; we only have poison but no undef, and
    translate `llvm.mlir.poison` to `g_poison`, which LLVM is introducing to replace undef.
  - Some information represented as operation properties (e.g. the icmp condition code) is
    represented as special operands in upstream gMIR. This includes all operands with type `immediate`
    or `unknown` in upstream's llvm/include/llvm/Target/GenericOpcodes.td.
  - GEP indices are normalized here, but GEP address arithmetic remains in the LLVM dialect
    until instruction selection. The currently supported pointer index width is 64 bits.
  - Only naturally aligned loads of `i8`/`i16`/`i32`/`i64` and pointers become `g_load`; the
    others stay in the LLVM dialect (see `loadMemOperand?`).
    TODO: Translate the others once the legalizer can split them, as LLVM's `lowerLoad`.
  - A static alloca is lowered directly to `riscv_stack.alloca` rather than to a frame index,
    using the RISC-V 64 data layout; this is the one target-specific lowering here.
-/

/-! ## Lowering Patterns -/

/--
  GMIR lowerings with Puddle for binary operations on values that gMIR can represent, i.e. whose
  types have an `LLT`. (This is intended to guard against matching byte type operands.)
-/
def lowerBinop (lOp : Llvm) (gOp : GMIR)
    (h : propertiesOf (OpCode.llvm lOp) = propertiesOf (OpCode.gmir gOp) := by rfl) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let lhsType ← Puddle.MatchProg.type (Attr := TypeAttr) fun t => (LLT.ofType? t).isSome
      let rhsType ← Puddle.MatchProg.type (Attr := TypeAttr) fun t => (LLT.ofType? t).isSome
      let resultType ← Puddle.MatchProg.type (Attr := TypeAttr) fun t => (LLT.ofType? t).isSome
      let lhs ← Puddle.MatchProg.value lhsType
      let rhs ← Puddle.MatchProg.value rhsType
      let root ← Puddle.MatchProg.root (.llvm lOp) #[lhs, rhs] #[resultType]
      return (resultType, lhs, rhs, root))
    (fun (resultType, lhs, rhs, root) => do
      let props ← Puddle.CreateProg.applyNative root.properties
                    (fun p => some (cast h p))
      let newOp ← Puddle.CreateProg.operation (.gmir gOp) #[lhs, rhs] #[resultType] (.inr props)
      return newOp)
    (fun newOp => newOp)















/--
  GMIR lowerings with Puddle for unary operations on values that gMIR can represent, whose
  properties satisfy `guard` and are converted with `convert`.
-/
def lowerUnop (lOp : Llvm) (gOp : GMIR)
    (convert : propertiesOf (OpCode.llvm lOp) → propertiesOf (OpCode.gmir gOp))
    (guard : propertiesOf (OpCode.llvm lOp) → Bool := fun _ => true) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let operandType ← Puddle.MatchProg.type (Attr := TypeAttr) fun t => (LLT.ofType? t).isSome
      let resultType ← Puddle.MatchProg.type (Attr := TypeAttr) fun t => (LLT.ofType? t).isSome
      let operand ← Puddle.MatchProg.value operandType
      let root ← Puddle.MatchProg.root (.llvm lOp) #[operand] #[resultType]
      Puddle.MatchProg.matchNative root.properties guard
      return (resultType, operand, root))
    (fun (resultType, operand, root) => do
      let props ← Puddle.CreateProg.applyNative root.properties (fun p => some (convert p))
      Puddle.CreateProg.operation (.gmir gOp) #[operand] #[resultType] (.inr props))
    (fun newOp => newOp)

/- As in LLVM, a `ctlz`/`cttz` whose zero input is poison becomes a `_zero_poison` count. -/

/--
  GMIR lowerings with Puddle for the bit counts, whose result has the type of their operand, as in
  LLVM. gMIR computes the count at the width of the result type, so the matcher ties it to the
  operand's type.
-/
def lowerCount (lOp : Llvm) (gOp : GMIR)
    (convert : propertiesOf (OpCode.llvm lOp) → propertiesOf (OpCode.gmir gOp))
    (guard : propertiesOf (OpCode.llvm lOp) → Bool := fun _ => true) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let type ← Puddle.MatchProg.type (Attr := IntegerType)
      let operand ← Puddle.MatchProg.value type
      let root ← Puddle.MatchProg.root (.llvm lOp) #[operand] #[type]
      Puddle.MatchProg.matchNative root.properties guard
      return (type, operand, root))
    (fun (type, operand, root) => do
      let props ← Puddle.CreateProg.applyNative root.properties (fun p => some (convert p))
      Puddle.CreateProg.operation (.gmir gOp) #[operand] #[type] (.inr props))
    (fun newOp => newOp)











/--
  `llvm.icmp` -> `g_icmp` on an `i1` result, as LLVM computes it. gMIR computes the comparison at
  the width of the result type.
-/
def lowerIcmp : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let lhsType ← Puddle.MatchProg.type (Attr := TypeAttr) fun t => (LLT.ofType? t).isSome
      let rhsType ← Puddle.MatchProg.type (Attr := TypeAttr) fun t => (LLT.ofType? t).isSome
      let resultType ← Puddle.MatchProg.type (Attr := IntegerType) (·.bitwidth = 1)
      let lhs ← Puddle.MatchProg.value lhsType
      let rhs ← Puddle.MatchProg.value rhsType
      let root ← Puddle.MatchProg.root (.llvm .icmp) #[lhs, rhs] #[resultType]
      return (resultType, lhs, rhs, root))
    (fun (resultType, lhs, rhs, root) => do
      let props ← Puddle.CreateProg.applyNative
          (Outputs := Puddle.Handle OpCode (.prop (.gmir .g_icmp))) root.properties some
      Puddle.CreateProg.operation (.gmir .g_icmp) #[lhs, rhs] #[resultType] (.inr props))
    (fun newOp => newOp)

/- LLVM translates `abs` to `G_ABS` and drops `is_int_min_poison`, which `g_abs` refines. -/







/--
  `llvm.intr.fshl`/`llvm.intr.fshr` -> `g_fshl`/`g_fshr`, except for `i32` and `i64`: instruction
  selection still matches those widths in the LLVM dialect (as rotates or LLVM's
  `expandFunnelShift`), while the legalizer lowers the other widths to shifts.
-/
def lowerFunnelShiftIntrinsic (lOp : Llvm) (gOp : GMIR) : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let type ← Puddle.MatchProg.type (Attr := IntegerType)
        fun t => t.bitwidth ≠ 32 && t.bitwidth ≠ 64
      let x ← Puddle.MatchProg.value type
      let y ← Puddle.MatchProg.value type
      let z ← Puddle.MatchProg.value type
      let _ ← Puddle.MatchProg.root (.llvm lOp) #[x, y, z] #[type]
      return (type, x, y, z))
    (fun (type, x, y, z) => Puddle.CreateProg.operation (.gmir gOp) #[x, y, z] #[type])
    (fun newOp => newOp)



/--
  `llvm.select` -> `g_select`, as in LLVM's `IRTranslator::translateSelect`. The `i1` condition
  selects as `g_select` does, see `GMIR.selectNonzero_one`. The values are integers or pointers.
-/
def lowerSelect : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let condType ← Puddle.MatchProg.type (Attr := IntegerType) (·.bitwidth = 1)
      let type ← Puddle.MatchProg.type (Attr := TypeAttr) fun t => (LLT.ofType? t).isSome
      let cond ← Puddle.MatchProg.value condType
      let tval ← Puddle.MatchProg.value type
      let fval ← Puddle.MatchProg.value type
      let _ ← Puddle.MatchProg.root (.llvm .select) #[cond, tval, fval] #[type]
      return (type, cond, tval, fval))
    (fun (type, cond, tval, fval) =>
      Puddle.CreateProg.operation (.gmir .g_select) #[cond, tval, fval] #[type])
    (fun newOp => newOp)


/--
  GMIR lowerings with Puddle for integer casts.
-/
def lowerIntegerCast (lOp : Llvm) (gOp : GMIR)
    (h : propertiesOf (OpCode.llvm lOp) = propertiesOf (OpCode.gmir gOp) := by rfl) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let operandType ← Puddle.MatchProg.type (Attr := IntegerType)
      let resultType ← Puddle.MatchProg.type (Attr := IntegerType)
      let operand ← Puddle.MatchProg.value operandType
      let root ← Puddle.MatchProg.root (.llvm lOp) #[operand] #[resultType]
      return (resultType, operand, root))
    (fun (resultType, operand, root) => do
      let props ← Puddle.CreateProg.applyNative root.properties
                    (fun p => some (cast h p))
      let newOp ← Puddle.CreateProg.operation (.gmir gOp) #[operand] #[resultType] (.inr props)
      return newOp)
    (fun newOp => newOp)




/--
  Normalize dynamic GEP indices to the current 64-bit pointer index type, as in
  LLVM's `IRTranslator::translateGetElementPtr`: sign-extend narrower indices
  and truncate wider ones before scaling them. Rewrite a dynamic index that is a
  constant as an `i64` constant instead. Preserve constant indices and GEP flags. Plain truncation may refine poison from a violated GEP no-wrap flag.
-/
private def normalizeGEPIndices : LocalRewritePattern OpCode := fun ctx op => do
  let some (ptr, indices, props) := matchGetelementptrIndices op ctx.raw | return (ctx, none)
  let mut ctx := ctx
  let mut ops := #[]
  let mut operands := #[ptr]
  for index in indices do
    if let .integerType type := (index.getType! ctx.raw).val then
      if type.bitwidth ≠ 0 && type.bitwidth ≠ 64 then
        /- Fold a constant index into an `i64` `g_constant`, so that load/store selection can
           still fold it into the access's immediate offset. -/
        let constant := matchConstantIntVal index ctx.raw <|> matchGConstantIntVal index ctx.raw
        let (ctx', castOp) ← if let some value := constant then
            WfRewriter.createOp! ctx GMIR.g_constant #[IntegerType.signless 64] #[] #[] #[]
                (GMIRConstantProperties.mk (.ofInt (BitVec.ofInt 64 value).toInt (.signless 64)))
                none
          else if type.bitwidth < 64 then
            WfRewriter.createOp! ctx GMIR.g_sext #[IntegerType.signless 64]
                #[index] #[] #[] () none
          else
            WfRewriter.createOp! ctx GMIR.g_trunc #[IntegerType.signless 64]
                #[index] #[] #[] (NswNuwProperties.mk false false) none
        ctx := ctx'
        ops := ops.push castOp
        operands := operands.push (castOp.getResult 0)
        continue
    operands := operands.push index
  if ops.isEmpty then return (ctx, none)
  let (ctx', gep) ← WfRewriter.createOp! ctx Llvm.getelementptr (op.getResultTypes! ctx.raw)
      operands #[] #[] props none
  return (ctx', some (ops.push gep, #[gep.getResult 0]))

/--
  The properties of the fixed RISC-V stack object for an `llvm.alloca` with properties `props`
  of `count` elements, where `count` is the value of an integer constant of type `countType`, or
  `none` if its size or alignment does not fit the object. The checks on the alloca's opcode,
  operand and result counts, `inalloca`, result type, and position in the entry block of its
  function are made by `lowerStaticAllocaOf`.
-/
public def staticAllocaProperties? (countType : TypeAttr) (count : Int)
    (props : AllocaProperties) : Option RISCVStackAllocaProperties := do
  let .integerType countWidth := countType.val | none
  let count := (BitVec.ofInt countWidth.bitwidth count).toNat
  let some layout := DataLayout.riscv64.query props.elem_type.val | none
  let size := count * layout.allocSize
  /- Do not silently wrap the fixed object's size to a signed 64-bit value. -/
  if size >= 2 ^ 63 then none
  let alignment : Int := if props.alignment.value = 0 then layout.preferredAlignment
    else props.alignment.value
  if !isValidLLVMAlignment alignment || alignment >= 2 ^ 63 then none
  return { size := BitVec.ofNat 64 size
           alignment := BitVec.ofInt 64 alignment }

/-- Whether `op` is in the entry block of a function. -/
public def inEntryBlock (ctx : IRContext OpCode) (op : OperationPtr) : Option Unit := do
  let some parentOp := op.getParentOp! ctx | none
  let some funcOp := FunctionOp.of? parentOp ctx | none
  let some entry := funcOp.getEntryBlock? | none
  guard (op.getParent! ctx = some entry)

/--
  Lower a constant-count entry-block allocation to a fixed RISC-V stack object, as
  `IRTranslator` turns a static alloca into a frame index. The count is the `cstOp` constant
  whose value `countOf` reads: an `llvm.mlir.constant`, or the `g_constant` that
  `lowerIntegerConstant` has already made of it. Dynamic allocations and `inalloca` need
  additional stack-lifetime support in the backend. This must run before legalization, which can
  hide a narrow constant count behind `g_trunc`.
-/
public def lowerStaticAllocaOf (cstOp : OpCode)
    (countOf : propertiesOf cstOp → Option Int) : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let countType ← Puddle.MatchProg.type (Attr := IntegerType)
      let countOp ← Puddle.MatchProg.operation cstOp #[] #[countType]
          fun props => (countOf props).isSome
      let resultType ← Puddle.MatchProg.type (Attr := TypeAttr)
          fun t => t.val matches .llvmPointerType _
      let root ← Puddle.MatchProg.root (.llvm .alloca) #[countOp.res[0]!] #[resultType]
          fun props => !props.inalloca
      /- The allocation is static: it is in the entry block of its function. -/
      let () ← Puddle.MatchProg.inspectOperation (Outputs := Unit) root.op inEntryBlock
      /- Its size and alignment fit a fixed stack object. -/
      Puddle.MatchProg.matchNative (countType, countOp.properties, root.properties)
          fun (countType, count, props) =>
            ((countOf count).bind (staticAllocaProperties? countType · props)).isSome
      return (resultType, countType, countOp.properties, root.properties))
    (fun (resultType, countType, count, props) => do
      let stackProps ← Puddle.CreateProg.applyNative
          (Outputs := Puddle.Handle OpCode (.prop (.riscv_stack .alloca))) (countType, count, props)
          fun (countType, count, props) =>
            (countOf count).bind (staticAllocaProperties? countType · props)
      let regType ← Puddle.CreateProg.type (RegisterType.mk none)
      let stackOp ← Puddle.CreateProg.operation (.riscv_stack .alloca) #[] #[regType]
          (.inr stackProps)
      Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[stackOp.res[0]!] #[resultType])
    (fun castBackOp => castBackOp)

/-- `lowerStaticAllocaOf`, counted by an `llvm.mlir.constant`. -/
public def lowerStaticAlloca_pattern : Puddle.Pattern OpCode :=
  lowerStaticAllocaOf (.llvm .mlir__constant) fun props =>
    match props.value with
    | .integer value => some value.value
    | _ => none

/-- `lowerStaticAllocaOf`, counted by the `g_constant` that `lowerIntegerConstant` made. -/
public def lowerStaticAllocaGMIR_pattern : Puddle.Pattern OpCode :=
  lowerStaticAllocaOf (.gmir .g_constant) fun props => some props.value.value

/-- `lowerStaticAllocaOf`, counted by an `arith.constant`. -/
public def lowerStaticAllocaArith_pattern : Puddle.Pattern OpCode :=
  lowerStaticAllocaOf (.arith .constant) fun props =>
    match props with
    | .int value => some value.value
    | _ => none

/-- `lowerStaticAllocaOf`, counted by an `llvm.mlir.zero`. -/
public def lowerStaticAllocaZero_pattern : Puddle.Pattern OpCode :=
  lowerStaticAllocaOf (.llvm .mlir__zero) fun _ => some 0

/--
  The memory operand of the `g_load` for an `llvm.load` of `type`, if it is a naturally aligned load
  of an `i8`, `i16`, `i32`, `i64` or pointer (see `memAccessWidth?`). A missing alignment is the
  ABI one. Byte loads are not translated, since a `g_load` would lose their per-bit poison (LLVM
  lowers them to `G_LOAD` anyway, see LangRef's byte type). They were not selected from our LLVM
  dialect either.
-/
def loadMemOperand? (type : TypeAttr) (props : LoadProperties) : Option MachineMemOperand := do
  let width ← memAccessWidth? type
  -- Only atomic loads have a `syncscope`; we do not model them.
  guard props.syncscope.isNone
  let alignment ← if props.alignment.value = 0
    then (DataLayout.riscv64.query type.val).map (·.abiAlignment)
    else some props.alignment.value.toNat
  guard (width ≤ alignment)
  return { size := .ofNat 64 (8 * width), alignment := .ofNat 64 alignment,
           volatile_ := props.volatile_, nontemporal := props.nontemporal,
           invariant := props.invariant }

/-- `llvm.load` -> `gmir.g_load`, for the loads `loadMemOperand?` accepts. -/
def lowerLoad_pattern : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let addrType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let resultType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let addr ← Puddle.MatchProg.value addrType
      let root ← Puddle.MatchProg.root (.llvm .load) #[addr] #[resultType]
      Puddle.MatchProg.matchNative (resultType, root.properties)
          fun (type, props) => (loadMemOperand? type props).isSome
      return (resultType, addr, root.properties))
    (fun (resultType, addr, props) => do
      let mmo ← Puddle.CreateProg.applyNative
          (Outputs := Puddle.Handle OpCode (.prop (.gmir .g_load))) (resultType, props)
          fun (type, props) => loadMemOperand? type props
      Puddle.CreateProg.operation (.gmir .g_load) #[addr] #[resultType] mmo)
    (fun load => load)


/-- `llvm.mlir.constant` (integer) -> `gmir.g_constant`. -/
def lowerIntegerConstant : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let resultType ← Puddle.MatchProg.type (Attr := IntegerType)
      let root ← Puddle.MatchProg.root (.llvm .mlir__constant) #[] #[resultType]
          (fun props => props.value matches .integer _)
      return (resultType, root))
    (fun (resultType, root) => do
      let props ← Puddle.CreateProg.applyNative root.properties fun props =>
        match props.value with
        | .integer value => some (GMIRConstantProperties.mk value)
        | _ => none
      Puddle.CreateProg.operation (.gmir .g_constant) #[] #[resultType] (.inr props))
    (fun newOp => newOp)


/--
  `llvm.mlir.poison` (integer or pointer) -> `gmir.g_poison`, as LLVM's IRTranslator turns poison
  of any type into `G_IMPLICIT_DEF`. Byte poison is translated by `lowerBytePoison`.
-/
def lowerPoison : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let resultType ← Puddle.MatchProg.type (Attr := TypeAttr) fun t => (LLT.ofType? t).isSome
      let _ ← Puddle.MatchProg.root (.llvm .mlir__poison) #[] #[resultType]
      return resultType)
    (fun resultType => Puddle.CreateProg.operation (.gmir .g_poison) #[] #[resultType])
    (fun newOp => newOp)


/--
  The integer type with the same width as the byte type `type`.
  Returns `none` if `type` is not a byte type.
-/
def TypeAttr.intOfByte? (type : TypeAttr) : Option TypeAttr := do
  let type ← type.cast? LLVM.ByteType
  return IntegerType.signless type.bitwidth

/--
  `lOp` on bytes -> `gOp` on integers of the same widths, between `builtin.unrealized_conversion_cast`s.
  LLVM converts all byte types to integer types of the same width when translating to gMIR
  (see `getLLTForType`); this mirrors that conversion. The properties are converted with `convert`.
-/
def lowerUnaryByteOp (lOp : Llvm) (gOp : GMIR)
    (convert : propertiesOf (OpCode.llvm lOp) → propertiesOf (OpCode.gmir gOp)) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let operandType ← Puddle.MatchProg.type (Attr := LLVM.ByteType)
      let resultType ← Puddle.MatchProg.type (Attr := LLVM.ByteType)
      let operand ← Puddle.MatchProg.value operandType
      let root ← Puddle.MatchProg.root (.llvm lOp) #[operand] #[resultType]
      return (operandType, resultType, operand, root))
    (fun (operandType, resultType, operand, root) => do
      let intOperandType ← Puddle.CreateProg.applyNative (Outputs := Puddle.Handle OpCode .type)
          operandType TypeAttr.intOfByte?
      let intResultType ← Puddle.CreateProg.applyNative (Outputs := Puddle.Handle OpCode .type)
          resultType TypeAttr.intOfByte?
      let castOp ← Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[operand] #[intOperandType]
      let props ← Puddle.CreateProg.applyNative root.properties (fun p => some (convert p))
      let newOp ← Puddle.CreateProg.operation (.gmir gOp) #[castOp.res[0]!]
          #[intResultType] (.inr props)
      Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast) #[newOp.res[0]!]
          #[resultType])
    (fun castBackOp => castBackOp)

/--
  `llvm.mlir.poison` (byte) -> `gmir.g_poison` on the integer of the same width, cast back to the
  byte type, as in `lowerUnaryByteOp`. An integer poison casts to a wholly poison byte
  (see `LLVM.Byte.fromInt`).
-/
def lowerBytePoison : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let resultType ← Puddle.MatchProg.type (Attr := LLVM.ByteType)
      let _ ← Puddle.MatchProg.root (.llvm .mlir__poison) #[] #[resultType]
      return resultType)
    (fun resultType => do
      let intType ← Puddle.CreateProg.applyNative (Outputs := Puddle.Handle OpCode .type)
          resultType TypeAttr.intOfByte?
      let poison ← Puddle.CreateProg.operation (.gmir .g_poison) #[] #[intType]
      Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast) #[poison.res[0]!]
          #[resultType])
    (fun castOp => castOp)



/--
  A shift of a byte by an integer amount -> `gOp` on the integer of the same width, between
  `builtin.unrealized_conversion_cast`s, as in `lowerUnaryByteOp`.
-/
def lowerByteShift (lOp : Llvm) (gOp : GMIR)
    (h : propertiesOf (OpCode.llvm lOp) = propertiesOf (OpCode.gmir gOp) := by rfl) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let byteType ← Puddle.MatchProg.type (Attr := LLVM.ByteType)
      let amountType ← Puddle.MatchProg.type (Attr := IntegerType)
      let value ← Puddle.MatchProg.value byteType
      let amount ← Puddle.MatchProg.value amountType
      let root ← Puddle.MatchProg.root (.llvm lOp) #[value, amount] #[byteType]
      return (byteType, value, amount, root))
    (fun (byteType, value, amount, root) => do
      let intType ← Puddle.CreateProg.applyNative (Outputs := Puddle.Handle OpCode .type)
          byteType TypeAttr.intOfByte?
      let castOp ← Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[value] #[intType]
      let props ← Puddle.CreateProg.applyNative root.properties (fun p => some (cast h p))
      let newOp ← Puddle.CreateProg.operation (.gmir gOp) #[castOp.res[0]!, amount]
          #[intType] (.inr props)
      Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast) #[newOp.res[0]!]
          #[byteType])
    (fun castBackOp => castBackOp)



/--
  Whether `opType` and `resType` are a byte and an integer type of the same nonzero width. A byte
  of no bits casts to a poison integer, while `llvm.bitcast` yields its value.
-/
def isByteIntBitcast (opType resType : TypeAttr) : Bool :=
  match opType.val, resType.val with
  | .byteType b, .integerType i | .integerType i, .byteType b =>
    b.bitwidth = i.bitwidth && 0 < b.bitwidth
  | _, _ => false

/--
  `llvm.bitcast` between a byte and an integer of the same width -> `builtin.unrealized_conversion_cast`.
  LLVM reuses the source register for these (see `translateBitCast`).
-/
def lowerByteIntBitcast : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let operandType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let resultType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let operand ← Puddle.MatchProg.value operandType
      let _ ← Puddle.MatchProg.root (.llvm .bitcast) #[operand] #[resultType]
      Puddle.MatchProg.matchNative (operandType, resultType)
          fun (operandType, resultType) => isByteIntBitcast operandType resultType
      return (resultType, operand))
    (fun (resultType, operand) => do
      Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast) #[operand] #[resultType])
    (fun castOp => castOp)


/--
  Whether `iN -> !llvm.byte<N> -> iN` is the identity (see `LLVM.Byte.toFrozenInt_fromInt`).
  The round trip from a byte freezes its poison bits, so it is not folded.
-/
def isIntToByteRoundTrip (inputType interType : TypeAttr) : Bool :=
  match inputType.val, interType.val with
  | .integerType i, .byteType b => i.bitwidth = b.bitwidth && 0 < i.bitwidth
  | _, _ => false


/-! ## Pass implementation -/

/--
  The Puddle patterns of the pass, in the order it tries them. `g_bswap` and `g_bitreverse`
  appear twice, as they always have.
-/
public def llvmToGMIRPatternList : List (Puddle.Pattern OpCode) := [
  lowerBinop .add .g_add, lowerBinop .sub .g_sub, lowerIcmp, lowerSelect,
  lowerIntegerCast .sext .g_sext, lowerIntegerCast .zext .g_zext, lowerIntegerCast .trunc .g_trunc,
  lowerBinop .and .g_and, lowerBinop .or .g_or, lowerBinop .xor .g_xor,
  lowerBinop .shl .g_shl, lowerBinop .lshr .g_lshr, lowerBinop .ashr .g_ashr,
  lowerBinop .mul .g_mul, lowerBinop .sdiv .g_sdiv, lowerBinop .udiv .g_udiv,
  lowerBinop .srem .g_srem, lowerBinop .urem .g_urem,
  lowerUnop .intr__bswap .g_bswap id, lowerUnop .intr__bitreverse .g_bitreverse id,
  lowerBinop .intr__smax .g_smax, lowerBinop .intr__smin .g_smin,
  lowerBinop .intr__umax .g_umax, lowerBinop .intr__umin .g_umin,
  lowerUnop .intr__abs .g_abs (fun _ => ()),
  lowerFunnelShiftIntrinsic .intr__fshl .g_fshl, lowerFunnelShiftIntrinsic .intr__fshr .g_fshr,
  lowerBinop .intr__sadd__sat .g_saddsat, lowerBinop .intr__uadd__sat .g_uaddsat,
  lowerBinop .intr__ssub__sat .g_ssubsat, lowerBinop .intr__usub__sat .g_usubsat,
  lowerBinop .intr__sshl__sat .g_sshlsat, lowerBinop .intr__ushl__sat .g_ushlsat,
  lowerCount .intr__ctlz .g_ctlz (fun _ => ()) (!·.is_zero_poison),
  lowerCount .intr__cttz .g_cttz (fun _ => ()) (!·.is_zero_poison),
  lowerCount .intr__ctlz .g_ctlz_zero_poison (fun _ => ()) (·.is_zero_poison),
  lowerCount .intr__cttz .g_cttz_zero_poison (fun _ => ()) (·.is_zero_poison),
  lowerCount .intr__ctpop .g_ctpop id,
  lowerIntegerConstant, lowerPoison, lowerBytePoison,
  lowerUnaryByteOp .trunc .g_trunc (fun _ => ⟨false, false⟩),
  -- Unproven (`allPoisonByte`), so not run:
  -- lowerByteShift .shl .g_shl, lowerByteShift .lshr .g_lshr,
  lowerByteIntBitcast,
  lowerStaticAlloca_pattern, lowerStaticAllocaGMIR_pattern, lowerStaticAllocaArith_pattern,
  lowerStaticAllocaZero_pattern, lowerLoad_pattern, reconcilePairingCast isIntToByteRoundTrip]

/-- The patterns of the strict pass: all of `llvmToGMIRPatternList`, which are proved valid
(`Veir.Passes.LLVMToGMIR.Validity`). -/
public def llvmToGMIRStrictPatternList : List (Puddle.Pattern OpCode) := llvmToGMIRPatternList

/-- The strict pass: the branch step with its checks, then the proved patterns through the
module-filtered driver, then the erasure of the dead casts by the driver. `normalizeGEPIndices` is
not run. Its soundness is `LLVMToGMIRPass.runStrict_sound`. -/
public def LLVMToGMIRPass.runStrict : PurePass := fun ctx moduleOp => do
  let ctx ← LLVMToGMIRBranches.run true ctx moduleOp
  checkModuleRoot "llvm-to-gmir" ctx moduleOp
  let ctx ← applyToFunctionsStrict "llvm-to-gmir"
    (RewritePattern.GreedyRewritePattern
      (llvmToGMIRStrictPatternList.map fun rule => rule.compile.run).toArray) ctx moduleOp
  applyInContextStrict "llvm-to-gmir" (RewritePattern.GreedyRewritePattern #[]) ctx moduleOp

/-- The compiled patterns of `llvmToGMIRPatternList`. -/
private def llvmToGMIRPatterns : Array (Puddle.CompiledPattern OpCode) :=
  (llvmToGMIRPatternList.map (·.compile)).toArray

public def LLVMToGMIRPass.impl (strict : Bool) (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) :=
  if strict then ExceptT.mk (pure (LLVMToGMIRPass.runStrict ctx op)) else do
    -- Branches are translated by a separate step, which is proved to refine the module.
    -- `Veir.Passes.LLVMToGMIR.Validity` proves that the gMIR branches interpret as the LLVM ones.
    let ctx ← ExceptT.mk (pure (LLVMToGMIRBranches.run false ctx op))
    -- `normalizeGEPIndices` is unproven, so not run:
    -- `llvmToGMIRPatterns.map (·.run) ++ #[.fromLocalRewrite normalizeGEPIndices]`.
    let pattern := RewritePattern.GreedyRewritePattern (llvmToGMIRPatterns.map (·.run))
    match RewritePattern.applyToFunctions pattern ctx op with
    | none => throw "Error while applying llvm-to-gmir translation"
    | some ctx =>
      -- A local rewrite may only erase the matched cast, so the folded first cast is left dead;
      -- the driver erases it. `eliminateDeadOp`, which also erases allocating operations, is
      -- unproven, so not run.
      match RewritePattern.applyInContext (RewritePattern.GreedyRewritePattern #[]) ctx op with
      | none => throw "Error while applying DCE after llvm-to-gmir translation"
      | some ctx => pure ctx

public def LLVMToGMIRPass : Pass OpCode :=
  { name := "llvm-to-gmir"
    description := "Lower llvm dialect operations to the gmir dialect."
    options := .ofList [
      ("strict", { description :=
                     "Only run the rewrites proved to refine the module, and check what they assume.",
                   defaultValue := false })]
    run := fun options => LLVMToGMIRPass.impl ((options.get? "strict").getD false) }

end Veir
