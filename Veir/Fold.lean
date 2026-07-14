import Veir.Interpreter.Basic
import Veir.PatternRewriter.Basic

/-!
  # Constant folding infrastructure

  Folding infrastructure in the style of MLIR's `fold`/`createOrFold`, with one
  important difference: the folded values are computed by the interpreter
  (`interpretOp'`), which defines the semantics of each operation, instead of by
  per-operation reimplementations of the semantics.

  Each opcode can be queried through `OpCode.foldsTo` to determine whether it
  folds for a given pattern of constant operands. There are three possible
  outcomes:

  * `.operand j`: the single result of the operation is always refined by
    operand `j` (e.g. `arith.addi %x, %c0` folds to `%x`). This requires a
    per-opcode entry in the fold table and a proof against the interpreter
    semantics.
  * `.constant rv`: the single result of the operation is always refined by the
    runtime value `rv`, even though not all operands are known (e.g.
    `arith.muli %x, %c0` folds to `0`, and `arith.divsi %x, %c0` is immediate
    UB and therefore folds to `poison`).
  * `.evaluate`: all operands are known constants, so the operation can simply
    be evaluated with the interpreter. This outcome is fully generic and needs
    no per-opcode logic: whatever the interpreter returns is, by definition,
    the value the operation would produce at runtime. If the interpreter
    signals UB the operation folds to `poison` (which UB refines).

  Folded results are materialized as `arith.constant` / `llvm.mlir.constant`
  ops (depending on the dialect of the folded operation), and poison results as
  `llvm.mlir.poison`.
-/

namespace Veir

/--
  The result of querying whether an operation folds, mirroring MLIR's
  `OpFoldResult`. Folding is currently restricted to operations with exactly
  one result.
-/
inductive FoldOutcome where
  /-- The result of the operation is refined by operand `j`. -/
  | operand (j : Nat)
  /-- The result of the operation is refined by the constant `rv`.
      `rv` may be poison, e.g. for operations that trigger immediate UB. -/
  | constant (rv : RuntimeValue)
  /-- All operands are constant: evaluate the operation with the interpreter
      and materialize the result. -/
  | evaluate

/--
  If `val` is defined by a constant-like operation with an integer result,
  return the runtime value it materializes.

  The conversions here must match the interpretation of the corresponding
  constant operations in `interpretOp'` exactly: this is what makes folding
  agree with the runtime semantics.
-/
def ValuePtr.constantValue (val : ValuePtr) (ctx : IRContext OpCode) : Option RuntimeValue := do
  let defOp ← val.getDefiningOp! ctx
  match defOp.getOpType! ctx with
  | .arith .constant =>
    let .integerType intTy := (val.getType! ctx).val | none
    let bw := intTy.bitwidth
    let properties := defOp.getProperties! ctx (.arith .constant)
    return .int bw (.val (BitVec.ofInt bw properties.value.value))
  | .llvm .mlir__constant =>
    let .integerType intTy := (val.getType! ctx).val | none
    let bw := intTy.bitwidth
    let properties := defOp.getProperties! ctx (.llvm .mlir__constant)
    let .integer intAttr := properties.value | none
    return .int bw (Data.LLVM.Int.constant bw intAttr.value)
  | .llvm .mlir__poison =>
    let .integerType intTy := (val.getType! ctx).val | none
    return .int intTy.bitwidth (Data.LLVM.Int.mlir_poison intTy.bitwidth)
  | .riscv .li =>
    let .registerType _ := (val.getType! ctx).val | none
    let properties := defOp.getProperties! ctx (.riscv .li)
    return .reg (Data.RISCV.li (BitVec.ofInt 64 properties.value.value))
  | .mod_arith .constant =>
    -- `mod_arith` has no runtime representation (it is lowered before
    -- interpretation); constants are recovered as their canonical residue in
    -- `[0, q)`, stored in the modulus' storage type. Note that the verifier
    -- only checks that the value fits the storage type, so the reduction here
    -- also canonicalizes non-canonical constants.
    let .modArithType mt := (val.getType! ctx).val | none
    let q := mt.modulus.value
    if q ≤ 0 then none else
    let properties := defOp.getProperties! ctx (.mod_arith .constant)
    return .int mt.modulus.type.bitwidth
      (.val (BitVec.ofNat mt.modulus.type.bitwidth (properties.value.value % q).toNat))
  | _ => none

/--
  Opcodes whose interpretation may be evaluated at fold time: they must be
  pure, memory-independent, and free of control flow.

  Note: this is deliberately not `OpCode.isSideEffecting`, which classifies
  non-volatile `llvm.load` as non-side-effecting. Evaluating a load at fold
  time would read from a dummy memory and miscompile.
-/
def OpCode.isFoldEvaluable : OpCode → Bool
  | .arith _ => true
  | .llvm op => match op with
    | .add | .sub | .mul | .sdiv | .udiv | .srem | .urem
    | .shl | .lshr | .ashr | .and | .or | .xor => true
    | _ => false
  | .riscv op => match op with
    -- Loads and stores must not be evaluated at fold time (note that loads
    -- read memory even though `isSideEffecting` classifies them as pure).
    | .ld | .lw | .lwu | .lh | .lhu | .lb | .lbu
    | .sd | .sw | .sh | .sb => false
    -- Everything else is pure register arithmetic.
    | _ => true
  | _ => false

/--
  Fold table for `arith` operations with partially-constant operands.
  The all-constant case is handled generically by `OpCode.foldsTo`.

  Every entry here claims that, for all values of the unknown operands, the
  result of the operation is refined by the returned value. Poison entries
  correspond to operations that trigger immediate UB (which refines to
  poison).
-/
def Arith.foldsTo (op : Arith) (_properties : HasDialectOpInfo.propertiesOf op)
    (_resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    Option FoldOutcome :=
  match op with
  | .addi =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then some (.operand 0) else none
    | _ => none
  | .subi =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then some (.operand 0) else none
    | _ => none
  | .muli =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw (.val 0)))
      else if c = 1 then some (.operand 0)
      else none
    | _ => none
  | .andi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw (.val 0)))
      else if c = BitVec.allOnes bw then some (.operand 0)
      else none
    | _ => none
  | .ori =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.operand 0)
      else if c = BitVec.allOnes bw then
        some (.constant (.int bw (.val (BitVec.allOnes bw))))
      else none
    | _ => none
  | .xori =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then some (.operand 0) else none
    | _ => none
  | .shli =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then some (.operand 0) else none
    | _ => none
  | .shrsi =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then some (.operand 0) else none
    | _ => none
  | .shrui =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then some (.operand 0) else none
    | _ => none
  -- Division / remainder by zero is immediate UB: fold to poison.
  | .divsi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw .poison)) else none
    | _ => none
  | .divui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw .poison)) else none
    | _ => none
  | .remsi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw .poison)) else none
    | _ => none
  | .remui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw .poison)) else none
    | _ => none
  | _ => none

/--
  Fold table for `llvm` operations with partially-constant operands.
  See `Arith.foldsTo`.
-/
def Llvm.foldsTo (op : Llvm) (_properties : HasDialectOpInfo.propertiesOf op)
    (_resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    Option FoldOutcome :=
  match op with
  | .add =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then some (.operand 0) else none
    | _ => none
  | .sub =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then some (.operand 0) else none
    | _ => none
  | .mul =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw (.val 0)))
      else if c = 1 then some (.operand 0)
      else none
    | _ => none
  | .and =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw (.val 0)))
      else if c = BitVec.allOnes bw then some (.operand 0)
      else none
    | _ => none
  | .or =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.operand 0)
      else if c = BitVec.allOnes bw then
        some (.constant (.int bw (.val (BitVec.allOnes bw))))
      else none
    | _ => none
  | .xor =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then some (.operand 0) else none
    | _ => none
  | .shl =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then some (.operand 0) else none
    | _ => none
  | .lshr =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then some (.operand 0) else none
    | _ => none
  | .ashr =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then some (.operand 0) else none
    | _ => none
  -- Division / remainder by zero is immediate UB: fold to poison.
  | .sdiv =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw .poison)) else none
    | _ => none
  | .udiv =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw .poison)) else none
    | _ => none
  | .srem =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw .poison)) else none
    | _ => none
  | .urem =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw .poison)) else none
    | _ => none
  | _ => none

/--
  Fold table for `riscv` operations with partially-constant operands.
  See `Arith.foldsTo`.

  Register-register operations are interpreted as `RISCV.f rs2 rs1` with
  `rs1 = operands[0]` and `rs2 = operands[1]`, so the identities below key off
  a constant `operands[1]`. RISC-V registers have no poison, and division by
  zero is defined (it is handled by the all-constant `.evaluate` path), so no
  entry here produces poison. Immediate-carrying operations (`addi`, `slli`,
  ...) fold on their properties instead of an operand.
-/
def Riscv.foldsTo (op : Riscv) (properties : HasDialectOpInfo.propertiesOf op)
    (_resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    Option FoldOutcome :=
  match op with
  | .add => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then some (.operand 0) else none
    | _ => none
  | .sub => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then some (.operand 0) else none
    | _ => none
  | .xor => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then some (.operand 0) else none
    | _ => none
  | .or => match constOperands.toList with
    | [_, some (.reg c)] =>
      if c.val = 0 then some (.operand 0)
      else if c.val = BitVec.allOnes 64 then
        some (.constant (.reg (Data.RISCV.li (BitVec.allOnes 64))))
      else none
    | _ => none
  | .and => match constOperands.toList with
    | [_, some (.reg c)] =>
      if c.val = 0 then some (.constant (.reg (Data.RISCV.li 0)))
      else if c.val = BitVec.allOnes 64 then some (.operand 0)
      else none
    | _ => none
  | .mul => match constOperands.toList with
    | [_, some (.reg c)] =>
      if c.val = 0 then some (.constant (.reg (Data.RISCV.li 0)))
      else if c.val = 1 then some (.operand 0)
      else none
    | _ => none
  | .sll => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then some (.operand 0) else none
    | _ => none
  | .srl => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then some (.operand 0) else none
    | _ => none
  | .sra => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then some (.operand 0) else none
    | _ => none
  -- Immediate forms: adding, or-ing, xor-ing, or shifting by 0 is the
  -- identity; and-ing with 0 is 0.
  | .addi => match constOperands.toList with
    | [_] => if properties.value.value = 0 then some (.operand 0) else none
    | _ => none
  | .ori => match constOperands.toList with
    | [_] => if properties.value.value = 0 then some (.operand 0) else none
    | _ => none
  | .xori => match constOperands.toList with
    | [_] => if properties.value.value = 0 then some (.operand 0) else none
    | _ => none
  | .andi => match constOperands.toList with
    | [_] =>
      if properties.value.value = 0 then
        some (.constant (.reg (Data.RISCV.li 0)))
      else none
    | _ => none
  | .slli => match constOperands.toList with
    | [_] => if properties.value.value = 0 then some (.operand 0) else none
    | _ => none
  | .srli => match constOperands.toList with
    | [_] => if properties.value.value = 0 then some (.operand 0) else none
    | _ => none
  | .srai => match constOperands.toList with
    | [_] => if properties.value.value = 0 then some (.operand 0) else none
    | _ => none
  | _ => none

/-- The modulus `q` (as a positive `Nat`) and storage bitwidth of a single
    `!mod_arith.int` result type. -/
def modArithModulus (resultTypes : Array TypeAttr) : Option (Nat × Nat) :=
  match resultTypes.toList with
  | [resType] =>
    match resType.val with
    | .modArithType mt =>
      let q := mt.modulus.value.toNat
      if q = 0 then none else some (q, mt.modulus.type.bitwidth)
    | _ => none
  | _ => none

/--
  Fold table for `mod_arith` operations. See `Arith.foldsTo`.

  `mod_arith` is not interpreted (it is lowered to `arith` before
  interpretation), so the all-constant case cannot go through `.evaluate`;
  instead it is computed here, modulo the modulus `q` recovered from the
  result type. Constant operands are canonical residues in `[0, q)` (see
  `ValuePtr.constantValue`), and the arithmetic is performed on `Nat` so it
  cannot overflow the storage type. The `x + 0`, `x - 0`, and `x * 1`
  identities rely on the dialect invariant that runtime `mod_arith` values are
  canonical residues (the same assumption the `mod-arith-to-arith` lowering
  makes).
-/
def Mod_Arith.foldsTo (op : Mod_Arith) (_properties : HasDialectOpInfo.propertiesOf op)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    Option FoldOutcome :=
  match op with
  | .add =>
    match constOperands.toList with
    | [some (.int _ (.val a)), some (.int _ (.val b))] => do
      let (q, bw) ← modArithModulus resultTypes
      some (.constant (.int bw (.val (BitVec.ofNat bw ((a.toNat + b.toNat) % q)))))
    | [_, some (.int _ (.val c))] => if c = 0 then some (.operand 0) else none
    | _ => none
  | .sub =>
    match constOperands.toList with
    | [some (.int _ (.val a)), some (.int _ (.val b))] => do
      let (q, bw) ← modArithModulus resultTypes
      some (.constant (.int bw (.val (BitVec.ofNat bw ((a.toNat + q - b.toNat) % q)))))
    | [_, some (.int _ (.val c))] => if c = 0 then some (.operand 0) else none
    | _ => none
  | .mul =>
    match constOperands.toList with
    | [some (.int _ (.val a)), some (.int _ (.val b))] => do
      let (q, bw) ← modArithModulus resultTypes
      some (.constant (.int bw (.val (BitVec.ofNat bw ((a.toNat * b.toNat) % q)))))
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw (.val 0)))
      else if c = 1 then some (.operand 0)
      else none
    | _ => none
  | .constant => none

/--
  Query whether an operation folds, given its result types and the values of
  its constant-defined operands (`constOperands[i] = some rv` iff operand `i`
  is defined by a constant-like operation with value `rv`).

  When every operand is a known constant and the opcode is evaluable, the
  answer is always `.evaluate` — no per-opcode logic is involved. Otherwise
  the per-dialect fold tables are consulted for identities (and, for the
  uninterpreted `mod_arith` dialect, for all-constant folds computed in the
  table itself).
-/
def OpCode.foldsTo (opCode : OpCode) (properties : HasOpInfo.propertiesOf opCode)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    Option FoldOutcome :=
  if opCode.isFoldEvaluable && !constOperands.isEmpty
      && constOperands.all (·.isSome) then
    some .evaluate
  else
    match opCode with
    | .arith op => Arith.foldsTo op properties resultTypes constOperands
    | .llvm op => Llvm.foldsTo op properties resultTypes constOperands
    | .riscv op => Riscv.foldsTo op properties resultTypes constOperands
    | .mod_arith op => Mod_Arith.foldsTo op properties resultTypes constOperands
    | _ => none

/--
  Evaluate a side-effect-free operation with the interpreter. Returns the
  result values, `Interp.ub` if the operation triggers UB, and `none` if the
  interpreter cannot evaluate it (or it performs control flow).

  Must only be called for `isFoldEvaluable` opcodes: those neither read nor
  write memory, so the dummy memory state is irrelevant.
-/
def foldEvaluate (opCode : OpCode) (properties : HasOpInfo.propertiesOf opCode)
    (resultTypes : Array TypeAttr) (operands : Array RuntimeValue)
    : Interp (Array RuntimeValue) := do
  let (results, _mem, action) ←
    interpretOp' opCode properties resultTypes operands #[] MemoryState.empty
  if action.isSome then none
  else return results

/--
  Materialize a runtime value as a constant-like operation at the given
  insertion point. Concrete integers become `arith.constant`, or
  `llvm.mlir.constant` when the folded operation `forOp` belongs to the `llvm`
  dialect. Poison becomes `llvm.mlir.poison` (the only poison-producing
  constant available). Register values become `riscv.li`.
-/
def PatternRewriter.materializeConstant! (rewriter : PatternRewriter OpCode)
    (rv : RuntimeValue) (resType : TypeAttr) (forOp : OpCode) (ip : InsertPoint)
    : Option (PatternRewriter OpCode × OperationPtr) :=
  match rv with
  | .int bw (.val v) =>
    match forOp with
    | .llvm _ =>
      let properties : LLVMConstantProperties :=
        { value := .integer (IntegerAttr.mk v.toInt (IntegerType.mk bw)) }
      rewriter.createOp! (.llvm .mlir__constant) #[resType] #[] #[] #[] properties (some ip)
    | .mod_arith _ =>
      -- `v` is a canonical residue in `[0, q)`, stored with the modulus'
      -- storage type (read off the `!mod_arith.int` result type).
      match resType.val with
      | .modArithType mt =>
        let properties : ModArithConstantProperties :=
          { value := IntegerAttr.mk v.toNat mt.modulus.type }
        rewriter.createOp! (.mod_arith .constant) #[resType] #[] #[] #[] properties (some ip)
      | _ => none
    | _ =>
      let properties : ArithConstantProperties :=
        { value := IntegerAttr.mk v.toInt (IntegerType.mk bw) }
      rewriter.createOp! (.arith .constant) #[resType] #[] #[] #[] properties (some ip)
  | .int _ .poison =>
    rewriter.createOp! (.llvm .mlir__poison) #[resType] #[] #[] #[] () (some ip)
  | .reg r =>
    let properties : RISCVImmediateProperties :=
      { value := IntegerAttr.mk r.val.toInt (IntegerType.mk 64) }
    rewriter.createOp! (.riscv .li) #[resType] #[] #[] #[] properties (some ip)
  | _ => none

/--
  Detached counterpart of `PatternRewriter.materializeConstant!`, for use by
  `LocalRewritePattern`s. The returned operation is in the returned context but
  is not linked into a block; `RewritePattern.fromLocalRewrite` performs the
  insertion after the local pattern succeeds.
-/
def WfRewriter.materializeConstant! (ctx : WfIRContext OpCode)
    (rv : RuntimeValue) (resType : TypeAttr) (forOp : OpCode) :
    Option (WfIRContext OpCode × OperationPtr) :=
  match rv with
  | .int bw (.val v) =>
    match forOp with
    | .llvm _ =>
      let properties : LLVMConstantProperties :=
        { value := .integer (IntegerAttr.mk v.toInt (IntegerType.mk bw)) }
      WfRewriter.createOp! ctx (.llvm .mlir__constant) #[resType] #[] #[] #[] properties none
    | .mod_arith _ =>
      match resType.val with
      | .modArithType mt =>
        let properties : ModArithConstantProperties :=
          { value := IntegerAttr.mk v.toNat mt.modulus.type }
        WfRewriter.createOp! ctx (.mod_arith .constant) #[resType] #[] #[] #[] properties none
      | _ => none
    | _ =>
      let properties : ArithConstantProperties :=
        { value := IntegerAttr.mk v.toInt (IntegerType.mk bw) }
      WfRewriter.createOp! ctx (.arith .constant) #[resType] #[] #[] #[] properties none
  | .int _ .poison =>
    WfRewriter.createOp! ctx (.llvm .mlir__poison) #[resType] #[] #[] #[] () none
  | .reg r =>
    let properties : RISCVImmediateProperties :=
      { value := IntegerAttr.mk r.val.toInt (IntegerType.mk 64) }
    WfRewriter.createOp! ctx (.riscv .li) #[resType] #[] #[] #[] properties none
  | _ => none

/--
  Replace all uses of the single result of `op` with `newVal` and erase `op`.
  Panics if `op` does not have exactly one result, if `newVal` is that result,
  or if anything is out of bounds — verified IR reaching this through
  `foldOperation` satisfies all of these.
-/
def PatternRewriter.replaceOpWithValue! {OpInfo : Type} [HasOpInfo OpInfo]
    (rewriter : PatternRewriter OpInfo)
    (op : OperationPtr) (newVal : ValuePtr) : PatternRewriter OpInfo :=
  let rewriter := rewriter.replaceValue! (op.getResult 0) newVal
  rewriter.eraseOp! op

/--
  The resolved decision of whether and how an operation folds, shared by
  `foldOperation` (folding existing operations) and
  `PatternRewriter.createOrFoldOp!` (folding at creation time).
-/
inductive FoldDecision where
  /-- Use operand `j` in place of the result. -/
  | useOperand (j : Nat)
  /-- Materialize `rv` as a constant and use it in place of the result. -/
  | useConstant (rv : RuntimeValue)
  /-- The operation does not fold. -/
  | noFold

/--
  Decide whether an operation folds, given its opcode, properties, result
  types, and the values of its constant-defined operands. This resolves the
  `FoldOutcome` reported by `OpCode.foldsTo`: `.evaluate` outcomes are
  computed with the interpreter, and interpreter-reported UB becomes a poison
  constant (which UB refines).

  Folding is restricted to single-result operations; this also excludes
  structural ops (module, functions, terminators), and every op `foldsTo` can
  answer for is verified to have no regions and no successors.
-/
def foldDecision (opType : OpCode) (properties : HasOpInfo.propertiesOf opType)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue))
    : FoldDecision :=
  if opType.isConstantLike then .noFold else
  if resultTypes.size ≠ 1 then .noFold else
  match OpCode.foldsTo opType properties resultTypes constOperands with
  | none => .noFold
  | some (.operand j) => .useOperand j
  | some (.constant rv) => .useConstant rv
  | some .evaluate =>
    -- `.evaluate` is only answered when every operand is a known constant.
    let values := constOperands.map (·.get!)
    match (foldEvaluate opType properties resultTypes values : Option (UBOr _)) with
    | none => .noFold
    | some (.ok results) =>
      if results.size = 1 then .useConstant results[0]! else .noFold
    | some .ub =>
      -- The operation triggers UB whenever it is executed: fold to poison.
      match resultTypes[0]!.val with
      | .integerType intTy => .useConstant (.int intTy.bitwidth .poison)
      | _ => .noFold

/--
  Rewrite pattern that folds an existing operation, replacing it with one of
  its operands or with a materialized constant.
-/
def foldOperationLocal (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  if _ : op.InBounds ctx.raw then
    let opType := op.getOpType! ctx.raw
    let operands := op.getOperands! ctx.raw
    let resultTypes := op.getResultTypes! ctx.raw
    let constOperands := operands.map (ValuePtr.constantValue · ctx.raw)
    match foldDecision opType (op.getProperties! ctx.raw opType) resultTypes constOperands with
    | .noFold => some (ctx, none)
    | .useOperand j =>
      match operands[j]? with
      | some operand => some (ctx, some (#[], #[operand]))
      | none => some (ctx, none)
    | .useConstant rv => do
      let some resultType := resultTypes[0]? | return (ctx, none)
      let (ctx, newOp) ← WfRewriter.materializeConstant! ctx rv resultType opType
      return (ctx, some (#[newOp], #[newOp.getResult 0]))
  else some (ctx, none)

/-- Rewrite-pattern wrapper around the semantics-friendly local folding pattern. -/
def foldOperation (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite foldOperationLocal rewriter op opInBounds

/--
  Create an operation at the given insertion point, unless it can be folded,
  in which case no operation is created and the folded values are returned
  instead. This is the analog of MLIR's `OpBuilder::createOrFold`, restricted
  to operations without regions or block operands.

  Returns the values to use in place of the operation's results.
-/
def PatternRewriter.createOrFoldOp! (rewriter : PatternRewriter OpCode) (opType : OpCode)
    (resultTypes : Array TypeAttr) (operands : Array ValuePtr)
    (properties : HasOpInfo.propertiesOf opType) (insertionPoint : InsertPoint)
    : Option (PatternRewriter OpCode × Array ValuePtr) := do
  let constOperands := operands.map (ValuePtr.constantValue · rewriter.ctx.raw)
  match foldDecision opType properties resultTypes constOperands with
  | .useOperand j =>
    return (rewriter, #[operands[j]!])
  | .useConstant rv =>
    let (rewriter, newOp) ← rewriter.materializeConstant! rv resultTypes[0]!
      opType insertionPoint
    return (rewriter, newOp.getResults! rewriter.ctx.raw)
  | .noFold =>
    let (rewriter, newOp) ← rewriter.createOp! opType resultTypes operands
      #[] #[] properties (some insertionPoint)
    return (rewriter, newOp.getResults! rewriter.ctx.raw)

/--
  Create or fold an operation, replace `oldOp` with the resulting values, and
  erase `oldOp`. The result counts must agree; folding itself remains restricted
  to single-result operations, while the no-fold path supports multiple results.
-/
def PatternRewriter.createOrFoldAndReplaceOp! (rewriter : PatternRewriter OpCode)
    (oldOp : OperationPtr) (opType : OpCode) (resultTypes : Array TypeAttr)
    (operands : Array ValuePtr) (properties : HasOpInfo.propertiesOf opType)
    (insertionPoint : InsertPoint) : Option (PatternRewriter OpCode) := do
  let (rewriter, newValues) ←
    rewriter.createOrFoldOp! opType resultTypes operands properties insertionPoint
  guard (oldOp.getNumResults! rewriter.ctx.raw == newValues.size)
  let mut rewriter := rewriter
  for h : i in 0...newValues.size do
    rewriter := rewriter.replaceValue! (oldOp.getResult i) newValues[i]
  return rewriter.eraseOp! oldOp

end Veir
