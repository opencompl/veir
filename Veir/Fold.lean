import Veir.Interpreter.Basic

/-!
  # Constant folding infrastructure

  Pure folding infrastructure in the style of MLIR's `fold`, with one important
  difference: the folded values are computed by the interpreter
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

  This module never mutates the IR. Constant materialization, `createOrFold`,
  and rewrite patterns live in `Veir.Fold.Rewriter`.
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
  -- Select with a known non-poison condition returns the selected operand
  -- exactly (poison on the non-selected arm does not propagate). A poison
  -- condition is deliberately not matched: it makes the result poison, not
  -- the selected operand.
  | .select =>
    match constOperands.toList with
    | [some (.int 1 (.val c)), _, _] =>
      if c = 1 then some (.operand 1) else some (.operand 2)
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
  -- See the `arith.select` entry.
  | .select =>
    match constOperands.toList with
    | [some (.int 1 (.val c)), _, _] =>
      if c = 1 then some (.operand 1) else some (.operand 2)
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
  -- Zicond: with a known condition (`rs2` = operand 1), `czero.eqz` and
  -- `czero.nez` either forward `rs1` unchanged or produce zero. Registers
  -- have no poison, so both branches fold (unlike `select`, whose condition
  -- may be poison).
  | .czeroeqz => match constOperands.toList with
    | [_, some (.reg c)] =>
      if c.val = 0 then some (.constant (.reg (Data.RISCV.li 0)))
      else some (.operand 0)
    | _ => none
  | .czeronez => match constOperands.toList with
    | [_, some (.reg c)] =>
      if c.val = 0 then some (.operand 0)
      else some (.constant (.reg (Data.RISCV.li 0)))
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
  The resolved decision of whether and how an operation folds.

  This is the pure interface consumed by both data-flow analyses and rewriting
  clients. It never changes the IR or materializes a constant operation.
-/
inductive FoldDecision where
  /-- Use operand `j` in place of the result. -/
  | useOperand (j : Nat)
  /-- Use the runtime constant `rv` in place of the result. -/
  | useConstant (rv : RuntimeValue)
  /-- The operation does not fold with the supplied operand information. -/
  | noFold

/--
Whether a runtime value can represent a folded result of the given type.
Modular integers use an `.int` runtime value with the modulus storage width,
even though the interpreter's general `RuntimeValue.Conforms` relation keeps
`.int` exclusive to ordinary `integerType`s.
-/
def RuntimeValue.conformsFoldResult (rv : RuntimeValue) (resultType : TypeAttr) : Prop :=
  match rv, resultType.val with
  | .int bw _, .modArithType modType => modType.modulus.type.bitwidth = bw
  | _, _ => rv.Conforms resultType

instance : Decidable (RuntimeValue.conformsFoldResult rv resultType) := by
  unfold RuntimeValue.conformsFoldResult
  split <;> infer_instance

/-- Return a constant decision only when `rv` conforms to the sole result type. -/
private def conformingConstantDecision
    (resultTypes : Array TypeAttr) (rv : RuntimeValue) : FoldDecision :=
  match resultTypes[0]? with
  | some resultType =>
    if rv.conformsFoldResult resultType then .useConstant rv else .noFold
  | none => .noFold

/--
  Decide whether an operation folds, given its opcode, properties, result
  types, and the values of its known-constant operands. This resolves the
  `FoldOutcome` reported by `OpCode.foldsTo`: `.evaluate` outcomes are computed
  with the interpreter, and interpreter-reported UB becomes a poison constant.

  Unknown operands are represented by `none`. A data-flow client may use that
  representation for either an uninitialized or an overdefined lattice value;
  after `.noFold`, the client retains responsibility for deciding whether to
  wait for more information or move its result to top.

  Folding is restricted to single-result operations. Returned operand indices
  and runtime constants are validated before they are exposed to callers.
-/
def foldDecision (opType : OpCode) (properties : HasOpInfo.propertiesOf opType)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue))
    : FoldDecision :=
  if opType.isConstantLike then .noFold else
  if resultTypes.size ≠ 1 then .noFold else
  match OpCode.foldsTo opType properties resultTypes constOperands with
  | none => .noFold
  | some (.operand j) =>
    if j < constOperands.size then .useOperand j else .noFold
  | some (.constant rv) => conformingConstantDecision resultTypes rv
  | some .evaluate =>
    -- `.evaluate` is only answered when every operand is a known constant.
    let values := constOperands.map (·.get!)
    match (foldEvaluate opType properties resultTypes values : Option (UBOr _)) with
    | none => .noFold
    | some (.ok results) =>
      match results.toList with
      | [result] => conformingConstantDecision resultTypes result
      | _ => .noFold
    | some .ub =>
      -- The operation triggers UB whenever it is executed: fold to poison.
      match resultTypes[0]!.val with
      | .integerType intTy =>
        conformingConstantDecision resultTypes (.int intTy.bitwidth .poison)
      | _ => .noFold

/--
Read-only convenience wrapper around `foldDecision` for an existing operation.
The supplied constant array remains explicit so SCCP can provide constants
inferred from lattice facts rather than only constants materialized in the IR.
-/
def foldDecisionForOp (op : OperationPtr)
    (constOperands : Array (Option RuntimeValue))
    (ctx : IRContext OpCode) : FoldDecision :=
  if constOperands.size ≠ op.getNumOperands! ctx then
    .noFold
  else
    let opType := op.getOpType! ctx
    foldDecision opType (op.getProperties! ctx opType)
      (op.getResultTypes! ctx) constOperands

end Veir
