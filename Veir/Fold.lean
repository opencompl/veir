module

public import Veir.Interfaces.ConstantLikeInterfaces
public import Veir.Interpreter.Basic
public import Veir.Interpreter.Evaluate

/-!
  # Constant folding decisions

  Each opcode can be queried through `OpCode.foldsTo` to determine whether it
  folds for a given pattern of constant operands. This module never mutates
  the IR or materializes constants.
-/

public section

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
      and return the result. -/
  | evaluate

/-- The resolved decision of whether and how an operation folds. -/
inductive FoldDecision where
  /-- Use operand `j` in place of the result. -/
  | useOperand (j : Nat)
  /-- Use the runtime constant `rv` in place of the result. -/
  | useConstant (rv : RuntimeValue)
  /-- The operation does not fold with the supplied operand information. -/
  | noFold

/-- Construct a poison outcome for a supported result type. -/
private def poisonOutcome (resultTypes : Array TypeAttr) : Option FoldOutcome :=
  match resultTypes[0]? with
  | some resultType =>
    match resultType.val with
    | .integerType intTy => some (.constant (.int intTy.bitwidth .poison))
    | _ => none
  | none => none

/--
  Fold table for `arith` operations with partially-constant operands.
  The all-constant case is handled generically by `OpCode.foldsTo`.
-/
def Arith.foldsTo (op : Arith) (_properties : HasDialectOpInfo.propertiesOf op)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
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
  -- condition makes the result poison regardless of either arm.
  | .select =>
    match constOperands.toList with
    | [some (.int 1 (.val c)), _, _] =>
      if c = 1 then some (.operand 1) else some (.operand 2)
    | [some (.int 1 .poison), _, _] => poisonOutcome resultTypes
    | _ => none
  | _ => none

/--
  Fold table for `llvm` operations with partially-constant operands.
  See `Arith.foldsTo`.
-/
def Llvm.foldsTo (op : Llvm) (_properties : HasDialectOpInfo.propertiesOf op)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
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
    | [some (.int 1 .poison), _, _] => poisonOutcome resultTypes
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

/-- The positive modulus and storage width of a single `mod_arith` result. -/
private def modArithResultInfo (resultTypes : Array TypeAttr) : Option (Nat × Nat) := do
  let [resultType] := resultTypes.toList | none
  let .modArithType modArithType := resultType.val | none
  if modArithType.modulus.value ≤ 0 then none
  else some (modArithType.modulus.value.toNat, modArithType.modulus.type.bitwidth)

/--
  Fold table for partially-constant `mod_arith` operations.

  Returning an operand for the usual zero and one identities would require
  that operand to be a canonical residue. `RuntimeValue.Conforms` guarantees
  only its storage width, so the only partial fold here is multiplication by
  zero, whose constant result refines a poison operand as well.
-/
def Mod_Arith.foldsTo (op : Mod_Arith) (_properties : HasDialectOpInfo.propertiesOf op)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    Option FoldOutcome := do
  let (modulus, bitwidth) ← modArithResultInfo resultTypes
  let isZeroResidue {w : Nat} (value : BitVec w) :=
    value.toNat % modulus = 0
  match op with
  | .mul =>
    match constOperands.toList with
    | [some (.int _ (.val c)), _] =>
      if isZeroResidue c then some (.constant (.int bitwidth (.val 0))) else none
    | [_, some (.int _ (.val c))] =>
      if isZeroResidue c then some (.constant (.int bitwidth (.val 0))) else none
    | _ => none
  | .add | .sub | .constant => none

/--
  Query whether an operation folds, given its result types and the values of
  its constant-defined operands (`constOperands[i] = some rv` iff operand `i`
  is defined by a constant-like operation with value `rv`).

  When every operand is a known constant and the opcode is evaluable, the
  answer is always `.evaluate` — no per-opcode logic is involved. Otherwise
  the per-dialect fold tables are consulted for identities.
-/
def OpCode.foldsTo (opCode : OpCode) (properties : HasOpInfo.propertiesOf opCode)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    Option FoldOutcome :=
  if opCode.isFoldEvaluable properties && !constOperands.isEmpty
      && constOperands.all (·.isSome) then
    some .evaluate
  else
    match opCode with
    | .arith op => Arith.foldsTo op properties resultTypes constOperands
    | .llvm op => Llvm.foldsTo op properties resultTypes constOperands
    | .riscv op => Riscv.foldsTo op properties resultTypes constOperands
    | .mod_arith op => Mod_Arith.foldsTo op properties resultTypes constOperands
    | _ => none

namespace Fold.Impl

/-- Return a constant decision only when `rv` conforms to the sole result type. -/
private def conformingConstantDecision
    (resultTypes : Array TypeAttr) (rv : RuntimeValue) : FoldDecision :=
  match resultTypes[0]? with
  | some resultType =>
    if rv.Conforms resultType then .useConstant rv else .noFold
  | none => .noFold

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
    let values := constOperands.map (·.get!)
    match (foldEvaluate opType properties resultTypes values : Option (UBOr _)) with
    | none => .noFold
    | some (.ok results) =>
      match results.toList with
      | [result] => conformingConstantDecision resultTypes result
      | _ => .noFold
    | some .ub =>
      match resultTypes[0]!.val with
      | .integerType intTy =>
        conformingConstantDecision resultTypes (.int intTy.bitwidth .poison)
      | _ => .noFold

def foldDecisionForOp (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opInBounds : op.InBounds ctx.raw)
    (constOperands : Array (Option RuntimeValue)) : FoldDecision :=
  if constOperands.size ≠ op.getNumOperands ctx.raw opInBounds then
    .noFold
  else
    let opType := op.getOpType ctx.raw opInBounds
    foldDecision opType
      (op.getProperties ctx.raw opType opInBounds (by grind))
      (op.getResultTypes ctx.raw opInBounds) constOperands

end Fold.Impl

end Veir
