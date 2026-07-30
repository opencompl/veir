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
  A resolved fold result, mirroring MLIR's `OpFoldResult`. Folding is currently
  restricted to operations with exactly one result.
-/
inductive FoldResult where
  /-- The result of the operation is refined by operand `j`. -/
  | operand (j : Nat)
  /-- The result of the operation is refined by the constant `rv`.
      `rv` may be poison, e.g. for operations that trigger immediate UB. -/
  | constant (rv : RuntimeValue)

/-- An opcode-level fold action that may still require interpreter evaluation. -/
inductive FoldAction where
  /-- A partial fold that is already resolved. -/
  | result (result : FoldResult)
  /-- All operands are constant: evaluate the operation with the interpreter
      and return the result. -/
  | evaluate

/-- Construct a poison result for a supported result type. -/
private def poisonOutcome (resultTypes : Array TypeAttr) : Option FoldResult :=
  match resultTypes[0]? with
  | some resultType =>
    match resultType.val with
    | .integerType intTy => some (.constant (.int intTy.bitwidth .poison))
    | _ => none
  | none => none

/--
  Partial folds shared by `arith.select` and `llvm.select`.

  Besides a known condition, this handles poison arms, the boolean
  `select %c, true, false`, and equal known integer arms. Each case depends
  only on the select itself and its supplied constant operands.
-/
private def selectFoldsTo (resultTypes : Array TypeAttr)
    (constOperands : Array (Option RuntimeValue)) : Option FoldResult :=
  match constOperands.toList with
  | [some (.int 1 (.val c)), _, _] =>
    if c = 1 then some (.operand 1) else some (.operand 2)
  | [some (.int 1 .poison), _, _] => poisonOutcome resultTypes
  | [_, some (.int _ .poison), _] => some (.operand 2)
  | [_, _, some (.int _ .poison)] => some (.operand 1)
  | [_, some (.int 1 (.val t)), some (.int 1 (.val f))] =>
    if t = 1 ∧ f = 0 then some (.operand 0)
    else if t = f then some (.constant (.int 1 (.val t)))
    else none
  | [_, some (.int bw lhs), some (.int bw' rhs)] =>
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    if lhs = rhs then some (.constant (.int bw lhs)) else none
  | [_, some (.byte bw lhs), some (.byte bw' rhs)] =>
    if h : bw' ≠ bw then none else
    let rhs := rhs.cast (by simp at h; exact h)
    if lhs = rhs then some (.constant (.byte bw lhs)) else none
  | [_, some (.float bw lhs), some (.float bw' rhs)] =>
    if bw = bw' ∧ lhs.toBits = rhs.toBits then
      some (.constant (.float bw lhs))
    else none
  | [_, some (.addr lhs), some (.addr rhs)] =>
    if lhs = rhs then some (.constant (.addr lhs)) else none
  | [_, some (.reg lhs), some (.reg rhs)] =>
    if lhs = rhs then some (.constant (.reg lhs)) else none
  | _ => none

/--
  Fold table for `arith` operations with partially-constant operands.
  The all-constant case is handled generically by `OpCode.foldsTo`.
-/
def Arith.foldsTo (op : Arith) (properties : HasDialectOpInfo.propertiesOf op)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    Option FoldResult :=
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
      if c = 0 then some (.constant (.int bw .poison))
      else if c = 1 then some (.operand 0)
      else none
    | _ => none
  | .divui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw .poison))
      else if c = 1 then some (.operand 0)
      else none
    | _ => none
  | .ceildivui | .ceildivsi | .floordivsi =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] =>
      if c = 1 then some (.operand 0) else none
    | _ => none
  | .remsi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw .poison))
      else if c = 1 ∨ c = BitVec.allOnes bw then
        some (.constant (.int bw (.val 0)))
      else none
    | _ => none
  | .remui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw .poison))
      else if c = 1 then some (.constant (.int bw (.val 0)))
      else none
    | _ => none
  | .maxsi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.intMin bw then some (.operand 0)
      else if c = BitVec.intMax bw then some (.constant (.int bw (.val c)))
      else none
    | _ => none
  | .minsi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.intMax bw then some (.operand 0)
      else if c = BitVec.intMin bw then some (.constant (.int bw (.val c)))
      else none
    | _ => none
  | .maxui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.operand 0)
      else if c = BitVec.allOnes bw then some (.constant (.int bw (.val c)))
      else none
    | _ => none
  | .minui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.allOnes bw then some (.operand 0)
      else if c = 0 then some (.constant (.int bw (.val 0)))
      else none
    | _ => none
  | .cmpi =>
    match constOperands.toList with
    | [_, some (.int 1 (.val c))] =>
      if properties.predicate = .ne ∧ c = 0 then some (.operand 0)
      else if properties.predicate = .eq ∧ c = 1 then some (.operand 0)
      else none
    | _ => none
  | .select => selectFoldsTo resultTypes constOperands
  | _ => none

/--
  Fold table for `llvm` operations with partially-constant operands.
  See `Arith.foldsTo`.
-/
def Llvm.foldsTo (op : Llvm) (properties : HasDialectOpInfo.propertiesOf op)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    Option FoldResult :=
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
      if c = 0 then some (.constant (.int bw .poison))
      else if c = 1 then some (.operand 0)
      else none
    | _ => none
  | .udiv =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw .poison))
      else if c = 1 then some (.operand 0)
      else none
    | _ => none
  | .srem =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw .poison))
      else if c = 1 ∨ c = BitVec.allOnes bw then
        some (.constant (.int bw (.val 0)))
      else none
    | _ => none
  | .urem =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.constant (.int bw .poison))
      else if c = 1 then some (.constant (.int bw (.val 0)))
      else none
    | _ => none
  | .intr__smax =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.intMin bw then some (.operand 0)
      else if c = BitVec.intMax bw then some (.constant (.int bw (.val c)))
      else none
    | _ => none
  | .intr__smin =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.intMax bw then some (.operand 0)
      else if c = BitVec.intMin bw then some (.constant (.int bw (.val c)))
      else none
    | _ => none
  | .intr__umax =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then some (.operand 0)
      else if c = BitVec.allOnes bw then some (.constant (.int bw (.val c)))
      else none
    | _ => none
  | .intr__umin =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.allOnes bw then some (.operand 0)
      else if c = 0 then some (.constant (.int bw (.val 0)))
      else none
    | _ => none
  | .icmp =>
    match constOperands.toList with
    | [_, some (.int 1 (.val c))] =>
      if properties.predicate = .ne ∧ c = 0 then some (.operand 0)
      else if properties.predicate = .eq ∧ c = 1 then some (.operand 0)
      else none
    | _ => none
  | .select => selectFoldsTo resultTypes constOperands
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
    Option FoldResult :=
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
    Option FoldResult := do
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
    Option FoldAction :=
  if opCode.isFoldEvaluable properties && !constOperands.isEmpty
      && constOperands.all (·.isSome) then
    some .evaluate
  else
    match opCode with
    | .arith op => (Arith.foldsTo op properties resultTypes constOperands).map .result
    | .llvm op => (Llvm.foldsTo op properties resultTypes constOperands).map .result
    | .riscv op => (Riscv.foldsTo op properties resultTypes constOperands).map .result
    | .mod_arith op =>
      (Mod_Arith.foldsTo op properties resultTypes constOperands).map .result
    | _ => none

namespace Fold.Impl

/-- Return a constant result only when `rv` conforms to the sole result type. -/
private def conformingConstantResult
    (resultTypes : Array TypeAttr) (rv : RuntimeValue) : Option FoldResult :=
  match resultTypes[0]? with
  | some resultType =>
    if rv.Conforms resultType then some (.constant rv) else none
  | none => none

def foldDecision (opType : OpCode) (properties : HasOpInfo.propertiesOf opType)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue))
    : Option FoldResult :=
  if opType.isConstantLike then none else
  if resultTypes.size ≠ 1 then none else
  match OpCode.foldsTo opType properties resultTypes constOperands with
  | none => none
  | some (.result (.operand j)) =>
    if j < constOperands.size then some (.operand j) else none
  | some (.result (.constant rv)) => conformingConstantResult resultTypes rv
  | some .evaluate =>
    let values := constOperands.map (·.get!)
    match (foldEvaluate opType properties resultTypes values : Option (UBOr _)) with
    | none => none
    | some (.ok results) =>
      match results.toList with
      | [result] => conformingConstantResult resultTypes result
      | _ => none
    | some .ub =>
      match resultTypes[0]!.val with
      | .integerType intTy =>
        conformingConstantResult resultTypes (.int intTy.bitwidth .poison)
      | _ => none

def foldDecisionForOp (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opInBounds : op.InBounds ctx.raw)
    (constOperands : Array (Option RuntimeValue)) : Option FoldResult :=
  if constOperands.size ≠ op.getNumOperands ctx.raw opInBounds then
    none
  else
    let opType := op.getOpType ctx.raw opInBounds
    foldDecision opType
      (op.getProperties ctx.raw opType opInBounds (by grind))
      (op.getResultTypes ctx.raw opInBounds) constOperands

end Fold.Impl

end Veir
