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
  The decision of whether and how an operation folds. Folding is currently
  restricted to operations with exactly one result.
-/
inductive FoldDecision where
  /-- Use operand `j` in place of the result. -/
  | useOperand (j : Nat)
  /-- Use the runtime constant `rv` in place of the result. -/
  | useConstant (rv : RuntimeValue)
  /-- The operation does not fold with the supplied operand information. -/
  | noFold

/-- Construct a poison decision for a supported result type. -/
private def poisonDecision (resultTypes : Array TypeAttr) : FoldDecision :=
  match resultTypes[0]? with
  | some resultType =>
    match resultType.val with
    | .integerType intTy => .useConstant (.int intTy.bitwidth .poison)
    | _ => .noFold
  | none => .noFold

/--
  Partial folds shared by `arith.select` and `llvm.select`.

  Besides a known condition, this handles poison arms, the boolean
  `select %c, true, false`, and equal known integer arms. Each case depends
  only on the select itself and its supplied constant operands.
-/
private def selectFoldsTo (resultTypes : Array TypeAttr)
    (constOperands : Array (Option RuntimeValue)) : FoldDecision :=
  match constOperands.toList with
  | [some (.int 1 (.val c)), _, _] =>
    if c = 1 then .useOperand 1 else .useOperand 2
  | [some (.int 1 .poison), _, _] => poisonDecision resultTypes
  | [_, some (.int _ .poison), _] => .useOperand 2
  | [_, _, some (.int _ .poison)] => .useOperand 1
  | [_, some (.int 1 (.val t)), some (.int 1 (.val f))] =>
    if t = 1 ∧ f = 0 then .useOperand 0
    else if t = f then .useConstant (.int 1 (.val t))
    else .noFold
  | [_, some (.int bw lhs), some (.int bw' rhs)] =>
    if h : bw' ≠ bw then .noFold else
    let rhs := rhs.cast (by simp at h; exact h)
    if lhs = rhs then .useConstant (.int bw lhs) else .noFold
  | [_, some (.byte bw lhs), some (.byte bw' rhs)] =>
    if h : bw' ≠ bw then .noFold else
    let rhs := rhs.cast (by simp at h; exact h)
    if lhs = rhs then .useConstant (.byte bw lhs) else .noFold
  | [_, some (.float bw lhs), some (.float bw' rhs)] =>
    if bw = bw' ∧ lhs.toBits = rhs.toBits then
      .useConstant (.float bw lhs)
    else .noFold
  | [_, some (.addr lhs), some (.addr rhs)] =>
    if lhs = rhs then .useConstant (.addr lhs) else .noFold
  | [_, some (.reg lhs), some (.reg rhs)] =>
    if lhs = rhs then .useConstant (.reg lhs) else .noFold
  | _ => .noFold

/--
  Fold table for `arith` operations with partially-constant operands.
  The all-constant case is handled generically by `OpCode.foldsTo`.
-/
def Arith.foldsTo (op : Arith) (properties : HasDialectOpInfo.propertiesOf op)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    FoldDecision :=
  match op with
  | .addi =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .subi =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .muli =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw (.val 0))
      else if c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .andi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw (.val 0))
      else if c = BitVec.allOnes bw then .useOperand 0
      else .noFold
    | _ => .noFold
  | .ori =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useOperand 0
      else if c = BitVec.allOnes bw then
        .useConstant (.int bw (.val (BitVec.allOnes bw)))
      else .noFold
    | _ => .noFold
  | .xori =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .shli =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .shrsi =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .shrui =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  -- Division / remainder by zero is immediate UB: fold to poison.
  | .divsi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .divui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .ceildivui | .ceildivsi | .floordivsi =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] =>
      if c = 1 then .useOperand 0 else .noFold
    | _ => .noFold
  | .remsi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 ∨ c = BitVec.allOnes bw then
        .useConstant (.int bw (.val 0))
      else .noFold
    | _ => .noFold
  | .remui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 then .useConstant (.int bw (.val 0))
      else .noFold
    | _ => .noFold
  | .maxsi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.intMin bw then .useOperand 0
      else if c = BitVec.intMax bw then .useConstant (.int bw (.val c))
      else .noFold
    | _ => .noFold
  | .minsi =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.intMax bw then .useOperand 0
      else if c = BitVec.intMin bw then .useConstant (.int bw (.val c))
      else .noFold
    | _ => .noFold
  | .maxui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useOperand 0
      else if c = BitVec.allOnes bw then .useConstant (.int bw (.val c))
      else .noFold
    | _ => .noFold
  | .minui =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.allOnes bw then .useOperand 0
      else if c = 0 then .useConstant (.int bw (.val 0))
      else .noFold
    | _ => .noFold
  | .cmpi =>
    match constOperands.toList with
    | [_, some (.int 1 (.val c))] =>
      if properties.predicate = .ne ∧ c = 0 then .useOperand 0
      else if properties.predicate = .eq ∧ c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .select => selectFoldsTo resultTypes constOperands
  | _ => .noFold

/--
  Fold table for `llvm` operations with partially-constant operands.
  See `Arith.foldsTo`.
-/
def Llvm.foldsTo (op : Llvm) (properties : HasDialectOpInfo.propertiesOf op)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    FoldDecision :=
  match op with
  | .add =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .sub =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .mul =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw (.val 0))
      else if c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .and =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw (.val 0))
      else if c = BitVec.allOnes bw then .useOperand 0
      else .noFold
    | _ => .noFold
  | .or =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useOperand 0
      else if c = BitVec.allOnes bw then
        .useConstant (.int bw (.val (BitVec.allOnes bw)))
      else .noFold
    | _ => .noFold
  | .xor =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .shl =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .lshr =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .ashr =>
    match constOperands.toList with
    | [_, some (.int _ (.val c))] => if c = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  -- Division / remainder by zero is immediate UB: fold to poison.
  | .sdiv =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .udiv =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .srem =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 ∨ c = BitVec.allOnes bw then
        .useConstant (.int bw (.val 0))
      else .noFold
    | _ => .noFold
  | .urem =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useConstant (.int bw .poison)
      else if c = 1 then .useConstant (.int bw (.val 0))
      else .noFold
    | _ => .noFold
  | .intr__smax =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.intMin bw then .useOperand 0
      else if c = BitVec.intMax bw then .useConstant (.int bw (.val c))
      else .noFold
    | _ => .noFold
  | .intr__smin =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.intMax bw then .useOperand 0
      else if c = BitVec.intMin bw then .useConstant (.int bw (.val c))
      else .noFold
    | _ => .noFold
  | .intr__umax =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = 0 then .useOperand 0
      else if c = BitVec.allOnes bw then .useConstant (.int bw (.val c))
      else .noFold
    | _ => .noFold
  | .intr__umin =>
    match constOperands.toList with
    | [_, some (.int bw (.val c))] =>
      if c = BitVec.allOnes bw then .useOperand 0
      else if c = 0 then .useConstant (.int bw (.val 0))
      else .noFold
    | _ => .noFold
  | .icmp =>
    match constOperands.toList with
    | [_, some (.int 1 (.val c))] =>
      if properties.predicate = .ne ∧ c = 0 then .useOperand 0
      else if properties.predicate = .eq ∧ c = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .select => selectFoldsTo resultTypes constOperands
  | _ => .noFold

/--
  Fold table for `riscv` operations with partially-constant operands.
  See `Arith.foldsTo`.

  Register-register operations are interpreted as `RISCV.f rs2 rs1` with
  `rs1 = operands[0]` and `rs2 = operands[1]`, so the identities below key off
  a constant `operands[1]`. RISC-V registers have no poison, and division by
  zero is defined (it is handled by generic all-constant evaluation), so no
  entry here produces poison. Immediate-carrying operations (`addi`, `slli`,
  ...) fold on their properties instead of an operand.
-/
def Riscv.foldsTo (op : Riscv) (properties : HasDialectOpInfo.propertiesOf op)
    (_resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    FoldDecision :=
  match op with
  | .add => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .sub => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .xor => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .or => match constOperands.toList with
    | [_, some (.reg c)] =>
      if c.val = 0 then .useOperand 0
      else if c.val = BitVec.allOnes 64 then
        .useConstant (.reg (Data.RISCV.li (BitVec.allOnes 64)))
      else .noFold
    | _ => .noFold
  | .and => match constOperands.toList with
    | [_, some (.reg c)] =>
      if c.val = 0 then .useConstant (.reg (Data.RISCV.li 0))
      else if c.val = BitVec.allOnes 64 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .mul => match constOperands.toList with
    | [_, some (.reg c)] =>
      if c.val = 0 then .useConstant (.reg (Data.RISCV.li 0))
      else if c.val = 1 then .useOperand 0
      else .noFold
    | _ => .noFold
  | .sll => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .srl => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .sra => match constOperands.toList with
    | [_, some (.reg c)] => if c.val = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .czeroeqz => match constOperands.toList with
    | [_, some (.reg c)] =>
      if c.val = 0 then .useConstant (.reg (Data.RISCV.li 0))
      else .useOperand 0
    | _ => .noFold
  | .czeronez => match constOperands.toList with
    | [_, some (.reg c)] =>
      if c.val = 0 then .useOperand 0
      else .useConstant (.reg (Data.RISCV.li 0))
    | _ => .noFold
  | .addi => match constOperands.toList with
    | [_] => if properties.value.value = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .ori => match constOperands.toList with
    | [_] => if properties.value.value = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .xori => match constOperands.toList with
    | [_] => if properties.value.value = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .andi => match constOperands.toList with
    | [_] =>
      if properties.value.value = 0 then
        .useConstant (.reg (Data.RISCV.li 0))
      else .noFold
    | _ => .noFold
  | .slli => match constOperands.toList with
    | [_] => if properties.value.value = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .srli => match constOperands.toList with
    | [_] => if properties.value.value = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | .srai => match constOperands.toList with
    | [_] => if properties.value.value = 0 then .useOperand 0 else .noFold
    | _ => .noFold
  | _ => .noFold

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
    FoldDecision :=
  match modArithResultInfo resultTypes with
  | none => .noFold
  | some (modulus, bitwidth) =>
    let isZeroResidue {w : Nat} (value : BitVec w) :=
      value.toNat % modulus = 0
    match op with
    | .mul =>
      match constOperands.toList with
      | [some (.int _ (.val c)), _] =>
        if isZeroResidue c then .useConstant (.int bitwidth (.val 0)) else .noFold
      | [_, some (.int _ (.val c))] =>
        if isZeroResidue c then .useConstant (.int bitwidth (.val 0)) else .noFold
      | _ => .noFold
    | .add | .sub | .constant => .noFold

/-- Return a constant decision only when `rv` conforms to the sole result type. -/
private def conformingConstantDecision
    (resultTypes : Array TypeAttr) (rv : RuntimeValue) : FoldDecision :=
  match resultTypes.toList with
  | [resultType] =>
    if rv.Conforms resultType then .useConstant rv else .noFold
  | _ => .noFold

/-- Resolve generic all-constant folding with the interpreter. -/
private def evaluatedFoldDecision (opCode : OpCode)
    (properties : HasOpInfo.propertiesOf opCode)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    FoldDecision :=
  let values := constOperands.map (·.get!)
  match (foldEvaluate opCode properties resultTypes values : Option (UBOr _)) with
  | none => .noFold
  | some (.ok results) =>
    match results.toList with
    | [result] => conformingConstantDecision resultTypes result
    | _ => .noFold
  | some .ub => poisonDecision resultTypes

/-- Reject malformed operand and constant decisions from dialect fold tables. -/
private def validateFoldDecision (resultTypes : Array TypeAttr)
    (constOperands : Array (Option RuntimeValue)) (decision : FoldDecision) :
    FoldDecision :=
  match decision with
  | .useOperand j =>
    if j < constOperands.size then .useOperand j else .noFold
  | .useConstant rv => conformingConstantDecision resultTypes rv
  | .noFold => .noFold

/--
  Query whether an operation folds, given its result types and the values of
  its constant-defined operands (`constOperands[i] = some rv` iff operand `i`
  is defined by a constant-like operation with value `rv`).

  When every operand is a known constant and the opcode is evaluable, the
  interpreter computes the decision directly. Otherwise the per-dialect fold
  tables are consulted for identities.
-/
def OpCode.foldsTo (opCode : OpCode) (properties : HasOpInfo.propertiesOf opCode)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    FoldDecision :=
  if resultTypes.size ≠ 1 then .noFold else
  let decision :=
    if opCode.isFoldEvaluable properties && !constOperands.isEmpty
        && constOperands.all (·.isSome) then
      evaluatedFoldDecision opCode properties resultTypes constOperands
    else
      match opCode with
      | .arith op => Arith.foldsTo op properties resultTypes constOperands
      | .llvm op => Llvm.foldsTo op properties resultTypes constOperands
      | .riscv op => Riscv.foldsTo op properties resultTypes constOperands
      | .mod_arith op => Mod_Arith.foldsTo op properties resultTypes constOperands
      | _ => .noFold
  validateFoldDecision resultTypes constOperands decision

namespace Fold.Impl

def foldDecision (opType : OpCode) (properties : HasOpInfo.propertiesOf opType)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue))
    : FoldDecision :=
  if opType.isConstantLike then .noFold else
  OpCode.foldsTo opType properties resultTypes constOperands

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
