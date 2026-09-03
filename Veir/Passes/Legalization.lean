module

public import Veir.Pass
public import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
public import Veir.PatternRewriter.Basic

/-!
  This pass legalizes LLVM operations to prepare for instruction selection.
  For now, this is restricted to widening integer values.
-/

namespace Veir

public section

/--
This wip implements an equivalent of LLVM's GISel framework for building legalization passes.
https://github.com/llvm/llvm-project/blob/main/llvm/include/llvm/CodeGen/GlobalISel/LegalizerInfo.h
-/

-- TODO: Most of these are unimplemented.
inductive LegalizeAction where
  | legal
  | narrowScalar
  | widenScalar
  | fewerElements
  | moreElements
  | bitcast
  | lower
  | libcall
  | custom
  | unsupported
  | notFound
  deriving Repr, BEq

/--
  The LegalityQuery object bundles together all the information that's needed to decide whether a
  given operation is legal or not.
-/
structure LegalityQuery where
  opcode : OpCode
  -- sizes[0] is always the bitwidth of the result type.
  -- sizes[1..] for when the legality also depends on operand types.
  sizes : Array Nat

/--
  The result of a query. It either indicates a final answer of Legal or Unsupported or describes an
  action that must be taken to make an operation more legal.
-/
structure LegalizeActionStep where
  action : LegalizeAction
  typeIndex : Nat := 0
  newBw : Nat := 0

abbrev LegalityPredicate := LegalityQuery → Bool
abbrev LegalizeMutation := LegalityQuery → Nat × Nat

namespace LegalityPredicates

-- NOTE: These are not yet well aligned with LLVM's legality predicates.

def sizeInSet (typeIndex : Nat) (sizes : Array Nat) : LegalityPredicate :=
  fun q => sizes.contains q.sizes[typeIndex]!

def sizeNotPow2 (typeIndex : Nat) : LegalityPredicate :=
  fun q => !Nat.isPowerOfTwo q.sizes[typeIndex]!

def scalarNarrowerThan (typeIndex bw : Nat) : LegalityPredicate :=
  fun q => q.sizes[typeIndex]! < bw

end LegalityPredicates

namespace LegalityMutations

def widenScalarToNextPow2 (typeIndex : Nat) : LegalizeMutation :=
  fun q => (typeIndex, Nat.nextPowerOfTwo q.sizes[typeIndex]!)

def clampScalar (typeIndex minBw maxBw : Nat) : LegalizeMutation :=
  fun q => (typeIndex, min maxBw (max minBw q.sizes[typeIndex]!))

end LegalityMutations

/--
  A single rule in a legalizer info ruleset.
  The specified action is chosen when the predicate is true. Where appropriate for the action
  (e.g. for WidenScalar) the new type is selected using the given mutator.
-/
structure LegalizeRule where
  predicate : LegalityPredicate
  action : LegalizeAction
  mutation : LegalizeMutation

abbrev LegalizeRuleSet := Array LegalizeRule

private def LegalizeRule.apply (rule : LegalizeRule) (q : LegalityQuery) : Option LegalizeActionStep :=
  if rule.predicate q then
    let (typeIndex, newBw) := rule.mutation q
    some { action := rule.action, typeIndex, newBw }
  else
    none

def legalFor (sizes : Array Nat) : LegalizeRule :=
  { predicate := LegalityPredicates.sizeInSet 0 sizes
    action := .legal
    mutation := fun _ => (0, 0) }

def customFor (sizes : Array Nat) : LegalizeRule :=
  { predicate := LegalityPredicates.sizeInSet 0 sizes
    action := .custom
    mutation := fun _ => (0, 0) }

def widenScalarToNextPow2 (typeIndex : Nat) : LegalizeRule :=
  { predicate := LegalityPredicates.sizeNotPow2 typeIndex
    action := .widenScalar
    mutation := LegalityMutations.widenScalarToNextPow2 typeIndex }

def clampScalar (typeIndex minBw maxBw : Nat) : LegalizeRule :=
  { predicate := LegalityPredicates.scalarNarrowerThan typeIndex maxBw
    action := .widenScalar
    mutation := LegalityMutations.clampScalar typeIndex minBw maxBw }

structure LegalizerInfo where
  ruleSets : Std.HashMap OpCode LegalizeRuleSet := ∅
  legalizeCustom : LocalRewritePattern OpCode := fun ctx _ => some (ctx, none)

namespace LegalizerInfo

def defineRuleSet
    (info : LegalizerInfo)
    (ops : Array OpCode)
    (rules : LegalizeRuleSet) : LegalizerInfo :=
  { info with
    ruleSets := ops.foldl (fun m op => m.insert op rules) info.ruleSets }

def getAction (info : LegalizerInfo) (q : LegalityQuery) : LegalizeActionStep :=
  match info.ruleSets.get? q.opcode with
  | none => { action := .notFound }
  | some ruleset =>
    (ruleset.findSome? (·.apply q)).getD { action := .notFound }

end LegalizerInfo

end

/--
  Sigma type for an operation plus its properties.
-/
abbrev OpWithProp := (op : OpCode) × (propertiesOf op)

/--
  Converts the types of the arguments and result of a single-result binary operation.
-/
def convertBinaryOp (ctx : WfIRContext OpCode) (op : OperationPtr) (newtype : TypeAttr) (convLhs convRhs newOp convRes : OpWithProp) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let type := ((op.getResult 0).get! ctx.raw).type
  let [lhs, rhs] := (op.getOperands! ctx.raw).toList | return (ctx, none)
  let (ctx, lhsOp) ← WfRewriter.createOp! ctx convLhs.fst #[newtype] #[lhs] #[] #[] convLhs.snd none
  let (ctx, rhsOp) ← WfRewriter.createOp! ctx convRhs.fst #[newtype] #[rhs] #[] #[] convRhs.snd none
  let (ctx, newOp) ← WfRewriter.createOp! ctx newOp.fst #[newtype] #[lhsOp.getResult 0, rhsOp.getResult 0] #[] #[] newOp.snd none
  let (ctx, resOp) ← WfRewriter.createOp! ctx convRes.fst #[type] #[newOp.getResult 0] #[] #[] convRes.snd none
  return (ctx, some (#[lhsOp, rhsOp, newOp, resOp], #[resOp.getResult 0]))

/--
  Integer values can be zero-extended, sign-extended, or any-extended (i.e., extended with arbitrary bits).
-/
inductive IntegerExtKind
| any
| zero
| sign

/--
  Return the LLVM operation corresponding to an `IntegerExtKind`.
-/
def expandIntegerExtOp (type : IntegerExtKind) : ((op : OpCode) × propertiesOf op) :=
  match type with
  | .sign => .mk (OpCode.llvm .sext) ()
  | .zero => .mk (OpCode.llvm .zext) (.mk false)
  | .any => .mk (OpCode.llvm .zext) (.mk false) -- FIXME

/--
  Widen the operands and result type of a homogeneously-typed binary LLVM operation.
-/
def widenSimpleBinaryIntOp (ctx : WfIRContext OpCode) (op : OperationPtr) (newBw : Nat) (extType : IntegerExtKind) (newOp : Option OpWithProp := none) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let oldOp := Sigma.mk (op.getOpType! ctx.raw) (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
  let .integerType ⟨bw⟩ := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if bw ≥ newBw then return (ctx, none)
  let expandOp := expandIntegerExtOp extType
  convertBinaryOp ctx op (IntegerType.mk newBw) expandOp expandOp (newOp.getD oldOp) ⟨.llvm .trunc, .mk false false⟩

def queryOf (ctx : WfIRContext OpCode) (op : OperationPtr) : Option LegalityQuery := do
  let opcode := op.getOpType! ctx.raw
  let resultType : TypeAttr ← (op.getResultTypes! ctx.raw)[0]?
  -- Skips over types without bitwidth.
  let bw ← Attribute.bitwidthOfType resultType
  some { opcode, sizes := #[bw] }

def widenScalar (ctx : WfIRContext OpCode) (op : OperationPtr) (newBw : Nat) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  match op.getOpType! ctx.raw with
  | .llvm .add =>
    widenSimpleBinaryIntOp ctx op newBw .any (some ⟨.llvm .add, .mk false false⟩)
  | .llvm .sub =>
    widenSimpleBinaryIntOp ctx op newBw .any (some ⟨.llvm .sub, .mk false false⟩)
  | .llvm .mul =>
    widenSimpleBinaryIntOp ctx op newBw .any (some ⟨.llvm .mul, .mk false false⟩)
  | .llvm .and =>
    widenSimpleBinaryIntOp ctx op newBw .any (some ⟨.llvm .and, ()⟩)
  | .llvm .xor =>
    widenSimpleBinaryIntOp ctx op newBw .any (some ⟨.llvm .xor, ()⟩)
  | .llvm .or =>
    widenSimpleBinaryIntOp ctx op newBw .any (some ⟨.llvm .or, .mk false⟩)
  | _ => return (ctx, none)

public def legalizeInstrStep (info : LegalizerInfo) (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  match queryOf ctx op with
  | none => some (ctx, none)
  | some q =>
    let step := info.getAction q
    match step.action with
    | .legal => some (ctx, none)
    | .widenScalar => widenScalar ctx op step.newBw
    | .custom => info.legalizeCustom ctx op
    | _ => some (ctx, none)

end Veir
