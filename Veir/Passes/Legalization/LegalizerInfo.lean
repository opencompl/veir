module

public import Veir.GlobalOpInfo

/-!
# Legalization Rules

This file defines how a target specifies which GMIR operations it can select, and how the others
are legalized.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/include/llvm/CodeGen/GlobalISel/LegalizerInfo.h
-/

namespace Veir

public section

variable {opcode : GMIR}

/-!
## Legality queries

The legality of a gMIR operation depends on its opcode, on the type of each of its type groups (see
`GMIR.genericOpInfo`), and on its properties.
-/

/--
Low Level Type

The type's size in bits.
For legalization, we only care about the bits occupied by a *scalar*, not by floats or integers.

TODO: Make this a dedicated type once pointers or vectors are part of legalization.

Also see: https://llvm.org/docs/GlobalISel/GMIR.html#low-level-type
-/
abbrev LLT := Nat

/-- The low-level type of `type`. Returns `none` if `type` is not an integer type. -/
def LLT.ofType? (type : TypeAttr) : Option LLT :=
  match type.val with
  | .integerType type => some type.bitwidth
  | _ => none

/--
`LegalityQuery` bundles all the information that's needed to decide whether an `opcode` operation
is legal or not. LLVM's query has the immediate operands, which VeIR keeps in the properties.
-/
structure LegalityQuery (opcode : GMIR) where
  /-- The type of each type group of the operation. -/
  types : Array LLT
  /-- The properties of the operation. -/
  properties : GMIR.propertiesOf opcode

/--
The type of each type group of `op`, indexed by the type group.
The type groups in `GMIR.genericOpInfo` are expected to be numbered by the order in which they first appear.
-/
def GMIR.getTypeGroupTypes! (opCode : GMIR) (op : OperationPtr) (ctx : IRContext OpCode) :
    Array TypeAttr := Id.run do
  let mut types := #[]
  for (.type group, type) in opCode.getTypedGroups! op ctx do
    if group == types.size then
      types := types.push type
  return types

/-- The legality query of `op`. Returns `none` if one of its types is not a scalar integer. -/
def LegalityQuery.of? (ctx : IRContext OpCode) (op : OperationPtr) (opcode : GMIR) :
    Option (LegalityQuery opcode) := do
  let types ← (opcode.getTypeGroupTypes! op ctx).mapM LLT.ofType?
  return { types, properties := op.getProperties! ctx opcode }

/-- The common LLT of type group `typeIdx`. -/
def LegalityQuery.getLLT! (query : LegalityQuery opcode) (typeIdx : TypeGroup) : LLT :=
  let .type idx := typeIdx
  query.types[idx]!

/-- A condition on a legality query. -/
abbrev LegalityPredicate (opcode : GMIR) := LegalityQuery opcode → Bool

namespace LegalityPredicate

/-- True if type group `typeIdx` is `type`. -/
def typeIs (typeIdx : TypeGroup) (type : LLT) : LegalityPredicate opcode :=
  fun query => query.getLLT! typeIdx == type

/-- True if all of `predicates` hold. -/
def all (predicates : List (LegalityPredicate opcode)) : LegalityPredicate opcode :=
  fun query => predicates.all (· query)

end LegalityPredicate

/-!
## Legalization rules

A target gives a list of rules for each opcode. The legalizer takes the action of the first rule
that applies, and the operation is unsupported when no rule applies.
-/

/-- The action the legalizer takes on an operation. -/
inductive LegalizeAction where
  /--
  The operation is expected to be selectable directly by the target, and no transformation is
  necessary.
  -/
  | legal
  /-- The operation should be implemented with type group `typeIdx` widened to `newType`. -/
  | widenScalar (typeIdx : TypeGroup) (newType : LLT)
  /-- This operation is completely unsupported on the target. -/
  | unsupported

/-- A single legalization rule. Returns the action to take, or `none` if the rule does not apply. -/
abbrev LegalizeRule (opcode : GMIR) := LegalityQuery opcode → Option LegalizeAction

namespace LegalizeRule

/-- The operation is legal if `predicate` is true. -/
def legalIf (predicate : LegalityPredicate opcode) : LegalizeRule opcode :=
  fun query => if predicate query then some .legal else none

/-- The operation is legal when type group 0 is any type in `types`. -/
def legalFor (types : List LLT) : LegalizeRule opcode :=
  legalIf fun query => types.contains (query.getLLT! (.type 0))

/-- The operation is legal when type groups 0 and 1 are any type pair in `pairs`. -/
def legalForTypePairs (pairs : List (LLT × LLT)) : LegalizeRule opcode :=
  legalIf fun query => pairs.contains (query.getLLT! (.type 0), query.getLLT! (.type 1))

/-- The operation is always legal. -/
def alwaysLegal : LegalizeRule opcode :=
  legalIf fun _ => true

/-- Widen the scalar to the one selected by `mutation` if `predicate` is true. -/
def widenScalarIf (predicate : LegalityPredicate opcode)
    (mutation : LegalityQuery opcode → TypeGroup × LLT) : LegalizeRule opcode :=
  fun query => if predicate query then
    let (typeIdx, newType) := mutation query
    some (.widenScalar typeIdx newType)
  else none

/-- Ensure the scalar of type group `typeIdx` is at least as wide as `type`. -/
def minScalar (typeIdx : TypeGroup) (newType : LLT) : LegalizeRule opcode :=
  widenScalarIf (fun query => (query.getLLT! typeIdx) < newType) fun _ => (typeIdx, newType)

end LegalizeRule

/-- The legalization rules of a target. -/
structure LegalizerInfo where
  /-- The rules of each opcode, in the order they are tried. -/
  rules : (opcode : GMIR) → List (LegalizeRule opcode)

/--
Determine what action should be taken to legalize `op`, using the first rule of `opcode` that
applies.
-/
def LegalizerInfo.getAction (info : LegalizerInfo) (ctx : IRContext OpCode) (op : OperationPtr)
    (opcode : GMIR) : LegalizeAction := Id.run do
  let some query := LegalityQuery.of? ctx op opcode | return .unsupported
  return (info.rules opcode).findSome? (· query) |>.getD .unsupported

end

end Veir
