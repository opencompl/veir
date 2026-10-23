module

public import Veir.GlobalOpInfo
public import Veir.PatternRewriter.Puddle.Definitions

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

For legalization, we only care about the bits occupied by a *scalar*, not by floats or integers.

Also see: https://llvm.org/docs/GlobalISel/GMIR.html#low-level-type
-/
inductive LLT where
  /-- A scalar of `width` bits. -/
  | scalar (width : Nat)
  /-- A pointer in address space `addressSpace`. -/
  | pointer (addressSpace : Nat)
deriving Inhabited, Repr, DecidableEq

/--
The low-level type of `type`. Returns `none` if `type` is neither an integer nor a pointer type.
A `!llvm.ptr` has no address space, so it is in address space 0.
-/
def LLT.ofType? (type : TypeAttr) : Option LLT :=
  match type.val with
  | .integerType type => some (.scalar type.bitwidth)
  | .llvmPointerType _ => some (.pointer 0)
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

/--
The legality query of an `opcode` operation whose type groups have `types` and whose properties are
`properties`. Returns `none` if one of the types has no low-level type.
TODO: Support the byte type.
-/
def LegalityQuery.ofTypes? (types : Array TypeAttr) (properties : GMIR.propertiesOf opcode) :
    Option (LegalityQuery opcode) := do
  return { types := ← types.mapM LLT.ofType?, properties }

/-- The legality query of `op`. Returns `none` if one of its types has no low-level type. -/
def LegalityQuery.of? (ctx : IRContext OpCode) (op : OperationPtr) (opcode : GMIR) :
    Option (LegalityQuery opcode) :=
  LegalityQuery.ofTypes? (opcode.getTypeGroupTypes! op ctx) (op.getProperties! ctx opcode)

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

/-- True if type group `typeIdx` is a scalar narrower than `width` bits. -/
def scalarNarrowerThan (typeIdx : TypeGroup) (width : Nat) : LegalityPredicate opcode :=
  fun query => match query.getLLT! typeIdx with
    | .scalar width' => width' < width
    | .pointer _ => false

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
  /-- The operation should be implemented with type group `typeIdx` widened to `width` bits. -/
  | widenScalar (typeIdx : TypeGroup) (width : Nat)
  /-- The operation is expanded into legal operations, as in `LegalizerHelper::lower`. -/
  | lower
  /-- The operation is legalized by the target's `legalizeCustom` pattern. -/
  | custom
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

/-- Lower the operation if `predicate` is true. -/
def lowerIf (predicate : LegalityPredicate opcode) : LegalizeRule opcode :=
  fun query => if predicate query then some .lower else none

/-- Always lower the operation. -/
def lower : LegalizeRule opcode :=
  lowerIf fun _ => true

/-- Use the target's `legalizeCustom` pattern if `predicate` is true. -/
def customIf (predicate : LegalityPredicate opcode) : LegalizeRule opcode :=
  fun query => if predicate query then some .custom else none

/-- Use the target's `legalizeCustom` pattern when type group 0 is any type in `types`. -/
def customFor (types : List LLT) : LegalizeRule opcode :=
  customIf fun query => types.contains (query.getLLT! (.type 0))

/--
Use the target's `legalizeCustom` pattern when type groups 0 and 1 are any type pair in `pairs`.
-/
def customForTypePairs (pairs : List (LLT × LLT)) : LegalizeRule opcode :=
  customIf fun query => pairs.contains (query.getLLT! (.type 0), query.getLLT! (.type 1))

/-- Widen the scalar to the width selected by `mutation` if `predicate` is true. -/
def widenScalarIf (predicate : LegalityPredicate opcode)
    (mutation : LegalityQuery opcode → TypeGroup × Nat) : LegalizeRule opcode :=
  fun query => if predicate query then
    let (typeIdx, width) := mutation query
    some (.widenScalar typeIdx width)
  else none

/-- Ensure the scalar of type group `typeIdx` is at least `width` bits wide. -/
def minScalar (typeIdx : TypeGroup) (width : Nat) : LegalizeRule opcode :=
  widenScalarIf (.scalarNarrowerThan typeIdx width) fun _ => (typeIdx, width)

end LegalizeRule

/-- The legalization rules of a target. -/
structure LegalizerInfo where
  /-- The rules of each opcode, in the order they are tried. -/
  rules : (opcode : GMIR) → List (LegalizeRule opcode)
  /-- The pattern that legalizes an operation whose action is `custom`, if any. -/
  legalizeCustom : (opcode : GMIR) → Option (Puddle.Pattern OpCode) := fun _ => none

/-- The action of the first rule of `opcode` that applies to `query`. -/
def LegalizerInfo.getActionFor (info : LegalizerInfo) (query : LegalityQuery opcode) :
    LegalizeAction :=
  (info.rules opcode).findSome? (· query) |>.getD .unsupported

/--
Determine what action should be taken to legalize `op`, using the first rule of `opcode` that
applies.
-/
def LegalizerInfo.getAction (info : LegalizerInfo) (ctx : IRContext OpCode) (op : OperationPtr)
    (opcode : GMIR) : LegalizeAction :=
  match LegalityQuery.of? ctx op opcode with
  | some query => info.getActionFor query
  | none => .unsupported

/--
Whether an `opcode` operation whose type groups have `types` and whose properties are `properties`
is legal.
-/
def LegalizerInfo.isLegal (info : LegalizerInfo) (opcode : GMIR) (types : Array TypeAttr)
    (properties : GMIR.propertiesOf opcode) : Bool :=
  match LegalityQuery.ofTypes? types properties with
  | none => false
  | some query => info.getActionFor query matches .legal

end

end Veir
