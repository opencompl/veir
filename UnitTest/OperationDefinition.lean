import Veir.GlobalOpInfo

open Veir

private def arithAddiDefinition : OperationDefinition :=
  (Arith.operationDefinition? .addi).getD {}

private def arithConstantDefinition : OperationDefinition :=
  (Arith.operationDefinition? .constant).getD {}

private def pdlReplaceDefinition : OperationDefinition :=
  (PDL.operationDefinition? .replace).getD {}

/-! Static bindings retain declared order and point to existing storage keys. -/
#guard arithAddiDefinition.findOperand? "lhs" = some 0
#guard arithAddiDefinition.findOperand? "rhs" = some 1
#guard arithAddiDefinition.findResult? "result" = some 0
#guard (arithAddiDefinition.findProperty? "overflowFlags").map (·.storageKey) =
  some "overflowFlags"
#guard (arithAddiDefinition.findProperty? "overflowFlags").map (·.presence) =
  some .optional
#guard (arithConstantDefinition.findProperty? "value").map (·.storageKey) = some "value"
#guard pdlReplaceDefinition.findOperand? "replOperation" = some 1
#guard (PDL.operationDefinition? .erase).isNone

private def fieldKindsDefinition : OperationDefinition := {
  attributes := #[{ name := "tag", storageKey := "shared" }]
  properties := #[{ name := "flags", storageKey := "shared" }]
}

#guard (fieldKindsDefinition.findAttribute? "tag").map (·.storageKey) = some "shared"
#guard (fieldKindsDefinition.findProperty? "flags").map (·.storageKey) = some "shared"
#guard fieldKindsDefinition.validate = .ok ()

/-! Dialect metadata is available through the global opcode interface. -/
#guard (OpCode.operationDefinition? (.arith .addi)).isSome
#guard (OpCode.operationDefinition? (.arith .muli)).isNone
#guard (OpCode.operationDefinition? (.pdl .replace)).isSome

/-! Fixed groups resolve without per-instance segment metadata. -/
#guard arithAddiDefinition.operands.resolveSizes 2 = .ok #[1, 1]
#guard arithAddiDefinition.results.resolveSizes 1 = .ok #[1]
#guard arithAddiDefinition.operands.resolveSizes 1 =
  .error "segment sizes describe 2 values, got 1"

/-! Optional and variadic groups use property-backed sizes. -/
#guard pdlReplaceDefinition.operands.resolveSizes 3 (some #[1, 0, 2]) =
  .ok #[1, 0, 2]
#guard pdlReplaceDefinition.operands.resolveSizes 3 =
  .error "missing segment sizes property 'operandSegmentSizes'"
#guard pdlReplaceDefinition.operands.resolveSizes 3 (some #[1, 2, 0]) =
  .error "group 'replOperation' does not accept segment size 2"

/-! Invalid duplicate bindings and ambiguous dynamic groups are rejected. -/
private def duplicateNameDefinition : OperationDefinition := {
  operands := { groups := #[
    NamedValueGroup.mk "value" .one,
    NamedValueGroup.mk "value" .one
  ] }
}

#guard match duplicateNameDefinition.validate with
  | .error _ => true
  | .ok _ => false

private def ambiguousGroupDefinition : OperationDefinition := {
  operands := { groups := #[
    NamedValueGroup.mk "maybe" .optional,
    NamedValueGroup.mk "rest" .variadic
  ] }
}

#guard match ambiguousGroupDefinition.validate with
  | .error _ => true
  | .ok _ => false
#guard match ambiguousGroupDefinition.operands.resolveSizes 2 with
  | .error _ => true
  | .ok _ => false

#guard arithAddiDefinition.validate = .ok ()
#guard arithConstantDefinition.validate = .ok ()
#guard pdlReplaceDefinition.validate = .ok ()
