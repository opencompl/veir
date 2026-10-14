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

/-! Dialect metadata is available through the global opcode interface. -/
#guard (OpCode.operationDefinition? (.arith .addi)).isSome
#guard (OpCode.operationDefinition? (.arith .muli)).isNone
#guard (OpCode.operationDefinition? (.pdl .replace)).isSome

/-! Fixed groups resolve without per-instance segment metadata. -/
#guard resolveSizes arithAddiDefinition.operands 2 = .ok #[1, 1]
#guard resolveSizes arithAddiDefinition.results 1 = .ok #[1]
#guard resolveSizes arithAddiDefinition.operands 1 =
  .error "segment sizes describe 2 values, got 1"
#guard resolveSizes arithAddiDefinition.operands 2 (some #[1]) =
  .error "expected 2 segment sizes, got 1"

/-! Optional and variadic groups use property-backed sizes. -/
#guard resolveSizes pdlReplaceDefinition.operands 3 (some #[1, 0, 2]) =
  .ok #[1, 0, 2]
#guard resolveSizes pdlReplaceDefinition.operands 2 (some #[1, 1, 0]) =
  .ok #[1, 1, 0]
#guard resolveSizes pdlReplaceDefinition.operands 1 (some #[1, 0, 0]) =
  .ok #[1, 0, 0]
#guard resolveSizes pdlReplaceDefinition.operands 3 =
  .error "segment sizes are required when multiple operand or result groups are dynamic"
#guard resolveSizes pdlReplaceDefinition.operands 3 (some #[1, 2, 0]) =
  .error "group 'replOperation' does not accept segment size 2"
#guard resolveSizes pdlReplaceDefinition.operands 5 (some #[1, 1, 1]) =
  .error "segment sizes describe 3 values, got 5"
#guard usesSegmentSizes pdlReplaceDefinition.operands

/-! A lone dynamic group is inferred from the flattened value count. -/
private def singleVariadicGroups : Array NamedValueGroup :=
  #[NamedValueGroup.mk "rest" .variadic]

#guard resolveSizes singleVariadicGroups 3 = .ok #[3]
#guard resolveSizes singleVariadicGroups 0 = .ok #[0]

private def singleOptionalGroups : Array NamedValueGroup :=
  #[NamedValueGroup.mk "maybe" .optional]

#guard resolveSizes singleOptionalGroups 0 = .ok #[0]
#guard resolveSizes singleOptionalGroups 1 = .ok #[1]
#guard match resolveSizes singleOptionalGroups 2 with
  | .error _ => true
  | .ok _ => false

private def fixedPlusVariadicGroups : Array NamedValueGroup :=
  #[
    NamedValueGroup.mk "first" .one,
    NamedValueGroup.mk "rest" .variadic
  ]

#guard resolveSizes fixedPlusVariadicGroups 0 =
  .error "expected at least 1 values, got 0"
#guard resolveSizes fixedPlusVariadicGroups 4 = .ok #[1, 3]

/-! Result-side dynamic groups are inferred or use `resultSegmentSizes`-backed sizes. -/
private def resultSegmentsDefinition : OperationDefinition := {
  results := #[
    NamedValueGroup.mk "fixed" .one,
    NamedValueGroup.mk "rest" .variadic
  ]
}

#guard resolveSizes resultSegmentsDefinition.results 3 (some #[1, 2]) =
  .ok #[1, 2]
#guard resolveSizes resultSegmentsDefinition.results 3 = .ok #[1, 2]
#guard !usesSegmentSizes resultSegmentsDefinition.results

private def multiDynamicResultsDefinition : OperationDefinition := {
  results := #[
    NamedValueGroup.mk "maybe" .optional,
    NamedValueGroup.mk "rest" .variadic
  ]
}

#guard usesSegmentSizes multiDynamicResultsDefinition.results
#guard resolveSizes multiDynamicResultsDefinition.results 2 =
  .error "segment sizes are required when multiple operand or result groups are dynamic"

/-! Ambiguous dynamic groups resolve only with explicit sizes. -/
private def ambiguousGroupDefinition : OperationDefinition := {
  operands := #[
    NamedValueGroup.mk "maybe" .optional,
    NamedValueGroup.mk "rest" .variadic
  ]
}

#guard match resolveSizes ambiguousGroupDefinition.operands 2 with
  | .error _ => true
  | .ok _ => false

#guard !usesSegmentSizes arithAddiDefinition.operands
#guard arithAddiDefinition.findOperand? "lhs" =
  findGroupIndex? arithAddiDefinition.operands "lhs"
