# Puddle Prototype Plan

## Goal

Build a minimal Puddle prototype that proves one rewrite end-to-end:

```text
%zero = arith.constant 0
%root = arith.addi %x, %zero
────────────────────────────────
replace %root with %x
```

The prototype must compile to a real `LocalRewritePattern` and derive
`LocalRewritePattern.PreservesSemantics`. The user-facing correctness proof should express the
algebraic fact `x + 0 = x` without mentioning IR pointers, dominance, interpreter states, or value
mappings.

Operation creation is intentionally excluded from the initial prototype. `CreateProg` will only be
introduced after the match-and-replace-only design has reached `PreservesSemantics` end-to-end.

## Initial rule shape

The first version has only two components:

```text
Puddle.MatchProg → Puddle.Replacement
```

It compiles successful rewrites to:

```lean
some (ctx, some (#[], replacementValues))
```

The input context is unchanged and the list of newly created operations is always empty.

## Milestones

### 1. Implement the minimal matcher

- [x] Match a distinguished `arith.addi` root operation.
- [x] Bind the first operand as `x`.
- [x] Follow the second operand to its defining operation.
- [x] Check that the defining operation is `arith.constant` with value zero.
- [x] Export only the matched references needed by replacement and semantic validation.
- [x] Treat matching constraints as hypotheses of rule validity, rather than attempting to prove
      that every possible assignment satisfies them.

Do not generalize the matcher beyond what `addZero` needs at this stage.

### 2. Implement terminal replacement and `Puddle.Pattern`

- [x] Define a terminal `Puddle.Replacement` that selects existing matched values.
- [x] Ensure the replacement cannot select the root's own results.
- [x] Ensure the number of replacement values agrees with the number of root results; supporting
      only one result in the prototype is acceptable.
- [x] Define the prototype `Puddle.Pattern` as a `Puddle.MatchProg` paired with its
      `Puddle.Replacement`.
- [x] Make replacement terminal: no matching or other actions can occur after it.
- [x] Define the minimal `addZero` rule using the matcher and terminal replacement.

There is no `CreateProg` in this representation yet.

### 3. Define minimal algebraic validity

- [x] Define only the denotational semantics needed for the prototype matcher and replacement.
- [x] State `Puddle.Pattern.Valid` as refinement in the direction required by
      `LocalRewritePattern.PreservesSemantics`.
- [x] Provide an equality-based introduction theorem so ordinary rewrites can be proven by
      equality.
- [x] Prove `addZero_valid` using the algebraic fact `x + 0 = x`.

The `addZero_valid` proof must not mention:

- `WfIRContext`;
- `OperationPtr` or `ValuePtr`;
- dominance;
- `InterpreterState`;
- `EquationLemmaAt` or `DefinesDominating`;
- `LocalRewritePattern.mapping`.

### 4. Compile to `LocalRewritePattern`

- [x] Run the matcher against the supplied context and root.
- [x] Resolve the terminal replacement against the successful match assignment.
- [x] Return the unchanged context.
- [x] Return `newOps := #[]`.
- [x] Return the resolved matched values as `newValues`.
- [x] Ensure all non-match cases leave the context unchanged.

Test at least these cases:

- [x] Successful `x + 0` match.
- [x] Wrong root opcode.
- [x] Wrong operand count.
- [x] Second operand has no defining operation.
- [x] Defining operation is not `arith.constant`.
- [x] Constant value is not zero.

### 5. Reach `PreservesSemantics` with the prototype

- [x] Prove that the compiled `addZero` rule satisfies
      `LocalRewritePattern.PreservesSemantics`.
- [x] Introduce `addZero_preservesSemantics` here, once its implementation and supporting
      definitions are ready; do not maintain an earlier placeholder theorem.
- [x] It is acceptable for this first bridge proof to be specialized to `addZero`.
- [x] Record the reusable interpreter lemmas that the proof actually requires.
- [x] Keep all IR, dominance, state-refinement, and value-mapping reasoning inside the bridge.

Likely supporting facts include:

- obtaining the runtime value of the dominating matched operand `x`;
- obtaining the runtime result of the matched constant from `EquationLemmaAt`;
- relating the matched root operation to its algebraic denotation;
- simplifying `interpretOpList []`;
- resolving `#[x]` in the target state;
- turning result equality into runtime-value refinement.

This is the decisive prototype milestone. Do not introduce `CreateProg` before it is complete.

### 6. Generalize semantic preservation

- [x] Strengthen denotational validity so unsupported matcher operations cannot make validity
      vacuously true.
- [x] Preserve support for constrained `arith.constant` and unconstrained `arith.addi`.
- [x] Prove the generic bridge:

```lean
theorem Puddle.Pattern.Valid.preservesSemantics
    {anyRewrite : Puddle.Pattern}
    (h : anyRewrite.Valid)
    (hOps : anyRewrite.compile.ReturnOps)
    (hCtx : anyRewrite.compile.ReturnCtxChanges)
    (hBounds : anyRewrite.compile.ReturnValuesInBounds)
    (hValues : anyRewrite.compile.ReturnValues) :
    anyRewrite.compile.PreservesSemantics hOps hCtx hBounds hValues
```

- [x] Keep the four structural obligations explicit; deriving them remains step 7.
- [x] Make `addZero_preservesSemantics` a short specialization of the generic theorem.
- [x] Keep runtime matching behavior unchanged.
- [x] Add proof-level regressions for the generic theorem and unsupported denotations.

### 7. Derive structural obligations

For compiled match-and-replace-only rules, prove the applicable obligations generically:

- [ ] `ReturnsCtxNoChanges`;
- [ ] `ReturnCtxChanges`;
- [ ] `ReturnOps`;
- [ ] `ReturnOpsNodup`;
- [ ] `ReturnValues`;
- [ ] `ReturnValuesInBounds`;
- [ ] `ReturnValuesNotOwnResults`;
- [ ] `ReturnValuesDominate`;
- [ ] `MatchedOpHasNoRegions`.

Full `LocalRewritePattern.Sound` may remain deferred if its rewrite-level dominance or verification
obligations require work unrelated to the semantic vertical slice.

### 8. Introduce `CreateProg`

Only after the match-and-replace rule has reached `PreservesSemantics` and its applicable
structural obligations have been derived, introduce a distinct creation phase:

```text
Puddle.MatchProg → Puddle.CreateProg → Puddle.Replacement
```

- [x] Add exactly one operation-creation command initially.
- [x] Permit creation operands to use safe matched values.
- [x] Permit replacement to select the created result.
- [x] Ensure matching is unavailable once creation starts.
- [x] Ensure replacement remains terminal.
- [x] Compile the created operation into `newOps`.
- [x] Add one end-to-end rule that creates one operation and reaches `PreservesSemantics`.

### 9. Extend incrementally

After the one-created-operation rule works:

- [x] Generalize the semantic bridge to multiple sequentially created operations.
- [ ] Add general operation properties.
- [x] Add explicit result types.
- [x] Add multiple root results and replacements.
- [ ] Add operations with multiple created results.
- [ ] Add richer nested matching.
- [ ] Add more dialects and opcodes.
- [ ] Add UB/refinement-sensitive examples.
- [ ] Complete the remaining `LocalRewritePattern.Sound` obligations.
- [x] Add an ordered builder DSL for creation programs, including handles for consuming earlier
      created results.
- [ ] Add further ergonomic surface syntax and proof-simplification support.
- [ ] Add negative tests for illegal phase ordering and unavailable values.

## Deferred from the prototype

Until the initial bridge is complete, do not add:

- `CreateProg` or operation-creation commands;
- a polished `puddle do` macro;
- arbitrary operation graphs;
- multiple results;
- regions or control flow;
- memory-reading or side-effecting operations;
- comprehensive simplification tactics;
- complete dialect genericity;
- full `LocalRewritePattern.Sound`, unless it follows immediately from the prototype.

## Definition of done for the prototype

The initial prototype is complete when:

1. `addZero` performs a real runtime match and compiles to a real `LocalRewritePattern`.
2. Its successful result is `(ctx, some (#[], #[x]))`.
3. `addZero_valid` is an algebraic proof equivalent to `x + 0 = x`.
4. `addZero_preservesSemantics` contains no `sorry` and follows from that validity proof.
5. Pattern authors do not need to understand or prove dominance, interpreter-state, or value-mapping
   details.
6. No `CreateProg` implementation was needed to reach this point.
