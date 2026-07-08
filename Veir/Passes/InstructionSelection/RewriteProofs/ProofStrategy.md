# Proving `PreservesSemantics` for RISC-V lowerings

This document describes the proof strategy used for the `lowerUnaryWLocal` lowerings
(`ctlz_local`, `cttz_local`, `ctpop_local` in `Veir/Passes/InstructionSelection/RISCV64.lean`)
and the `lowerBinopNotLocal` lowerings (`andn_local`, `orn_local`, `xnor_local` in
`Veir/Passes/InstructionSelection/RISCV64Sdag.lean`), and how to extend it to the other
`*_local` lowerings (`add_local`, `bswap_local`, `selectBinopImmLocal`, …).

## What we prove

For each lowering `foo_local : LocalRewritePattern OpCode` we prove

```lean
theorem foo_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics foo_local h h₂ h₃ h₄
```

`PreservesSemantics` (`Veir/PatternRewriter/Semantics.lean`) is a one-step forward simulation:

- **Given**: the pattern fired (`hpattern : foo_local ctx op = some (newCtx, some (newOps, newValues))`),
  the matched `op` interpreted successfully in a source state (`interpretOp op state = some (newState, cf)`),
  and a target state `state'` on `newCtx` that refines `state` at `InsertPoint.before op`
  (plus `Dom`/`Verified`/`DefinesDominating` side conditions).
- **Show**: `interpretOpList newOps.toList state'` succeeds with the *same* control flow `cf`,
  the *same* memory, and the values in `newValues` refine the matched op's result values
  (`sourceValues ⊒ targetValues`).

## Architecture: one proof per lowering *shape*, not per lowering

Lowerings sharing a shape are written as instances of a combinator in `RISCV64.lean`, and the
structural proof is done **once per combinator**. Currently:

- `lowerUnaryWLocal match? op64 op32 props64 props32` — match a single-operand LLVM integer op
  on `i64`/`i32`, then emit `castToRegLocal` → `op64` (or its `W` variant `op32` for `i32`) →
  `replaceWithRegLocal`. Its shared correctness proof is
  `lowerUnaryWLocal_preservesSemantics` (`RewriteProofs/LowerUnaryW.lean`).
- `lowerBinopNotLocal match? dst props` (`RISCV64Sdag.lean`) — match a two-operand LLVM integer
  op on `i64` one of whose operands is a `not` (`xor _, -1`, via `matchNot`, on either side),
  then emit `castToRegLocal` ×2 → binary reg-reg `dst` → `replaceWithRegLocal`. Its shared
  correctness proof is `lowerBinopNotLocal_preservesSemantics`
  (`RewriteProofs/LowerBinopNot.lean`). This is the first *DAG-matching* proof: it recovers the
  runtime value of the matched `not` from the `EquationLemmaAt` hypothesis (see
  "Matched-subgraph semantics" below).

The generic theorem is parameterized over everything opcode-specific:

```lean
theorem lowerUnaryWLocal_preservesSemantics
    (hMatchImplies : …)   -- syntactic facts from a successful match?     (Layer 2)
    (hVerified    : …)   -- Verified op ⇒ IsVerifiedIntegerUnop           (Layer 1)
    (hSemSrc      : …)   -- Llvm.interpretOp' srcOp … = srcFn             (rfl)
    (hSemR64      : …)   -- Riscv.interpretOp' op64 … = f64               (rfl)
    (hSemR32      : …)   -- Riscv.interpretOp' op32 … = f32               (rfl)
    (hRefine64    : …)   -- srcFn x props ⊒ toInt (f64 (toReg xt)) 64     (Layer 0)
    (hRefine32    : …)   -- srcFn x props ⊒ toInt (f32 (toReg xt)) 32     (Layer 0)
    : LocalRewritePattern.PreservesSemantics (lowerUnaryWLocal match? op64 op32 props64 props32) …
```

so instantiating it for a concrete lowering is a single term. The three `hSem*` interpreter
computation facts are discharged by `rfl` at concrete opcodes. Example (`ctlz`):

```lean
theorem ctlz_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics ctlz_local h h₂ h₃ h₄ :=
  lowerUnaryWLocal_preservesSemantics
    (srcOp := .intr__ctlz)
    (srcFn := fun x props => Data.LLVM.Int.ctlz x props.is_zero_poison)
    (f64 := Data.RISCV.clz) (f32 := Data.RISCV.clzw)
    (fun hMatch => matchCtlz_implies hMatch)
    (fun opVerif hOpType => OperationPtr.Verified.llvm_intr__ctlz opVerif hOpType)
    (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (fun _ _ props h => ctlz_isRefinedBy_toInt_clz props.is_zero_poison h)
    (fun _ _ props h => ctlz_isRefinedBy_toInt_clzw props.is_zero_poison h)
```

The instantiations live in `namespace Example` at the bottom of `LowerUnaryW.lean`.

## The per-lowering layers

### Layer 0 — Pure data refinement lemmas (per lowering, the only real new work)

The mathematical core, stated purely on `Data.LLVM.Int` / `Data.RISCV.Reg` with no IR at all,
one per (bitwidth, RISC-V opcode) branch:

```lean
theorem ctlz_isRefinedBy_toInt_clz {x xt : Data.LLVM.Int 64} (pf : Bool) (h : x ⊒ xt) :
    Data.LLVM.Int.ctlz x pf ⊒ RISCV.Reg.toInt (Data.RISCV.clz (LLVM.Int.toReg xt)) 64
```

i.e. *"round-tripping the (possibly more defined) operand through registers and running the
RISC-V instruction refines the LLVM operation"*.

Proof recipe: unfold refinement with `Data.LLVM.Int.isRefinedBy_iff`, split the
poison/value obligations, reduce the value equality to a bitvector goal, close with
`bv_decide` / `veir_bv_decide`. Poison bookkeeping (`isPoison_ctlz`, `getValueD_eq`, …) usually
falls to `grind`. For binops the statement takes two refined operands
(`h₁ : x ⊒ xt`, `h₂ : y ⊒ yt`).

These lemmas live next to the instantiation (`Example` namespace of `LowerUnaryW.lean`); if they
grow they can move to `Veir/Data/…/Lemmas.lean`.

### Layer 1 — Verifier facts (per LLVM opcode, mostly shared)

A `Verified.*` lemma in `Veir/Verifier.lean` extracting the structural facts the verifier
guarantees for the matched opcode:

```lean
theorem OperationPtr.Verified.llvm_intr__ctlz … : op.IsVerifiedIntegerUnop ctx
```

`IsVerifiedIntegerUnop` / `IsVerifiedIntegerBinop` bundle: operand/result/successor/region
counts, result type = operand type, and that type is an integer type. The heavy lifting is done
once per *shape* (`verifyIntegerUnop_eq_ok` + `verifyIntegerUnop_ok_of_Verified`); the
per-opcode lemma is then a three-liner that just points the dispatcher at the concrete opcode.
These exist for the unops and binops proven or planned so far. Ops with a different verifier
shape (e.g. `icmp`, `select`, `load`/`store`) need their own `IsVerified*` bundle, built the
same way.

### Layer 2 — Matcher facts (per LLVM opcode, mostly exist already)

`matchFoo_implies` in `Veir/Passes/Matching/Lemmas.lean`: what a successful `matchFoo` says
syntactically — op type, number of results, `getOperands! = #[operand…]`, and the properties
equation. These exist for most matchers already; if one is missing, copy an existing one
(the proof is `simp only [matchFoo, bind, Option.bind, pure]` + `grind`).

### Layer 3 — Matched-subgraph semantics (per *matcher*, only for DAG-matching patterns)

Patterns that inspect an operand's *defining op* (`matchNot`, `matchConstantIntVal`,
`getDefiningOp` + `matchShl`/…) match more than the interpreted op, so their proofs need the
*runtime* value of the matched subgraph, not just syntax. `PreservesSemantics` provides exactly
the needed invariant: `state.EquationLemmaAt (InsertPoint.before op)` says every *pure* op
dominating the match point has already been interpreted consistently into the source state.
`RewriteProofs/CommonGraphLemmas.lean` packages this per matcher:

- `OperationPtr.Pure.llvm_xor` / `.llvm_mlir__constant` — per-opcode purity facts (needed to
  invoke `EquationLemmaAt`; one short `split`/`simp` proof per opcode);
- `matchBinaryOp_interpretOp_unfold` / `constantOp_interpretOp_unfold` — unfold one successful
  `interpretOp` of the given shape into its result bindings; applied at `newState := state`
  they unfold an `EquationHolds` fact;
- `matchNot_getVar?_of_EquationLemmaAt` — the packaged lemma: a successful `matchNot v = some y`
  with `v` an operand of `op` yields `getVar? v = xor yv (-1)` where `yv` is `y`'s value, plus
  the structural side conditions (`y`'s type, dominance at `before op`, in-bounds,
  not-a-result-of-`op`) that `exists_refined_int_getVar?` needs.

A new matcher (e.g. `matchConstantIntVal` for the immediate-selection patterns) gets one such
lemma, built the same way: syntactic facts from the `match*_implies` lemma, dominance of the
defining op via `strictlyDominates_of_getDefiningOp!_of_mem_getOperands!` (plus
`strictlyDominates_trans` for deeper chains), purity, then `EquationHolds` unfolding.

## The shared machinery (already written, reused by every combinator proof)

### Source-interpretation unfolding

`matchUnaryOp_interpretOp_unfold` (`LowerUnaryW.lean`) is generic over the source opcode: given
the matcher's syntactic facts, the `hSemSrc` computation fact, and a successful
`interpretOp op state`, it produces

- the operand's runtime value **as an existential** (`∃ x, state.variables.getVar? operand = some (.int bw x)`),
- memory unchanged,
- the result variable bound to `srcFn x props`,
- `cf = none`.

The operand value is *derived* inside the lemma — from `interpretOp_some_iff`, the matcher's
`getOperands!` fact, and `VariableState.getVar?_conforms` + the operand's integer type
(`RuntimeValue.Conforms.integerType` turns "conforms to `i{bw}`" into "`= .int bw x`") — so
callers don't have to supply it. The binop analogue is `matchBinaryOp_interpretOp_unfold`
(`CommonGraphLemmas.lean`), exposing two existentials via two
`Array.exists_mapM_option_eq_some_iff` reads (indices 0 and 1); it doubles as the
`EquationHolds` unfolder for matched defining binops (Layer 3).

### Forward lemmas for the emitted ops

`CommonForwardInterpret.lean` holds *forward symbolic-execution* lemmas, thin specializations of
the generic `interpretOp_forward` (`Veir/Interpreter/Lemmas.lean`):

- `interpretOp_castToReg_forward` — `unrealized_conversion_cast`, `.int bw x` ↦ `.reg (toReg x)`;
- `interpretOp_castBack_forward` — the reverse cast, `.reg r` ↦ `.int bw (toInt r bw)`;
- `interpretOp_riscv_unaryReg_forward` — **generic over the RISC-V opcode**: any unary
  reg-to-reg op whose `Riscv.interpretOp'` maps `.reg r` to `.reg (f r)` (hypothesis `hSem`,
  discharged by `rfl` at each concrete opcode). Covers `clz`/`clzw`/`ctz`/`ctzw`/`cpop`/`cpopw`
  and any future unary Zbb op with **no new lemma needed**;
- `interpretOp_riscv_binaryReg_forward` — the binary analogue: `.reg r₁, .reg r₂` ↦
  `.reg (f r₁ r₂)`, two operand hypotheses. Covers `andn`/`orn`/`xnor` and any future binary
  reg-reg op (`add`/`sub`/`max`/…) with no new lemma needed. Beware the interpreter's operand
  order: `Riscv.interpretOp'` maps `[op1, op2]` to e.g. `RISCV.andn op2 op1`, so at
  instantiation `f := fun r₁ r₂ => RISCV.andn r₂ r₁`.

Each lemma's conclusion gives the successful one-step interpretation, memory unchanged, the
result binding, and a **frame clause** (all non-result variables unchanged). The frame clause
is what lets facts about earlier values survive to later ops in the chain — see the two-cast
prefix of `lowerBinopNotLocal_preservesSemantics`, where the second cast's frame keeps the
first cast's result binding and the first cast's frame keeps `y`'s value; the membership side
conditions (`y ∉ xCastOp.getResults!`, `xCastOp.getResult 0 ∉ yCastOp.getResults!`) are
discharged by `ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds`
(`CommonBaseLemmas.lean`): a value existing *before* a `createOp` is never a result of the
freshly created op. New emitted-op *shapes* (ops with immediates, `li`) need one new
specialization each — ~20 lines of boilerplate: instantiate `interpretOp_forward` with explicit
`vals := #[…]`, `results := #[…]`, `mem' := state.memory`, and discharge the three obligations
with the same `simp` scripts as the existing ones.

### Peel tactics

`CommonTactics.lean` provides macros that mirror the monadic structure of the pattern in
`hpattern`:

- `peelSplittableCondition` / `peelSplittableCondition'` — split an `if`/`match` guard,
  discharge the impossible branch with `grind`;
- `peelOpCreation` / `peelOpCreation!` — peel one op-creation bind, introducing the updated
  context, the new op, and the creation hypothesis (the `!` form also rewrites `createOp!` to
  plain `createOp` and transports a dominance hypothesis into the new context);
- `peelCastToRegLocal` / `peelReplaceWithRegLocal` — same, specialized to the two cast helpers;
- `cleanupHpattern` — substitute the final `newOps`/`newValues`/`newCtx` equalities.

The matcher itself is peeled inline in the generic proof (case on `match? op ctx.raw`, the
`none` branch contradicts `hpattern`), since the matcher is now a *parameter* rather than a
concrete function.

### Base lemmas

`CommonBaseLemmas.lean` holds the glue: `LocalRewritePattern.exists_refined_int_getVar?`
(read a refined integer operand in the target state), `WfRewriter.createOp!_none_eq`
(reduce `createOp!` at a `none` insertion point to `createOp`), `getProperties!` preservation
lemmas, and the axiom `ValuePtr.dominatesIp_before_WfRewriter_createOp` (dominance is preserved
when creating a detached op — axiomatised because `dominatesIp` is opaque).

## Checklist: proving a new lowering

**If it fits `lowerUnaryWLocal`** (single integer operand, one unary reg-to-reg RISC-V op per
bitwidth): define it as a `lowerUnaryWLocal` instance in `RISCV64.lean`, then in the `Example`
namespace of `LowerUnaryW.lean`:

1. **Layer 0**: `foo_isRefinedBy_toInt_<riscvop>` — one per bitwidth branch.
2. **Layer 1**: check `OperationPtr.Verified.llvm_foo` exists in `Verifier.lean`; add the
   three-liner if missing.
3. **Layer 2**: check `matchFoo_implies` exists in `Matching/Lemmas.lean`; add if missing.
4. Instantiate `lowerUnaryWLocal_preservesSemantics` (the three `hSem*` arguments are `rfl`).
5. **Axiom check**: `#guard_msgs in #print axioms foo_local_preservesSemantics` to pin the
   axiom footprint.

**If it fits `lowerBinopNotLocal`** (two integer operands with a `not` on one side, one binary
reg-to-reg RISC-V op at `i64`): same steps against `lowerBinopNotLocal_preservesSemantics` in
`LowerBinopNot.lean`, with *two* Layer-0 lemmas (one per `not`-operand orientation; mind the
riscv operand order, see the forward-lemma note above).

**If it needs a new shape** (binop, longer chain, extra guards): first factor the lowering
through a new combinator in `RISCV64.lean`, then prove that combinator's
`PreservesSemantics` once, generic over the opcode-specific parameters, following
`lowerUnaryWLocal_preservesSemantics` as the template. Its proof body is a linear script:
peel the matcher and guards, unfold the source interpretation, peel the op creations (one
`peel*` per created op, in program order), read the refined operand(s) with
`exists_refined_int_getVar?`, establish the structural facts about the created ops (`grind`,
seeded with `*_WfRewriter_createOp` transport lemmas where needed), symbolically execute the
emitted chain with the forward lemmas, and assemble the simulation triple. Then instantiate
per lowering as above.

## Adapting to other lowering shapes

- **Binops** (`add_local`, `mul_local`, …): everything needed is now in place — the binop
  unfold lemma, the binary reg-reg forward lemma, and the frame-clause plumbing are all
  demonstrated by `lowerBinopNotLocal_preservesSemantics`, which is the template to follow
  (it is a plain binop proof plus one `matchNot` graph read). A plain binop combinator's proof
  is that proof minus the `matchNot`/orientation parts.
- **DAG-matching patterns** (`selectBinopImmLocal`, `bexti_local`, `orcb_local`, …): each
  matcher applied to a *defining op* needs one Layer-3 lemma
  (`match*_getVar?_of_EquationLemmaAt` style, see `matchNot_getVar?_of_EquationLemmaAt`);
  constants additionally reuse `constantOp_interpretOp_unfold` and
  `OperationPtr.Pure.llvm_mlir__constant` as-is.
- **Longer chains** (`bswap_local` 32-bit emits `cast, rev8, srli, castBack`): one extra
  `peelOpCreation!` and one extra forward-lemma application per op; ops with an immediate
  (`srli`) need their forward lemma to take the properties (`RISCVImmediateProperties`) into
  account when unfolding `Riscv.interpretOp'`.
- **Nested branching** (`bswap_local` branches *after* creating `rev8Op`): the `rcases` on the
  bitwidth happens at the point where `hpattern` branches; peel the shared prefix first, split,
  then peel each branch's suffix.
- **Guards other than bitwidth** (e.g. constant-operand checks in `fshrConst_local`): each
  `if c then return (ctx, none)` / `let some … := … | return (ctx, none)` in the pattern is one
  `peelSplittableCondition` / matcher-style peel; the surviving hypothesis feeds the data lemma.

## Gotchas

- **`RewriteProofs` is not in the lake build graph**: nothing under `Veir/` imports these files,
  so `lake build` alone does not check them. Build them explicitly, e.g.
  `lake build Veir.Passes.InstructionSelection.RewriteProofs.LowerUnaryW`.
- **`interpretOp_forward` needs explicit `vals`/`results`/`mem'`** — unification won't infer
  them from the goal.
- **`clear hpattern` inside dischargers**: the `peel*` macros clear `hpattern` in their
  `by grind`/`by simp` side goals so its proof term isn't captured, which would block later
  peels. Keep this if you write new peel macros.
- **`grind` seeding for transport chains**: facts about ops created two contexts ago
  (`retOp`'s result types viewed in `ctx₃`) need the `*_WfRewriter_createOp` transport lemmas
  passed explicitly to `grind [...]`, instantiated at the right creation hypothesis.
- **Bitwidth literals**: destructure `intType` (`obtain ⟨bw⟩ := intType`) and `subst` the
  branch hypothesis before applying the Layer-0 lemmas, which are stated at literal `64`/`32`.
- **`maxHeartbeats`**: the combinator theorem needs `set_option maxHeartbeats 1000000` (many
  `grind` calls over a large context).
- **Expected axioms**: `#print axioms` will list the dominance axioms
  (`OperationPtr.dominates*`, `ValuePtr.dominatesIp*`,
  `IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates`,
  `ValuePtr.dominatesIp_before_WfRewriter_createOp`; DAG-matching proofs add
  `OperationPtr.strictlyDominates_trans` and
  `ValuePtr.dominatesIp_before_of_strictlyDominates`),
  `OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants`, `floatEqOfToBitsEq`,
  and a `…bv_decide.ax_…` native axiom per `bv_decide`/`veir_bv_decide` use (including
  `MemoryState.llvmLoad._native.bv_decide.ax_8` pulled in by the interpreter) — that's the
  accepted baseline, pin it with `#guard_msgs` (see the end of `LowerBinopNot.lean`).
- **Un-inferable implicits in packaged lemmas**: hypotheses whose only mention of a variable is
  inside a `(by grind)` default argument (e.g. `opInBounds` in
  `matchNot_getVar?_of_EquationLemmaAt`) must be *explicit* — unification cannot recover them
  from proof terms at the call site.
- **`simp` swaps negated `if` branches**: the initial `simp … at hpattern` applies
  `ne_eq`/`ite_not`, so a source-level `if t.bitwidth ≠ 64 then bail else continue` becomes
  `if t.bitwidth = 64 then continue else bail` — split it with
  `split at hpattern; case isFalse hne => simp at hpattern` and `rename_i hBw`, rather than
  assuming the source branch order (this is why `lowerBinopNotLocal_preservesSemantics` does
  not use `peelSplittableCondition` for the bitwidth guard).

## File map

| File | Contents | Growth per new lowering |
|---|---|---|
| `RewriteProofs/LowerUnaryW.lean` | `matchUnaryOp_interpretOp_unfold`, `lowerUnaryWLocal_preservesSemantics`, and per-lowering Layer-0 lemmas + instantiations | two data lemmas + one instantiation (unary); new file per new *shape* |
| `RewriteProofs/LowerBinopNot.lean` | `lowerBinopNotLocal_preservesSemantics` (the DAG-matching template proof), per-lowering Layer-0 lemmas + instantiations (`andn`/`orn`/`xnor`), `#guard_msgs` axiom pins | two data lemmas + one instantiation (binop-with-not) |
| `RewriteProofs/CommonGraphLemmas.lean` | Layer 3: `OperationPtr.Pure.llvm_*`, `matchBinaryOp_interpretOp_unfold`, `constantOp_interpretOp_unfold`, `matchNot_getVar?_of_EquationLemmaAt` | one packaged lemma per new *matcher* used on defining ops |
| `RewriteProofs/CommonForwardInterpret.lean` | forward lemmas (casts + generic unary/binary reg-to-reg riscv ops) | one lemma per new emitted-op *shape* |
| `RewriteProofs/CommonTactics.lean` | `peel*` macros, `cleanupHpattern` | rarely |
| `RewriteProofs/CommonBaseLemmas.lean` | `exists_refined_int_getVar?`, `not_mem_getResults!_of_inBounds_of_not_inBounds`, `createOp!` reduction, properties/dominance transport | rarely |
| `RewriteProofs/CommonMatchLemmas.lean` | ctlz-specific unfold/peel lemmas — currently unused (superseded by the generic `matchUnaryOp_interpretOp_unfold`); candidate for deletion | — |
| `Veir/Passes/InstructionSelection/RISCV64.lean` | the GlobalISel lowering combinators (`lowerUnaryWLocal`) and their instances | one `def` (or a new combinator) |
| `Veir/Passes/InstructionSelection/RISCV64Sdag.lean` | the SelectionDAG lowering combinators (`lowerBinopNotLocal`, `selectBinopImmLocal`, …) and their instances | one `def` (or a new combinator) |
| `Veir/Verifier.lean` | `IsVerified*` bundles + `Verified.llvm_*` extractors (Layer 1; incl. `Verified.llvm_mlir__constant`) | one 3-line lemma (unop/binop) |
| `Veir/Passes/Matching/Lemmas.lean` | `match*_implies` (Layer 2) | usually nothing |
| `Veir/Interpreter/Lemmas.lean` | generic `interpretOp_forward`, `interpretOpList_cons` | nothing |
| `Veir/Interpreter/EquationLemma.lean` | `Pure`, `EquationHolds`, `EquationLemmaAt` (the Layer-3 invariant) | nothing |
| `Veir/Dominance.lean` | dominance axioms (incl. `strictlyDominates_trans`, `dominatesIp_before_of_strictlyDominates`) | nothing |
| `Veir/PatternRewriter/Semantics.lean` | `PreservesSemantics` | nothing |
