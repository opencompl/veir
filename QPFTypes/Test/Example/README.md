# Guarded corecursion examples

These examples live on **`main`**, using its existing `QPF.Cofix`, `@[qpf]`,
constructors, and one-layer destructors. They do not import or implement the
`qpf/wip` branch's `codef` machinery.

New corecursive functions are **`unsafe def` specifications**: Lean elaborates and
typechecks their bodies without requiring termination. This neither proves
productivity nor provides lazy evaluation, and these definitions must not be used
as logical axioms or tested with `#eval`. The existing safe `CoList.map` and its
proofs are left intact. Type/constructor/destructor definitions remain safe.

## Types and motivating uses

| File | Shape (greatest fixed point in `X`) | Use |
| --- | --- | --- |
| [`Stream.lean`](Stream.lean) | `α × X` | Infinite sequences, generators, stream transducers |
| [`CoList.lean`](CoList.lean) | `Unit ⊕ (α × X)` | Possibly-finite lazy lists |
| [`Delay.lean`](Delay.lean) | `α ⊕ X` | Partial computations, potentially nonterminating search |
| [`Tree.lean`](Tree.lean) | `Unit ⊕ (α × X × X)` | Possibly-infinite binary trees |
| [`RoseTree.lean`](RoseTree.lean) | `α × (Σ n, Fin n → X)` | Finitely branching transition/search trees |
| [`CoTree.lean`](CoTree.lean) | `α × CoList X` | Game trees with coinductive child lists; potentially infinite breadth and depth |
| [`Language.lean`](Language.lean) | `Bool × (α → X)` | Languages as tries / unfolded deterministic automata |
| [`ITree.lean`](ITree.lean) | `R ⊕ X ⊕ (Σ e, E e → X)` | Effectful, potentially nonterminating computations |

`Delay Unit` has the conatural-number shape, so a separate conatural API would
largely repeat these patterns. `RoseTree` children use finite vectors rather than
`List`, avoiding new library instances while retaining variable finite arity.
In contrast, `CoTree` nests a greatest fixed point through another greatest fixed
point, `CoList`: its children are coinductive data, not a function-valued family.
`CoList` exposes its inherited polynomial instance so it can be reused this way.
ITree's event-tag / answer-family encoding keeps dependent branching small, as in
the pre-existing example. These are ordinary, unindexed data types in `Type`;
Rocq's indexed coinductive predicates in `Prop` and mutually defined type families
are not modeled here. Mutual *functions* are included.

## What the guarded fragment needs to handle

All the positive bodies have counterparts accepted by **Rocq 9.1.1** in
[`GuardedCorecursion.v`](GuardedCorecursion.v). This is a coverage catalogue, not
a proposal to translate Lean to Rocq or to adopt Rocq's conversion/equality rules.

### Direct guarded corecursion

| Pattern | Examples | What matters |
| --- | --- | --- |
| Generate from arbitrary state | `Stream.iterate` | Recursive arguments need not decrease; `step a` is fine. |
| Observe inputs before constructing output | `Stream.interleave`, existing `CoList.map` | Input destructors/matches are allowed; `interleave` also swaps arguments. |
| Emit several constructors per call | `Stream.stutter` | There need not be exactly one guard. |
| Branch *beneath* an existing guard | `Stream.sample` | A match/conditional preserves the surrounding guard; branches need not add another. |
| Nonrecursive branches graft existing values | `CoList.append`, `ITree.bind`'s return branch | Guards constrain recursive occurrences, not every return path. |
| Explicit computational delay | `Delay.search` | An unsuccessful search emits `later`; it need not ever emit `now`. |
| Several recursive positions | `Tree.mirror` | Both children may contain independent recursive calls. |
| Function-valued recursive positions | `Language.union`, `ITree.bind`'s visible branch | Calls under lambdas are allowed, including an event-dependent domain `E e`. |

### Rocq-supported edges beyond a literal constructor check

| Pattern | Examples | What matters |
| --- | --- | --- |
| Reduction exposes a guard | `Stream.iterate` | A `let` binds the recursive result *before* the constructor, and transparent `id` wraps it. Rocq checks after reduction, not by counting surface constructor tokens. |
| Mutual corecursion, including nullary definitions | `Stream.truesFalses` / `falsesTrues` | Each reference to either member must be guarded; merely having a guard somewhere on a mutual cycle is not the criterion. |
| Nested strictly positive containers | `RoseTree.unfold` | A constructor guards calls through `Sigma.mk` and a lambda. The number of children and function domain depend on input state. |
| Nested coinductive containers | `CoTree.map`, `CoTree.unfold` through `CoList.mapCorec` | The outer cofixpoint builds trees; the inner one builds their possibly-infinite child lists, capturing the outer recursive reference. |
| Nested cofixpoints capturing outer calls | `ITree.iter` through `ITree.bind` | Unfolding the helper exposes a local cofixpoint whose body captures a `tau`-guarded outer call. See below. |

`ITree.iter` is a particularly useful boundary for a staged implementation. In
`bind`, the continuation `k` is captured **outside** the local `go` cofixpoint.
Moving it to an explicit recursive parameter preserves the apparent equations of
`bind`, but Rocq then rejects the same `iter`: the outer recursive occurrence is
in an argument to the inner cofixpoint. Thus “any call to bind is guarded” is not
a valid rule. The local-recursion arrangement is intentional, following the
Interaction Trees library, not just a Lean coding style choice. This case can be
kept separate from an initial direct-constructor implementation, but is part of
the Rocq baseline.

`CoTree` adds nested **coinductive data**, not just nested recursive functions:
its children have type `CoList (CoTree α)`. Following Korkut's game-tree library,
`CoList.mapCorec` captures its mapping function outside the local recursion.
Unfolding that helper in `CoTree.map` or `CoTree.unfold` exposes a list cofixpoint
whose head constructs a child tree and whose tail continues the child list.
Recursive positions must be tracked through the nesting: a list's element field
is a recursive *tree* position here. Moving the mapping function into an explicit
recursive parameter makes both outer definitions fail Rocq's guard check. The
existing safe `CoList.map` is left unchanged; `mapCorec` is a separate unsafe
specification of the required nested-cofixpoint arrangement.

## Boundaries: productivity alone is not Rocq guardedness

The same `.v` file contains `Fail CoFixpoint` checks. Each was also checked without
`Fail` to confirm it fails for **guardedness**, not a name/type error.

- `Streams.filter`: the rejected-element branch has no guard and could search
  forever. An eventual-match proof/terminating search would be a different design;
  `Delay.search` instead makes the delay observable.
- `Streams.canceled`: `tail (cons 0 canceled)` cancels its purported guard.
- `Streams.natsMapped`: `cons 0 (map S natsMapped)` is productive, but `map` is not
  a constructor. Arbitrary productive/causal helpers are not automatically allowed.
- `Streams.nested`: an outer constructor does not allow `f (f input)`.
- `Streams.scrutinized`: an outer constructor does not allow matching on a
  recursive result. Input observation and recursive-result observation differ.
- `Streams.wrongField`: a recursive occurrence in `head wrongField` is in a
  **nonrecursive** constructor field. A constructor anywhere above a call is not
  enough; it must be the appropriate recursive position.
- `RoseTrees.copy`: `List.map copy children` over an unknown list is rejected.
  In contrast, the auxiliary `binaryRose` with literal `[binaryRose; binaryRose]`
  is accepted: nested inductive **constructors** are not arbitrary traversals.
- `CoTrees.mapAll` and `unfoldAll`: even with **coinductive** child lists, passing
  the outer recursive function as an argument to the inner cofixpoint is rejected.
  The accepted `mapCorec` helper instead captures it in the inner body.
- `Languages.concat`: the usual productive derivative equation places a call
  underneath `union` and is not directly guarded. Do not assume that all the
  operations supported by Isabelle in the cited trie literature are Rocq-guarded.
- `ITrees.iterAll` and `iterNoTau`: respectively, passing rather than capturing
  the recursive continuation, and omitting the required outer `tau` guard.

None of these rejected definitions is offered as a positive Lean example.
Likewise, recursive occurrences in types, match motives, or constructor parameters
are not licensed by the accepted lambda/match/container examples. Rocq's kernel
checker is the precise reference for these restrictions, not the informal slogan
“at least one constructor per iteration”.

## Sources

- **Rocq reference manual**, [Coinductive types and corecursive functions](https://rocq-prover.org/doc/V9.1.0/refman/language/core/coinductive.html):
  streams, mutual `CoFixpoint`, guardedness, rejected filtering, and lazy unfolding.
  For the detailed treatment of recursive positions, lambdas, cases, nested
  cofixpoints, and reduction, see [`check_one_cofix` in the 9.1.1 kernel](https://github.com/rocq-prover/rocq/blob/V9.1.1/kernel/inductive.ml#L1703-L1787).
- **Adam Chlipala**, [*Certified Programming with Dependent Types*, “Coinduction”](https://adam.chlipala.net/cpdt/html/Coinductive.html):
  alternating mutual streams, `interleave`, and why destructors/arbitrary helpers
  around calls differ from constructors and transparent identity functions.
  Rocq's [standard `Streams` library](https://github.com/rocq-prover/stdlib/blob/master/theories/Streams/Streams.v)
  also supplies `map`, `const`, and `zipWith`; we avoid duplicating all their shapes.
- **Yves Bertot**, [*CoInduction in Coq*](https://inria.hal.science/inria-00001174),
  §§1–3: lazy lists, streams, binary trees, and guarded constructions. The rose
  tree is a variable-arity extension of the branching-tree pattern.
- **Joomy Korkut**, [*A Rose Tree Is Blooming (Proof Pearl)*](https://joomy.korkutblech.com/papers/game-trees-cpp26.pdf),
  CPP 2026, §3, and Bloomberg's [`theories/Cotrees.v`](https://github.com/bloomberg/game-trees/blob/69b610f3ee77775e742f7dbf3acbb8e2e6aec96a/theories/Cotrees.v):
  `cotree` with `colist` children, `comap`, `comap_cotree`, and `unfold_cotree`.
  These provide the nested-coinductive examples and the captured-function helper.
- **Venanzio Capretta**, [*General Recursion via Coinductive Types*](https://arxiv.org/abs/cs/0505037),
  LMCS 2005, §3: the unquotiented type of partial elements (`return` / `step`).
- **Dmitriy Traytel**, [*Formal Languages, Formally and Coinductively*](https://arxiv.org/abs/1611.09633),
  §§2–3: language tries, pointwise union, and the more challenging concatenation
  equation. This is an Isabelle source of examples, not authority on Rocq acceptance.
- **Interaction Trees library**, [`ITreeDefinition.v`](https://github.com/DeepSpec/InteractionTrees/blob/284d42248a3c5517cff9f582e335fcee2f6bdc1f/theories/Core/ITreeDefinition.v):
  `ITree.subst`, `bind`, and `iter`, particularly the comment explaining why the
  continuation is outside the cofixpoint and why iteration inserts `Tau`.

## Rechecking

From the repository root, Lean's normal test target imports every example:

```sh
(cd QPFTypes && lake build Test)
```

The Rocq file is a standalone reference check, not a new dependency of the Lean
build. For the versions used here (Rocq 9.1.1 / Stdlib 9.0.0), with Nix:

```sh
pkgs=github:NixOS/nixpkgs/4fe25e12eb9f4c744966dd3de5a05246cf098601
stdlib=$(nix build --no-link --print-out-paths "$pkgs#rocqPackages.stdlib")
tmp=$(mktemp -d)
cp QPFTypes/Test/Example/GuardedCorecursion.v "$tmp/"
nix shell "$pkgs#rocq-core" -c rocq compile \
  -Q "$stdlib/lib/coq/9.1/user-contrib/Stdlib" Stdlib \
  "$tmp/GuardedCorecursion.v"
```

Compilation succeeds only if the positive definitions pass and every `Fail`
command is rejected. Stdlib's advisory warning about `Fin.t` is expected. Keeping
Rocq's generated artifacts in the temporary directory avoids dirtying the tree.
