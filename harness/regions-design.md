# Phase F: Regions + symbol-table semantics — design note

**Status**: F.1 (design only). No implementation code attached.

**Required by `harness/quality-gates.md` §9** before any Phase F
implementation work begins.

**Replaces**: the original Phase B framing in
`harness/symbol-table-spike.md` (deferred 2026-05-15; folded into
Phase F). The "Hybrid" recommendation from that doc carries forward
as the symbol-table half of this design.

---

## 1. Scope

Phase F lands two coupled architectural additions:

1. **Region semantics** — operations may own regions; regions contain
   blocks; blocks own operations and arguments and end in terminators.
2. **Symbol-table semantics** — some operations carry a `Symbol` name;
   other operations refer to symbols via `SymbolRefAttr`; scoping is
   determined by the region tree.

**Big surprise from the F.1 research survey**: VEIR already has
*structural* region support — `Operation.regions : Array RegionPtr`,
`Region`, `Block`, and the FieldsInBounds + WellFormed proofs for
all three exist today (`Veir/IR/Basic.lean:167,278,304`,
`Veir/IR/Fields.lean`, `Veir/Rewriter/WellFormed/{Region,OpRegion,Block,BlockArguments,BlockOperands}.lean`).
What's missing is **semantic invariants on top of that structure**
plus **dialect operations that use the structure**. The design
question is therefore much narrower than originally framed:

- *Not*: "should we add regions to the verified IR?" (already there)
- *But*: "what additional invariants and machinery make regions
  *useful* for Function/Polymorphic/Struct, and which of those go
  in `WellFormed` vs at verify-time vs unverified?"

### Not in scope for Phase F

- `AffineScope` and `AutomaticAllocationScope` traits — defer.
- `replaceAllSymbolUses` — rewrite-tier concern; defer.
- Multi-module symbol resolution (cross-`include.from`) — defer.
- Polymorphic templates' type-parameter scoping (LLZK's
  `LLZKSymbolTable` custom trait specifics) — Phase G.2.
- Full structural verification of `IsolatedFromAbove` — done at
  verify-time, not as a `WellFormed` invariant.

---

## 2. Why now

| Blocked artifact | What Phase F provides |
|---|---|
| Tier 3 dialects: Function, Polymorphic, Struct | Region-using ops + terminator invariants + symbol-table machinery |
| 5 of 8 differential tests (Bool, Cast, Constrain, RAM, Global) | `function.def` wrapper for non-module-level ops |
| Verified-pass pilots 5–9 (LLZK transforms) | Symbol-resolved IR traversal + region-aware rewrites |
| Nested `SymbolRefAttr` (`@A::@B`) | Symbol-table scoping |
| `SymbolUserOpInterface` semantics | Resolution machinery |

The differential testing harness made the absence of Phase F
*observable*: today, 5 tests sit at `// XFAIL: llzk-opt` with the
same root cause ("LLZK rejects this op outside a `function.def`
wrapper"). Phase F is the bottleneck.

---

## 3. Current state of VEIR's verified IR — what already exists

Empirical findings from the F.1 research survey
(`tasks/a862be48f77f98bb9.output`). **This is much further along
than I assumed when writing this design's outline.**

### 3.1 The `Operation` structure already carries regions

`Veir/IR/Basic.lean:167`:

```lean
structure Operation (OpInfo : Type) [HasOpInfo OpInfo] where
  results : Array OpResult
  prev : Option OperationPtr            -- doubly-linked op list
  next : Option OperationPtr
  parent : Option BlockPtr              -- ← owning block
  opType : OpInfo
  attrs : DictionaryAttr
  properties : HasOpInfo.propertiesOf opType
  blockOperands : Array BlockOperand    -- successor blocks (Cf-style)
  regions : Array RegionPtr             -- ← already there
  operands : Array OpOperand
```

### 3.2 The `Region` and `Block` structures exist

```lean
structure Region where
  firstBlock : Option BlockPtr
  lastBlock : Option BlockPtr
  parent : Option OperationPtr

structure Block where
  firstUse : Option BlockOperandPtr
  prev : Option BlockPtr
  next : Option BlockPtr
  parent : Option RegionPtr
  firstOp : Option OperationPtr           -- doubly-linked op list within block
  lastOp : Option OperationPtr
  arguments : Array BlockArgument
```

### 3.3 `IRContext` is tri-keyed

```lean
structure IRContext (OpInfo : Type) where
  operations : HashMap OperationPtr (Operation OpInfo)
  blocks : HashMap BlockPtr Block
  regions : HashMap RegionPtr Region
  nextID : Nat
```

(HashMap, not flat arrays — sparse representation.)

### 3.4 What's already verified

`Veir/IR/WellFormed.lean` (1,366 lines) + `Veir/Rewriter/WellFormed/*`
(8 files, 1,335 lines). Pointer-validity + structural invariants
are proved for regions and blocks:

- **`FieldsInBounds`** (`Veir/IR/Fields.lean`, 873 lines): every
  pointer reference in any structure is in-bounds, including
  `Operation.regions`, `Region.firstBlock/lastBlock/parent`,
  `Block.firstOp/lastOp/parent`. Preservation theorems exist for
  all setters.
- **WellFormed**:
  - `OperationPtr.WellFormed`: regions are unique within an op
    (`regions_unique`); `region_parent` bijection (every region in
    an op's `regions` array has its `parent` set to that op, and
    vice versa).
  - `RegionPtr.WellFormed`: parent operation exists and contains
    this region.
  - `BlockPtr.WellFormed`: parent region, arg indices, owners.
  - `IRContext.WellFormed`: `blockChain` (every region has an
    ordered chain of blocks via prev/next).
- **Existing rewriter primitives** (`Veir/Rewriter/Basic.lean`):
  `Rewriter.initOpRegions` (create N empty regions for an op),
  `Rewriter.pushRegion` (append a region). Both have WellFormed
  preservation proofs (`Veir/Rewriter/WellFormed/{Region,OpRegion}.lean`).

### 3.5 What's NOT yet there

- **Block-as-SSA-value**: `BlockArgument` is a separate value type,
  not a variant of `ValuePtr`. The `valueDefUseChains` invariant
  doesn't track block-argument producers. Operations cannot consume
  block-argument values today through the normal operand path.
- **Terminator invariants**: no WellFormed predicate "every block
  ends in a terminator op". Verify-time check doesn't exist either.
- **Region-aware rewriter primitives** beyond `initOpRegions` /
  `pushRegion`: no `createBlock`, `insertBlock`, `eraseBlock`,
  `moveBlock`, `moveRegion` with WellFormed preservation.
- **Symbol tables**: zero infrastructure. `FlatSymbolRefAttr` is
  textual only. No name-to-pointer resolution, no scope enforcement,
  no `SymbolTable` data structure.
- **Cf dialect still uses `blockOperands`, not regions**: `cf.br`
  and `cf.cond_br` reference successor *operations* (via
  `BlockOperand`), not blocks within a region. This is a successor
  model; not a CFG-with-regions model. Either coexists with the
  new region machinery (Cf stays as-is, new region ops use the new
  path), or migrates (more work, more invariants).

### 3.6 Implication for design

The "should we add structural regions to VEIR's verified IR?"
question is **settled**. The remaining questions are scoped to:

1. Block-arguments-as-SSA-values: needed for `function.def`'s entry
   block to accept function arguments as SSA values consumed by ops
   inside the body. Today's `BlockArgument` is a separate type
   parallel to `OpResult`; making it a `ValuePtr` variant is a
   focused extension.
2. Terminator invariants: verified or verify-time?
3. Symbol-table machinery: new file `Veir/IR/SymbolTable.lean`,
   verified or unverified resolver?
4. Cf migration: out of scope or in scope?
5. Region-aware rewriter primitives: how many, with what proofs?

---

## 4. What regions mean (MLIR reference)

(For readers without MLIR background.) A **region** is an ordered
list of **blocks**; a **block** has typed **arguments**, an ordered
list of **operations**, and ends in a **terminator** op.

Traits constraining regions:

- **`IsolatedFromAbove`**: SSA values defined outside the op cannot
  be used inside its regions; symbol references are the only
  cross-boundary mechanism.
- **`SingleBlock`** / **`NoTerminator`** / **`GraphRegionNoTerminator`**:
  relaxations.

Region kinds:

1. **SSACFG region**: blocks form a CFG; ops execute per branches.
2. **Graph region**: blocks are unordered; declarative IR. LLZK
   uses this for `struct.def`.

---

## 5. What symbol tables mean (MLIR reference + LLZK extension)

A `Symbol`-trait op declares a name (`sym_name : StringAttr`, see
`harness/porting-notes.md` Gotcha 5). A `SymbolTable`-trait op
contains a region whose top-level Symbol-trait ops are looked up by
name.

- **`FlatSymbolRefAttr`** (`@name`): already in VEIR.
- **Nested `SymbolRefAttr`** (`@outer::@inner`): not yet; path
  parsing + resolution needed.
- **LLZK's `LLZKSymbolTable`**: custom trait on `struct.def` and
  `poly.template`; same lookup semantics with extra visibility
  rules. Phase G concern; Phase F provides the base.

---

## 6. Design alternatives, narrowed

Given §3's finding that structural regions already exist, the
"three extremes" framing from `harness/symbol-table-spike.md`
collapses. The question is no longer whether to add regions to
`Veir/IR/` (done) but **how much semantic verification to bolt on
top**.

### A. Minimal: structural only

Build on what's there. Add `BlockArgument` as a `ValuePtr` variant
(so ops inside the body of `function.def` can consume function args
as SSA values). Add a handful of rewriter primitives for block
manipulation. **Don't** add terminator invariants, **don't** add
symbol tables, **don't** touch Cf. Ship Function dialect on top.

**Pros**: smallest possible Phase F. Maybe 2-3 weeks.

**Cons**: Function-without-terminator-check leaves verifier-time
holes (an `function.def` with no `function.return` would pass VEIR
but fail in LLZK). Symbol resolution still pass-level. The 5 XFAIL
differentials lift (because `function.def` wraps their ops), but no
verification beyond what's there today.

### B. Balanced: structural + verify-time semantic

Alternative A's surface, plus:
- Verify-time terminator presence check
  (`OperationPtr.verifyLocalInvariants` extension).
- Verify-time `IsolatedFromAbove` SSA-closure check.
- Unverified `IRContext.resolveSymbol` walker in
  `Veir/IR/SymbolTable.lean` (the Hybrid recommendation from
  `symbol-table-spike.md`).

**Pros**: matches existing VEIR practice (verify-time checks for
op shape; unverified walkers for things that aren't yet provable).
LLZK-grade well-formedness, just not all encoded in `WellFormed`.

**Cons**: Two-tier reasoning (structural vs semantic). Passes that
depend on terminator presence or symbol integrity carry an explicit
hypothesis (or rely on the verifier pre-pass).

### C. Aggressive: extend `WellFormed` to semantic invariants

Alternative B's surface, plus promote terminator presence and
symbol integrity into `WellFormed`. Cf migrates to region-based
successors.

**Pros**: Verified passes can take terminator presence and symbol
integrity as guaranteed. Cleanest end state.

**Cons**: Largest surface change. ~3-5K LoC of new proof debt for
the WellFormed extension. Cf migration is its own project. Likely
extends Phase F by weeks.

---

## 7. Recommendation

**Choose B (Balanced).** It threads the "existing VEIR pattern"
needle, ships the unblocking value (Function dialect, 5 XFAIL diffs
lift), and leaves clean upgrade paths to C.

Why specifically B over A or C:

- **vs. A**: A leaves real holes in semantic verification. The
  Function port specifically needs a `function.def` body with a
  terminator — if VEIR accepts a body without one, every Function
  consumer downstream has to re-check. Adding the verify-time check
  is cheap (~50-100 LoC) and we get the value.
- **vs. C**: C's WellFormed extension is large and not on the
  critical path for Phase G. Verified-pass pilots 5–9 don't all
  need terminator-as-WellFormed; the ones that do can prove a
  local hypothesis or wait for the upgrade.

### Migration path to C

For each invariant that's verify-time in B but could be `WellFormed`:

1. **Terminator presence**: add `Block.terminator : OperationPtr`
   as a required field (today the terminator is implicitly the
   `lastOp`; we'd assert "lastOp is a terminator" structurally).
   Upgrade when a verified pass needs it.
2. **Symbol integrity**: add `IRContext.SymbolsResolve : Prop`
   predicate (parallels `Veir/Dominance.lean`'s `IRContext.Dom`
   axiom). Upgrade when a verified pass needs it.
3. **`IsolatedFromAbove`**: verify-time only; upgrade only if a
   pilot directly depends on the closure property.

These three upgrades are independent and incremental.

---

## 8. Phased implementation (F.2 – F.5)

Concrete sub-phases, in dependency order. Each ends with `lake build`
clean + the `Veir/Rewriter/WellFormed/` proofs re-verified.

### F.2 — Block arguments as SSA values + rewriter primitives

- [ ] **F.2.1** Extend `ValuePtr` with a `.blockArg` variant
      (`BlockArgPtr := { block : BlockPtr, index : Nat }`). Update
      `Attribute.lean`, related pointer types.
- [ ] **F.2.2** Extend `valueDefUseChains` invariant in
      `Veir/IR/WellFormed.lean` to track block-argument producers
      and uses. *This is the most substantive proof work in F.*
- [ ] **F.2.3** Rewriter primitives in `Veir/Rewriter/`:
      `createBlock`, `insertBlock`, `eraseBlock`, `moveBlock`,
      `moveRegion`. Each with a `Veir/Rewriter/WellFormed/`
      preservation theorem. Leverage the existing
      `Veir/Rewriter/WellFormed/{Region,OpRegion,Block,BlockArguments}.lean`
      pattern.

### F.3 — Verify-time terminator + IsolatedFromAbove

- [ ] **F.3.1** Extend `OperationPtr.verifyLocalInvariants` with
      "for each region this op owns, each block's lastOp is a
      terminator". Add `isTerminator : Bool` to per-dialect
      `OpInfo` instances. Existing dialects: terminators are
      `cf.br`, `cf.cond_br`, `func.return`, `llvm.return`,
      `llvm.br`, `llvm.cond_br`. LLZK adds `function.return`.
- [ ] **F.3.2** Extend verify with `IsolatedFromAbove` check: for
      any op with the trait, walk its regions and verify no SSA
      value reference crosses out of the op's region boundary.
- [ ] **F.3.3** `harness/coverage.md` §Regions rows updated:
      "Terminator op validation" ❌ → ⚠️ (verify-time only),
      `IsolatedFromAbove` ❌ → ⚠️.

### F.4 — Symbol-table machinery (unverified)

- [ ] **F.4.1** Add `SymbolRefAttr` to `Veir/IR/Attribute.lean` as
      a `List ByteArray` (the dotted path). Distinct case from
      `FlatSymbolRefAttr` (kept for the simple case;
      `FlatSymbolRefAttr` can be implemented as a singleton
      `SymbolRefAttr` later if desired).
- [ ] **F.4.2** Parser `parseOptionalSymbolRefAttr` handles
      `@outer::@inner::@deep`. Extends
      `parseOptionalFlatSymbolRefAttr`.
- [ ] **F.4.3** `Veir/IR/SymbolTable.lean` (new): unverified
      walker:
      ```lean
      def IRContext.resolveSymbol
          (ctx : IRContext OpInfo)
          (fromOp : OperationPtr)
          (ref : SymbolRefAttr) :
          Option OperationPtr
      ```
      Walks up the region tree from `fromOp` to find enclosing
      ops with the `SymbolTable` trait, then looks up each
      path segment.
- [ ] **F.4.4** `coverage.md` §Symbols rows updated.

### F.5 — Prototype: `function.def` port

- [ ] **F.5.1** Port `Function` dialect. `function.def`: 0 operands,
      0 results, 1 region. `function.return`: any number of
      operands, 0 results, terminator (per-op `isTerminator := true`).
      `function.call`: takes a `FlatSymbolRefAttr` `callee` + the
      argument operands.
- [ ] **F.5.2** Per the established checklist: identity + invalid
      lit tests at `Test/LLZK/Function/`. Differential test at
      `Test/LLZK/Function/differential/`.
- [ ] **F.5.3** Rewrite the 5 currently-XFAIL differential tests
      (Bool/Cast/Constrain/RAM/Global write) to use a
      `function.def` wrapper with the appropriate
      `function.allow_*` attribute. Flip `// XFAIL: llzk-opt`
      to `// REQUIRES: llzk-opt`.

### Acceptance for F.1 (this doc)

- ✅ Empirical state of regions in VEIR established (§3).
- ✅ Design alternatives narrowed by §3's findings (§6).
- ✅ Recommendation made with rationale (§7).
- ✅ Migration path to fully-verified for each unverified-today
  invariant (§7).
- ✅ Phased implementation broken into F.2-F.5 with checkboxes (§8).
- ✅ Estimated proof debt (next section).
- ✅ Open questions explicit (§11).

---

## 9. Estimated proof debt (revised down based on §3)

Original estimate before the survey: 3-5K LoC of new proof debt for
WellFormed extension. **Now revised significantly down** because the
structural region/block invariants are already proved.

**B (recommended) — Proof debt**:

| Surface | Existing LoC | Phase F addition |
|---|---|---|
| `Veir/IR/Region.lean` (new file with `BlockArgument` integration into `ValuePtr`) | 0 | ~200–400 |
| `Veir/IR/WellFormed.lean` extension for `valueDefUseChains` w/ block args | 1,366 | ~300–500 |
| `Veir/Rewriter/` new block-level primitives | 883 | ~600–1,000 |
| `Veir/Rewriter/WellFormed/` proofs for new primitives | 1,335 | ~500–1,000 |
| `Veir/IR/SymbolTable.lean` (unverified walker) | 0 | ~200–400 |
| `OperationPtr.verifyLocalInvariants` extension (terminator + IsolatedFromAbove) | varies | ~100–200 |

**Total**: ~1,900–3,500 LoC of new code, of which ~1,400–2,500 is
proof code, the rest declarations + helpers. Substantial but not
overwhelming; uses established VEIR patterns (FieldsInBounds is
1.2-1.3× generalizable, per the agent survey).

**Time**: 2-4 weeks if F is the focus. Less if there's pre-existing
context from the F.1 survey.

**C (aggressive) — Additional proof debt**:

| Upgrade | Addition |
|---|---|
| Terminator presence as `WellFormed` | +500 LoC |
| Symbol integrity as `WellFormed` | +800–1,200 LoC |
| `IsolatedFromAbove` as `WellFormed` | +1,000–1,500 LoC |

Each is an independent project; can be slotted in as needed.

---

## 10. Migration plan for existing dialects

**Zero churn on currently-ported dialects.** Every existing op has
`regions := #[]` by default; the new invariants are trivially true
for empty region arrays. Confirmed by §3.4: `regions_unique` and
`region_parent` invariants exist *today* and hold for all current
dialects.

The only existing dialect that *uses* region-shaped concepts is Cf,
and Cf uses the `blockOperands` path, not regions. Cf is **not
migrated** in this design — it stays on the successor model. A
future Cf-to-regions migration is its own project (the migration
note in §11 below).

---

## 11. Open questions

### Blocking before F.2

1. **`BlockArgument` integration into `ValuePtr`**.
   Should `ValuePtr` extend from `.opResult OpResultPtr` and
   `.blockArg BlockArgPtr`? This requires extending every existing
   `ValuePtr`-consuming function — operand iteration, def-use
   walks, type queries. *Tentative answer*: yes; the change is
   focused and the alternative (block args as a parallel value
   type) prevents ops inside a region from consuming function
   arguments as ordinary operands, which is a hard requirement
   for `function.def`.
2. **`valueDefUseChains` extension**: the `firstUse`/`nextUse`
   chain pattern needs to extend to block-arg producers. The
   existing `BlockOperands.lean` use-chain infrastructure should
   generalize, but needs concrete proof sketch. *Tentative
   answer*: extension; the existing `firstUse`/`back` pointer
   pattern in `BlockOperand` is the same shape needed for block
   args.

### Deferrable to F.3 (verify-time semantics)

3. **Terminator op classification**: per-OpCode `isTerminator : Bool`
   on `HasDialectOpInfo`? Or a global registry? *Tentative answer*:
   per-OpCode on the dialect's OpInfo instance — matches the
   per-dialect-properties pattern.
4. **`IsolatedFromAbove` enforcement scope**: just check operand
   reachability, or also block-arg references? *Tentative answer*:
   both; block args defined outside should also be inaccessible.

### Deferrable to F.4 (symbol-table)

5. **Path representation for `SymbolRefAttr`**: `List ByteArray` or
   single `ByteArray` with delimiter? *Tentative*: `List ByteArray`,
   ergonomic for resolution code.
6. **Resolution context**: `resolveSymbol` takes an `OperationPtr`
   and walks up. Does it need a `BlockPtr` overload? *Tentative*:
   no, the `OperationPtr` version suffices; pass the block's
   parent op.

### Deferrable to F.5 (Function port)

7. **`function.allow_witness` / `allow_constraint` /
   `allow_non_native_field_ops`** encoding: as `Function`
   property struct or as `UnitAttr`-presence flags in the
   attribute dict? *Tentative*: properties struct (mirrors LLZK
   ODS, more typed).
8. **`function.call` resolution**: F.4 ships an unverified
   `resolveSymbol`; does `function.call` use it at verify-time to
   check the callee exists? *Tentative*: yes, in
   `OperationPtr.verifyLocalInvariants` for `.function .call` —
   call `ctx.resolveSymbol callee` and error if `none`.

### Future (out of Phase F)

9. **Cf migration to regions**: today's `cf.br ^bb1(%x)` uses
   `blockOperands`; the region model would use a terminator op
   that points at a `BlockPtr` and carries the operand list. The
   existing `blockOperands` infrastructure could be reused (rename
   to "terminator successor"), or both paths could coexist. Out
   of Phase F; flag as a follow-up project.
10. **`replaceAllSymbolUses`**: when an op with a symbol is
    renamed, update every `SymbolRefAttr` that resolves to it.
    Out of Phase F.
11. **Multi-module resolution** via `include.from`: cross-file
    symbol lookup. Out of Phase F.

---

## 12. References

- `harness/symbol-table-spike.md` — deferred Phase B framing; the
  Hybrid recommendation is the symbol-table half of this design.
- `harness/coverage.md` §Regions and §Symbols — what's gated.
- `plan.md` §Phase F — phased implementation tracking.
- `harness/quality-gates.md` §9 — what F.1 must answer.
- `SESSION_RETRO_2026-05-17.md` — original 3-6 weeks Phase F
  estimate (revised down to 2-4 weeks for B based on §3).
- MLIR upstream `mlir/lib/IR/SymbolTable.cpp` — reference
  semantics for SymbolTable lookup.
- `llzk-lib/include/llzk/Dialect/Function/IR/Ops.td` — F.5 port
  target.
- Agent survey transcript:
  `tasks/a862be48f77f98bb9.output` (background research
  task that surfaced §3's findings).

---

## 13. What this doc enables

Concretely:

- **Phase G.1 (Function dialect port)** can begin as soon as F.2–F.5
  land. The design above provides everything Function needs
  (region, terminator, symbol-callable, allow-* attributes).
- **The 5 XFAIL differential tests** all lift simultaneously once
  F.5 ships.
- **Verified-pass pilots 5–6 (EnforceNoOverwrite, UnusedDeclElim)**
  become tractable once F.4 ships — both need symbol-reference
  traversal.
- **Phase G.2 (Polymorphic)** and **G.3 (Struct)** depend on Phase
  F + nested `SymbolRefAttr` (F.4 provides) + the
  `LLZKSymbolTable` custom trait (G-level concern).

Two project pieces gated outside Phase F:

- **`Veir/Dominance.lean`** axiomatization replacement — needed
  for verified-pass pilot 7 (CSE). Independent project.
- **Interpreter equivalence framework** — needed for any
  `interpret ; pass = interpret` proofs. Independent project.

---

## Appendix: revised estimate vs original

The original `plan.md` §Phase F estimate was "≈3–6 weeks". The F.1
survey reduced this:

- **B (recommended)**: 2-4 weeks. Lower because structural region
  invariants are already proved (§3.4); only block-args-as-SSA-values
  + rewriter primitives + verify-time semantics + unverified symbol
  walker remain.
- **C (aggressive)**: 4-8 weeks. Includes upgrading terminator
  presence and symbol integrity to `WellFormed` invariants.

Phase F is no longer the dominant bottleneck for verified LLZK
passes — Phase H (the pilots themselves) and the
`Veir/Dominance.lean` axiomatization replacement (gating pilot 7
specifically) are likely comparable or larger projects.
