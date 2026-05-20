# LLZK ↔ VEIR coverage and gap review

**This document is mandatory reading for anyone consuming this VEIR fork
as an LLZK implementation.** It tracks every LLZK feature with its
current support status in VEIR, the caveat that applies if support is
partial, and the workaround in use.

Updated on every dialect port, every infrastructure addition, and
whenever a new gap is encountered during porting. See `plan.md` §Living
document for the protocol.

**Legend**

- ✅ **Supported** — round-trips and is typed as a first-class VEIR `Attribute`/`OpCode`/structure
- ⚠️ **Partial** — works for a defined subset; caveat below; downstream consumers must be aware
- 🟡 **Round-trip only** — survives parser→printer textually via `UnregisteredAttr` or similar fallback, but is not typed; programmatic pattern-matching does NOT see the feature
- ❌ **Unsupported** — no parser, no representation
- 🚧 **In progress** — has an open work item

---

## §Dialects

| LLZK dialect | Status | Caveats |
|---|---|---|
| `felt` | ✅ Supported | `felt.const` value now stored as structured `FeltConstAttr` (printed `<{value = #felt<const 42> : !felt.type}>` — matches LLZK exactly, fixed 2026-05-17). Trait semantics (`NotFieldNative`, `Commutative`, `AllowConstraintAttr`, `AllowWitnessAttr`) **not encoded**. Folder/canonicalizer **not implemented**. Custom assembly format (`%0 = felt.add %a, %b`) **not supported** — generic format only. Most felt arith ops (add, mul, neg, etc.) **require a `function.def` wrapper** in LLZK; module-level use is VEIR-only. |
| `include` | ✅ Supported | `include.from` round-trips with typed `IncludeFromProperties { sym_name : StringAttr, path : StringAttr }`. **Fixed 2026-05-17**: was `FlatSymbolRefAttr` (printed as `@aliasName`); LLZK uses `StringAttr` (`"aliasName"`) per `SymbolNameAttr` constraint. Differential test now passes. `HasParent<ModuleOp>` trait **not encoded** — VEIR will accept the op anywhere, not just as a direct child of a module. `Symbol` trait semantics (uniqueness, lookup) **not encoded**. |
| `string` | ✅ Supported | Round-trips through `veir-opt`. One op (`string.new`), one type (`!string.type`). Custom assembly format (`%0 = string.new "x"`) **not supported** — generic form only. `Pure`, `ConstantLike`, `hasFolder` traits **not encoded**. |
| `cast` | ✅ Supported | `cast.tofelt` (int → felt) and `cast.toindex` (felt → index) round-trip. **Not encoded**: `InferTypeOpInterface` (result type must be explicit in textual form), `Pure`, `NotFieldNative` traits. Operand-type check (`AnyLLZKIntType`) **not enforced** — VEIR accepts any operand type. |
| `ram` | ✅ Supported | `ram.load` and `ram.store` round-trip with typed operand/result/region/successor *count* checks. Uses `index` and `!felt.type`. **Per-op type predicates not encoded** (e.g. VEIR will not enforce that `ram.store`'s second operand is `!felt.type`). **Not encoded**: `MemRead`/`MemWrite` memory effects, `WitnessGen` trait — VEIR treats both ops as pure. |
| `bool` | ✅ Supported | All 6 ops ported: `and`, `or`, `xor`, `not`, `assert` (with optional `msg`), `cmp`. **`bool.cmp`'s `predicate` enum (`FeltCmpPredicate`) stored as `IntegerAttr` with `i32` type** (values 0..5 for eq/ne/lt/le/gt/ge), not the LLZK-native `#bool<eq>`-style structured attribute. Printed form differs from LLZK: `<{predicate = 0 : i32}>` vs `<{predicate = #bool<eq>}>`. Range-checked (0..5) at parse time. **Not encoded**: `Pure`, `Commutative`, `NotFieldNative`, `TypesUnify` traits; `MemoryEffectsOpInterface` on assert. |
| `constrain` (eq only) | ⚠️ Partial | `constrain.eq` ported (2 operands, 0 results). **`constrain.in` deferred** until Array types land (Phase D.3). **Not encoded**: `ConstraintOpInterface`, `ConstraintGen`, `SymbolUserOpInterface`, `Commutative`, `ElementwiseMappable`, `TypesUnify` traits — VEIR accepts mismatched operand types. |
| `global` | ✅ Supported | `global.def` (`sym_name : StringAttr`, optional `const`, `type : Attribute`, optional `initial_value : Attribute`), `global.read` / `global.write` (`name_ref : FlatSymbolRefAttr`). **Fixed 2026-05-17**: `sym_name` was `FlatSymbolRefAttr` (`@x`); LLZK uses `StringAttr` (`"x"`) since `SymbolNameAttr` is a `StringAttr` constraint. **Not encoded**: `HasParent<ModuleOp>`, `Symbol`, `SymbolUserOpInterface`, `GlobalRefOpInterface`, `WitnessGen` on write. **No validation** that `type` is an LLZK type (VEIR accepts `i32` though LLZK requires `!felt.type` or similar), that `initial_value` matches `type`, that `name_ref` resolves to an existing `global.def`, that writes to `const` globals are rejected, or that `const` globals carry an `initial_value`. Differential test of `global.def + global.read` would pass, but our test exercises `global.write` too which LLZK requires a `function.def` wrapper for — hence XFAIL until Phase G.1. |
| `pod` | ❌ Unsupported | Planned Phase D.2. Blocked on `AffineMapAttr` + variadic-of-variadic (Phase C). |
| `array` | ❌ Unsupported | Planned Phase D.3. Types + non-symbol ops first; symbol-bearing dimension forms gated on Phase F. `ShapedTypeInterface` and `PromotableMemOpInterface` will not be encoded. |
| `function` | ⚠️ Partial | Phase F.5 prototype (2026-05-18): `function.def` (`sym_name : StringAttr`, `function_type : FunctionType`, 1 region body) and `function.return` (variadic operands, terminator). Verifier checks operand/result/region/successor arity; per-region terminator-presence still wired only via `OpCode.isTerminator` (no consumer yet). **Deferred**: optional `arg_attrs` / `res_attrs` DictArrayAttrs (argument decorators like `{llzk.pub}`), `function.call` (Phase C — needs `VariadicOfVariadic` and `SymbolRefAttr`), `FunctionOpInterface`, `Symbol` trait, `IsolatedFromAbove`, `AllowConstraintAttr` / `AllowWitnessAttr` / `AllowNonNativeFieldOpsAttr` checks (LLZK carries them as discardable `function.allow_*` attributes; VEIR passes them through unverified). **Round-trip identity test passes**; all 5 previously-XFAILed differential tests (Bool, Cast, RAM, Constrain, Global-write) lifted to PASS on 2026-05-18 by wrapping their bodies in `function.def` with the appropriate `function.allow_*` markers. |
| `polymorphic` | ❌ Unsupported | Planned Phase G.2. Blocked on regions, type variables, `LLZKSymbolTable` trait. |
| `struct` | ❌ Unsupported | Planned Phase G.3. The boss fight: regions + symbols + parametric types + member symbols + nested function. |
| `smt` | ❌ Unsupported | Orthogonal. Port-when-needed. |

---

## §Types

| LLZK type | Status | Caveats |
|---|---|---|
| `!felt.type` | ✅ | — |
| `!felt.type<"name">` | ✅ | Field-spec name is preserved as a `ByteArray` on `FeltType`. **No field-modulus semantics.** Distinct field names compare distinct in `Attribute.decEq`; that's the only place the name participates. |
| `!string.type` | ✅ | First parameterless dialect type ported. |
| `!array.type<dims x elem>` | ❌ | Planned D.3. Symbol-bearing dim forms `!array.type<5,@N x !felt.type>` blocked on Phase F. Affine-map dim forms `!array.type<#map x !felt.type>` blocked on Phase C.2. |
| `!struct.type<@A>` | ❌ | Planned G.3. |
| `!struct.type<@A<[5, @C, !felt.type, #map]>>` | ❌ | Mixed-kind parameter list — needs all of: integer literal, symbol ref, type, affine map. |
| `!poly.tvar<@T>` | ❌ | Planned G.2. |
| `!pod.type<[@field: !felt.type, ...]>` | ❌ | Planned D.2. Named-record attribute-list parameter. |
| SMT types (`!smt.bv<N>`, `!smt.int`, `!smt.array<K,V>`, …) | ❌ | Orthogonal. |

---

## §Attributes

| LLZK attribute | Status | Caveats |
|---|---|---|
| `#felt<const N> : !felt.type[<"name">]` (structured) | ✅ Supported | Landed 2026-05-17 as `FeltConstAttr { value : Int, fieldType : FeltType }`. Replaces the prior `IntegerAttr` workaround. Printed form matches LLZK's generic-MLIR output exactly: `<{value = #felt<const 42> : !felt.type}>`. First per-dialect structured attribute parser in VEIR — establishes the pattern for `#bool<...>`, `#poly<...>`, etc. (Note: dialect mnemonic in attribute syntax is `felt`, not `felt.const`; `const` is a keyword in the body.) Felt differential test now passes against `llzk-opt`. |
| `#field<name, prime>` (`LLZK_FieldSpecAttr`) | ❌ | Field modulus not encoded anywhere. Bigger semantic gap than the textual one. |
| `#bool.cmp<eq|ne|lt|le|gt|ge>` (enum) | ⚠️ Partial (IntegerAttr workaround) | Stored as `IntegerAttr` with `i32` type, values 0..5 mapping eq/ne/lt/le/gt/ge. Generic-form printed as `<{predicate = N : i32}>` rather than LLZK's `<{predicate = #bool<eq>}>`. The IR-level value round-trips faithfully; only the textual form differs. Range-checked at parse time. See `Veir/Dialects/LLZK/Bool/Properties.lean` `BoolCmpProperties`. |
| `SymbolRefAttr` (flat: `@name`) | ✅ | Landed upstream PR #533 as `FlatSymbolRefAttr`. Stored as the raw text including the `@`. Parsed via `parseOptionalFlatSymbolRefAttr`. |
| `SymbolRefAttr` (nested: `@outer::@inner`) | ❌ | Not yet representable. Needed for Struct/Polymorphic nested member references. Phase F (folded in from retired Phase B). |
| `AffineMapAttr` (`affine_map<(i,j) -> (i+j)>`) | ❌ | Planned C.2. Black-box (textual) representation recommended initially. |
| `DenseI32ArrayAttr` | ✅ (`DenseArrayAttr`) | — |
| `StrArrayAttr` | ❌ | Used by POD field names. Phase D.2. |
| `AllowConstraintAttr`, `AllowWitnessAttr`, `WitnessGen`, `ConstraintGen` traits | ❌ | These are *traits*, not attributes per se. **No trait encoding in VEIR today.** Felt ops carry no information about whether they're constraint-legal or witness-legal. |

---

## §Symbols and symbol tables

| Feature | Status | Caveats |
|---|---|---|
| `FlatSymbolRefAttr` (`@name`) as an `Attribute` case | ✅ | Landed upstream PR #533. |
| Nested `SymbolRefAttr` (`@outer::@inner`) | ⚠️ Partial | **Data structure landed 2026-05-17** as `SymbolRefAttr { rootRef, nestedRefs }` in `Veir/IR/Attribute.lean`. Parser supports flat form only — nested form (`::`) requires a lexer extension (no current consumer needs it). Resolver (`Veir/IR/SymbolTable.lean`) accepts the structure and returns `none` on non-empty `nestedRefs` (conservative). Phase G.2/G.3 will need to enable nested form. |
| `Symbol` trait (op declares a name) | ⚠️ | The trait is not encoded, but operationally an op can store a `FlatSymbolRefAttr` in its property dict and that round-trips. No invariant that the name is unique within a scope. |
| `SymbolUserOpInterface` (op resolves a symbol) | ⚠️ Partial | `Veir/IR/SymbolTable.lean` ships an **unverified** `IRContext.resolveSymbol` walker (Phase F.4, 2026-05-17). Per the Hybrid recommendation in `harness/regions-design.md` §7, this is *not* part of `WellFormed`; passes consuming it must handle `none` returns explicitly. |
| `SymbolTable` trait (parent op contains symbols) | ❌ | Walker treats the whole IR as a single flat scope; no nested-scope resolution. Walking up region trees to enclosing SymbolTable ops is the F.4 → G design upgrade. |
| `LLZKSymbolTable` (custom LLZK variant) | ❌ | Phase G (Polymorphic, Struct). |
| Nested symbol lookup (`@A::@B`) | ❌ | Phase F: parser + semantic resolution land together with regions. |

---

## §Affine maps

| Feature | Status | Caveats |
|---|---|---|
| `AffineMapAttr` round-trip | ❌ | Phase C.2 (planned black-box). |
| Affine-map semantic interpretation (compute dim/symbol arity, evaluate map) | ❌ | Out of scope for initial port. Required only if a pass needs to interpret the maps. |
| Variadic-of-variadic operands with `mapOpGroupSizes` | ❌ | Phase C.3. Used by `array.new`, `pod.new`. |

---

## §Op-level features

| Feature | Status | Caveats |
|---|---|---|
| Operand/result/region/successor *count* checks | ✅ | Encoded in `Veir/Verifier.lean`. |
| Operand/result *type* checks (per-op verifier) | ⚠️ | Only generic count-and-shape; per-op type predicates (e.g. "lhs and rhs must be same type as result") **not encoded**. |
| `InferTypeOpInterface` | ❌ | Cast uses this; result type will need to be explicit in the textual form. |
| Custom assembly format (`%0 = felt.add %a, %b`) | ❌ | Generic format only (`"felt.add"(%a, %b) : (...) -> ...`). Lit tests use generic form. |
| Variadic operands | ⚠️ | Simple variadic supported via OpCode arms; verifier per-op. |
| Variadic-of-variadic operands | ❌ | Phase C.3. |
| Optional operands/results/attributes | ⚠️ | Optional attributes are handled (e.g. `parseOptionalAttribute`); optional operands case-by-case. |

---

## §Regions and structural features

| Feature | Status | Caveats |
|---|---|---|
| Multi-block regions (structural) | ⚠️ Partial | **Surprise finding 2026-05-17**: `Operation.regions : Array RegionPtr`, `Region`, and `Block` are already defined in `Veir/IR/Basic.lean`; FieldsInBounds + WellFormed proofs exist for all three (`Veir/IR/Fields.lean`, `Veir/IR/WellFormed.lean`, `Veir/Rewriter/WellFormed/{Region,OpRegion,Block,BlockArguments,BlockOperands}.lean`). What's missing: dialect ops that *use* regions, block-arg-as-SSA-value integration, terminator invariants, symbol-table machinery. See `harness/regions-design.md` §3 for the full empirical state. |
| Block arguments as SSA values | ❌ | `BlockArgument` exists as a separate type but isn't a `ValuePtr` variant; ops inside a region can't consume block args via the normal operand path. Phase F.2.1. |
| Region entry block / argument list | ⚠️ Partial | Block-args structurally there; SSA integration is F.2.1. |
| Terminator op validation | ❌ | No "every block ends in a terminator" invariant (neither structural nor verify-time). Phase F.3.1 — verify-time only, per `harness/regions-design.md` §7 Alternative B. |
| `IsolatedFromAbove` trait | ❌ | Phase F.3.2 — verify-time only. |
| Rewriter primitives (block-level) | ⚠️ Partial | `Rewriter.initOpRegions` and `Rewriter.pushRegion` exist with WellFormed-preservation proofs (`Veir/Rewriter/WellFormed/{Region,OpRegion}.lean`). Block-level primitives (`createBlock`, `insertBlock`, `eraseBlock`, `moveBlock`, `moveRegion`) are Phase F.2.3. |
| `AffineScope` trait | ❌ | Out of initial scope (per `regions-design.md` §1). |
| `AutomaticAllocationScope` | ❌ | Out of initial scope. |
| `SingleBlock`, `NoTerminator`, `GraphRegionNoTerminator` | ❌ | Phase F (single-block variants); LLZK Struct/Polymorphic use `GraphRegionNoTerminator`. |

---

## §Op interfaces

LLZK defines several custom op interfaces. In VEIR there is no
mechanism to declare op interfaces as such; the marker effect is
achieved either by:
(a) checking the opcode in code that consumes the interface, or
(b) adding a `Properties` field that consumers read.

Either way, **no interface methods are dispatched dynamically**. The
implication: any LLZK pass that *requires* dynamic dispatch through an
op interface cannot be ported verbatim — it must be specialized to the
opcodes that implement the interface.

| Op interface | Used by | VEIR status |
|---|---|---|
| `ConstraintOpInterface` (marker) | Constrain ops | ❌ |
| `GlobalRefOpInterface` | Global | ❌ |
| `ArrayAccessOpInterface`, `ArrayRefOpInterface` | Array | ❌ |
| `MemberRefOpInterface` | Struct | ❌ |
| `FunctionOpInterface` (MLIR builtin) | Function | ❌ |
| `CallableOpInterface` (MLIR builtin) | Function call sites | ❌ |
| `SymbolUserOpInterface` (MLIR builtin) | Global, Function, etc. | ❌ |
| `PolymorphicOpInterface` | Polymorphic | ❌ |
| `InferTypeOpInterface` (MLIR builtin) | Cast | ❌ |
| `PromotableMemOpInterface` (MLIR builtin) | Array | ❌ |
| `ShapedTypeInterface` (MLIR builtin) | Array types | ❌ |

---

## §Traits (semantic markers)

| Trait | Status | Caveats |
|---|---|---|
| `Pure` | ❌ | Not modeled. DCE uses a heuristic ("zero results → side effects"). |
| `Commutative` | ❌ | Not modeled. Verified rewrites that depend on commutativity must prove it from the algebra, not the trait. |
| `Idempotent` | ❌ | — |
| `Involution` | ❌ | — |
| `MemRead`, `MemWrite`, `MemoryEffects<...>` | ❌ | Not modeled. RAM dialect ops will round-trip but VEIR sees them as generic ops. |
| `IsolatedFromAbove` | ❌ | Phase F. |
| `SymbolTable`, `Symbol` (MLIR builtin) | ❌ | Phase F (design alongside regions). |
| `ConstantLike` | ❌ | — |
| `HasFolder` (`hasFolder = 1`) | ❌ | No folder dispatch. Folders are an LLZK concept that maps to "constant folding inside the verifier"; VEIR doesn't have this hook. |
| `NotFieldNative` (LLZK-specific) | ❌ | Marks ops that aren't field-native (e.g., bit ops on felts). Not encoded. |
| `WitnessGen`, `ConstraintGen` (LLZK-specific) | ❌ | Mark whether an op produces a witness or a constraint. Not encoded — important for any verification of constraint-soundness. |
| `AllowConstraintAttr`, `AllowWitnessAttr` (LLZK-specific) | ❌ | Function-level traits. Not encoded. |

---

## §Verification machinery (VEIR side)

| Capability | Status | Caveats |
|---|---|---|
| `WellFormed` preservation across rewrites | ✅ | All rewriter primitives have completed proofs (`Veir/Rewriter/WellFormed/`). Zero `sorry` in `Veir/IR/` and `Veir/Rewriter/`. |
| Data-level refinement (`isRefinedBy`) | ⚠️ | Framework exists in `Veir/Data/Refinement.lean`. Only two passes use it (RISCV `constant_refinement`, `add_refinement`). |
| Dominance | ❌ | **Axiomatized in `Veir/Dominance.lean`** (9 axioms). Blocks any pass that requires SSA dominance reasoning (e.g., a properly-verified CSE). |
| First verified LLZK pass | ✅ | `felt-combine` (`Veir/Passes/Felt/Combine.lean` + `Veir/Passes/Felt/Proofs.lean`) implements `felt.add x (felt.const 0) → x` and proves the algebraic identity `add x (const 0) = x` against the `Veir/Data/Felt/` semantic model. Pass-side rewriter precondition discharges still use `sorry` (consistent with current VEIR practice). Proof is imported from `Combine.lean` so default `lake build` checks it. |
| Felt semantic model | ✅ Supported | **Phase E.5 (2026-05-19)** upgraded from provisional `abbrev Felt := Int` to `abbrev Felt (p : Nat) := ZMod p` via Mathlib. Model exposes `const`, `add`, `sub`, `mul`, `neg`. All verified Felt rewrites (15 as of 2026-05-20, see row below) re-proved with the modulus universally quantified — the IR doesn't pin a specific field, so passes must be sound for arbitrary `p`. Mathlib's `CommRing (ZMod p)` instances discharge each identity directly (`simp` or `push_cast; ring`). Axiom footprint: only `propext` and `Quot.sound` (standard Lean). Toolchain pinned to `v4.30.0-rc2` to match Mathlib master. |
| Verified `felt-combine` rewrites | ✅ Supported | **15 patterns** in `Veir/Passes/Felt/{Combine,Proofs}.lean`, each with a paired soundness theorem over `Felt p := ZMod p`. **Phase E.1-E.4 (4)**: `right_identity_zero_add`, `constant_fold_add`, `self_subtraction_to_zero`, `assoc_const_fold_add`. **Tier 1 (E.5 follow-up, 8 rewrites, 2026-05-20)**: `right_identity_one_mul`, `right_zero_mul` (multiplicative annihilation), `constant_fold_sub`, `constant_fold_mul`, `constant_fold_neg`, `add_neg_to_zero`, `neg_neg_to_self`, `add_const_swap` (canonicalize constants to right of `felt.add`). **Tier 2 (3 rewrites, same date)**: `add_sub_const_cancel` ((x+c)-c → x), `sub_add_const_cancel` ((x-c)+c → x), `assoc_const_fold_mul` ((x*c1)*c2 → x*(c1*c2)). All hold in any commutative ring; primality not threaded. Tier 3 (`div_self`, `mul_inv_self`, etc.) deferred — needs `[Fact (p.Prime)]`. |
| `felt-combine` + `dce` pipeline | ✅ Supported | Pipeline composition validated by `Test/LLZK/Felt/pipelines/{combine_then_dce,telescoping_then_dce}.mlir`. After `felt-combine`'s 15 verified rewrites fire to a fixpoint, the unverified `dce` pass (`Veir/Passes/DCE/dce.lean`) removes the now-unused intermediate consts/adds/subs. Tests are anchored by `constrain.eq` (0 results, treated as side-effecting by DCE's `hasSideEffects` heuristic) so DCE preserves the chain that feeds it. **Caveat**: `dce` is heuristic, not verified — anything with results is assumed pure, which is sound for the Felt dialect but not in general. |
| `interpret ; pass = interpret` | ❌ | No framework. Building one is its own project. |
| Side-effect analysis | ⚠️ | Heuristic in `Veir/Passes/DCE/dce.lean` (TODO at L12). Verified passes that depend on "this op is pure" must prove it explicitly. |
| Pattern preconditions discharged | ⚠️ | The `RewritePattern` infra requires several preconditions per call site; current passes discharge them with `sorry`. There are **~179 `sorry`s in `Veir/Passes/`** as of 2026-05-02 — none in the IR or Rewriter cores, all in pass implementations. |
| Pass composition theorems | ❌ | `PassPipeline` runs passes and re-verifies, but there is no theorem that two passes preserve a common invariant. |

---

## §Tests and tooling

| Capability | Status | Caveats |
|---|---|---|
| FileCheck lit suite | ✅ | 331 total as of 2026-05-18 (post-Function port + identity/invalid tests). Without `LLZK_OPT`: 323 PASS + 8 UNSUPPORTED. With `LLZK_OPT`: **331 PASS + 0 XFAIL + 0 FAIL** (Phase F.5 lifted all 5 XFAIL differentials). |
| Differential testing (vs `llzk-opt`) | ✅ Supported | Active when `LLZK_OPT` env or `llzk-opt` on `$PATH`. **All 8 differential tests pass cleanly** as of 2026-05-18: Bool (`logical`, lifted via `function.allow_non_native_field_ops`), Cast (`casts`, same), Constrain (`eq`, via `function.allow_constraint`), Felt (`arith`, module-level since 2026-05-17), Global (`def_read_write`, via `function.allow_witness` + `llzk.lang` module marker), Include (`from`), RAM (`load_store`, via `function.allow_witness` + non-native-field), String (`literals`). Four tests use a `.allowlist` for the cosmetic `value = N : i1` ↔ `value = true/false` printer divergence; no semantic divergences remain. |
| Unit tests (`lake test`) | ✅ | UnitTest target, 40/40. No Lean-level unit tests programmatically constructing and matching on LLZK `Attribute` cases (would catch Gotcha 2 from the Felt retro). |
| `veir-opt` CLI | ✅ | Single binary, parses and re-prints. Pass pipeline via `-p`. |
| Benchmarks | ⚠️ | `RunBenchmarks.lean` exists; not currently exercised by LLZK code. |

---

## §Known cross-cutting limitations

These are not LLZK-feature-specific but affect any downstream consumer:

1. **No structured LLZK attributes.** Everything `#dialect.name<...>`
   falls through to `UnregisteredAttr` (textual round-trip only).
   Pattern-matching on the structured form is not possible until VEIR
   gains a per-dialect attribute parser.
2. **Silent textual round-trip via `UnregisteredAttr`** — see
   `harness/porting-notes.md` §Gotcha 2. A test that only FileChecks
   text can pass even when the typed parser is dead code.
3. **No semantic interpretation of constraints.** Even when Felt
   round-trips, VEIR has no notion that `constrain.eq` defines a
   constraint over a finite field. Pass verification cannot use
   constraint semantics until that's modeled.
4. **No interpreter for any LLZK dialect.** VEIR's interpreter
   (`Veir/Interpreter/`) handles LLVM and RISCV. Felt has no
   interpreter arms. This blocks any `interpret ; pass = interpret`
   style proof for LLZK passes.
5. **Custom assembly is unsupported.** Anywhere LLZK MLIR uses
   `%0 = felt.add %a, %b` instead of `"felt.add"(%a, %b) : ...`, VEIR
   will reject it. Producers should emit generic-form MLIR before
   feeding to `veir-opt`.

---

## §Maintenance protocol

Three rules, restated from `plan.md` for visibility:

1. **Coverage updates are non-optional.** Any commit that changes the
   status of a row updates this file in the same commit.
2. **New gaps must be added.** Anyone hitting a previously-unrecorded
   gap during porting adds a row and links it from the porting commit
   message.
3. **Status downgrades are loud.** Removing or weakening support
   requires a status update and a note in `harness/porting-notes.md`
   explaining the regression.
