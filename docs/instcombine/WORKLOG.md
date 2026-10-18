# Coordinator checkpoint

This is a resumable audit, not a completed deliverable. The requested exhaustive
inventory and per-rewrite outcomes are still in progress. `README.md` is generated
from the inventory; `summary.json` contains current counts, not final totals.

The target remains LLVM `29eff20316c550d8e689a318c614e40186107820`, resolved before
the VM restart. Do not re-pin the target during resumption. The 20 source files
are preserved under `source/`, with their hashes in `llvm-pin.json`.

## Validation

```sh
python3 Tools/InstCombine/build_catalog.py
python3 Tools/InstCombine/check_coverage.py
PYTHONPATH=/tmp/instcombine-audit-parser python3 Tools/InstCombine/audit_functions.py
python3 Tools/InstCombine/audit_analysis_guards.py
python3 Tools/InstCombine/audit_entry_sites.py
python3 Tools/InstCombine/check_proofs.py
```

The parser audit uses `tree-sitter==0.25.2` and `tree-sitter-cpp==0.23.4`; install
these optional dependencies again if `/tmp` was cleared. It reports wrong
function references and entries whose ranges cross function boundaries.

`check_proofs.py` builds each recorded successful module, checks that the named
theorem has exactly `Pattern.Valid` for the named pattern, and inspects transitive
axioms. It rejects `sorryAx` and native/custom axioms. `verified-proofs.json`
records hashes of successful Lean files and a fingerprint of the local Lean
sources/toolchain. The catalog counts a proof only when both fingerprints match.
The checker also builds execution-test modules named by each proof manifest.
Re-run it after semantic dependencies change, even if the rewrite file is unchanged.

Coverage combines human claims, candidate-site mapping, and reviewed exclusions.
A complete mechanical checklist alone is not evidence of an exhaustive audit.
Generic return descriptions and unsplit multi-branch summaries are unfinished
families, not finished rewrites. An unavailable proof lemma is pending work,
not a Puddle limitation. Scalar specializations must not be described as proving
LLVM vector instances or unimplemented output-flag propagation.

## Work remaining after restart

- Comparison source review is now complete for both assigned ranges; continue
  independent QA if new discrepancies arise.
- Calls source audit is complete. AddSub/MulDivRem were reopened after source
  spot checks found stale intrafunction spans and duplicate aliases. Luna
  inventory_compares_b is correcting those and FP-only statuses before Memory.
- Luna inventory_finish_demanded_core owns Core and Demanded branch-detail QA,
  then the Bitwise helper/caller follow-up. Initial Core completion/exclusion
  claims were rejected because legacy broad summaries were unchanged; they are
  now being split into actual transformations, with query-only guard blocks
  classified as helpers. Demanded FP families also remain under detail review.
- Bitwise coverage has been reopened after concrete helper/caller duplication
  and guard-detail issues were found; see bitwise-coverage.json qa_followup.
- Revisit broad summaries in arithmetic, calls, demanded bits/classes, vectors,
  memory, and InstructionCombining. `function-boundary-audit.json` identifies
  some, but not all, questionable ranges.
- Continue Sol 5.6 implementation/proofs from the existing LLVM scalar semantic
  lemmas in `Veir/Passes/InstCombineLLVM/Semantics.lean`. The initial hard-coded
  constant-type bug is repaired and covered by execution/verifier tests at i8/i32.
  Execution checks now cover all seven patterns, including the exact NSW-output
  SubSwap variant. The stable checker checkpoint has five source rewrites and
  seven checked theorems. A fresh Sol worker, proof_negator_next, is implementing
  constant negation, boolean-extension negation, and sign-bit right-shift swaps.
- Give every real rewrite a checked proof, a concrete validated counterexample,
  or a specific confirmed Puddle limitation. Pending work remains pending until
  one of those outcomes is established.
- Rebuild the consolidated Markdown and report final counts only after coverage
  and per-rewrite outcomes are complete.

Luna workers own source discovery and descriptions. Sol 5.6 workers own Puddle
implementations and proofs. The runtime permits three workers alongside the
coordinator, despite the user's allowance of up to ten. Workers share the same
filesystem; assign distinct inventory files or explicitly transfer ownership.

## Proof-model repairs already made

`IntegerAttr.normalizeValue`/`ofInt` exposure supports typed normalized constant
creation proofs without changing their behavior. `HandleContext` helper exposure in Puddle validity allows structural kernel
reduction across module boundaries. Two byte-mask proofs in `Memory.lean` now
use `BitVec.and_assoc` instead of native `bv_decide`, removing inherited native
axioms from `Pattern.Valid`. These changes do not alter interpreter behavior.

The catalog now computes source coverage from current claims and exclusions on
each generation; summary.json distinguishes unmapped sites (including excluded
helpers) from genuinely unclassified sites. The advisory analysis-call scanner
does not change statuses; calls on constants and structural predicates may be
false positives and require manual review.

Root QA corrected additional false unsupported claims in compares-b: constant
shift arithmetic, clamp interval arithmetic, funnel rotations, and abs poison
semantics are supported scalar proof work. The cttz/ctlz trunc dispatcher is a
local delegation. select-L3074 is pending scalar funnel/freeze proof; source
nonpoison analysis only controls omission of freeze. select-L4056 still needs
external matcher/use reconstruction review. See capability guide pure-intrinsic
table before treating source CallInst as a generic effectful call.

A sixth source rewrite, NegateConstant, now compiles and has i8/i32 execution
tests including negative and signed-minimum inputs; its manifest is recorded.
Boolean-extension negation is active proof work. The last independent successful
checkpoint remains five source rules/seven theorems until the current batch is
rechecked; all-source fingerprints intentionally go stale during Lean edits.

Coordinator Select QA retired duplicate IDs select-L4846/5307/5329/5525 in favor
of their earlier source-range records (see retired-inventory-ids.json). The two
min/max reconstruction outcomes at5124/5127 are now distinguished: no-cast FP
reconstruction versus outer-cast reconstruction. The coverage checker refuses
to reconcile any file with explicit incomplete-family entries, even if a stale
human coverage claim says complete.

## Resumed checkpoint, 2026-10-18 around 21:20 UTC

- The independent proof checker now passes eight source entries / twelve
  patterns: NegateConstant, both BooleanExtension directions, and both exact-
  preserving sign-bit RightShift directions join the earlier five entries.
  Runtime execution tests at i8/i32 verify generated operation invariants.
  Next Sol batch: trunc negation and other concrete scalar Negator/algebra forms.
- Arithmetic and memory candidate reconciliation are complete. Core and demanded
  remain under whole-file human QA, with zero globally unclassified candidate
  sites. Candidate coverage alone does not establish exhaustiveness.
- Core ctpop/free-inversion scalar constructions were incorrectly marked
  unsupported solely for one-use/free-inversion profitability. These are now
  pending expressible scalar proof work; PHI/all-user mutations remain distinct.
- Root retired stale select-L5012 (duplicate of select-L4797; its source span
  actually dispatches foldSelectValueEquivalence, already select-L5014).
  Select helper wrappers5005/5036/5132 are delegations, not duplicate rewrites.
- Root confirmed missing FP/with.overflow/vector/effectful memory semantics for
  specific Select/Compare/Bitwise cases and recorded precise blockers.
  cast-L1981 is pending for the expressible trunc-nsw alternative; its independent
  sign-bit-analysis alternative remains a documented limitation. cmpb-L7001-add
  is pending for a compare-root specialization without changing other users.
- Pointer semantics are partially modeled: one-index GEP and 64-bit pointer/int
  casts exist. Pointer icmp and pointer-result select do not have interpreter
  cases. The capability guide now states these distinctions explicitly.

## Later resumed checkpoint (source review reconciled)

- All20 pinned source files now have completed human audit claims; mechanical
  coverage has zero unclassified candidate sites. This is source-review evidence,
  not a formal exhaustiveness proof. Source-specific QA continues during proofs.
- The last successful proof checkpoint has12 source entries /17 patterns:
  general NegateTrunc commute plus its recursive double-negation specialization,
  AddI1, SubI1, AllOnesSub joined the prior eight. The latter three now each have
  their own Lean file (the temporary AddSubBasic module was split per user).
  Sol is continuing additive negation/cancellation patterns.
- build_catalog now requires distinct Lean files across source-entry IDs and
  explicitly labels counts as entries with implementations in a stated scope.
  It does not claim a concrete specialization proves every upstream variant.
- Runtime reports 'agent thread limit reached' for additional Sol spawns even
  after a Luna completes. Current reusable threads: inventory_compares_b (Luna,
  owns bitwise/compares-a/compares-b/select/casts),
  inventory_finish_demanded_core (Luna, owns core/demanded/arithmetic), and
  proof_negator_next (Sol5.6, sole Lean/proofs-foundation/test owner). Root owns
  calls/memory/atomic and coordinator tooling. Avoid concurrent file edits.
- Root corrected stale add-L1948 opcode/guard data, split divrem-L1330 into the
  vector poison fold and four helper dispatches, and corrected optional-freeze
  versus essential SSA-analysis limitations. A continues arithmetic field QA.
- Root normalized Calls/Memory opcode arrays: actions/types belong in prose,
  actual affected opcodes in arrays. Intrinsic names use llvm.* notation.
  The nonterminating unreachable marker is a store through a poison pointer,
  not an unreachable terminator. Calls-null-callee preserves invoke/callbr
  without inserting that marker; ordinary calls receive it before erasure.
- Memory interpreter exists; effects are rejected by Puddle SupportedOpCode.
  Blockers must not claim that scalar load/store/GEP semantics do not exist.
- Current counts are roughly2230+ real rewrite entries and1150 pending outcomes;
  exact figures are generated in summary.json. Zero counterexamples so far.

## Proof and provenance checkpoint (2026-10-18, after 21:35 UTC)

- The stable proof checkpoint is 20 source entries and 32 Puddle patterns,
  all independently checked with ordinary kernel axioms. The i1 min/max and
  count-zero intrinsic families now have separate modules and verifier cases.
  The sole available Sol 5.6 worker is implementing six arbitrary-width AddSub
  bitwise identities next. Further new-agent spawns still fail with the runtime
  `agent thread limit reached`; existing Luna threads are being reused.
- Source inventory review remains reconciled across all 20 files. Vector, PHI,
  atomic, Calls, and memory received additional source-specific QA. Reconciliation
  is a checklist, not a formal completeness proof.
- Catalog validation now rejects proof-manifest source files or lines outside
  their inventory entry. It caught the negated-NOT reference at159 (prior add
  branch break), corrected to160, plus four stale unsupported-entry references.
  Existing IDs remain stable; their numeric suffixes are not source-line truth.
- Repeated generic helper calls are distinguished from source transformations.
  `stripNullTest` is outside the pinned directory, and `getFreelyInverted` is
  delegated to its inventoried helper cases. The De Morgan source algorithms
  retain one entry each, with scalar root-only proof scope distinguished from
  full all-user graph rewriting; proof specializations do not create new source
  rewrite entries. Explicit one-use/shared-use branches remain distinct.
- Corrected dataflow labels for constant-only ConstantRange/overflow tests,
  count-zero structural identities and funnel-shift constant checks. General
  nested-condition implication and narrowing based on SSA overflow facts are
  confirmed missing matcher capabilities. Metadata guards and one-use alone
  are not semantic blockers.
- New optional inventory fields preserve intrinsic IDs and value/type details
  separately from actual LLVM opcode arrays; the renderer validates and shows
  these fields. Luna is normalizing core/demanded/calls/memory while the other
  Luna checks arithmetic semantic boundaries and opcode fields.

## Stable checkpoint: 26 source entries / 46 patterns

- Sol completed six arbitrary-width AddSub bitwise identities (AddXorAnd,
  SubOrAnd, SubAddOr, SubAddAnd, SubOrXor, SubAndNot). The independent checker
  passed all 26 source entries / 46 patterns, with zero counterexamples.
  A separate Luna compared source, match/creation graphs, flag scopes and
  runtime verifier cases; no discrepancies were found. Sol is now processing
  the bitwise proof queue. Active Lean edits temporarily stale the global proof
  fingerprint; the last successful checkpoint remains 26/46.
- Luna produced three source-grounded queues: proof-queue-bitwise.json (25),
  proof-queue-arithmetic.json (23), proof-queue-casts-select.json (25). They are
  work lists, not completed outcomes; filter against current proof manifests.
- Opcode arrays across all inventory partitions now contain actual LLVM
  instruction mnemonics. build_catalog enforces the allowed set. Intrinsics and
  non-instruction labels are preserved in separate optional fields. Root fixed
  generic vector-binop opcode omissions, constant-folded output opcodes, and
  constructor/dispatch spans in InstructionCombining.cpp2493–2584.
- Demanded-bit/FP fact transfer and recursive dispatch were reclassified as
  helper/delegation where the span makes no independent IR change. Actual
  replacements/operand mutations/flag changes remain rewrite entries. Source
  counts consequently decreased; this is removal of non-rewrites, not dropping
  unimplemented work.
- Root reviewed all 11 analysis-like-call advisories: constants, ElementCount
  type facts, the nonselected XOR disjunct beside NUWSub, or structural ICmp
  inversion. Entries now retain analysis_audit_note, shown in the document and
  advisory report; no report entry is silently suppressed.
- External pinned ValueTracking.cpp9073–9100 was read to confirm
  isKnownInversion. It compares ICmp graphs/predicates/APInt regions. Corrected
  bitwise-L3730's erroneous description (output A xor ~B, not A xor ~A), and
  documented that both inversion rules match ICmps, not literal NOT instructions.
  This was an inventory error, not an LLVM counterexample.
- New capability boundary: LLVM icmp samesign is absent from IcmpProperties;
  ordinary flag-free scalar comparisons remain supported. Luna is auditing
  corresponding compare/select entries. Root documented default RV64 layout
  scope and restored pending status for one-index GEP stride-type
  canonicalization (root property mutation itself is expressible).

## Later stable checkpoint: 32 source entries / 68 patterns

- Sol added six bitwise source entries after the 26/46 checkpoint:
  bitwise-L4832 (XorAndOr), L5716 (XorAndXor), L5681 (XorOrSelf),
  L5690 (XorAndSelf), L5726 (XorNotAndSelf), L5730 (XorAndNotNot).
  Independent checker and executable verifier tests pass 32 source modules /
  68 pattern theorems. No counterexamples. ScratchBitwise.lean was removed.
- A Luna independently reviewed all excluded mutation and constructor-like
  candidates and their caller references. All 347 unmapped mechanical sites
  have exact exclusions; no omitted rewrite was found among the reviewed cases.
  Source reconciliation remains 20/20, zero unclassified sites.
- Luna is also auditing mutation APIs omitted by the original return/mutation
  regex, with an advisory mutation-audit report/tool. This is a separate
  completeness cross-check; no automated regex is treated as an exhaustive
  rewrite count.
- Added the missing icmp-samesign KnownBits transfer as an analysis helper.
  Kept strictness canonicalization as one source entry (cmpb-L7486), with its
  flagged-parameter limitation documented rather than counted as a second
  rewrite. Relevant compare/select/bitwise entries now distinguish source
  samesign handling from flag-free Puddle scope.
- Calls clamp-to-saturation with explicit narrow sext inputs and bswap-shift
  with constant byte-aligned amounts are pending useful scalar specializations;
  their general arbitrary-SSA analysis branches remain documented limitations.
  Clarified cast blockers so modeled trunc/zext flags are not blamed for missing
  SSA facts.

## Stable checkpoint: 34 source entries / 74 patterns

- Sol validated 34 source modules and 74 Pattern.Valid theorems, including
  bitwise-L5704 and bitwise-L1956. The latter includes the arbitrary-width
  or.disjoint poison condition. Executable i8/i32 verifier cases passed.
  No counterexamples have been found; 1,095 entries still awaited outcomes
  at this checkpoint, so the task remains incomplete.
- A separate Luna recorded source correspondence for the seven recent
  bitwise entries and six AddSub entries in proof-source-review.json, with
  module hashes. This review is independent of the kernel proof checker.
- Broader mutation scanning is recorded in audit_mutations.py and
  mutation-audit.json. Span corrections cover missed operand/property writes.
  Neutral-operand and always-overflow helper outcomes are being reconciled
  explicitly rather than hidden behind their caller's delegation entry.
- The pinned external ValueTracking.cpp:9042–9070 shows isKnownNegation is
  structural matching, not SSA analysis. Restored negator-L346a,
  sdiv-knownneg-L2042, and calls-extrema-negation-L2467 to pending. The signed
  division result is select(Op0 == INT_MIN, 1, -1), preserving the exceptional
  modular-negation case. Their scalar Puddle possibilities remain to implement.

## Stable proof checkpoint: 39 source entries / 90 patterns

- Sol added bitwise-L1999, L4840, L4848, L1983 and L1991 after the
  34/74 checkpoint. All are arbitrary-width scalar identities with explicit
  poison/disjoint-OR reasoning and source orientation variants. The kernel
  checker and executable verifier tests pass 39 modules / 90 theorems.
- Root added audit_opcodes.py to compare concrete C++ constructors with output
  opcode fields. Its initial 81 findings included real missing freeze, trunc,
  icmp, GEP and aggregate operations as well as overlapping sibling ranges and
  constant-folded builders. Luna is correcting the real omissions and recording
  reasons for the false positives. This tool is advisory, not an opcode oracle.
- A broader mutation-verb scan found a previously omitted nonlocal rewrite:
  replacedSelectWithOperand replaces select uses outside the defining block
  under dominance and single-predecessor guards. It is now inventoried as
  cmpb-L7141-replaced-select-operand with the CFG/Puddle blocker. Earlier
  mechanical coverage did not catch this success-return/replaceUsesOutsideBlock
  combination; source reconciliation is not a proof of exhaustiveness.
- Mutation advisory evidence now includes 95 independently reviewed Boolean
  returns (mutation-return-review.json) and 35 non-Boolean sites reviewed by
  root (mutation-manual-review.json). The audit validates their source pin,
  exact source text and referenced IDs, and distinguishes explicit reviews from
  mere range coverage. No default fallback silently claims a site is a query.
- Corrected a temporary erroneous restriction of OptimizeOverflowCheck to its
  unsigned-add comparison caller. Its other caller in InstCombineCalls.cpp:949
  handles signed/unsigned add/sub/mul with.overflow intrinsics; all helper
  descriptions and signed NSW versus unsigned NUW outcomes must retain that
  full scope. Prospective proof specialization is separate from source scope.
- Concrete helper transformations and caller dispatch are being reconciled for
  PHI control-flow folds, nonnull pointer simplification, GEP offset rebuilding,
  unreachable-region cleanup, and demanded FP classes. Actual IR mutation is
  not classified as analysis-only merely because it resides in a helper.

## Stable proof checkpoint: 45 source entries / 105 patterns

- Sol added the remaining basic complement identities (L1965, L5270, L5284,
  L4863) and the double-negated/sink-negation multiply entries. The checker
  passed 45 modules / 105 theorems before the next proof edits began.
- A second Sol 5.6 worker now owns comparison modules, CompareSemantics.lean,
  UnitTest/InstCombineLLVMComparisons.lean and proofs-comparisons.json. The
  original Sol owns arithmetic/bitwise modules and the original helper/test/
  proof files. Each manifest names its execution test module; the global
  checker merges them. Active edits stale the shared context hash, so displayed
  currently-validated counts may temporarily be zero until a coordinated check.
- Added explicit PatternMatch and parser-backed enclosing-guard opcode audits.
  Initial 51 span-local and 12 enclosing-guard sites exposed missing matched
  opcodes and stale source spans. Corrected actual omissions; remaining direct
  findings are documented exclusion guards/sibling alternatives. Enclosing
  analysis review corrected the undef-analysis distinction between disjoint
  and plain OR and retained structural isKnownInversion as analysis-free.
- Helper reconciliation now counts actual nonnull/GEP/PHI/CFG/FP transformations
  while separating their dataflow fact transfer and caller dispatch. Added the
  missing negated-factor multiply branch and a canonical run-loop DCE outcome
  with repeated-site references. Demanded shuffle lane-mask analysis is
  separate from its final mask write and single-lane insertion outcome.
- Latest advisory mutation review covers 1,737 candidate sites: 166 are outside
  source entry ranges, all with explicit evidence notes; none remain under the
  default needs-review label. Range coverage and regex audits remain checks,
  not a claim that every arbitrary C++ optimization can be found mechanically.

## Parallel proof batches and final helper audit corrections

- Three Sol 5.6 workers now have separate ownership: arithmetic/bitwise,
  comparisons/selects, and casts/integer intrinsics. Their manifests and runtime
  test modules are independent; a shared validation barrier prevents active
  edits from invalidating the global Lean context fingerprint mid-check.
- Corrected select-L5421's structural isKnownInversion description: it checks
  two ICmps and complementary predicate/constant regions, including matching
  samesign flags. It does not perform arithmetic-negation or NSW reasoning.
- Counted the earlier same-block use substitutions in simplifyDivRemOfSelect
  as a nonlocal mutation. Documented shared overflow postlude trunc/mask users,
  external unreachable-terminator dispatch, and the shuffle evaluator's exact
  reachable opcodes and poison-mask guards. The latter supports floating binary
  operations but rejects select in its caller gate; only integer div/rem, not
  shifts, reject poison shuffle-mask elements.
- Regenerated opcode audits: eight constructor and three direct matcher
  advisory sites remain explained sibling alternatives or exclusion guards;
  no enclosing-guard opcode or analysis findings remain.

## Stable proof checkpoint: 51 source entries / 111 patterns

- All recorded pattern modules, all three runtime test modules, and transitive
  theorem axiom checks pass together. Source outcomes: 51 proved entries,
  1,104 unsupported, 1,083 pending, zero counterexamples.
- New entries since 45/105: mul-negconst-L420, addconst-L882, cmpb-L5202,
  cmpb-L5206, cmpb-L5264, and cast-L243. Comparisons are explicit i32
  specializations; cast composition is i8->i16->i32 zero extension with both
  source nneg flags modeled. ComposeZExt.lean is the dedicated cast file.
- The global axiom check rejected the first comparison proofs: both pbv_decide
  and ordinary bv_decide use native certificate checking in this Lean version.
  Sol replaced them with Nat/BitVec order algebra. The accepted final proofs
  depend only on propext, Classical.choice and Quot.sound. No native or sorry
  axioms are counted. This was a proof-validation issue, not an LLVM
  counterexample.
- The three Sol workers resumed larger independent batches after this barrier.

- Follow-up source review corrected cast-L2030/L2034: the root-trunc guard
  excludes only pre-trunc widths larger than the destination. The recursive
  predicate admits other trunc/zext/sext nodes, and reconstruction may emit
  these casts. Their opcode sets now reflect the full recursive family rather
  than treating every trunc occurrence as a rejected input.

- The same recursive-cast review found missing integer-cast outputs,
  FP-to-integer nodes in truncation reevaluation, and vscale in zero-extension
  reevaluation. Added these opcode/intrinsic variants to their existing
  parameterized-family entries, retaining predicate-specific guards.

## Source-variant completion accounting

- Added explicit scope_review_complete, remaining_supported_scope and
  unsupported_scope manifest fields. Proof counts still count valid patterns
  for their stated scope; final completion now additionally requires all
  supported source variants to be accounted for. Missing scope reviews and
  known remaining supported variants have separate counters, which may overlap.
- Fixed-width examples, omitted supported flags, and unimplemented integer
  cast-pair alternatives are intermediate progress, not framework limitations.
  Missing vector/FP/CFG semantics remain legitimate documented limitations.
- Updated generated Markdown to strip trailing spaces. The upstream LICENSE
  snapshot retains its original bytes, including its final blank line.

- Restored calls-canonicalize-constant-arg-helper-L914 to pending: its only
  caller is a commutative intrinsic. Attribute-free modeled scalar integer
  intrinsic instances can use dedicated Puddle opcodes; treating every C++
  CallInst as an unsupported effectful call was too broad. The full parameter
  attribute permutation remains unmodeled.

## Active proof ownership after fresh worker contexts

- proof_negator_next: arithmetic/bitwise/shift stream, Semantics.lean,
  BitwiseSemantics.lean, ProofTactics.lean, Constants tests, foundation manifest.
- proof_casts_batch2 (Sol 5.6): cast/intrinsic stream, CastIntrinsicSemantics,
  CastsIntrinsics tests and manifest. Concrete next cast IDs: L1717, L1722,
  L1728, L1745, L1753, L1763, L1136, L1145, L1153. Its predecessor completed
  L1644 and all four count-bitreverse flag/orientation variants; ctpop reorder
  remains partial beyond bitreverse.
- proof_comparisons_batch2 (Sol 5.6): CompareSemantics, Comparisons tests and
  manifest. Predecessor completed eight arbitrary-width scalar entries /20
  patterns, including swapped/NE/disjoint variants; all listed supported
  scope gaps for those eight are closed. Next IDs: cmpb-L5477, L5483, L5509,
  L5631, L5654, L6275, L6484.
- Fresh workers replaced completed threads that began returning only context
  checkpoints. Their files were buildable at transfer; no partial proof work
  was discarded. Last GLOBAL stable check is still 51 entries /111 patterns.

## Stable proof checkpoint: 69 source entries /146 patterns

- Combined build, all three runtime test modules, and transitive axiom checks
  pass. Counts: 69 implemented/proved source entries, 146 recorded pattern
  variants, zero counterexamples, 1,103 unsupported, 1,066 pending outcomes.
- Compared with 51/111, this includes ten arithmetic/bitwise entries (12
  patterns), five new comparison entries plus the supported variants of all
  eight comparison entries (20 total), and three cast/intrinsic entries plus
  their flag/orientation variants.
- The first check counted only134 patterns because the prior comparison worker
  omitted12 additional_patterns records, despite implementing/testing them.
  The fresh worker registered every variant; the rerun individually checked
  all146 theorem types and axiom dependencies.
- Scope accounting still requires51 reviews (47 old records plus4 reviewed
  but conservatively marked false) and7 entries list known supported gaps.
  These are not completion claims for the entire LLVM families.
- Four new cast modules are independently buildable but were not counted yet:
  their runtime fixtures and manifest registration are the next worker step.
  All workers resumed after the69/146 barrier.

- Added audit_registered_patterns.py after the comparison registration omission.
  It finds concrete named Pattern.Valid declarations in the simple entry-module
  namespace layout and compares them with manifest theorem names; parameterized
  template lemmas are not enumerated. Findings during edits are expected. The
  catalog records them and cannot claim final completion with unregistered
  concrete declarations or unreviewed namespace layouts. The audit is syntactic;
  Lean checking still establishes the theorem type and dependency list.

## Ongoing next batch

- Continued the pinned target after coordinator context refresh; active workers
  remain the arithmetic/bitwise, cast/intrinsic, and comparison Sol 5.6 streams.
- Arithmetic/bitwise worker completed the seven remaining masked-merge operand
  arrangements and audited the original 47 source scopes. Finite flag and
  operand-order gaps are being implemented before another global checkpoint.
- Corrected proof-queue wording for multiplication: HasNSW/HasNUW are the
  outer instruction flags, not global options. The concrete source guards
  require those flags together with the corresponding inner-operation flags.
- Comparison worker reports seven new entries /30 patterns locally building;
  runtime tests and registration are in progress. Its next assigned batch is
  boolean-select identities, with separate select semantics/tests/manifest.

## Counterexample validation and source refinements

- Added a confirmed interpreter blocker for ic-extractvalue-empty-L4763:
  extractvalue has dialect/verifier support but no interpretOp' branch.
- Removed impossible FCmp from select-L1851: its NUWTrunc operand enforces
  integer comparison types. Clarified short-circuit logical AND/OR in the four
  nested-select flattening descriptions.
- Found a candidate model counterexample for freeze(add X,1) ->
  add(freeze X,1): Puddle chooses zero for freeze(poison), giving0 versus1.
  Assigned a concrete Pattern and formal not-Valid proof to the comparison
  worker. This is not an LLVM bug claim; deterministic freeze is a model
  limitation. No counterexample count is recorded until independently checked.
- Extended the checker to type-check counterexample theorems as not-Valid and
  store their certificates separately in verified-counterexamples.json. The
  catalog now requires current-context validation for negative outcomes too.
  Both proof kinds reject unexpected axioms, duplicated theorem/definition
  registrations, and missing axiom-output reports.
- Comparison queue prioritizes finishing supported variants of its current
  seven entries (disjoint OR, guarded relational predicates, and XOR orders)
  after the freeze check, before moving on to the queued select identities.

- The comparison runtime suite stalled in an actual rewrite loop, not Lean
  proof compilation: the XOR constant-move rule omitted LLVM's nonconstant-B
  canonicalization guard and the fixture supplied two constants. Greedy
  applyInContext repeatedly swapped them. The algebraic Valid proof is sound;
  the worker is restoring termination behavior and source-valid fixtures.
  This is not a semantic counterexample and is not counted as one.
- Clarified L6484's exact (A xor C) cmp B -> (A xor B) cmp C output. Source
  m_c_ICmp permits comparison swapping but m_Xor itself is ordered; an extra
  XOR-operand permutation is not required to cover this source branch.

## Stable proof checkpoint: 85 source entries /206 patterns

- Combined build, all runtime/verifier suites, and exact Pattern.Valid theorem
  typing/transitive-axiom audit passed. No unexpected axioms or unregistered
  concrete theorem declarations. There are85 implemented/proved entries,206
  validated patterns,0 counterexamples,1,104 unsupported entries, and1,049
  pending outcomes. All implemented source scopes have been reviewed;20 still
  list supported variants awaiting implementation.
- Compared with69/146, this adds nine cast entries /11patterns, seven comparison
  entries /30patterns, and19 operand-arrangement variants in existing
  arithmetic/bitwise entries. Counts are source scopes, not full-family claims.
- The comparison runtime loop was fixed with a contextual one-use/nonconstant
  guard on the XOR constant-move pattern; its50 regressions then passed in1.6s.
  Formal semantics deliberately ignores that contextual guard and proves the
  unconditional identity. A follow-up review will broaden the execution guard
  from mlir.constant to all modeled constant-like opcodes.
- All workers released to continue: foundation lands four prepared NSW
  variants; casts generalizes prior mask rules to arbitrary widths; comparisons
  formalizes the freeze model counterexample then finishes current source
  variants before the queued boolean-select batch.

- Added a pointer-model blocker for ic-inttoptr-ptrtoint-roundtrip-L434:
  InterpretsTo quantifies fixed results over every memory, while inttoptr uses
  memory-dependent decode/object identity. An impossible fixed-result premise
  must not produce a vacuous success claim. ptrtoint-only and simple GEP
  remain separately modeled; this is not a blanket pointer-opcode exclusion.

## Runtime fixture audit after85/206

- applyInContext returning some context does not imply a rewrite fired. Asked
  all workers to assert replacement of the precise producer used by test.test
  in addition to final verifier/output checks. Foundation has strengthened all
  eight test helpers and its complete suite passes.
- Comparison flag fixtures used nsw/nuw Boolean dictionary keys that the
  parser ignores; NswNuwProperties reads overflowFlags instead. Assigned
  correction to overflowFlags=3:i32 plus source-property assertions. This
  affects claimed runtime coverage, not the existing quantified Valid proofs.
- Foundation's four NSW-preserving variants now compile and pass actual
  overflowFlags=1:i32 fixtures with output NSW assertions. They are registered
  and independently axiom-audited by the worker, awaiting next globalcheck.

## Stable checkpoint: 86 implemented /85 proved /1 model counterexample

- Global checker built86 per-entry modules, validated212 Pattern.Valid
  theorems and1 not-Valid theorem, and ran all four runtime/verifier suites.
  Axiom lists contain only the approved kernel axioms. Registration audit
  reports no missing concrete declarations.
- The negative result is ic-freeze-push-through-op-L5236, implemented as
  freeze(add X,1) -> add(freeze X,1). Width2, poison X, and constant1 give
  modeled values0 and1 respectively. The fixture meets one-use/nonpoison-
  constant/unflagged-add guards. This is a deterministic-freeze model
  counterexample, not an LLVM bug. Its certificate is separate in
  verified-counterexamples.json.
- This check includes arbitrary widths for six cast-mask families, ZExtNNegI1,
  and zext/zext composition; four NSW-preserving arithmetic variants; two
  all-IntegerAttr subtraction variants; and strengthened actual-firing and
  parsed-overflow-flag assertions in the runtime suites.
- Current totals: 2,238 transformation entries;86 implemented,85 proved,
  1 counterexample,1,105 unsupported,1,047 pending. Among implemented positive
  entries, all scope reviews are done and9 still list supported scope gaps.
  The task remains incomplete. All workers resumed after the stable check.
- Corrected sub-L2443 source description: dyn_castNegVal accepts any
  ConstantInt, not just signed-negative constants. The newly added patterns
  already implement the correct all-constant scope.

## Further source-description and constructor audit

- Extended the advisory output-opcode scan to lowercase create wrappers and
  explicit-opcode generic constructors such as CastInst::Create. It now
  recognizes 2,624 constructor sites. The eight remaining candidates are the
  previously reviewed sibling-branch or constant-folding cases.
- Corrected bool multiplication entries: mul-L540 matches mul/zext/sext and
  emits and/zext; mul-L555 matches mul/sext and emits select/sub. The constant
  branch mul-L618 folds negation of constants, so no sub instruction is emitted.
- Added fneg to the five FAddCombine output families that can reach the
  createNaryFAdd final-negation wrapper. Refined the three negative-operand
  addition helper descriptions/opcodes and documented both placements of the
  increment, including manually commuted root-add forms.
- Audited every dyn_castNegVal caller. Corrected cmpa-L3788/L3790 and
  cmpb-L8025/L8028 arm orientation and constant/explicit-negation conditions;
  the helper accepts all ConstantInt values, not only signed-negative ones.
- Corrected shift-common-oramount-L557 reasoning: OR with W-1 is at least W-1,
  and a defined shift amount is less than W, so it must equal W-1. Other amounts
  make the source poison. No power-of-two width assumption applies. The srem
  shift-amount queue includes the sign-bit power-of-two divisor and the zero
  remainder of negative dividends. Clarified shift-L1216's high W-C bit mask.
- The proof workers continue independently. Current sources are under edit;
  the most recent stable global result remains 85 proved entries / 212 positive
  patterns plus one formal model counterexample. New declarations are counted
  only after the next combined checker run.

## Compound matcher and overlap follow-up

- Added audit_match_aliases.py using the pinned PatternMatch.h definitions.
  Reviewed AddLike/disjoint-OR, SExtLike/zext-nneg, optional casts, logical
  AND/OR/select forms, Signum's shift/negation graph, intrinsic aliases, and
  branch matchers. Corrected missing match opcodes and relevant descriptions
  in 33 source entries, plus optional output truncation in the log2-ceil fold.
  The remaining 11 alias candidates have explicit source exclusions recorded
  in match-alias-review.json. The enclosing-guard audit now includes compound
  matchers and treats an ancestor else arm as a failed guard, rather than a
  positive match requirement; no unresolved enclosing candidates remain.
- Verified from pinned Instruction.cpp that LLVM CondBr and UncondBr opcodes
  both print as the IR mnemonic br, so the catalog's mnemonic convention stays
  unchanged. Source/reference headers were inspected under /tmp; the target
  commit and snapshot hashes were not changed.
- Retired two overlapping GEP umbrella entries whose outcomes already have
  precise entries. Reasons/replacement IDs are in retired-inventory-ids.json.
  Corrected stale switch source spans so the select-range and KnownBits folds
  reference their own successful returns. Current transformation count is
  2,236 (3,048 total entries including delegation/helper sites).
- Five prepareWorklist cases now have explicit unsupported outcomes: dead-edge
  PHI updates, branch/switch dead-edge propagation, unreachable-block cleanup,
  dead-instruction/noalias deletion, and ConstantVector/ConstantExpr operand
  folding. These require missing CFG/liveness/alias or constant-expression
  semantics; scalar instruction constant folding remains pending separately.
- The m_Not definition accepts both xor operand orders. Foundation source
  reviews now explicitly list missing constant-left NOT variants in 20 entries;
  existing RHS-constant proofs remain valid, but those scope gaps are not closed.
- Cast/intrinsic worker reached a stable checkpoint with ctpop bswap/rotate
  cases and nine further scalar cast-pair patterns. Comparison worker reached
  a stable checkpoint with 16 dynamic signed/unsigned relational cancellation
  patterns and the remaining two XOR comparison orientations. Foundation has
  five new patterns across three entries and is finishing shift/multiply flags.
  Waiting for its buildable checkpoint before the combined proof check.
- Added argparse handling to check_proofs.py: --help now displays usage and
  exits instead of accidentally launching a full build. No proof criteria changed.
- A Luna worker is independently reviewing all overlapping inventory sites and
  the compound-matcher exclusions. The cast worker is paused to respect the
  four-slot runtime limit; comparison and foundation will resume after validation.

## Stable checkpoint: 89 implemented /88 proved /1 model counterexample

- Combined checker passed: 89 per-entry modules, 248 positive Pattern.Valid
  proofs, and one not-Valid theorem. All execution/verifier suites passed;
  allowed-axiom audit and registration audit were clean. Certificates and
  proof-validation.log record this checkpoint. All three Sol 5.6 workers resumed
  afterward, so later edits intentionally make current-context validation stale.
- Relative to the prior 85/212 positive checkpoint: foundation added six patterns
  across three entries (including two L233 flag slices); casts added 12 patterns
  for ctpop reorder and cast-pair composition; comparisons added 18 patterns
  for XOR operand orientation and dynamic relational add cancellation.
- At validation time there were 1,110 unsupported entries and 1,037 pending
  outcomes; 27 implemented entries recorded remaining supported variants.
  These are source-entry counts, not assertions that complete LLVM families
  are proved. The full task is still incomplete.

## Luna overlap and missing-site review integration

- overlap-review-luna.json independently reviewed 70 overlapping source sites
  in 35 groups and all 11 compound-matcher exclusions. Applied its two span
  corrections (gcd division and disjoint insert/extract index paths). The
  index-path comparisons are property comparisons, not SSA/dataflow analysis;
  corrected the corresponding three uses_analysis fields.
- no-site-review-luna.json reviewed all 70 entries lacking a heuristic site,
  with concrete source-action evidence. Applied 11 genuine span corrections
  in demanded-bits/FP-class and landingpad clauses. Retired the mislocated
  ic-vector-binop-splat-reassociate-L2719 duplicate in favor of the precise
  ic-vector-binop-splat-shuffle-reassociate-L2671 entry.
- Eight branch-specific entries already referenced their result constructors
  or branch action correctly, but installed results at a later shared site.
  Kept precise primary ranges and added separately validated supporting source
  links for shared construction/replacement, rather than widening ranges over
  unrelated sibling branches. The disjoint-OR ctpop entry also links its exact
  acceptance guard. build_catalog.py validates/renders these optional ranges.
- After the final duplicate retirement: 3,047 total inventory entries, 2,235
  transformation entries, and 1,109 unsupported outcomes. Pending transformations
  remain 1,037 relative to the stable 88-positive /1-negative checkpoint.

## October 19: variant completion and undef/freeze source review

- All 20 foundation entries with missing constant-left NOT forms now have those
  forms, including independent choices when a pattern contains multiple NOTs:
  105 additional concrete patterns, with firing/verifier fixtures. Comparison
  workers added 18 OR/mixed-AddLike/subtraction variants and closed the remaining
  five comparison scope gaps. Cast composition now covers all 17 modeled scalar
  integer table cases; casts L1160/L1167/L1172 add three new arbitrary-width
  source-entry implementations. These local checks await the next global barrier.
- Luna independently reviewed m_Undef, freeze helper dispatches, GEP normalization,
  and two undef-excluding guards (undef-freeze-review-luna.json). The pinned matcher
  includes poison, so negator-L125a and freeze-use-choice-L5446 are not entirely
  blocked by missing undef semantics. Scalar poison cases are pending proof or
  counterexample; actual undef and vectors remain separately limited.
- select-L718 and addhelper-L1210 also return to pending: they exclude LLVM undef
  through a source guard rather than matching an undef operation. Their algebra
  may be proved in Puddle's deterministic scalar/poison domain; an absent undef
  predicate alone is not an adequate whole-family blocker. No theorem is inferred
  from this source review. Removed the stale negator unsupported proof record.
- Five freeze visitor wrappers now have kind=delegation and link to their actual
  helper implementations. They no longer inflate transformation/unsupported
  counts. The use-choice helper can return a safe arbitrary SSA select arm, not
  only constants; its description and installer source reference now say so.
- GEP normalization now references only its local loop (3375-3421), with matched
  opcode getelementptr; sext/zext/trunc are outputs. Preceding external simplify
  and demanded-vector calls have two separate delegation entries. The cast
  worker is checking a model counterexample: the GEP interpreter uses unsigned
  idx.toNat, while the LLVM rewrite sign-extends a narrow negative index.
- The comparison worker is checking a separate freeze(poison) all-ones choice
  counterexample, reusing its existing negative-proof infrastructure. Neither
  candidate is counted until a formal not-Valid theorem is validated.
- Catalog after source corrections: 3,049 entries, 2,230 transformations,
  644 delegations, 175 analysis helpers, 1,100 confirmed unsupported. There are
  currently 92 registered implemented entries / 382 patterns; the last successful
  global certificate remains 88 positive entries / 248 patterns plus one negative
  entry. Current source edits make that certificate historical. Only one already
  implemented entry still records supported variants pending (multiply/shift flags).
- Added proof-queue-core-inversion.json for ten source helper branches that can
  reuse current semantic infrastructure. It is a queue, not an outcome report.

## Follow-up scalar capability corrections

- A scalar-capability screen restored three source families to pending:
  ic-gep-constant-offset-to-ptradd-L3423 has a meaningful one-i64-index default
  RV64 specialization; cmpb-L8701 is shared by ICmp and FCmp visitors, not only
  FP; bitwise-L5370 permits the legal degenerate i1-to-i1 bitcast of scalar ICmp.
  Luna independently confirmed these source subsets. No proofs are inferred.
- Clarified cast-L2740/L2820 blockers: their source guards require integer widths
  different from the pointer width, whereas Puddle only interprets the i64 case.
  That interpreted identity-width case cannot trigger the source normalization.
- cast-L243's scope review found additional modeled ByteType and same-address-
  space pointer-only bitcast compositions. The cast worker recorded them as
  supported pending variants; memory-reconstructing pointer conversions remain
  separately constrained. The 17 completed IntegerType patterns remain valid.
- Catalog scope accounting now also displays/counts remaining supported variants
  on counterexample entries. A negative theorem does not hide explicitly listed
  unimplemented alternatives, such as other GEP index-normalization branches.
- Pointer and freeze-poison counterexample modules passed focused builds,
  firing/verifier fixtures, and allowed-axiom checks. Both workers are holding
  Lean edits. Foundation is completing poison negation and add/sub/mul flag
  weakening before the global validation. Its generic helper does not handle
  shl at its call sites; the separate shl flag mutation is not charged to that
  helper's source entry.
- external-reference-sources.json records immutable URLs and hashes of the
  supplemental pinned matcher, cast-legality, opcode and analysis references
  read under /tmp. They are reference evidence, not additional transformation
  files or a change to the target LLVM commit.

## Resumed checkpoint and scalar GEP review

- Preserved the original LLVM pin after restart. Focused cast/GEP builds were rechecked successfully; the next full proof checkpoint awaits the foundation matcher correction.
- Luna reviewed unsupported scalar families (unsupported-scalar-review-luna.json). Five one-index GEP composition/exact-index families return to pending because default-RV64 i64 unflagged specializations are modeled. Their arbitrary layout/vector/flagged scopes remain separate questions.
- Sequential-index merging must use a successful simplifyAddInst result; emitting arbitrary new addition would not reproduce that source branch. Corrected its opcode lists, removed nonexistent inttoptr from the selective pointer-difference entry, and listed all four possible exact division/shift output opcodes.
- The pointer-difference blocker concerns selective use replacement and pointer object identity, not an inttoptr reconstruction that the source never performs.

## Full validation after restart

- Built all 96 source-entry modules and associated runtime suites (289 build jobs). Checked the exact Pattern.Valid / not-Valid theorem types and allowed axioms for 385 positive pattern variants and three counterexamples. No sorry/native-evaluation axioms; no unregistered concrete patterns.
- Current verified counts: 96 implemented entries = 93 proved entries + 3 counterexample entries; 388 concrete patterns. Catalog: 2,230 transformations, 1,092 unsupported, 1,042 pending; three implemented entries retain supported scope work. All 20 source/config files reconciled, with zero unclassified candidate sites. This is a checkpoint, not task completion.
- Counterexamples are the two freeze model choices and narrow GEP index normalization. Updated the capability guide to reflect the validated GEP result.

- Reviewed Luna pending-core/demanded report as advisory: it includes helper/delegation and already-implemented rows, and some generic evidence citations need correction. Its proposed unsupported classifications were not applied wholesale. The independently confirmed pointer-roundtrip fixed-result/provenance blocker was applied. Scalar symmetric select/minmax reassociation remains pending; rebuilding a two-node DAG is possible despite source in-place mutation. Added proof-queue-symmetric-pairs.json.
- Clarified common-condition select distribution: at least one simplifyBinOp arm must succeed in the source. A generic distribution pattern that builds both arms would prove broader algebra rather than reproduce that guarded branch.

## Active next tranche (2026-10-19 00:47 UTC)

- Foundation Sol 5.6 worker: finish mul-shl-constant-L233 outer flags, then core inversion branches 3024/3030/3050/3061/3073/3080 and strict-bitwise 3165. Owns foundation semantics, modules, constants fixtures and proofs-foundation.json.
- Cast Sol 5.6 worker: finish cast-L243 ByteType/same-address-space pointer composition scope, then core inversion casts L3150. Owns CastIntrinsicSemantics, cast modules/fixtures and cast manifests.
- Comparison/select Sol 5.6 worker: initial 17 scalar select queue entries and select-L718, then core inversion select/minmax branches3094/3097 and logical DeMorgan variants coordinated with foundation. Owns SelectSemantics/CompareSemantics, select modules/fixtures and proofs-selects.json.
- No source pin update is needed. Before each global validation, hold all Lean edits, run `python3 Tools/InstCombine/check_proofs.py`, then `python3 Tools/InstCombine/build_catalog.py` before resuming workers. Source-only documentation corrections may continue during the barrier.
- Current edited sources naturally invalidate the previous whole-context certificate; the last successful checkpoint is still 93 positive source entries /385 positive patterns plus3 counterexamples. Do not present historical certificates as validation of newly edited Lean.

## Normalized i1 matcher coverage gap

- Coordinator found matchIntConstant compares raw attr.value, while IntegerAttr.ofInt normalizes signless i1 all-ones to +1. A matcher requesting -1 therefore misses valid parsed i1 NOT inputs even when its conditional validity theorem quantifies over all widths. This is matcher incompleteness, not a failed theorem.
- matcher-normalization-review.json lists candidate files/owners; source width restrictions must be checked before assigning an actual gap. Foundation owns the reusable matcher/proof approach; comparison/select and casts workers were notified and will include parsed i1 firing fixtures. Existing whole-family scope-complete claims need this cross-cutting review before final completion.

- First normalization migration batch passed locally:10bitwise source entries /100existing orientation patterns now match bit-normalized constants, with all100 parsed i1 firing/progress/verifier tests and representative i8 coverage in UnitTest.InstCombineLLVMNormalizedBitwise. Existing theorem names preserved; allowed-axiom audits pass. Root resolved these10audit rows; foundation owner registers execution modules.

## Normalization migration completed locally; next global barrier

- All23legacy source entries now use normalized bit matching for all-ones constants. Cast worker migrated10files/100orientations with exhaustive i1 firing fixtures; foundation migrated13files with i1 per-entry fixtures and existing i8 orientation coverage. Existing theorem names are preserved, and both runtime suites pass. The26candidate audit rows (23legacy plus3newcore files) are resolved locally.
- Foundation added7core inversion source entries /48 Valid patterns, with all48runtime variants and normalized-i1 cases passing. Finite deeper recursive shapes and logical DeMorgan variants remain explicitly supported pending work; mul-shl-L233 outer flags also remain.
- Cast worker added11Byte/pointer cast-composition variants and core inversion-casts L3150 with12patterns. Select worker has at least12source entries /19patterns locally checked. All workers are reaching a stable edit barrier for the next combined proof/axiom/runtime check. GEP constant-offset implementation is in flight.
- Removed scalar-only wording from22generic source opcode-parameter labels (including vector-only source branches); scalar model restrictions belong in proof scope. Optional AST audit dependency versions are now in Tools/InstCombine/requirements-audit.txt.

## Combined normalization and source-entry checkpoint

- Built 119 source-entry modules and runtime fixtures (319 jobs); checked 480 exact Pattern.Valid theorem types and three negated Pattern.Valid proofs with only the allowed logical axioms. All 26 normalization review candidates are resolved and globally checked.
- Saved catalogue: 118 implemented entries, 115 proved entries, three counterexample entries, 483 patterns; 1,092 unsupported and 1,020 pending transformations. Nine implemented families retain supported scope work. This is not task completion.
- Workers resumed: foundation arithmetic/bitwise and flag scope; cast worker narrow supported GEP cases; comparison worker remaining select and core inversion cases.
- Audit command-line entry points now parse arguments before writing reports: --help displays usage without running the audit, and unknown options are rejected.
- Python tools compile and their help path works. The all-files whitespace check reports the vendored LLVM LICENSE.TXT final blank line; the immutable upstream license is retained byte-for-byte. Non-vendored changes pass the whitespace check.

- Further source QA restored four incorrectly unsupported scalar families: core shift/bitwise distribution L1016/L1026/L1039 and calls extrema move-NOT L2441. The shift branches require no SSA dataflow analysis; the constant-mask description now includes both X and Y and the exact nested opcode structure/guard. Recursive min/max inversion has expressible finite scalar shapes. Vector/undef limitations remain explicit. These corrections increase pending work; they are not new proof outcomes.

- Source QA of masked-ICmp helper branches439/468/482/492/498 and floating-class branch410 added their strict OR and short-circuit select input forms, shared canonical-mask guards and caller references. L439 now lists only emitted AND/ICmp opcodes; its OR operations compute APInt constants, not runtime instructions. Fixed its incomplete formula and clarified branch410 is the NaN/ordered complement. Existing helper delegation stays separately recorded.
- The two match-opcode advisory candidates already have valid inventory notes: an excluded ULT-add shape and a separately inventoried XOR+KnownBits disjunct. Saved explicit dispositions in match-opcode-review.json.

- Added advisory audit_extra_output_opcodes.py:208 entries list output opcodes not explained by directly recognized constructors in their span. This is not208 confirmed errors: helper-created operations, in-place mutation, and construction outside narrow source spans can explain candidates. A Luna review is queued for the next available worker slot; no automatic removals or proof-status changes are made.

## User-requested stopping point

- User requested wrapping up only current proofs and then a summary. No new proof batches were started after that request; select/foundation are holding, and cast/GEP is finishing its in-flight generalization before the final combined check. The original all-rewrites goal remains incomplete.
- Luna completed a contextual pass on the39AddSub/AndOrXor output-opcode candidates. Coordinator applied26source-checked corrections across the initial and contextual batches, rejected two incorrect proposals, and retained a helper-generated truncation missed by a third proposal. The remaining167advisory cases stay explicitly unresolved; they are neither assumed correct nor counted as failed proofs.
- Generic match/replacement opcode-parameter notes now render in the Markdown catalogue instead of remaining only in JSON.

## Final checkpoint at the requested wrap-up

- All proof workers are paused at stable boundaries; no further proof batches are active.
- Full combined validation passed: 127 source-entry modules, 327 build jobs, 530 exact Pattern.Valid theorem checks and 3 negated Pattern.Valid counterexample checks. Runtime firing/progress/verifier suites passed. Allowed axioms are propext, Classical.choice, and Quot.sound; there are zero unregistered concrete patterns.
- Saved current catalogue: 126 implemented source entries, 123 with positive proofs and 3 with formal counterexamples, comprising 533 concrete patterns. All certificates match the current Lean source context.
- Inventory has 2,230 transformation entries across 20 reconciled files, plus 644 delegation sites and 175 analysis helpers. There are 1,088 unsupported entries and 1,016 pending source outcomes. Fifteen implemented entries retain supported variant work; 167 output-opcode metadata audit candidates remain unresolved. The full original task is not complete.
- Counterexamples concern two freeze semantics choices and narrow GEP index normalization in the current Puddle model; they are not claims of LLVM miscompilation.
- The immutable source pin remains 29eff20316c550d8e689a318c614e40186107820. Non-vendored whitespace checks and Python compilation pass; the upstream LICENSE.TXT final blank line is preserved.
