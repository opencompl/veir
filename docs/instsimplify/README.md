# LLVM InstSimplify audit and Puddle port

The [catalog](rewrites.md) records 800 audited source entries. **238 independent rule families are implemented and proven `Pattern.Valid`**, within their stated domains; **zero counterexamples were established**. Another 482 entries remain without complete standalone ports. This selection excludes entries marked `covered_by`, but still includes 69 forwarding/helper/guard entries; it is not a count of 482 distinct unproved equations. See the blocker categorization below. All entries have terminal outcomes.

The final combined Lean build, declaration-type audit, and axiom audit passed. All 1,168 source return sites are accounted for. See [summary.json](summary.json) for counting details and [validation.json](validation.json) for the validation record.

## Frozen sources

The target is LLVM `main` commit [`fb3ef86994775a17f4e9f1576d17590e79a8e198`](https://github.com/llvm/llvm-project/commit/fb3ef86994775a17f4e9f1576d17590e79a8e198), resolved from GitHub at the start of this task. Its commit timestamp is October 21, 2026, 11:34:40 p.m. America/Los_Angeles (October 22, 06:34:40 UTC). See [llvm-pin.json](llvm-pin.json). Later LLVM commits are outside this snapshot.

The audit covers rewrite-producing branches in [`llvm/lib/Analysis/InstructionSimplify.cpp`](upstream/InstructionSimplify.cpp), including the shared recursive simplification algorithms and intrinsic simplifiers. The [pass driver](upstream/InstSimplifyPass.cpp) delegates to this library and also deletes trivially dead instructions. Pass scheduling, dead-instruction deletion, public API forwarding, and failure returns are distinguished from peephole rewrites. Calls into external constant-folding, value-tracking, or target-library machinery are identified as delegations; their independent implementations are not silently counted as rules defined in InstSimplify.

Each rule is identified by its successful source return line (`IS` followed by the line number; suffixes distinguish multiple rules at one return). Source links use the frozen commit. Separate coverage files account for source return sites, including failures and delegations; source return counts are not rewrite counts. The `u` suffix separates an unsupported scalar `undef` alternative from another alternative at the same return that has a proof. The pass driver's dead-instruction deletion is documented separately in the catalog.

Luna agents prepared the source inventory; Sol 6.1 agents reviewed the source guards while implementing the Puddle patterns and proving them. The coordinator checked coverage, reviewed classifications and source-output fidelity, and consolidated the results. Return-site coverage is a consistency check, not a proof that the descriptions capture every semantic condition. Each entry links the original source for review.

## Formalization boundary

Puddle's [`Pattern.Valid`](../../Veir/PatternRewriter/Puddle/Validity.lean) requires supported operations, a constrained root, structural well-formedness, and refinement of the matched root results. The proofs use the repository's existing operation semantics. They are not proofs about LLVM's C++ implementation or a separate proof that the VeIR semantics completely match LLVM.

The relevant operation interpreter is `Llvm.interpretOp'` in [`OpInfo.lean`](../../Veir/Dialects/LLVM/OpInfo.lean), not the separate CTree interpreter. An opcode being declared or accepted by the parser does not establish that this interpreter models it. A vacuous proof caused by an unimplemented interpreter case will not be counted as a successful port.

The repository's existing interpreter definitions carry two native `bv_decide` dependencies from [`MemoryState.loadByte64` and `MemoryState.llvmLoad`](../../Veir/Interpreter/Memory.lean#L245), in addition to Lean's standard logical axioms. They appear transitively in many `Pattern.Valid` axiom reports, including integer-only rules, because validity references the shared interpreter. They predate this port. The axiom audit records this trusted baseline explicitly; it must not be described as an axiom-free development.

Some LLVM rules explicitly simplify an operation whose source execution has immediate undefined behavior, such as integer division by zero. This is different from an unimplemented opcode: the interpreter models these cases as `Interp.ub`. Since Puddle's `InterpretsTo` premise requires an `.ok` result, a validity proof for such a source-UB rule has no defined source executions to check. These entries must disclose that fact and substantiate it with the modeled source behavior; they do not claim a stronger execution theorem.

Puddle can inspect operation context during matching, but [`MatchDecl.Models`](../../Veir/PatternRewriter/Puddle/Validity.lean) deliberately does not retain facts from `inspectOperation`. A rewrite whose validity depends on dominance, assumptions, known bits, or another contextual analysis therefore needs additional formal support. Native guards on modeled types and properties can be used in validity proofs.

Ports must state their supported type and flag domain. In particular, a scalar integer proof is not a vector or floating-point proof. Unsupported variants and missing facilities belong in each rule's entry. Proof difficulty alone is not evidence that a rewrite cannot be represented.

LLVM integer constants are normally represented by VeIR's `mlir__constant` with a normalized APInt payload. An alternate VeIR encoding such as `mlir__zero` is covered only where stated. Pointer ports use the existing RISC-V 64-bit data layout and pointer model. In particular, `inttoptr` decodes object identity from memory, while the local `InterpretsTo` judgment requires a memory-independent intermediate result. The pointer cast entries document this limitation and include checked operational witnesses; these are not reported as LLVM counterexamples or counted through vacuous validity proofs.

Some constant-range comparison guards are implemented extensionally by checking every value of the integer type. Those entries disclose their exponential runtime cost (`2^w` for width `w`); the proofs cover arbitrary widths, but this implementation is impractical at large widths. These are reference ports, not an integrated replacement for the LLVM pass.

Counts refer to independently ported source rule families. A family parameterized by opcode, predicate, bitwidth, or operand order counts once, with its individual `Pattern.Valid` declarations listed in the catalog. Caller entries with `covered_by` cross-references do not add to the implemented/proven count. A proof of a supported scalar domain does not establish the unsupported domains of the same LLVM rule. A zero counterexample count means none was established; it does not classify unimplemented rules as correct.

## Why 482 entries have no complete standalone port

This is a categorization of the existing `unsupported` entries without a `covered_by` cross-reference, not a record of 482 failed theorem attempts. Each entry has one primary category, so the counts below sum exactly to 482. Some entries have additional blockers; secondary categories in [blockers.json](blockers.json) overlap and are non-exhaustive.

| Primary category | Entries | Missing support or explanation |
| --- | ---: | --- |
| Floating-point semantics | 109 | Floating-point operations/intrinsics, NaNs, signed zero, rounding, exceptions and constrained FP behavior need modeled semantics. |
| Recursive and contextual simplification | 84 | Generic recursive simplifier correctness, composition of returned rewrites, and select-arm substitution soundness have not been formalized. |
| Certified analysis facts | 75 | KnownBits, ranges, dominance, assumptions, poison implication or decomposition facts need semantic certificates retained by Puddle validity. |
| Forwarders and other catalog structure | 69 | Internal forwarding calls, condition/eligibility helpers, apparently unreachable branches and outer guards do not supply independent local rewrite equations. |
| Vector and aggregate semantics | 56 | Vector/scalable/SVE, insert/extract, shuffle/interleave and overflow-result aggregate semantics are missing from the relevant interpreter. |
| Pointer and target-model limitations | 24 | Pointer provenance, DataLayout, constant expressions, cast interpretation and memory-dependent pointer identity need additional formal support. |
| Undef semantics | 24 | LLVM nondeterministic undef is not interpreted; this is distinct from the existing scalar poison semantics. |
| Other intrinsic semantics | 15 | Includes pdep/pext, scmp/ucmp, high-half multiplication and fixed-point multiplication intrinsics. |
| External evaluators and memory/calls | 13 | Generic external constant-folding contracts and global-memory/load/call/GC semantics need formal support. |
| PHI and control-flow context | 13 | Incoming-edge, predecessor and CFG semantics needed by PHI-based simplification are not modeled by local rewrite validity. |
| **Total** | **482** | |

The 69 catalog-structure entries comprise 56 plain forwarding calls, three condition/eligibility helpers, eight apparently unreachable min/max helper paths, and two preempted-branch/outer-guard cases. For example, IS4158/IS4161 forward to already-proved saturating-comparison rules, and IS4858/IS4889 forward to already-proved select rules. They should not be presented as separate failed mathematical proofs. Apparent unreachability is based on source inspection, not a formal global theorem.

The remaining 413 entries need additional semantics, analysis certificates, or contextual/recursive correctness machinery for a complete port. An opcode being declared does not imply its semantics is implemented. These classifications describe the current formalization boundary, not an impossibility of extending Puddle or evidence that LLVM is incorrect. The established counterexample count remains zero.

This review also corrected misleading catalog reasons: IS1344 needs a certified KnownBits fact and returns poison (it does not involve `undef`); IS0879/IS1122 forward to nonrecursive dominance analysis; IS0125 needs select-context reasoning rather than a successful recursive-result certificate; IS5237b/IS5242b need `undef` semantics as well as poison analysis; and IS7924's reachability guard does not imply scalar poison is unmodeled. [blockers.json](blockers.json) records the category and source link for every selected entry.

## Artifacts

- `inventory/*.json`: Luna's branch-level source audit and return-site coverage; final implementation outcomes are recorded separately in `results/*.json`.
- `upstream/`: the frozen LLVM sources, retaining their upstream license headers.
- [rewrites.md](rewrites.md): the full source catalog, opcodes, guards, missing facilities, proof domains, and links to each Lean file/theorem.
- `results/*.json`: reviewed implementation outcomes and corrections to inventory descriptions.
- [blockers.json](blockers.json): per-entry primary/secondary blocker categories for the 482 entries discussed above.
- [summary.json](summary.json): generated counts, with `independent_ports` excluding shared caller sites.
- [validation.json](validation.json): final check results, toolchain, artifact hashes, and trusted axiom baseline.
- [Veir/InstSimplify](../../Veir/InstSimplify): separate rule modules and shared proof helpers.
- [Veir/InstSimplify.lean](../../Veir/InstSimplify.lean): generated aggregate import target.
- [AxiomAudit.lean](AxiomAudit.lean): generated `#print axioms` checks for all reported theorem declarations.
- [ProofTypeAudit.lean](ProofTypeAudit.lean): checks that every reported proof name is a theorem and every successful entry includes a theorem concluding `Pattern.Valid`.

## Reproduce the checks

From the VeIR repository root, using the repository's pinned Lean toolchain:

```sh
python3 docs/instsimplify/check_inventory.py
python3 docs/instsimplify/check_results.py --generate
python3 docs/instsimplify/render_catalog.py
lake build Veir.InstSimplify Veir.InstSimplify.ProofAudit
lake env lean docs/instsimplify/ProofTypeAudit.lean
lake env lean docs/instsimplify/AxiomAudit.lean > /tmp/instsimplify-axioms.log
python3 docs/instsimplify/check_axioms.py /tmp/instsimplify-axioms.log
```

`check_results.py` rejects pending/missing outcomes, missing proof artifacts, duplicate IDs, cyclic shared implementations, unaccounted rule files, and `sorry`/`admit`/new `axiom` declarations. The Lean build, theorem-type audit, and axiom audit are separate checks: Python bookkeeping alone does not validate a proof. Diagnostic witness files for unsupported entries are built and audited without being counted as successful ports. During development, `--allow-pending` permits generating an aggregate of completed results; it is not the final completeness check.
