# Verifying mem2reg

To start with, I agree that we go with non-pruned IDFs for block-argument placement and a dominator-tree traversal for SSA renaming. 
For the proof to be a bit easier, I think we can follow Zhao et al.'s decomposition into smaller semantics-preserving transformations, keeping the allocation until the SSA construction and load-store forwarding have been justified.

**Supported programs**

The first version would promote one fixed-size scalar allocation at a time, allocated in the entry block of an SSACFG region. Its pointer would only be used as the address operand of direct, non-volatile loads and stores matching the allocation's scalar type and size. We'll reject candidates whose pointer escapes or is used in pointer arithmetic, so we don't need alias analysis for these checks.

We'll require an initialising store before leaving entry and before any entry-block load. Initially we will exclude calls, nested regions and allocations with uses in unreachable blocks.

The escape and pointer-arithmetic restrictions would apply to the allocation being promoted. The surrounding function can still contain other allocations and pointer computations. We'll need the memory model to justify why those accesses cannot alias the promoted allocation.

**SSA construction and load-store forwarding**

1. We can compute the non-pruned IDF of blocks containing stores to the allocation and insert block arguments at those merge points. During SSA renaming, we traverse the dominator tree to determine the reaching definition at each load and each outgoing edge, following [MLIR's mem2reg](https://mlir.llvm.org/doxygen/Mem2Reg_8cpp_source.html).

2. For the correctness proof, we can first insert the block arguments with loads in predecessor blocks and stores at the start of the destination block, as in [Zhao et al., Section 4.2](https://web.eecs.umich.edu/~mahlke/courses/583w24/lectures/Apr8/group23_paper.pdf).

   ```text
   predecessor
     incoming = load p
     branch B(..., incoming)

   B(..., value)
     store value, p
     ... original instructions ...
   ```

   This passes the current memory value through a block argument and writes it back. We can prove that this preserves the semantics before replacing the original loads. That way, the proof still has the memory value to compare the SSA value against.

   Zhao's algorithm uses maximal phi-function placement. Our version instead can use John's IDF to select the blocks where this transformation is applied as in normal `mem2reg`.

3. We can then prove load-store forwarding, store elimination and dead allocation elimination separately, and compose the results. The simulation relation would relate the source allocation's contents to the target SSA value, as well as relating the remaining memory and variable environments.

For block-argument insertion, we'll need to prove the argument and all incoming branch-operand updates correct together, including backedges and multiple successor occurrences that name the same block. We'll also need to preserve typing and dominance.

For SSA renaming, we need to show that the reaching definitions agree across each edge into a block without a new argument. I think we can prove this using the path-based dominance and DF definitions, then connect it to the executable dominance and IDF analyses through their correctness results.

**Memory-model requirements**

Checking the allocation pointer's uses isn't enough under the current pointer semantics. Another pointer can still access the allocation, including through type punning in memory.

For restricted mem2reg, I think [CompCert's block-based memory model](https://compcert.org/doc/html/compcert.common.Memory.html) is a useful starting point. A pointer identifies an allocation block and an offset within it. Pointer arithmetic changes the offset without changing the block, so it cannot derive a pointer to a different allocation.

| Requirement | What we need to establish |
| --- | --- |
| Non-aliasing | Accesses through unrelated pointers cannot read or overwrite the promoted allocation |
| Dead allocation elimination | Deleting the allocation preserves defined observable behaviour, including observations of subsequent allocations' addresses |
| Stack deallocation | Returning from the function releases its stack allocations while preserving caller memory and surviving heap allocations |
| Load-store semantics | The inserted load followed by a store of the same value preserves the required memory relation, including poison |

CompCert's block-based model doesn't by itself give us general LLVM pointer-integer casts. For those, I think we should go to at [Beck et al., A Two-Phase Infinite/Finite Low-Level Memory Model](https://arxiv.org/html/2404.16143v1), which supports pointer-integer casts and proves dead-alloca elimination. Adopting the full two-phase design would be a larger change than starting with abstract allocation blocks.

We'll need to specify how allocation, pointer casts, loads and stores interact, including pointers reconstructed from integer bytes. Stack deallocation alone won't prevent forged pointers, and we can't ignore different numerical addresses if the program observes them through pointer-to-integer conversion. So allowing casts elsewhere in the function needs more than adopting CompCert's block-based model unchanged.

We can also look at CompCert's [SimplLocals proof](https://github.com/fanlong/compcert4lean/blob/d8d1e5b696eb5c263ff3eb9030e4eb8b9dde6655/CompCert4Lean/Cfrontend/SimplLocalsproof.lean) for the simulation relation. It relates promoted memory variables to target temporary values and uses a memory injection for the remaining allocations. That's part of the correctness proof, though. We still need the memory semantics to justify why removing the allocation cannot affect observable behaviour.
