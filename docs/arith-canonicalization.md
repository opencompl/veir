# MLIR Arith canonicalization and Puddle verification

Pinned LLVM commit: [`32ec2901f308caee5c76dbdc8d21a12a08d5457a`](https://github.com/llvm/llvm-project/commit/32ec2901f308caee5c76dbdc8d21a12a08d5457a).
Resolved from `refs/heads/main` at 2026-10-19 02:07:58 UTC; all source links below use this commit.

## Scope and counting

The inventory includes registered TableGen patterns, handwritten C++ canonicalization patterns, and individual operation-fold rules invoked by `--canonicalize`. Concrete template instances have separate entries; symmetric operand-order variants explicitly described in one rule are counted once. Constant evaluation is a rule family parameterized by its constant operands. The generic canonicalizer's dead-operation removal and constant uniquing are infrastructure, not additional Arith peepholes. `arith.constant`'s attribute-returning fold hook is materialization support: the greedy driver skips folding constant-like operations.

Opcode lists use `arith.constant` as the representative constant producer; upstream `ConstantLike` matchers and fold adaptors can obtain attributes from other producers too. An empty replacement-opcode list means forwarding an existing SSA value. In-place folds list the operation that remains after its operands or properties change.

Each Puddle rule is checked independently. The collection does not reproduce the greedy driver's scheduling or the order of early returns within a fold hook; independently valid rules can overlap. The source conditions below describe when the upstream branch applies.

A proven entry means a Lean theorem of `Puddle.Pattern.Valid` for the stated implementation scope. Scalar integer rules quantify over widths and include poison/refinement and the flags stated in each entry. This does not claim coverage of vector/tensor/index variants: VeIR's Arith interpreter currently models scalar integers. Missing floating-point, index, shaped-value or contextual semantics are documented explicitly. A counterexample is a checked failure of the stated upstream rule, not a failed proof search.

**Signed remainder semantics:** verification retains VeIR's original `arith.remsi` semantics, as requested: `INT_MIN % -1` is undefined behavior. The interpreter, direct LLVM lowering, and existing UB tests are unchanged. The pinned constant folder can materialize zero in this case; that is a refinement of an undefined source, not evidence that the source operation is defined.

**Arith support:** [Veir/Dialects/Arith/Puddle.lean](../Veir/Dialects/Arith/Puddle.lean) adds the shared Puddle proof API, including operation-interpretation lemmas and constant match/create helpers. The translations build on VeIR's existing scalar-integer Arith parser, verifier, interpreter, and LLVM lowering. Additional proof helpers live alongside the individual rewrite files.

## Results

| Inventory entries | Implemented | Proven correct | Counterexamples | Unsupported | Pending |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 266 | 183 | 172 | 11 | 83 | 0 |

Implementation counts include counterexample patterns; only proven patterns are candidates for use in an optimizer. The source snapshots and SHA-256 manifest live in [arith-canonicalization/upstream](arith-canonicalization/upstream). The JSON inventories and result manifests are the machine-readable sources for this document.

## Reproducing verification

`Veir.Passes.ArithCanonicalize` imports every implemented entry, including checked counterexamples. It is imported by the main `Veir` library, so the proofs are part of the normal build. The module does not register counterexample patterns as optimizations.

```sh
lake build Veir
lake test
uv run lit Test/Interpreter/Arith Test/Passes/ArithToLLVM -v
python3 Tools/arith-inventory --check
```

The inventory checker validates source checksums, TableGen registration coverage, operation fold-hook coverage, complete outcomes, and generated documentation/imports. Lean checks the proof declarations. Matcher regression tests additionally check normalized i1 constants, stable constant operand ordering, creation of fresh result types, and the positive-one guard on signed extended multiplication.

## Rewrites

### TD001: AddIAddConstant

[Original code: ArithCanonicalization.td:73–78](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L73-L78).

Combine nested addi with a constant on each level: addi(addi(x,c0),c1) -> addi(x,c0+c1).

**Matched:** `arith.addi`, `arith.constant`. **Replacement:** `arith.addi`, `arith.constant`.

**Conditions:** Both matched constants are ConstantLike integer attributes; APInt arithmetic is at the result width; overflow flags are merged by bitwise intersection.

**Status: Counterexample.** Lean-checked direct ¬Pattern.Valid witness at i4: x=0x1, c0=0x8, c1=0xf; source result=0x8, while the replacement is poison. Both source operations and the replacement retain nsw=true, nuw=false under upstream flag intersection.

**Coverage:** general-width scalar integer pattern using arith.constant; i4 counterexample

**Lean:** [Veir/Passes/ArithCanonicalize/TD001.lean](../Veir/Passes/ArithCanonicalize/TD001.lean); `Veir.ArithCanonicalize.TD001.pattern_not_valid`.

### TD002: AddISubConstantRHS

[Original code: ArithCanonicalization.td:81–86](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L81-L86).

Fold addi(subi(x,c0),c1) into addi(x,c1-c0).

**Matched:** `arith.addi`, `arith.subi`, `arith.constant`. **Replacement:** `arith.addi`, `arith.constant`.

**Conditions:** Both constants are ConstantLike integer attributes; overflow flags from inner subi and outer addi are merged by bitwise intersection.

**Status: Counterexample.** Lean-checked direct ¬Pattern.Valid witness at i4: x=0x1, c0=0x1, c1=0x8; source result=0x8, while the replacement is poison. Both source operations and the replacement retain nsw=true, nuw=false under upstream flag intersection.

**Coverage:** general-width scalar integer pattern using arith.constant; i4 counterexample

**Lean:** [Veir/Passes/ArithCanonicalize/TD002.lean](../Veir/Passes/ArithCanonicalize/TD002.lean); `Veir.ArithCanonicalize.TD002.pattern_not_valid`.

### TD003: AddISubConstantLHS

[Original code: ArithCanonicalization.td:89–94](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L89-L94).

Fold addi(subi(c0,x),c1) into subi(c0+c1,x).

**Matched:** `arith.addi`, `arith.subi`, `arith.constant`. **Replacement:** `arith.subi`, `arith.constant`.

**Conditions:** Both constants are ConstantLike integer attributes; overflow flags from inner subi and outer addi are merged by bitwise intersection.

**Status: Counterexample.** Lean-checked direct ¬Pattern.Valid witness at i4: x=0x1, c0=0x1, c1=0x7; source result=0x7, while the replacement is poison. Both source operations and the replacement retain nsw=true, nuw=false under upstream flag intersection.

**Coverage:** general-width scalar integer pattern using arith.constant; i4 counterexample

**Lean:** [Veir/Passes/ArithCanonicalize/TD003.lean](../Veir/Passes/ArithCanonicalize/TD003.lean); `Veir.ArithCanonicalize.TD003.pattern_not_valid`.

### TD004: AddIMulNegativeOneRhs

[Original code: ArithCanonicalization.td:102–107](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L102-L107).

Rewrite addi(x,muli(y,-1)) to subi(x,y).

**Matched:** `arith.addi`, `arith.muli`, `arith.constant`. **Replacement:** `arith.subi`.

**Conditions:** Multiplier constant must be scalar/splat integer all-ones (-1); replacement uses default/no-overflow flags (TODO in source notes lost overflow flags).

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar all-ones multiplier, arbitrary source overflow flags, and default-flag subtraction target; includes signless i1.

**Coverage:** scalar integer arith.constant instance of pinned upstream pattern

**Lean:** [Veir/Passes/ArithCanonicalize/TD004.lean](../Veir/Passes/ArithCanonicalize/TD004.lean); `Veir.ArithCanonicalize.TD004.pattern_valid`.

### TD005: AddIMulNegativeOneLhs

[Original code: ArithCanonicalization.td:110–115](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L110-L115).

Rewrite addi(muli(x,-1),y) to subi(y,x).

**Matched:** `arith.addi`, `arith.muli`, `arith.constant`. **Replacement:** `arith.subi`.

**Conditions:** Multiplier constant must be scalar/splat integer all-ones (-1); replacement uses default/no-overflow flags (TODO in source notes lost overflow flags).

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar all-ones multiplier, arbitrary source overflow flags, and default-flag subtraction target; includes signless i1.

**Coverage:** scalar integer arith.constant instance of pinned upstream pattern

**Lean:** [Veir/Passes/ArithCanonicalize/TD005.lean](../Veir/Passes/ArithCanonicalize/TD005.lean); `Veir.ArithCanonicalize.TD005.pattern_valid`.

### TD006: MulIMulIConstant

[Original code: ArithCanonicalization.td:118–125](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L118-L125).

Combine muli(muli(x,c0),c1) into muli(x,c0*c1).

**Matched:** `arith.muli`, `arith.constant`. **Replacement:** `arith.muli`, `arith.constant`.

**Conditions:** Both constants’ integer attribute types must equal the outer result type; overflow flags are merged by bitwise intersection.

**Status: Counterexample.** Lean-checked direct ¬Pattern.Valid witness at i4: x=0xf, c0=0x2, c1=0x4; source result=0x8, while the replacement is poison. Both source operations and the replacement retain nsw=true, nuw=false under upstream flag intersection.

**Coverage:** general-width scalar integer pattern using arith.constant; i4 counterexample

**Lean:** [Veir/Passes/ArithCanonicalize/TD006.lean](../Veir/Passes/ArithCanonicalize/TD006.lean); `Veir.ArithCanonicalize.TD006.pattern_not_valid`.

### TD007: AddUIExtendedToAddI

[Original code: ArithCanonicalization.td:133–136](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L133-L136).

Replace addui_extended(x,y) by addi(x,y) and x for the unused overflow result.

**Matched:** `arith.addui_extended`. **Replacement:** `arith.addi`.

**Conditions:** Second/overflow result must have no uses; any replacement value is permitted for that unused result; addi receives default/no-overflow flags.

**Status: Cannot be implemented with current Puddle support.** The rewrite replaces an unused secondary result by an arbitrary value. Puddle Pattern.Valid requires elementwise refinement of every root result; MatchDecl.Models deliberately forgets use-count facts from inspectOperation. It cannot validate the exact upstream dead-result replacement without a liveness-aware semantic model (and the add/sub arbitrary replacement can have a different type).

**Coverage:** Full upstream rule

### TD008: SubUIExtendedToSubI

[Original code: ArithCanonicalization.td:144–147](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L144-L147).

Replace subui_extended(x,y) by subi(x,y) and x for the unused borrow result.

**Matched:** `arith.subui_extended`. **Replacement:** `arith.subi`.

**Conditions:** Second/borrow result must have no uses; any replacement value is permitted for that unused result; subi receives default/no-overflow flags.

**Status: Cannot be implemented with current Puddle support.** The rewrite replaces an unused secondary result by an arbitrary value. Puddle Pattern.Valid requires elementwise refinement of every root result; MatchDecl.Models deliberately forgets use-count facts from inspectOperation. It cannot validate the exact upstream dead-result replacement without a liveness-aware semantic model (and the add/sub arbitrary replacement can have a different type).

**Coverage:** Full upstream rule

### TD009: SubIRHSAddConstant

[Original code: ArithCanonicalization.td:154–159](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L154-L159).

Fold subi(addi(x,c0),c1) into addi(x,c0-c1).

**Matched:** `arith.subi`, `arith.addi`, `arith.constant`. **Replacement:** `arith.addi`, `arith.constant`.

**Conditions:** Both constants are ConstantLike integer attributes; replacement uses default/no-overflow flags (TODO in source notes lost overflow flags).

**Status: Succeeded — proven.** All-width Pattern.Valid proof: arbitrary source add/sub overflow flags may poison; the default-flag replacement computes the same modular result when source is defined.

**Coverage:** scalar integer arith.constant instance of pinned upstream pattern

**Lean:** [Veir/Passes/ArithCanonicalize/TD009.lean](../Veir/Passes/ArithCanonicalize/TD009.lean); `Veir.ArithCanonicalize.TD009.pattern_valid`.

### TD010: SubILHSAddConstant

[Original code: ArithCanonicalization.td:162–167](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L162-L167).

Fold subi(c1,addi(x,c0)) into subi(c1-c0,x).

**Matched:** `arith.subi`, `arith.addi`, `arith.constant`. **Replacement:** `arith.subi`, `arith.constant`.

**Conditions:** Both constants are ConstantLike integer attributes; overflow flags from inner addi and outer subi are merged by bitwise intersection.

**Status: Counterexample.** Lean-checked direct ¬Pattern.Valid witness at i4: x=0x1, c0=0x8, c1=0x0; source result=0x7, while the replacement is poison. Both source operations and the replacement retain nsw=true, nuw=false under upstream flag intersection.

**Coverage:** general-width scalar integer pattern using arith.constant; i4 counterexample

**Lean:** [Veir/Passes/ArithCanonicalize/TD010.lean](../Veir/Passes/ArithCanonicalize/TD010.lean); `Veir.ArithCanonicalize.TD010.pattern_not_valid`.

### TD011: SubIRHSSubConstantRHS

[Original code: ArithCanonicalization.td:170–175](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L170-L175).

Fold subi(subi(x,c0),c1) into subi(x,c0+c1).

**Matched:** `arith.subi`, `arith.constant`. **Replacement:** `arith.subi`, `arith.constant`.

**Conditions:** Both constants are ConstantLike integer attributes; overflow flags are merged by bitwise intersection.

**Status: Counterexample.** Lean-checked direct ¬Pattern.Valid witness at i4: x=0x0, c0=0x1, c1=0x7; source result=0x8, while the replacement is poison. Both source operations and the replacement retain nsw=true, nuw=false under upstream flag intersection.

**Coverage:** general-width scalar integer pattern using arith.constant; i4 counterexample

**Lean:** [Veir/Passes/ArithCanonicalize/TD011.lean](../Veir/Passes/ArithCanonicalize/TD011.lean); `Veir.ArithCanonicalize.TD011.pattern_not_valid`.

### TD012: SubIRHSSubConstantLHS

[Original code: ArithCanonicalization.td:178–183](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L178-L183).

Fold subi(subi(c0,x),c1) into subi(c0-c1,x).

**Matched:** `arith.subi`, `arith.constant`. **Replacement:** `arith.subi`, `arith.constant`.

**Conditions:** Both constants are ConstantLike integer attributes; overflow flags are merged by bitwise intersection.

**Status: Counterexample.** Lean-checked direct ¬Pattern.Valid witness at i4: x=0x1, c0=0x0, c1=0x8; source result=0x7, while the replacement is poison. Both source operations and the replacement retain nsw=true, nuw=false under upstream flag intersection.

**Coverage:** general-width scalar integer pattern using arith.constant; i4 counterexample

**Lean:** [Veir/Passes/ArithCanonicalize/TD012.lean](../Veir/Passes/ArithCanonicalize/TD012.lean); `Veir.ArithCanonicalize.TD012.pattern_not_valid`.

### TD013: SubILHSSubConstantRHS

[Original code: ArithCanonicalization.td:186–191](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L186-L191).

Fold subi(c1,subi(x,c0)) into subi(c0+c1,x).

**Matched:** `arith.subi`, `arith.constant`. **Replacement:** `arith.subi`, `arith.constant`.

**Conditions:** Both constants are ConstantLike integer attributes; overflow flags are merged by bitwise intersection.

**Status: Counterexample.** Lean-checked direct ¬Pattern.Valid witness at i4: x=0x1, c0=0x1, c1=0x7; source result=0x7, while the replacement is poison. Both source operations and the replacement retain nsw=true, nuw=false under upstream flag intersection.

**Coverage:** general-width scalar integer pattern using arith.constant; i4 counterexample

**Lean:** [Veir/Passes/ArithCanonicalize/TD013.lean](../Veir/Passes/ArithCanonicalize/TD013.lean); `Veir.ArithCanonicalize.TD013.pattern_not_valid`.

### TD014: SubILHSSubConstantLHS

[Original code: ArithCanonicalization.td:194–199](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L194-L199).

Fold subi(c1,subi(c0,x)) into addi(x,c1-c0).

**Matched:** `arith.subi`, `arith.constant`. **Replacement:** `arith.addi`, `arith.constant`.

**Conditions:** Both constants are ConstantLike integer attributes; overflow flags are merged by bitwise intersection.

**Status: Counterexample.** Lean-checked direct ¬Pattern.Valid witness at i4: x=0x1, c0=0x1, c1=0x8; source result=0x8, while the replacement is poison. Both source operations and the replacement retain nsw=true, nuw=false under upstream flag intersection.

**Coverage:** general-width scalar integer pattern using arith.constant; i4 counterexample

**Lean:** [Veir/Passes/ArithCanonicalize/TD014.lean](../Veir/Passes/ArithCanonicalize/TD014.lean); `Veir.ArithCanonicalize.TD014.pattern_not_valid`.

### TD015: SubISubILHSRHSLHS

[Original code: ArithCanonicalization.td:202–206](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L202-L206).

Rewrite subi(subi(x,y),x) to subi(0,y).

**Matched:** `arith.subi`. **Replacement:** `arith.subi`, `arith.constant`.

**Conditions:** Repeated x must be the same SSA value; zero constant materialization requires scalar or statically shaped type; overflow flags are merged by bitwise intersection.

**Status: Succeeded — proven.** All-width exact Pattern.Valid proof for subi(subi(x,y),x) to subi(0,y), retaining upstream intersected nsw/nuw flags and poison refinement.

**Coverage:** general-width scalar integer Puddle instance of pinned rule; shaped variants outside current scalar model

**Lean:** [Veir/Passes/ArithCanonicalize/TD015.lean](../Veir/Passes/ArithCanonicalize/TD015.lean); `Veir.ArithCanonicalize.TD015.valid`.

### TD016: MulSIExtendedToMulI

[Original code: ArithCanonicalization.td:214–217](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L214-L217).

Replace mulsi_extended(x,y) by muli(x,y) and x for unused high result.

**Matched:** `arith.mulsi_extended`. **Replacement:** `arith.muli`.

**Conditions:** High result must have no uses; any replacement value is permitted for that unused result; muli receives default/no-overflow flags.

**Status: Cannot be implemented with current Puddle support.** The rewrite replaces an unused secondary result by an arbitrary value. Puddle Pattern.Valid requires elementwise refinement of every root result; MatchDecl.Models deliberately forgets use-count facts from inspectOperation. It cannot validate the exact upstream dead-result replacement without a liveness-aware semantic model (and the add/sub arbitrary replacement can have a different type).

**Coverage:** Full upstream rule

### TD017: MulSIExtendedRHSOne

[Original code: ArithCanonicalization.td:227–234](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L227-L234).

Rewrite mulsi_extended(x,1) to x and extsi(cmpi slt,x,0).

**Matched:** `arith.mulsi_extended`, `arith.constant`. **Replacement:** `arith.extsi`, `arith.cmpi`, `arith.constant`.

**Conditions:** RHS must be scalar/splat integer value strictly positive and equal to 1; zero constant for cmpi must be materializable for x type.

**Status: Succeeded — proven.** Pattern.Valid proof of mulsi_extended(x, strictly positive one) to (x, extsi(cmpi slt x, 0)); proves signed high product is the replicated sign bit, including poison.

**Coverage:** scalar integer; all widths greater than one (exact upstream strictly-positive-one guard); both results

**Lean:** [Veir/Passes/ArithCanonicalize/TD017.lean](../Veir/Passes/ArithCanonicalize/TD017.lean); `Veir.ArithCanonicalize.TD017.valid`.

### TD018: MulUIExtendedToMulI

[Original code: ArithCanonicalization.td:242–245](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L242-L245).

Replace mului_extended(x,y) by muli(x,y) and x for unused high result.

**Matched:** `arith.mului_extended`. **Replacement:** `arith.muli`.

**Conditions:** High result must have no uses; any replacement value is permitted for that unused result; muli receives default/no-overflow flags.

**Status: Cannot be implemented with current Puddle support.** The rewrite replaces an unused secondary result by an arbitrary value. Puddle Pattern.Valid requires elementwise refinement of every root result; MatchDecl.Models deliberately forgets use-count facts from inspectOperation. It cannot validate the exact upstream dead-result replacement without a liveness-aware semantic model (and the add/sub arbitrary replacement can have a different type).

**Coverage:** Full upstream rule

### TD019: XOrIXOrIConstant

[Original code: ArithCanonicalization.td:255–261](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L255-L261).

Combine xori(xori(x,c0),c1) into xori(x,c0 xor c1).

**Matched:** `arith.xori`, `arith.constant`. **Replacement:** `arith.xori`, `arith.constant`.

**Conditions:** Both integer attribute types must equal the outer result type.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar integer arith.constant instances. The matcher preserves upstream attribute-type guards; OR allows arbitrary source disjoint flags and creates a default-flag target.

**Coverage:** scalar integer arith.constant instance of pinned upstream pattern

**Lean:** [Veir/Passes/ArithCanonicalize/TD019.lean](../Veir/Passes/ArithCanonicalize/TD019.lean); `Veir.ArithCanonicalize.TD019.pattern_valid`.

### TD020: XOrINotCmpI

[Original code: ArithCanonicalization.td:265–269](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L265-L269).

Rewrite xori(cmpi(pred,a,b),true) to cmpi(invert(pred),a,b).

**Matched:** `arith.xori`, `arith.cmpi`, `arith.constant`. **Replacement:** `arith.cmpi`.

**Conditions:** The xor constant must be scalar i1 constant 1; all CmpI predicates have a defined inverse.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for xor(cmpi(pred,a,b),i1 true) to cmpi(invert(pred),a,b), covering all ten predicates and poison.

**Coverage:** scalar integer operands and arith.constant i1 one subset of ConstantLike matcher

**Lean:** [Veir/Passes/ArithCanonicalize/TD020.lean](../Veir/Passes/ArithCanonicalize/TD020.lean); `Veir.ArithCanonicalize.TD020.valid`.

### TD021: XOrIOfExtUI

[Original code: ArithCanonicalization.td:274–278](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L274-L278).

Push xori through two extui operations: xori(extui(x),extui(y)) -> extui(xori(x,y)).

**Matched:** `arith.xori`, `arith.extui`. **Replacement:** `arith.extui`, `arith.xori`.

**Conditions:** Narrow source types must match; resulting nneg is preserved only when both input extui ops carry nneg.

**Status: Succeeded — proven.** Pattern.Valid proof of xori commuting with two extui operations, including poison; nneg on replacement is conjunction of input nneg flags.

**Coverage:** scalar integer; all valid widening widths; all input nneg flags

**Lean:** [Veir/Passes/ArithCanonicalize/TD021.lean](../Veir/Passes/ArithCanonicalize/TD021.lean); `Veir.ArithCanonicalize.TD021.valid`.

### TD022: XOrIOfExtSI

[Original code: ArithCanonicalization.td:281–283](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L281-L283).

Push xori through two extsi operations.

**Matched:** `arith.xori`, `arith.extsi`. **Replacement:** `arith.extsi`, `arith.xori`.

**Conditions:** Narrow source types must match.

**Status: Succeeded — proven.** Pattern.Valid proof of xori commuting with two extsi operations, including poison; no flags.

**Coverage:** scalar integer; all valid widening widths

**Lean:** [Veir/Passes/ArithCanonicalize/TD022.lean](../Veir/Passes/ArithCanonicalize/TD022.lean); `Veir.ArithCanonicalize.TD022.valid`.

### TD023: CmpIExtSI

[Original code: ArithCanonicalization.td:290–295](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L290-L295).

Push equality/inequality cmpi through matching extsi operands.

**Matched:** `arith.cmpi`, `arith.extsi`. **Replacement:** `arith.cmpi`.

**Conditions:** Narrow source types must match; predicate must be eq or ne.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for eq/ne cmpi through two matching sign extensions, preserving the predicate and poison.

**Coverage:** scalar integer source/result types and signless i1 cmpi result; exact source-width and eq/ne guards

**Lean:** [Veir/Passes/ArithCanonicalize/TD023.lean](../Veir/Passes/ArithCanonicalize/TD023.lean); `Veir.ArithCanonicalize.TD023.valid`.

### TD024: CmpIExtUI

[Original code: ArithCanonicalization.td:298–303](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L298-L303).

Push equality/inequality cmpi through matching extui operands.

**Matched:** `arith.cmpi`, `arith.extui`. **Replacement:** `arith.cmpi`.

**Conditions:** Narrow source types must match; predicate must be eq or ne; nneg flags do not constrain match.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for eq/ne cmpi through two matching zero extensions, preserving the predicate and poison. Independent extui nneg flags are retained on the source and included in the refinement.

**Coverage:** scalar integer source/result types and signless i1 cmpi result; exact source-width and eq/ne guards

**Lean:** [Veir/Passes/ArithCanonicalize/TD024.lean](../Veir/Passes/ArithCanonicalize/TD024.lean); `Veir.ArithCanonicalize.TD024.valid`.

### TD025: SelectNotCond

[Original code: ArithCanonicalization.td:310–313](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L310-L313).

Rewrite select(xori(pred,-1),a,b) to select(pred,b,a).

**Matched:** `arith.select`, `arith.xori`, `arith.constant`. **Replacement:** `arith.select`.

**Conditions:** Xor constant must be scalar/splat all-ones (-1).

**Status: Succeeded — proven.** Pattern.Valid proof of i1 condition complement and arm swap, including poison. Signless i1 all-ones is normalized as integer attribute value +1.

**Coverage:** scalar integer; arbitrary result width and signedness

**Lean:** [Veir/Passes/ArithCanonicalize/TD025.lean](../Veir/Passes/ArithCanonicalize/TD025.lean); `Veir.ArithCanonicalize.TD025.valid`.

### TD026: RedundantSelectTrue

[Original code: ArithCanonicalization.td:316–318](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L316-L318).

Simplify select(pred,select(pred,a,b),c) to select(pred,a,c).

**Matched:** `arith.select`. **Replacement:** `arith.select`.

**Conditions:** Inner and outer conditions must be the same SSA value.

**Status: Succeeded — proven.** Pattern.Valid proof for redundant nested select with the same condition SSA value, including poison and arbitrary arm values.

**Coverage:** scalar integer; arbitrary result width and signedness

**Lean:** [Veir/Passes/ArithCanonicalize/TD026.lean](../Veir/Passes/ArithCanonicalize/TD026.lean); `Veir.ArithCanonicalize.TD026.valid`.

### TD027: RedundantSelectFalse

[Original code: ArithCanonicalization.td:321–323](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L321-L323).

Simplify select(pred,a,select(pred,b,c)) to select(pred,a,c).

**Matched:** `arith.select`. **Replacement:** `arith.select`.

**Conditions:** Inner and outer conditions must be the same SSA value.

**Status: Succeeded — proven.** Pattern.Valid proof for redundant nested select with the same condition SSA value, including poison and arbitrary arm values.

**Coverage:** scalar integer; arbitrary result width and signedness

**Lean:** [Veir/Passes/ArithCanonicalize/TD027.lean](../Veir/Passes/ArithCanonicalize/TD027.lean); `Veir.ArithCanonicalize.TD027.valid`.

### TD028: SelectI1ToNot

[Original code: ArithCanonicalization.td:326–330](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L326-L330).

Rewrite select(pred,false,true) to xori(pred,true).

**Matched:** `arith.select`, `arith.constant`. **Replacement:** `arith.xori`, `arith.constant`.

**Conditions:** True/false arms must be scalar i1 constants 0 and 1, respectively.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar i1 select(false,true) to XOR with literal one; poison-aware.

**Coverage:** general-width scalar integer Puddle instance of pinned TableGen rule (arith.constant subset of ConstantLike only for TD028)

**Lean:** [Veir/Passes/ArithCanonicalize/TD028.lean](../Veir/Passes/ArithCanonicalize/TD028.lean); `Veir.ArithCanonicalize.TD028.pattern_valid`.

### TD029: SelectCmpISltToMinSI

[Original code: ArithCanonicalization.td:349–349](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L349-L349).

Canonicalize select(cmpi slt,a,b) to arith.minsi(a,b) when select arms are a,b arms.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** `arith.minsi`.

**Conditions:** Predicate is exactly slt; compare operands and the corresponding select arms are SSA-identical as required by the base pattern.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar select(cmpi predicate, a, b) to the pinned signed/unsigned min/max operation; exact predicate and arm-order match, including poison.

**Coverage:** general-width scalar integer Puddle instance of pinned TableGen rule

**Lean:** [Veir/Passes/ArithCanonicalize/TD029.lean](../Veir/Passes/ArithCanonicalize/TD029.lean); `Veir.ArithCanonicalize.TD029.pattern_valid`.

### TD030: SelectCmpISleToMinSI

[Original code: ArithCanonicalization.td:350–350](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L350-L350).

Canonicalize select(cmpi sle,a,b) to arith.minsi(a,b) when select arms are a,b arms.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** `arith.minsi`.

**Conditions:** Predicate is exactly sle; compare operands and the corresponding select arms are SSA-identical as required by the base pattern.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar select(cmpi predicate, a, b) to the pinned signed/unsigned min/max operation; exact predicate and arm-order match, including poison.

**Coverage:** general-width scalar integer Puddle instance of pinned TableGen rule

**Lean:** [Veir/Passes/ArithCanonicalize/TD030.lean](../Veir/Passes/ArithCanonicalize/TD030.lean); `Veir.ArithCanonicalize.TD030.pattern_valid`.

### TD031: SelectCmpISgtToMaxSI

[Original code: ArithCanonicalization.td:351–351](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L351-L351).

Canonicalize select(cmpi sgt,a,b) to arith.maxsi(a,b) when select arms are a,b arms.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** `arith.maxsi`.

**Conditions:** Predicate is exactly sgt; compare operands and the corresponding select arms are SSA-identical as required by the base pattern.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar select(cmpi predicate, a, b) to the pinned signed/unsigned min/max operation; exact predicate and arm-order match, including poison.

**Coverage:** general-width scalar integer Puddle instance of pinned TableGen rule

**Lean:** [Veir/Passes/ArithCanonicalize/TD031.lean](../Veir/Passes/ArithCanonicalize/TD031.lean); `Veir.ArithCanonicalize.TD031.pattern_valid`.

### TD032: SelectCmpISgeToMaxSI

[Original code: ArithCanonicalization.td:352–352](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L352-L352).

Canonicalize select(cmpi sge,a,b) to arith.maxsi(a,b) when select arms are a,b arms.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** `arith.maxsi`.

**Conditions:** Predicate is exactly sge; compare operands and the corresponding select arms are SSA-identical as required by the base pattern.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar select(cmpi predicate, a, b) to the pinned signed/unsigned min/max operation; exact predicate and arm-order match, including poison.

**Coverage:** general-width scalar integer Puddle instance of pinned TableGen rule

**Lean:** [Veir/Passes/ArithCanonicalize/TD032.lean](../Veir/Passes/ArithCanonicalize/TD032.lean); `Veir.ArithCanonicalize.TD032.pattern_valid`.

### TD033: SelectCmpIUltToMinUI

[Original code: ArithCanonicalization.td:353–353](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L353-L353).

Canonicalize select(cmpi ult,a,b) to arith.minui(a,b) when select arms are a,b arms.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** `arith.minui`.

**Conditions:** Predicate is exactly ult; compare operands and the corresponding select arms are SSA-identical as required by the base pattern.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar select(cmpi predicate, a, b) to the pinned signed/unsigned min/max operation; exact predicate and arm-order match, including poison.

**Coverage:** general-width scalar integer Puddle instance of pinned TableGen rule

**Lean:** [Veir/Passes/ArithCanonicalize/TD033.lean](../Veir/Passes/ArithCanonicalize/TD033.lean); `Veir.ArithCanonicalize.TD033.pattern_valid`.

### TD034: SelectCmpIUleToMinUI

[Original code: ArithCanonicalization.td:354–354](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L354-L354).

Canonicalize select(cmpi ule,a,b) to arith.minui(a,b) when select arms are a,b arms.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** `arith.minui`.

**Conditions:** Predicate is exactly ule; compare operands and the corresponding select arms are SSA-identical as required by the base pattern.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar select(cmpi predicate, a, b) to the pinned signed/unsigned min/max operation; exact predicate and arm-order match, including poison.

**Coverage:** general-width scalar integer Puddle instance of pinned TableGen rule

**Lean:** [Veir/Passes/ArithCanonicalize/TD034.lean](../Veir/Passes/ArithCanonicalize/TD034.lean); `Veir.ArithCanonicalize.TD034.pattern_valid`.

### TD035: SelectCmpIUgtToMaxUI

[Original code: ArithCanonicalization.td:355–355](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L355-L355).

Canonicalize select(cmpi ugt,a,b) to arith.maxui(a,b) when select arms are a,b arms.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** `arith.maxui`.

**Conditions:** Predicate is exactly ugt; compare operands and the corresponding select arms are SSA-identical as required by the base pattern.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar select(cmpi predicate, a, b) to the pinned signed/unsigned min/max operation; exact predicate and arm-order match, including poison.

**Coverage:** general-width scalar integer Puddle instance of pinned TableGen rule

**Lean:** [Veir/Passes/ArithCanonicalize/TD035.lean](../Veir/Passes/ArithCanonicalize/TD035.lean); `Veir.ArithCanonicalize.TD035.pattern_valid`.

### TD036: SelectCmpIUgeToMaxUI

[Original code: ArithCanonicalization.td:356–356](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L356-L356).

Canonicalize select(cmpi uge,a,b) to arith.maxui(a,b) when select arms are a,b arms.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** `arith.maxui`.

**Conditions:** Predicate is exactly uge; compare operands and the corresponding select arms are SSA-identical as required by the base pattern.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar select(cmpi predicate, a, b) to the pinned signed/unsigned min/max operation; exact predicate and arm-order match, including poison.

**Coverage:** general-width scalar integer Puddle instance of pinned TableGen rule

**Lean:** [Veir/Passes/ArithCanonicalize/TD036.lean](../Veir/Passes/ArithCanonicalize/TD036.lean); `Veir.ArithCanonicalize.TD036.pattern_valid`.

### TD037: SelectCmpISltToMaxSI

[Original code: ArithCanonicalization.td:359–359](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L359-L359).

Canonicalize select(cmpi slt,a,b) to arith.maxsi(a,b) when select arms are b,a arms.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** `arith.maxsi`.

**Conditions:** Predicate is exactly slt; compare operands and the corresponding select arms are SSA-identical as required by the base pattern.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar select(cmpi predicate, a, b) to the pinned signed/unsigned min/max operation; exact predicate and arm-order match, including poison.

**Coverage:** general-width scalar integer Puddle instance of pinned TableGen rule

**Lean:** [Veir/Passes/ArithCanonicalize/TD037.lean](../Veir/Passes/ArithCanonicalize/TD037.lean); `Veir.ArithCanonicalize.TD037.pattern_valid`.

### TD038: SelectCmpISleToMaxSI

[Original code: ArithCanonicalization.td:360–360](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L360-L360).

Canonicalize select(cmpi sle,a,b) to arith.maxsi(a,b) when select arms are b,a arms.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** `arith.maxsi`.

**Conditions:** Predicate is exactly sle; compare operands and the corresponding select arms are SSA-identical as required by the base pattern.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar select(cmpi predicate, a, b) to the pinned signed/unsigned min/max operation; exact predicate and arm-order match, including poison.

**Coverage:** general-width scalar integer Puddle instance of pinned TableGen rule

**Lean:** [Veir/Passes/ArithCanonicalize/TD038.lean](../Veir/Passes/ArithCanonicalize/TD038.lean); `Veir.ArithCanonicalize.TD038.pattern_valid`.

### TD039: SelectCmpISgtToMinSI

[Original code: ArithCanonicalization.td:361–361](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L361-L361).

Canonicalize select(cmpi sgt,a,b) to arith.minsi(a,b) when select arms are b,a arms.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** `arith.minsi`.

**Conditions:** Predicate is exactly sgt; compare operands and the corresponding select arms are SSA-identical as required by the base pattern.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar select(cmpi predicate, a, b) to the pinned signed/unsigned min/max operation; exact predicate and arm-order match, including poison.

**Coverage:** general-width scalar integer Puddle instance of pinned TableGen rule

**Lean:** [Veir/Passes/ArithCanonicalize/TD039.lean](../Veir/Passes/ArithCanonicalize/TD039.lean); `Veir.ArithCanonicalize.TD039.pattern_valid`.

### TD040: SelectCmpISgeToMinSI

[Original code: ArithCanonicalization.td:362–362](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L362-L362).

Canonicalize select(cmpi sge,a,b) to arith.minsi(a,b) when select arms are b,a arms.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** `arith.minsi`.

**Conditions:** Predicate is exactly sge; compare operands and the corresponding select arms are SSA-identical as required by the base pattern.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar select(cmpi predicate, a, b) to the pinned signed/unsigned min/max operation; exact predicate and arm-order match, including poison.

**Coverage:** general-width scalar integer Puddle instance of pinned TableGen rule

**Lean:** [Veir/Passes/ArithCanonicalize/TD040.lean](../Veir/Passes/ArithCanonicalize/TD040.lean); `Veir.ArithCanonicalize.TD040.pattern_valid`.

### TD041: SelectCmpIUltToMaxUI

[Original code: ArithCanonicalization.td:363–363](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L363-L363).

Canonicalize select(cmpi ult,a,b) to arith.maxui(a,b) when select arms are b,a arms.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** `arith.maxui`.

**Conditions:** Predicate is exactly ult; compare operands and the corresponding select arms are SSA-identical as required by the base pattern.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar select(cmpi predicate, a, b) to the pinned signed/unsigned min/max operation; exact predicate and arm-order match, including poison.

**Coverage:** general-width scalar integer Puddle instance of pinned TableGen rule

**Lean:** [Veir/Passes/ArithCanonicalize/TD041.lean](../Veir/Passes/ArithCanonicalize/TD041.lean); `Veir.ArithCanonicalize.TD041.pattern_valid`.

### TD042: SelectCmpIUleToMaxUI

[Original code: ArithCanonicalization.td:364–364](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L364-L364).

Canonicalize select(cmpi ule,a,b) to arith.maxui(a,b) when select arms are b,a arms.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** `arith.maxui`.

**Conditions:** Predicate is exactly ule; compare operands and the corresponding select arms are SSA-identical as required by the base pattern.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar select(cmpi predicate, a, b) to the pinned signed/unsigned min/max operation; exact predicate and arm-order match, including poison.

**Coverage:** general-width scalar integer Puddle instance of pinned TableGen rule

**Lean:** [Veir/Passes/ArithCanonicalize/TD042.lean](../Veir/Passes/ArithCanonicalize/TD042.lean); `Veir.ArithCanonicalize.TD042.pattern_valid`.

### TD043: SelectCmpIUgtToMinUI

[Original code: ArithCanonicalization.td:365–365](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L365-L365).

Canonicalize select(cmpi ugt,a,b) to arith.minui(a,b) when select arms are b,a arms.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** `arith.minui`.

**Conditions:** Predicate is exactly ugt; compare operands and the corresponding select arms are SSA-identical as required by the base pattern.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar select(cmpi predicate, a, b) to the pinned signed/unsigned min/max operation; exact predicate and arm-order match, including poison.

**Coverage:** general-width scalar integer Puddle instance of pinned TableGen rule

**Lean:** [Veir/Passes/ArithCanonicalize/TD043.lean](../Veir/Passes/ArithCanonicalize/TD043.lean); `Veir.ArithCanonicalize.TD043.pattern_valid`.

### TD044: SelectCmpIUgeToMinUI

[Original code: ArithCanonicalization.td:366–366](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L366-L366).

Canonicalize select(cmpi uge,a,b) to arith.minui(a,b) when select arms are b,a arms.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** `arith.minui`.

**Conditions:** Predicate is exactly uge; compare operands and the corresponding select arms are SSA-identical as required by the base pattern.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar select(cmpi predicate, a, b) to the pinned signed/unsigned min/max operation; exact predicate and arm-order match, including poison.

**Coverage:** general-width scalar integer Puddle instance of pinned TableGen rule

**Lean:** [Veir/Passes/ArithCanonicalize/TD044.lean](../Veir/Passes/ArithCanonicalize/TD044.lean); `Veir.ArithCanonicalize.TD044.pattern_valid`.

### TD045: IndexCastOfExtSI

[Original code: ArithCanonicalization.td:373–374](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L373-L374).

Remove redundant sign extension under index_cast.

**Matched:** `arith.index_cast`, `arith.extsi`. **Replacement:** `arith.index_cast`.

**Conditions:** No additional pattern constraint; replacement must satisfy op verifier/type rules.

**Status: Cannot be implemented with current Puddle support.** VeIR has no arith.index_cast/index_castui opcode or target-dependent index RuntimeValue/conformance/interpreter. The rewrite cannot be stated with its upstream source and destination semantics in current Puddle.

**Coverage:** Full upstream rule

### TD046: IndexCastUIOfExtUI

[Original code: ArithCanonicalization.td:381–383](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L381-L383).

Remove nested zero extension under index_castui.

**Matched:** `arith.index_castui`, `arith.extui`. **Replacement:** `arith.index_castui`.

**Conditions:** No additional pattern constraint; outer index_castui retains inner extui nneg attribute.

**Status: Cannot be implemented with current Puddle support.** VeIR has no arith.index_cast/index_castui opcode or target-dependent index RuntimeValue/conformance/interpreter. The rewrite cannot be stated with its upstream source and destination semantics in current Puddle.

**Coverage:** Full upstream rule

### TD047: BitcastOfBitcast

[Original code: ArithCanonicalization.td:391–392](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L391-L392).

Collapse nested bitcast.

**Matched:** `arith.bitcast`. **Replacement:** `arith.bitcast`.

**Conditions:** Types must satisfy bitcast verifier constraints.

**Status: Cannot be implemented with current Puddle support.** VeIR has no arith.bitcast opcode or Arith float/integer bitcast interpretation. LLVM bitcast supports a restricted scalar int/byte/pointer subset, which does not provide the upstream Arith floating and shaped bitcast semantics.

**Coverage:** Full upstream rule

### TD048: ExtSIOfExtUI

[Original code: ArithCanonicalization.td:399–401](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L399-L401).

Replace extsi(extui(x)) with extui(x).

**Matched:** `arith.extsi`, `arith.extui`. **Replacement:** `arith.extui`.

**Conditions:** No additional pattern constraint; retain extui nneg attribute.

**Status: Succeeded — proven.** Pattern.Valid proof that extsi(extui(x)) equals a wider extui(x), retaining the inner nneg flag and poison behavior.

**Coverage:** scalar integer; all strictly increasing source, middle, and result widths; either nneg value

**Lean:** [Veir/Passes/ArithCanonicalize/TD048.lean](../Veir/Passes/ArithCanonicalize/TD048.lean); `Veir.ArithCanonicalize.TD048.valid`.

### TD049: AndIAndIConstant

[Original code: ArithCanonicalization.td:408–414](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L408-L414).

Combine andi(andi(x,c0),c1) into andi(x,c0 & c1).

**Matched:** `arith.andi`, `arith.constant`. **Replacement:** `arith.andi`, `arith.constant`.

**Conditions:** Both integer attribute types must equal the outer result type.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar integer arith.constant instances. The matcher preserves upstream attribute-type guards; OR allows arbitrary source disjoint flags and creates a default-flag target.

**Coverage:** scalar integer arith.constant instance of pinned upstream pattern

**Lean:** [Veir/Passes/ArithCanonicalize/TD049.lean](../Veir/Passes/ArithCanonicalize/TD049.lean); `Veir.ArithCanonicalize.TD049.pattern_valid`.

### TD050: AndOfExtUI

[Original code: ArithCanonicalization.td:419–423](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L419-L423).

Push andi through two extui operations.

**Matched:** `arith.andi`, `arith.extui`. **Replacement:** `arith.extui`, `arith.andi`.

**Conditions:** Narrow source types must match; resulting nneg is true if either input extui has nneg.

**Status: Succeeded — proven.** Pattern.Valid proof of andi commuting with two extui operations, including poison; nneg on replacement is disjunction of input nneg flags.

**Coverage:** scalar integer; all valid widening widths; all input nneg flags

**Lean:** [Veir/Passes/ArithCanonicalize/TD050.lean](../Veir/Passes/ArithCanonicalize/TD050.lean); `Veir.ArithCanonicalize.TD050.valid`.

### TD051: AndOfExtSI

[Original code: ArithCanonicalization.td:426–429](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L426-L429).

Push andi through two extsi operations.

**Matched:** `arith.andi`, `arith.extsi`. **Replacement:** `arith.extsi`, `arith.andi`.

**Conditions:** Narrow source types must match.

**Status: Succeeded — proven.** Pattern.Valid proof of andi commuting with two extsi operations, including poison; no flags.

**Coverage:** scalar integer; all valid widening widths

**Lean:** [Veir/Passes/ArithCanonicalize/TD051.lean](../Veir/Passes/ArithCanonicalize/TD051.lean); `Veir.ArithCanonicalize.TD051.valid`.

### TD052: OrIOrIConstant

[Original code: ArithCanonicalization.td:436–442](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L436-L442).

Combine ori(ori(x,c0),c1) into ori(x,c0 | c1).

**Matched:** `arith.ori`, `arith.constant`. **Replacement:** `arith.ori`, `arith.constant`.

**Conditions:** Both integer attribute types must equal the outer result type.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for scalar integer arith.constant instances. The matcher preserves upstream attribute-type guards; OR allows arbitrary source disjoint flags and creates a default-flag target.

**Coverage:** scalar integer arith.constant instance of pinned upstream pattern

**Lean:** [Veir/Passes/ArithCanonicalize/TD052.lean](../Veir/Passes/ArithCanonicalize/TD052.lean); `Veir.ArithCanonicalize.TD052.pattern_valid`.

### TD053: OrOfExtUI

[Original code: ArithCanonicalization.td:447–451](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L447-L451).

Push ori through two extui operations.

**Matched:** `arith.ori`, `arith.extui`. **Replacement:** `arith.extui`, `arith.ori`.

**Conditions:** Narrow source types must match; resulting nneg is preserved only when both input extui ops carry nneg.

**Status: Succeeded — proven.** Pattern.Valid proof of ori commuting with two extui operations, including poison from optional disjoint on the source OR; target OR has upstream default disjoint=false; nneg on replacement is conjunction of both input nneg flags.

**Coverage:** scalar integer; all valid widening widths; all input nneg and source disjoint flags

**Lean:** [Veir/Passes/ArithCanonicalize/TD053.lean](../Veir/Passes/ArithCanonicalize/TD053.lean); `Veir.ArithCanonicalize.TD053.valid`.

### TD054: OrOfExtSI

[Original code: ArithCanonicalization.td:454–457](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L454-L457).

Push ori through two extsi operations.

**Matched:** `arith.ori`, `arith.extsi`. **Replacement:** `arith.extsi`, `arith.ori`.

**Conditions:** Narrow source types must match.

**Status: Succeeded — proven.** Pattern.Valid proof of ori commuting with two extsi operations, including poison from optional disjoint on the source OR; target OR has upstream default disjoint=false; no extension flags.

**Coverage:** scalar integer; all valid widening widths; optional source disjoint flag

**Lean:** [Veir/Passes/ArithCanonicalize/TD054.lean](../Veir/Passes/ArithCanonicalize/TD054.lean); `Veir.ArithCanonicalize.TD054.valid`.

### TD055: TruncIExtSIToExtSI

[Original code: ArithCanonicalization.td:475–479](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L475-L479).

Cancel truncation of an extension when the trunc result remains wider than the original source.

**Matched:** `arith.trunci`, `arith.extsi`. **Replacement:** `arith.extsi`.

**Conditions:** Extension result width > trunc result width > source width; preserve semantics at widths above zero.

**Status: Succeeded — proven.** Pattern.Valid proof of trunci(extsi(x)) to an extsi at the intermediate result width. All nsw/nuw truncation flags are modeled; the source may become poison while the replacement remains defined.

**Coverage:** scalar integer; all source < result < extension widths; all truncation flags

**Lean:** [Veir/Passes/ArithCanonicalize/TD055.lean](../Veir/Passes/ArithCanonicalize/TD055.lean); `Veir.ArithCanonicalize.TD055.valid`.

### TD056: TruncIExtUIToExtUI

[Original code: ArithCanonicalization.td:482–486](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L482-L486).

Cancel truncation of an extension when the trunc result remains wider than the original source.

**Matched:** `arith.trunci`, `arith.extui`. **Replacement:** `arith.extui`.

**Conditions:** Extension result width > trunc result width > source width; preserve extui nneg.

**Status: Succeeded — proven.** Pattern.Valid proof of trunci(extui(x)) to an extui at the intermediate result width, preserving nneg and modeling all nsw/nuw truncation flags.

**Coverage:** scalar integer; all source < result < extension widths; all nneg/nsw/nuw flags

**Lean:** [Veir/Passes/ArithCanonicalize/TD056.lean](../Veir/Passes/ArithCanonicalize/TD056.lean); `Veir.ArithCanonicalize.TD056.valid`.

### TD057: TruncIShrSIToTrunciShrUI

[Original code: ArithCanonicalization.td:489–493](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L489-L493).

Rewrite trunci(shrsi(x,c)) to trunci(shrui(x,c)) when truncation removes exactly the shifted-off sign bits.

**Matched:** `arith.trunci`, `arith.shrsi`, `arith.constant`. **Replacement:** `arith.trunci`, `arith.shrui`, `arith.constant`.

**Conditions:** Shift amount must be scalar/splat integer and equal input width minus trunc result width; the typed shift attribute is retained; exact flag and trunc overflow attribute are preserved.

**Status: Counterexample.** Direct Lean proof that arithmetic-to-logical shift rewrite violates Pattern.Valid with retained nsw: source i8 -4 >>s 4 → i4 -1 is defined; logical shift gives i8 15 then i4 nsw poison.

**Coverage:** general scalar integer Puddle pattern; concrete i8→i4 witness

**Lean:** [Veir/Passes/ArithCanonicalize/TD057.lean](../Veir/Passes/ArithCanonicalize/TD057.lean); `Veir.ArithCanonicalize.TD057.pattern_not_valid`.

### TD058: TruncFSIToFPToSIToFP

[Original code: ArithCanonicalization.td:500–503](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L500-L503).

Cancel truncf(sitofp(x)) when truncf uses default rounding mode.

**Matched:** `arith.truncf`, `arith.sitofp`. **Replacement:** `arith.sitofp`.

**Conditions:** Outer truncf rounding mode must be absent/null; floating-point fast-math flags are not checked by this pattern.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks the matched Arith floating-point opcodes and their interpreter semantics (including exact APFloat formats, rounding modes, NaN/signed-zero behavior and fast-math). Existing RuntimeValue.float alone does not supply these semantics; the LLVM interpreter also leaves floating arithmetic unsupported. A Puddle Valid proof using failed interpretation would be vacuous, so none is claimed.

**Coverage:** Full upstream rule

### TD059: TruncFUIToFPToUIToFP

[Original code: ArithCanonicalization.td:506–509](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L506-L509).

Cancel truncf(uitofp(x)) when truncf uses default rounding mode.

**Matched:** `arith.truncf`, `arith.uitofp`. **Replacement:** `arith.uitofp`.

**Conditions:** Outer truncf rounding mode must be absent/null; preserve uitofp nneg; floating-point fast-math flags are not checked by this pattern.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks the matched Arith floating-point opcodes and their interpreter semantics (including exact APFloat formats, rounding modes, NaN/signed-zero behavior and fast-math). Existing RuntimeValue.float alone does not supply these semantics; the LLVM interpreter also leaves floating arithmetic unsupported. A Puddle Valid proof using failed interpretation would be vacuous, so none is claimed.

**Coverage:** Full upstream rule

### TD060: SIToFPOfExtSI

[Original code: ArithCanonicalization.td:516–518](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L516-L518).

Remove redundant sign extension before sitofp.

**Matched:** `arith.sitofp`, `arith.extsi`. **Replacement:** `arith.sitofp`.

**Conditions:** No additional pattern constraint.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks the matched Arith floating-point opcodes and their interpreter semantics (including exact APFloat formats, rounding modes, NaN/signed-zero behavior and fast-math). Existing RuntimeValue.float alone does not supply these semantics; the LLVM interpreter also leaves floating arithmetic unsupported. A Puddle Valid proof using failed interpretation would be vacuous, so none is claimed.

**Coverage:** Full upstream rule

### TD061: SIToFPOfExtUI

[Original code: ArithCanonicalization.td:521–523](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L521-L523).

Rewrite sitofp(extui(x)) as uitofp(x).

**Matched:** `arith.sitofp`, `arith.extui`. **Replacement:** `arith.uitofp`.

**Conditions:** Preserve extui nneg on replacement uitofp.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks the matched Arith floating-point opcodes and their interpreter semantics (including exact APFloat formats, rounding modes, NaN/signed-zero behavior and fast-math). Existing RuntimeValue.float alone does not supply these semantics; the LLVM interpreter also leaves floating arithmetic unsupported. A Puddle Valid proof using failed interpretation would be vacuous, so none is claimed.

**Coverage:** Full upstream rule

### TD062: UIToFPOfExtUI

[Original code: ArithCanonicalization.td:530–532](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L530-L532).

Remove redundant extui before uitofp.

**Matched:** `arith.uitofp`, `arith.extui`. **Replacement:** `arith.uitofp`.

**Conditions:** Preserve extui nneg on replacement uitofp.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks the matched Arith floating-point opcodes and their interpreter semantics (including exact APFloat formats, rounding modes, NaN/signed-zero behavior and fast-math). Existing RuntimeValue.float alone does not supply these semantics; the LLVM interpreter also leaves floating arithmetic unsupported. A Puddle Valid proof using failed interpretation would be vacuous, so none is claimed.

**Coverage:** Full upstream rule

### TD063: AddFOfNegFLhs

[Original code: ArithCanonicalization.td:544–546](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L544-L546).

Rewrite addf(negf(x),y) to subf(y,x).

**Matched:** `arith.addf`, `arith.negf`. **Replacement:** `arith.subf`.

**Conditions:** Negf fast-math flags are ignored; addf fast-math flags and rounding mode are preserved on subf. Source comment claims bit identity for any rounding mode.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks the matched Arith floating-point opcodes and their interpreter semantics (including exact APFloat formats, rounding modes, NaN/signed-zero behavior and fast-math). Existing RuntimeValue.float alone does not supply these semantics; the LLVM interpreter also leaves floating arithmetic unsupported. A Puddle Valid proof using failed interpretation would be vacuous, so none is claimed.

**Coverage:** Full upstream rule

### TD064: AddFOfNegFRhs

[Original code: ArithCanonicalization.td:548–550](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L548-L550).

Rewrite addf(x,negf(y)) to subf(x,y).

**Matched:** `arith.addf`, `arith.negf`. **Replacement:** `arith.subf`.

**Conditions:** Negf fast-math flags are ignored; addf fast-math flags and rounding mode are preserved on subf. Source comment claims bit identity for any rounding mode.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks the matched Arith floating-point opcodes and their interpreter semantics (including exact APFloat formats, rounding modes, NaN/signed-zero behavior and fast-math). Existing RuntimeValue.float alone does not supply these semantics; the LLVM interpreter also leaves floating arithmetic unsupported. A Puddle Valid proof using failed interpretation would be vacuous, so none is claimed.

**Coverage:** Full upstream rule

### TD065: SubFOfNegZero

[Original code: ArithCanonicalization.td:564–568](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L564-L568).

Rewrite subf(-0.0,x) to negf(x).

**Matched:** `arith.subf`, `arith.constant`. **Replacement:** `arith.negf`.

**Conditions:** LHS must match scalar/splat negative-zero float; subf rounding mode must be absent/null (source TODO says custom rounding mode safety unverified); subf fast-math flags are transferred.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks the matched Arith floating-point opcodes and their interpreter semantics (including exact APFloat formats, rounding modes, NaN/signed-zero behavior and fast-math). Existing RuntimeValue.float alone does not supply these semantics; the LLVM interpreter also leaves floating arithmetic unsupported. A Puddle Valid proof using failed interpretation would be vacuous, so none is claimed.

**Coverage:** Full upstream rule

### TD066: MulFOfNegF

[Original code: ArithCanonicalization.td:577–581](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L577-L581).

Rewrite mulf(negf(x),negf(y)) to mulf(x,y).

**Matched:** `arith.mulf`, `arith.negf`. **Replacement:** `arith.mulf`.

**Conditions:** x and y types must match; outer mulf rounding mode must be absent/null; preserve outer fast-math flags. Source TODO says custom-rounding safety unverified.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks the matched Arith floating-point opcodes and their interpreter semantics (including exact APFloat formats, rounding modes, NaN/signed-zero behavior and fast-math). Existing RuntimeValue.float alone does not supply these semantics; the LLVM interpreter also leaves floating arithmetic unsupported. A Puddle Valid proof using failed interpretation would be vacuous, so none is claimed.

**Coverage:** Full upstream rule

### TD067: DivFOfNegF

[Original code: ArithCanonicalization.td:590–594](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithCanonicalization.td#L590-L594).

Rewrite divf(negf(x),negf(y)) to divf(x,y).

**Matched:** `arith.divf`, `arith.negf`. **Replacement:** `arith.divf`.

**Conditions:** x and y types must match; outer divf rounding mode must be absent/null; preserve outer fast-math flags. Source TODO says custom-rounding safety unverified.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks the matched Arith floating-point opcodes and their interpreter semantics (including exact APFloat formats, rounding modes, NaN/signed-zero behavior and fast-math). Existing RuntimeValue.float alone does not supply these semantics; the LLVM interpreter also leaves floating arithmetic unsupported. A Puddle Valid proof using failed interpretation would be vacuous, so none is claimed.

**Coverage:** Full upstream rule

### CP001: NarrowExtremum<TruncI, extsi, maxsi>

[Original code: ArithOps.cpp:1369–1427](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1369-L1427).

trunci(extremum(ext(x),ext(y))) -> extremum(x,y); concrete extremum is arith.maxsi.

**Matched:** `arith.trunci`, `arith.maxsi`, `arith.extsi`. **Replacement:** `arith.maxsi`.

**Conditions:** Extremum has one use; both extremum operands are produced by the stated extension; both extension sources have the trunci result type.

**Status: Succeeded — proven.** Pattern.Valid proof of trunci(maxsi(extsi(x), extsi(y))) to maxsi(x,y), with the upstream one-use matcher guard via inspectOperation and all poison behavior.

**Coverage:** scalar integer; all valid widening widths; arbitrary trunc nsw/nuw flags

**Lean:** [Veir/Passes/ArithCanonicalize/CP001.lean](../Veir/Passes/ArithCanonicalize/CP001.lean); `Veir.ArithCanonicalize.CP001.valid`.

### CP002: NarrowExtremum<TruncI, extsi, minsi>

[Original code: ArithOps.cpp:1369–1427](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1369-L1427).

trunci(extremum(ext(x),ext(y))) -> extremum(x,y); concrete extremum is arith.minsi.

**Matched:** `arith.trunci`, `arith.minsi`, `arith.extsi`. **Replacement:** `arith.minsi`.

**Conditions:** Extremum has one use; both extremum operands are produced by the stated extension; both extension sources have the trunci result type.

**Status: Succeeded — proven.** Pattern.Valid proof of trunci(minsi(extsi(x), extsi(y))) to minsi(x,y), with the upstream one-use matcher guard via inspectOperation and all poison behavior.

**Coverage:** scalar integer; all valid widening widths; arbitrary trunc nsw/nuw flags

**Lean:** [Veir/Passes/ArithCanonicalize/CP002.lean](../Veir/Passes/ArithCanonicalize/CP002.lean); `Veir.ArithCanonicalize.CP002.valid`.

### CP003: NarrowExtremum<TruncI, extui, maxui>

[Original code: ArithOps.cpp:1369–1427](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1369-L1427).

trunci(extremum(ext(x),ext(y))) -> extremum(x,y); concrete extremum is arith.maxui.

**Matched:** `arith.trunci`, `arith.maxui`, `arith.extui`. **Replacement:** `arith.maxui`.

**Conditions:** Extremum has one use; both extremum operands are produced by the stated extension; both extension sources have the trunci result type.

**Status: Succeeded — proven.** Pattern.Valid proof of trunci(maxui(extui(x), extui(y))) to maxui(x,y), with the upstream one-use matcher guard via inspectOperation and all poison behavior.

**Coverage:** scalar integer; all valid widening widths; arbitrary trunc nsw/nuw and extui nneg flags

**Lean:** [Veir/Passes/ArithCanonicalize/CP003.lean](../Veir/Passes/ArithCanonicalize/CP003.lean); `Veir.ArithCanonicalize.CP003.valid`.

### CP004: NarrowExtremum<TruncI, extui, minui>

[Original code: ArithOps.cpp:1369–1427](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1369-L1427).

trunci(extremum(ext(x),ext(y))) -> extremum(x,y); concrete extremum is arith.minui.

**Matched:** `arith.trunci`, `arith.minui`, `arith.extui`. **Replacement:** `arith.minui`.

**Conditions:** Extremum has one use; both extremum operands are produced by the stated extension; both extension sources have the trunci result type.

**Status: Succeeded — proven.** Pattern.Valid proof of trunci(minui(extui(x), extui(y))) to minui(x,y), with the upstream one-use matcher guard via inspectOperation and all poison behavior.

**Coverage:** scalar integer; all valid widening widths; arbitrary trunc nsw/nuw and extui nneg flags

**Lean:** [Veir/Passes/ArithCanonicalize/CP004.lean](../Veir/Passes/ArithCanonicalize/CP004.lean); `Veir.ArithCanonicalize.CP004.valid`.

### CP005: NarrowExtremum<extf, maximumf>

[Original code: ArithOps.cpp:1369–1427](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1369-L1427).

truncf(maximumf(extf(x),extf(y))) -> maximumf(x,y).

**Matched:** `arith.truncf`, `arith.extf`, `arith.maximumf`. **Replacement:** `arith.maximumf`.

**Conditions:** Extremum has one use; both extension inputs equal trunc result type; source FP semantics widen losslessly including signed zero and signaling-NaN behavior; `nnan` permits ignoring NaN representation differences.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.extf, arith.maximumf, arith.truncf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### CP006: NarrowExtremum<extf, maxnumf>

[Original code: ArithOps.cpp:1369–1427](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1369-L1427).

truncf(maxnumf(extf(x),extf(y))) -> maxnumf(x,y).

**Matched:** `arith.truncf`, `arith.extf`, `arith.maxnumf`. **Replacement:** `arith.maxnumf`.

**Conditions:** Extremum has one use; both extension inputs equal trunc result type; source FP semantics widen losslessly including signed zero and signaling-NaN behavior; `nnan` permits ignoring NaN representation differences.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.extf, arith.maxnumf, arith.truncf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### CP007: NarrowExtremum<extf, maximumnumf>

[Original code: ArithOps.cpp:1369–1427](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1369-L1427).

truncf(maximumnumf(extf(x),extf(y))) -> maximumnumf(x,y).

**Matched:** `arith.truncf`, `arith.extf`, `arith.maximumnumf`. **Replacement:** `arith.maximumnumf`.

**Conditions:** Extremum has one use; both extension inputs equal trunc result type; source FP semantics widen losslessly including signed zero and signaling-NaN behavior; `nnan` permits ignoring NaN representation differences.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.extf, arith.maximumnumf, arith.truncf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### CP008: NarrowExtremum<extf, minimumf>

[Original code: ArithOps.cpp:1369–1427](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1369-L1427).

truncf(minimumf(extf(x),extf(y))) -> minimumf(x,y).

**Matched:** `arith.truncf`, `arith.extf`, `arith.minimumf`. **Replacement:** `arith.minimumf`.

**Conditions:** Extremum has one use; both extension inputs equal trunc result type; source FP semantics widen losslessly including signed zero and signaling-NaN behavior; `nnan` permits ignoring NaN representation differences.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.extf, arith.minimumf, arith.truncf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### CP009: NarrowExtremum<extf, minnumf>

[Original code: ArithOps.cpp:1369–1427](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1369-L1427).

truncf(minnumf(extf(x),extf(y))) -> minnumf(x,y).

**Matched:** `arith.truncf`, `arith.extf`, `arith.minnumf`. **Replacement:** `arith.minnumf`.

**Conditions:** Extremum has one use; both extension inputs equal trunc result type; source FP semantics widen losslessly including signed zero and signaling-NaN behavior; `nnan` permits ignoring NaN representation differences.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.extf, arith.minnumf, arith.truncf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### CP010: NarrowExtremum<extf, minimumnumf>

[Original code: ArithOps.cpp:1369–1427](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1369-L1427).

truncf(minimumnumf(extf(x),extf(y))) -> minimumnumf(x,y).

**Matched:** `arith.truncf`, `arith.extf`, `arith.minimumnumf`. **Replacement:** `arith.minimumnumf`.

**Conditions:** Extremum has one use; both extension inputs equal trunc result type; source FP semantics widen losslessly including signed zero and signaling-NaN behavior; `nnan` permits ignoring NaN representation differences.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.extf, arith.minimumnumf, arith.truncf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### CP011: CmpFIntToFPConst

[Original code: ArithOps.cpp:2734–3017](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2734-L3017).

cmpf(pred, sitofp(x)|uitofp(x), C) becomes an integer comparison with truncTowardZero(C), or an i1 constant. ORD -> true and UNO -> false. Above the integer maximum, ne/lt/le -> true and eq/gt/ge -> false; below the minimum, ne/gt/ge -> true and eq/lt/le -> false. For a fractional C, eq -> false and ne -> true; signed comparisons use < ceil(C) or <= floor(C), and > floor(C) or >= ceil(C), implemented by adjusting the predicate around truncTowardZero(C). Unsigned negative thresholds collapse to constants. For integral C (including -0.0), retain the equivalent signed/unsigned integer predicate. Ordered/unordered variants share the integer predicate because neither input is NaN under the guards.

**Matched:** `arith.cmpf`, `arith.sitofp`, `arith.uitofp`, `arith.constant`. **Replacement:** `arith.cmpi`, `arith.constant`.

**Conditions:** Scalar RHS is a non-NaN FloatAttr with positive mantissa width m; LHS is sitofp/uitofp of an integer of width w (value bits v=w-1 signed, w unsigned). If w>m, reject finite thresholds with m <= ilogb(C) <= v, and reject infinite thresholds if the largest finite FP exponent is < v. Then apply range checks against FP-converted integer extrema. In-range C must convert toward zero without opInvalidOp. The implementation handles ORD/UNO and the twelve relational predicates; convertToIntegerPredicate has an unreachable default for other predicates.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.cmpf, arith.sitofp, arith.uitofp. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### CP012: SelectToExtUI1

[Original code: ArithOps.cpp:3029–3060](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3029-L3060).

select(cond, 1, 0) -> extui(cond).

**Matched:** `arith.select`, `arith.constant`. **Replacement:** `arith.extui`.

**Conditions:** Result type is integer and not i1; true/false arms match the stated constants.

**Status: Succeeded — proven.** Pattern.Valid proof of select(cond, 1, 0) to extui(cond), with signless-i1 constant normalization and poison semantics.

**Coverage:** scalar integer; all result widths greater than one; arbitrary integer signedness

**Lean:** [Veir/Passes/ArithCanonicalize/CP012.lean](../Veir/Passes/ArithCanonicalize/CP012.lean); `Veir.ArithCanonicalize.CP012.valid`.

### CP013: SelectToExtUI2

[Original code: ArithOps.cpp:3029–3060](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3029-L3060).

select(cond, 0, 1) -> extui(xori(cond, 1)).

**Matched:** `arith.select`, `arith.constant`. **Replacement:** `arith.extui`, `arith.xori`, `arith.constant`.

**Conditions:** Result type is integer and not i1; true/false arms match the stated constants.

**Status: Succeeded — proven.** Pattern.Valid proof of select(cond, 0, 1) to extui(xori(cond, 1)), with signless-i1 constant normalization and poison semantics.

**Coverage:** scalar integer; all result widths greater than one; arbitrary integer signedness

**Lean:** [Veir/Passes/ArithCanonicalize/CP013.lean](../Veir/Passes/ArithCanonicalize/CP013.lean); `Veir.ArithCanonicalize.CP013.valid`.

### F001: arith::AddIOp::fold

[Original code: ArithOps.cpp:433–451](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L433-L451).

addi(x, 0) -> x.

**Matched:** `arith.addi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches scalar or splat zero.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for addi(x, 0) -> x, including poison, applicable overflow or exact flags.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F001.lean](../Veir/Passes/ArithCanonicalize/F001.lean); `Veir.ArithCanonicalize.F001.valid`.

### F002: arith::AddIOp::fold

[Original code: ArithOps.cpp:433–451](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L433-L451).

addi(subi(a, b), b) -> a.

**Matched:** `arith.addi`, `arith.subi`. **Replacement:** existing SSA value.

**Conditions:** LHS is subi(a,b), and outer RHS is exactly its RHS operand.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for addi(subi(a, b), b) -> a, including poison, applicable overflow or exact flags.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F002.lean](../Veir/Passes/ArithCanonicalize/F002.lean); `Veir.ArithCanonicalize.F002.valid`.

### F003: arith::AddIOp::fold

[Original code: ArithOps.cpp:433–451](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L433-L451).

addi(b, subi(a, b)) -> a.

**Matched:** `arith.addi`, `arith.subi`. **Replacement:** existing SSA value.

**Conditions:** RHS is subi(a,b), and outer LHS is exactly its RHS operand.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for addi(b, subi(a, b)) -> a, including poison, applicable overflow or exact flags.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F003.lean](../Veir/Passes/ArithCanonicalize/F003.lean); `Veir.ArithCanonicalize.F003.valid`.

### F004: arith::AddIOp::fold

[Original code: ArithOps.cpp:433–451](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L433-L451).

Constant-fold addi over integer attributes: (a,b) -> a+b modulo result bit width.

**Matched:** `arith.addi`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands fold to compatible IntegerAttr values; generic constFold helper handles scalar and shaped elementwise cases, and propagates poison.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for scalar constant-folded addi: a + b modulo result width. Source overflow flags may produce poison, which refines the modular constant.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F004.lean](../Veir/Passes/ArithCanonicalize/F004.lean); `Veir.ArithCanonicalize.F004.valid`.

### F005: arith::AddUIExtendedOp::fold

[Original code: ArithOps.cpp:476–516](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L476-L516).

addui_extended(x, 0) -> (x, false).

**Matched:** `arith.addui_extended`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** RHS matches zero; false is zero attribute of overflow result type.

**Status: Succeeded — proven.** Two-result Puddle Pattern.Valid proof for addui_extended(x, 0) -> (x, false); each result is checked under poison refinement.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F005.lean](../Veir/Passes/ArithCanonicalize/F005.lean); `Veir.ArithCanonicalize.F005.valid`.

### F006: arith::AddUIExtendedOp::fold

[Original code: ArithOps.cpp:476–516](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L476-L516).

addui_extended(constant_a, constant_b) -> (constant_sum, constant_carry), carry = unsigned sum < lhs.

**Matched:** `arith.addui_extended`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands constant-fold as IntegerAttr; if sum is poison, both results are poison; otherwise carry folds over lhs and sum using i1 same-shape type; failure to materialize carry causes fold failure.

**Status: Succeeded — proven.** Pattern.Valid proof of constant folding both addui_extended results, including the unsigned carry, via exact bitvector arithmetic and normalized IntegerAttr values.

**Coverage:** scalar integer; all valid widths and signednesses; both results

**Lean:** [Veir/Passes/ArithCanonicalize/F006.lean](../Veir/Passes/ArithCanonicalize/F006.lean); `Veir.ArithCanonicalize.F006.valid`.

### F007: arith::SubUIExtendedOp::fold

[Original code: ArithOps.cpp:540–595](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L540-L595).

subui_extended(x, 0) -> (x, false).

**Matched:** `arith.subui_extended`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** RHS matches zero; false has borrow result type.

**Status: Succeeded — proven.** Two-result Puddle Pattern.Valid proof for subui_extended(x, 0) -> (x, false); each result is checked under poison refinement.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F007.lean](../Veir/Passes/ArithCanonicalize/F007.lean); `Veir.ArithCanonicalize.F007.valid`.

### F008: arith::SubUIExtendedOp::fold

[Original code: ArithOps.cpp:540–595](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L540-L595).

subui_extended(x, x) -> (0, false).

**Matched:** `arith.subui_extended`. **Replacement:** `arith.constant`.

**Conditions:** Operands are identical; result shape must be static if shaped; zero attr must be buildable.

**Status: Succeeded — proven.** Two-result Puddle Pattern.Valid proof for subui_extended(x, x) -> (0, false); each result is checked under poison refinement.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F008.lean](../Veir/Passes/ArithCanonicalize/F008.lean); `Veir.ArithCanonicalize.F008.valid`.

### F009: arith::SubUIExtendedOp::fold

[Original code: ArithOps.cpp:540–595](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L540-L595).

subui_extended(constant_a, constant_b) -> (constant_diff, constant_borrow), borrow = lhs < rhs unsigned.

**Matched:** `arith.subui_extended`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands fold to IntegerAttr; poison diff propagates to both results; otherwise borrow is elementwise over operands with i1 same-shape result; if borrow cannot fold, fail.

**Status: Succeeded — proven.** Pattern.Valid proof of constant folding both subui_extended results, including the unsigned borrow, via exact bitvector arithmetic and normalized IntegerAttr values.

**Coverage:** scalar integer; all valid widths and signednesses; both results

**Lean:** [Veir/Passes/ArithCanonicalize/F009.lean](../Veir/Passes/ArithCanonicalize/F009.lean); `Veir.ArithCanonicalize.F009.valid`.

### F010: arith::SubIOp::fold

[Original code: ArithOps.cpp:606–635](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L606-L635).

subi(x, x) -> 0.

**Matched:** `arith.subi`. **Replacement:** `arith.constant`.

**Conditions:** Operands identical; scalar or static-shaped result only; dynamic-shaped result cannot materialize zero.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for subi(x, x) -> 0, including poison, applicable overflow or exact flags.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F010.lean](../Veir/Passes/ArithCanonicalize/F010.lean); `Veir.ArithCanonicalize.F010.valid`.

### F011: arith::SubIOp::fold

[Original code: ArithOps.cpp:606–635](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L606-L635).

subi(x, 0) -> x.

**Matched:** `arith.subi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches zero.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for subi(x, 0) -> x, including poison, applicable overflow or exact flags.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F011.lean](../Veir/Passes/ArithCanonicalize/F011.lean); `Veir.ArithCanonicalize.F011.valid`.

### F012: arith::SubIOp::fold

[Original code: ArithOps.cpp:606–635](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L606-L635).

subi(addi(a, b), b) -> a.

**Matched:** `arith.subi`, `arith.addi`. **Replacement:** existing SSA value.

**Conditions:** LHS is addi(a,b), outer RHS equals addi RHS.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for subi(addi(a, b), b) -> a, including poison, applicable overflow or exact flags.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F012.lean](../Veir/Passes/ArithCanonicalize/F012.lean); `Veir.ArithCanonicalize.F012.valid`.

### F013: arith::SubIOp::fold

[Original code: ArithOps.cpp:606–635](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L606-L635).

subi(addi(a, b), a) -> b.

**Matched:** `arith.subi`, `arith.addi`. **Replacement:** existing SSA value.

**Conditions:** LHS is addi(a,b), outer RHS equals addi LHS.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for subi(addi(a, b), a) -> b, including poison, applicable overflow or exact flags.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F013.lean](../Veir/Passes/ArithCanonicalize/F013.lean); `Veir.ArithCanonicalize.F013.valid`.

### F014: arith::SubIOp::fold

[Original code: ArithOps.cpp:606–635](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L606-L635).

subi(a, subi(a, b)) -> b.

**Matched:** `arith.subi`. **Replacement:** existing SSA value.

**Conditions:** RHS is subi(a,b), outer LHS equals inner LHS.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for subi(a, subi(a, b)) -> b, including poison, applicable overflow or exact flags.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F014.lean](../Veir/Passes/ArithCanonicalize/F014.lean); `Veir.ArithCanonicalize.F014.valid`.

### F015: arith::SubIOp::fold

[Original code: ArithOps.cpp:606–635](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L606-L635).

Constant-fold subi: (a,b) -> a-b modulo result bit width.

**Matched:** `arith.subi`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands fold to compatible IntegerAttr values; constFoldBinaryOp semantics apply, including generic poison propagation.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for scalar constant-folded subi: a - b modulo result width. Source overflow flags may produce poison, which refines the modular constant.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F015.lean](../Veir/Passes/ArithCanonicalize/F015.lean); `Veir.ArithCanonicalize.F015.valid`.

### F016: arith::MulIOp::fold

[Original code: ArithOps.cpp:648–661](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L648-L661).

muli(x, 0) -> 0.

**Matched:** `arith.muli`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches zero; returns RHS attribute.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for muli(x, 0) -> 0, including poison, applicable overflow or exact flags.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F016.lean](../Veir/Passes/ArithCanonicalize/F016.lean); `Veir.ArithCanonicalize.F016.valid`.

### F017: arith::MulIOp::fold

[Original code: ArithOps.cpp:648–661](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L648-L661).

muli(x, 1) -> x.

**Matched:** `arith.muli`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches one.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for muli(x, 1) -> x, including poison, applicable overflow or exact flags.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F017.lean](../Veir/Passes/ArithCanonicalize/F017.lean); `Veir.ArithCanonicalize.F017.valid`.

### F018: arith::MulIOp::fold

[Original code: ArithOps.cpp:648–661](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L648-L661).

Constant-fold muli: (a,b) -> a*b modulo result bit width.

**Matched:** `arith.muli`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands fold to compatible IntegerAttr values; the folder deliberately does not handle overflow flags/overflow case beyond modular result semantics.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for scalar constant-folded muli: a * b modulo result width. Source overflow flags may produce poison, which refines the modular constant.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F018.lean](../Veir/Passes/ArithCanonicalize/F018.lean); `Veir.ArithCanonicalize.F018.valid`.

### F019: arith::MulSIExtendedOp::fold

[Original code: ArithOps.cpp:706–732](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L706-L732).

mulsi_extended(x, 0) -> (0, 0).

**Matched:** `arith.mulsi_extended`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** RHS matches zero; reuse zero attribute for both results.

**Status: Succeeded — proven.** Pattern.Valid proof of both results for mulsi_extended(x, 0) to (0, 0), including poison on either result.

**Coverage:** scalar integer; all widths and signednesses

**Lean:** [Veir/Passes/ArithCanonicalize/F019.lean](../Veir/Passes/ArithCanonicalize/F019.lean); `Veir.ArithCanonicalize.F019.valid`.

### F020: arith::MulSIExtendedOp::fold

[Original code: ArithOps.cpp:706–732](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L706-L732).

Constant-fold mulsi_extended constants to (low product, signed high product).

**Matched:** `arith.mulsi_extended`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands fold via IntegerAttr low product; high product uses APIntOps::mulhs and is asserted available.

**Status: Succeeded — proven.** Pattern.Valid proof of constant folding both mulsi_extended results, including the signed high product, via exact bitvector arithmetic and normalized IntegerAttr values.

**Coverage:** scalar integer; all valid widths and signednesses; both results

**Lean:** [Veir/Passes/ArithCanonicalize/F020.lean](../Veir/Passes/ArithCanonicalize/F020.lean); `Veir.ArithCanonicalize.F020.valid`.

### F021: arith::MulUIExtendedOp::fold

[Original code: ArithOps.cpp:750–785](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L750-L785).

mului_extended(x, 0) -> (0, 0).

**Matched:** `arith.mului_extended`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** RHS matches zero; reuse zero attribute.

**Status: Succeeded — proven.** Pattern.Valid proof of both results for mului_extended(x, 0) to (0, 0), including poison on either result.

**Coverage:** scalar integer; all widths and signednesses

**Lean:** [Veir/Passes/ArithCanonicalize/F021.lean](../Veir/Passes/ArithCanonicalize/F021.lean); `Veir.ArithCanonicalize.F021.valid`.

### F022: arith::MulUIExtendedOp::fold

[Original code: ArithOps.cpp:750–785](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L750-L785).

mului_extended(x, 1) -> (x, 0).

**Matched:** `arith.mului_extended`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** RHS matches one; zero attribute must be buildable for LHS type.

**Status: Succeeded — proven.** Pattern.Valid proof of both results for mului_extended(x, 1) to (x, 0), including poison on either result.

**Coverage:** scalar integer; all widths and signednesses

**Lean:** [Veir/Passes/ArithCanonicalize/F022.lean](../Veir/Passes/ArithCanonicalize/F022.lean); `Veir.ArithCanonicalize.F022.valid`.

### F023: arith::MulUIExtendedOp::fold

[Original code: ArithOps.cpp:750–785](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L750-L785).

Constant-fold mului_extended constants to (low product, unsigned high product).

**Matched:** `arith.mului_extended`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands fold via IntegerAttr low product; high product uses APIntOps::mulhu and is asserted available.

**Status: Succeeded — proven.** Pattern.Valid proof of constant folding both mului_extended results, including the unsigned high product, via exact bitvector arithmetic and normalized IntegerAttr values.

**Coverage:** scalar integer; all valid widths and signednesses; both results

**Lean:** [Veir/Passes/ArithCanonicalize/F023.lean](../Veir/Passes/ArithCanonicalize/F023.lean); `Veir.ArithCanonicalize.F023.valid`.

### F024: arith::DivUIOp::fold

[Original code: ArithOps.cpp:812–845](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L812-L845).

divui(x, 1) -> x.

**Matched:** `arith.divui`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches one.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for divui(x, 1) -> x, including poison, the exact flag, and undefined division cases.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F024.lean](../Veir/Passes/ArithCanonicalize/F024.lean); `Veir.ArithCanonicalize.F024.valid`.

### F025: arith::DivUIOp::fold

[Original code: ArithOps.cpp:812–845](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L812-L845).

divui(0, x) -> 0.

**Matched:** `arith.divui`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** LHS matches zero; division by zero is undefined, so choosing zero is a valid refinement.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for divui(0, x) -> 0, including poison, the exact flag, and undefined division cases.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F025.lean](../Veir/Passes/ArithCanonicalize/F025.lean); `Veir.ArithCanonicalize.F025.valid`.

### F026: arith::DivUIOp::fold

[Original code: ArithOps.cpp:812–845](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L812-L845).

divui(x, x) -> 1.

**Matched:** `arith.divui`. **Replacement:** `arith.constant`.

**Conditions:** Operands identical; includes x=0 where source is undefined, so constant 1 is a valid refinement.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for divui(x, x) -> 1; successful source excludes zero or poison divisor, and exact division preserves the result.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F026.lean](../Veir/Passes/ArithCanonicalize/F026.lean); `Veir.ArithCanonicalize.F026.valid`.

### F027: arith::DivUIOp::fold

[Original code: ArithOps.cpp:812–845](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L812-L845).

(a*b)/b -> a for divui, when multiplication carries nuw.

**Matched:** `arith.divui`, `arith.muli`. **Replacement:** existing SSA value.

**Conditions:** LHS is arith.muli with one operand identical to divisor RHS; inner muli must have nuw overflow flag; operand order can be either.

**Status: Succeeded — proven.** Two Pattern.Valid proofs cover (a*b)/b and (b*a)/b for divui when muli has nuw. The proof handles arbitrary nsw and exact flags, overflow poison, and zero-divisor behavior.

**Coverage:** scalar integer; all widths and signednesses; both multiplication operand orders

**Lean:** [Veir/Passes/ArithCanonicalize/F027.lean](../Veir/Passes/ArithCanonicalize/F027.lean); `Veir.ArithCanonicalize.F027.valid; Veir.ArithCanonicalize.F027.valid_swapped`.

### F028: arith::DivUIOp::fold

[Original code: ArithOps.cpp:812–845](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L812-L845).

Constant-fold divui: unsigned quotient.

**Matched:** `arith.divui`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands fold to IntegerAttr and divisor is nonzero.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for scalar constant-folded divui(a, b) -> unsigned quotient a/b, guarded by a nonzero divisor; zero divisors are excluded and any source poison result refines the constant.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F028.lean](../Veir/Passes/ArithCanonicalize/F028.lean); `Veir.ArithCanonicalize.F028.valid`.

### F029: arith::DivSIOp::fold

[Original code: ArithOps.cpp:864–897](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L864-L897).

divsi(x, 1) -> x.

**Matched:** `arith.divsi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches one.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for divsi(x, 1) -> x, including poison, the exact flag, and undefined division cases.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F029.lean](../Veir/Passes/ArithCanonicalize/F029.lean); `Veir.ArithCanonicalize.F029.valid`.

### F030: arith::DivSIOp::fold

[Original code: ArithOps.cpp:864–897](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L864-L897).

divsi(0, x) -> 0.

**Matched:** `arith.divsi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** LHS matches zero; division by zero is undefined, so choosing zero is a valid refinement.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for divsi(0, x) -> 0, including poison, the exact flag, and undefined division cases.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F030.lean](../Veir/Passes/ArithCanonicalize/F030.lean); `Veir.ArithCanonicalize.F030.valid`.

### F031: arith::DivSIOp::fold

[Original code: ArithOps.cpp:864–897](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L864-L897).

divsi(x, x) -> 1.

**Matched:** `arith.divsi`. **Replacement:** `arith.constant`.

**Conditions:** Operands identical; includes x=0 where source is undefined, so constant 1 is a valid refinement.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for divsi(x, x) -> 1, including poison and exact division. Zero and signed overflow source cases are undefined.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F031.lean](../Veir/Passes/ArithCanonicalize/F031.lean); `Veir.ArithCanonicalize.F031.valid`.

### F032: arith::DivSIOp::fold

[Original code: ArithOps.cpp:864–897](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L864-L897).

(a*b)/b -> a for divsi, when multiplication carries nsw.

**Matched:** `arith.divsi`, `arith.muli`. **Replacement:** existing SSA value.

**Conditions:** LHS is arith.muli with one operand identical to divisor RHS; inner muli must have nsw overflow flag; operand order can be either.

**Status: Succeeded — proven.** Two all-width Puddle Pattern.Valid proofs for divsi(muli(a,b),b) -> a in both multiplication operand orders. Matching requires nsw on the multiplication; arbitrary nuw and exact flags, poison, zero divisors, and signed division overflow are handled by source UB and refinement.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F032.lean](../Veir/Passes/ArithCanonicalize/F032.lean); `Veir.ArithCanonicalize.F032.valid; Veir.ArithCanonicalize.F032.valid_commuted`.

### F033: arith::DivSIOp::fold

[Original code: ArithOps.cpp:864–897](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L864-L897).

Constant-fold divsi: signed quotient.

**Matched:** `arith.divsi`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands fold to IntegerAttr and divisor is nonzero; signed division must also be representable (MIN / -1 does not fold).

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for scalar signed quotient constants, guarded by nonzero divisor and excluding INT_MIN/-1 overflow; exact-source poison refines the computed constant.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F033.lean](../Veir/Passes/ArithCanonicalize/F033.lean); `Veir.ArithCanonicalize.F033.valid`.

### F034: arith::CeilDivUIOp::fold

[Original code: ArithOps.cpp:920–952](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L920-L952).

ceildivui(x, 1) -> x.

**Matched:** `arith.ceildivui`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches one.

**Status: Succeeded — proven.** All-width Puddle Pattern.Valid proof for ceildivui(x, 1) -> x; the source division condition excludes the zero-width encoding of one.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F034.lean](../Veir/Passes/ArithCanonicalize/F034.lean); `Veir.ArithCanonicalize.F034.valid`.

### F035: arith::CeilDivUIOp::fold

[Original code: ArithOps.cpp:920–952](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L920-L952).

ceildivui(0, x) -> 0.

**Matched:** `arith.ceildivui`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** LHS matches zero; x=0 case is undefined and refining to zero is valid.

**Status: Succeeded — proven.** All-width Puddle Pattern.Valid proof for ceildivui(0, x) -> 0; zero divisors are undefined and a poison divisor cannot produce a defined result.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F035.lean](../Veir/Passes/ArithCanonicalize/F035.lean); `Veir.ArithCanonicalize.F035.valid`.

### F036: arith::CeilDivUIOp::fold

[Original code: ArithOps.cpp:920–952](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L920-L952).

ceildivui(x, x) -> 1.

**Matched:** `arith.ceildivui`. **Replacement:** `arith.constant`.

**Conditions:** Operands identical; x=0 is undefined and replacement is a valid refinement.

**Status: Succeeded — proven.** All-width Puddle Pattern.Valid proof for ceildivui(x, x) -> 1; the source division condition excludes zero and poison divisors.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F036.lean](../Veir/Passes/ArithCanonicalize/F036.lean); `Veir.ArithCanonicalize.F036.valid`.

### F037: arith::CeilDivUIOp::fold

[Original code: ArithOps.cpp:920–952](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L920-L952).

Constant-fold unsigned ceil division: q=a/b if divisible, else q+1.

**Matched:** `arith.ceildivui`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands constants; divisor nonzero; increment overflow rejects fold.

**Status: Succeeded — proven.** All-width Puddle Pattern.Valid proof for unsigned ceil-division constant evaluation. The proof equates the interpreter predecessor quotient with the pinned APInt quotient-plus-remainder formula, with nonzero-divisor and correction-overflow guards.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F037.lean](../Veir/Passes/ArithCanonicalize/F037.lean); `Veir.ArithCanonicalize.F037.valid`.

### F038: arith::CeilDivSIOp::fold

[Original code: ArithOps.cpp:962–1013](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L962-L1013).

ceildivsi(x, 1) -> x.

**Matched:** `arith.ceildivsi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches one.

**Status: Succeeded — proven.** All-width Puddle Pattern.Valid proof for ceildivsi x / 1 -> x; signed division by zero or signed overflow is excluded by source UB and poison refinement is preserved.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F038.lean](../Veir/Passes/ArithCanonicalize/F038.lean); `Veir.ArithCanonicalize.F038.valid`.

### F039: arith::CeilDivSIOp::fold

[Original code: ArithOps.cpp:962–1013](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L962-L1013).

ceildivsi(0, x) -> 0.

**Matched:** `arith.ceildivsi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** LHS matches zero; x=0 is undefined and replacement is valid refinement.

**Status: Succeeded — proven.** All-width Puddle Pattern.Valid proof for ceildivsi 0 / x -> 0; signed division by zero or signed overflow is excluded by source UB and poison refinement is preserved.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F039.lean](../Veir/Passes/ArithCanonicalize/F039.lean); `Veir.ArithCanonicalize.F039.valid`.

### F040: arith::CeilDivSIOp::fold

[Original code: ArithOps.cpp:962–1013](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L962-L1013).

ceildivsi(x, x) -> 1.

**Matched:** `arith.ceildivsi`. **Replacement:** `arith.constant`.

**Conditions:** Operands identical; x=0 is undefined and replacement is valid refinement.

**Status: Succeeded — proven.** All-width Puddle Pattern.Valid proof for ceildivsi x / x -> 1; signed division by zero or signed overflow is excluded by source UB and poison refinement is preserved.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F040.lean](../Veir/Passes/ArithCanonicalize/F040.lean); `Veir.ArithCanonicalize.F040.valid`.

### F041: arith::CeilDivSIOp::fold

[Original code: ArithOps.cpp:962–1013](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L962-L1013).

Constant-fold signed ceil division, correcting truncating quotient by +1 only for positive inexact quotient.

**Matched:** `arith.ceildivsi`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands constants; divisor nonzero; MIN/-1 overflow rejects; inexact correction is checked for overflow.

**Status: Succeeded — proven.** All-width Puddle Pattern.Valid proof for signed ceil-division constant evaluation. The calculator applies the pinned truncating quotient correction only for equal-sign inexact operands; matching excludes zero divisors, MIN/-1 signed overflow, and correction overflow.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F041.lean](../Veir/Passes/ArithCanonicalize/F041.lean); `Veir.ArithCanonicalize.F041.valid`.

### F042: arith::FloorDivSIOp::fold

[Original code: ArithOps.cpp:1023–1052](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1023-L1052).

floordivsi(x, 1) -> x.

**Matched:** `arith.floordivsi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches one.

**Status: Succeeded — proven.** All-width Puddle Pattern.Valid proof for floordivsi x / 1 -> x; signed division by zero or signed overflow is excluded by source UB and poison refinement is preserved.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F042.lean](../Veir/Passes/ArithCanonicalize/F042.lean); `Veir.ArithCanonicalize.F042.valid`.

### F043: arith::FloorDivSIOp::fold

[Original code: ArithOps.cpp:1023–1052](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1023-L1052).

floordivsi(0, x) -> 0.

**Matched:** `arith.floordivsi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** LHS matches zero; x=0 undefined and replacement valid refinement.

**Status: Succeeded — proven.** All-width Puddle Pattern.Valid proof for floordivsi 0 / x -> 0; signed division by zero or signed overflow is excluded by source UB and poison refinement is preserved.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F043.lean](../Veir/Passes/ArithCanonicalize/F043.lean); `Veir.ArithCanonicalize.F043.valid`.

### F044: arith::FloorDivSIOp::fold

[Original code: ArithOps.cpp:1023–1052](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1023-L1052).

floordivsi(x, x) -> 1.

**Matched:** `arith.floordivsi`. **Replacement:** `arith.constant`.

**Conditions:** Operands identical; x=0 undefined and replacement valid refinement.

**Status: Succeeded — proven.** All-width Puddle Pattern.Valid proof for floordivsi x / x -> 1; signed division by zero or signed overflow is excluded by source UB and poison refinement is preserved.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F044.lean](../Veir/Passes/ArithCanonicalize/F044.lean); `Veir.ArithCanonicalize.F044.valid`.

### F045: arith::FloorDivSIOp::fold

[Original code: ArithOps.cpp:1023–1052](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1023-L1052).

Constant-fold signed floor division.

**Matched:** `arith.floordivsi`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands constants; divisor nonzero; signed overflow (MIN/-1) rejects fold.

**Status: Succeeded — proven.** All-width Puddle Pattern.Valid proof for signed floor-division constant evaluation. The calculator applies the floor correction to truncating division for opposite-sign inexact operands; matching excludes zero divisors and MIN/-1 signed overflow.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F045.lean](../Veir/Passes/ArithCanonicalize/F045.lean); `Veir.ArithCanonicalize.F045.valid`.

### F046: arith::RemUIOp::fold

[Original code: ArithOps.cpp:1058–1084](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1058-L1084).

remui(x, 1) -> 0.

**Matched:** `arith.remui`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** RHS matches one.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for remui(x, 1) -> 0, including poison and undefined remainder cases.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F046.lean](../Veir/Passes/ArithCanonicalize/F046.lean); `Veir.ArithCanonicalize.F046.valid`.

### F047a: arith::RemUIOp::fold

[Original code: ArithOps.cpp:1058–1084](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1058-L1084).

remui(0, x) -> 0.

**Matched:** `arith.remui`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** LHS matches zero; if x=0, source is undefined, so zero is a valid refinement.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for remui(0, x) -> 0, including poison and undefined remainder cases.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F047a.lean](../Veir/Passes/ArithCanonicalize/F047a.lean); `Veir.ArithCanonicalize.F047a.valid`.

### F047b: arith::RemUIOp::fold

[Original code: ArithOps.cpp:1058–1084](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1058-L1084).

remui(x, x) -> 0.

**Matched:** `arith.remui`. **Replacement:** `arith.constant`.

**Conditions:** Operands are identical; when x=0 source is undefined, so zero is a valid refinement.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for remui(x, x) -> 0, including poison and undefined remainder cases.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F047b.lean](../Veir/Passes/ArithCanonicalize/F047b.lean); `Veir.ArithCanonicalize.F047b.valid`.

### F048: arith::RemUIOp::fold

[Original code: ArithOps.cpp:1058–1084](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1058-L1084).

Constant-fold unsigned remainder.

**Matched:** `arith.remui`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands fold to compatible integer attributes; divisor is nonzero. The common helper also propagates poison.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for scalar constant-folded remui(a, b) -> unsigned remainder a%b, guarded by a nonzero divisor; zero divisors are excluded and any source poison result refines the constant.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F048.lean](../Veir/Passes/ArithCanonicalize/F048.lean); `Veir.ArithCanonicalize.F048.valid`.

### F049: arith::RemSIOp::fold

[Original code: ArithOps.cpp:1094–1120](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1094-L1120).

remsi(x, 1) -> 0.

**Matched:** `arith.remsi`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** RHS matches one.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for remsi(x, 1) -> 0, including poison and undefined remainder cases.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F049.lean](../Veir/Passes/ArithCanonicalize/F049.lean); `Veir.ArithCanonicalize.F049.valid`.

### F050a: arith::RemSIOp::fold

[Original code: ArithOps.cpp:1094–1120](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1094-L1120).

remsi(0, x) -> 0.

**Matched:** `arith.remsi`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** LHS matches zero; if x=0, source is undefined, so zero is a valid refinement.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for remsi(0, x) -> 0, including poison and undefined remainder cases.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F050a.lean](../Veir/Passes/ArithCanonicalize/F050a.lean); `Veir.ArithCanonicalize.F050a.valid`.

### F050b: arith::RemSIOp::fold

[Original code: ArithOps.cpp:1094–1120](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1094-L1120).

remsi(x, x) -> 0.

**Matched:** `arith.remsi`. **Replacement:** `arith.constant`.

**Conditions:** Operands are identical; when x=0 source is undefined, so zero is a valid refinement.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for remsi(x, x) -> 0, including poison and undefined remainder cases.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F050b.lean](../Veir/Passes/ArithCanonicalize/F050b.lean); `Veir.ArithCanonicalize.F050b.valid`.

### F051: arith::RemSIOp::fold

[Original code: ArithOps.cpp:1094–1120](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1094-L1120).

Constant-fold signed remainder.

**Matched:** `arith.remsi`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands fold to integer attributes; the divisor must be nonzero. The pinned folder computes zero for INT_MIN % -1. Verification preserves VeIR's original semantics, as requested: that source case is undefined behavior, so replacing it with zero is a refinement. The common helper also handles poison propagation.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for scalar constant-folded remsi(a, b) -> signed remainder a srem b, guarded by a nonzero divisor; zero divisors are excluded and VeIR signed-overflow UB permits the folded result.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F051.lean](../Veir/Passes/ArithCanonicalize/F051.lean); `Veir.ArithCanonicalize.F051.valid`.

### F052: arith::AndIOp::fold

[Original code: ArithOps.cpp:1154–1181](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1154-L1181).

andi(x, 0) -> 0.

**Matched:** `arith.andi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches scalar/splat zero.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for andi(x, 0) -> 0; covers poison.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F052.lean](../Veir/Passes/ArithCanonicalize/F052.lean); `Veir.ArithCanonicalize.F052.valid`.

### F053: arith::AndIOp::fold

[Original code: ArithOps.cpp:1154–1181](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1154-L1181).

andi(x, all_ones) -> x.

**Matched:** `arith.andi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS is IntegerAttr constant whose APInt is all ones.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for andi(x, all_ones) -> x; covers poison; all-ones matching compares normalized bit patterns.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F053.lean](../Veir/Passes/ArithCanonicalize/F053.lean); `Veir.ArithCanonicalize.F053.valid`.

### F054: arith::AndIOp::fold

[Original code: ArithOps.cpp:1154–1181](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1154-L1181).

andi(x, xori(x, all_ones)) -> 0.

**Matched:** `arith.andi`, `arith.xori`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** RHS is xori with LHS equal to outer LHS and XOR mask all ones.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for andi(x, xori(x, all_ones)) -> 0, including poison and normalized all-ones bit-pattern matching.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F054.lean](../Veir/Passes/ArithCanonicalize/F054.lean); `Veir.ArithCanonicalize.F054.valid`.

### F055: arith::AndIOp::fold

[Original code: ArithOps.cpp:1154–1181](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1154-L1181).

andi(xori(x, all_ones), x) -> 0.

**Matched:** `arith.andi`, `arith.xori`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** LHS is xori with LHS equal to outer RHS and XOR mask all ones.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for andi(xori(x, all_ones), x) -> 0, including poison and normalized all-ones bit-pattern matching.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F055.lean](../Veir/Passes/ArithCanonicalize/F055.lean); `Veir.ArithCanonicalize.F055.valid`.

### F056: arith::AndIOp::fold

[Original code: ArithOps.cpp:1154–1181](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1154-L1181).

andi(a, andi(a, b)) -> andi(a, b), in either operand ordering.

**Matched:** `arith.andi`. **Replacement:** existing SSA value.

**Conditions:** One operand is nested andi; other operand equals either nested operand; helper checks both outer and inner operand order.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for nested andi absorption in both inner and outer operand orders (four instances), including poison.

**Coverage:** all scalar integer operand-order instances of pinned fold; shaped variants outside scalar Puddle model

**Lean:** [Veir/Passes/ArithCanonicalize/F056.lean](../Veir/Passes/ArithCanonicalize/F056.lean); `Veir.ArithCanonicalize.F056.valid`.

### F057: arith::AndIOp::fold

[Original code: ArithOps.cpp:1154–1181](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1154-L1181).

Constant-fold andi: a & b.

**Matched:** `arith.andi`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands fold to compatible IntegerAttr values; generic const fold supports shaped elementwise values and poison.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for scalar constant-folded andi; integer attributes are normalized to the exact result bit pattern, including OR disjoint flag poison refinement.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F057.lean](../Veir/Passes/ArithCanonicalize/F057.lean); `Veir.ArithCanonicalize.F057.valid`.

### F058: arith::OrIOp::fold

[Original code: ArithOps.cpp:1187–1216](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1187-L1216).

ori(x, 0) -> x.

**Matched:** `arith.ori`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS is zero IntegerAttr.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for ori(x, 0) -> x; covers poison.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F058.lean](../Veir/Passes/ArithCanonicalize/F058.lean); `Veir.ArithCanonicalize.F058.valid`.

### F059: arith::OrIOp::fold

[Original code: ArithOps.cpp:1187–1216](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1187-L1216).

ori(x, all_ones) -> all_ones.

**Matched:** `arith.ori`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** RHS is all-ones IntegerAttr.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for ori(x, all_ones) -> all_ones; covers poison; all-ones matching compares normalized bit patterns.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F059.lean](../Veir/Passes/ArithCanonicalize/F059.lean); `Veir.ArithCanonicalize.F059.valid`.

### F060: arith::OrIOp::fold

[Original code: ArithOps.cpp:1187–1216](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1187-L1216).

ori(x, xori(x, all_ones)) -> all_ones.

**Matched:** `arith.ori`, `arith.xori`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS is xori with common x and all-ones mask; returns the XOR constant.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for ori(x, xori(x, all_ones)) -> all_ones, including poison and normalized all-ones bit-pattern matching.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F060.lean](../Veir/Passes/ArithCanonicalize/F060.lean); `Veir.ArithCanonicalize.F060.valid`.

### F061: arith::OrIOp::fold

[Original code: ArithOps.cpp:1187–1216](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1187-L1216).

ori(xori(x, all_ones), x) -> all_ones.

**Matched:** `arith.ori`, `arith.xori`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** LHS is xori with common x and all-ones mask; returns the XOR constant.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for ori(xori(x, all_ones), x) -> all_ones, including poison and normalized all-ones bit-pattern matching.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F061.lean](../Veir/Passes/ArithCanonicalize/F061.lean); `Veir.ArithCanonicalize.F061.valid`.

### F062: arith::OrIOp::fold

[Original code: ArithOps.cpp:1187–1216](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1187-L1216).

ori(a, ori(a, b)) -> ori(a, b), in either operand ordering.

**Matched:** `arith.ori`. **Replacement:** existing SSA value.

**Conditions:** One operand is nested ori; other equals either nested operand; helper checks both orders.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for nested ori absorption in both inner and outer operand orders (four instances), retaining arbitrary independent disjoint flags and poison.

**Coverage:** all scalar integer operand-order instances of pinned fold; shaped variants outside scalar Puddle model

**Lean:** [Veir/Passes/ArithCanonicalize/F062.lean](../Veir/Passes/ArithCanonicalize/F062.lean); `Veir.ArithCanonicalize.F062.valid`.

### F063: arith::OrIOp::fold

[Original code: ArithOps.cpp:1187–1216](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1187-L1216).

Constant-fold ori: a | b.

**Matched:** `arith.ori`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands fold to compatible IntegerAttr values; generic const fold supports shaped elementwise values and poison.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for scalar constant-folded ori; integer attributes are normalized to the exact result bit pattern, including OR disjoint flag poison refinement.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F063.lean](../Veir/Passes/ArithCanonicalize/F063.lean); `Veir.ArithCanonicalize.F063.valid`.

### F064: arith::XOrIOp::fold

[Original code: ArithOps.cpp:1222–1254](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1222-L1254).

xori(x, 0) -> x.

**Matched:** `arith.xori`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches scalar/splat zero.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for xori(x, 0) -> x; covers poison.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F064.lean](../Veir/Passes/ArithCanonicalize/F064.lean); `Veir.ArithCanonicalize.F064.valid`.

### F065: arith::XOrIOp::fold

[Original code: ArithOps.cpp:1222–1254](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1222-L1254).

xori(x, x) -> 0.

**Matched:** `arith.xori`. **Replacement:** `arith.constant`.

**Conditions:** Operands identical; scalar or static-shaped type only; dynamic-shaped result cannot materialize zero.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for xori(x, x) -> 0; covers poison.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F065.lean](../Veir/Passes/ArithCanonicalize/F065.lean); `Veir.ArithCanonicalize.F065.valid`.

### F066: arith::XOrIOp::fold

[Original code: ArithOps.cpp:1222–1254](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1222-L1254).

xori(xori(x, a), a) -> x, including both inner operand orders.

**Matched:** `arith.xori`. **Replacement:** existing SSA value.

**Conditions:** LHS is xori and either inner operand equals outer RHS.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for xori(xori(x,a),a) cancellation with both inner operand orders, including poison.

**Coverage:** all scalar integer operand-order instances of pinned fold; shaped variants outside scalar Puddle model

**Lean:** [Veir/Passes/ArithCanonicalize/F066.lean](../Veir/Passes/ArithCanonicalize/F066.lean); `Veir.ArithCanonicalize.F066.valid`.

### F067: arith::XOrIOp::fold

[Original code: ArithOps.cpp:1222–1254](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1222-L1254).

xori(a, xori(x, a)) -> x, including both inner operand orders.

**Matched:** `arith.xori`. **Replacement:** existing SSA value.

**Conditions:** RHS is xori and either inner operand equals outer LHS.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for xori(a,xori(x,a)) cancellation with both inner operand orders, including poison.

**Coverage:** all scalar integer operand-order instances of pinned fold; shaped variants outside scalar Puddle model

**Lean:** [Veir/Passes/ArithCanonicalize/F067.lean](../Veir/Passes/ArithCanonicalize/F067.lean); `Veir.ArithCanonicalize.F067.valid`.

### F068: arith::XOrIOp::fold

[Original code: ArithOps.cpp:1222–1254](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1222-L1254).

Constant-fold xori: a ^ b.

**Matched:** `arith.xori`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands fold to compatible IntegerAttr values; generic const fold supports shaped elementwise values and poison.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for scalar constant-folded xori; integer attributes are normalized to the exact result bit pattern, including OR disjoint flag poison refinement.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F068.lean](../Veir/Passes/ArithCanonicalize/F068.lean); `Veir.ArithCanonicalize.F068.valid`.

### F069: arith::ShLIOp::fold

[Original code: ArithOps.cpp:3209–3230](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3209-L3230).

shli(x, 0) -> x.

**Matched:** `arith.shli`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches zero.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for shli(x, 0) -> x; out-of-range counts and enabled overflow/exact flags preserve poison refinement.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F069.lean](../Veir/Passes/ArithCanonicalize/F069.lean); `Veir.ArithCanonicalize.F069.valid`.

### F070: arith::ShLIOp::fold

[Original code: ArithOps.cpp:3209–3230](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3209-L3230).

shli(0, x) -> 0.

**Matched:** `arith.shli`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** LHS matches zero; even if shift count is out of range, replacing possible poison with zero is a valid refinement.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for shli(0, x) -> 0; out-of-range counts and enabled overflow/exact flags preserve poison refinement.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F070.lean](../Veir/Passes/ArithCanonicalize/F070.lean); `Veir.ArithCanonicalize.F070.valid`.

### F071: arith::ShLIOp::fold

[Original code: ArithOps.cpp:3209–3230](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3209-L3230).

Constant-fold shli: a << b.

**Matched:** `arith.shli`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands constant and shift count b is less than bit width; out-of-range shift count is not folded (no poison is materialized).

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for scalar constant-folded shli (left shift); source overflow/exact poison refines the APInt result, with explicit shift count < bit width guard.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F071.lean](../Veir/Passes/ArithCanonicalize/F071.lean); `Veir.ArithCanonicalize.F071.valid`.

### F072: arith::ShRUIOp::fold

[Original code: ArithOps.cpp:3236–3261](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3236-L3261).

shrui(x, 0) -> x.

**Matched:** `arith.shrui`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches zero.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for shrui(x, 0) -> x; out-of-range counts and enabled overflow/exact flags preserve poison refinement.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F072.lean](../Veir/Passes/ArithCanonicalize/F072.lean); `Veir.ArithCanonicalize.F072.valid`.

### F073: arith::ShRUIOp::fold

[Original code: ArithOps.cpp:3236–3261](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3236-L3261).

shrui(0, x) -> 0.

**Matched:** `arith.shrui`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** LHS matches zero; out-of-range shift count would be poison, so zero is a valid refinement.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for shrui(0, x) -> 0; out-of-range counts and enabled overflow/exact flags preserve poison refinement.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F073.lean](../Veir/Passes/ArithCanonicalize/F073.lean); `Veir.ArithCanonicalize.F073.valid`.

### F074: arith::ShRUIOp::fold

[Original code: ArithOps.cpp:3236–3261](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3236-L3261).

shrui(x, x) -> 0.

**Matched:** `arith.shrui`. **Replacement:** `arith.constant`.

**Conditions:** Operands identical; for in-range unsigned x, x >> x is zero; out-of-range source is poison and can refine to zero.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for shrui(x,x) -> 0; out-of-range/exact source poison refines zero, and in-range bitvector self-shift is zero.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F074.lean](../Veir/Passes/ArithCanonicalize/F074.lean); `Veir.ArithCanonicalize.F074.valid`.

### F075: arith::ShRUIOp::fold

[Original code: ArithOps.cpp:3236–3261](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3236-L3261).

Constant-fold shrui: logical a >> b.

**Matched:** `arith.shrui`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands constant and b < bit width; out-of-range shift count is not folded.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for scalar constant-folded shrui (logical right shift); source overflow/exact poison refines the APInt result, with explicit shift count < bit width guard.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F075.lean](../Veir/Passes/ArithCanonicalize/F075.lean); `Veir.ArithCanonicalize.F075.valid`.

### F076: arith::ShRSIOp::fold

[Original code: ArithOps.cpp:3267–3297](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3267-L3297).

shrsi(x, 0) -> x.

**Matched:** `arith.shrsi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches zero.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for shrsi(x, 0) -> x; out-of-range counts and enabled overflow/exact flags preserve poison refinement.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F076.lean](../Veir/Passes/ArithCanonicalize/F076.lean); `Veir.ArithCanonicalize.F076.valid`.

### F077: arith::ShRSIOp::fold

[Original code: ArithOps.cpp:3267–3297](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3267-L3297).

shrsi(0, x) -> 0.

**Matched:** `arith.shrsi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** LHS matches zero; out-of-range shift count yields poison and can refine to zero.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for shrsi(0, x) -> 0; out-of-range counts and enabled overflow/exact flags preserve poison refinement.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F077.lean](../Veir/Passes/ArithCanonicalize/F077.lean); `Veir.ArithCanonicalize.F077.valid`.

### F078: arith::ShRSIOp::fold

[Original code: ArithOps.cpp:3267–3297](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3267-L3297).

shrsi(x, x) -> 0.

**Matched:** `arith.shrsi`. **Replacement:** `arith.constant`.

**Conditions:** Operands identical; in-range x is nonnegative and x >> x is zero; out-of-range source can refine from poison.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for shrsi(x,x) -> 0; out-of-range/exact source poison refines zero, and in-range bitvector self-shift is zero.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F078.lean](../Veir/Passes/ArithCanonicalize/F078.lean); `Veir.ArithCanonicalize.F078.valid`.

### F079: arith::ShRSIOp::fold

[Original code: ArithOps.cpp:3267–3297](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3267-L3297).

shrsi(-1, x) -> -1.

**Matched:** `arith.shrsi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** LHS is all-ones integer constant; any in-range arithmetic shift is all ones; out-of-range source poison can refine to this constant.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for shrsi(all_ones, x) -> all_ones, with normalized bit-pattern matching and exact/out-of-range poison refinement.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F079.lean](../Veir/Passes/ArithCanonicalize/F079.lean); `Veir.ArithCanonicalize.F079.valid`.

### F080: arith::ShRSIOp::fold

[Original code: ArithOps.cpp:3267–3297](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3267-L3297).

Constant-fold shrsi: arithmetic a >> b.

**Matched:** `arith.shrsi`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands constant and b < bit width; out-of-range shift count is not folded.

**Status: Succeeded — proven.** Puddle Pattern.Valid proof for scalar constant-folded shrsi (arithmetic right shift); source overflow/exact poison refines the APInt result, with explicit shift count < bit width guard.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/F080.lean](../Veir/Passes/ArithCanonicalize/F080.lean); `Veir.ArithCanonicalize.F080.valid`.

### F081: arith::CmpIOp::fold

[Original code: ArithOps.cpp:2584–2658](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2584-L2658).

cmpi(pred, x, x) -> bool(pred is true on equal operands).

**Matched:** `arith.cmpi`. **Replacement:** `arith.constant`.

**Conditions:** LHS and RHS identical; true for eq/sle/sge/ule/uge, false for ne/slt/sgt/ult/ugt.

**Status: Succeeded — proven.** Two exact predicate partitions cover all ten cmpi(x,x) cases; both Pattern.Valid proofs quantify all integer widths and poison.

**Coverage:** scalar integer cmpi result i1; both true/false predicate partitions

**Lean:** [Veir/Passes/ArithCanonicalize/F081.lean](../Veir/Passes/ArithCanonicalize/F081.lean); `Veir.ArithCanonicalize.F081.pattern_true_valid; Veir.ArithCanonicalize.F081.pattern_false_valid`.

### F082: arith::CmpIOp::fold

[Original code: ArithOps.cpp:2584–2658](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2584-L2658).

cmpi(ne, extsi(x:i1), 0) -> x.

**Matched:** `arith.cmpi`, `arith.extsi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS zero; LHS is extsi from 1-bit integer (scalar or vector element width); predicate ne.

**Status: Succeeded — proven.** Scalar i1 extsi comparison to zero folds to source, for every wider integer width and poison.

**Coverage:** scalar i1-to-wider-integer extsi with arith.constant zero RHS; shaped and non-Arith constant producers outside current Puddle instance

**Lean:** [Veir/Passes/ArithCanonicalize/F082.lean](../Veir/Passes/ArithCanonicalize/F082.lean); `Veir.ArithCanonicalize.F082.valid`.

### F083: arith::CmpIOp::fold

[Original code: ArithOps.cpp:2584–2658](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2584-L2658).

cmpi(ne, extui(x:i1), 0) -> x.

**Matched:** `arith.cmpi`, `arith.extui`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS zero; LHS is extui from 1-bit integer; predicate ne.

**Status: Succeeded — proven.** Scalar i1 extui comparison to zero folds to source, including arbitrary nneg property and poison.

**Coverage:** scalar i1-to-wider-integer extui with arith.constant zero RHS; arbitrary nneg property; shaped and non-Arith constant producers outside current Puddle instance

**Lean:** [Veir/Passes/ArithCanonicalize/F083.lean](../Veir/Passes/ArithCanonicalize/F083.lean); `Veir.ArithCanonicalize.F083.valid`.

### F084: arith::CmpIOp::fold

[Original code: ArithOps.cpp:2584–2658](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2584-L2658).

cmpi(ne, x:i1, 0) -> x.

**Matched:** `arith.cmpi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS zero; LHS element type i1; predicate ne.

**Status: Succeeded — proven.** All-value Pattern.Valid proof for scalar i1 cmpi ne(x, 0) → x, including poison and both bit values.

**Coverage:** scalar i1 integer and arith.constant RHS subset of pinned fold

**Lean:** [Veir/Passes/ArithCanonicalize/F084.lean](../Veir/Passes/ArithCanonicalize/F084.lean); `Veir.ArithCanonicalize.F084.valid`.

### F085: arith::CmpIOp::fold

[Original code: ArithOps.cpp:2584–2658](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2584-L2658).

cmpi(eq, x:i1, 1) -> x.

**Matched:** `arith.cmpi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS one; LHS element type i1; predicate eq.

**Status: Succeeded — proven.** All-value Pattern.Valid proof for scalar i1 cmpi eq(x, 1) → x, including poison and both bit values.

**Coverage:** scalar i1 integer and arith.constant RHS subset of pinned fold

**Lean:** [Veir/Passes/ArithCanonicalize/F085.lean](../Veir/Passes/ArithCanonicalize/F085.lean); `Veir.ArithCanonicalize.F085.valid`.

### F086: arith::CmpIOp::fold

[Original code: ArithOps.cpp:2584–2658](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2584-L2658).

Move constant LHS to RHS and invert order predicate in-place: cmpi(pred,c,x) -> cmpi(invert_order(pred),x,c).

**Matched:** `arith.cmpi`, `arith.constant`. **Replacement:** `arith.cmpi`.

**Conditions:** Adaptor has constant LHS and nonconstant RHS; maps slt↔sgt, sle↔sge, ult↔ugt, ule↔uge; eq/ne unchanged; updates predicate and swaps operands, returns same op.

**Status: Succeeded — proven.** All ten integer predicates preserve meaning under operand swap and order-predicate swap; matcher rejects any ConstantLike RHS producer.

**Coverage:** scalar integer cmpi with arith.constant LHS and any non-ConstantLike RHS; other constant-like LHS producers and shaped variants outside this instance

**Lean:** [Veir/Passes/ArithCanonicalize/F086.lean](../Veir/Passes/ArithCanonicalize/F086.lean); `Veir.ArithCanonicalize.F086.valid`.

### F087: arith::CmpIOp::fold

[Original code: ArithOps.cpp:2584–2658](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2584-L2658).

Constant-fold cmpi using the selected signed/unsigned/equality predicate.

**Matched:** `arith.cmpi`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands fold to integer attributes; result is i1 with same shape as integer operands.

**Status: Succeeded — proven.** Both scalar arith.constant operands fold under all ten comparison predicates to a typed signless i1 constant.

**Coverage:** scalar integer cmpi with two arith.constant operands and signless i1 result; shaped and other folded constant producers outside this instance

**Lean:** [Veir/Passes/ArithCanonicalize/F087.lean](../Veir/Passes/ArithCanonicalize/F087.lean); `Veir.ArithCanonicalize.F087.valid`.

### F088: arith::NegFOp::fold

[Original code: ArithOps.cpp:1266–1276](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1266-L1276).

negf(negf(x)) -> x.

**Matched:** `arith.negf`. **Replacement:** existing SSA value.

**Conditions:** Operand is defined by arith.negf.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.negf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F089: arith::NegFOp::fold

[Original code: ArithOps.cpp:1266–1276](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1266-L1276).

Constant-fold negf by APFloat unary negation.

**Matched:** `arith.negf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Operand constant and its FP semantics have signed representation; otherwise conditional folder fails.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.negf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F090: arith::FlushDenormalsOp::fold

[Original code: ArithOps.cpp:1282–1298](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1282-L1298).

flush_denormals(flush_denormals(x)) -> flush_denormals(x) (return inner op result).

**Matched:** `arith.flush_denormals`. **Replacement:** existing SSA value.

**Conditions:** Operand is defined by arith.flush_denormals.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.flush_denormals. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F091: arith::FlushDenormalsOp::fold

[Original code: ArithOps.cpp:1282–1298](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1282-L1298).

Constant-fold flush_denormals: denormal -> signed zero; other constants unchanged.

**Matched:** `arith.flush_denormals`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Float constant; sign of denormal is preserved when creating zero.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.flush_denormals. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F092: arith::AddFOp::fold

[Original code: ArithOps.cpp:1304–1319](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1304-L1319).

addf(x, -0.0) -> x.

**Matched:** `arith.addf`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS is negative-zero float constant.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.addf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F093: arith::AddFOp::fold

[Original code: ArithOps.cpp:1304–1319](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1304-L1319).

addf(x, +0.0) -> x.

**Matched:** `arith.addf`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS is positive-zero float constant and fastmath contains nsz.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.addf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F094: arith::AddFOp::fold

[Original code: ArithOps.cpp:1304–1319](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1304-L1319).

Constant-fold addf with the op rounding mode.

**Matched:** `arith.addf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands FloatAttr-compatible constants; APFloat add uses converted arith rounding mode.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.addf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F095: arith::SubFOp::fold

[Original code: ArithOps.cpp:1330–1351](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1330-L1351).

subf(x, +0.0) -> x.

**Matched:** `arith.subf`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS is positive-zero float constant.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.subf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F096: arith::SubFOp::fold

[Original code: ArithOps.cpp:1330–1351](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1330-L1351).

subf(x, -0.0) -> x.

**Matched:** `arith.subf`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS negative zero and fastmath contains nsz.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.subf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F097: arith::SubFOp::fold

[Original code: ArithOps.cpp:1330–1351](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1330-L1351).

Constant-fold subf using op rounding mode.

**Matched:** `arith.subf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands constants; if target FP semantics lack signed representation and a < b (negative difference), APFloat path rejects the fold; otherwise subtraction is rounded per op mode.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.subf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F098: arith::MaximumFOp::fold

[Original code: ArithOps.cpp:1429–1439](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1429-L1439).

maximumf(x,x) -> x.

**Matched:** `arith.maximumf`. **Replacement:** existing SSA value.

**Conditions:** Operands identical.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.maximumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F099: arith::MaximumFOp::fold

[Original code: ArithOps.cpp:1429–1439](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1429-L1439).

maximumf(x, -infinity) -> x.

**Matched:** `arith.maximumf`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches -infinity float constant.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.maximumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F100: arith::MaximumFOp::fold

[Original code: ArithOps.cpp:1429–1439](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1429-L1439).

Constant-fold maximumf with llvm::maximum.

**Matched:** `arith.maximumf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands FloatAttr-compatible constants; APFloat semantics are those of llvm::maximum.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.maximumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F101: arith::MaxNumFOp::fold

[Original code: ArithOps.cpp:1445–1455](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1445-L1455).

maxnumf(x,x) -> x.

**Matched:** `arith.maxnumf`. **Replacement:** existing SSA value.

**Conditions:** Operands identical.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.maxnumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F102: arith::MaxNumFOp::fold

[Original code: ArithOps.cpp:1445–1455](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1445-L1455).

maxnumf(x, NaN) -> x.

**Matched:** `arith.maxnumf`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches NaN float constant.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.maxnumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F103: arith::MaxNumFOp::fold

[Original code: ArithOps.cpp:1445–1455](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1445-L1455).

Constant-fold maxnumf with llvm::maxnum.

**Matched:** `arith.maxnumf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands FloatAttr-compatible constants; APFloat semantics are those of llvm::maxnum.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.maxnumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F104: arith::MaximumNumFOp::fold

[Original code: ArithOps.cpp:1461–1471](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1461-L1471).

maximumnumf(x,x) -> x.

**Matched:** `arith.maximumnumf`. **Replacement:** existing SSA value.

**Conditions:** Operands identical.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.maximumnumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F105: arith::MaximumNumFOp::fold

[Original code: ArithOps.cpp:1461–1471](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1461-L1471).

maximumnumf(x, NaN) -> x.

**Matched:** `arith.maximumnumf`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches NaN float constant.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.maximumnumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F106: arith::MaximumNumFOp::fold

[Original code: ArithOps.cpp:1461–1471](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1461-L1471).

Constant-fold maximumnumf with llvm::maximumnum.

**Matched:** `arith.maximumnumf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands FloatAttr-compatible constants; APFloat semantics are those of llvm::maximumnum.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.maximumnumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F107: arith::MinimumFOp::fold

[Original code: ArithOps.cpp:1523–1533](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1523-L1533).

minimumf(x,x) -> x.

**Matched:** `arith.minimumf`. **Replacement:** existing SSA value.

**Conditions:** Operands identical.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.minimumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F108: arith::MinimumFOp::fold

[Original code: ArithOps.cpp:1523–1533](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1523-L1533).

minimumf(x, +infinity) -> x.

**Matched:** `arith.minimumf`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches +infinity float constant.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.minimumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F109: arith::MinimumFOp::fold

[Original code: ArithOps.cpp:1523–1533](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1523-L1533).

Constant-fold minimumf with llvm::minimum.

**Matched:** `arith.minimumf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands FloatAttr-compatible constants; APFloat semantics are those of llvm::minimum.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.minimumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F110: arith::MinNumFOp::fold

[Original code: ArithOps.cpp:1539–1549](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1539-L1549).

minnumf(x,x) -> x.

**Matched:** `arith.minnumf`. **Replacement:** existing SSA value.

**Conditions:** Operands identical.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.minnumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F111: arith::MinNumFOp::fold

[Original code: ArithOps.cpp:1539–1549](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1539-L1549).

minnumf(x, NaN) -> x.

**Matched:** `arith.minnumf`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches NaN float constant.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.minnumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F112: arith::MinNumFOp::fold

[Original code: ArithOps.cpp:1539–1549](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1539-L1549).

Constant-fold minnumf with llvm::minnum.

**Matched:** `arith.minnumf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands FloatAttr-compatible constants; APFloat semantics are those of llvm::minnum.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.minnumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F113: arith::MinimumNumFOp::fold

[Original code: ArithOps.cpp:1555–1565](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1555-L1565).

minimumnumf(x,x) -> x.

**Matched:** `arith.minimumnumf`. **Replacement:** existing SSA value.

**Conditions:** Operands identical.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.minimumnumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F114: arith::MinimumNumFOp::fold

[Original code: ArithOps.cpp:1555–1565](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1555-L1565).

minimumnumf(x, NaN) -> x.

**Matched:** `arith.minimumnumf`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches NaN float constant.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.minimumnumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F115: arith::MinimumNumFOp::fold

[Original code: ArithOps.cpp:1555–1565](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1555-L1565).

Constant-fold minimumnumf with llvm::minimumnum.

**Matched:** `arith.minimumnumf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands FloatAttr-compatible constants; APFloat semantics are those of llvm::minimumnum.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.minimumnumf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F116: arith::MaxSIOp::fold

[Original code: ArithOps.cpp:1477–1494](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1477-L1494).

maxsi(x,x) -> x.

**Matched:** `arith.maxsi`. **Replacement:** existing SSA value.

**Conditions:** Operands identical.

**Status: Succeeded — proven.** Pattern.Valid proof for the scalar upstream fold at every integer width, including poison semantics.

**Coverage:** scalar integer; all widths and signednesses

**Lean:** [Veir/Passes/ArithCanonicalize/F116.lean](../Veir/Passes/ArithCanonicalize/F116.lean); `Veir.ArithCanonicalize.F116.valid`.

### F117: arith::MaxSIOp::fold

[Original code: ArithOps.cpp:1477–1494](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1477-L1494).

maxsi(x, max signed value) -> return RHS.

**Matched:** `arith.maxsi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS is integer constant with stated extreme value.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for the typed scalar extremal constant fold; exact signed/unsigned bitpattern guard and poison refinement.

**Coverage:** scalar integer and arith.constant RHS subset of pinned fold

**Lean:** [Veir/Passes/ArithCanonicalize/F117.lean](../Veir/Passes/ArithCanonicalize/F117.lean); `Veir.ArithCanonicalize.F117.valid`.

### F118: arith::MaxSIOp::fold

[Original code: ArithOps.cpp:1477–1494](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1477-L1494).

maxsi(x, min signed value) -> return LHS.

**Matched:** `arith.maxsi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS is integer constant with stated extreme value.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for the typed scalar extremal constant fold; exact signed/unsigned bitpattern guard and poison refinement.

**Coverage:** scalar integer and arith.constant RHS subset of pinned fold

**Lean:** [Veir/Passes/ArithCanonicalize/F118.lean](../Veir/Passes/ArithCanonicalize/F118.lean); `Veir.ArithCanonicalize.F118.valid`.

### F119: arith::MaxSIOp::fold

[Original code: ArithOps.cpp:1477–1494](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1477-L1494).

Constant-fold maxsi to signed max.

**Matched:** `arith.maxsi`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands IntegerAttr-compatible constants.

**Status: Succeeded — proven.** Both scalar arith.constant operands fold to signed maximum at every integer width.

**Coverage:** scalar integer maxsi with two arith.constant operands; shaped and other folded constant producers outside this instance

**Lean:** [Veir/Passes/ArithCanonicalize/F119.lean](../Veir/Passes/ArithCanonicalize/F119.lean); `Veir.ArithCanonicalize.F119.valid`.

### F120: arith::MaxUIOp::fold

[Original code: ArithOps.cpp:1500–1517](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1500-L1517).

maxui(x,x) -> x.

**Matched:** `arith.maxui`. **Replacement:** existing SSA value.

**Conditions:** Operands identical.

**Status: Succeeded — proven.** Pattern.Valid proof for the scalar upstream fold at every integer width, including poison semantics.

**Coverage:** scalar integer; all widths and signednesses

**Lean:** [Veir/Passes/ArithCanonicalize/F120.lean](../Veir/Passes/ArithCanonicalize/F120.lean); `Veir.ArithCanonicalize.F120.valid`.

### F121: arith::MaxUIOp::fold

[Original code: ArithOps.cpp:1500–1517](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1500-L1517).

maxui(x, all-ones value) -> return RHS.

**Matched:** `arith.maxui`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS is integer constant with stated extreme value.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for the typed scalar extremal constant fold; exact signed/unsigned bitpattern guard and poison refinement.

**Coverage:** scalar integer and arith.constant RHS subset of pinned fold

**Lean:** [Veir/Passes/ArithCanonicalize/F121.lean](../Veir/Passes/ArithCanonicalize/F121.lean); `Veir.ArithCanonicalize.F121.valid`.

### F122: arith::MaxUIOp::fold

[Original code: ArithOps.cpp:1500–1517](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1500-L1517).

maxui(x, zero value) -> return LHS.

**Matched:** `arith.maxui`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS is integer constant with stated extreme value.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for the typed scalar extremal constant fold; exact signed/unsigned bitpattern guard and poison refinement.

**Coverage:** scalar integer and arith.constant RHS subset of pinned fold

**Lean:** [Veir/Passes/ArithCanonicalize/F122.lean](../Veir/Passes/ArithCanonicalize/F122.lean); `Veir.ArithCanonicalize.F122.valid`.

### F123: arith::MaxUIOp::fold

[Original code: ArithOps.cpp:1500–1517](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1500-L1517).

Constant-fold maxui to unsigned max.

**Matched:** `arith.maxui`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands IntegerAttr-compatible constants.

**Status: Succeeded — proven.** Both scalar arith.constant operands fold to unsigned maximum at every integer width.

**Coverage:** scalar integer maxui with two arith.constant operands; shaped and other folded constant producers outside this instance

**Lean:** [Veir/Passes/ArithCanonicalize/F123.lean](../Veir/Passes/ArithCanonicalize/F123.lean); `Veir.ArithCanonicalize.F123.valid`.

### F124: arith::MinSIOp::fold

[Original code: ArithOps.cpp:1571–1588](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1571-L1588).

minsi(x,x) -> x.

**Matched:** `arith.minsi`. **Replacement:** existing SSA value.

**Conditions:** Operands identical.

**Status: Succeeded — proven.** Pattern.Valid proof for the scalar upstream fold at every integer width, including poison semantics.

**Coverage:** scalar integer; all widths and signednesses

**Lean:** [Veir/Passes/ArithCanonicalize/F124.lean](../Veir/Passes/ArithCanonicalize/F124.lean); `Veir.ArithCanonicalize.F124.valid`.

### F125: arith::MinSIOp::fold

[Original code: ArithOps.cpp:1571–1588](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1571-L1588).

minsi(x, min signed value) -> return RHS.

**Matched:** `arith.minsi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS is integer constant with stated extreme value.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for the typed scalar extremal constant fold; exact signed/unsigned bitpattern guard and poison refinement.

**Coverage:** scalar integer and arith.constant RHS subset of pinned fold

**Lean:** [Veir/Passes/ArithCanonicalize/F125.lean](../Veir/Passes/ArithCanonicalize/F125.lean); `Veir.ArithCanonicalize.F125.valid`.

### F126: arith::MinSIOp::fold

[Original code: ArithOps.cpp:1571–1588](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1571-L1588).

minsi(x, max signed value) -> return LHS.

**Matched:** `arith.minsi`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS is integer constant with stated extreme value.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for the typed scalar extremal constant fold; exact signed/unsigned bitpattern guard and poison refinement.

**Coverage:** scalar integer and arith.constant RHS subset of pinned fold

**Lean:** [Veir/Passes/ArithCanonicalize/F126.lean](../Veir/Passes/ArithCanonicalize/F126.lean); `Veir.ArithCanonicalize.F126.valid`.

### F127: arith::MinSIOp::fold

[Original code: ArithOps.cpp:1571–1588](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1571-L1588).

Constant-fold minsi to signed min.

**Matched:** `arith.minsi`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands IntegerAttr-compatible constants.

**Status: Succeeded — proven.** Both scalar arith.constant operands fold to signed minimum at every integer width.

**Coverage:** scalar integer minsi with two arith.constant operands; shaped and other folded constant producers outside this instance

**Lean:** [Veir/Passes/ArithCanonicalize/F127.lean](../Veir/Passes/ArithCanonicalize/F127.lean); `Veir.ArithCanonicalize.F127.valid`.

### F128: arith::MinUIOp::fold

[Original code: ArithOps.cpp:1594–1611](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1594-L1611).

minui(x,x) -> x.

**Matched:** `arith.minui`. **Replacement:** existing SSA value.

**Conditions:** Operands identical.

**Status: Succeeded — proven.** Pattern.Valid proof for the scalar upstream fold at every integer width, including poison semantics.

**Coverage:** scalar integer; all widths and signednesses

**Lean:** [Veir/Passes/ArithCanonicalize/F128.lean](../Veir/Passes/ArithCanonicalize/F128.lean); `Veir.ArithCanonicalize.F128.valid`.

### F129: arith::MinUIOp::fold

[Original code: ArithOps.cpp:1594–1611](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1594-L1611).

minui(x, zero value) -> return RHS.

**Matched:** `arith.minui`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS is integer constant with stated extreme value.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for the typed scalar extremal constant fold; exact signed/unsigned bitpattern guard and poison refinement.

**Coverage:** scalar integer and arith.constant RHS subset of pinned fold

**Lean:** [Veir/Passes/ArithCanonicalize/F129.lean](../Veir/Passes/ArithCanonicalize/F129.lean); `Veir.ArithCanonicalize.F129.valid`.

### F130: arith::MinUIOp::fold

[Original code: ArithOps.cpp:1594–1611](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1594-L1611).

minui(x, all-ones value) -> return LHS.

**Matched:** `arith.minui`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS is integer constant with stated extreme value.

**Status: Succeeded — proven.** All-width Pattern.Valid proof for the typed scalar extremal constant fold; exact signed/unsigned bitpattern guard and poison refinement.

**Coverage:** scalar integer and arith.constant RHS subset of pinned fold

**Lean:** [Veir/Passes/ArithCanonicalize/F130.lean](../Veir/Passes/ArithCanonicalize/F130.lean); `Veir.ArithCanonicalize.F130.valid`.

### F131: arith::MinUIOp::fold

[Original code: ArithOps.cpp:1594–1611](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1594-L1611).

Constant-fold minui to unsigned min.

**Matched:** `arith.minui`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands IntegerAttr-compatible constants.

**Status: Succeeded — proven.** Both scalar arith.constant operands fold to unsigned minimum at every integer width.

**Coverage:** scalar integer minui with two arith.constant operands; shaped and other folded constant producers outside this instance

**Lean:** [Veir/Passes/ArithCanonicalize/F131.lean](../Veir/Passes/ArithCanonicalize/F131.lean); `Veir.ArithCanonicalize.F131.valid`.

### F132: arith::MulFOp::fold

[Original code: ArithOps.cpp:1617–1642](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1617-L1642).

mulf(x, 1.0) -> x.

**Matched:** `arith.mulf`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches one float.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.mulf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F133: arith::MulFOp::fold

[Original code: ArithOps.cpp:1617–1642](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1617-L1642).

mulf(x, 0.0) -> 0.0 when one operand is zero.

**Matched:** `arith.mulf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Fastmath contains both nnan and nsz; not both operands are constants; either operand may be any signed zero; returns the zero operand to preserve its sign.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.mulf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F134: arith::MulFOp::fold

[Original code: ArithOps.cpp:1617–1642](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1617-L1642).

Constant-fold mulf using op rounding mode.

**Matched:** `arith.mulf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands FloatAttr constants; the constant path preserves signed zero; APFloat multiply uses the op rounding mode.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.mulf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F135: arith::DivFOp::fold

[Original code: ArithOps.cpp:1653–1665](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1653-L1665).

divf(x, 1.0) -> x.

**Matched:** `arith.divf`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** RHS matches one float.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.divf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F136: arith::DivFOp::fold

[Original code: ArithOps.cpp:1653–1665](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1653-L1665).

Constant-fold divf using op rounding mode.

**Matched:** `arith.divf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands FloatAttr constants; APFloat divide uses op rounding mode.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.divf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F137: arith::RemFOp::fold

[Original code: ArithOps.cpp:1676–1686](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1676-L1686).

Constant-fold remf using APFloat remainder (mod), with result sign of LHS.

**Matched:** `arith.remf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands FloatAttr constants; operation calls APFloat::mod.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.remf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F140: arith::ExtUIOp::fold

[Original code: ArithOps.cpp:1819–1835](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1819-L1835).

Fold nested extui by bypassing inner extui; preserve the inner nneg attribute on the outer op.

**Matched:** `arith.extui`. **Replacement:** `arith.extui`.

**Conditions:** Operand is defined by extui; mutates operand and nneg in place; inner nneg describes surviving source.

**Status: Succeeded — proven.** Pattern.Valid proof that nested zero extension equals direct extension with the inner nneg flag retained; outer nneg is vacuous after the first widening.

**Coverage:** scalar integer; all strictly increasing source, middle, and result widths; both nneg flags

**Lean:** [Veir/Passes/ArithCanonicalize/F140.lean](../Veir/Passes/ArithCanonicalize/F140.lean); `Veir.ArithCanonicalize.F140.valid`.

### F141: arith::ExtUIOp::fold

[Original code: ArithOps.cpp:1819–1835](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1819-L1835).

Constant-fold extui by zero-extending each integer element.

**Matched:** `arith.extui`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Integer constant; target integer element width is used; constFoldCastOp succeeds only when conversion is supported.

**Status: Succeeded — proven.** Pattern.Valid proof of scalar integer constant-folding extui; the replacement attribute is constructed from the exact BitVec cast result, including source poison from nneg flags.

**Coverage:** scalar integer; all legal source/result widths; nneg flags

**Lean:** [Veir/Passes/ArithCanonicalize/F141.lean](../Veir/Passes/ArithCanonicalize/F141.lean); `Veir.ArithCanonicalize.F141.valid`.

### F142: arith::ExtSIOp::fold

[Original code: ArithOps.cpp:1849–1862](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1849-L1862).

Fold nested extsi by bypassing inner extsi.

**Matched:** `arith.extsi`. **Replacement:** `arith.extsi`.

**Conditions:** Operand is defined by extsi; mutates operand in place.

**Status: Succeeded — proven.** Pattern.Valid proof that nested sign extension equals direct sign extension, using all-width BitVec signed-value composition and strict verified width ordering.

**Coverage:** scalar integer; all strictly increasing source, middle, and result widths

**Lean:** [Veir/Passes/ArithCanonicalize/F142.lean](../Veir/Passes/ArithCanonicalize/F142.lean); `Veir.ArithCanonicalize.F142.valid`.

### F143: arith::ExtSIOp::fold

[Original code: ArithOps.cpp:1849–1862](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1849-L1862).

Constant-fold extsi by sign-extending each integer element.

**Matched:** `arith.extsi`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Integer constant; target integer element width; conversion supported.

**Status: Succeeded — proven.** Pattern.Valid proof of scalar integer constant-folding extsi; the replacement attribute is constructed from the exact BitVec cast result, including source poison from none flags.

**Coverage:** scalar integer; all legal source/result widths; none flags

**Lean:** [Veir/Passes/ArithCanonicalize/F143.lean](../Veir/Passes/ArithCanonicalize/F143.lean); `Veir.ArithCanonicalize.F143.valid`.

### F144: arith::ExtFOp::fold

[Original code: ArithOps.cpp:1883–1912](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1883-L1912).

extf(truncf(x)) -> x.

**Matched:** `arith.extf`, `arith.truncf`. **Replacement:** existing SSA value.

**Conditions:** Operand is truncf(x) and truncf operand type equals extf result type; both truncf and extf fastmath contain contract.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.extf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F145: arith::ExtFOp::fold

[Original code: ArithOps.cpp:1883–1912](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1883-L1912).

Constant-fold extf to target FP semantics.

**Matched:** `arith.extf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** FloatAttr constant; convertFloatValue to target semantics must succeed without information loss; otherwise no fold.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.extf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F146: arith::ScalingExtFOp::fold

[Original code: ArithOps.cpp:1988–2009](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1988-L2009).

Constant-fold scaling_extf(in, scale) according to mulf(extf(in), extf(scale)).

**Matched:** `arith.scaling_extf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Scale element type is exactly f8E8M0FNU; both operands are compatible scalar/dense FP constants; static shaped result and equal element counts required for dense operands. Both widenings must be lossless; multiplication uses default rounding. Dense splats and non-splats share the same elementwise semantic rule. Poison propagation is documented separately in G006.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.scaling_extf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F147a: arith::TruncIOp::fold

[Original code: ArithOps.cpp:2024–2057](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2024-L2057).

trunci(extui(x)) -> trunci(x), in place.

**Matched:** `arith.trunci`, `arith.extui`. **Replacement:** `arith.trunci`.

**Conditions:** Source element width is greater than trunc result element width; source is unwrapped from one extui/extsi.

**Status: Succeeded — proven.** Pattern.Valid proof that trunci(unsigned extension(x)) folds to trunci(x), preserving original nsw/nuw flags and the extension poison behavior.

**Coverage:** scalar integer; all widths satisfying result < source < extension; arbitrary original flags

**Lean:** [Veir/Passes/ArithCanonicalize/F147a.lean](../Veir/Passes/ArithCanonicalize/F147a.lean); `Veir.ArithCanonicalize.F147a.valid`.

### F147b: arith::TruncIOp::fold

[Original code: ArithOps.cpp:2024–2057](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2024-L2057).

trunci(extsi(x)) -> trunci(x), in place.

**Matched:** `arith.trunci`, `arith.extsi`. **Replacement:** `arith.trunci`.

**Conditions:** Source element width is greater than trunc result element width; source is unwrapped from one extui/extsi.

**Status: Succeeded — proven.** Pattern.Valid proof that trunci(signed extension(x)) folds to trunci(x), preserving original nsw/nuw flags and the extension poison behavior.

**Coverage:** scalar integer; all widths satisfying result < source < extension; arbitrary original flags

**Lean:** [Veir/Passes/ArithCanonicalize/F147b.lean](../Veir/Passes/ArithCanonicalize/F147b.lean); `Veir.ArithCanonicalize.F147b.valid`.

### F148a: arith::TruncIOp::fold

[Original code: ArithOps.cpp:2024–2057](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2024-L2057).

trunci(extui(x)) -> x.

**Matched:** `arith.trunci`, `arith.extui`. **Replacement:** existing SSA value.

**Conditions:** Source element type equals trunc result element type.

**Status: Succeeded — proven.** Pattern.Valid proof of trunci(extui(x)) to x at the original width, including arbitrary inner nneg and outer nsw/nuw poison behavior.

**Coverage:** scalar integer; every strictly widening extension and reverse truncation; all flags

**Lean:** [Veir/Passes/ArithCanonicalize/F148a.lean](../Veir/Passes/ArithCanonicalize/F148a.lean); `Veir.ArithCanonicalize.F148a.valid`.

### F148b: arith::TruncIOp::fold

[Original code: ArithOps.cpp:2024–2057](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2024-L2057).

trunci(extsi(x)) -> x.

**Matched:** `arith.trunci`, `arith.extsi`. **Replacement:** existing SSA value.

**Conditions:** Source element type equals trunc result element type.

**Status: Succeeded — proven.** Pattern.Valid proof of trunci(extsi(x)) to x at the original width, including arbitrary outer nsw/nuw poison behavior.

**Coverage:** scalar integer; every strictly widening extension and reverse truncation; all flags

**Lean:** [Veir/Passes/ArithCanonicalize/F148b.lean](../Veir/Passes/ArithCanonicalize/F148b.lean); `Veir.ArithCanonicalize.F148b.valid`.

### F149: arith::TruncIOp::fold

[Original code: ArithOps.cpp:2024–2057](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2024-L2057).

trunci(trunci(x)) -> trunci(x), in place.

**Matched:** `arith.trunci`. **Replacement:** `arith.trunci`.

**Conditions:** Input is defined by trunci; outer operand is reset to inner operand.

**Status: Counterexample.** Direct Lean proof that nested trunci bypass violates Pattern.Valid: source i16 255 → i8 -1 → i4 nsw -1 is defined; direct i16 → i4 nsw is poison.

**Coverage:** general scalar integer Puddle pattern; concrete i16→i8→i4 witness

**Lean:** [Veir/Passes/ArithCanonicalize/F149.lean](../Veir/Passes/ArithCanonicalize/F149.lean); `Veir.ArithCanonicalize.F149.pattern_not_valid`.

### F150: arith::TruncIOp::fold

[Original code: ArithOps.cpp:2024–2057](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2024-L2057).

Constant-fold trunci to low result-width bits.

**Matched:** `arith.trunci`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Integer constant; truncation to result element bit width.

**Status: Succeeded — proven.** Pattern.Valid proof of scalar integer constant-folding trunci; the replacement attribute is constructed from the exact BitVec cast result, including source poison from nsw/nuw flags.

**Coverage:** scalar integer; all legal source/result widths; nsw/nuw flags

**Lean:** [Veir/Passes/ArithCanonicalize/F150.lean](../Veir/Passes/ArithCanonicalize/F150.lean); `Veir.ArithCanonicalize.F150.valid`.

### F151: arith::TruncFOp::fold

[Original code: ArithOps.cpp:2082–2120](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2082-L2120).

truncf(extf(x)) -> truncf(x), in place.

**Matched:** `arith.truncf`, `arith.extf`. **Replacement:** `arith.truncf`.

**Conditions:** Source-to-intermediate FP conversion is lossless including signaling NaNs and signed zero; source width > result width.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.truncf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F152: arith::TruncFOp::fold

[Original code: ArithOps.cpp:2082–2120](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2082-L2120).

truncf(extf(x)) -> x.

**Matched:** `arith.truncf`, `arith.extf`. **Replacement:** existing SSA value.

**Conditions:** Source-to-intermediate FP conversion is lossless; source type equals trunc result element type.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.truncf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F153: arith::TruncFOp::fold

[Original code: ArithOps.cpp:2082–2120](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2082-L2120).

Constant-fold truncf with its rounding mode.

**Matched:** `arith.truncf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** FloatAttr constant; convertFloatValue at the operation rounding mode must have no information loss and APFloat status opOK. Unrepresentable infinity/NaN is rejected before conversion. Inexact, overflowing, or otherwise lossy conversions do not fold.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.truncf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F154: arith::ConvertFOp::fold

[Original code: ArithOps.cpp:2145–2161](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2145-L2161).

Constant-fold convertf to target FP semantics with its rounding mode.

**Matched:** `arith.convertf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** FloatAttr constant; source and destination have equal bitwidth but different semantics. Conversion at the operation rounding mode must lose no information and return APFloat status opOK; unrepresentable special values are rejected.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.convertf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F155: arith::ScalingTruncFOp::fold

[Original code: ArithOps.cpp:2192–2219](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2192-L2219).

Constant-fold scaling_truncf(in,scale) as truncf(in / extf(scale)).

**Matched:** `arith.scaling_truncf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Scale element type is exactly f8E8M0FNU; both operands are compatible scalar/dense FP constants; static shape and equal element counts required for dense operands. Scale extension to input semantics must be lossless; division uses default rounding and final truncation uses the operation rounding mode; conversion must succeed. Poison propagation is documented separately in G006.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.scaling_truncf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F156: arith::UIToFPOp::fold

[Original code: ArithOps.cpp:2271–2283](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2271-L2283).

Constant-fold uitofp by unsigned APInt-to-APFloat conversion (nearest ties to even).

**Matched:** `arith.uitofp`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** IntegerAttr constant; destination float semantics available.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.uitofp. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F157: arith::SIToFPOp::fold

[Original code: ArithOps.cpp:2298–2315](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2298-L2315).

Constant-fold sitofp by signed APInt-to-APFloat conversion (nearest ties to even).

**Matched:** `arith.sitofp`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** IntegerAttr constant; negative input is rejected when target FP semantics have no signed representation; otherwise target semantics available.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.sitofp. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F158: arith::FPToUIOp::fold

[Original code: ArithOps.cpp:2330–2342](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2330-L2342).

Constant-fold fptoui by conversion toward zero to unsigned result width.

**Matched:** `arith.fptoui`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** FloatAttr constant; APFloat conversion must not return opInvalidOp (value representable under conversion).

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.fptoui. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F159: arith::FPToSIOp::fold

[Original code: ArithOps.cpp:2352–2364](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2352-L2364).

Constant-fold fptosi by conversion toward zero to signed result width.

**Matched:** `arith.fptosi`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** FloatAttr constant; APFloat conversion must not return opInvalidOp (value representable under conversion).

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.fptosi. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F160: arith::IndexCastOp::fold

[Original code: ArithOps.cpp:2397–2421](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2397-L2421).

Constant-fold index_cast with sign extension/truncation to target storage width.

**Matched:** `arith.index_cast`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Integer constant; result width is integer result width or index internal storage width 64.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks the Arith index-cast opcodes and target-dependent index runtime semantics. A proof requires an index width/data-layout model, rather than silently treating index as a fixed integer width.

**Coverage:** Full upstream rule

### F161: arith::IndexCastOp::fold

[Original code: ArithOps.cpp:2397–2421](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2397-L2421).

index_cast(index_cast(x:A):B):A -> x.

**Matched:** `arith.index_cast`. **Replacement:** existing SSA value.

**Conditions:** Input is same op; inner source type exactly outer result type; intermediate width >= source width (index width treated as 64); avoids lossy narrower inner cast.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks the Arith index-cast opcodes and target-dependent index runtime semantics. A proof requires an index width/data-layout model, rather than silently treating index as a fixed integer width.

**Coverage:** Full upstream rule

### F162: arith::IndexCastUIOp::fold

[Original code: ArithOps.cpp:2437–2461](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2437-L2461).

Constant-fold index_castui with zero extension/truncation to target storage width.

**Matched:** `arith.index_castui`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Integer constant; result width is integer result width or index internal storage width 64.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks the Arith index-cast opcodes and target-dependent index runtime semantics. A proof requires an index width/data-layout model, rather than silently treating index as a fixed integer width.

**Coverage:** Full upstream rule

### F163: arith::IndexCastUIOp::fold

[Original code: ArithOps.cpp:2437–2461](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2437-L2461).

index_castui(index_castui(x:A):B):A -> x.

**Matched:** `arith.index_castui`. **Replacement:** existing SSA value.

**Conditions:** Input is same op; inner source type exactly outer result type; intermediate width >= source width (index width treated as 64).

**Status: Cannot be implemented with current Puddle support.** VeIR lacks the Arith index-cast opcodes and target-dependent index runtime semantics. A proof requires an index width/data-layout model, rather than silently treating index as a fixed integer width.

**Coverage:** Full upstream rule

### F164: arith::BitcastOp::fold

[Original code: ArithOps.cpp:2484–2515](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2484-L2515).

Constant-fold shaped dense elements by bitcasting their element type.

**Matched:** `arith.bitcast`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Operand is DenseElementsAttr; result is shaped; DenseElementsAttr::bitcast must accept result element type.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks arith.bitcast and its floating/integer/shaped bitcast interpretation. The restricted LLVM scalar int/byte/pointer bitcast interpretation does not cover this upstream Arith rule.

**Coverage:** Full upstream rule

### F165: arith::BitcastOp::fold

[Original code: ArithOps.cpp:2484–2515](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2484-L2515).

bitcast(poison) -> poison.

**Matched:** `arith.bitcast`, `ub.poison`. **Replacement:** `ub.poison`.

**Conditions:** Operand is UB poison and result is scalar (shaped poison path not handled here).

**Status: Cannot be implemented with current Puddle support.** VeIR lacks arith.bitcast and its floating/integer/shaped bitcast interpretation. The restricted LLVM scalar int/byte/pointer bitcast interpretation does not cover this upstream Arith rule.

**Coverage:** Full upstream rule

### F166: arith::BitcastOp::fold

[Original code: ArithOps.cpp:2484–2515](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2484-L2515).

Constant-fold scalar integer/float bitcast by preserving raw bits.

**Matched:** `arith.bitcast`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Operand is IntegerAttr or FloatAttr; result scalar integer/float width equals source bits; result type determines IntegerAttr vs FloatAttr interpretation.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks arith.bitcast and its floating/integer/shaped bitcast interpretation. The restricted LLVM scalar int/byte/pointer bitcast interpretation does not cover this upstream Arith rule.

**Coverage:** Full upstream rule

### F167: arith::CmpFOp::fold

[Original code: ArithOps.cpp:2717–2732](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2717-L2732).

Constant-fold cmpf when both operands are float constants, applying the selected floating predicate to APFloat comparison, including unordered/NaN cases.

**Matched:** `arith.cmpf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Both operands are scalar FloatAttr constants; evaluate the selected predicate (including AlwaysTrue/AlwaysFalse and unordered comparisons) on APFloat::compare. The separate single-NaN branches below do not require the other operand to be constant.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.cmpf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F167a: arith::CmpFOp::fold

[Original code: ArithOps.cpp:2717–2732](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2717-L2732).

cmpf(pred, a, b) -> the predicate result for unordered operands when LHS is a constant NaN, even if the other operand is unknown.

**Matched:** `arith.cmpf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** LHS fold-adaptor attribute is a scalar FloatAttr NaN. The implementation substitutes it for the other attribute locally and evaluates the predicate: unordered predicates (UEQ/UGT/UGE/ULT/ULE/UNE/UNO) and AlwaysTrue yield true; ordered predicates and AlwaysFalse yield false.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.cmpf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F167b: arith::CmpFOp::fold

[Original code: ArithOps.cpp:2717–2732](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L2717-L2732).

cmpf(pred, a, b) -> the predicate result for unordered operands when RHS is a constant NaN, even if the other operand is unknown.

**Matched:** `arith.cmpf`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** RHS fold-adaptor attribute is a scalar FloatAttr NaN. The implementation substitutes it for the other attribute locally and evaluates the predicate: unordered predicates (UEQ/UGT/UGE/ULT/ULE/UNE/UNO) and AlwaysTrue yield true; ordered predicates and AlwaysFalse yield false.

**Status: Cannot be implemented with current Puddle support.** VeIR lacks Arith floating-point interpreter semantics for arith.cmpf. RuntimeValue.float does not supply APFloat arithmetic, conversions, rounding modes, fast-math, or exact NaN/signed-zero semantics. Failed interpretation is not used to claim a vacuous Valid proof.

**Coverage:** Full upstream rule

### F168: arith::SelectOp::fold

[Original code: ArithOps.cpp:3074–3151](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3074-L3151).

select(cond, trueVal, falseVal) -> trueVal when arms are the same SSA value.

**Matched:** `arith.select`. **Replacement:** existing SSA value.

**Conditions:** True and false SSA values identical.

**Status: Succeeded — proven.** Pattern.Valid proof for the scalar upstream fold at every integer width, including poison semantics.

**Coverage:** scalar integer; all widths and signednesses

**Lean:** [Veir/Passes/ArithCanonicalize/F168.lean](../Veir/Passes/ArithCanonicalize/F168.lean); `Veir.ArithCanonicalize.F168.valid`.

### F169: arith::SelectOp::fold

[Original code: ArithOps.cpp:3074–3151](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3074-L3151).

select(true, t, f) -> t.

**Matched:** `arith.select`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** Condition folds to one.

**Status: Succeeded — proven.** Pattern.Valid proof for the scalar upstream fold at every integer width, including poison semantics.

**Coverage:** scalar integer; all widths and signednesses

**Lean:** [Veir/Passes/ArithCanonicalize/F169.lean](../Veir/Passes/ArithCanonicalize/F169.lean); `Veir.ArithCanonicalize.F169.valid`.

### F170: arith::SelectOp::fold

[Original code: ArithOps.cpp:3074–3151](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3074-L3151).

select(false, t, f) -> f.

**Matched:** `arith.select`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** Condition folds to zero.

**Status: Succeeded — proven.** Pattern.Valid proof for the scalar upstream fold at every integer width, including poison semantics.

**Coverage:** scalar integer; all widths and signednesses

**Lean:** [Veir/Passes/ArithCanonicalize/F170.lean](../Veir/Passes/ArithCanonicalize/F170.lean); `Veir.ArithCanonicalize.F170.valid`.

### F171: arith::SelectOp::fold

[Original code: ArithOps.cpp:3074–3151](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3074-L3151).

select(cond, poison, x) -> x.

**Matched:** `arith.select`, `ub.poison`. **Replacement:** existing SSA value.

**Conditions:** True arm is fully poison.

**Status: Succeeded — proven.** Pattern.Valid proof for the fully poison integer arm represented by llvm.mlir.poison, the operation used by VeIR integer poison materialization.

**Coverage:** scalar integer; all widths and signednesses; llvm.mlir.poison producer

**Lean:** [Veir/Passes/ArithCanonicalize/F171.lean](../Veir/Passes/ArithCanonicalize/F171.lean); `Veir.ArithCanonicalize.F171.valid`.

### F172: arith::SelectOp::fold

[Original code: ArithOps.cpp:3074–3151](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3074-L3151).

select(cond, x, poison) -> x.

**Matched:** `arith.select`, `ub.poison`. **Replacement:** existing SSA value.

**Conditions:** False arm is fully poison.

**Status: Succeeded — proven.** Pattern.Valid proof for the fully poison integer arm represented by llvm.mlir.poison, the operation used by VeIR integer poison materialization.

**Coverage:** scalar integer; all widths and signednesses; llvm.mlir.poison producer

**Lean:** [Veir/Passes/ArithCanonicalize/F172.lean](../Veir/Passes/ArithCanonicalize/F172.lean); `Veir.ArithCanonicalize.F172.valid`.

### F173: arith::SelectOp::fold

[Original code: ArithOps.cpp:3074–3151](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3074-L3151).

select(cond, true, false) -> cond.

**Matched:** `arith.select`, `arith.constant`. **Replacement:** existing SSA value.

**Conditions:** Result type is signless i1; true arm constant one and false arm constant zero.

**Status: Succeeded — proven.** Pattern.Valid proof of select(cond, true, false) to cond, with exact signless-i1 type guard and poison semantics.

**Coverage:** scalar signless i1; all condition values including poison

**Lean:** [Veir/Passes/ArithCanonicalize/F173.lean](../Veir/Passes/ArithCanonicalize/F173.lean); `Veir.ArithCanonicalize.F173.valid`.

### F174a: arith::SelectOp::fold

[Original code: ArithOps.cpp:3074–3151](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3074-L3151).

select(cmpi eq, a, b) with arms {a,b} -> false arm.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** existing SSA value.

**Conditions:** Condition is cmpi eq; true and false arms match the cmpi operands in either order.

**Status: Succeeded — proven.** Two Pattern.Valid proofs cover both select arm orders for cmpi eq, including poison inputs.

**Coverage:** scalar integer; all widths and signednesses; both arm orders

**Lean:** [Veir/Passes/ArithCanonicalize/F174a.lean](../Veir/Passes/ArithCanonicalize/F174a.lean); `Veir.ArithCanonicalize.F174a.valid; Veir.ArithCanonicalize.F174a.valid_swapped`.

### F174b: arith::SelectOp::fold

[Original code: ArithOps.cpp:3074–3151](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3074-L3151).

select(cmpi ne, a, b) with arms {a,b} -> true arm.

**Matched:** `arith.select`, `arith.cmpi`. **Replacement:** existing SSA value.

**Conditions:** Condition is cmpi ne; true and false arms match the cmpi operands in either order.

**Status: Succeeded — proven.** Two Pattern.Valid proofs cover both select arm orders for cmpi ne, including poison inputs.

**Coverage:** scalar integer; all widths and signednesses; both arm orders

**Lean:** [Veir/Passes/ArithCanonicalize/F174b.lean](../Veir/Passes/ArithCanonicalize/F174b.lean); `Veir.ArithCanonicalize.F174b.valid; Veir.ArithCanonicalize.F174b.valid_swapped`.

### F175: arith::SelectOp::fold

[Original code: ArithOps.cpp:3074–3151](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L3074-L3151).

Constant-fold select elementwise for a non-splat dense condition and dense true/false arms.

**Matched:** `arith.select`, `arith.constant`. **Replacement:** `arith.constant`.

**Conditions:** Condition, true arm, and false arm are DenseElementsAttr; condition shape is static; each BoolAttr chooses corresponding arm element.

**Status: Cannot be implemented with current Puddle support.** This rule specifically requires non-splat dense vector/tensor conditions and dense result attributes. RuntimeValue has no shaped lane values and Arith verification/interpreting is scalar integer only. There is no scalar instance of this branch.

**Coverage:** Dense vector/tensor rule

### G001: OpTrait::IsCommutative::foldTrait

[Original code: Operation.cpp:863–878](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/IR/Operation.cpp#L863-L878).

For commutative Arith ops, move constant operands to the end in-place, preserving relative order of nonconstant and constant operands.

**Matched:** `arith.addi`, `arith.addui_extended`, `arith.muli`, `arith.mulsi_extended`, `arith.mului_extended`, `arith.andi`, `arith.ori`, `arith.xori`, `arith.addf`, `arith.maximumf`, `arith.maxnumf`, `arith.maximumnumf`, `arith.maxsi`, `arith.maxui`, `arith.minimumf`, `arith.minnumf`, `arith.minimumnumf`, `arith.minsi`, `arith.minui`, `arith.mulf`. **Replacement:** `arith.addi`, `arith.addui_extended`, `arith.muli`, `arith.mulsi_extended`, `arith.mului_extended`, `arith.andi`, `arith.ori`, `arith.xori`, `arith.addf`, `arith.maximumf`, `arith.maxnumf`, `arith.maximumnumf`, `arith.maxsi`, `arith.maxui`, `arith.minimumf`, `arith.minnumf`, `arith.minimumnumf`, `arith.minsi`, `arith.minui`, `arith.mulf`.

**Conditions:** At least two operands; operation has Commutative trait; fold adaptor marks constants by non-null attributes; stable partition changes operand order only if a constant precedes a nonconstant.

**Status: Succeeded — proven.** All-width Pattern.Valid for scalar addi, muli, andi, ori (preserving disjoint), xori, maxsi, maxui, minsi, minui via the parameterized theorem; also exact two-result addui_extended, mulsi_extended, mului_extended patterns with `pattern_addui_extended_valid`, `pattern_mulsi_extended_valid`, `pattern_mului_extended_valid`. Original properties and both extended results are preserved. RHS ConstantLike producer is rejected to retain stable constant ordering.

**Coverage:** 12 scalar integer Arith commutative operations; shaped and FP variants remain unsupported by the current Puddle integer model and are not claimed by these theorems

**Lean:** [Veir/Passes/ArithCanonicalize/G001.lean](../Veir/Passes/ArithCanonicalize/G001.lean); `Veir.ArithCanonicalize.G001.pattern_valid`.

### G002: OpTrait::IsIdempotent::foldTrait

[Original code: Operation.cpp:880–892](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/IR/Operation.cpp#L880-L892).

andi(x,x) -> x; ori(x,x) -> x.

**Matched:** `arith.andi`, `arith.ori`. **Replacement:** existing SSA value.

**Conditions:** Operation has Idempotent trait and binary operands are the same SSA value. Generic helper also handles unary idempotent op nested with itself, but no Arith idempotent op is unary.

**Status: Succeeded — proven.** Two Puddle Pattern.Valid proofs for generic idempotence: andi(x,x) and ori(x,x), including poison and the VeIR OR disjoint flag.

**Coverage:** all scalar integer bit widths and signednesses modeled by VeIR

**Lean:** [Veir/Passes/ArithCanonicalize/G002.lean](../Veir/Passes/ArithCanonicalize/G002.lean); `Veir.ArithCanonicalize.G002.andValid; Veir.ArithCanonicalize.G002.orValid`.

### G003: CastOpInterface::foldTrait (identity bitcast)

[Original code: CastInterfaces.cpp:20–36](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Interfaces/CastInterfaces.cpp#L20-L36).

arith.bitcast(x : T) : T -> x. The cast-interface trait forwards all operands when operand and result type lists agree exactly. Among verified Arith operations this identity case is available for bitcast; width-changing casts and int/float or int/index casts cannot have identical types, and convertf explicitly rejects identical element types.

**Matched:** `arith.bitcast`. **Replacement:** existing SSA value.

**Conditions:** Nonempty operands and identical operand/result type lists; inherited CastOpInterface trait. For shaped bitcast the entire types (not only element widths) must agree.

**Status: Cannot be implemented with current Puddle support.** VeIR has no arith.bitcast opcode or its float/integer/shaped runtime semantics. Adding a vacuous identity proof over failed interpretation would not implement the upstream rule.

**Coverage:** Full upstream bitcast identity

### G004: CommonFolders binary poison propagation

[Original code: CommonFolders.h:43–66](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/include/mlir/Dialect/CommonFolders.h#L43-L66).

For the listed binary operations, an operand folded to ub.poison yields poison; the other operand need not be constant. Extended arithmetic yields poison for both results (addui/subui have an explicit two-result poison branch).

**Matched:** `arith.addi`, `arith.addui_extended`, `arith.subui_extended`, `arith.subi`, `arith.muli`, `arith.mulsi_extended`, `arith.mului_extended`, `arith.divui`, `arith.divsi`, `arith.ceildivui`, `arith.ceildivsi`, `arith.floordivsi`, `arith.remui`, `arith.remsi`, `arith.andi`, `arith.ori`, `arith.xori`, `arith.addf`, `arith.subf`, `arith.maximumf`, `arith.maxnumf`, `arith.maximumnumf`, `arith.maxsi`, `arith.maxui`, `arith.minimumf`, `arith.minnumf`, `arith.minimumnumf`, `arith.minsi`, `arith.minui`, `arith.mulf`, `arith.divf`, `arith.remf`, `ub.poison`. **Replacement:** `ub.poison`.

**Conditions:** The operation-specific earlier folds must not already have succeeded; the default PoisonAttr helper specialization recognizes a fully poisoned fold-adaptor attribute. Caller-side error flags remain false when the helper bypasses calculation. Excludes shli/shrsi/shrui (their bounded flag remains false, rejecting the fold), cmpi (explicit-result-type helper disables poison propagation and TypedAttr gating), cmpf and select. This separates the poison branch from the numeric constant-evaluation entries.

**Status: Succeeded — proven.** All 21 listed scalar integer operation families have Pattern.Valid proofs for poison on either operand. Extended operations create and prove poison for both results. Source UB exclusions for division/remainder remain in their interpretation; right-poison divisor cases are vacuous only when source interpretation is undefined. The patterns are independently checked and do not encode upstream early-return priority.

**Coverage:** 17 single-result scalar integer ops (addi, subi, muli, divui, divsi, ceildivui, ceildivsi, floordivsi, remui, remsi, andi, ori, xori, maxsi, maxui, minsi, minui); four two-result scalar extended ops (addui_extended, subui_extended, mulsi_extended, mului_extended). Floating-point and shaped variants are outside current integer Puddle model. Upstream excludes shifts, cmpi, cmpf, select.

**Lean:** [Veir/Passes/ArithCanonicalize/G004.lean](../Veir/Passes/ArithCanonicalize/G004.lean); `Veir.ArithCanonicalize.G004.addiValid; Veir.ArithCanonicalize.G004.subiValid; Veir.ArithCanonicalize.G004.muliValid; Veir.ArithCanonicalize.G004.divuiValid; Veir.ArithCanonicalize.G004.divsiValid; Veir.ArithCanonicalize.G004.ceildivuiValid; Veir.ArithCanonicalize.G004.ceildivsiValid; Veir.ArithCanonicalize.G004.floordivsiValid; Veir.ArithCanonicalize.G004.remuiValid; Veir.ArithCanonicalize.G004.remsiValid; Veir.ArithCanonicalize.G004.andiValid; Veir.ArithCanonicalize.G004.oriValid; Veir.ArithCanonicalize.G004.xoriValid; Veir.ArithCanonicalize.G004.maxsiValid; Veir.ArithCanonicalize.G004.maxuiValid; Veir.ArithCanonicalize.G004.minsiValid; Veir.ArithCanonicalize.G004.minuiValid; Veir.ArithCanonicalize.G004.addui_extendedValid; Veir.ArithCanonicalize.G004.subui_extendedValid; Veir.ArithCanonicalize.G004.mulsi_extendedValid; Veir.ArithCanonicalize.G004.mului_extendedValid`.

### G005: CommonFolders unary/cast poison propagation

[Original code: CommonFolders.h:354–375](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/include/mlir/Dialect/CommonFolders.h#L354-L375).

For the listed unary/cast operations, op(ub.poison) -> ub.poison of the result type. Negation/flush use the analogous unary helper; integer/float/index casts use constFoldCastOp.

**Matched:** `arith.negf`, `arith.flush_denormals`, `arith.extui`, `arith.extsi`, `arith.extf`, `arith.trunci`, `arith.truncf`, `arith.convertf`, `arith.uitofp`, `arith.sitofp`, `arith.fptoui`, `arith.fptosi`, `arith.index_cast`, `arith.index_castui`, `ub.poison`. **Replacement:** `ub.poison`.

**Conditions:** The operation-specific earlier folds must not already have succeeded. The helper receives a fully poisoned fold-adaptor attribute and returns it before attempting numeric conversion, bypassing conversion-status checks. Numeric constant branches are listed separately. Bitcast has its own explicit F165 branch.

**Status: Succeeded — proven.** Three Pattern.Valid proofs for integer cast poison propagation via llvm.mlir.poison, VeIR’s integer poison materialization. The float, index, and shaped instances of this generic rule remain unsupported by the current interpreter.

**Coverage:** scalar integer extui/extsi/trunci; all legal widths; all nneg/nsw/nuw flags; excludes float/index/shaped operations

**Lean:** [Veir/Passes/ArithCanonicalize/G005.lean](../Veir/Passes/ArithCanonicalize/G005.lean); `Veir.ArithCanonicalize.G005.extuiValid; Veir.ArithCanonicalize.G005.extsiValid; Veir.ArithCanonicalize.G005.trunciValid`.

### G006: Scaling-cast poison propagation

[Original code: ArithOps.cpp:1924–1938](https://github.com/llvm/llvm-project/blob/32ec2901f308caee5c76dbdc8d21a12a08d5457a/mlir/lib/Dialect/Arith/IR/ArithOps.cpp#L1924-L1938).

scaling_extf(poison, scale), scaling_extf(in, poison), scaling_truncf(poison, scale), or scaling_truncf(in, poison) -> poison of the result type. Only one operand needs to be a known poison; the other may be unknown.

**Matched:** `arith.scaling_extf`, `arith.scaling_truncf`, `ub.poison`. **Replacement:** `ub.poison`.

**Conditions:** The scale element type must be exactly f8E8M0FNU (checked by both callers before invoking foldScalingCastOp). The helper recognizes a fully poisoned input or scale attribute before checking whether both operands are constant or performing any conversion. This is separate from numeric constant evaluation in F146/F155.

**Status: Cannot be implemented with current Puddle support.** VeIR has no arith.scaling_extf/scaling_truncf opcodes or floating-point interpretation, including the f8E8M0FNU scale format. A poison rewrite cannot be verified against a meaningful source interpretation until that support exists.

**Coverage:** Full upstream rule
