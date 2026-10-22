# LLVM InstSimplify rewrites

Pinned LLVM commit: [`fb3ef86994775a17f4e9f1576d17590e79a8e198`](https://github.com/llvm/llvm-project/commit/fb3ef86994775a17f4e9f1576d17590e79a8e198).

See [scope, methodology, and formalization limits](README.md). The source inventory was prepared by Luna agents; Lean implementations and proofs by Sol 6.1 agents. A rule's proof applies only to the domain explicitly recorded in its entry.

## Counts

Independent implemented ports: **238**. Independent ports proven `Pattern.Valid`: **238**. Independent counterexamples: **0**. Caller entries marked `covered_by` are excluded from these totals. A source rule parameterized by opcode or operand order counts once; its concrete patterns and theorems are listed below.

| Inventory kind | Entries | Independent implementations | Entries with proofs (including shared) | Counterexamples | Unsupported | Pending |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| rewrite | 486 | 219 | 221 | 0 | 265 | 0 |
| schema | 122 | 18 | 22 | 0 | 100 | 0 |
| delegation | 192 | 1 | 29 | 0 | 163 | 0 |

Each row below is one audited source entry. Shared recursive algorithms and delegation sites are labeled separately to avoid treating dispatcher calls as additional peephole equations.

<a id="is0121"></a>

## IS0121 — `simplifyCmpSelCase`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:120–121](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L120-L121). Kind: schema.
- **Rewrite:** %cmp simplified to the select condition (%cond).; returns `TrueOrFalse`. Guard: `SimplifiedCmp == Cond`.
- **Matched/replaced opcodes:** `icmp`, `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive comparison simplification; exact predicate, swapped-predicate, and select-condition identity matching.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0125"></a>

## IS0125 — `simplifyCmpSelCase`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:125–125](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L125). Kind: schema.
- **Rewrite:** If the composed comparison did not simplify and `Cond` is syntactically `Pred LHS, RHS` (or the swapped predicate with operands reversed), return typed `TrueOrFalse`. Guard: `!SimplifiedCmp && isSameCompare(Cond, Pred, LHS, RHS)`.
- **Matched/replaced opcodes:** `icmp`, `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive comparison simplification; exact predicate, swapped-predicate, and select-condition identity matching.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** This fallback recognizes the same comparison syntactically after recursive simplification failed. Its result relies on the enclosing select-arm condition; it needs a contextual substitution soundness argument, not a correctness certificate for a successful recursive result.

<a id="is0127"></a>

## IS0127 — `simplifyCmpSelCase`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:127–127](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L127). Kind: schema.
- **Rewrite:** Return the simplified composed comparison when neither select-condition identity case applies. Guard: `SimplifiedCmp != Cond` and not (`!SimplifiedCmp && isSameCompare(Cond, Pred, LHS, RHS)`).
- **Matched/replaced opcodes:** `icmp`, `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive comparison simplification; exact predicate, swapped-predicate, and select-condition identity matching.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Simple internal forwarding to already inventoried helper cases; this return adds no distinct rewrite equation.

<a id="is0134"></a>

## IS0134 — `simplifyCmpSelTrueCase`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:134–134](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L134). Kind: schema.
- **Rewrite:** For the true arm of a select, simplify `Pred LHS, RHS`; if it matches the select condition, use typed true. Guard: call `simplifyCmpSelCase` with `getTrue(Cond->getType())`.
- **Matched/replaced opcodes:** `icmp`, `fcmp`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive comparison simplification; preserves select condition result type and arm polarity.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Simple internal forwarding to already inventoried helper cases; this return adds no distinct rewrite equation.

<a id="is0142"></a>

## IS0142 — `simplifyCmpSelFalseCase`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:142–142](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L142). Kind: schema.
- **Rewrite:** For the false arm of a select, simplify `Pred LHS, RHS`; if it matches the select condition, use typed false. Guard: call `simplifyCmpSelCase` with `getFalse(Cond->getType())`.
- **Matched/replaced opcodes:** `icmp`, `fcmp`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive comparison simplification; preserves select condition result type and arm polarity.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Simple internal forwarding to already inventoried helper cases; this return adds no distinct rewrite equation.

<a id="is0160"></a>

## IS0160 — `handleOtherCmpSelSimplifications`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:158–160](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L158-L160). Kind: delegation.
- **Rewrite:** If the false value simplified to false, then the result of the compare is equal to "Cond && TCmp".  This also catches the case when the false value simplified to false and the true value to true, returning "Cond". Folding select to and/or isn't poison-safe in general; impliesPoison checks whether folding it does not convert a well-defined value into poison.; returns `V`. Guard: `match(FCmp, m_Zero()) && impliesPoison(TCmp, Cond)` and `Value *V = simplifyAndInst(Cond, TCmp, Q, MaxRecurse)`. Delegates to `simplifyAndInst`.
- **Matched/replaced opcodes:** `icmp`, `fcmp`, `and`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget; analysis required: poison implication (`impliesPoison`) proves select-to-boolean folding preserves definedness.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** impliesPoison analysis result is not represented in Models; inspectOperation facts are erased.

<a id="is0165"></a>

## IS0165 — `handleOtherCmpSelSimplifications`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:163–165](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L163-L165). Kind: delegation.
- **Rewrite:** If the true value simplified to true, then the result of the compare is equal to "Cond || FCmp".; returns `V`. Guard: `match(TCmp, m_One()) && impliesPoison(FCmp, Cond)` and `Value *V = simplifyOrInst(Cond, FCmp, Q, MaxRecurse)`. Delegates to `simplifyOrInst`.
- **Matched/replaced opcodes:** `icmp`, `fcmp`, `and`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget; analysis required: poison implication (`impliesPoison`) proves select-to-boolean folding preserves definedness.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** impliesPoison analysis result is not represented in Models; inspectOperation facts are erased.

<a id="is0171"></a>

## IS0171 — `handleOtherCmpSelSimplifications`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:169–171](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L169-L171). Kind: delegation.
- **Rewrite:** Finally, if the false value simplified to true and the true value to false, then the result of the compare is equal to "!Cond".; returns `V`. Guard: `match(FCmp, m_One()) && match(TCmp, m_Zero())` and `Value *V = simplifyXorInst( Cond, Constant::getAllOnesValue(Cond->getType()), Q, MaxRecurse)`. Delegates to `simplifyXorInst`.
- **Matched/replaced opcodes:** `icmp`, `fcmp`, `and`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0218"></a>

## IS0218 — `expandBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:217–218](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L217-L218). Kind: schema.
- **Rewrite:** Does the expanded pair of binops simplify to the existing binop?; returns `B`. Guard: `(L == B0 && R == B1) || (Instruction::isCommutative(OpcodeToExpand) && L == B1 && R == B0)`.
- **Matched/replaced opcodes:** `add`, `sub`, `mul`, `and`, `or`, `xor`, `shl`, `lshr`, `ashr`, `udiv`, `sdiv`, `urem`, `srem`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0227"></a>

## IS0227 — `expandBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:227–227](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L227). Kind: schema.
- **Rewrite:** Return the simplified expanded result `S = simplifyBinOp(OpcodeToExpand, L, R)` after distributing `Opcode` to both operands of `V`; `L` and `R` are successful simplifications of `B0 op OtherOp` and `B1 op OtherOp`. Guard: `V` is a binary op with opcode `OpcodeToExpand`, both child operations simplify, and `S` is nonnull.
- **Matched/replaced opcodes:** `add`, `sub`, `mul`, `and`, `or`, `xor`, `shl`, `lshr`, `ashr`, `udiv`, `sdiv`, `urem`, `srem`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0242"></a>

## IS0242 — `expandCommutativeBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:241–242](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L241-L242). Kind: schema.
- **Rewrite:** Recursion is always used, so bail out at once if we already hit the limit.; returns `V`. Guard: `Value *V = expandBinOp(Opcode, L, R, OpcodeToExpand, Q, MaxRecurse)`.
- **Matched/replaced opcodes:** `add`, `mul`, `and`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0244"></a>

## IS0244 — `expandCommutativeBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:243–244](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L243-L244). Kind: schema.
- **Rewrite:** Recursion is always used, so bail out at once if we already hit the limit.; returns `V`. Guard: `Value *V = expandBinOp(Opcode, R, L, OpcodeToExpand, Q, MaxRecurse)`.
- **Matched/replaced opcodes:** `add`, `mul`, `and`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0274"></a>

## IS0274 — `simplifyAssociativeBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:271–274](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L271-L274). Kind: schema.
- **Rewrite:** It does!  Return "A op V" if it simplifies or is already available. If V equals B then "A op V" is just the LHS.; returns `LHS`. Guard: `Op0 && Op0->getOpcode() == Opcode` and `Value *V = simplifyBinOp(Opcode, B, C, Q, MaxRecurse)` and `V == B`.
- **Matched/replaced opcodes:** `add`, `mul`, `and`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0278"></a>

## IS0278 — `simplifyAssociativeBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:275–278](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L275-L278). Kind: schema.
- **Rewrite:** Otherwise return "A op V" if it simplifies.; returns `W`. Guard: `Op0 && Op0->getOpcode() == Opcode` and `Value *V = simplifyBinOp(Opcode, B, C, Q, MaxRecurse)` and `Value *W = simplifyBinOp(Opcode, A, V, Q, MaxRecurse)`.
- **Matched/replaced opcodes:** `add`, `mul`, `and`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0294"></a>

## IS0294 — `simplifyAssociativeBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:291–294](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L291-L294). Kind: schema.
- **Rewrite:** It does!  Return "V op C" if it simplifies or is already available. If V equals B then "V op C" is just the RHS.; returns `RHS`. Guard: `Op1 && Op1->getOpcode() == Opcode` and `Value *V = simplifyBinOp(Opcode, A, B, Q, MaxRecurse)` and `V == B`.
- **Matched/replaced opcodes:** `add`, `mul`, `and`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0298"></a>

## IS0298 — `simplifyAssociativeBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:295–298](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L295-L298). Kind: schema.
- **Rewrite:** Otherwise return "V op C" if it simplifies.; returns `W`. Guard: `Op1 && Op1->getOpcode() == Opcode` and `Value *V = simplifyBinOp(Opcode, A, B, Q, MaxRecurse)` and `Value *W = simplifyBinOp(Opcode, V, C, Q, MaxRecurse)`.
- **Matched/replaced opcodes:** `add`, `mul`, `and`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0318"></a>

## IS0318 — `simplifyAssociativeBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:315–318](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L315-L318). Kind: schema.
- **Rewrite:** It does!  Return "V op B" if it simplifies or is already available. If V equals A then "V op B" is just the LHS.; returns `LHS`. Guard: `Op0 && Op0->getOpcode() == Opcode` and `Value *V = simplifyBinOp(Opcode, C, A, Q, MaxRecurse)` and `V == A`.
- **Matched/replaced opcodes:** `add`, `mul`, `and`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0322"></a>

## IS0322 — `simplifyAssociativeBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:319–322](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L319-L322). Kind: schema.
- **Rewrite:** Otherwise return "V op B" if it simplifies.; returns `W`. Guard: `Op0 && Op0->getOpcode() == Opcode` and `Value *V = simplifyBinOp(Opcode, C, A, Q, MaxRecurse)` and `Value *W = simplifyBinOp(Opcode, V, B, Q, MaxRecurse)`.
- **Matched/replaced opcodes:** `add`, `mul`, `and`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0338"></a>

## IS0338 — `simplifyAssociativeBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:335–338](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L335-L338). Kind: schema.
- **Rewrite:** It does!  Return "B op V" if it simplifies or is already available. If V equals C then "B op V" is just the RHS.; returns `RHS`. Guard: `Op1 && Op1->getOpcode() == Opcode` and `Value *V = simplifyBinOp(Opcode, C, A, Q, MaxRecurse)` and `V == C`.
- **Matched/replaced opcodes:** `add`, `mul`, `and`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0342"></a>

## IS0342 — `simplifyAssociativeBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:339–342](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L339-L342). Kind: schema.
- **Rewrite:** Otherwise return "B op V" if it simplifies.; returns `W`. Guard: `Op1 && Op1->getOpcode() == Opcode` and `Value *V = simplifyBinOp(Opcode, C, A, Q, MaxRecurse)` and `Value *W = simplifyBinOp(Opcode, B, V, Q, MaxRecurse)`.
- **Matched/replaced opcodes:** `add`, `mul`, `and`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0383"></a>

## IS0383 — `threadBinOpOverSelect`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:382–383](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L382-L383). Kind: schema.
- **Rewrite:** If they simplified to the same value, then return the common value. If they both failed to simplify then return null.; returns `TV`. Guard: `TV == FV`.
- **Matched/replaced opcodes:** `add`, `sub`, `mul`, `and`, `or`, `xor`, `shl`, `lshr`, `ashr`, `udiv`, `sdiv`, `urem`, `srem`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive evaluation of select true/false arms under the same operands.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0387"></a>

## IS0387 — `threadBinOpOverSelect`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:386–387](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L386-L387). Kind: schema.
- **Rewrite:** If one branch simplified to undef, return the other one.; returns `FV`. Guard: `TV && Q.isUndefValue(TV)`.
- **Matched/replaced opcodes:** `add`, `sub`, `mul`, `and`, `or`, `xor`, `shl`, `lshr`, `ashr`, `udiv`, `sdiv`, `urem`, `srem`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM undef nondeterministic semantics; recursive evaluation of select true/false arms under the same operands.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** LLVM undef has no interpretOp' semantics: .mlir__undef falls through to failure. This branch cannot be proved by a vacuous successful-interpretation assumption.

<a id="is0389"></a>

## IS0389 — `threadBinOpOverSelect`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:388–389](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L388-L389). Kind: schema.
- **Rewrite:** If one branch simplified to undef, return the other one.; returns `TV`. Guard: `FV && Q.isUndefValue(FV)`.
- **Matched/replaced opcodes:** `add`, `sub`, `mul`, `and`, `or`, `xor`, `shl`, `lshr`, `ashr`, `udiv`, `sdiv`, `urem`, `srem`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM undef nondeterministic semantics; recursive evaluation of select true/false arms under the same operands.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** LLVM undef has no interpretOp' semantics: .mlir__undef falls through to failure. This branch cannot be proved by a vacuous successful-interpretation assumption.

<a id="is0394"></a>

## IS0394 — `threadBinOpOverSelect`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:393–394](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L393-L394). Kind: schema.
- **Rewrite:** If applying the operation did not change the true and false select values, then the result of the binop is the select itself.; returns `SI`. Guard: `TV == SI->getTrueValue() && FV == SI->getFalseValue()`.
- **Matched/replaced opcodes:** `add`, `sub`, `mul`, `and`, `or`, `xor`, `shl`, `lshr`, `ashr`, `udiv`, `sdiv`, `urem`, `srem`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive evaluation of select true/false arms under the same operands.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0413"></a>

## IS0413 — `threadBinOpOverSelect`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:410–413](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L410-L413). Kind: schema.
- **Rewrite:** The value that didn't simplify is "UnsimplifiedLHS op UnsimplifiedRHS". We already know that "op" is the same as for the simplified value.  See if the operands match too.  If so, return the simplified value.; returns `Simplified`. Guard: `(FV && !TV) || (TV && !FV)` and `Simplified && Simplified->getOpcode() == unsigned(Opcode) && !Simplified->hasPoisonGeneratingFlags()` and `Simplified->getOperand(0) == UnsimplifiedLHS && Simplified->getOperand(1) == UnsimplifiedRHS`.
- **Matched/replaced opcodes:** `add`, `sub`, `mul`, `and`, `or`, `xor`, `shl`, `lshr`, `ashr`, `udiv`, `sdiv`, `urem`, `srem`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: simplified result must have no poison-generating flags; recursive evaluation of select true/false arms under the same operands.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0417"></a>

## IS0417 — `threadBinOpOverSelect`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:414–417](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L414-L417). Kind: schema.
- **Rewrite:** The value that didn't simplify is "UnsimplifiedLHS op UnsimplifiedRHS". We already know that "op" is the same as for the simplified value.  See if the operands match too.  If so, return the simplified value.; returns `Simplified`. Guard: `(FV && !TV) || (TV && !FV)` and `Simplified && Simplified->getOpcode() == unsigned(Opcode) && !Simplified->hasPoisonGeneratingFlags()` and `Simplified->isCommutative() && Simplified->getOperand(1) == UnsimplifiedLHS && Simplified->getOperand(0) == UnsimplifiedRHS`.
- **Matched/replaced opcodes:** `add`, `sub`, `mul`, `and`, `or`, `xor`, `shl`, `lshr`, `ashr`, `udiv`, `sdiv`, `urem`, `srem`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: simplified result must have no poison-generating flags; recursive evaluation of select true/false arms under the same operands.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0464"></a>

## IS0464 — `threadCmpOverSelect`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:463–464](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L463-L464). Kind: schema.
- **Rewrite:** If both sides simplified to the same value, then use it as the result of the original comparison.; returns `TCmp`. Guard: `TCmp == FCmp`.
- **Matched/replaced opcodes:** `icmp`, `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive evaluation of select true/false arms under the same operands.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0469"></a>

## IS0469 — `threadCmpOverSelect`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:468–469](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L468-L469). Kind: schema.
- **Rewrite:** The remaining cases only make sense if the select condition has the same type as the result of the comparison, so bail out if this is not so.; returns `handleOtherCmpSelSimplifications(TCmp, FCmp, Cond, Q, MaxRecurse)`. Guard: `Cond->getType()->isVectorTy() == RHS->getType()->isVectorTy()`.
- **Matched/replaced opcodes:** `icmp`, `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive evaluation of select true/false arms under the same operands.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0518"></a>

## IS0518 — `threadBinOpOverPHI`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:518–518](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L518). Kind: schema.
- **Rewrite:** For a PHI operand, evaluate the binop/comparison for every non-self incoming value at that predecessor terminator; return the common simplified value only if every edge simplifies to the same value. Guard: non-PHI operand dominates the PHI (or is argument/constant; absent DT, only entry-block non-invoke/non-callbr instructions qualify), and no edge result is null or differs.
- **Matched/replaced opcodes:** `add`, `sub`, `mul`, `and`, `or`, `xor`, `shl`, `lshr`, `ashr`, `udiv`, `sdiv`, `urem`, `srem`.
- **Beyond opcode/constant/SSA matching:** Yes — requires per-edge phi evaluation, skips self-references, checks non-phi operand dominance, and simplifies with the incoming terminator as context; requires LLVM PHI incoming values, edge terminator context, and self-reference handling; Veir block arguments do not provide this LLVM PHI model.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** LLVM PHI opcode/incoming-edge semantics and dominating-edge ValueTracking facts are not represented by Puddle Models.

<a id="is0563"></a>

## IS0563 — `threadCmpOverPHI`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:563–563](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L563). Kind: schema.
- **Rewrite:** For a PHI operand, evaluate the binop/comparison for every non-self incoming value at that predecessor terminator; return the common simplified value only if every edge simplifies to the same value. Guard: non-PHI operand dominates the PHI (or is argument/constant; absent DT, only entry-block non-invoke/non-callbr instructions qualify), and no edge result is null or differs.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — requires per-edge phi evaluation, skips self-references, checks non-phi operand dominance, and simplifies with the incoming terminator as context; requires LLVM PHI incoming values, edge terminator context, and self-reference handling; Veir block arguments do not provide this LLVM PHI model.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** LLVM PHI opcode/incoming-edge semantics and dominating-edge ValueTracking facts are not represented by Puddle Models.

<a id="is0580"></a>

## IS0580 — `foldOrCommuteConstant`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:577–580](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L577-L580). Kind: delegation.
- **Rewrite:** When both operands are constants and a folding context is available, fold the floating-point binary operation with `ConstantFoldFPInstOperands`.
- **Matched/replaced opcodes:** `add`, `sub`, `mul`, `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `and`, `or`, `xor`, `udiv`, `sdiv`, `urem`, `srem`.
- **Beyond opcode/constant/SSA matching:** Yes — constant-folding semantics; floating-point folding also requires CtxI and DataLayout; recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Floating-point constant folding requires LLVM FP opcode evaluation and IEEE/fast-math/rounding semantics not provided by interpretOp'; float RuntimeValues alone do not supply those opcode semantics.

<a id="is0582"></a>

## IS0582 — `foldOrCommuteConstant`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:580–582](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L580-L582). Kind: delegation.
- **Rewrite:** When both operands are constants, fold the binary operation with `ConstantFoldBinaryOpOperands` (including the floating-point fallback when no folding context is available).
- **Matched/replaced opcodes:** `add`, `sub`, `mul`, `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `and`, `or`, `xor`, `udiv`, `sdiv`, `urem`, `srem`.
- **Beyond opcode/constant/SSA matching:** Yes — constant-folding semantics; floating-point folding also requires CtxI and DataLayout; recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS0582.lean](../../Veir/InstSimplify/IS0582.lean).
- **Theorems:** `Veir.InstSimplify.IS0582.pattern_add_valid`, `Veir.InstSimplify.IS0582.pattern_sub_valid`, `Veir.InstSimplify.IS0582.pattern_mul_valid`, `Veir.InstSimplify.IS0582.pattern_shl_valid`, `Veir.InstSimplify.IS0582.pattern_lshr_valid`, `Veir.InstSimplify.IS0582.pattern_ashr_valid`, `Veir.InstSimplify.IS0582.pattern_and_valid`, `Veir.InstSimplify.IS0582.pattern_or_valid`, `Veir.InstSimplify.IS0582.pattern_xor_valid`, `Veir.InstSimplify.IS0582.pattern_udiv_valid`, `Veir.InstSimplify.IS0582.pattern_sdiv_valid`, `Veir.InstSimplify.IS0582.pattern_urem_valid`, `Veir.InstSimplify.IS0582.pattern_srem_valid`, `Veir.InstSimplify.IS0582.pattern_shl_poison_valid`, `Veir.InstSimplify.IS0582.pattern_lshr_poison_valid`, `Veir.InstSimplify.IS0582.pattern_ashr_poison_valid`, `Veir.InstSimplify.IS0582.pattern_udiv_poison_valid`, `Veir.InstSimplify.IS0582.pattern_sdiv_poison_valid`, `Veir.InstSimplify.IS0582.pattern_urem_poison_valid`, `Veir.InstSimplify.IS0582.pattern_srem_poison_valid`.
- **Details / missing facilities:** 20 faithful scalar constant-fold patterns:13 numerical folds plus7 poison-output branches for overshifts and zero/signed-overflow div/rem, matching LLVM ConstantFold.cpp. Numeric branches exclude those poison cases; source overflow/exact flags ignored by upstream constant folder remain arbitrary and refine correctly. Div/rem poison source evaluates UB, not interpreter failure. Exact upstream output policy: https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/IR/ConstantFold.cpp#L767-L876

<a id="is0597"></a>

## IS0597 — `simplifyAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:596–597](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L596-L597). Kind: delegation.
- **Rewrite:** Given operands for an Add, see if we can fold the result. If not, this returns null.; returns `C`. Guard: `Constant *C = foldOrCommuteConstant(Instruction::Add, Op0, Op1, Q)`. Delegates to `foldOrCommuteConstant`.
- **Matched/replaced opcodes:** `add`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar integer constants only, arbitrary widths and source flags.
- **Lean:** [Veir/InstSimplify/IS0582.lean](../../Veir/InstSimplify/IS0582.lean).
- **Theorems:** `Veir.InstSimplify.IS0582.pattern_add_valid`.
- **Shared implementation:** [IS0582](#is0582). This caller is not an additional independent port.
- **Details / missing facilities:** Dispatch covered by numerical and poison-output scalar constant-folding patterns in IS0582, matching LLVM outputs. Not counted as an independent rewrite; other constant classes lack interpreter support.

<a id="is0601"></a>

## IS0601 — `simplifyAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:600–601](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L600-L601). Kind: rewrite.
- **Rewrite:** X + poison -> poison; returns `Op1`. Guard: `isa<PoisonValue>(Op1)`.
- **Matched/replaced opcodes:** `add`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM poison propagation semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS0601.lean](../../Veir/InstSimplify/IS0601.lean).
- **Theorems:** `Veir.InstSimplify.IS0601.pattern_valid`, `Veir.InstSimplify.IS0601.pattern_left_valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is0605"></a>

## IS0605 — `simplifyAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:604–605](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L604-L605). Kind: rewrite.
- **Rewrite:** X + undef -> undef; returns `Op1`. Guard: `Q.isUndefValue(Op1)`.
- **Matched/replaced opcodes:** `add`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM undef nondeterministic semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** LLVM undef has no interpretOp' semantics: .mlir__undef falls through to failure. This branch cannot be proved by a vacuous successful-interpretation assumption.

<a id="is0609"></a>

## IS0609 — `simplifyAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:608–609](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L608-L609). Kind: rewrite.
- **Rewrite:** X + 0 -> X; returns `Op0`. Guard: `match(Op1, m_Zero())`.
- **Matched/replaced opcodes:** `add`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS0609.lean](../../Veir/InstSimplify/IS0609.lean).
- **Theorems:** `Veir.InstSimplify.IS0609.valid`, `Veir.InstSimplify.IS0609.valid_left`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is0613"></a>

## IS0613 — `simplifyAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:612–613](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L612-L613). Kind: rewrite.
- **Rewrite:** X + (-X) -> 0 when isKnownNegation proves the operands are additive inverses; this is not a test that both operands are negative.
- **Matched/replaced opcodes:** `add`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-negation analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** isKnownNegation is an external ValueTracking analysis; no semantic specification or proof-producing bridge is available for its full accepted operand language.

<a id="is0621"></a>

## IS0621 — `simplifyAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:620–621](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L620-L621). Kind: rewrite.
- **Rewrite:** X + (Y - X) -> Y (Y - X) + X -> Y Eg: X + -X -> 0; returns `Y`. Guard: `match(Op1, m_Sub(m_Value(Y), m_Specific(Op0))) || match(Op0, m_Sub(m_Value(Y), m_Specific(Op1)))`.
- **Matched/replaced opcodes:** `add`, `sub`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS0621.lean](../../Veir/InstSimplify/IS0621.lean).
- **Theorems:** `Veir.InstSimplify.IS0621.valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is0626"></a>

## IS0626 — `simplifyAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:625–626](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L625-L626). Kind: rewrite.
- **Rewrite:** X + ~X -> -1   since   ~X = -X-1; returns `Constant::getAllOnesValue(Ty)`. Guard: `match(Op0, m_Not(m_Specific(Op1))) || match(Op1, m_Not(m_Specific(Op0)))`.
- **Matched/replaced opcodes:** `add`, `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS0626.lean](../../Veir/InstSimplify/IS0626.lean).
- **Theorems:** `Veir.InstSimplify.IS0626.pattern_00_valid`, `Veir.InstSimplify.IS0626.pattern_01_valid`, `Veir.InstSimplify.IS0626.pattern_10_valid`, `Veir.InstSimplify.IS0626.pattern_11_valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is0633"></a>

## IS0633 — `simplifyAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:632–633](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L632-L633). Kind: rewrite.
- **Rewrite:** add nsw/nuw (xor Y, signmask), signmask --> Y The no-wrapping add guarantees that the top bit will be set by the add. Therefore, the xor must be clearing the already set sign bit of Y.; returns `Y`. Guard: `(IsNSW || IsNUW) && match(Op1, m_SignMask()) && match(Op0, m_Xor(m_Value(Y), m_SignMask()))`.
- **Matched/replaced opcodes:** `add`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction flags: requires `nsw` or `nuw` on the add.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Arbitrary scalar integer widths and signedness attributes; every source no-wrap/exact requirement preserved, all other flags arbitrary, poison refinement included.
- **Lean:** [Veir/InstSimplify/IS0633.lean](../../Veir/InstSimplify/IS0633.lean).
- **Theorems:** `Veir.InstSimplify.IS0633.valid`.
- **Details / missing facilities:** Checked by Lean; APInt-bit matching admits all equivalent signed/unsigned/i1 integer attribute spellings.

<a id="is0637"></a>

## IS0637 — `simplifyAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:637–637](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L637). Kind: rewrite.
- **Rewrite:** `add nuw X, -1 -> -1`. Guard: add has `nuw` and RHS is all ones.
- **Matched/replaced opcodes:** `add`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction flag: `nuw`.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS0637.lean](../../Veir/InstSimplify/IS0637.lean).
- **Theorems:** `Veir.InstSimplify.IS0637.pattern_valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is0642"></a>

## IS0642 — `simplifyAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:640–642](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L640-L642). Kind: delegation.
- **Rewrite:** i1 add -> xor.; returns `V`. Guard: `MaxRecurse && Op0->getType()->isIntOrIntVectorTy(1)` and `Value *V = simplifyXorInst(Op0, Op1, Q, MaxRecurse - 1)`. Delegates to `simplifyXorInst`.
- **Matched/replaced opcodes:** `add`.
- **Beyond opcode/constant/SSA matching:** Yes — type required: integer scalar/vector with the stated bit width; recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0647"></a>

## IS0647 — `simplifyAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:646–647](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L646-L647). Kind: delegation.
- **Rewrite:** Try some generic simplifications for associative operations.; returns `V`. Guard: `Value *V = simplifyAssociativeBinOp(Instruction::Add, Op0, Op1, Q, MaxRecurse)`. Delegates to `simplifyAssociativeBinOp`.
- **Matched/replaced opcodes:** `add`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0727"></a>

## IS0727 — `simplifyByDomEq`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:726–727](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L726-L727). Kind: schema.
- **Rewrite:** At top-level recursion depth, `sub X,Y`, `xor X,Y`, `urem X,Y`, or `srem X,Y` folds to zero when a dominating condition implies `X == Y`.
- **Matched/replaced opcodes:** `sub`, `xor`, `urem`, `srem`.
- **Beyond opcode/constant/SSA matching:** Yes — requires a dominating `icmp eq` proof for the two operands at the current instruction context.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Dominating icmp-equality analysis at the top recursion level has no Models assumption relating operand values.

<a id="is0731"></a>

## IS0731 — `simplifyByDomEq`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:730–731](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L730-L731). Kind: schema.
- **Rewrite:** At top-level recursion depth, `sdiv X,Y` or `udiv X,Y` folds to one when a dominating condition implies `X == Y`.
- **Matched/replaced opcodes:** `sdiv`, `udiv`.
- **Beyond opcode/constant/SSA matching:** Yes — requires a dominating `icmp eq` proof for the two operands at the current instruction context.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Dominating icmp-equality analysis at the top recursion level has no Models assumption relating operand values.

<a id="is0736"></a>

## IS0736 — `simplifyByDomEq`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:735–736](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L735-L736). Kind: schema.
- **Rewrite:** At top-level recursion depth, `and X,Y` or `or X,Y` folds to Y when a dominating condition implies `X == Y`.
- **Matched/replaced opcodes:** `and`, `or`.
- **Beyond opcode/constant/SSA matching:** Yes — requires a dominating `icmp eq` proof for the two operands at the current instruction context.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Dominating icmp-equality analysis at the top recursion level has no Models assumption relating operand values.

<a id="is0749"></a>

## IS0749 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:748–749](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L748-L749). Kind: delegation.
- **Rewrite:** Given operands for a Sub, see if we can fold the result. If not, this returns null.; returns `C`. Guard: `Constant *C = foldOrCommuteConstant(Instruction::Sub, Op0, Op1, Q)`. Delegates to `foldOrCommuteConstant`.
- **Matched/replaced opcodes:** `sub`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar integer constants only, arbitrary widths and source flags.
- **Lean:** [Veir/InstSimplify/IS0582.lean](../../Veir/InstSimplify/IS0582.lean).
- **Theorems:** `Veir.InstSimplify.IS0582.pattern_sub_valid`.
- **Shared implementation:** [IS0582](#is0582). This caller is not an additional independent port.
- **Details / missing facilities:** Dispatch covered by numerical and poison-output scalar constant-folding patterns in IS0582, matching LLVM outputs. Not counted as an independent rewrite; other constant classes lack interpreter support.

<a id="is0754"></a>

## IS0754 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:753–754](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L753-L754). Kind: rewrite.
- **Rewrite:** X - poison -> poison poison - X -> poison; returns `PoisonValue::get(Op0->getType())`. Guard: `isa<PoisonValue>(Op0) || isa<PoisonValue>(Op1)`.
- **Matched/replaced opcodes:** `sub`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM poison propagation semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS0754.lean](../../Veir/InstSimplify/IS0754.lean).
- **Theorems:** `Veir.InstSimplify.IS0754.pattern_sub_right_valid`, `Veir.InstSimplify.IS0754.pattern_sub_left_valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is0759"></a>

## IS0759 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:758–759](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L758-L759). Kind: rewrite.
- **Rewrite:** X - undef -> undef undef - X -> undef; returns `UndefValue::get(Op0->getType())`. Guard: `Q.isUndefValue(Op0) || Q.isUndefValue(Op1)`.
- **Matched/replaced opcodes:** `sub`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM undef nondeterministic semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** LLVM undef has no interpretOp' semantics: .mlir__undef falls through to failure. This branch cannot be proved by a vacuous successful-interpretation assumption.

<a id="is0763"></a>

## IS0763 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:762–763](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L762-L763). Kind: rewrite.
- **Rewrite:** X - 0 -> X; returns `Op0`. Guard: `match(Op1, m_Zero())`.
- **Matched/replaced opcodes:** `sub`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS0763.lean](../../Veir/InstSimplify/IS0763.lean).
- **Theorems:** `Veir.InstSimplify.IS0763.pattern_valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is0767"></a>

## IS0767 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:766–767](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L766-L767). Kind: rewrite.
- **Rewrite:** X - X -> 0; returns `Constant::getNullValue(Op0->getType())`. Guard: `Op0 == Op1`.
- **Matched/replaced opcodes:** `sub`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS0767.lean](../../Veir/InstSimplify/IS0767.lean).
- **Theorems:** `Veir.InstSimplify.IS0767.valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is0773"></a>

## IS0773 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:771–773](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L771-L773). Kind: rewrite.
- **Rewrite:** 0 - X -> 0 if the sub is NUW.; returns `Constant::getNullValue(Op0->getType())`. Guard: `match(Op0, m_Zero())` and `IsNUW`.
- **Matched/replaced opcodes:** `sub`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: nuw flag.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS0773.lean](../../Veir/InstSimplify/IS0773.lean).
- **Theorems:** `Veir.InstSimplify.IS0773.pattern_valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is0780"></a>

## IS0780 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:777–780](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L777-L780). Kind: rewrite.
- **Rewrite:** Op1 is either 0 or the minimum signed value. If the sub is NSW, then Op1 must be 0 because negating the minimum signed value is undefined.; returns `Constant::getNullValue(Op0->getType())`. Guard: `match(Op0, m_Zero())` and `Known.Zero.isMaxSignedValue()` and `IsNSW`.
- **Matched/replaced opcodes:** `sub`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-bits/sign-bit/range facts computed from operands; instruction property required: nsw flag.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** computeKnownBits must establish that every bit of X except the sign bit is zero. Puddle Models has no proof-bearing bridge for this ValueTracking result on arbitrary operands; the nsw flag alone does not establish the rewrite. The source comment about undefined signed negation is not an LLVM undef value.

<a id="is0783"></a>

## IS0783 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:781–783](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L781-L783). Kind: rewrite.
- **Rewrite:** 0 - X -> X if X is 0 or the minimum signed value.; returns `Op1`. Guard: `match(Op0, m_Zero())` and `Known.Zero.isMaxSignedValue()`.
- **Matched/replaced opcodes:** `sub`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-bits/sign-bit/range facts computed from operands.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** computeKnownBits has no proof-producing bridge into Models; metadata native guards cannot inspect dynamic operand bits.

<a id="is0797"></a>

## IS0797 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:794–797](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L794-L797). Kind: delegation.
- **Rewrite:** It does, we successfully reassociated!; returns `W`. Guard: `MaxRecurse && match(Op0, m_Add(m_Value(X), m_Value(Y)))) { // (X + Y` and `Value *W = simplifyBinOp(Instruction::Add, X, V, Q, MaxRecurse - 1)` and `Value *V = simplifyBinOp(Instruction::Sub, Y, Z, Q, MaxRecurse - 1)`. Delegates to `simplifyBinOp`.
- **Matched/replaced opcodes:** `sub`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0805"></a>

## IS0805 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:802–805](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L802-L805). Kind: delegation.
- **Rewrite:** It does, we successfully reassociated!; returns `W`. Guard: `MaxRecurse && match(Op0, m_Add(m_Value(X), m_Value(Y)))) { // (X + Y` and `Value *W = simplifyBinOp(Instruction::Add, Y, V, Q, MaxRecurse - 1)` and `Value *V = simplifyBinOp(Instruction::Sub, X, Z, Q, MaxRecurse - 1)`. Delegates to `simplifyBinOp`.
- **Matched/replaced opcodes:** `sub`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0819"></a>

## IS0819 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:816–819](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L816-L819). Kind: delegation.
- **Rewrite:** It does, we successfully reassociated!; returns `W`. Guard: `MaxRecurse && match(Op1, m_Add(m_Value(Y), m_Value(Z)))) { // X - (Y + Z` and `Value *W = simplifyBinOp(Instruction::Sub, V, Z, Q, MaxRecurse - 1)` and `Value *V = simplifyBinOp(Instruction::Sub, X, Y, Q, MaxRecurse - 1)`. Delegates to `simplifyBinOp`.
- **Matched/replaced opcodes:** `sub`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0827"></a>

## IS0827 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:824–827](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L824-L827). Kind: delegation.
- **Rewrite:** It does, we successfully reassociated!; returns `W`. Guard: `MaxRecurse && match(Op1, m_Add(m_Value(Y), m_Value(Z)))) { // X - (Y + Z` and `Value *W = simplifyBinOp(Instruction::Sub, V, Y, Q, MaxRecurse - 1)` and `Value *V = simplifyBinOp(Instruction::Sub, X, Z, Q, MaxRecurse - 1)`. Delegates to `simplifyBinOp`.
- **Matched/replaced opcodes:** `sub`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0841"></a>

## IS0841 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:838–841](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L838-L841). Kind: delegation.
- **Rewrite:** It does, we successfully reassociated!; returns `W`. Guard: `Value *W = simplifyBinOp(Instruction::Add, V, Y, Q, MaxRecurse - 1)` and `MaxRecurse && match(Op1, m_Sub(m_Value(X), m_Value(Y)))) // Z - (X - Y` and `Value *V = simplifyBinOp(Instruction::Sub, Z, X, Q, MaxRecurse - 1)`. Delegates to `simplifyBinOp`.
- **Matched/replaced opcodes:** `sub`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0854"></a>

## IS0854 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:850–854](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L850-L854). Kind: delegation.
- **Rewrite:** It does, return the simplified "trunc V".; returns `W`. Guard: `MaxRecurse && match(Op0, m_Trunc(m_Value(X))) && match(Op1, m_Trunc(m_Value(Y)))` and `X->getType() == Y->getType()` and `Value *V = simplifyBinOp(Instruction::Sub, X, Y, Q, MaxRecurse - 1)` and `Value *W = simplifyCastInst(Instruction::Trunc, V, Op0->getType(), Q, MaxRecurse - 1)`. Delegates to `simplifyCastInst`.
- **Matched/replaced opcodes:** `sub`, `trunc`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0860"></a>

## IS0860 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:860–860](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L860). Kind: rewrite.
- **Rewrite:** `ptrtoint(GEP(base, I)) - ptrtoint(GEP(base, J))` folds to the signed integer cast of `I - J` when both pointers strip to the same base with constant offsets. Guard: both operands match ptr-to-int-or-address forms; `computePointerDifference` finds same base; cast uses target DataLayout.
- **Matched/replaced opcodes:** `sub`, `getelementptr`, `ptrtoint`, `addrspacecast`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: DataLayout index widths and common-base constant-offset proof.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Requires DataLayout pointer stripping/common-base and constant-offset analysis; no proof-producing bridge relates GEP chains and ptrtoint in Models.

<a id="is0867"></a>

## IS0867 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:865–867](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L865-L867). Kind: delegation.
- **Rewrite:** i1 sub -> xor.; returns `V`. Guard: `MaxRecurse && Op0->getType()->isIntOrIntVectorTy(1)` and `Value *V = simplifyXorInst(Op0, Op1, Q, MaxRecurse - 1)`. Delegates to `simplifyXorInst`.
- **Matched/replaced opcodes:** `sub`.
- **Beyond opcode/constant/SSA matching:** Yes — type required: integer scalar/vector with the stated bit width; recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0879"></a>

## IS0879 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:878–879](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L878-L879). Kind: delegation.
- **Rewrite:** Threading Sub over selects and phi nodes is pointless, so don't bother. Threading over the select in "A - select(cond, B, C)" means evaluating "A-B" and "A-C" and seeing if they are equal; but they are equal if and only if B and C are equal.  If B and C are equal then (since we assume that operands have already been simplified) "select(cond, B, C)" should have been simplified to the common value of B and C already.  Analysing "A-B" and "A-C" thus gains nothing, but costs compile time.  Similarly for threading over phi nodes.; returns `V`. Guard: `Value *V = simplifyByDomEq(Instruction::Sub, Op0, Op1, Q, MaxRecurse)`. Delegates to `simplifyByDomEq`.
- **Matched/replaced opcodes:** `sub`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Simple internal forwarding to already inventoried helper cases; this return adds no distinct rewrite equation. Calls simplifyByDomEq, which checks a dominating equality certificate and does not recurse.

<a id="is0886"></a>

## IS0886 — `simplifySubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:884–886](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L884-L886). Kind: rewrite.
- **Rewrite:** (sub nuw C_Mask, (xor X, C_Mask)) -> X; returns `X`. Guard: `IsNUW` and `match(Op1, m_Xor(m_Value(X), m_Specific(Op0))) && match(Op0, m_LowBitMask())`.
- **Matched/replaced opcodes:** `sub`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: nuw flag.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Arbitrary scalar integer widths and signedness attributes; every source no-wrap/exact requirement preserved, all other flags arbitrary, poison refinement included.
- **Lean:** [Veir/InstSimplify/IS0886.lean](../../Veir/InstSimplify/IS0886.lean).
- **Theorems:** `Veir.InstSimplify.IS0886.valid`.
- **Details / missing facilities:** Checked by Lean; APInt-bit matching admits all equivalent signed/unsigned/i1 integer attribute spellings.

<a id="is0902"></a>

## IS0902 — `simplifyMulInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:901–902](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L901-L902). Kind: delegation.
- **Rewrite:** Given operands for a Mul, see if we can fold the result. If not, this returns null.; returns `C`. Guard: `Constant *C = foldOrCommuteConstant(Instruction::Mul, Op0, Op1, Q)`. Delegates to `foldOrCommuteConstant`.
- **Matched/replaced opcodes:** `mul`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar integer constants only, arbitrary widths and source flags.
- **Lean:** [Veir/InstSimplify/IS0582.lean](../../Veir/InstSimplify/IS0582.lean).
- **Theorems:** `Veir.InstSimplify.IS0582.pattern_mul_valid`.
- **Shared implementation:** [IS0582](#is0582). This caller is not an additional independent port.
- **Details / missing facilities:** Dispatch covered by numerical and poison-output scalar constant-folding patterns in IS0582, matching LLVM outputs. Not counted as an independent rewrite; other constant classes lack interpreter support.

<a id="is0906"></a>

## IS0906 — `simplifyMulInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:905–906](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L905-L906). Kind: rewrite.
- **Rewrite:** X * poison -> poison; returns `Op1`. Guard: `isa<PoisonValue>(Op1)`.
- **Matched/replaced opcodes:** `mul`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM poison propagation semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS0906.lean](../../Veir/InstSimplify/IS0906.lean).
- **Theorems:** `Veir.InstSimplify.IS0906.pattern_valid`, `Veir.InstSimplify.IS0906.pattern_left_valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is0911"></a>

## IS0911 — `simplifyMulInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:910–911](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L910-L911). Kind: rewrite.
- **Rewrite:** `mul X,0 -> 0`, with either operand order. The undef alternative at this return is recorded separately as IS0911u.
- **Matched/replaced opcodes:** `mul`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM undef nondeterministic semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Both operand orders, all scalar widths and flags for zero multiplication; undef scalar alternative has no interpreter semantics.
- **Lean:** [Veir/InstSimplify/IS0911.lean](../../Veir/InstSimplify/IS0911.lean).
- **Theorems:** `Veir.InstSimplify.IS0911.pattern_valid`, `Veir.InstSimplify.IS0911.pattern_left_valid`.
- **Details / missing facilities:** Both scalar zero-multiply branches compiled; the separate IS0911u catalog entry records the unsupported undef alternative.

<a id="is0911u"></a>

## IS0911u — `simplifyMulInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:910–911](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L910-L911). Kind: rewrite.
- **Rewrite:** `mul X,undef -> 0`, with either operand order.
- **Matched/replaced opcodes:** `mul`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM undef nondeterministic semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Details / missing facilities:** LLVM undef is not represented by LLVM.Int and mlir__undef has no successful interpretation in Llvm.interpretOp'. Poison is a distinct value and cannot substitute for undef. No vacuous Pattern.Valid proof from the missing interpreter case is claimed.

<a id="is0915"></a>

## IS0915 — `simplifyMulInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:914–915](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L914-L915). Kind: rewrite.
- **Rewrite:** X * 1 -> X; returns `Op0`. Guard: `match(Op1, m_One())`.
- **Matched/replaced opcodes:** `mul`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS0915.lean](../../Veir/InstSimplify/IS0915.lean).
- **Theorems:** `Veir.InstSimplify.IS0915.pattern_valid`, `Veir.InstSimplify.IS0915.pattern_left_valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is0923"></a>

## IS0923 — `simplifyMulInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:922–923](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L922-L923). Kind: rewrite.
- **Rewrite:** (X / Y) * Y -> X if the division is exact.; returns `X`. Guard: `Q.IIQ.UseInstrInfo && (match(Op0, m_Exact(m_IDiv(m_Value(X), m_Specific(Op1)))) || // (X / Y) * Y match(Op1, m_Exact(m_IDiv(m_Value(X), m_Specific(Op0)))))) // Y * (X / Y`.
- **Matched/replaced opcodes:** `mul`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: exact operator flag; instruction property required: InstrInfoQuery operator flags; instruction property required: operator flags via InstrInfoQuery.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Arbitrary scalar integer widths and signedness attributes; every source no-wrap/exact requirement preserved, all other flags arbitrary, poison refinement included.
- **Lean:** [Veir/InstSimplify/IS0923.lean](../../Veir/InstSimplify/IS0923.lean).
- **Theorems:** `Veir.InstSimplify.IS0923.pattern_udiv_valid`, `Veir.InstSimplify.IS0923.pattern_udiv_left_valid`, `Veir.InstSimplify.IS0923.pattern_sdiv_valid`, `Veir.InstSimplify.IS0923.pattern_sdiv_left_valid`.
- **Details / missing facilities:** Checked by Lean; APInt-bit matching admits all equivalent signed/unsigned/i1 integer attribute spellings.

<a id="is0929"></a>

## IS0929 — `simplifyMulInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:926–929](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L926-L929). Kind: rewrite.
- **Rewrite:** mul i1 nsw is a special-case because -1 * -1 is poison (+1 is not representable). All other cases reduce to 0, so just return 0.; returns `ConstantInt::getNullValue(Op0->getType())`. Guard: `Op0->getType()->isIntOrIntVectorTy(1)` and `Q.IIQ.UseInstrInfo && (match(Op0, m_Exact(m_IDiv(m_Value(X), m_Specific(Op1)))) || // (X / Y) * Y match(Op1, m_Exact(m_IDiv(m_Value(X), m_Specific(Op0)))))) // Y * (X / Y` and `IsNSW`.
- **Matched/replaced opcodes:** `mul`.
- **Beyond opcode/constant/SSA matching:** Yes — type required: i1 scalar or vector; instruction flag: `nsw`.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS0929.lean](../../Veir/InstSimplify/IS0929.lean).
- **Theorems:** `Veir.InstSimplify.IS0929.valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is0934"></a>

## IS0934 — `simplifyMulInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:930–934](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L930-L934). Kind: delegation.
- **Rewrite:** For i1 operands, treat multiplication as bitwise AND and return the recursive `simplifyAndInst` result when it simplifies. Guard: `Op0->getType()->isIntOrIntVectorTy(1)` and `MaxRecurse`.
- **Matched/replaced opcodes:** `mul`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: exact operator flag; instruction property required: InstrInfoQuery operator flags; instruction property required: operator flags via InstrInfoQuery; type required: integer scalar/vector with the stated bit width; recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0940"></a>

## IS0940 — `simplifyMulInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:939–940](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L939-L940). Kind: delegation.
- **Rewrite:** Try some generic simplifications for associative operations.; returns `V`. Guard: `Value *V = simplifyAssociativeBinOp(Instruction::Mul, Op0, Op1, Q, MaxRecurse)`. Delegates to `simplifyAssociativeBinOp`.
- **Matched/replaced opcodes:** `mul`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0945"></a>

## IS0945 — `simplifyMulInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:944–945](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L944-L945). Kind: delegation.
- **Rewrite:** Mul distributes over Add. Try some generic simplifications based on this.; returns `V`. Guard: `Value *V = expandCommutativeBinOp(Instruction::Mul, Op0, Op1, Instruction::Add, Q, MaxRecurse)`. Delegates to `expandCommutativeBinOp`.
- **Matched/replaced opcodes:** `mul`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0952"></a>

## IS0952 — `simplifyMulInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:950–952](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L950-L952). Kind: delegation.
- **Rewrite:** If the operation is with the result of a select instruction, check whether operating on either branch of the select always yields the same value.; returns `V`. Guard: `isa<SelectInst>(Op0) || isa<SelectInst>(Op1)` and `Value *V = threadBinOpOverSelect(Instruction::Mul, Op0, Op1, Q, MaxRecurse)`. Delegates to `threadBinOpOverSelect`.
- **Matched/replaced opcodes:** `mul`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive simplifier schema/dispatch: Puddle has no recursive engine whose successful result is accompanied by a refinement proof and recursion-budget invariant. A single fixed instance cannot establish this schema.

<a id="is0959"></a>

## IS0959 — `simplifyMulInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:957–959](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L957-L959). Kind: delegation.
- **Rewrite:** If the operation is with the result of a phi instruction, check whether operating on all incoming values of the phi always yields the same value.; returns `V`. Guard: `isa<PHINode>(Op0) || isa<PHINode>(Op1)` and `Value *V = threadBinOpOverPHI(Instruction::Mul, Op0, Op1, Q, MaxRecurse)`. Delegates to `threadBinOpOverPHI`.
- **Matched/replaced opcodes:** `mul`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** LLVM PHI opcode/incoming-edge semantics and dominating-edge ValueTracking facts are not represented by Puddle Models.

<a id="is1016"></a>

## IS1016 — `isDivZero`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1013–1016](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1013-L1016). Kind: rewrite.
- **Rewrite:** Special-case: we can't take the abs() of a minimum signed value. If that's the divisor, then all we have to do is prove that the dividend is also not the minimum signed value.; returns `isICmpTrue(CmpInst::ICMP_NE, X, Y, Q, MaxRecurse)`. Guard: `IsSigned` and `match(Y, m_APInt(C))` and `C->isMinSignedValue()`.
- **Matched/replaced opcodes:** `sdiv`, `udiv`, `srem`, `urem`, `icmp`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Calls recursively simplified icmp and requires its semantic correctness plus path-sensitive magnitude analysis; no recursive simplifier composition interface.

<a id="is1057"></a>

## IS1057 — `simplifyDivRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1056–1057](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1056-L1057). Kind: schema.
- **Rewrite:** `sdiv`, `udiv`, `srem`, or `urem` with a poison divisor folds to poison. The undef alternative at this return is IS1057u.
- **Matched/replaced opcodes:** `sdiv`, `udiv`, `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions; LLVM undef nondeterministic semantics; LLVM poison propagation semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All four scalar div/rem opcodes with poison divisor; undef divisor has no interpreter semantics.
- **Lean:** [Veir/InstSimplify/IS1057.lean](../../Veir/InstSimplify/IS1057.lean).
- **Theorems:** `Veir.InstSimplify.IS1057.pattern_sdiv_valid`, `Veir.InstSimplify.IS1057.sdiv_source_ub`, `Veir.InstSimplify.IS1057.pattern_udiv_valid`, `Veir.InstSimplify.IS1057.udiv_source_ub`, `Veir.InstSimplify.IS1057.pattern_srem_valid`, `Veir.InstSimplify.IS1057.srem_source_ub`, `Veir.InstSimplify.IS1057.pattern_urem_valid`, `Veir.InstSimplify.IS1057.urem_source_ub`.
- **Details / missing facilities:** Explicit source_ub lemmas prove immediate UB for poison divisor, not interpreter failure. Valid follows because no source .ok execution exists. Separate IS1057u records the unsupported undef divisor.

<a id="is1057u"></a>

## IS1057u — `simplifyDivRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1056–1057](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1056-L1057). Kind: rewrite.
- **Rewrite:** `sdiv X,undef`, `udiv X,undef`, `srem X,undef`, and `urem X,undef` fold to poison.
- **Matched/replaced opcodes:** `sdiv`, `udiv`, `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions; LLVM undef nondeterministic semantics; LLVM poison propagation semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Details / missing facilities:** LLVM undef is not represented by LLVM.Int and mlir__undef has no successful interpretation in Llvm.interpretOp'. Poison is a distinct value and cannot substitute for undef. No vacuous Pattern.Valid proof from the missing interpreter case is claimed.

<a id="is1063"></a>

## IS1063 — `simplifyDivRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1062–1063](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1062-L1063). Kind: schema.
- **Rewrite:** X / 0 -> poison X % 0 -> poison We don't need to preserve faults!; returns `PoisonValue::get(Ty)`. Guard: `match(Op1, m_Zero())`.
- **Matched/replaced opcodes:** `sdiv`, `udiv`, `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions; LLVM poison propagation semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS1063.lean](../../Veir/InstSimplify/IS1063.lean).
- **Theorems:** `Veir.InstSimplify.IS1063.pattern_sdiv_valid`, `Veir.InstSimplify.IS1063.sdiv_source_ub`, `Veir.InstSimplify.IS1063.pattern_udiv_valid`, `Veir.InstSimplify.IS1063.udiv_source_ub`, `Veir.InstSimplify.IS1063.pattern_srem_valid`, `Veir.InstSimplify.IS1063.srem_source_ub`, `Veir.InstSimplify.IS1063.pattern_urem_valid`, `Veir.InstSimplify.IS1063.urem_source_ub`.
- **Details / missing facilities:** Explicit source_ub operational lemmas prove actual immediate UB for all four opcodes. Pattern.Valid follows because there is no defined source .ok execution; this is not an unsupported-opcode failure.

<a id="is1068"></a>

## IS1068 — `simplifyDivRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1067–1068](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1067-L1068). Kind: schema.
- **Rewrite:** poison / X -> poison poison % X -> poison; returns `Op0`. Guard: `isa<PoisonValue>(Op0)`.
- **Matched/replaced opcodes:** `sdiv`, `udiv`, `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions; LLVM poison propagation semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS1068.lean](../../Veir/InstSimplify/IS1068.lean).
- **Theorems:** `Veir.InstSimplify.IS1068.pattern_sdiv_valid`, `Veir.InstSimplify.IS1068.pattern_udiv_valid`, `Veir.InstSimplify.IS1068.pattern_srem_valid`, `Veir.InstSimplify.IS1068.pattern_urem_valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is1073"></a>

## IS1073 — `simplifyDivRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1072–1073](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1072-L1073). Kind: schema.
- **Rewrite:** undef / X -> 0 undef % X -> 0; returns `Constant::getNullValue(Ty)`. Guard: `Q.isUndefValue(Op0)`.
- **Matched/replaced opcodes:** `sdiv`, `udiv`, `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions; LLVM undef nondeterministic semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** LLVM undef has no interpretOp' semantics: .mlir__undef falls through to failure. This branch cannot be proved by a vacuous successful-interpretation assumption.

<a id="is1078"></a>

## IS1078 — `simplifyDivRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1077–1078](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1077-L1078). Kind: schema.
- **Rewrite:** 0 / X -> 0 0 % X -> 0; returns `Constant::getNullValue(Op0->getType())`. Guard: `match(Op0, m_Zero())`.
- **Matched/replaced opcodes:** `sdiv`, `udiv`, `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS1078.lean](../../Veir/InstSimplify/IS1078.lean).
- **Theorems:** `Veir.InstSimplify.IS1078.pattern_sdiv_valid`, `Veir.InstSimplify.IS1078.pattern_udiv_valid`, `Veir.InstSimplify.IS1078.pattern_srem_valid`, `Veir.InstSimplify.IS1078.pattern_urem_valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is1083"></a>

## IS1083 — `simplifyDivRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1082–1083](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1082-L1083). Kind: schema.
- **Rewrite:** X / X -> 1 X % X -> 0; returns `IsDiv ? ConstantInt::get(Ty, 1) : Constant::getNullValue(Ty)`. Guard: `Op0 == Op1`.
- **Matched/replaced opcodes:** `sdiv`, `udiv`, `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS1083.lean](../../Veir/InstSimplify/IS1083.lean).
- **Theorems:** `Veir.InstSimplify.IS1083.pattern_sdiv_valid`, `Veir.InstSimplify.IS1083.pattern_udiv_valid`, `Veir.InstSimplify.IS1083.pattern_srem_valid`, `Veir.InstSimplify.IS1083.pattern_urem_valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is1092"></a>

## IS1092 — `simplifyDivRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1091–1092](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1091-L1092). Kind: schema.
- **Rewrite:** X / 0 -> poison X % 0 -> poison If the divisor is known to be zero, just return poison. This can happen in some cases where its provable indirectly the denominator is zero but it's not trivially simplifiable (i.e known zero through a phi node).; returns `PoisonValue::get(Ty)`. Guard: `Known.isZero()`.
- **Matched/replaced opcodes:** `sdiv`, `udiv`, `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions; LLVM poison propagation semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** computeKnownBits divisor-is-zero result has no semantic bridge into Models.

<a id="is1100"></a>

## IS1100 — `simplifyDivRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1099–1100](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1099-L1100). Kind: schema.
- **Rewrite:** X / 1 -> X X % 1 -> 0 If the divisor can only be zero or one, we can't have division-by-zero or remainder-by-zero, so assume the divisor is 1. e.g. 1, zext (i8 X), sdiv X (Y and 1); returns `IsDiv ? Op0 : Constant::getNullValue(Ty)`. Guard: `Known.countMinLeadingZeros() == Known.getBitWidth() - 1`.
- **Matched/replaced opcodes:** `sdiv`, `udiv`, `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** computeKnownBits zero-or-one result has no semantic bridge into Models; literal-one specialization remains representable.

<a id="is1114"></a>

## IS1114 — `simplifyDivRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1112–1114](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1112-L1114). Kind: schema.
- **Rewrite:** The multiplication can't overflow if it is defined not to, or if X == A / Y for some A.; returns `IsDiv ? X : Constant::getNullValue(Op0->getType())`. Guard: `match(Op0, m_c_Mul(m_Value(X), m_Specific(Op1)))` and `(IsSigned && Q.IIQ.hasNoSignedWrap(Mul)) || (!IsSigned && Q.IIQ.hasNoUnsignedWrap(Mul)) || (IsSigned && match(X, m_SDiv(m_Value(), m_Specific(Op1)))) || (!IsSigned && match(X, m_UDiv(m_Value(), m_Specific(Op1))))`.
- **Matched/replaced opcodes:** `sdiv`, `udiv`, `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: operator flags via InstrInfoQuery; generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Arbitrary scalar integer widths/signedness, poison included; source NSW/NUW conditions preserved and all other flags arbitrary.
- **Lean:** [Veir/InstSimplify/IS1114.lean](../../Veir/InstSimplify/IS1114.lean).
- **Theorems:** `Veir.InstSimplify.IS1114.pattern_sdiv_valid`, `Veir.InstSimplify.IS1114.pattern_sdiv_commute_valid`, `Veir.InstSimplify.IS1114.pattern_udiv_valid`, `Veir.InstSimplify.IS1114.pattern_udiv_commute_valid`, `Veir.InstSimplify.IS1114.pattern_srem_valid`, `Veir.InstSimplify.IS1114.pattern_srem_commute_valid`, `Veir.InstSimplify.IS1114.pattern_urem_valid`, `Veir.InstSimplify.IS1114.pattern_urem_commute_valid`, `Veir.InstSimplify.IS1114.pattern_quotient_sdiv_valid`, `Veir.InstSimplify.IS1114.pattern_quotient_sdiv_commute_valid`, `Veir.InstSimplify.IS1114.pattern_quotient_udiv_valid`, `Veir.InstSimplify.IS1114.pattern_quotient_udiv_commute_valid`, `Veir.InstSimplify.IS1114.pattern_quotient_srem_valid`, `Veir.InstSimplify.IS1114.pattern_quotient_srem_commute_valid`, `Veir.InstSimplify.IS1114.pattern_quotient_urem_valid`, `Veir.InstSimplify.IS1114.pattern_quotient_urem_commute_valid`.
- **Details / missing facilities:** All4 div/rem opcodes, both multiplier orders, both source no-wrap flags and recognized same-divisor quotient alternative proved. Arbitrary exact flags and all remaining multiply flags preserved.

<a id="is1119"></a>

## IS1119 — `simplifyDivRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1118–1119](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1118-L1119). Kind: schema.
- **Rewrite:** For division or remainder of a product by one factor, use `isDivZero` to detect when the product's other factor must be zero; return zero for division or the original product for remainder.
- **Matched/replaced opcodes:** `sdiv`, `udiv`, `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: division-to-zero analysis; generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** isDivZero depends on recursive icmp simplification and computeKnownBits; no semantic composition/analysis bridge.

<a id="is1122"></a>

## IS1122 — `simplifyDivRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1121–1122](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1121-L1122). Kind: delegation.
- **Rewrite:** Apply the dominance-based equality simplifier to the division or remainder operands; return its result when it finds an equivalent value.
- **Matched/replaced opcodes:** `sdiv`, `udiv`, `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Simple internal forwarding to already inventoried helper cases; this return adds no distinct rewrite equation. Calls simplifyByDomEq, which checks a dominating equality certificate and does not recurse.

<a id="is1128"></a>

## IS1128 — `simplifyDivRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1126–1128](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1126-L1128). Kind: schema.
- **Rewrite:** If the operation is with the result of a select instruction, check whether operating on either branch of the select always yields the same value.; returns `V`. Guard: `isa<SelectInst>(Op0) || isa<SelectInst>(Op1)` and `Value *V = threadBinOpOverSelect(Opcode, Op0, Op1, Q, MaxRecurse)`.
- **Matched/replaced opcodes:** `sdiv`, `udiv`, `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive threadBinOpOverSelect schema requires semantic certificates for both recursively simplified arms and their recursion budget; Puddle has no engine/composition contract for this schema.

<a id="is1134"></a>

## IS1134 — `simplifyDivRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1132–1134](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1132-L1134). Kind: schema.
- **Rewrite:** If the operation is with the result of a phi instruction, check whether operating on all incoming values of the phi always yields the same value.; returns `V`. Guard: `isa<PHINode>(Op0) || isa<PHINode>(Op1)` and `Value *V = threadBinOpOverPHI(Opcode, Op0, Op1, Q, MaxRecurse)`.
- **Matched/replaced opcodes:** `sdiv`, `udiv`, `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** LLVM PHI opcode/incoming-edge semantics and dominating-edge ValueTracking facts are not represented by Puddle Models.

<a id="is1144"></a>

## IS1144 — `simplifyDiv`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1143–1144](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1143-L1144). Kind: delegation.
- **Rewrite:** These are simplifications common to SDiv and UDiv.; returns `C`. Guard: `Constant *C = foldOrCommuteConstant(Opcode, Op0, Op1, Q)`. Delegates to `foldOrCommuteConstant`.
- **Matched/replaced opcodes:** `sdiv`, `udiv`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar integer constants only, arbitrary widths and source flags.
- **Lean:** [Veir/InstSimplify/IS0582.lean](../../Veir/InstSimplify/IS0582.lean).
- **Theorems:** `Veir.InstSimplify.IS0582.pattern_sdiv_valid`, `Veir.InstSimplify.IS0582.pattern_udiv_valid`, `Veir.InstSimplify.IS0582.pattern_sdiv_poison_valid`, `Veir.InstSimplify.IS0582.pattern_udiv_poison_valid`.
- **Shared implementation:** [IS0582](#is0582). This caller is not an additional independent port.
- **Details / missing facilities:** Dispatch covered by numerical and poison-output scalar constant-folding patterns in IS0582, matching LLVM outputs. Not counted as an independent rewrite; other constant classes lack interpreter support.

<a id="is1147"></a>

## IS1147 — `simplifyDiv`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1146–1147](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1146-L1147). Kind: schema.
- **Rewrite:** These are simplifications common to SDiv and UDiv.; returns `V`. Guard: `Value *V = simplifyDivRem(Opcode, Op0, Op1, Q, MaxRecurse)`.
- **Matched/replaced opcodes:** `sdiv`, `udiv`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Simple internal forwarding to already inventoried helper cases; this return adds no distinct rewrite equation.

<a id="is1157"></a>

## IS1157 — `simplifyDiv`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1154–1157](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1154-L1157). Kind: schema.
- **Rewrite:** If this is an exact divide by a constant, then the dividend (Op0) must have at least as many trailing zeros as the divisor to divide evenly. If it has less trailing zeros, then the result must be poison.; returns `PoisonValue::get(Op0->getType())`. Guard: `IsExact && match(Op1, m_APInt(DivC))` and `DivC->countr_zero()` and `KnownOp0.countMaxTrailingZeros() < DivC->countr_zero()`.
- **Matched/replaced opcodes:** `sdiv`, `udiv`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-bits/sign-bit/range facts computed from operands; instruction property required: exact flag; generic recursive schema; preserve source recursion bound and associativity/commutativity conditions; LLVM poison propagation semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** computeKnownBits maximum trailing-zero analysis has no semantic bridge into Models.

<a id="is1168"></a>

## IS1168 — `simplifyDiv`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1166–1168](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1166-L1168). Kind: schema.
- **Rewrite:** udiv exact (mul nsw X, C), C --> X sdiv exact (mul nuw X, C), C --> X where C is not a power of 2.; returns `X`. Guard: `IsExact && match(Op1, m_APInt(DivC))` and `!DivC->isPowerOf2() && (Opcode == Instruction::UDiv ? match(Op0, m_NSWMul(m_Value(X), m_Specific(Op1))) : match(Op0, m_NUWMul(m_Value(X), m_Specific(Op1))))`.
- **Matched/replaced opcodes:** `sdiv`, `udiv`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: exact flag; instruction property required: no-unsigned-wrap operator flag; instruction property required: no-signed-wrap operator flag; generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Both scalar rules: udiv exact after nsw multiplication, sdiv exact after nuw multiplication; arbitrary integer widths/signedness, all other flags arbitrary; nonzero/non-power-of-two divisor.
- **Lean:** [Veir/InstSimplify/IS1168.lean](../../Veir/InstSimplify/IS1168.lean).
- **Theorems:** `Veir.InstSimplify.IS1168.guard_equivalent_to_source`, `Veir.InstSimplify.IS1168.pattern_udiv_valid`, `Veir.InstSimplify.IS1168.pattern_sdiv_valid`.
- **Details / missing facilities:** Both cross-wrap bridge theorems and power-of-two-divisor characterization proved without axioms. Native non-divisor-of2^width guard is proved equivalent to the source non-power-of-two test after the earlier zero-divisor case, via guard_equivalent_to_source. Compiled by Lean.

<a id="is1178"></a>

## IS1178 — `simplifyRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1177–1178](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1177-L1178). Kind: delegation.
- **Rewrite:** These are simplifications common to SRem and URem.; returns `C`. Guard: `Constant *C = foldOrCommuteConstant(Opcode, Op0, Op1, Q)`. Delegates to `foldOrCommuteConstant`.
- **Matched/replaced opcodes:** `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar integer constants only, arbitrary widths and source flags.
- **Lean:** [Veir/InstSimplify/IS0582.lean](../../Veir/InstSimplify/IS0582.lean).
- **Theorems:** `Veir.InstSimplify.IS0582.pattern_srem_valid`, `Veir.InstSimplify.IS0582.pattern_urem_valid`, `Veir.InstSimplify.IS0582.pattern_srem_poison_valid`, `Veir.InstSimplify.IS0582.pattern_urem_poison_valid`.
- **Shared implementation:** [IS0582](#is0582). This caller is not an additional independent port.
- **Details / missing facilities:** Dispatch covered by numerical and poison-output scalar constant-folding patterns in IS0582, matching LLVM outputs. Not counted as an independent rewrite; other constant classes lack interpreter support.

<a id="is1181"></a>

## IS1181 — `simplifyRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1180–1181](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1180-L1181). Kind: schema.
- **Rewrite:** These are simplifications common to SRem and URem.; returns `V`. Guard: `Value *V = simplifyDivRem(Opcode, Op0, Op1, Q, MaxRecurse)`.
- **Matched/replaced opcodes:** `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Simple internal forwarding to already inventoried helper cases; this return adds no distinct rewrite equation.

<a id="is1189"></a>

## IS1189 — `simplifyRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1187–1189](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1187-L1189). Kind: schema.
- **Rewrite:** (X << Y) % X -> 0; returns `Constant::getNullValue(Op0->getType())`. Guard: `Q.IIQ.UseInstrInfo` and `(Opcode == Instruction::SRem && match(Op0, m_NSWShl(m_Specific(Op1), m_Value()))) || (Opcode == Instruction::URem && match(Op0, m_NUWShl(m_Specific(Op1), m_Value())))`.
- **Matched/replaced opcodes:** `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: no-unsigned-wrap operator flag; instruction property required: no-signed-wrap operator flag; instruction property required: InstrInfoQuery operator flags; instruction property required: operator flags via InstrInfoQuery; generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Arbitrary scalar integer widths/signedness, poison included; source NSW/NUW conditions preserved and all other flags arbitrary.
- **Lean:** [Veir/InstSimplify/IS1189.lean](../../Veir/InstSimplify/IS1189.lean).
- **Theorems:** `Veir.InstSimplify.IS1189.pattern_srem_valid`, `Veir.InstSimplify.IS1189.pattern_urem_valid`.
- **Details / missing facilities:** Checked by Lean, all scalar syntactic branches represented.

<a id="is1198"></a>

## IS1198 — `simplifyRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1195–1198](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1195-L1198). Kind: schema.
- **Rewrite:** (srem (mul nsw X, C1), C0) -> 0 if C1 s% C0 == 0 (urem (mul nuw X, C1), C0) -> 0 if C1 u% C0 == 0; returns `C.srem(*C0).isZero()`. Guard: `Q.IIQ.UseInstrInfo` and `match(Op1, m_APInt(C0))` and `Opcode == Instruction::SRem ? match(Op0, m_NSWMul(m_Value(), m_CheckedInt([C0](const APInt &C) { return C.srem(*C0).isZero(); }))) : match(Op0, m_NUWMul(m_Value(), m_CheckedInt([C0](const APInt &C) { return C.urem(*C0).isZero(); })))`.
- **Matched/replaced opcodes:** `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: no-unsigned-wrap operator flag; instruction property required: no-signed-wrap operator flag; instruction property required: InstrInfoQuery operator flags; instruction property required: operator flags via InstrInfoQuery; generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Native metadata predicate inside IS1204 scalar constant-multiple remainder rule.
- **Lean:** [Veir/InstSimplify/IS1204.lean](../../Veir/InstSimplify/IS1204.lean).
- **Theorems:** `Veir.InstSimplify.IS1204.pattern_srem_valid`.
- **Shared implementation:** [IS1204](#is1204). This caller is not an additional independent port.
- **Details / missing facilities:** Not an independent rewrite: callback C1 srem/urem C0 ==0 is implemented as the bitvector metadata guard in IS1204.

<a id="is1202"></a>

## IS1202 — `simplifyRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1200–1202](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1200-L1202). Kind: schema.
- **Rewrite:** (srem (mul nsw X, C1), C0) -> 0 if C1 s% C0 == 0 (urem (mul nuw X, C1), C0) -> 0 if C1 u% C0 == 0; returns `C.urem(*C0).isZero()`. Guard: `Q.IIQ.UseInstrInfo` and `match(Op1, m_APInt(C0))`.
- **Matched/replaced opcodes:** `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: InstrInfoQuery operator flags; instruction property required: operator flags via InstrInfoQuery; generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Native metadata predicate inside IS1204 scalar constant-multiple remainder rule.
- **Lean:** [Veir/InstSimplify/IS1204.lean](../../Veir/InstSimplify/IS1204.lean).
- **Theorems:** `Veir.InstSimplify.IS1204.pattern_urem_valid`.
- **Shared implementation:** [IS1204](#is1204). This caller is not an additional independent port.
- **Details / missing facilities:** Not an independent rewrite: callback C1 srem/urem C0 ==0 is implemented as the bitvector metadata guard in IS1204.

<a id="is1204"></a>

## IS1204 — `simplifyRem`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1202–1204](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1202-L1204). Kind: schema.
- **Rewrite:** (srem (mul nsw X, C1), C0) -> 0 if C1 s% C0 == 0 (urem (mul nuw X, C1), C0) -> 0 if C1 u% C0 == 0; returns `Constant::getNullValue(Op0->getType())`. Guard: `Q.IIQ.UseInstrInfo` and `match(Op1, m_APInt(C0))`.
- **Matched/replaced opcodes:** `srem`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: InstrInfoQuery operator flags; instruction property required: operator flags via InstrInfoQuery; generic recursive schema; preserve source recursion bound and associativity/commutativity conditions.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Arbitrary scalar integer widths/signedness, poison included; source NSW/NUW conditions preserved and all other flags arbitrary.
- **Lean:** [Veir/InstSimplify/IS1204.lean](../../Veir/InstSimplify/IS1204.lean).
- **Theorems:** `Veir.InstSimplify.IS1204.pattern_srem_valid`, `Veir.InstSimplify.IS1204.pattern_urem_valid`.
- **Details / missing facilities:** Checked by Lean, all scalar syntactic branches represented.

<a id="is1216"></a>

## IS1216 — `simplifySDivInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1215–1216](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1215-L1216). Kind: rewrite.
- **Rewrite:** sdiv X,Y -> -1 when isKnownNegation(X,Y,NeedNSW=true) proves opposite operands without signed negation overflow.
- **Matched/replaced opcodes:** `sdiv`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-negation analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** External isKnownNegation NeedNSW analysis has no semantic specification or bridge for its full operand language.

<a id="is1218"></a>

## IS1218 — `simplifySDivInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1218–1218](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1218). Kind: delegation.
- **Rewrite:** Fallback delegation to common SDiv simplification after the known-negation special case does not fire.
- **Matched/replaced opcodes:** `sdiv`.
- **Beyond opcode/constant/SSA matching:** Yes — shared simplification schema; preserve exactness flag and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Simple internal forwarding to already inventoried helper cases; this return adds no distinct rewrite equation.

<a id="is1230"></a>

## IS1230 — `simplifyUDivInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1230–1230](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1230). Kind: delegation.
- **Rewrite:** Delegate UDiv folding to shared `simplifyDiv`.
- **Matched/replaced opcodes:** `udiv`.
- **Beyond opcode/constant/SSA matching:** Yes — shared simplification schema; preserve exactness flag and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Simple internal forwarding to already inventoried helper cases; this return adds no distinct rewrite equation.

<a id="is1246"></a>

## IS1246 — `simplifySRemInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1245–1246](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1245-L1246). Kind: rewrite.
- **Rewrite:** If the divisor is 0, the result is undefined, so assume the divisor is -1. srem Op0, (sext i1 X) --> srem Op0, -1 --> 0; returns `ConstantInt::getNullValue(Op0->getType())`. Guard: `match(Op1, m_SExt(m_Value(X))) && X->getType()->isIntOrIntVectorTy(1)`.
- **Matched/replaced opcodes:** `srem`, `sext`.
- **Beyond opcode/constant/SSA matching:** Yes — type required: integer scalar/vector with the stated bit width.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Arbitrary scalar integer widths and signedness attributes; every source no-wrap/exact requirement preserved, all other flags arbitrary, poison refinement included.
- **Lean:** [Veir/InstSimplify/IS1246.lean](../../Veir/InstSimplify/IS1246.lean).
- **Theorems:** `Veir.InstSimplify.IS1246.valid`.
- **Details / missing facilities:** Checked by Lean; APInt-bit matching admits all equivalent signed/unsigned/i1 integer attribute spellings.

<a id="is1250"></a>

## IS1250 — `simplifySRemInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1249–1250](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1249-L1250). Kind: rewrite.
- **Rewrite:** If the two operands are negated, return 0.; returns `ConstantInt::getNullValue(Op0->getType())`. Guard: `isKnownNegation(Op0, Op1)`.
- **Matched/replaced opcodes:** `srem`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-negation analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** External isKnownNegation analysis has no semantic specification or bridge for its full operand language.

<a id="is1252"></a>

## IS1252 — `simplifySRemInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1252–1252](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1252). Kind: delegation.
- **Rewrite:** Fallback delegation to common SRem simplification after the i1 sign-extension and known-negation special cases do not fire.
- **Matched/replaced opcodes:** `srem`.
- **Beyond opcode/constant/SSA matching:** Yes — shared simplification schema and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Simple internal forwarding to already inventoried helper cases; this return adds no distinct rewrite equation.

<a id="is1263"></a>

## IS1263 — `simplifyURemInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1263–1263](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1263). Kind: delegation.
- **Rewrite:** Delegate URem folding to shared `simplifyRem`.
- **Matched/replaced opcodes:** `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — shared simplification schema and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Simple internal forwarding to already inventoried helper cases; this return adds no distinct rewrite equation.

<a id="is1306"></a>

## IS1306 — `simplifyShift`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1305–1306](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1305-L1306). Kind: delegation.
- **Rewrite:** Given operands for an Shl, LShr or AShr, see if we can fold the result. If not, this returns null.; returns `C`. Guard: `Constant *C = foldOrCommuteConstant(Opcode, Op0, Op1, Q)`. Delegates to `foldOrCommuteConstant`.
- **Matched/replaced opcodes:** `shl`, `lshr`, `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget; shared shift schema for the named opcode family; preserve poison shift-amount and exactness/nowrap semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar integer constants only, arbitrary widths and source flags.
- **Lean:** [Veir/InstSimplify/IS0582.lean](../../Veir/InstSimplify/IS0582.lean).
- **Theorems:** `Veir.InstSimplify.IS0582.pattern_shl_valid`, `Veir.InstSimplify.IS0582.pattern_lshr_valid`, `Veir.InstSimplify.IS0582.pattern_ashr_valid`, `Veir.InstSimplify.IS0582.pattern_shl_poison_valid`, `Veir.InstSimplify.IS0582.pattern_lshr_poison_valid`, `Veir.InstSimplify.IS0582.pattern_ashr_poison_valid`.
- **Shared implementation:** [IS0582](#is0582). This caller is not an additional independent port.
- **Details / missing facilities:** Dispatch covered by numerical and poison-output scalar constant-folding patterns in IS0582, matching LLVM outputs. Not counted as an independent rewrite; other constant classes lack interpreter support.

<a id="is1310"></a>

## IS1310 — `simplifyShift`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1309–1310](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1309-L1310). Kind: schema.
- **Rewrite:** poison shift by X -> poison; returns `Op0`. Guard: `isa<PoisonValue>(Op0)`.
- **Matched/replaced opcodes:** `shl`, `lshr`, `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — shared shift schema for the named opcode family; preserve poison shift-amount and exactness/nowrap semantics; LLVM poison propagation semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS1310.lean](../../Veir/InstSimplify/IS1310.lean).
- **Theorems:** `Veir.InstSimplify.IS1310.pattern_shl_left_valid`, `Veir.InstSimplify.IS1310.pattern_lshr_left_valid`, `Veir.InstSimplify.IS1310.pattern_ashr_left_valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is1314"></a>

## IS1314 — `simplifyShift`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1313–1314](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1313-L1314). Kind: schema.
- **Rewrite:** 0 shift by X -> 0; returns `Constant::getNullValue(Op0->getType())`. Guard: `match(Op0, m_Zero())`.
- **Matched/replaced opcodes:** `shl`, `lshr`, `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — shared shift schema for the named opcode family; preserve poison shift-amount and exactness/nowrap semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS1314.lean](../../Veir/InstSimplify/IS1314.lean).
- **Theorems:** `Veir.InstSimplify.IS1314.pattern_shl_left_valid`, `Veir.InstSimplify.IS1314.pattern_lshr_left_valid`, `Veir.InstSimplify.IS1314.pattern_ashr_left_valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is1322"></a>

## IS1322 — `simplifyShift`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1321–1322](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1321-L1322). Kind: schema.
- **Rewrite:** X shift by 0 -> X Shift-by-sign-extended bool must be shift-by-0 because shift-by-all-ones would be poison.; returns `Op0`. Guard: `match(Op1, m_Zero()) || (match(Op1, m_SExt(m_Value(X))) && X->getType()->isIntOrIntVectorTy(1))`.
- **Matched/replaced opcodes:** `shl`, `lshr`, `ashr`, `sext`.
- **Beyond opcode/constant/SSA matching:** Yes — type required: integer scalar/vector with the stated bit width; shared shift schema for the named opcode family; preserve poison shift-amount and exactness/nowrap semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Arbitrary scalar integer widths and signedness attributes; every source no-wrap/exact requirement preserved, all other flags arbitrary, poison refinement included.
- **Lean:** [Veir/InstSimplify/IS1322.lean](../../Veir/InstSimplify/IS1322.lean).
- **Theorems:** `Veir.InstSimplify.IS1322.pattern_shl_right_valid`, `Veir.InstSimplify.IS1322.pattern_lshr_right_valid`, `Veir.InstSimplify.IS1322.pattern_ashr_right_valid`, `Veir.InstSimplify.IS1322.pattern_sext_shl_valid`, `Veir.InstSimplify.IS1322.pattern_sext_lshr_valid`, `Veir.InstSimplify.IS1322.pattern_sext_ashr_valid`.
- **Details / missing facilities:** Both literal-zero and sign-extended i1 shift-count branches proved for shl/lshr/ashr, arbitrary target width satisfying the modeled sext width constraint.

<a id="is1326"></a>

## IS1326 — `simplifyShift`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1325–1326](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1325-L1326). Kind: schema.
- **Rewrite:** `shl`, `lshr`, or `ashr` by a constant count at least the integer bitwidth folds to poison. `isPoisonShift` also recognizes vector splats and fixed vectors whose lanes all have poison shifts. Its undef alternative is IS1326u.
- **Matched/replaced opcodes:** `shl`, `lshr`, `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — shared shift schema for the named opcode family; preserve poison shift-amount and exactness/nowrap semantics; LLVM poison propagation semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All three scalar shift opcodes, arbitrary constant count n:Int and all widths, under metadata guard width≤count.toNat. LLVM undef/vector shift-count alternatives unsupported.
- **Lean:** [Veir/InstSimplify/IS1326.lean](../../Veir/InstSimplify/IS1326.lean).
- **Theorems:** `Veir.InstSimplify.IS1326.pattern_shl_valid`, `Veir.InstSimplify.IS1326.pattern_lshr_valid`, `Veir.InstSimplify.IS1326.pattern_ashr_valid`.
- **Details / missing facilities:** All scalar constant overshift branches compiled. Separate IS1326u records unsupported undef shift amounts; vector-lane variants lack interpreter types/semantics.

<a id="is1326u"></a>

## IS1326u — `simplifyShift`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1325–1326](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1325-L1326). Kind: rewrite.
- **Rewrite:** `shl X,undef`, `lshr X,undef`, and `ashr X,undef` fold to poison because undef can choose an out-of-range count; prior zero-source and constant-folding branches take precedence.
- **Matched/replaced opcodes:** `shl`, `lshr`, `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — shared shift schema for the named opcode family; preserve poison shift-amount and exactness/nowrap semantics; LLVM poison propagation semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Details / missing facilities:** LLVM undef is not represented by LLVM.Int and mlir__undef has no successful interpretation in Llvm.interpretOp'. Poison is a distinct value and cannot substitute for undef. No vacuous Pattern.Valid proof from the missing interpreter case is claimed.

<a id="is1332"></a>

## IS1332 — `simplifyShift`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1330–1332](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1330-L1332). Kind: schema.
- **Rewrite:** If the operation is with the result of a select instruction, check whether operating on either branch of the select always yields the same value.; returns `V`. Guard: `isa<SelectInst>(Op0) || isa<SelectInst>(Op1)` and `Value *V = threadBinOpOverSelect(Opcode, Op0, Op1, Q, MaxRecurse)`.
- **Matched/replaced opcodes:** `shl`, `lshr`, `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — shared shift schema for the named opcode family; preserve poison shift-amount and exactness/nowrap semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Generic recursive threadBinOpOverSelect schema requires semantic certificates for both recursively simplified arms and their recursion budget; Puddle has no engine/composition contract for this schema.

<a id="is1338"></a>

## IS1338 — `simplifyShift`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1336–1338](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1336-L1338). Kind: schema.
- **Rewrite:** If the operation is with the result of a phi instruction, check whether operating on all incoming values of the phi always yields the same value.; returns `V`. Guard: `isa<PHINode>(Op0) || isa<PHINode>(Op1)` and `Value *V = threadBinOpOverPHI(Opcode, Op0, Op1, Q, MaxRecurse)`.
- **Matched/replaced opcodes:** `shl`, `lshr`, `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — shared shift schema for the named opcode family; preserve poison shift-amount and exactness/nowrap semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** LLVM PHI opcode/incoming-edge semantics and dominating-edge ValueTracking facts are not represented by Puddle Models.

<a id="is1344"></a>

## IS1344 — `simplifyShift`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1343–1344](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1343-L1344). Kind: schema.
- **Rewrite:** If any bits in the shift amount make that value greater than or equal to the number of bits in the type, the shift is undefined.; returns `PoisonValue::get(Op0->getType())`. Guard: `KnownAmt.getMinValue().uge(KnownAmt.getBitWidth())`.
- **Matched/replaced opcodes:** `shl`, `lshr`, `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-bits/sign-bit/range facts computed from operands; shared shift schema for the named opcode family; preserve poison shift-amount and exactness/nowrap semantics; LLVM poison propagation semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** KnownBits proves the minimum shift amount is at least the bit width, so the operation returns poison. Scalar poison is modeled, but the KnownBits fact has no semantic certificate in Puddle Models. This branch does not involve an LLVM undef value.

<a id="is1350"></a>

## IS1350 — `simplifyShift`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1349–1350](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1349-L1350). Kind: schema.
- **Rewrite:** If all valid bits in the shift amount are known zero, the first operand is unchanged.; returns `Op0`. Guard: `KnownAmt.countMinTrailingZeros() >= NumValidShiftBits`.
- **Matched/replaced opcodes:** `shl`, `lshr`, `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-bits/sign-bit/range facts computed from operands; shared shift schema for the named opcode family; preserve poison shift-amount and exactness/nowrap semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** computeKnownBits minimum trailing-zero analysis has no semantic bridge into Models.

<a id="is1364"></a>

## IS1364 — `simplifyShift`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1362–1364](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1362-L1364). Kind: schema.
- **Rewrite:** Check for nsw shl leading to a poison value.; returns `PoisonValue::get(Op0->getType())`. Guard: `IsNSW` and `KnownShl.hasConflict()`.
- **Matched/replaced opcodes:** `shl`, `lshr`, `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-bits/sign-bit/range facts computed from operands; instruction property required: nsw flag; shared shift schema for the named opcode family; preserve poison shift-amount and exactness/nowrap semantics; LLVM poison propagation semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** KnownBits::shl conflict analysis has no semantic bridge into Models.

<a id="is1377"></a>

## IS1377 — `simplifyRightShift`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1376–1377](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1376-L1377). Kind: schema.
- **Rewrite:** Given operands for an LShr or AShr, see if we can fold the result.  If not, this returns null.; returns `V`. Guard: `Value *V = simplifyShift(Opcode, Op0, Op1, /*IsNSW*/ false, Q, MaxRecurse)`.
- **Matched/replaced opcodes:** `lshr`, `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: nsw flag; shared shift schema for the named opcode family; preserve poison shift-amount and exactness/nowrap semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Simple internal forwarding to already inventoried helper cases; this return adds no distinct rewrite equation.

<a id="is1381"></a>

## IS1381 — `simplifyRightShift`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1380–1381](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1380-L1381). Kind: schema.
- **Rewrite:** X >> X -> 0; returns `Constant::getNullValue(Op0->getType())`. Guard: `Op0 == Op1`.
- **Matched/replaced opcodes:** `lshr`, `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — shared shift schema for the named opcode family; preserve poison shift-amount and exactness/nowrap semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS1381.lean](../../Veir/InstSimplify/IS1381.lean).
- **Theorems:** `Veir.InstSimplify.IS1381.pattern_lshr_valid`, `Veir.InstSimplify.IS1381.pattern_ashr_valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is1386"></a>

## IS1386 — `simplifyRightShift`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1385–1386](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1385-L1386). Kind: schema.
- **Rewrite:** undef >> X -> 0 undef >> X -> undef (if it's exact); returns `IsExact ? Op0 : Constant::getNullValue(Op0->getType())`. Guard: `Q.isUndefValue(Op0)`.
- **Matched/replaced opcodes:** `lshr`, `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM undef nondeterministic semantics; shared shift schema for the named opcode family; preserve poison shift-amount and exactness/nowrap semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** LLVM undef has no interpretOp' semantics: .mlir__undef falls through to failure. This branch cannot be proved by a vacuous successful-interpretation assumption.

<a id="is1393"></a>

## IS1393 — `simplifyRightShift`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1391–1393](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1391-L1393). Kind: schema.
- **Rewrite:** The low bit cannot be shifted out of an exact shift if it is set. TODO: Generalize by counting trailing zeros (see fold for exact division).; returns `Op0`. Guard: `IsExact` and `Op0Known.One[0]`.
- **Matched/replaced opcodes:** `lshr`, `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-bits/sign-bit/range facts computed from operands; instruction property required: exact flag; shared shift schema for the named opcode family; preserve poison shift-amount and exactness/nowrap semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** computeKnownBits low-bit-one analysis has no semantic bridge into Models.

<a id="is1405"></a>

## IS1405 — `simplifyShlInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1404–1405](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1404-L1405). Kind: delegation.
- **Rewrite:** Given operands for an Shl, see if we can fold the result. If not, this returns null.; returns `V`. Guard: `Value *V = simplifyShift(Instruction::Shl, Op0, Op1, IsNSW, Q, MaxRecurse)`. Delegates to `simplifyShift`.
- **Matched/replaced opcodes:** `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: nsw flag; recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Simple internal forwarding to already inventoried helper cases; this return adds no distinct rewrite equation.

<a id="is1411"></a>

## IS1411 — `simplifyShlInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1410–1411](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1410-L1411). Kind: rewrite.
- **Rewrite:** undef << X -> 0 undef << X -> undef if (if it's NSW/NUW); returns `IsNSW || IsNUW ? Op0 : Constant::getNullValue(Ty)`. Guard: `Q.isUndefValue(Op0)`.
- **Matched/replaced opcodes:** `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM undef nondeterministic semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** LLVM undef has no interpretOp' semantics: .mlir__undef falls through to failure. This branch cannot be proved by a vacuous successful-interpretation assumption.

<a id="is1417"></a>

## IS1417 — `simplifyShlInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1416–1417](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1416-L1417). Kind: rewrite.
- **Rewrite:** (X >> A) << A -> X; returns `X`. Guard: `Q.IIQ.UseInstrInfo && match(Op0, m_Exact(m_Shr(m_Value(X), m_Specific(Op1))))`.
- **Matched/replaced opcodes:** `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: exact operator flag; instruction property required: InstrInfoQuery operator flags; instruction property required: operator flags via InstrInfoQuery.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS1417.lean](../../Veir/InstSimplify/IS1417.lean).
- **Theorems:** `Veir.InstSimplify.IS1417.pattern_lshr_valid`, `Veir.InstSimplify.IS1417.pattern_ashr_valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is1421"></a>

## IS1421 — `simplifyShlInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1420–1421](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1420-L1421). Kind: rewrite.
- **Rewrite:** shl nuw i8 C, %x  ->  C  iff C has sign bit set.; returns `Op0`. Guard: `IsNUW && match(Op0, m_Negative())`.
- **Matched/replaced opcodes:** `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: nuw flag.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Arbitrary scalar integer widths and signedness attributes; every source no-wrap/exact requirement preserved, all other flags arbitrary, poison refinement included.
- **Lean:** [Veir/InstSimplify/IS1421.lean](../../Veir/InstSimplify/IS1421.lean).
- **Theorems:** `Veir.InstSimplify.IS1421.valid`.
- **Details / missing facilities:** Checked by Lean; APInt-bit matching admits all equivalent signed/unsigned/i1 integer attribute spellings.

<a id="is1430"></a>

## IS1430 — `simplifyShlInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1429–1430](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1429-L1430). Kind: rewrite.
- **Rewrite:** "nuw" guarantees that only zeros are shifted out, and "nsw" guarantees that the sign-bit does not change, so the only input that does not produce poison is 0, and "0 << (bitwidth-1) --> 0".; returns `Constant::getNullValue(Ty)`. Guard: `IsNSW && IsNUW && match(Op1, m_SpecificInt(Ty->getScalarSizeInBits() - 1))`.
- **Matched/replaced opcodes:** `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: nsw flag; instruction property required: nuw flag.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Arbitrary scalar integer widths and signedness attributes; every source no-wrap/exact requirement preserved, all other flags arbitrary, poison refinement included.
- **Lean:** [Veir/InstSimplify/IS1430.lean](../../Veir/InstSimplify/IS1430.lean).
- **Theorems:** `Veir.InstSimplify.IS1430.valid`.
- **Details / missing facilities:** Both flags preserved, amount=width-1. Requires width>1 because the source earlier shift-by-zero case returns the operand at width1, so this branch is unreachable there.

<a id="is1446"></a>

## IS1446 — `simplifyLShrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1445–1446](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1445-L1446). Kind: delegation.
- **Rewrite:** Given operands for an LShr, see if we can fold the result. If not, this returns null.; returns `V`. Guard: `Value *V = simplifyRightShift(Instruction::LShr, Op0, Op1, IsExact, Q, MaxRecurse)`. Delegates to `simplifyRightShift`.
- **Matched/replaced opcodes:** `lshr`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: exact flag; recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Simple internal forwarding to already inventoried helper cases; this return adds no distinct rewrite equation.

<a id="is1451"></a>

## IS1451 — `simplifyLShrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1450–1451](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1450-L1451). Kind: rewrite.
- **Rewrite:** (X << A) >> A -> X; returns `X`. Guard: `Q.IIQ.UseInstrInfo && match(Op0, m_NUWShl(m_Value(X), m_Specific(Op1)))`.
- **Matched/replaced opcodes:** `lshr`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: no-unsigned-wrap operator flag; instruction property required: InstrInfoQuery operator flags; instruction property required: operator flags via InstrInfoQuery.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS1451.lean](../../Veir/InstSimplify/IS1451.lean).
- **Theorems:** `Veir.InstSimplify.IS1451.valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is1466"></a>

## IS1466 — `simplifyLShrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1464–1466](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1464-L1466). Kind: rewrite.
- **Rewrite:** ((X << A) | Y) >> A -> X  if effective width of Y is not larger than A. We can return X as we do in the above case since OR alters no bits in X. SimplifyDemandedBits in InstCombine can do more general optimization for bit manipulation. This pattern aims to provide opportunities for other optimizers by supporting a simple but common case in InstSimplify.; returns `X`. Guard: `Q.IIQ.UseInstrInfo && match(Op1, m_APInt(ShRAmt)) && match(Op0, m_c_Or(m_NUWShl(m_Value(X), m_APInt(ShLAmt)), m_Value(Y))) && *ShRAmt == *ShLAmt` and `ShRAmt->uge(EffWidthY)`.
- **Matched/replaced opcodes:** `lshr`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-bits/sign-bit/range facts computed from operands; instruction property required: no-unsigned-wrap operator flag; instruction property required: InstrInfoQuery operator flags; instruction property required: operator flags via InstrInfoQuery.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Requires computeKnownBits maximum-active-bits analysis of Y; no semantic bridge into Models.

<a id="is1483"></a>

## IS1483 — `simplifyAShrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1482–1483](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1482-L1483). Kind: delegation.
- **Rewrite:** Given operands for an AShr, see if we can fold the result. If not, this returns null.; returns `V`. Guard: `Value *V = simplifyRightShift(Instruction::AShr, Op0, Op1, IsExact, Q, MaxRecurse)`. Delegates to `simplifyRightShift`.
- **Matched/replaced opcodes:** `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: exact flag; recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** Simple internal forwarding to already inventoried helper cases; this return adds no distinct rewrite equation.

<a id="is1490"></a>

## IS1490 — `simplifyAShrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1489–1490](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1489-L1490). Kind: rewrite.
- **Rewrite:** -1 >>a X --> -1 (-1 << X) a>> X --> -1 We could return the original -1 constant to preserve poison elements.; returns `Constant::getAllOnesValue(Op0->getType())`. Guard: `match(Op0, m_AllOnes()) || match(Op0, m_Shl(m_AllOnes(), m_Specific(Op1)))`.
- **Matched/replaced opcodes:** `ashr`, `shl`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS1490.lean](../../Veir/InstSimplify/IS1490.lean).
- **Theorems:** `Veir.InstSimplify.IS1490.pattern_valid`, `Veir.InstSimplify.IS1490.pattern_nested_valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is1495"></a>

## IS1495 — `simplifyAShrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1494–1495](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1494-L1495). Kind: rewrite.
- **Rewrite:** (X << A) >> A -> X; returns `X`. Guard: `Q.IIQ.UseInstrInfo && match(Op0, m_NSWShl(m_Value(X), m_Specific(Op1)))`.
- **Matched/replaced opcodes:** `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: no-signed-wrap operator flag; instruction property required: InstrInfoQuery operator flags; instruction property required: operator flags via InstrInfoQuery.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All scalar integer widths, all signedness attributes, all source flags except those explicitly required by the source rule. Poison included; vector/FP types absent from this interpreter.
- **Lean:** [Veir/InstSimplify/IS1495.lean](../../Veir/InstSimplify/IS1495.lean).
- **Theorems:** `Veir.InstSimplify.IS1495.valid`.
- **Details / missing facilities:** Lean compilation successful. Constant matching compares APInt bits and admits signed/unsigned/i1 metadata spellings.

<a id="is1500"></a>

## IS1500 — `simplifyAShrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1499–1500](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1499-L1500). Kind: rewrite.
- **Rewrite:** Arithmetic shifting an all-sign-bit value is a no-op.; returns `Op0`. Guard: `NumSignBits == Op0->getType()->getScalarSizeInBits()`.
- **Matched/replaced opcodes:** `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-bits/sign-bit/range facts computed from operands.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer operations; vector/FP variants excluded by absent interpreter semantics.
- **Details / missing facilities:** ComputeNumSignBits analysis has no semantic bridge into Models.

<a id="is1534"></a>

## IS1534 — `simplifyUnsignedRangeCheck`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1531–1534](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1531-L1534). Kind: rewrite.
- **Rewrite:** A >=/<= B || (A - B) != 0  <-->  true; returns `ConstantInt::getTrue(UnsignedICmp->getType())`. Guard: `match(Y, m_Sub(m_Value(A), m_Value(B)))` and `match(UnsignedICmp, m_c_ICmp(UnsignedPred, m_Specific(A), m_Specific(B))) && ICmpInst::isUnsigned(UnsignedPred)` and `(UnsignedPred == ICmpInst::ICMP_UGE || UnsignedPred == ICmpInst::ICMP_ULE) && EqPred == ICmpInst::ICMP_NE && !IsAnd`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`, `sub`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary source/destination widths and signedness, all source flags and operand orientations; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS1534.lean](../../Veir/InstSimplify/IS1534.lean).
- **Theorems:** `Veir.InstSimplify.IS1534.valid_or`.
- **Details / missing facilities:** Complete scalar source family compiled with poison refinement and kernel proofs; Boolean cases use the kernel int1_cases theorem.

<a id="is1539"></a>

## IS1539 — `simplifyUnsignedRangeCheck`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1536–1539](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1536-L1539). Kind: rewrite.
- **Rewrite:** A </> B && (A - B) == 0  <-->  false; returns `ConstantInt::getFalse(UnsignedICmp->getType())`. Guard: `match(Y, m_Sub(m_Value(A), m_Value(B)))` and `match(UnsignedICmp, m_c_ICmp(UnsignedPred, m_Specific(A), m_Specific(B))) && ICmpInst::isUnsigned(UnsignedPred)` and `(UnsignedPred == ICmpInst::ICMP_ULT || UnsignedPred == ICmpInst::ICMP_UGT) && EqPred == ICmpInst::ICMP_EQ && IsAnd`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`, `sub`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and signedness; all source flags, normalized APInt constant spellings, and source operand orientations. Vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS1539.lean](../../Veir/InstSimplify/IS1539.lean).
- **Theorems:** `Veir.InstSimplify.IS1539.valid_and`.
- **Details / missing facilities:** Complete scalar source family compiled with kernel proofs and LLVM poison refinement; native guards implement the exact source conditions.

<a id="is1545"></a>

## IS1545 — `simplifyUnsignedRangeCheck`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1542–1545](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1542-L1545). Kind: rewrite.
- **Rewrite:** A </> B && (A - B) != 0  <-->  A </> B A </> B || (A - B) != 0  <-->  (A - B) != 0; returns `IsAnd ? UnsignedICmp : ZeroICmp`. Guard: `match(Y, m_Sub(m_Value(A), m_Value(B)))` and `match(UnsignedICmp, m_c_ICmp(UnsignedPred, m_Specific(A), m_Specific(B))) && ICmpInst::isUnsigned(UnsignedPred)` and `EqPred == ICmpInst::ICMP_NE && (UnsignedPred == ICmpInst::ICMP_ULT || UnsignedPred == ICmpInst::ICMP_UGT)`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`, `sub`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and signedness; all source flags, normalized APInt constant spellings, and source operand orientations. Vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS1545.lean](../../Veir/InstSimplify/IS1545.lean).
- **Theorems:** `Veir.InstSimplify.IS1545.valid_and`, `Veir.InstSimplify.IS1545.valid_or`.
- **Details / missing facilities:** Complete scalar source family compiled with kernel proofs and LLVM poison refinement; native guards implement the exact source conditions.

<a id="is1551"></a>

## IS1551 — `simplifyUnsignedRangeCheck`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1548–1551](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1548-L1551). Kind: rewrite.
- **Rewrite:** A <=/>= B && (A - B) == 0  <-->  (A - B) == 0 A <=/>= B || (A - B) == 0  <-->  A <=/>= B; returns `IsAnd ? ZeroICmp : UnsignedICmp`. Guard: `match(Y, m_Sub(m_Value(A), m_Value(B)))` and `match(UnsignedICmp, m_c_ICmp(UnsignedPred, m_Specific(A), m_Specific(B))) && ICmpInst::isUnsigned(UnsignedPred)` and `EqPred == ICmpInst::ICMP_EQ && (UnsignedPred == ICmpInst::ICMP_ULE || UnsignedPred == ICmpInst::ICMP_UGE)`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`, `sub`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and signedness; all source flags, normalized APInt constant spellings, and source operand orientations. Vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS1551.lean](../../Veir/InstSimplify/IS1551.lean).
- **Theorems:** `Veir.InstSimplify.IS1551.valid_and`, `Veir.InstSimplify.IS1551.valid_or`.
- **Details / missing facilities:** Complete scalar source family compiled with kernel proofs and LLVM poison refinement; native guards implement the exact source conditions.

<a id="is1561"></a>

## IS1561 — `simplifyUnsignedRangeCheck`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1558–1561](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1558-L1561). Kind: rewrite.
- **Rewrite:** Given  Y = (A - B) Y >= A && Y != 0  --> Y >= A  iff B != 0 Y <  A || Y == 0  --> Y <  A  iff B != 0; returns `UnsignedICmp`. Guard: `match(Y, m_Sub(m_Value(A), m_Value(B)))` and `match(UnsignedICmp, m_c_ICmp(UnsignedPred, m_Specific(Y), m_Specific(A)))` and `UnsignedPred == ICmpInst::ICMP_UGE && IsAnd && EqPred == ICmpInst::ICMP_NE && isKnownNonZero(B, Q)`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`, `sub`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-nonzero value-tracking proof; analysis required: source value-tracking proves the matched operand nonzero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is1564"></a>

## IS1564 — `simplifyUnsignedRangeCheck`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1561–1564](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1561-L1564). Kind: rewrite.
- **Rewrite:** Given  Y = (A - B) Y >= A && Y != 0  --> Y >= A  iff B != 0 Y <  A || Y == 0  --> Y <  A  iff B != 0; returns `UnsignedICmp`. Guard: `match(Y, m_Sub(m_Value(A), m_Value(B)))` and `match(UnsignedICmp, m_c_ICmp(UnsignedPred, m_Specific(Y), m_Specific(A)))` and `UnsignedPred == ICmpInst::ICMP_ULT && !IsAnd && EqPred == ICmpInst::ICMP_EQ && isKnownNonZero(B, Q)`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`, `sub`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-nonzero value-tracking proof; analysis required: source value-tracking proves the matched operand nonzero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is1582"></a>

## IS1582 — `simplifyUnsignedRangeCheck`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1581–1582](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1581-L1582). Kind: rewrite.
- **Rewrite:** X > Y && Y == 0  -->  Y == 0  iff X != 0 X > Y || Y == 0  -->  X > Y   iff X != 0; returns `IsAnd ? ZeroICmp : UnsignedICmp`. Guard: `UnsignedPred == ICmpInst::ICMP_UGT && EqPred == ICmpInst::ICMP_EQ && isKnownNonZero(X, Q)`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-nonzero value-tracking proof; analysis required: source value-tracking proves the matched operand nonzero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is1588"></a>

## IS1588 — `simplifyUnsignedRangeCheck`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1587–1588](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1587-L1588). Kind: rewrite.
- **Rewrite:** X <= Y && Y != 0  -->  X <= Y  iff X != 0 X <= Y || Y != 0  -->  Y != 0  iff X != 0; returns `IsAnd ? UnsignedICmp : ZeroICmp`. Guard: `UnsignedPred == ICmpInst::ICMP_ULE && EqPred == ICmpInst::ICMP_NE && isKnownNonZero(X, Q)`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-nonzero value-tracking proof; analysis required: source value-tracking proves the matched operand nonzero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is1598"></a>

## IS1598 — `simplifyUnsignedRangeCheck`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1597–1598](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1597-L1598). Kind: rewrite.
- **Rewrite:** X < Y && Y != 0  -->  X < Y X < Y || Y != 0  -->  Y != 0; returns `IsAnd ? UnsignedICmp : ZeroICmp`. Guard: `UnsignedPred == ICmpInst::ICMP_ULT && EqPred == ICmpInst::ICMP_NE`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary source/destination widths and signedness, all source flags and operand orientations; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS1598.lean](../../Veir/InstSimplify/IS1598.lean).
- **Theorems:** `Veir.InstSimplify.IS1598.valid_and`, `Veir.InstSimplify.IS1598.valid_or`.
- **Details / missing facilities:** Complete scalar source family compiled with poison refinement and kernel proofs; Boolean cases use the kernel int1_cases theorem.

<a id="is1603"></a>

## IS1603 — `simplifyUnsignedRangeCheck`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1602–1603](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1602-L1603). Kind: rewrite.
- **Rewrite:** X >= Y && Y == 0  -->  Y == 0 X >= Y || Y == 0  -->  X >= Y; returns `IsAnd ? ZeroICmp : UnsignedICmp`. Guard: `UnsignedPred == ICmpInst::ICMP_UGE && EqPred == ICmpInst::ICMP_EQ`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary source/destination widths and signedness, all source flags and operand orientations; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS1603.lean](../../Veir/InstSimplify/IS1603.lean).
- **Theorems:** `Veir.InstSimplify.IS1603.valid_and`, `Veir.InstSimplify.IS1603.valid_or`.
- **Details / missing facilities:** Complete scalar source family compiled with poison refinement and kernel proofs; Boolean cases use the kernel int1_cases theorem.

<a id="is1608"></a>

## IS1608 — `simplifyUnsignedRangeCheck`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1607–1608](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1607-L1608). Kind: rewrite.
- **Rewrite:** X < Y && Y == 0  -->  false; returns `getFalse(UnsignedICmp->getType())`. Guard: `UnsignedPred == ICmpInst::ICMP_ULT && EqPred == ICmpInst::ICMP_EQ && IsAnd`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary source/destination widths and signedness, all source flags and operand orientations; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS1608.lean](../../Veir/InstSimplify/IS1608.lean).
- **Theorems:** `Veir.InstSimplify.IS1608.valid_and`.
- **Details / missing facilities:** Complete scalar source family compiled with poison refinement and kernel proofs; Boolean cases use the kernel int1_cases theorem.

<a id="is1613"></a>

## IS1613 — `simplifyUnsignedRangeCheck`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1612–1613](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1612-L1613). Kind: rewrite.
- **Rewrite:** X >= Y || Y != 0  -->  true; returns `getTrue(UnsignedICmp->getType())`. Guard: `UnsignedPred == ICmpInst::ICMP_UGE && EqPred == ICmpInst::ICMP_NE && !IsAnd`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary source/destination widths and signedness, all source flags and operand orientations; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS1613.lean](../../Veir/InstSimplify/IS1613.lean).
- **Theorems:** `Veir.InstSimplify.IS1613.valid_or`.
- **Details / missing facilities:** Complete scalar source family compiled with poison refinement and kernel proofs; Boolean cases use the kernel int1_cases theorem.

<a id="is1638"></a>

## IS1638 — `simplifyAndOrOfICmpsWithConstants`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1637–1638](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1637-L1638). Kind: rewrite.
- **Rewrite:** For and-of-compares, check if the intersection is empty: (icmp X, C0) && (icmp X, C1) --> empty set --> false; returns `getFalse(Cmp0->getType())`. Guard: `IsAnd && Range0.intersectWith(Range1).isEmptySet()`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: integer or floating-point range-set analysis.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM comparison sets of arbitrary width/predicates/constants; source set guard represented extensionally. Both root orders are covered by independently quantified predicate/constant pairs; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS1638.lean](../../Veir/InstSimplify/IS1638.lean).
- **Theorems:** `Veir.InstSimplify.IS1638.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags. ConstantRange integer regions represented extensionally as comparison sets; metadata guard exhaustively checks 2^w values (exponential runtime cost).

<a id="is1643"></a>

## IS1643 — `simplifyAndOrOfICmpsWithConstants`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1642–1643](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1642-L1643). Kind: rewrite.
- **Rewrite:** For or-of-compares, check if the union is full: (icmp X, C0) || (icmp X, C1) --> full set --> true; returns `getTrue(Cmp0->getType())`. Guard: `!IsAnd && Range0.unionWith(Range1).isFullSet()`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: integer or floating-point range-set analysis.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM comparison sets of arbitrary width/predicates/constants; source set guard represented extensionally. Both root orders are covered by independently quantified predicate/constant pairs; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS1643.lean](../../Veir/InstSimplify/IS1643.lean).
- **Theorems:** `Veir.InstSimplify.IS1643.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags. ConstantRange integer regions represented extensionally as comparison sets; metadata guard exhaustively checks 2^w values (exponential runtime cost).

<a id="is1651"></a>

## IS1651 — `simplifyAndOrOfICmpsWithConstants`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1650–1651](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1650-L1651). Kind: rewrite.
- **Rewrite:** Is one range a superset of the other? If this is and-of-compares, take the smaller set: (icmp sgt X, 4) && (icmp sgt X, 42) --> icmp sgt X, 42 If this is or-of-compares, take the larger set: (icmp sgt X, 4) || (icmp sgt X, 42) --> icmp sgt X, 4; returns `IsAnd ? Cmp1 : Cmp0`. Guard: `Range0.contains(Range1)`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: integer or floating-point range-set analysis.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM comparison sets of arbitrary width/predicates/constants; source set guard represented extensionally. Both root orders are covered by independently quantified predicate/constant pairs; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS1651.lean](../../Veir/InstSimplify/IS1651.lean).
- **Theorems:** `Veir.InstSimplify.IS1651.valid_and`, `Veir.InstSimplify.IS1651.valid_or`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags. ConstantRange integer regions represented extensionally as comparison sets; metadata guard exhaustively checks 2^w values (exponential runtime cost).

<a id="is1653"></a>

## IS1653 — `simplifyAndOrOfICmpsWithConstants`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1652–1653](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1652-L1653). Kind: rewrite.
- **Rewrite:** Is one range a superset of the other? If this is and-of-compares, take the smaller set: (icmp sgt X, 4) && (icmp sgt X, 42) --> icmp sgt X, 42 If this is or-of-compares, take the larger set: (icmp sgt X, 4) || (icmp sgt X, 42) --> icmp sgt X, 4; returns `IsAnd ? Cmp0 : Cmp1`. Guard: `Range1.contains(Range0)`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: integer or floating-point range-set analysis.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM comparison sets of arbitrary width/predicates/constants; source set guard represented extensionally. Both root orders are covered by independently quantified predicate/constant pairs; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS1653.lean](../../Veir/InstSimplify/IS1653.lean).
- **Theorems:** `Veir.InstSimplify.IS1653.valid_and`, `Veir.InstSimplify.IS1653.valid_or`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags. ConstantRange integer regions represented extensionally as comparison sets; metadata guard exhaustively checks 2^w values (exponential runtime cost).

<a id="is1682"></a>

## IS1682 — `simplifyAndOfICmpsWithAdd`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1679–1682](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1679-L1682). Kind: rewrite.
- **Rewrite:** (icmp ult (add V,C0),C1) AND (icmp sgt V,C0) -> false; C1-C0=2 in APInt modular arithmetic; C0 signed-positive.
- **Matched/replaced opcodes:** `and`, `icmp`, `add`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and signedness; all source flags, normalized APInt constant spellings, and source operand orientations. Vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS1682.lean](../../Veir/InstSimplify/IS1682.lean).
- **Theorems:** `Veir.InstSimplify.IS1682.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with kernel proofs and LLVM poison refinement; native guards implement the exact source conditions.

<a id="is1684"></a>

## IS1684 — `simplifyAndOfICmpsWithAdd`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1681–1684](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1681-L1684). Kind: rewrite.
- **Rewrite:** (icmp slt (add V,C0),C1) AND (icmp sgt V,C0) -> false; C1-C0=2 in APInt modular arithmetic; C0 signed-positive and add nsw.
- **Matched/replaced opcodes:** `and`, `icmp`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: nsw flag.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and signedness; all source flags, normalized APInt constant spellings, and source operand orientations. Vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS1684.lean](../../Veir/InstSimplify/IS1684.lean).
- **Theorems:** `Veir.InstSimplify.IS1684.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with kernel proofs and LLVM poison refinement; native guards implement the exact source conditions.

<a id="is1688"></a>

## IS1688 — `simplifyAndOfICmpsWithAdd`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1685–1688](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1685-L1688). Kind: rewrite.
- **Rewrite:** (icmp ule (add V,C0),C1) AND (icmp sgt V,C0) -> false; C1-C0=1 in APInt modular arithmetic; C0 signed-positive.
- **Matched/replaced opcodes:** `and`, `icmp`, `add`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and signedness; all source flags, normalized APInt constant spellings, and source operand orientations. Vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS1688.lean](../../Veir/InstSimplify/IS1688.lean).
- **Theorems:** `Veir.InstSimplify.IS1688.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with kernel proofs and LLVM poison refinement; native guards implement the exact source conditions.

<a id="is1690"></a>

## IS1690 — `simplifyAndOfICmpsWithAdd`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1687–1690](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1687-L1690). Kind: rewrite.
- **Rewrite:** (icmp sle (add V,C0),C1) AND (icmp sgt V,C0) -> false; C1-C0=1 in APInt modular arithmetic; C0 signed-positive and add nsw.
- **Matched/replaced opcodes:** `and`, `icmp`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: nsw flag.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and signedness; all source flags, normalized APInt constant spellings, and source operand orientations. Vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS1690.lean](../../Veir/InstSimplify/IS1690.lean).
- **Theorems:** `Veir.InstSimplify.IS1690.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with kernel proofs and LLVM poison refinement; native guards implement the exact source conditions.

<a id="is1696"></a>

## IS1696 — `simplifyAndOfICmpsWithAdd`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1693–1696](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1693-L1696). Kind: rewrite.
- **Rewrite:** (icmp ult (add V,C0),C1) AND (icmp ugt V,C0) -> false; C1-C0=2 in APInt modular arithmetic; C0 nonzero and add nuw.
- **Matched/replaced opcodes:** `and`, `icmp`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: nuw flag.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and signedness; all source flags, normalized APInt constant spellings, and source operand orientations. Vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS1696.lean](../../Veir/InstSimplify/IS1696.lean).
- **Theorems:** `Veir.InstSimplify.IS1696.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with kernel proofs and LLVM poison refinement; native guards implement the exact source conditions.

<a id="is1699"></a>

## IS1699 — `simplifyAndOfICmpsWithAdd`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1696–1699](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1696-L1699). Kind: rewrite.
- **Rewrite:** (icmp ule (add V,C0),C1) AND (icmp ugt V,C0) -> false; C1-C0=1 in APInt modular arithmetic; C0 nonzero and add nuw.
- **Matched/replaced opcodes:** `and`, `icmp`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: nuw flag.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and signedness; all source flags, normalized APInt constant spellings, and source operand orientations. Vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS1699.lean](../../Veir/InstSimplify/IS1699.lean).
- **Theorems:** `Veir.InstSimplify.IS1699.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with kernel proofs and LLVM poison refinement; native guards implement the exact source conditions.

<a id="is1717"></a>

## IS1717 — `simplifyAndOrOfICmpsWithCtpop`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1716–1717](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1716-L1717). Kind: rewrite.
- **Rewrite:** Absorb ctpop(X) comparison against any nonzero APInt C with the indicated X-zero comparison; C may have a negative signed interpretation.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`, `ctpop`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths, all three operand-order commutations (both equality comparisons and outer and/or); all disjoint flags; every normalized nonzero APInt C.
- **Lean:** [Veir/InstSimplify/IS1717.lean](../../Veir/InstSimplify/IS1717.lean).
- **Theorems:** `Veir.InstSimplify.IS1717_valid`.
- **Details / missing facilities:** Pinned source checks C->isZero(), not signed positivity; own LLVM ctpop/icmp/and-or patterns with exact retained comparison result and kernel-checked validity.

<a id="is1720"></a>

## IS1720 — `simplifyAndOrOfICmpsWithCtpop`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1719–1720](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1719-L1720). Kind: rewrite.
- **Rewrite:** Absorb ctpop(X) comparison against any nonzero APInt C with the indicated X-zero comparison; C may have a negative signed interpretation.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`, `ctpop`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths, all three operand-order commutations (both equality comparisons and outer and/or); all disjoint flags; every normalized nonzero APInt C.
- **Lean:** [Veir/InstSimplify/IS1720.lean](../../Veir/InstSimplify/IS1720.lean).
- **Theorems:** `Veir.InstSimplify.IS1720_valid`.
- **Details / missing facilities:** Pinned source checks C->isZero(), not signed positivity; own LLVM ctpop/icmp/and-or patterns with exact retained comparison result and kernel-checked validity.

<a id="is1728"></a>

## IS1728 — `simplifyAndOfICmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1727–1728](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1727-L1728). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyUnsignedRangeCheck for the enclosing and operation.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS1534.lean](../../Veir/InstSimplify/IS1534.lean), [Veir/InstSimplify/IS1539.lean](../../Veir/InstSimplify/IS1539.lean), [Veir/InstSimplify/IS1545.lean](../../Veir/InstSimplify/IS1545.lean), [Veir/InstSimplify/IS1551.lean](../../Veir/InstSimplify/IS1551.lean), [Veir/InstSimplify/IS1598.lean](../../Veir/InstSimplify/IS1598.lean), [Veir/InstSimplify/IS1603.lean](../../Veir/InstSimplify/IS1603.lean), [Veir/InstSimplify/IS1608.lean](../../Veir/InstSimplify/IS1608.lean), [Veir/InstSimplify/IS1613.lean](../../Veir/InstSimplify/IS1613.lean).
- **Theorems:** `Veir.InstSimplify.IS1534.valid_or`, `Veir.InstSimplify.IS1539.valid_and`, `Veir.InstSimplify.IS1545.valid_and`, `Veir.InstSimplify.IS1545.valid_or`, `Veir.InstSimplify.IS1551.valid_and`, `Veir.InstSimplify.IS1551.valid_or`, `Veir.InstSimplify.IS1598.valid_and`, `Veir.InstSimplify.IS1598.valid_or`, `Veir.InstSimplify.IS1603.valid_and`, `Veir.InstSimplify.IS1603.valid_or`, `Veir.InstSimplify.IS1608.valid_and`, `Veir.InstSimplify.IS1613.valid_or`.
- **Shared implementation:** [IS1534](#is1534), [IS1539](#is1539), [IS1545](#is1545), [IS1551](#is1551), [IS1598](#is1598), [IS1603](#is1603), [IS1608](#is1608), [IS1613](#is1613). This caller is not an additional independent port.
- **Details / missing facilities:** Partial dispatcher coverage: cited syntactic subtraction and unsigned-zero comparison families are proved. Remaining source branches IS1561/1564/1582/1588 require sound isKnownNonZero/ValueTracking facts; Puddle inspectOperation analysis facts are erased from validity and no certificate interface supplies those facts. The complete helper contract therefore cannot be represented.

<a id="is1730"></a>

## IS1730 — `simplifyAndOfICmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1729–1730](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1729-L1730). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyUnsignedRangeCheck (commuted) for the enclosing and operation.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS1534.lean](../../Veir/InstSimplify/IS1534.lean), [Veir/InstSimplify/IS1539.lean](../../Veir/InstSimplify/IS1539.lean), [Veir/InstSimplify/IS1545.lean](../../Veir/InstSimplify/IS1545.lean), [Veir/InstSimplify/IS1551.lean](../../Veir/InstSimplify/IS1551.lean), [Veir/InstSimplify/IS1598.lean](../../Veir/InstSimplify/IS1598.lean), [Veir/InstSimplify/IS1603.lean](../../Veir/InstSimplify/IS1603.lean), [Veir/InstSimplify/IS1608.lean](../../Veir/InstSimplify/IS1608.lean), [Veir/InstSimplify/IS1613.lean](../../Veir/InstSimplify/IS1613.lean).
- **Theorems:** `Veir.InstSimplify.IS1534.valid_or`, `Veir.InstSimplify.IS1539.valid_and`, `Veir.InstSimplify.IS1545.valid_and`, `Veir.InstSimplify.IS1545.valid_or`, `Veir.InstSimplify.IS1551.valid_and`, `Veir.InstSimplify.IS1551.valid_or`, `Veir.InstSimplify.IS1598.valid_and`, `Veir.InstSimplify.IS1598.valid_or`, `Veir.InstSimplify.IS1603.valid_and`, `Veir.InstSimplify.IS1603.valid_or`, `Veir.InstSimplify.IS1608.valid_and`, `Veir.InstSimplify.IS1613.valid_or`.
- **Shared implementation:** [IS1534](#is1534), [IS1539](#is1539), [IS1545](#is1545), [IS1551](#is1551), [IS1598](#is1598), [IS1603](#is1603), [IS1608](#is1608), [IS1613](#is1613). This caller is not an additional independent port.
- **Details / missing facilities:** Partial dispatcher coverage: cited syntactic subtraction and unsigned-zero comparison families are proved. Remaining source branches IS1561/1564/1582/1588 require sound isKnownNonZero/ValueTracking facts; Puddle inspectOperation analysis facts are erased from validity and no certificate interface supplies those facts. The complete helper contract therefore cannot be represented.

<a id="is1733"></a>

## IS1733 — `simplifyAndOfICmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1732–1733](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1732-L1733). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyAndOrOfICmpsWithConstants for the enclosing and operation.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar integer comparisons with constant operands; arbitrary width/predicates/constants; no FP/vector.
- **Lean:** [Veir/InstSimplify/IS1638.lean](../../Veir/InstSimplify/IS1638.lean), [Veir/InstSimplify/IS1643.lean](../../Veir/InstSimplify/IS1643.lean), [Veir/InstSimplify/IS1651.lean](../../Veir/InstSimplify/IS1651.lean), [Veir/InstSimplify/IS1653.lean](../../Veir/InstSimplify/IS1653.lean).
- **Theorems:** `Veir.InstSimplify.IS1638.valid`, `Veir.InstSimplify.IS1643.valid`, `Veir.InstSimplify.IS1651.valid_and`, `Veir.InstSimplify.IS1651.valid_or`, `Veir.InstSimplify.IS1653.valid_and`, `Veir.InstSimplify.IS1653.valid_or`.
- **Shared implementation:** [IS1638](#is1638), [IS1643](#is1643), [IS1651](#is1651), [IS1653](#is1653). This caller is not an additional independent port.
- **Details / missing facilities:** Scalar integer ConstantRange comparison-set helper dispatch covered by the four callee rules. Extensional native set checks enumerate 2^w inputs and may be impractical for large widths.

<a id="is1736"></a>

## IS1736 — `simplifyAndOfICmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1735–1736](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1735-L1736). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyAndOrOfICmpsWithCtpop for the enclosing and operation.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS1720.lean](../../Veir/InstSimplify/IS1720.lean).
- **Theorems:** `Veir.InstSimplify.IS1720_valid`.
- **Shared implementation:** [IS1720](#is1720). This caller is not an additional independent port.
- **Details / missing facilities:** Pure helper dispatch; the complete scalar ctpop AND family including both operand orders is implemented by the cited callee. No independent rewrite theorem is counted.

<a id="is1738"></a>

## IS1738 — `simplifyAndOfICmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1737–1738](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1737-L1738). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyAndOrOfICmpsWithCtpop (commuted) for the enclosing and operation.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS1720.lean](../../Veir/InstSimplify/IS1720.lean).
- **Theorems:** `Veir.InstSimplify.IS1720_valid`.
- **Shared implementation:** [IS1720](#is1720). This caller is not an additional independent port.
- **Details / missing facilities:** Pure helper dispatch; the complete scalar ctpop AND family including both operand orders is implemented by the cited callee. No independent rewrite theorem is counted.

<a id="is1741"></a>

## IS1741 — `simplifyAndOfICmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1740–1741](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1740-L1741). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyAndOfICmpsWithAdd for the enclosing and operation.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: operator flags via InstrInfoQuery.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS1682.lean](../../Veir/InstSimplify/IS1682.lean), [Veir/InstSimplify/IS1684.lean](../../Veir/InstSimplify/IS1684.lean), [Veir/InstSimplify/IS1688.lean](../../Veir/InstSimplify/IS1688.lean), [Veir/InstSimplify/IS1690.lean](../../Veir/InstSimplify/IS1690.lean), [Veir/InstSimplify/IS1696.lean](../../Veir/InstSimplify/IS1696.lean), [Veir/InstSimplify/IS1699.lean](../../Veir/InstSimplify/IS1699.lean).
- **Theorems:** `Veir.InstSimplify.IS1682.valid`, `Veir.InstSimplify.IS1684.valid`, `Veir.InstSimplify.IS1688.valid`, `Veir.InstSimplify.IS1690.valid`, `Veir.InstSimplify.IS1696.valid`, `Veir.InstSimplify.IS1699.valid`.
- **Shared implementation:** [IS1682](#is1682), [IS1684](#is1684), [IS1688](#is1688), [IS1690](#is1690), [IS1696](#is1696), [IS1699](#is1699). This caller is not an additional independent port.
- **Details / missing facilities:** Pure helper dispatch; all six scalar add/comparison AND branches, including both root operand orders, are implemented by the cited callees. No independent rewrite theorem is counted.

<a id="is1743"></a>

## IS1743 — `simplifyAndOfICmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1742–1743](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1742-L1743). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyAndOfICmpsWithAdd (commuted) for the enclosing and operation.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: operator flags via InstrInfoQuery.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS1682.lean](../../Veir/InstSimplify/IS1682.lean), [Veir/InstSimplify/IS1684.lean](../../Veir/InstSimplify/IS1684.lean), [Veir/InstSimplify/IS1688.lean](../../Veir/InstSimplify/IS1688.lean), [Veir/InstSimplify/IS1690.lean](../../Veir/InstSimplify/IS1690.lean), [Veir/InstSimplify/IS1696.lean](../../Veir/InstSimplify/IS1696.lean), [Veir/InstSimplify/IS1699.lean](../../Veir/InstSimplify/IS1699.lean).
- **Theorems:** `Veir.InstSimplify.IS1682.valid`, `Veir.InstSimplify.IS1684.valid`, `Veir.InstSimplify.IS1688.valid`, `Veir.InstSimplify.IS1690.valid`, `Veir.InstSimplify.IS1696.valid`, `Veir.InstSimplify.IS1699.valid`.
- **Shared implementation:** [IS1682](#is1682), [IS1684](#is1684), [IS1688](#is1688), [IS1690](#is1690), [IS1696](#is1696), [IS1699](#is1699). This caller is not an additional independent port.
- **Details / missing facilities:** Pure helper dispatch; all six scalar add/comparison AND branches, including both root operand orders, are implemented by the cited callees. No independent rewrite theorem is counted.

<a id="is1772"></a>

## IS1772 — `simplifyOrOfICmpsWithAdd`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1769–1772](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1769-L1772). Kind: rewrite.
- **Rewrite:** (icmp uge (add V,C0),C1) OR (icmp sle V,C0) -> true; C1-C0=2 in APInt modular arithmetic; C0 signed-positive.
- **Matched/replaced opcodes:** `or`, `icmp`, `add`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and signedness; all source flags, normalized APInt constant spellings, and source operand orientations. Vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS1772.lean](../../Veir/InstSimplify/IS1772.lean).
- **Theorems:** `Veir.InstSimplify.IS1772.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with kernel proofs and LLVM poison refinement; native guards implement the exact source conditions.

<a id="is1774"></a>

## IS1774 — `simplifyOrOfICmpsWithAdd`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1771–1774](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1771-L1774). Kind: rewrite.
- **Rewrite:** (icmp sge (add V,C0),C1) OR (icmp sle V,C0) -> true; C1-C0=2 in APInt modular arithmetic; C0 signed-positive and add nsw.
- **Matched/replaced opcodes:** `or`, `icmp`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: nsw flag.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and signedness; all source flags, normalized APInt constant spellings, and source operand orientations. Vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS1774.lean](../../Veir/InstSimplify/IS1774.lean).
- **Theorems:** `Veir.InstSimplify.IS1774.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with kernel proofs and LLVM poison refinement; native guards implement the exact source conditions.

<a id="is1778"></a>

## IS1778 — `simplifyOrOfICmpsWithAdd`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1775–1778](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1775-L1778). Kind: rewrite.
- **Rewrite:** (icmp ugt (add V,C0),C1) OR (icmp sle V,C0) -> true; C1-C0=1 in APInt modular arithmetic; C0 signed-positive.
- **Matched/replaced opcodes:** `or`, `icmp`, `add`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and signedness; all source flags, normalized APInt constant spellings, and source operand orientations. Vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS1778.lean](../../Veir/InstSimplify/IS1778.lean).
- **Theorems:** `Veir.InstSimplify.IS1778.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with kernel proofs and LLVM poison refinement; native guards implement the exact source conditions.

<a id="is1780"></a>

## IS1780 — `simplifyOrOfICmpsWithAdd`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1777–1780](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1777-L1780). Kind: rewrite.
- **Rewrite:** (icmp sgt (add V,C0),C1) OR (icmp sle V,C0) -> true; C1-C0=1 in APInt modular arithmetic; C0 signed-positive and add nsw.
- **Matched/replaced opcodes:** `or`, `icmp`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: nsw flag.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and signedness; all source flags, normalized APInt constant spellings, and source operand orientations. Vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS1780.lean](../../Veir/InstSimplify/IS1780.lean).
- **Theorems:** `Veir.InstSimplify.IS1780.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with kernel proofs and LLVM poison refinement; native guards implement the exact source conditions.

<a id="is1786"></a>

## IS1786 — `simplifyOrOfICmpsWithAdd`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1783–1786](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1783-L1786). Kind: rewrite.
- **Rewrite:** (icmp uge (add V,C0),C1) OR (icmp ule V,C0) -> true; C1-C0=2 in APInt modular arithmetic; C0 nonzero and add nuw.
- **Matched/replaced opcodes:** `or`, `icmp`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: nuw flag.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and signedness; all source flags, normalized APInt constant spellings, and source operand orientations. Vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS1786.lean](../../Veir/InstSimplify/IS1786.lean).
- **Theorems:** `Veir.InstSimplify.IS1786.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with kernel proofs and LLVM poison refinement; native guards implement the exact source conditions.

<a id="is1789"></a>

## IS1789 — `simplifyOrOfICmpsWithAdd`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1786–1789](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1786-L1789). Kind: rewrite.
- **Rewrite:** (icmp ugt (add V,C0),C1) OR (icmp ule V,C0) -> true; C1-C0=1 in APInt modular arithmetic; C0 nonzero and add nuw.
- **Matched/replaced opcodes:** `or`, `icmp`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: nuw flag.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and signedness; all source flags, normalized APInt constant spellings, and source operand orientations. Vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS1789.lean](../../Veir/InstSimplify/IS1789.lean).
- **Theorems:** `Veir.InstSimplify.IS1789.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with kernel proofs and LLVM poison refinement; native guards implement the exact source conditions.

<a id="is1798"></a>

## IS1798 — `simplifyOrOfICmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1797–1798](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1797-L1798). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyUnsignedRangeCheck for the enclosing or operation.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS1534.lean](../../Veir/InstSimplify/IS1534.lean), [Veir/InstSimplify/IS1539.lean](../../Veir/InstSimplify/IS1539.lean), [Veir/InstSimplify/IS1545.lean](../../Veir/InstSimplify/IS1545.lean), [Veir/InstSimplify/IS1551.lean](../../Veir/InstSimplify/IS1551.lean), [Veir/InstSimplify/IS1598.lean](../../Veir/InstSimplify/IS1598.lean), [Veir/InstSimplify/IS1603.lean](../../Veir/InstSimplify/IS1603.lean), [Veir/InstSimplify/IS1608.lean](../../Veir/InstSimplify/IS1608.lean), [Veir/InstSimplify/IS1613.lean](../../Veir/InstSimplify/IS1613.lean).
- **Theorems:** `Veir.InstSimplify.IS1534.valid_or`, `Veir.InstSimplify.IS1539.valid_and`, `Veir.InstSimplify.IS1545.valid_and`, `Veir.InstSimplify.IS1545.valid_or`, `Veir.InstSimplify.IS1551.valid_and`, `Veir.InstSimplify.IS1551.valid_or`, `Veir.InstSimplify.IS1598.valid_and`, `Veir.InstSimplify.IS1598.valid_or`, `Veir.InstSimplify.IS1603.valid_and`, `Veir.InstSimplify.IS1603.valid_or`, `Veir.InstSimplify.IS1608.valid_and`, `Veir.InstSimplify.IS1613.valid_or`.
- **Shared implementation:** [IS1534](#is1534), [IS1539](#is1539), [IS1545](#is1545), [IS1551](#is1551), [IS1598](#is1598), [IS1603](#is1603), [IS1608](#is1608), [IS1613](#is1613). This caller is not an additional independent port.
- **Details / missing facilities:** Partial dispatcher coverage: cited syntactic subtraction and unsigned-zero comparison families are proved. Remaining source branches IS1561/1564/1582/1588 require sound isKnownNonZero/ValueTracking facts; Puddle inspectOperation analysis facts are erased from validity and no certificate interface supplies those facts. The complete helper contract therefore cannot be represented.

<a id="is1800"></a>

## IS1800 — `simplifyOrOfICmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1799–1800](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1799-L1800). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyUnsignedRangeCheck (commuted) for the enclosing or operation.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS1534.lean](../../Veir/InstSimplify/IS1534.lean), [Veir/InstSimplify/IS1539.lean](../../Veir/InstSimplify/IS1539.lean), [Veir/InstSimplify/IS1545.lean](../../Veir/InstSimplify/IS1545.lean), [Veir/InstSimplify/IS1551.lean](../../Veir/InstSimplify/IS1551.lean), [Veir/InstSimplify/IS1598.lean](../../Veir/InstSimplify/IS1598.lean), [Veir/InstSimplify/IS1603.lean](../../Veir/InstSimplify/IS1603.lean), [Veir/InstSimplify/IS1608.lean](../../Veir/InstSimplify/IS1608.lean), [Veir/InstSimplify/IS1613.lean](../../Veir/InstSimplify/IS1613.lean).
- **Theorems:** `Veir.InstSimplify.IS1534.valid_or`, `Veir.InstSimplify.IS1539.valid_and`, `Veir.InstSimplify.IS1545.valid_and`, `Veir.InstSimplify.IS1545.valid_or`, `Veir.InstSimplify.IS1551.valid_and`, `Veir.InstSimplify.IS1551.valid_or`, `Veir.InstSimplify.IS1598.valid_and`, `Veir.InstSimplify.IS1598.valid_or`, `Veir.InstSimplify.IS1603.valid_and`, `Veir.InstSimplify.IS1603.valid_or`, `Veir.InstSimplify.IS1608.valid_and`, `Veir.InstSimplify.IS1613.valid_or`.
- **Shared implementation:** [IS1534](#is1534), [IS1539](#is1539), [IS1545](#is1545), [IS1551](#is1551), [IS1598](#is1598), [IS1603](#is1603), [IS1608](#is1608), [IS1613](#is1613). This caller is not an additional independent port.
- **Details / missing facilities:** Partial dispatcher coverage: cited syntactic subtraction and unsigned-zero comparison families are proved. Remaining source branches IS1561/1564/1582/1588 require sound isKnownNonZero/ValueTracking facts; Puddle inspectOperation analysis facts are erased from validity and no certificate interface supplies those facts. The complete helper contract therefore cannot be represented.

<a id="is1803"></a>

## IS1803 — `simplifyOrOfICmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1802–1803](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1802-L1803). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyAndOrOfICmpsWithConstants for the enclosing or operation.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar integer comparisons with constant operands; arbitrary width/predicates/constants; no FP/vector.
- **Lean:** [Veir/InstSimplify/IS1638.lean](../../Veir/InstSimplify/IS1638.lean), [Veir/InstSimplify/IS1643.lean](../../Veir/InstSimplify/IS1643.lean), [Veir/InstSimplify/IS1651.lean](../../Veir/InstSimplify/IS1651.lean), [Veir/InstSimplify/IS1653.lean](../../Veir/InstSimplify/IS1653.lean).
- **Theorems:** `Veir.InstSimplify.IS1638.valid`, `Veir.InstSimplify.IS1643.valid`, `Veir.InstSimplify.IS1651.valid_and`, `Veir.InstSimplify.IS1651.valid_or`, `Veir.InstSimplify.IS1653.valid_and`, `Veir.InstSimplify.IS1653.valid_or`.
- **Shared implementation:** [IS1638](#is1638), [IS1643](#is1643), [IS1651](#is1651), [IS1653](#is1653). This caller is not an additional independent port.
- **Details / missing facilities:** Scalar integer ConstantRange comparison-set helper dispatch covered by the four callee rules. Extensional native set checks enumerate 2^w inputs and may be impractical for large widths.

<a id="is1806"></a>

## IS1806 — `simplifyOrOfICmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1805–1806](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1805-L1806). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyAndOrOfICmpsWithCtpop for the enclosing or operation.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS1717.lean](../../Veir/InstSimplify/IS1717.lean).
- **Theorems:** `Veir.InstSimplify.IS1717_valid`.
- **Shared implementation:** [IS1717](#is1717). This caller is not an additional independent port.
- **Details / missing facilities:** Pure helper dispatch; the complete scalar ctpop OR family including both operand orders is implemented by the cited callee. No independent rewrite theorem is counted.

<a id="is1808"></a>

## IS1808 — `simplifyOrOfICmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1807–1808](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1807-L1808). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyAndOrOfICmpsWithCtpop (commuted) for the enclosing or operation.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS1717.lean](../../Veir/InstSimplify/IS1717.lean).
- **Theorems:** `Veir.InstSimplify.IS1717_valid`.
- **Shared implementation:** [IS1717](#is1717). This caller is not an additional independent port.
- **Details / missing facilities:** Pure helper dispatch; the complete scalar ctpop OR family including both operand orders is implemented by the cited callee. No independent rewrite theorem is counted.

<a id="is1811"></a>

## IS1811 — `simplifyOrOfICmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1810–1811](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1810-L1811). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyOrOfICmpsWithAdd for the enclosing or operation.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: operator flags via InstrInfoQuery.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS1772.lean](../../Veir/InstSimplify/IS1772.lean), [Veir/InstSimplify/IS1774.lean](../../Veir/InstSimplify/IS1774.lean), [Veir/InstSimplify/IS1778.lean](../../Veir/InstSimplify/IS1778.lean), [Veir/InstSimplify/IS1780.lean](../../Veir/InstSimplify/IS1780.lean), [Veir/InstSimplify/IS1786.lean](../../Veir/InstSimplify/IS1786.lean), [Veir/InstSimplify/IS1789.lean](../../Veir/InstSimplify/IS1789.lean).
- **Theorems:** `Veir.InstSimplify.IS1772.valid`, `Veir.InstSimplify.IS1774.valid`, `Veir.InstSimplify.IS1778.valid`, `Veir.InstSimplify.IS1780.valid`, `Veir.InstSimplify.IS1786.valid`, `Veir.InstSimplify.IS1789.valid`.
- **Shared implementation:** [IS1772](#is1772), [IS1774](#is1774), [IS1778](#is1778), [IS1780](#is1780), [IS1786](#is1786), [IS1789](#is1789). This caller is not an additional independent port.
- **Details / missing facilities:** Pure helper dispatch; all six scalar add/comparison OR branches, including both root operand orders, are implemented by the cited callees. No independent rewrite theorem is counted.

<a id="is1813"></a>

## IS1813 — `simplifyOrOfICmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1812–1813](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1812-L1813). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyOrOfICmpsWithAdd (commuted) for the enclosing or operation.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: operator flags via InstrInfoQuery.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS1772.lean](../../Veir/InstSimplify/IS1772.lean), [Veir/InstSimplify/IS1774.lean](../../Veir/InstSimplify/IS1774.lean), [Veir/InstSimplify/IS1778.lean](../../Veir/InstSimplify/IS1778.lean), [Veir/InstSimplify/IS1780.lean](../../Veir/InstSimplify/IS1780.lean), [Veir/InstSimplify/IS1786.lean](../../Veir/InstSimplify/IS1786.lean), [Veir/InstSimplify/IS1789.lean](../../Veir/InstSimplify/IS1789.lean).
- **Theorems:** `Veir.InstSimplify.IS1772.valid`, `Veir.InstSimplify.IS1774.valid`, `Veir.InstSimplify.IS1778.valid`, `Veir.InstSimplify.IS1780.valid`, `Veir.InstSimplify.IS1786.valid`, `Veir.InstSimplify.IS1789.valid`.
- **Shared implementation:** [IS1772](#is1772), [IS1774](#is1774), [IS1778](#is1778), [IS1780](#is1780), [IS1786](#is1786), [IS1789](#is1789). This caller is not an additional independent port.
- **Details / missing facilities:** Pure helper dispatch; all six scalar add/comparison OR branches, including both root operand orders, are implemented by the cited callees. No independent rewrite theorem is counted.

<a id="is1843"></a>

## IS1843 — `simplifyAndOrOfFCmpsWithConstants`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1842–1843](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1842-L1843). Kind: rewrite.
- **Rewrite:** For and-of-compares, check if the intersection is empty: (fcmp X, C0) && (fcmp X, C1) --> empty set --> false; returns `ConstantInt::getBool(Cmp0->getType(), !IsAnd)`. Guard: `Range0->intersectWith(*Range1).isEmptySet()`.
- **Matched/replaced opcodes:** `and`, `or`, `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: integer or floating-point range-set analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** LLVM floating point fcmp/fabs operations have no case in Llvm.interpretOp'; cannot prove via missing semantics.

<a id="is1851"></a>

## IS1851 — `simplifyAndOrOfFCmpsWithConstants`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1850–1851](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1850-L1851). Kind: rewrite.
- **Rewrite:** Is one range a superset of the other? If this is and-of-compares, take the smaller set: (fcmp ogt X, 4) && (fcmp ogt X, 42) --> fcmp ogt X, 42 If this is or-of-compares, take the larger set: (fcmp ogt X, 4) || (fcmp ogt X, 42) --> fcmp ogt X, 4; returns `Cmp1`. Guard: `Range0->contains(*Range1)`.
- **Matched/replaced opcodes:** `and`, `or`, `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: integer or floating-point range-set analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** LLVM floating point fcmp/fabs operations have no case in Llvm.interpretOp'; cannot prove via missing semantics.

<a id="is1853"></a>

## IS1853 — `simplifyAndOrOfFCmpsWithConstants`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1852–1853](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1852-L1853). Kind: rewrite.
- **Rewrite:** Is one range a superset of the other? If this is and-of-compares, take the smaller set: (fcmp ogt X, 4) && (fcmp ogt X, 42) --> fcmp ogt X, 42 If this is or-of-compares, take the larger set: (fcmp ogt X, 4) || (fcmp ogt X, 42) --> fcmp ogt X, 4; returns `Cmp0`. Guard: `Range1->contains(*Range0)`.
- **Matched/replaced opcodes:** `and`, `or`, `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: integer or floating-point range-set analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** LLVM floating point fcmp/fabs operations have no case in Llvm.interpretOp'; cannot prove via missing semantics.

<a id="is1876"></a>

## IS1876 — `simplifyAndOrOfFCmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1876–1876](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1876). Kind: rewrite.
- **Rewrite:** For `(fcmp ord/uno X, +0) {and/or} (fcmp ordered/unordered X-or-fabs(X), Y)`, return the other `fcmp` when order classes agree; otherwise return false for AND or true for OR. Guard: `PredL` is ORD/UNO; `PredR` order class matches AND/OR mode; an RHS operand is X or `fabs(X)`; LHS constant is +0.
- **Matched/replaced opcodes:** `and`, `or`, `fcmp`, `fabs`.
- **Beyond opcode/constant/SSA matching:** Yes — floating-point predicate ordering and positive-zero semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** LLVM floating point fcmp/fabs operations have no case in Llvm.interpretOp'; cannot prove via missing semantics.

<a id="is1891"></a>

## IS1891 — `simplifyAndOrOfFCmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1891–1891](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1891). Kind: rewrite.
- **Rewrite:** Symmetric ORD/UNO simplification: for `(fcmp ordered/unordered X-or-fabs(X), Y) {and/or} (fcmp ord/uno X, +0)`, return the first `fcmp` when order classes agree; otherwise return false for AND or true for OR. Guard: `PredR` is ORD/UNO; `PredL` order class matches AND/OR mode; an LHS operand is X or `fabs(X)`; RHS constant is +0.
- **Matched/replaced opcodes:** `and`, `or`, `fcmp`, `fabs`.
- **Beyond opcode/constant/SSA matching:** Yes — floating-point predicate ordering and positive-zero semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** LLVM floating point fcmp/fabs operations have no case in Llvm.interpretOp'; cannot prove via missing semantics.

<a id="is1897"></a>

## IS1897 — `simplifyAndOrOfFCmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1896–1897](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1896-L1897). Kind: delegation.
- **Rewrite:** (fcmp o** X/abs(X), Y) & (fcmp ord X, 0) --> fcmp o** X/abs(X), Y (fcmp o** X/abs(X), Y) & (fcmp uno X, 0) --> false (fcmp u** X/abs(X), Y) | (fcmp uno X, 0) --> fcmp u** X/abs(X), Y (fcmp u** X/abs(X), Y) | (fcmp ord X, 0) --> true; returns `V`. Guard: `auto *V = simplifyAndOrOfFCmpsWithConstants(LHS, RHS, IsAnd)`. Delegates to `simplifyAndOrOfFCmpsWithConstants`.
- **Matched/replaced opcodes:** `and`, `or`, `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Delegates to floating-point comparison range combination. Llvm.interpretOp' has no floating-point comparison/value semantics, so the FCmp constant regions and returned comparison/Boolean result cannot be interpreted.

<a id="is1928"></a>

## IS1928 — `simplifyAndOrOfCmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1927–1928](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1927-L1928). Kind: delegation.
- **Rewrite:** After successful ICmp or FCmp combination simplification, return its result directly when no cast was stripped; this dispatch includes both integer and floating point comparisons.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`, `fcmp`, `cast`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS1534.lean](../../Veir/InstSimplify/IS1534.lean), [Veir/InstSimplify/IS1539.lean](../../Veir/InstSimplify/IS1539.lean), [Veir/InstSimplify/IS1545.lean](../../Veir/InstSimplify/IS1545.lean), [Veir/InstSimplify/IS1551.lean](../../Veir/InstSimplify/IS1551.lean), [Veir/InstSimplify/IS1598.lean](../../Veir/InstSimplify/IS1598.lean), [Veir/InstSimplify/IS1603.lean](../../Veir/InstSimplify/IS1603.lean), [Veir/InstSimplify/IS1608.lean](../../Veir/InstSimplify/IS1608.lean), [Veir/InstSimplify/IS1613.lean](../../Veir/InstSimplify/IS1613.lean), [Veir/InstSimplify/IS1638.lean](../../Veir/InstSimplify/IS1638.lean), [Veir/InstSimplify/IS1643.lean](../../Veir/InstSimplify/IS1643.lean), [Veir/InstSimplify/IS1651.lean](../../Veir/InstSimplify/IS1651.lean), [Veir/InstSimplify/IS1653.lean](../../Veir/InstSimplify/IS1653.lean), [Veir/InstSimplify/IS1682.lean](../../Veir/InstSimplify/IS1682.lean), [Veir/InstSimplify/IS1684.lean](../../Veir/InstSimplify/IS1684.lean), [Veir/InstSimplify/IS1688.lean](../../Veir/InstSimplify/IS1688.lean), [Veir/InstSimplify/IS1690.lean](../../Veir/InstSimplify/IS1690.lean), [Veir/InstSimplify/IS1696.lean](../../Veir/InstSimplify/IS1696.lean), [Veir/InstSimplify/IS1699.lean](../../Veir/InstSimplify/IS1699.lean), [Veir/InstSimplify/IS1717.lean](../../Veir/InstSimplify/IS1717.lean), [Veir/InstSimplify/IS1720.lean](../../Veir/InstSimplify/IS1720.lean), [Veir/InstSimplify/IS1772.lean](../../Veir/InstSimplify/IS1772.lean), [Veir/InstSimplify/IS1774.lean](../../Veir/InstSimplify/IS1774.lean), [Veir/InstSimplify/IS1778.lean](../../Veir/InstSimplify/IS1778.lean), [Veir/InstSimplify/IS1780.lean](../../Veir/InstSimplify/IS1780.lean), [Veir/InstSimplify/IS1786.lean](../../Veir/InstSimplify/IS1786.lean), [Veir/InstSimplify/IS1789.lean](../../Veir/InstSimplify/IS1789.lean).
- **Theorems:** `Veir.InstSimplify.IS1534.valid_or`, `Veir.InstSimplify.IS1539.valid_and`, `Veir.InstSimplify.IS1545.valid_and`, `Veir.InstSimplify.IS1545.valid_or`, `Veir.InstSimplify.IS1551.valid_and`, `Veir.InstSimplify.IS1551.valid_or`, `Veir.InstSimplify.IS1598.valid_and`, `Veir.InstSimplify.IS1598.valid_or`, `Veir.InstSimplify.IS1603.valid_and`, `Veir.InstSimplify.IS1603.valid_or`, `Veir.InstSimplify.IS1608.valid_and`, `Veir.InstSimplify.IS1613.valid_or`, `Veir.InstSimplify.IS1638.valid`, `Veir.InstSimplify.IS1643.valid`, `Veir.InstSimplify.IS1651.valid_and`, `Veir.InstSimplify.IS1651.valid_or`, `Veir.InstSimplify.IS1653.valid_and`, `Veir.InstSimplify.IS1653.valid_or`, `Veir.InstSimplify.IS1682.valid`, `Veir.InstSimplify.IS1684.valid`, `Veir.InstSimplify.IS1688.valid`, `Veir.InstSimplify.IS1690.valid`, `Veir.InstSimplify.IS1696.valid`, `Veir.InstSimplify.IS1699.valid`, `Veir.InstSimplify.IS1717_valid`, `Veir.InstSimplify.IS1720_valid`, `Veir.InstSimplify.IS1772.valid`, `Veir.InstSimplify.IS1774.valid`, `Veir.InstSimplify.IS1778.valid`, `Veir.InstSimplify.IS1780.valid`, `Veir.InstSimplify.IS1786.valid`, `Veir.InstSimplify.IS1789.valid`.
- **Shared implementation:** [IS1534](#is1534), [IS1539](#is1539), [IS1545](#is1545), [IS1551](#is1551), [IS1598](#is1598), [IS1603](#is1603), [IS1608](#is1608), [IS1613](#is1613), [IS1638](#is1638), [IS1643](#is1643), [IS1651](#is1651), [IS1653](#is1653), [IS1717](#is1717), [IS1720](#is1720), [IS1682](#is1682), [IS1684](#is1684), [IS1688](#is1688), [IS1690](#is1690), [IS1696](#is1696), [IS1699](#is1699), [IS1772](#is1772), [IS1774](#is1774), [IS1778](#is1778), [IS1780](#is1780), [IS1786](#is1786), [IS1789](#is1789). This caller is not an additional independent port.
- **Details / missing facilities:** Partial comparison-helper dispatch coverage: cited scalar integer syntactic, constant-range, ctpop, and add/comparison branches are proved. The complete source helper also invokes isKnownNonZero/ValueTracking branches lacking sound analysis certificates and FP comparison branches lacking interpreter semantics. IS1933 additionally folds the returned constant through the stripped cast; no complete contract is claimed for these dispatchers.

<a id="is1933"></a>

## IS1933 — `simplifyAndOrOfCmps`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1933–1933](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1933). Kind: delegation.
- **Rewrite:** After stripping matching casts and successfully simplifying the enclosed ICmp or FCmp combination to a constant, return ConstantFoldCastOperand of that constant through the original cast.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`, `fcmp`, `cast`.
- **Beyond opcode/constant/SSA matching:** Yes — constant cast folding and source/result type constraints.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS1534.lean](../../Veir/InstSimplify/IS1534.lean), [Veir/InstSimplify/IS1539.lean](../../Veir/InstSimplify/IS1539.lean), [Veir/InstSimplify/IS1545.lean](../../Veir/InstSimplify/IS1545.lean), [Veir/InstSimplify/IS1551.lean](../../Veir/InstSimplify/IS1551.lean), [Veir/InstSimplify/IS1598.lean](../../Veir/InstSimplify/IS1598.lean), [Veir/InstSimplify/IS1603.lean](../../Veir/InstSimplify/IS1603.lean), [Veir/InstSimplify/IS1608.lean](../../Veir/InstSimplify/IS1608.lean), [Veir/InstSimplify/IS1613.lean](../../Veir/InstSimplify/IS1613.lean), [Veir/InstSimplify/IS1638.lean](../../Veir/InstSimplify/IS1638.lean), [Veir/InstSimplify/IS1643.lean](../../Veir/InstSimplify/IS1643.lean), [Veir/InstSimplify/IS1651.lean](../../Veir/InstSimplify/IS1651.lean), [Veir/InstSimplify/IS1653.lean](../../Veir/InstSimplify/IS1653.lean), [Veir/InstSimplify/IS1682.lean](../../Veir/InstSimplify/IS1682.lean), [Veir/InstSimplify/IS1684.lean](../../Veir/InstSimplify/IS1684.lean), [Veir/InstSimplify/IS1688.lean](../../Veir/InstSimplify/IS1688.lean), [Veir/InstSimplify/IS1690.lean](../../Veir/InstSimplify/IS1690.lean), [Veir/InstSimplify/IS1696.lean](../../Veir/InstSimplify/IS1696.lean), [Veir/InstSimplify/IS1699.lean](../../Veir/InstSimplify/IS1699.lean), [Veir/InstSimplify/IS1717.lean](../../Veir/InstSimplify/IS1717.lean), [Veir/InstSimplify/IS1720.lean](../../Veir/InstSimplify/IS1720.lean), [Veir/InstSimplify/IS1772.lean](../../Veir/InstSimplify/IS1772.lean), [Veir/InstSimplify/IS1774.lean](../../Veir/InstSimplify/IS1774.lean), [Veir/InstSimplify/IS1778.lean](../../Veir/InstSimplify/IS1778.lean), [Veir/InstSimplify/IS1780.lean](../../Veir/InstSimplify/IS1780.lean), [Veir/InstSimplify/IS1786.lean](../../Veir/InstSimplify/IS1786.lean), [Veir/InstSimplify/IS1789.lean](../../Veir/InstSimplify/IS1789.lean).
- **Theorems:** `Veir.InstSimplify.IS1534.valid_or`, `Veir.InstSimplify.IS1539.valid_and`, `Veir.InstSimplify.IS1545.valid_and`, `Veir.InstSimplify.IS1545.valid_or`, `Veir.InstSimplify.IS1551.valid_and`, `Veir.InstSimplify.IS1551.valid_or`, `Veir.InstSimplify.IS1598.valid_and`, `Veir.InstSimplify.IS1598.valid_or`, `Veir.InstSimplify.IS1603.valid_and`, `Veir.InstSimplify.IS1603.valid_or`, `Veir.InstSimplify.IS1608.valid_and`, `Veir.InstSimplify.IS1613.valid_or`, `Veir.InstSimplify.IS1638.valid`, `Veir.InstSimplify.IS1643.valid`, `Veir.InstSimplify.IS1651.valid_and`, `Veir.InstSimplify.IS1651.valid_or`, `Veir.InstSimplify.IS1653.valid_and`, `Veir.InstSimplify.IS1653.valid_or`, `Veir.InstSimplify.IS1682.valid`, `Veir.InstSimplify.IS1684.valid`, `Veir.InstSimplify.IS1688.valid`, `Veir.InstSimplify.IS1690.valid`, `Veir.InstSimplify.IS1696.valid`, `Veir.InstSimplify.IS1699.valid`, `Veir.InstSimplify.IS1717_valid`, `Veir.InstSimplify.IS1720_valid`, `Veir.InstSimplify.IS1772.valid`, `Veir.InstSimplify.IS1774.valid`, `Veir.InstSimplify.IS1778.valid`, `Veir.InstSimplify.IS1780.valid`, `Veir.InstSimplify.IS1786.valid`, `Veir.InstSimplify.IS1789.valid`.
- **Shared implementation:** [IS1534](#is1534), [IS1539](#is1539), [IS1545](#is1545), [IS1551](#is1551), [IS1598](#is1598), [IS1603](#is1603), [IS1608](#is1608), [IS1613](#is1613), [IS1638](#is1638), [IS1643](#is1643), [IS1651](#is1651), [IS1653](#is1653), [IS1717](#is1717), [IS1720](#is1720), [IS1682](#is1682), [IS1684](#is1684), [IS1688](#is1688), [IS1690](#is1690), [IS1696](#is1696), [IS1699](#is1699), [IS1772](#is1772), [IS1774](#is1774), [IS1778](#is1778), [IS1780](#is1780), [IS1786](#is1786), [IS1789](#is1789). This caller is not an additional independent port.
- **Details / missing facilities:** Partial comparison-helper dispatch coverage: cited scalar integer syntactic, constant-range, ctpop, and add/comparison branches are proved. The complete source helper also invokes isKnownNonZero/ValueTracking branches lacking sound analysis certificates and FP comparison branches lacking interpreter semantics. IS1933 additionally folds the returned constant through the stripped cast; no complete contract is claimed for these dispatchers.

<a id="is1965"></a>

## IS1965 — `simplifyAndOrWithICmpEq`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1963–1965](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1963-L1965). Kind: rewrite.
- **Rewrite:** and (icmp eq a, b), x implies (a==b) inside x. or (icmp ne a, b), x implies (a==b) inside x. If x simplifies to true/false, we can simplify the and/or.; returns `Absorber`. Guard: `Pred == (Opcode == Instruction::And ? ICmpInst::ICMP_EQ : ICmpInst::ICMP_NE)` and `Res == Absorber`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Requires recursive simplifyWithOpReplaced with contextual equality and poison-refinement contract; Puddle has no reusable certified recursive replacement facility.

<a id="is1967"></a>

## IS1967 — `simplifyAndOrWithICmpEq`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1965–1967](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1965-L1967). Kind: rewrite.
- **Rewrite:** and (icmp eq a, b), x implies (a==b) inside x. or (icmp ne a, b), x implies (a==b) inside x. If x simplifies to true/false, we can simplify the and/or.; returns `Op0`. Guard: `Pred == (Opcode == Instruction::And ? ICmpInst::ICMP_EQ : ICmpInst::ICMP_NE)` and `Res == ConstantExpr::getBinOpIdentity(Opcode, Res->getType())`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Requires recursive simplifyWithOpReplaced with contextual equality and poison-refinement contract; Puddle has no reusable certified recursive replacement facility.

<a id="is1975"></a>

## IS1975 — `simplifyAndOrWithICmpEq`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1974–1975](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1974-L1975). Kind: rewrite.
- **Rewrite:** If we have and (icmp ne a, b), x and for a==b we can simplify x to false, then we can drop the icmp, as x will already be false in the case where the icmp is false. Similar for or and true.; returns `Op1`. Guard: `Res == Absorber`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Requires recursive simplifyWithOpReplaced with contextual equality and poison-refinement contract; Puddle has no reusable certified recursive replacement facility.

<a id="is1985"></a>

## IS1985 — `simplifyAndOrWithICmpEq`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1984–1985](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1984-L1985). Kind: rewrite.
- **Rewrite:** In the final case (Res == Absorber with inverted predicate), it is safe to refine poison during simplification, but not undef. For simplicity always disable undef-based folds here.; returns `Simplify(Res)`. Guard: `Value *Res = simplifyWithOpReplaced(Op1, A, B, Q.getWithoutUndef(), /* AllowRefinement */ true, /* DropFlags */ nullptr, MaxRecurse)`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Requires recursive simplifyWithOpReplaced with contextual equality and poison-refinement contract; Puddle has no reusable certified recursive replacement facility.

<a id="is1989"></a>

## IS1989 — `simplifyAndOrWithICmpEq`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:1988–1989](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L1988-L1989). Kind: rewrite.
- **Rewrite:** In the final case (Res == Absorber with inverted predicate), it is safe to refine poison during simplification, but not undef. For simplicity always disable undef-based folds here.; returns `Simplify(Res)`. Guard: `Value *Res = simplifyWithOpReplaced(Op1, B, A, Q.getWithoutUndef(), /* AllowRefinement */ true, /* DropFlags */ nullptr, MaxRecurse)`.
- **Matched/replaced opcodes:** `and`, `or`, `icmp`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Requires recursive simplifyWithOpReplaced with contextual equality and poison-refinement contract; Puddle has no reusable certified recursive replacement facility.

<a id="is2011"></a>

## IS2011 — `simplifyLogicOfAddSub`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2011–2011](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2011). Kind: rewrite.
- **Rewrite:** If operands are `(X + C)` and `(~C - X)` in either order, simplify `and` to zero and `or`/`xor` to all ones. Guard: C2 equals bitwise-not C1; same X; result op is And/Or/Xor.
- **Matched/replaced opcodes:** `add`, `sub`, `and`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and instruction flags; no vectors.
- **Lean:** [Veir/InstSimplify/IS2011.lean](../../Veir/InstSimplify/IS2011.lean).
- **Theorems:** `Veir.InstSimplify.IS2011.valid_and`, `Veir.InstSimplify.IS2011.valid_or`, `Veir.InstSimplify.IS2011.valid_xor`.
- **Details / missing facilities:** Compiled width-parametric LLVM scalar refinement proof, preserving poison and all source instruction flags.

<a id="is2024"></a>

## IS2024 — `simplifyAndCommutative`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2023–2024](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2023-L2024). Kind: rewrite.
- **Rewrite:** ~A & A =  0; returns `Constant::getNullValue(Op0->getType())`. Guard: `match(Op0, m_Not(m_Specific(Op1)))`.
- **Matched/replaced opcodes:** `and`, `or`, `xor`, `mul`, `shl`, `add`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2024.lean](../../Veir/InstSimplify/IS2024.lean).
- **Theorems:** `Veir.InstSimplify.IS2024.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2028"></a>

## IS2028 — `simplifyAndCommutative`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2027–2028](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2027-L2028). Kind: rewrite.
- **Rewrite:** (A | ?) & A = A; returns `Op1`. Guard: `match(Op0, m_c_Or(m_Specific(Op1), m_Value()))`.
- **Matched/replaced opcodes:** `and`, `or`, `xor`, `mul`, `shl`, `add`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2028.lean](../../Veir/InstSimplify/IS2028.lean).
- **Theorems:** `Veir.InstSimplify.IS2028.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2034"></a>

## IS2034 — `simplifyAndCommutative`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2033–2034](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2033-L2034). Kind: rewrite.
- **Rewrite:** (X | ~Y) & (X | Y) --> X; returns `X`. Guard: `match(Op0, m_c_Or(m_Value(X), m_Not(m_Value(Y)))) && match(Op1, m_c_Or(m_Specific(X), m_Specific(Y)))`.
- **Matched/replaced opcodes:** `and`, `or`, `xor`, `mul`, `shl`, `add`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2034.lean](../../Veir/InstSimplify/IS2034.lean).
- **Theorems:** `Veir.InstSimplify.IS2034.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2040"></a>

## IS2040 — `simplifyAndCommutative`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2039–2040](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2039-L2040). Kind: delegation.
- **Rewrite:** If we have a multiplication overflow check that is being 'and'ed with a check that one of the multipliers is not zero, we can omit the 'and', and only keep the overflow check.; returns `Op1`. Guard: `isCheckForZeroAndMulWithOverflow(Op0, Op1, true)`.
- **Matched/replaced opcodes:** `and`, `or`, `xor`, `mul`, `shl`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: overflow-intrinsic and zero-check pattern analysis; recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Requires isCheckForZeroAndMulWithOverflow recognition and semantics for the multiplication-with-overflow aggregate result and extractvalue projections. Llvm.interpretOp' does not interpret the required overflow intrinsic aggregate/extractvalue operations, so this scalar helper cannot currently be represented.

<a id="is2045"></a>

## IS2045 — `simplifyAndCommutative`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2044–2045](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2044-L2045). Kind: rewrite.
- **Rewrite:** -A & A = A if A is a power of two or zero.; returns `Op1`. Guard: `match(Op0, m_Neg(m_Specific(Op1))) && isKnownToBeAPowerOfTwo(Op1, Q.DL, /*OrZero*/ true, Q.AC, Q.CtxI, Q.DT)`.
- **Matched/replaced opcodes:** `and`, `or`, `xor`, `mul`, `shl`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: power-of-two value-tracking proof; analysis required: dominance analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is2051"></a>

## IS2051 — `simplifyAndCommutative`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2050–2051](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2050-L2051). Kind: rewrite.
- **Rewrite:** This is a similar pattern used for checking if a value is a power-of-2: (A - 1) & A --> 0 (if A is a power-of-2 or 0); returns `Constant::getNullValue(Op1->getType())`. Guard: `match(Op0, m_Add(m_Specific(Op1), m_AllOnes())) && isKnownToBeAPowerOfTwo(Op1, Q.DL, /*OrZero*/ true, Q.AC, Q.CtxI, Q.DT)`.
- **Matched/replaced opcodes:** `and`, `or`, `xor`, `mul`, `shl`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: power-of-two value-tracking proof; analysis required: dominance analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is2060"></a>

## IS2060 — `simplifyAndCommutative`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2059–2060](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2059-L2060). Kind: rewrite.
- **Rewrite:** (x << N) & ((x << M) - 1) --> 0, where x is known to be a power of 2 and M <= N.; returns `Constant::getNullValue(Op0->getType())`. Guard: `match(Op0, m_Shl(m_Value(X), m_APInt(Shift1))) && match(Op1, m_Add(m_Shl(m_Specific(X), m_APInt(Shift2)), m_AllOnes())) && isKnownToBeAPowerOfTwo(X, Q.DL, /*OrZero*/ true, Q.AC, Q.CtxI) && Shift1->uge(*Shift2)`.
- **Matched/replaced opcodes:** `and`, `or`, `xor`, `mul`, `shl`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: power-of-two value-tracking proof.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is2064"></a>

## IS2064 — `simplifyAndCommutative`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2063–2064](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2063-L2064). Kind: delegation.
- **Rewrite:** (x << N) & ((x << M) - 1) --> 0, where x is known to be a power of 2 and M <= N.; returns `V`. Guard: `Value *V = simplifyAndOrWithICmpEq(Instruction::And, Op0, Op1, Q, MaxRecurse)`. Delegates to `simplifyAndOrWithICmpEq`.
- **Matched/replaced opcodes:** `and`, `or`, `xor`, `mul`, `shl`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Shared implementation:** [IS1965](#is1965), [IS1967](#is1967), [IS1975](#is1975), [IS1985](#is1985), [IS1989](#is1989). This caller is not an additional independent port.
- **Details / missing facilities:** Delegates to contextual equality replacement helper (IS1965–IS1989): missing proof-bearing recursive simplifyWithOpReplaced and contextual poison-refinement composition contract.

<a id="is2074"></a>

## IS2074 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2073–2074](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2073-L2074). Kind: delegation.
- **Rewrite:** Given operands for an And, see if we can fold the result. If not, this returns null.; returns `C`. Guard: `Constant *C = foldOrCommuteConstant(Instruction::And, Op0, Op1, Q)`. Delegates to `foldOrCommuteConstant`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integer constant operands, arbitrary width and instruction properties; no FP/vector/undef.
- **Lean:** [Veir/InstSimplify/IS0582.lean](../../Veir/InstSimplify/IS0582.lean).
- **Theorems:** `Veir.InstSimplify.IS0582.pattern_and_valid`.
- **Shared implementation:** [IS0582](#is0582). This caller is not an additional independent port.
- **Details / missing facilities:** Successful constant-fold delegation covered by the certified scalar LLVM constant-fold pattern IS0582 for this opcode. Commutation itself returns no rewrite.

<a id="is2078"></a>

## IS2078 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2077–2078](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2077-L2078). Kind: rewrite.
- **Rewrite:** X & poison -> poison; returns `Op1`. Guard: `isa<PoisonValue>(Op1)`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM poison propagation semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2078.lean](../../Veir/InstSimplify/IS2078.lean).
- **Theorems:** `Veir.InstSimplify.IS2078.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2082"></a>

## IS2082 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2081–2082](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2081-L2082). Kind: rewrite.
- **Rewrite:** X & undef -> 0; returns `Constant::getNullValue(Op0->getType())`. Guard: `Q.isUndefValue(Op1)`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM undef nondeterministic semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** LLVM undef nondeterminism is absent from LLVM.Int and Llvm.interpretOp'.

<a id="is2086"></a>

## IS2086 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2085–2086](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2085-L2086). Kind: rewrite.
- **Rewrite:** X & X = X; returns `Op0`. Guard: `Op0 == Op1`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2086.lean](../../Veir/InstSimplify/IS2086.lean).
- **Theorems:** `Veir.InstSimplify.IS2086.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2090"></a>

## IS2090 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2089–2090](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2089-L2090). Kind: rewrite.
- **Rewrite:** X & 0 = 0; returns `Constant::getNullValue(Op0->getType())`. Guard: `match(Op1, m_Zero())`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2090.lean](../../Veir/InstSimplify/IS2090.lean).
- **Theorems:** `Veir.InstSimplify.IS2090.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2094"></a>

## IS2094 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2093–2094](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2093-L2094). Kind: rewrite.
- **Rewrite:** X & -1 = X; returns `Op0`. Guard: `match(Op1, m_AllOnes())`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2094.lean](../../Veir/InstSimplify/IS2094.lean).
- **Theorems:** `Veir.InstSimplify.IS2094.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2097"></a>

## IS2097 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2096–2097](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2096-L2097). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyAndCommutative for the enclosing and operation.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS2024.lean](../../Veir/InstSimplify/IS2024.lean), [Veir/InstSimplify/IS2028.lean](../../Veir/InstSimplify/IS2028.lean), [Veir/InstSimplify/IS2034.lean](../../Veir/InstSimplify/IS2034.lean).
- **Theorems:** `Veir.InstSimplify.IS2024.valid`, `Veir.InstSimplify.IS2028.valid`, `Veir.InstSimplify.IS2034.valid`.
- **Shared implementation:** [IS2024](#is2024), [IS2028](#is2028), [IS2034](#is2034). This caller is not an additional independent port.
- **Details / missing facilities:** Partial dispatcher coverage: cited structural absorption branches are proved with commutations. Other source branches require overflow aggregate/extractvalue semantics, sound power-of-two/known-bits certificates, or recursive simplifyWithOpReplaced composition, which the present LLVM/Puddle interfaces do not supply.

<a id="is2099"></a>

## IS2099 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2098–2099](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2098-L2099). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyAndCommutative (commuted) for the enclosing and operation.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS2024.lean](../../Veir/InstSimplify/IS2024.lean), [Veir/InstSimplify/IS2028.lean](../../Veir/InstSimplify/IS2028.lean), [Veir/InstSimplify/IS2034.lean](../../Veir/InstSimplify/IS2034.lean).
- **Theorems:** `Veir.InstSimplify.IS2024.valid`, `Veir.InstSimplify.IS2028.valid`, `Veir.InstSimplify.IS2034.valid`.
- **Shared implementation:** [IS2024](#is2024), [IS2028](#is2028), [IS2034](#is2034). This caller is not an additional independent port.
- **Details / missing facilities:** Partial dispatcher coverage: cited structural absorption branches are proved with commutations. Other source branches require overflow aggregate/extractvalue semantics, sound power-of-two/known-bits certificates, or recursive simplifyWithOpReplaced composition, which the present LLVM/Puddle interfaces do not supply.

<a id="is2102"></a>

## IS2102 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2101–2102](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2101-L2102). Kind: delegation.
- **Rewrite:** X & -1 = X; returns `V`. Guard: `Value *V = simplifyLogicOfAddSub(Op0, Op1, Instruction::And)`. Delegates to `simplifyLogicOfAddSub`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths and constant payload spellings; no vectors.
- **Lean:** [Veir/InstSimplify/IS2011.lean](../../Veir/InstSimplify/IS2011.lean).
- **Theorems:** `Veir.InstSimplify.IS2011.valid_and`.
- **Shared implementation:** [IS2011](#is2011). This caller is not an additional independent port.
- **Details / missing facilities:** Shared add/sub logic helper dispatch covered by the corresponding opcode pattern, including root commutation and all nsw/nuw/disjoint flags.

<a id="is2113"></a>

## IS2113 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2111–2113](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2111-L2113). Kind: rewrite.
- **Rewrite:** If all bits in the inverted and shifted mask are clear: and (shl X, ShAmt), Mask --> shl X, ShAmt; returns `Op0`. Guard: `match(Op1, m_APInt(Mask))` and `match(Op0, m_Shl(m_Value(X), m_APInt(ShAmt))) && (~(*Mask)).lshr(*ShAmt).isZero()`.
- **Matched/replaced opcodes:** `and`, `shl`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and instruction flags; no vectors.
- **Lean:** [Veir/InstSimplify/IS2113.lean](../../Veir/InstSimplify/IS2113.lean).
- **Theorems:** `Veir.InstSimplify.IS2113.valid`.
- **Details / missing facilities:** Compiled width-parametric LLVM scalar refinement proof, preserving poison and all source instruction flags.

<a id="is2119"></a>

## IS2119 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2117–2119](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2117-L2119). Kind: rewrite.
- **Rewrite:** If all bits in the inverted and shifted mask are clear: and (lshr X, ShAmt), Mask --> lshr X, ShAmt; returns `Op0`. Guard: `match(Op1, m_APInt(Mask))` and `match(Op0, m_LShr(m_Value(X), m_APInt(ShAmt))) && (~(*Mask)).shl(*ShAmt).isZero()`.
- **Matched/replaced opcodes:** `and`, `lshr`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and instruction flags; no vectors.
- **Lean:** [Veir/InstSimplify/IS2119.lean](../../Veir/InstSimplify/IS2119.lean).
- **Theorems:** `Veir.InstSimplify.IS2119.valid`.
- **Details / missing facilities:** Compiled width-parametric LLVM scalar refinement proof, preserving poison and all source instruction flags.

<a id="is2132"></a>

## IS2132 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2130–2132](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2130-L2132). Kind: rewrite.
- **Rewrite:** Use getActiveBits() to make use of the additional power of two knowledge; returns `ConstantInt::getNullValue(Op1->getType())`. Guard: `match(Op1, m_Power2(PowerC)) && match(Op0, m_Add(m_Value(Shift), m_AllOnes())) && isKnownToBeAPowerOfTwo(Shift, Q.DL, /*OrZero*/ false, Q.AC, Q.CtxI, Q.DT)` and `PowerC->getActiveBits() >= Known.getMaxValue().getActiveBits()`.
- **Matched/replaced opcodes:** `and`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: power-of-two value-tracking proof; analysis required: dominance analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is2136"></a>

## IS2136 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2135–2136](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2135-L2136). Kind: delegation.
- **Rewrite:** Use getActiveBits() to make use of the additional power of two knowledge; returns `V`. Guard: `Value *V = simplifyAndOrOfCmps(Q, Op0, Op1, true)`. Delegates to `simplifyAndOrOfCmps`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS1534.lean](../../Veir/InstSimplify/IS1534.lean), [Veir/InstSimplify/IS1539.lean](../../Veir/InstSimplify/IS1539.lean), [Veir/InstSimplify/IS1545.lean](../../Veir/InstSimplify/IS1545.lean), [Veir/InstSimplify/IS1551.lean](../../Veir/InstSimplify/IS1551.lean), [Veir/InstSimplify/IS1598.lean](../../Veir/InstSimplify/IS1598.lean), [Veir/InstSimplify/IS1603.lean](../../Veir/InstSimplify/IS1603.lean), [Veir/InstSimplify/IS1608.lean](../../Veir/InstSimplify/IS1608.lean), [Veir/InstSimplify/IS1613.lean](../../Veir/InstSimplify/IS1613.lean), [Veir/InstSimplify/IS1638.lean](../../Veir/InstSimplify/IS1638.lean), [Veir/InstSimplify/IS1643.lean](../../Veir/InstSimplify/IS1643.lean), [Veir/InstSimplify/IS1651.lean](../../Veir/InstSimplify/IS1651.lean), [Veir/InstSimplify/IS1653.lean](../../Veir/InstSimplify/IS1653.lean), [Veir/InstSimplify/IS1682.lean](../../Veir/InstSimplify/IS1682.lean), [Veir/InstSimplify/IS1684.lean](../../Veir/InstSimplify/IS1684.lean), [Veir/InstSimplify/IS1688.lean](../../Veir/InstSimplify/IS1688.lean), [Veir/InstSimplify/IS1690.lean](../../Veir/InstSimplify/IS1690.lean), [Veir/InstSimplify/IS1696.lean](../../Veir/InstSimplify/IS1696.lean), [Veir/InstSimplify/IS1699.lean](../../Veir/InstSimplify/IS1699.lean), [Veir/InstSimplify/IS1717.lean](../../Veir/InstSimplify/IS1717.lean), [Veir/InstSimplify/IS1720.lean](../../Veir/InstSimplify/IS1720.lean), [Veir/InstSimplify/IS1772.lean](../../Veir/InstSimplify/IS1772.lean), [Veir/InstSimplify/IS1774.lean](../../Veir/InstSimplify/IS1774.lean), [Veir/InstSimplify/IS1778.lean](../../Veir/InstSimplify/IS1778.lean), [Veir/InstSimplify/IS1780.lean](../../Veir/InstSimplify/IS1780.lean), [Veir/InstSimplify/IS1786.lean](../../Veir/InstSimplify/IS1786.lean), [Veir/InstSimplify/IS1789.lean](../../Veir/InstSimplify/IS1789.lean).
- **Theorems:** `Veir.InstSimplify.IS1534.valid_or`, `Veir.InstSimplify.IS1539.valid_and`, `Veir.InstSimplify.IS1545.valid_and`, `Veir.InstSimplify.IS1545.valid_or`, `Veir.InstSimplify.IS1551.valid_and`, `Veir.InstSimplify.IS1551.valid_or`, `Veir.InstSimplify.IS1598.valid_and`, `Veir.InstSimplify.IS1598.valid_or`, `Veir.InstSimplify.IS1603.valid_and`, `Veir.InstSimplify.IS1603.valid_or`, `Veir.InstSimplify.IS1608.valid_and`, `Veir.InstSimplify.IS1613.valid_or`, `Veir.InstSimplify.IS1638.valid`, `Veir.InstSimplify.IS1643.valid`, `Veir.InstSimplify.IS1651.valid_and`, `Veir.InstSimplify.IS1651.valid_or`, `Veir.InstSimplify.IS1653.valid_and`, `Veir.InstSimplify.IS1653.valid_or`, `Veir.InstSimplify.IS1682.valid`, `Veir.InstSimplify.IS1684.valid`, `Veir.InstSimplify.IS1688.valid`, `Veir.InstSimplify.IS1690.valid`, `Veir.InstSimplify.IS1696.valid`, `Veir.InstSimplify.IS1699.valid`, `Veir.InstSimplify.IS1717_valid`, `Veir.InstSimplify.IS1720_valid`, `Veir.InstSimplify.IS1772.valid`, `Veir.InstSimplify.IS1774.valid`, `Veir.InstSimplify.IS1778.valid`, `Veir.InstSimplify.IS1780.valid`, `Veir.InstSimplify.IS1786.valid`, `Veir.InstSimplify.IS1789.valid`.
- **Shared implementation:** [IS1534](#is1534), [IS1539](#is1539), [IS1545](#is1545), [IS1551](#is1551), [IS1598](#is1598), [IS1603](#is1603), [IS1608](#is1608), [IS1613](#is1613), [IS1638](#is1638), [IS1643](#is1643), [IS1651](#is1651), [IS1653](#is1653), [IS1717](#is1717), [IS1720](#is1720), [IS1682](#is1682), [IS1684](#is1684), [IS1688](#is1688), [IS1690](#is1690), [IS1696](#is1696), [IS1699](#is1699), [IS1772](#is1772), [IS1774](#is1774), [IS1778](#is1778), [IS1780](#is1780), [IS1786](#is1786), [IS1789](#is1789). This caller is not an additional independent port.
- **Details / missing facilities:** Partial comparison-helper dispatch coverage: cited scalar integer syntactic, constant-range, ctpop, and add/comparison branches are proved. The complete source helper also invokes isKnownNonZero/ValueTracking branches lacking sound analysis certificates and FP comparison branches lacking interpreter semantics. IS1933 additionally folds the returned constant through the stripped cast; no complete contract is claimed for these dispatchers.

<a id="is2143"></a>

## IS2143 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2142–2143](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2142-L2143). Kind: rewrite.
- **Rewrite:** zext(X) & sext(X) --> zext(X) sext(X) & zext(X) --> zext(X); returns `Op0`. Guard: `match(Op0, m_ZExt(m_Value(X))) && match(Op1, m_SExt(m_Specific(X)))`.
- **Matched/replaced opcodes:** `and`, `zext`, `sext`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary source/destination widths and signedness, all source flags and operand orientations; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS2143.lean](../../Veir/InstSimplify/IS2143.lean).
- **Theorems:** `Veir.InstSimplify.IS2143.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with poison refinement and kernel proofs; Boolean cases use the kernel int1_cases theorem.

<a id="is2145"></a>

## IS2145 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2144–2145](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2144-L2145). Kind: rewrite.
- **Rewrite:** zext(X) & sext(X) --> zext(X) sext(X) & zext(X) --> zext(X); returns `Op1`. Guard: `match(Op1, m_ZExt(m_Value(X))) && match(Op0, m_SExt(m_Specific(X)))`.
- **Matched/replaced opcodes:** `and`, `zext`, `sext`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary source/destination widths and signedness, all source flags and operand orientations; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS2145.lean](../../Veir/InstSimplify/IS2145.lean).
- **Theorems:** `Veir.InstSimplify.IS2145.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with poison refinement and kernel proofs; Boolean cases use the kernel int1_cases theorem.

<a id="is2151"></a>

## IS2151 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2150–2151](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2150-L2151). Kind: delegation.
- **Rewrite:** Try some generic simplifications for associative operations.; returns `V`. Guard: `Value *V = simplifyAssociativeBinOp(Instruction::And, Op0, Op1, Q, MaxRecurse)`. Delegates to `simplifyAssociativeBinOp`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Generic recursive dispatch requires certified recursive simplifyBinOp results, source recursion-budget composition, and/or control-flow-sensitive threading. Current Puddle has no reusable proof-bearing recursive simplifier facility; PHI interpretation is additionally absent where applicable.

<a id="is2156"></a>

## IS2156 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2155–2156](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2155-L2156). Kind: delegation.
- **Rewrite:** And distributes over Or.  Try some generic simplifications based on this.; returns `V`. Guard: `Value *V = expandCommutativeBinOp(Instruction::And, Op0, Op1, Instruction::Or, Q, MaxRecurse)`. Delegates to `expandCommutativeBinOp`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Generic recursive dispatch requires certified recursive simplifyBinOp results, source recursion-budget composition, and/or control-flow-sensitive threading. Current Puddle has no reusable proof-bearing recursive simplifier facility; PHI interpretation is additionally absent where applicable.

<a id="is2161"></a>

## IS2161 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2160–2161](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2160-L2161). Kind: delegation.
- **Rewrite:** And distributes over Xor.  Try some generic simplifications based on this.; returns `V`. Guard: `Value *V = expandCommutativeBinOp(Instruction::And, Op0, Op1, Instruction::Xor, Q, MaxRecurse)`. Delegates to `expandCommutativeBinOp`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Generic recursive dispatch requires certified recursive simplifyBinOp results, source recursion-budget composition, and/or control-flow-sensitive threading. Current Puddle has no reusable proof-bearing recursive simplifier facility; PHI interpretation is additionally absent where applicable.

<a id="is2167"></a>

## IS2167 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2164–2167](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2164-L2167). Kind: rewrite.
- **Rewrite:** A & (A && B) -> A && B; returns `Op1`. Guard: `isa<SelectInst>(Op0) || isa<SelectInst>(Op1)` and `Op0->getType()->isIntOrIntVectorTy(1)` and `match(Op1, m_Select(m_Specific(Op0), m_Value(), m_Zero()))`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — type required: integer scalar/vector with the stated bit width.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary source/destination widths and signedness, all source flags and operand orientations; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS2167.lean](../../Veir/InstSimplify/IS2167.lean).
- **Theorems:** `Veir.InstSimplify.IS2167.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with poison refinement and kernel proofs; Boolean cases use the kernel int1_cases theorem.

<a id="is2169"></a>

## IS2169 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2165–2169](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2165-L2169). Kind: rewrite.
- **Rewrite:** A & (A && B) -> A && B; returns `Op0`. Guard: `isa<SelectInst>(Op0) || isa<SelectInst>(Op1)` and `Op0->getType()->isIntOrIntVectorTy(1)` and `match(Op1, m_Select(m_Specific(Op0), m_Value(), m_Zero()))` and `else if match(Op0, m_Select(m_Specific(Op1), m_Value(), m_Zero()))`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — type required: integer scalar/vector with the stated bit width.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary source/destination widths and signedness, all source flags and operand orientations; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS2169.lean](../../Veir/InstSimplify/IS2169.lean).
- **Theorems:** `Veir.InstSimplify.IS2169.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with poison refinement and kernel proofs; Boolean cases use the kernel int1_cases theorem.

<a id="is2176"></a>

## IS2176 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2174–2176](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2174-L2176). Kind: delegation.
- **Rewrite:** If the operation is with the result of a select instruction, check whether operating on either branch of the select always yields the same value.; returns `V`. Guard: `isa<SelectInst>(Op0) || isa<SelectInst>(Op1)` and `Value *V = threadBinOpOverSelect(Instruction::And, Op0, Op1, Q, MaxRecurse)`. Delegates to `threadBinOpOverSelect`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Generic recursive dispatch requires certified recursive simplifyBinOp results, source recursion-budget composition, and/or control-flow-sensitive threading. Current Puddle has no reusable proof-bearing recursive simplifier facility; PHI interpretation is additionally absent where applicable.

<a id="is2184"></a>

## IS2184 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2182–2184](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2182-L2184). Kind: delegation.
- **Rewrite:** If the operation is with the result of a phi instruction, check whether operating on all incoming values of the phi always yields the same value.; returns `V`. Guard: `isa<PHINode>(Op0) || isa<PHINode>(Op1)` and `Value *V = threadBinOpOverPHI(Instruction::And, Op0, Op1, Q, MaxRecurse)`. Delegates to `threadBinOpOverPHI`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Generic recursive dispatch requires certified recursive simplifyBinOp results, source recursion-budget composition, and/or control-flow-sensitive threading. Current Puddle has no reusable proof-bearing recursive simplifier facility; PHI interpretation is additionally absent where applicable.

<a id="is2213"></a>

## IS2213 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2210–2213](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2210-L2213). Kind: rewrite.
- **Rewrite:** If the mask is extracting all bits from X or Y as is, we can skip this AND op.; returns `Y`. Guard: `Q.IIQ.UseInstrInfo && match(Op1, m_APInt(Mask)) && match(Op0, m_c_Or(m_CombineAnd(m_NUWShl(m_Value(X), m_APInt(ShAmt)), m_Value(XShifted)), m_Value(Y)))` and `EffWidthY <= ShftCnt` and `EffBitsY.isSubsetOf(*Mask) && !EffBitsX.intersects(*Mask)`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-bits/sign-bit/range facts computed from operands; instruction property required: no-unsigned-wrap operator flag; instruction property required: InstrInfoQuery operator flags; instruction property required: operator flags via InstrInfoQuery.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is2215"></a>

## IS2215 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2212–2215](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2212-L2215). Kind: rewrite.
- **Rewrite:** If the mask is extracting all bits from X or Y as is, we can skip this AND op.; returns `XShifted`. Guard: `Q.IIQ.UseInstrInfo && match(Op1, m_APInt(Mask)) && match(Op0, m_c_Or(m_CombineAnd(m_NUWShl(m_Value(X), m_APInt(ShAmt)), m_Value(XShifted)), m_Value(Y)))` and `EffWidthY <= ShftCnt` and `EffBitsX.isSubsetOf(*Mask) && !EffBitsY.intersects(*Mask)`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-bits/sign-bit/range facts computed from operands; instruction property required: no-unsigned-wrap operator flag; instruction property required: InstrInfoQuery operator flags; instruction property required: operator flags via InstrInfoQuery.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is2226"></a>

## IS2226 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2225–2226](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2225-L2226). Kind: rewrite.
- **Rewrite:** ((X | Y) ^ X ) & ((X | Y) ^ Y) --> 0 ((X | Y) ^ Y ) & ((X | Y) ^ X) --> 0; returns `Constant::getNullValue(Op0->getType())`. Guard: `match(Op0, m_c_Xor(m_Value(X), m_CombineAnd(m_BinOp(Or), m_c_Or(m_Deferred(X), m_Value(Y))))) && match(Op1, m_c_Xor(m_Specific(Or), m_Specific(Y)))`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2226.lean](../../Veir/InstSimplify/IS2226.lean).
- **Theorems:** `Veir.InstSimplify.IS2226.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2233"></a>

## IS2233 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2232–2233](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2232-L2233). Kind: rewrite.
- **Rewrite:** (A ^ C) & (A ^ ~C) -> 0; returns `Constant::getNullValue(Op0->getType())`. Guard: `match(Op0, m_Xor(m_Value(A), m_APInt(C1))) && match(Op1, m_Xor(m_Specific(A), m_SpecificInt(~*C1)))`.
- **Matched/replaced opcodes:** `and`, `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and instruction flags; no vectors.
- **Lean:** [Veir/InstSimplify/IS2233.lean](../../Veir/InstSimplify/IS2233.lean).
- **Theorems:** `Veir.InstSimplify.IS2233.valid`.
- **Details / missing facilities:** Compiled width-parametric LLVM scalar refinement proof, preserving poison and all source instruction flags.

<a id="is2239"></a>

## IS2239 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2236–2239](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2236-L2239). Kind: rewrite.
- **Rewrite:** If Op0 is true implies Op1 is true, then Op0 is a subset of Op1.; returns `Op0`. Guard: `Op0->getType()->isIntOrIntVectorTy(1)` and `std::optional<bool> Implied = isImpliedCondition(Op0, Op1, Q.DL)` and `*Implied == true`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: boolean implication/disjointness or dominating-condition analysis; type required: integer scalar/vector with the stated bit width.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is2242"></a>

## IS2242 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2239–2242](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2239-L2242). Kind: rewrite.
- **Rewrite:** If Op0 is true implies Op1 is false, then they are not true together.; returns `ConstantInt::getFalse(Op0->getType())`. Guard: `Op0->getType()->isIntOrIntVectorTy(1)` and `std::optional<bool> Implied = isImpliedCondition(Op0, Op1, Q.DL)` and `*Implied == false`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: boolean implication/disjointness or dominating-condition analysis; type required: integer scalar/vector with the stated bit width.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is2247"></a>

## IS2247 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2244–2247](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2244-L2247). Kind: rewrite.
- **Rewrite:** If Op1 is true implies Op0 is true, then Op1 is a subset of Op0.; returns `Op1`. Guard: `Op0->getType()->isIntOrIntVectorTy(1)` and `std::optional<bool> Implied = isImpliedCondition(Op1, Op0, Q.DL)` and `*Implied`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: boolean implication/disjointness or dominating-condition analysis; type required: integer scalar/vector with the stated bit width.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is2250"></a>

## IS2250 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2247–2250](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2247-L2250). Kind: rewrite.
- **Rewrite:** If Op1 is true implies Op0 is false, then they are not true together.; returns `ConstantInt::getFalse(Op1->getType())`. Guard: `Op0->getType()->isIntOrIntVectorTy(1)` and `std::optional<bool> Implied = isImpliedCondition(Op1, Op0, Q.DL)` and `!*Implied`.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: boolean implication/disjointness or dominating-condition analysis; type required: integer scalar/vector with the stated bit width.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is2255"></a>

## IS2255 — `simplifyAndInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2254–2255](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2254-L2255). Kind: delegation.
- **Rewrite:** At the top recursion level, return Op1 for and when a dominating condition implies Op0 == Op1.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Requires a proof-bearing certificate for isImpliedByDomCondition(ICMP_EQ, Op0, Op1, Q.CtxI, Q.DL). Current Puddle validity has no control-flow/dominating-equality certificate interface; inspectOperation facts are erased. The scalar result under a certified equality is elementary; the missing facility is the contextual equality evidence.

<a id="is2271"></a>

## IS2271 — `simplifyOrLogic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2270–2271](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2270-L2271). Kind: rewrite.
- **Rewrite:** X | ~X --> -1; returns `ConstantInt::getAllOnesValue(Ty)`. Guard: `match(Y, m_Not(m_Specific(X)))`.
- **Matched/replaced opcodes:** `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2271.lean](../../Veir/InstSimplify/IS2271.lean).
- **Theorems:** `Veir.InstSimplify.IS2271.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2275"></a>

## IS2275 — `simplifyOrLogic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2274–2275](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2274-L2275). Kind: rewrite.
- **Rewrite:** X | ~(X & ?) = -1; returns `ConstantInt::getAllOnesValue(Ty)`. Guard: `match(Y, m_Not(m_c_And(m_Specific(X), m_Value())))`.
- **Matched/replaced opcodes:** `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2275.lean](../../Veir/InstSimplify/IS2275.lean).
- **Theorems:** `Veir.InstSimplify.IS2275.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2279"></a>

## IS2279 — `simplifyOrLogic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2278–2279](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2278-L2279). Kind: rewrite.
- **Rewrite:** X | (X & ?) --> X; returns `X`. Guard: `match(Y, m_c_And(m_Specific(X), m_Value()))`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2279.lean](../../Veir/InstSimplify/IS2279.lean).
- **Theorems:** `Veir.InstSimplify.IS2279.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2287"></a>

## IS2287 — `simplifyOrLogic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2286–2287](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2286-L2287). Kind: rewrite.
- **Rewrite:** (A ^ B) | (A | B) --> A | B (A ^ B) | (B | A) --> B | A; returns `Y`. Guard: `match(X, m_Xor(m_Value(A), m_Value(B))) && match(Y, m_c_Or(m_Specific(A), m_Specific(B)))`.
- **Matched/replaced opcodes:** `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2287.lean](../../Veir/InstSimplify/IS2287.lean).
- **Theorems:** `Veir.InstSimplify.IS2287.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2293"></a>

## IS2293 — `simplifyOrLogic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2292–2293](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2292-L2293). Kind: rewrite.
- **Rewrite:** ~(A ^ B) | (A | B) --> -1 ~(A ^ B) | (B | A) --> -1; returns `ConstantInt::getAllOnesValue(Ty)`. Guard: `match(X, m_Not(m_Xor(m_Value(A), m_Value(B)))) && match(Y, m_c_Or(m_Specific(A), m_Specific(B)))`.
- **Matched/replaced opcodes:** `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2293.lean](../../Veir/InstSimplify/IS2293.lean).
- **Theorems:** `Veir.InstSimplify.IS2293.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2301"></a>

## IS2301 — `simplifyOrLogic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2300–2301](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2300-L2301). Kind: rewrite.
- **Rewrite:** (A & ~B) | (A ^ B) --> A ^ B (~B & A) | (A ^ B) --> A ^ B (A & ~B) | (B ^ A) --> B ^ A (~B & A) | (B ^ A) --> B ^ A; returns `Y`. Guard: `match(X, m_c_And(m_Value(A), m_Not(m_Value(B)))) && match(Y, m_c_Xor(m_Specific(A), m_Specific(B)))`.
- **Matched/replaced opcodes:** `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2301.lean](../../Veir/InstSimplify/IS2301.lean).
- **Theorems:** `Veir.InstSimplify.IS2301.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2309"></a>

## IS2309 — `simplifyOrLogic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2308–2309](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2308-L2309). Kind: rewrite.
- **Rewrite:** (~A ^ B) | (A & B) --> ~A ^ B (B ^ ~A) | (A & B) --> B ^ ~A (~A ^ B) | (B & A) --> ~A ^ B (B ^ ~A) | (B & A) --> B ^ ~A; returns `X`. Guard: `match(X, m_c_Xor(m_Not(m_Value(A)), m_Value(B))) && match(Y, m_c_And(m_Specific(A), m_Specific(B)))`.
- **Matched/replaced opcodes:** `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2309.lean](../../Veir/InstSimplify/IS2309.lean).
- **Theorems:** `Veir.InstSimplify.IS2309.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2317"></a>

## IS2317 — `simplifyOrLogic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2316–2317](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2316-L2317). Kind: rewrite.
- **Rewrite:** (~A | B) | (A ^ B) --> -1 (~A | B) | (B ^ A) --> -1 (B | ~A) | (A ^ B) --> -1 (B | ~A) | (B ^ A) --> -1; returns `ConstantInt::getAllOnesValue(Ty)`. Guard: `match(X, m_c_Or(m_Not(m_Value(A)), m_Value(B))) && match(Y, m_c_Xor(m_Specific(A), m_Specific(B)))`.
- **Matched/replaced opcodes:** `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2317.lean](../../Veir/InstSimplify/IS2317.lean).
- **Theorems:** `Veir.InstSimplify.IS2317.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2327"></a>

## IS2327 — `simplifyOrLogic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2326–2327](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2326-L2327). Kind: rewrite.
- **Rewrite:** (~A & B) | ~(A | B) --> ~A (~A & B) | ~(B | A) --> ~A (B & ~A) | ~(A | B) --> ~A (B & ~A) | ~(B | A) --> ~A; returns `NotA`. Guard: `match(X, m_c_And(m_CombineAnd(m_Value(NotA), m_Not(m_Value(A))), m_Value(B))) && match(Y, m_Not(m_c_Or(m_Specific(A), m_Specific(B))))`.
- **Matched/replaced opcodes:** `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2327.lean](../../Veir/InstSimplify/IS2327.lean).
- **Theorems:** `Veir.InstSimplify.IS2327.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2334"></a>

## IS2334 — `simplifyOrLogic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2333–2334](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2333-L2334). Kind: rewrite.
- **Rewrite:** The same is true of Logical And TODO: This could share the logic of the version above if there was a version of LogicalAnd that allowed more than just i1 types.; returns `NotA`. Guard: `match(X, m_c_LogicalAnd(m_CombineAnd(m_Value(NotA), m_Not(m_Value(A))), m_Value(B))) && match(Y, m_Not(m_c_LogicalOr(m_Specific(A), m_Specific(B))))`.
- **Matched/replaced opcodes:** `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM i1 integers; each logical operation may be bitwise or select, independently; all source operand commutations, root disjoint flags, and normalized zero/allones constants. Arbitrary-width bitwise form is covered by IS2327; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS2334.lean](../../Veir/InstSimplify/IS2334.lean).
- **Theorems:** `Veir.InstSimplify.IS2334.valid`.
- **Details / missing facilities:** Compiled complete scalar logical source family with kernel int1_cases proof, including mixed select/bitwise forms and all128 graph variants. No extra zero constant is required when logical AND is bitwise.

<a id="is2342"></a>

## IS2342 — `simplifyOrLogic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2341–2342](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2341-L2342). Kind: rewrite.
- **Rewrite:** ~(A ^ B) | (A & B) --> ~(A ^ B) ~(A ^ B) | (B & A) --> ~(A ^ B); returns `NotAB`. Guard: `match(X, m_CombineAnd(m_Not(m_Xor(m_Value(A), m_Value(B))), m_Value(NotAB))) && match(Y, m_c_And(m_Specific(A), m_Specific(B)))`.
- **Matched/replaced opcodes:** `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2342.lean](../../Veir/InstSimplify/IS2342.lean).
- **Theorems:** `Veir.InstSimplify.IS2342.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2349"></a>

## IS2349 — `simplifyOrLogic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2348–2349](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2348-L2349). Kind: rewrite.
- **Rewrite:** ~(A & B) | (A ^ B) --> ~(A & B) ~(A & B) | (B ^ A) --> ~(A & B); returns `NotAB`. Guard: `match(X, m_CombineAnd(m_Not(m_And(m_Value(A), m_Value(B))), m_Value(NotAB))) && match(Y, m_c_Xor(m_Specific(A), m_Specific(B)))`.
- **Matched/replaced opcodes:** `or`, `and`, `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2349.lean](../../Veir/InstSimplify/IS2349.lean).
- **Theorems:** `Veir.InstSimplify.IS2349.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2359"></a>

## IS2359 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2358–2359](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2358-L2359). Kind: delegation.
- **Rewrite:** Given operands for an Or, see if we can fold the result. If not, this returns null.; returns `C`. Guard: `Constant *C = foldOrCommuteConstant(Instruction::Or, Op0, Op1, Q)`. Delegates to `foldOrCommuteConstant`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integer constant operands, arbitrary width and instruction properties; no FP/vector/undef.
- **Lean:** [Veir/InstSimplify/IS0582.lean](../../Veir/InstSimplify/IS0582.lean).
- **Theorems:** `Veir.InstSimplify.IS0582.pattern_or_valid`.
- **Shared implementation:** [IS0582](#is0582). This caller is not an additional independent port.
- **Details / missing facilities:** Successful constant-fold delegation covered by the certified scalar LLVM constant-fold pattern IS0582 for this opcode. Commutation itself returns no rewrite.

<a id="is2363"></a>

## IS2363 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2362–2363](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2362-L2363). Kind: rewrite.
- **Rewrite:** X | poison -> poison; returns `Op1`. Guard: `isa<PoisonValue>(Op1)`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM poison propagation semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2363.lean](../../Veir/InstSimplify/IS2363.lean).
- **Theorems:** `Veir.InstSimplify.IS2363.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2369"></a>

## IS2369 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2368–2369](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2368-L2369). Kind: rewrite.
- **Rewrite:** `or X,all_ones -> all_ones`, with either operand order. LLVM constructs a complete all-ones result instead of reusing possible undef vector lanes. The scalar undef alternative is IS2369u.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM undef nondeterministic semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary width/signedness and or.disjoint flag, all-ones constant branch with every operand orientation. Undef branch unmodeled; no vectors.
- **Lean:** [Veir/InstSimplify/IS2369.lean](../../Veir/InstSimplify/IS2369.lean).
- **Theorems:** `Veir.InstSimplify.IS2369.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2369u"></a>

## IS2369u — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2368–2369](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2368-L2369). Kind: rewrite.
- **Rewrite:** `or X,undef -> all_ones`, with either operand order.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM undef nondeterministic semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Details / missing facilities:** LLVM undef is not represented by LLVM.Int and mlir__undef has no successful interpretation in Llvm.interpretOp'. Poison is a distinct value and cannot substitute for undef. No vacuous Pattern.Valid proof from the missing interpreter case is claimed.

<a id="is2374"></a>

## IS2374 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2373–2374](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2373-L2374). Kind: rewrite.
- **Rewrite:** X | X = X X | 0 = X; returns `Op0`. Guard: `Op0 == Op1 || match(Op1, m_Zero())`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2374.lean](../../Veir/InstSimplify/IS2374.lean).
- **Theorems:** `Veir.InstSimplify.IS2374.valid`, `Veir.InstSimplify.IS2374.Zero.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2377"></a>

## IS2377 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2376–2377](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2376-L2377). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyOrLogic for the enclosing or operation.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers with arbitrary widths and flags; logical-select cases require i1 as in the source; every inner and outer source commutation is parameterized by the callee patterns. Vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS2271.lean](../../Veir/InstSimplify/IS2271.lean), [Veir/InstSimplify/IS2275.lean](../../Veir/InstSimplify/IS2275.lean), [Veir/InstSimplify/IS2279.lean](../../Veir/InstSimplify/IS2279.lean), [Veir/InstSimplify/IS2287.lean](../../Veir/InstSimplify/IS2287.lean), [Veir/InstSimplify/IS2293.lean](../../Veir/InstSimplify/IS2293.lean), [Veir/InstSimplify/IS2301.lean](../../Veir/InstSimplify/IS2301.lean), [Veir/InstSimplify/IS2309.lean](../../Veir/InstSimplify/IS2309.lean), [Veir/InstSimplify/IS2317.lean](../../Veir/InstSimplify/IS2317.lean), [Veir/InstSimplify/IS2327.lean](../../Veir/InstSimplify/IS2327.lean), [Veir/InstSimplify/IS2334.lean](../../Veir/InstSimplify/IS2334.lean), [Veir/InstSimplify/IS2342.lean](../../Veir/InstSimplify/IS2342.lean), [Veir/InstSimplify/IS2349.lean](../../Veir/InstSimplify/IS2349.lean).
- **Theorems:** `Veir.InstSimplify.IS2271.valid`, `Veir.InstSimplify.IS2275.valid`, `Veir.InstSimplify.IS2279.valid`, `Veir.InstSimplify.IS2287.valid`, `Veir.InstSimplify.IS2293.valid`, `Veir.InstSimplify.IS2301.valid`, `Veir.InstSimplify.IS2309.valid`, `Veir.InstSimplify.IS2317.valid`, `Veir.InstSimplify.IS2327.valid`, `Veir.InstSimplify.IS2334.valid`, `Veir.InstSimplify.IS2342.valid`, `Veir.InstSimplify.IS2349.valid`.
- **Shared implementation:** [IS2271](#is2271), [IS2275](#is2275), [IS2279](#is2279), [IS2287](#is2287), [IS2293](#is2293), [IS2301](#is2301), [IS2309](#is2309), [IS2317](#is2317), [IS2327](#is2327), [IS2334](#is2334), [IS2342](#is2342), [IS2349](#is2349). This caller is not an additional independent port.
- **Details / missing facilities:** Pure simplifyOrLogic dispatch: all12 scalar callee families are proved, including logical selects and both root operand orders. No independent rewrite theorem is counted.

<a id="is2379"></a>

## IS2379 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2378–2379](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2378-L2379). Kind: delegation.
- **Rewrite:** Return the successful result of simplifyOrLogic (commuted) for the enclosing or operation.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers with arbitrary widths and flags; logical-select cases require i1 as in the source; every inner and outer source commutation is parameterized by the callee patterns. Vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS2271.lean](../../Veir/InstSimplify/IS2271.lean), [Veir/InstSimplify/IS2275.lean](../../Veir/InstSimplify/IS2275.lean), [Veir/InstSimplify/IS2279.lean](../../Veir/InstSimplify/IS2279.lean), [Veir/InstSimplify/IS2287.lean](../../Veir/InstSimplify/IS2287.lean), [Veir/InstSimplify/IS2293.lean](../../Veir/InstSimplify/IS2293.lean), [Veir/InstSimplify/IS2301.lean](../../Veir/InstSimplify/IS2301.lean), [Veir/InstSimplify/IS2309.lean](../../Veir/InstSimplify/IS2309.lean), [Veir/InstSimplify/IS2317.lean](../../Veir/InstSimplify/IS2317.lean), [Veir/InstSimplify/IS2327.lean](../../Veir/InstSimplify/IS2327.lean), [Veir/InstSimplify/IS2334.lean](../../Veir/InstSimplify/IS2334.lean), [Veir/InstSimplify/IS2342.lean](../../Veir/InstSimplify/IS2342.lean), [Veir/InstSimplify/IS2349.lean](../../Veir/InstSimplify/IS2349.lean).
- **Theorems:** `Veir.InstSimplify.IS2271.valid`, `Veir.InstSimplify.IS2275.valid`, `Veir.InstSimplify.IS2279.valid`, `Veir.InstSimplify.IS2287.valid`, `Veir.InstSimplify.IS2293.valid`, `Veir.InstSimplify.IS2301.valid`, `Veir.InstSimplify.IS2309.valid`, `Veir.InstSimplify.IS2317.valid`, `Veir.InstSimplify.IS2327.valid`, `Veir.InstSimplify.IS2334.valid`, `Veir.InstSimplify.IS2342.valid`, `Veir.InstSimplify.IS2349.valid`.
- **Shared implementation:** [IS2271](#is2271), [IS2275](#is2275), [IS2279](#is2279), [IS2287](#is2287), [IS2293](#is2293), [IS2301](#is2301), [IS2309](#is2309), [IS2317](#is2317), [IS2327](#is2327), [IS2334](#is2334), [IS2342](#is2342), [IS2349](#is2349). This caller is not an additional independent port.
- **Details / missing facilities:** Pure simplifyOrLogic dispatch: all12 scalar callee families are proved, including logical selects and both root operand orders. No independent rewrite theorem is counted.

<a id="is2382"></a>

## IS2382 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2381–2382](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2381-L2382). Kind: delegation.
- **Rewrite:** X | X = X X | 0 = X; returns `V`. Guard: `Value *V = simplifyLogicOfAddSub(Op0, Op1, Instruction::Or)`. Delegates to `simplifyLogicOfAddSub`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths and constant payload spellings; no vectors.
- **Lean:** [Veir/InstSimplify/IS2011.lean](../../Veir/InstSimplify/IS2011.lean).
- **Theorems:** `Veir.InstSimplify.IS2011.valid_or`.
- **Shared implementation:** [IS2011](#is2011). This caller is not an additional independent port.
- **Details / missing facilities:** Shared add/sub logic helper dispatch covered by the corresponding opcode pattern, including root commutation and all nsw/nuw/disjoint flags.

<a id="is2397"></a>

## IS2397 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2395–2397](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2395-L2397). Kind: rewrite.
- **Rewrite:** Rotated -1 is still -1: (-1 << X) | (-1 >> (C - X)) --> -1 (-1 >> X) | (-1 << (C - X)) --> -1 ...with C <= bitwidth (and commuted variants).; returns `ConstantInt::getAllOnesValue(X->getType())`. Guard: `(match(Op0, m_Shl(m_AllOnes(), m_Value(X))) && match(Op1, m_LShr(m_AllOnes(), m_Value(Y)))) || (match(Op1, m_Shl(m_AllOnes(), m_Value(X))) && match(Op0, m_LShr(m_AllOnes(), m_Value(Y))))` and `(match(X, m_Sub(m_APInt(C), m_Specific(Y))) || match(Y, m_Sub(m_APInt(C), m_Specific(X)))) && C->ule(X->getType()->getScalarSizeInBits())`.
- **Matched/replaced opcodes:** `or`, `sub`, `shl`, `lshr`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and signedness; all source flags, normalized APInt constant spellings, and source operand orientations. Vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS2397.lean](../../Veir/InstSimplify/IS2397.lean).
- **Theorems:** `Veir.InstSimplify.IS2397.valid`.
- **Details / missing facilities:** Both subtraction locations and both root operand orders proved for arbitrary shift/subtraction/disjoint flags. Kernel per-bit proof derives X+Y <= width from the defined shift bounds and modular C-X relation; poison branches refine the allones result.

<a id="is2406"></a>

## IS2406 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2405–2406](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2405-L2406). Kind: rewrite.
- **Rewrite:** zext(X) | sext(X) --> sext(X) sext(X) | zext(X) --> sext(X); returns `Op1`. Guard: `match(Op0, m_ZExt(m_Value(X))) && match(Op1, m_SExt(m_Specific(X)))`.
- **Matched/replaced opcodes:** `or`, `zext`, `sext`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary source/destination widths and signedness, all source flags and operand orientations; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS2406.lean](../../Veir/InstSimplify/IS2406.lean).
- **Theorems:** `Veir.InstSimplify.IS2406.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with poison refinement and kernel proofs; Boolean cases use the kernel int1_cases theorem.

<a id="is2408"></a>

## IS2408 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2407–2408](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2407-L2408). Kind: rewrite.
- **Rewrite:** zext(X) | sext(X) --> sext(X) sext(X) | zext(X) --> sext(X); returns `Op0`. Guard: `match(Op1, m_ZExt(m_Value(X))) && match(Op0, m_SExt(m_Specific(X)))`.
- **Matched/replaced opcodes:** `or`, `zext`, `sext`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary source/destination widths and signedness, all source flags and operand orientations; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS2408.lean](../../Veir/InstSimplify/IS2408.lean).
- **Theorems:** `Veir.InstSimplify.IS2408.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with poison refinement and kernel proofs; Boolean cases use the kernel int1_cases theorem.

<a id="is2419"></a>

## IS2419 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2418–2419](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2418-L2419). Kind: rewrite.
- **Rewrite:** (fshl X, ?, Y) | (shl X, Y) --> fshl X, ?, Y (shl X, Y) | (fshl X, ?, Y) --> fshl X, ?, Y; returns `Op0`. Guard: `match(Op0, m_Intrinsic<Intrinsic::fshl>(m_Value(X), m_Value(), m_Value(Y))) && match(Op1, m_Shl(m_Specific(X), m_Specific(Y)))`.
- **Matched/replaced opcodes:** `or`, `shl`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths and signedness, all source shift and OR flags; parameterized root OR commutation.
- **Lean:** [Veir/InstSimplify/IS2419.lean](../../Veir/InstSimplify/IS2419.lean).
- **Theorems:** `Veir.InstSimplify.IS2419_valid`.
- **Details / missing facilities:** Own LLVM funnel/shift/OR pattern and kernel-checked validity, returning the exact matched funnel result.

<a id="is2423"></a>

## IS2423 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2422–2423](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2422-L2423). Kind: rewrite.
- **Rewrite:** (fshl X, ?, Y) | (shl X, Y) --> fshl X, ?, Y (shl X, Y) | (fshl X, ?, Y) --> fshl X, ?, Y; returns `Op1`. Guard: `match(Op1, m_Intrinsic<Intrinsic::fshl>(m_Value(X), m_Value(), m_Value(Y))) && match(Op0, m_Shl(m_Specific(X), m_Specific(Y)))`.
- **Matched/replaced opcodes:** `or`, `shl`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths and signedness, all source shift and OR flags; parameterized root OR commutation.
- **Lean:** [Veir/InstSimplify/IS2423.lean](../../Veir/InstSimplify/IS2423.lean).
- **Theorems:** `Veir.InstSimplify.IS2423_valid`.
- **Shared implementation:** [IS2419](#is2419). This caller is not an additional independent port.
- **Details / missing facilities:** Own LLVM funnel/shift/OR pattern and kernel-checked validity, returning the exact matched funnel result.

<a id="is2430"></a>

## IS2430 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2429–2430](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2429-L2430). Kind: rewrite.
- **Rewrite:** (fshr ?, X, Y) | (lshr X, Y) --> fshr ?, X, Y (lshr X, Y) | (fshr ?, X, Y) --> fshr ?, X, Y; returns `Op0`. Guard: `match(Op0, m_Intrinsic<Intrinsic::fshr>(m_Value(), m_Value(X), m_Value(Y))) && match(Op1, m_LShr(m_Specific(X), m_Specific(Y)))`.
- **Matched/replaced opcodes:** `or`, `lshr`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths and signedness, all source shift and OR flags; parameterized root OR commutation.
- **Lean:** [Veir/InstSimplify/IS2430.lean](../../Veir/InstSimplify/IS2430.lean).
- **Theorems:** `Veir.InstSimplify.IS2430_valid`.
- **Details / missing facilities:** Own LLVM funnel/shift/OR pattern and kernel-checked validity, returning the exact matched funnel result.

<a id="is2434"></a>

## IS2434 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2433–2434](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2433-L2434). Kind: rewrite.
- **Rewrite:** (fshr ?, X, Y) | (lshr X, Y) --> fshr ?, X, Y (lshr X, Y) | (fshr ?, X, Y) --> fshr ?, X, Y; returns `Op1`. Guard: `match(Op1, m_Intrinsic<Intrinsic::fshr>(m_Value(), m_Value(X), m_Value(Y))) && match(Op0, m_LShr(m_Specific(X), m_Specific(Y)))`.
- **Matched/replaced opcodes:** `or`, `lshr`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths and signedness, all source shift and OR flags; parameterized root OR commutation.
- **Lean:** [Veir/InstSimplify/IS2434.lean](../../Veir/InstSimplify/IS2434.lean).
- **Theorems:** `Veir.InstSimplify.IS2434_valid`.
- **Shared implementation:** [IS2430](#is2430). This caller is not an additional independent port.
- **Details / missing facilities:** Own LLVM funnel/shift/OR pattern and kernel-checked validity, returning the exact matched funnel result.

<a id="is2438"></a>

## IS2438 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2437–2438](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2437-L2438). Kind: delegation.
- **Rewrite:** Return a successful simplifyAndOrWithICmpEq result for OR: simplify the other operand under the equality represented by the ICmp, then choose the absorber, original ICmp, or other operand according to the predicate and result.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Shared implementation:** [IS1965](#is1965), [IS1967](#is1967), [IS1975](#is1975), [IS1985](#is1985), [IS1989](#is1989). This caller is not an additional independent port.
- **Details / missing facilities:** Delegates to contextual equality replacement helper (IS1965–IS1989): missing proof-bearing recursive simplifyWithOpReplaced and contextual poison-refinement composition contract.

<a id="is2441"></a>

## IS2441 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2440–2441](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2440-L2441). Kind: delegation.
- **Rewrite:** Return a successful simplifyAndOrWithICmpEq result for OR with operands commuted: simplify the other operand under the equality represented by the ICmp, then choose the absorber, original ICmp, or other operand according to the predicate and result.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Shared implementation:** [IS1965](#is1965), [IS1967](#is1967), [IS1975](#is1975), [IS1985](#is1985), [IS1989](#is1989). This caller is not an additional independent port.
- **Details / missing facilities:** Delegates to contextual equality replacement helper (IS1965–IS1989): missing proof-bearing recursive simplifyWithOpReplaced and contextual poison-refinement composition contract.

<a id="is2444"></a>

## IS2444 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2443–2444](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2443-L2444). Kind: delegation.
- **Rewrite:** returns `V`. Guard: `Value *V = simplifyAndOrOfCmps(Q, Op0, Op1, false)`. Delegates to `simplifyAndOrOfCmps`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integer callee patterns, arbitrary widths and source flags; see each callee domain for exact predicates and operand variants.
- **Lean:** [Veir/InstSimplify/IS1534.lean](../../Veir/InstSimplify/IS1534.lean), [Veir/InstSimplify/IS1539.lean](../../Veir/InstSimplify/IS1539.lean), [Veir/InstSimplify/IS1545.lean](../../Veir/InstSimplify/IS1545.lean), [Veir/InstSimplify/IS1551.lean](../../Veir/InstSimplify/IS1551.lean), [Veir/InstSimplify/IS1598.lean](../../Veir/InstSimplify/IS1598.lean), [Veir/InstSimplify/IS1603.lean](../../Veir/InstSimplify/IS1603.lean), [Veir/InstSimplify/IS1608.lean](../../Veir/InstSimplify/IS1608.lean), [Veir/InstSimplify/IS1613.lean](../../Veir/InstSimplify/IS1613.lean), [Veir/InstSimplify/IS1638.lean](../../Veir/InstSimplify/IS1638.lean), [Veir/InstSimplify/IS1643.lean](../../Veir/InstSimplify/IS1643.lean), [Veir/InstSimplify/IS1651.lean](../../Veir/InstSimplify/IS1651.lean), [Veir/InstSimplify/IS1653.lean](../../Veir/InstSimplify/IS1653.lean), [Veir/InstSimplify/IS1682.lean](../../Veir/InstSimplify/IS1682.lean), [Veir/InstSimplify/IS1684.lean](../../Veir/InstSimplify/IS1684.lean), [Veir/InstSimplify/IS1688.lean](../../Veir/InstSimplify/IS1688.lean), [Veir/InstSimplify/IS1690.lean](../../Veir/InstSimplify/IS1690.lean), [Veir/InstSimplify/IS1696.lean](../../Veir/InstSimplify/IS1696.lean), [Veir/InstSimplify/IS1699.lean](../../Veir/InstSimplify/IS1699.lean), [Veir/InstSimplify/IS1717.lean](../../Veir/InstSimplify/IS1717.lean), [Veir/InstSimplify/IS1720.lean](../../Veir/InstSimplify/IS1720.lean), [Veir/InstSimplify/IS1772.lean](../../Veir/InstSimplify/IS1772.lean), [Veir/InstSimplify/IS1774.lean](../../Veir/InstSimplify/IS1774.lean), [Veir/InstSimplify/IS1778.lean](../../Veir/InstSimplify/IS1778.lean), [Veir/InstSimplify/IS1780.lean](../../Veir/InstSimplify/IS1780.lean), [Veir/InstSimplify/IS1786.lean](../../Veir/InstSimplify/IS1786.lean), [Veir/InstSimplify/IS1789.lean](../../Veir/InstSimplify/IS1789.lean).
- **Theorems:** `Veir.InstSimplify.IS1534.valid_or`, `Veir.InstSimplify.IS1539.valid_and`, `Veir.InstSimplify.IS1545.valid_and`, `Veir.InstSimplify.IS1545.valid_or`, `Veir.InstSimplify.IS1551.valid_and`, `Veir.InstSimplify.IS1551.valid_or`, `Veir.InstSimplify.IS1598.valid_and`, `Veir.InstSimplify.IS1598.valid_or`, `Veir.InstSimplify.IS1603.valid_and`, `Veir.InstSimplify.IS1603.valid_or`, `Veir.InstSimplify.IS1608.valid_and`, `Veir.InstSimplify.IS1613.valid_or`, `Veir.InstSimplify.IS1638.valid`, `Veir.InstSimplify.IS1643.valid`, `Veir.InstSimplify.IS1651.valid_and`, `Veir.InstSimplify.IS1651.valid_or`, `Veir.InstSimplify.IS1653.valid_and`, `Veir.InstSimplify.IS1653.valid_or`, `Veir.InstSimplify.IS1682.valid`, `Veir.InstSimplify.IS1684.valid`, `Veir.InstSimplify.IS1688.valid`, `Veir.InstSimplify.IS1690.valid`, `Veir.InstSimplify.IS1696.valid`, `Veir.InstSimplify.IS1699.valid`, `Veir.InstSimplify.IS1717_valid`, `Veir.InstSimplify.IS1720_valid`, `Veir.InstSimplify.IS1772.valid`, `Veir.InstSimplify.IS1774.valid`, `Veir.InstSimplify.IS1778.valid`, `Veir.InstSimplify.IS1780.valid`, `Veir.InstSimplify.IS1786.valid`, `Veir.InstSimplify.IS1789.valid`.
- **Shared implementation:** [IS1534](#is1534), [IS1539](#is1539), [IS1545](#is1545), [IS1551](#is1551), [IS1598](#is1598), [IS1603](#is1603), [IS1608](#is1608), [IS1613](#is1613), [IS1638](#is1638), [IS1643](#is1643), [IS1651](#is1651), [IS1653](#is1653), [IS1717](#is1717), [IS1720](#is1720), [IS1682](#is1682), [IS1684](#is1684), [IS1688](#is1688), [IS1690](#is1690), [IS1696](#is1696), [IS1699](#is1699), [IS1772](#is1772), [IS1774](#is1774), [IS1778](#is1778), [IS1780](#is1780), [IS1786](#is1786), [IS1789](#is1789). This caller is not an additional independent port.
- **Details / missing facilities:** Partial comparison-helper dispatch coverage: cited scalar integer syntactic, constant-range, ctpop, and add/comparison branches are proved. The complete source helper also invokes isKnownNonZero/ValueTracking branches lacking sound analysis certificates and FP comparison branches lacking interpreter semantics. IS1933 additionally folds the returned constant through the stripped cast; no complete contract is claimed for these dispatchers.

<a id="is2450"></a>

## IS2450 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2449–2450](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2449-L2450). Kind: delegation.
- **Rewrite:** If we have a multiplication overflow check that is being 'and'ed with a check that one of the multipliers is not zero, we can omit the 'and', and only keep the overflow check.; returns `Op1`. Guard: `isCheckForZeroAndMulWithOverflow(Op0, Op1, false)`. Delegates to `simplifyAndOrOfCmps`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — isCheckForZeroAndMulWithOverflow, not simplifyAndOrOfCmps; draft metadata corrected against source..
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Requires isCheckForZeroAndMulWithOverflow recognition and semantics for the multiplication-with-overflow aggregate result and extractvalue projections. Llvm.interpretOp' does not interpret the required overflow intrinsic aggregate/extractvalue operations, so this scalar helper cannot currently be represented.

<a id="is2452"></a>

## IS2452 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2451–2452](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2451-L2452). Kind: delegation.
- **Rewrite:** If we have a multiplication overflow check that is being 'and'ed with a check that one of the multipliers is not zero, we can omit the 'and', and only keep the overflow check.; returns `Op0`. Guard: `isCheckForZeroAndMulWithOverflow(Op1, Op0, false)`. Delegates to `simplifyAndOrOfCmps`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — isCheckForZeroAndMulWithOverflow, not simplifyAndOrOfCmps; draft metadata corrected against source..
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Requires isCheckForZeroAndMulWithOverflow recognition and semantics for the multiplication-with-overflow aggregate result and extractvalue projections. Llvm.interpretOp' does not interpret the required overflow intrinsic aggregate/extractvalue operations, so this scalar helper cannot currently be represented.

<a id="is2457"></a>

## IS2457 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2456–2457](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2456-L2457). Kind: delegation.
- **Rewrite:** Try some generic simplifications for associative operations.; returns `V`. Guard: `Value *V = simplifyAssociativeBinOp(Instruction::Or, Op0, Op1, Q, MaxRecurse)`. Delegates to `simplifyAssociativeBinOp`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Generic recursive dispatch requires certified recursive simplifyBinOp results, source recursion-budget composition, and/or control-flow-sensitive threading. Current Puddle has no reusable proof-bearing recursive simplifier facility; PHI interpretation is additionally absent where applicable.

<a id="is2462"></a>

## IS2462 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2461–2462](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2461-L2462). Kind: delegation.
- **Rewrite:** Or distributes over And.  Try some generic simplifications based on this.; returns `V`. Guard: `Value *V = expandCommutativeBinOp(Instruction::Or, Op0, Op1, Instruction::And, Q, MaxRecurse)`. Delegates to `expandCommutativeBinOp`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Generic recursive dispatch requires certified recursive simplifyBinOp results, source recursion-budget composition, and/or control-flow-sensitive threading. Current Puddle has no reusable proof-bearing recursive simplifier facility; PHI interpretation is additionally absent where applicable.

<a id="is2468"></a>

## IS2468 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2465–2468](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2465-L2468). Kind: rewrite.
- **Rewrite:** A | (A || B) -> A || B; returns `Op1`. Guard: `isa<SelectInst>(Op0) || isa<SelectInst>(Op1)` and `Op0->getType()->isIntOrIntVectorTy(1)` and `match(Op1, m_Select(m_Specific(Op0), m_One(), m_Value()))`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — type required: integer scalar/vector with the stated bit width.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary source/destination widths and signedness, all source flags and operand orientations; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS2468.lean](../../Veir/InstSimplify/IS2468.lean).
- **Theorems:** `Veir.InstSimplify.IS2468.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with poison refinement and kernel proofs; Boolean cases use the kernel int1_cases theorem.

<a id="is2470"></a>

## IS2470 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2466–2470](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2466-L2470). Kind: rewrite.
- **Rewrite:** A | (A || B) -> A || B; returns `Op0`. Guard: `isa<SelectInst>(Op0) || isa<SelectInst>(Op1)` and `Op0->getType()->isIntOrIntVectorTy(1)` and `match(Op1, m_Select(m_Specific(Op0), m_One(), m_Value()))` and `else if match(Op0, m_Select(m_Specific(Op1), m_One(), m_Value()))`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — type required: integer scalar/vector with the stated bit width.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary source/destination widths and signedness, all source flags and operand orientations; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS2470.lean](../../Veir/InstSimplify/IS2470.lean).
- **Theorems:** `Veir.InstSimplify.IS2470.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with poison refinement and kernel proofs; Boolean cases use the kernel int1_cases theorem.

<a id="is2477"></a>

## IS2477 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2475–2477](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2475-L2477). Kind: delegation.
- **Rewrite:** If the operation is with the result of a select instruction, check whether operating on either branch of the select always yields the same value.; returns `V`. Guard: `isa<SelectInst>(Op0) || isa<SelectInst>(Op1)` and `Value *V = threadBinOpOverSelect(Instruction::Or, Op0, Op1, Q, MaxRecurse)`. Delegates to `threadBinOpOverSelect`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Generic recursive dispatch requires certified recursive simplifyBinOp results, source recursion-budget composition, and/or control-flow-sensitive threading. Current Puddle has no reusable proof-bearing recursive simplifier facility; PHI interpretation is additionally absent where applicable.

<a id="is2495"></a>

## IS2495 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2491–2495](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2491-L2495). Kind: rewrite.
- **Rewrite:** `((V+N) & ~M) | (V & M) -> V+N` when M is a contiguous low-bit mask and `MaskedValueIsZero(N,M,Q)` proves `N & M == 0`; either order of the add operands is accepted.
- **Matched/replaced opcodes:** `or`, `and`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-zero mask proof.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is2501"></a>

## IS2501 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2497–2501](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2497-L2501). Kind: rewrite.
- **Rewrite:** `(V & M) | ((V+N) & ~M) -> V+N` when M is a contiguous low-bit mask and `MaskedValueIsZero(N,M,Q)` proves `N & M == 0`; either order of the add operands is accepted.
- **Matched/replaced opcodes:** `or`, `and`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: known-zero mask proof.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is2510"></a>

## IS2510 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2508–2510](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2508-L2510). Kind: delegation.
- **Rewrite:** If the operation is with the result of a phi instruction, check whether operating on all incoming values of the phi always yields the same value.; returns `V`. Guard: `isa<PHINode>(Op0) || isa<PHINode>(Op1)` and `Value *V = threadBinOpOverPHI(Instruction::Or, Op0, Op1, Q, MaxRecurse)`. Delegates to `threadBinOpOverPHI`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Generic recursive dispatch requires certified recursive simplifyBinOp results, source recursion-budget composition, and/or control-flow-sensitive threading. Current Puddle has no reusable proof-bearing recursive simplifier facility; PHI interpretation is additionally absent where applicable.

<a id="is2515"></a>

## IS2515 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2514–2515](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2514-L2515). Kind: rewrite.
- **Rewrite:** (A ^ C) | (A ^ ~C) -> -1, i.e. all bits set to one.; returns `Constant::getAllOnesValue(Op0->getType())`. Guard: `match(Op0, m_Xor(m_Value(A), m_APInt(C1))) && match(Op1, m_Xor(m_Specific(A), m_SpecificInt(~*C1)))`.
- **Matched/replaced opcodes:** `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width and instruction flags; no vectors.
- **Lean:** [Veir/InstSimplify/IS2515.lean](../../Veir/InstSimplify/IS2515.lean).
- **Theorems:** `Veir.InstSimplify.IS2515.valid`.
- **Details / missing facilities:** Compiled width-parametric LLVM scalar refinement proof, preserving poison and all source instruction flags.

<a id="is2522"></a>

## IS2522 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2519–2522](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2519-L2522). Kind: rewrite.
- **Rewrite:** If Op0 is false implies Op1 is false, then Op1 is a subset of Op0.; returns `Op0`. Guard: `Op0->getType()->isIntOrIntVectorTy(1)` and `std::optional<bool> Implied = isImpliedCondition(Op0, Op1, Q.DL, false)` and `*Implied == false`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: boolean implication/disjointness or dominating-condition analysis; type required: integer scalar/vector with the stated bit width.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is2525"></a>

## IS2525 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2522–2525](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2522-L2525). Kind: rewrite.
- **Rewrite:** If Op0 is false implies Op1 is true, then at least one is always true.; returns `ConstantInt::getTrue(Op0->getType())`. Guard: `Op0->getType()->isIntOrIntVectorTy(1)` and `std::optional<bool> Implied = isImpliedCondition(Op0, Op1, Q.DL, false)` and `*Implied == true`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: boolean implication/disjointness or dominating-condition analysis; type required: integer scalar/vector with the stated bit width.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is2531"></a>

## IS2531 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2528–2531](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2528-L2531). Kind: rewrite.
- **Rewrite:** If Op1 is false implies Op0 is false, then Op0 is a subset of Op1.; returns `Op1`. Guard: `Op0->getType()->isIntOrIntVectorTy(1)` and `std::optional<bool> Implied = isImpliedCondition(Op1, Op0, Q.DL, false)` and `*Implied == false`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: boolean implication/disjointness or dominating-condition analysis; type required: integer scalar/vector with the stated bit width.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is2534"></a>

## IS2534 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2531–2534](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2531-L2534). Kind: rewrite.
- **Rewrite:** If Op1 is false implies Op0 is true, then at least one is always true.; returns `ConstantInt::getTrue(Op1->getType())`. Guard: `Op0->getType()->isIntOrIntVectorTy(1)` and `std::optional<bool> Implied = isImpliedCondition(Op1, Op0, Q.DL, false)` and `*Implied == true`.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — analysis required: boolean implication/disjointness or dominating-condition analysis; type required: integer scalar/vector with the stated bit width.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Source requires semantic ValueTracking analysis (nonzero, power-of-two, known bits, masked-zero, or implied condition) on arbitrary values. Puddle inspectOperation facts are erased from validity; no proof-bearing analysis guard is available.

<a id="is2539"></a>

## IS2539 — `simplifyOrInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2538–2539](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2538-L2539). Kind: delegation.
- **Rewrite:** At the top recursion level, return Op1 for or when a dominating condition implies Op0 == Op1.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Requires a proof-bearing certificate for isImpliedByDomCondition(ICMP_EQ, Op0, Op1, Q.CtxI, Q.DL). Current Puddle validity has no control-flow/dominating-equality certificate interface; inspectOperation facts are erased. The scalar result under a certified equality is elementary; the missing facility is the contextual equality evidence.

<a id="is2553"></a>

## IS2553 — `simplifyXorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2552–2553](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2552-L2553). Kind: delegation.
- **Rewrite:** Given operands for a Xor, see if we can fold the result. If not, this returns null.; returns `C`. Guard: `Constant *C = foldOrCommuteConstant(Instruction::Xor, Op0, Op1, Q)`. Delegates to `foldOrCommuteConstant`.
- **Matched/replaced opcodes:** `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integer constant operands, arbitrary width and instruction properties; no FP/vector/undef.
- **Lean:** [Veir/InstSimplify/IS0582.lean](../../Veir/InstSimplify/IS0582.lean).
- **Theorems:** `Veir.InstSimplify.IS0582.pattern_xor_valid`.
- **Shared implementation:** [IS0582](#is0582). This caller is not an additional independent port.
- **Details / missing facilities:** Successful constant-fold delegation covered by the certified scalar LLVM constant-fold pattern IS0582 for this opcode. Commutation itself returns no rewrite.

<a id="is2557"></a>

## IS2557 — `simplifyXorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2556–2557](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2556-L2557). Kind: rewrite.
- **Rewrite:** X ^ poison -> poison; returns `Op1`. Guard: `isa<PoisonValue>(Op1)`.
- **Matched/replaced opcodes:** `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM poison propagation semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2557.lean](../../Veir/InstSimplify/IS2557.lean).
- **Theorems:** `Veir.InstSimplify.IS2557.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2561"></a>

## IS2561 — `simplifyXorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2560–2561](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2560-L2561). Kind: rewrite.
- **Rewrite:** A ^ undef -> undef; returns `Op1`. Guard: `Q.isUndefValue(Op1)`.
- **Matched/replaced opcodes:** `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM undef nondeterministic semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** LLVM undef nondeterminism is absent from LLVM.Int and Llvm.interpretOp'.

<a id="is2565"></a>

## IS2565 — `simplifyXorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2564–2565](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2564-L2565). Kind: rewrite.
- **Rewrite:** A ^ 0 = A; returns `Op0`. Guard: `match(Op1, m_Zero())`.
- **Matched/replaced opcodes:** `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2565.lean](../../Veir/InstSimplify/IS2565.lean).
- **Theorems:** `Veir.InstSimplify.IS2565.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2569"></a>

## IS2569 — `simplifyXorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2568–2569](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2568-L2569). Kind: rewrite.
- **Rewrite:** A ^ A = 0; returns `Constant::getNullValue(Op0->getType())`. Guard: `Op0 == Op1`.
- **Matched/replaced opcodes:** `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2569.lean](../../Veir/InstSimplify/IS2569.lean).
- **Theorems:** `Veir.InstSimplify.IS2569.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2573"></a>

## IS2573 — `simplifyXorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2572–2573](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2572-L2573). Kind: rewrite.
- **Rewrite:** A ^ ~A  =  ~A ^ A  =  -1; returns `Constant::getAllOnesValue(Op0->getType())`. Guard: `match(Op0, m_Not(m_Specific(Op1))) || match(Op1, m_Not(m_Specific(Op0)))`.
- **Matched/replaced opcodes:** `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2573.lean](../../Veir/InstSimplify/IS2573.lean).
- **Theorems:** `Veir.InstSimplify.IS2573.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2580"></a>

## IS2580 — `simplifyXorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2579–2580](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2579-L2580). Kind: rewrite.
- **Rewrite:** (~A & B) ^ (A | B) --> A -- There are 8 commuted variants.; returns `A`. Guard: `match(X, m_c_And(m_Not(m_Value(A)), m_Value(B))) && match(Y, m_c_Or(m_Specific(A), m_Specific(B)))`.
- **Matched/replaced opcodes:** `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2580.lean](../../Veir/InstSimplify/IS2580.lean).
- **Theorems:** `Veir.InstSimplify.IS2580.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2589"></a>

## IS2589 — `simplifyXorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2588–2589](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2588-L2589). Kind: rewrite.
- **Rewrite:** (~A | B) ^ (A & B) --> ~A -- There are 8 commuted variants. The 'not' op must contain a complete -1 operand (no undef elements for vector) for the transform to be safe.; returns `NotA`. Guard: `match(X, m_c_Or(m_CombineAnd(m_Not(m_Value(A)), m_Value(NotA)), m_Value(B))) && match(Y, m_c_And(m_Specific(A), m_Specific(B)))`.
- **Matched/replaced opcodes:** `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary bitwidth and signedness; all matched operation commutations where parameterized; no vectors.
- **Lean:** [Veir/InstSimplify/IS2589.lean](../../Veir/InstSimplify/IS2589.lean).
- **Theorems:** `Veir.InstSimplify.IS2589.valid`.
- **Details / missing facilities:** Compiled LLVM scalar refinement proof; arbitrary widths and instruction flags.

<a id="is2594"></a>

## IS2594 — `simplifyXorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2593–2594](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2593-L2594). Kind: delegation.
- **Rewrite:** Return the successful result of foldAndOrNot for the enclosing xor operation.
- **Matched/replaced opcodes:** `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary width, all source operand orientations; no vectors.
- **Lean:** [Veir/InstSimplify/IS2580.lean](../../Veir/InstSimplify/IS2580.lean), [Veir/InstSimplify/IS2589.lean](../../Veir/InstSimplify/IS2589.lean).
- **Theorems:** `Veir.InstSimplify.IS2580.valid`, `Veir.InstSimplify.IS2589.valid`.
- **Shared implementation:** [IS2580](#is2580), [IS2589](#is2589). This caller is not an additional independent port.
- **Details / missing facilities:** Helper dispatch in either root operand order is fully covered by both bitwise callee patterns and their parameterized operand commutations.

<a id="is2596"></a>

## IS2596 — `simplifyXorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2595–2596](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2595-L2596). Kind: delegation.
- **Rewrite:** Return the successful result of foldAndOrNot (commuted) for the enclosing xor operation.
- **Matched/replaced opcodes:** `xor`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary width, all source operand orientations; no vectors.
- **Lean:** [Veir/InstSimplify/IS2580.lean](../../Veir/InstSimplify/IS2580.lean), [Veir/InstSimplify/IS2589.lean](../../Veir/InstSimplify/IS2589.lean).
- **Theorems:** `Veir.InstSimplify.IS2580.valid`, `Veir.InstSimplify.IS2589.valid`.
- **Shared implementation:** [IS2580](#is2580), [IS2589](#is2589). This caller is not an additional independent port.
- **Details / missing facilities:** Helper dispatch in either root operand order is fully covered by both bitwise callee patterns and their parameterized operand commutations.

<a id="is2599"></a>

## IS2599 — `simplifyXorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2598–2599](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2598-L2599). Kind: delegation.
- **Rewrite:** returns `V`. Guard: `Value *V = simplifyLogicOfAddSub(Op0, Op1, Instruction::Xor)`. Delegates to `simplifyLogicOfAddSub`.
- **Matched/replaced opcodes:** `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths and constant payload spellings; no vectors.
- **Lean:** [Veir/InstSimplify/IS2011.lean](../../Veir/InstSimplify/IS2011.lean).
- **Theorems:** `Veir.InstSimplify.IS2011.valid_xor`.
- **Shared implementation:** [IS2011](#is2011). This caller is not an additional independent port.
- **Details / missing facilities:** Shared add/sub logic helper dispatch covered by the corresponding opcode pattern, including root commutation and all nsw/nuw/disjoint flags.

<a id="is2604"></a>

## IS2604 — `simplifyXorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2603–2604](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2603-L2604). Kind: delegation.
- **Rewrite:** Try some generic simplifications for associative operations.; returns `V`. Guard: `Value *V = simplifyAssociativeBinOp(Instruction::Xor, Op0, Op1, Q, MaxRecurse)`. Delegates to `simplifyAssociativeBinOp`.
- **Matched/replaced opcodes:** `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Generic recursive dispatch requires certified recursive simplifyBinOp results, source recursion-budget composition, and/or control-flow-sensitive threading. Current Puddle has no reusable proof-bearing recursive simplifier facility; PHI interpretation is additionally absent where applicable.

<a id="is2616"></a>

## IS2616 — `simplifyXorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2615–2616](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2615-L2616). Kind: delegation.
- **Rewrite:** At the top recursion level, return zero for xor when a dominating condition implies Op0 == Op1.
- **Matched/replaced opcodes:** `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive/shared helper dispatch; preserve callee and remaining recursion budget.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers of arbitrary width; vectors unmodeled.
- **Details / missing facilities:** Requires a proof-bearing certificate for isImpliedByDomCondition(ICMP_EQ, Op0, Op1, Q.CtxI, Q.DL). Current Puddle validity has no control-flow/dominating-equality certificate interface; inspectOperation facts are erased. The scalar result under a certified equality is elementary; the missing facility is the contextual equality evidence.

<a id="is2623"></a>

## IS2623 — `simplifyXorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2622–2623](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2622-L2623). Kind: rewrite.
- **Rewrite:** (xor (sub nuw C_Mask, X), C_Mask) -> X; returns `X`. Guard: `match(Op0, m_NUWSub(m_Specific(Op1), m_Value(X))) && match(Op1, m_LowBitMask())`.
- **Matched/replaced opcodes:** `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction property required: no-unsigned-wrap operator flag.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary source/destination widths and signedness, all source flags and operand orientations; vectors unmodeled.
- **Lean:** [Veir/InstSimplify/IS2623.lean](../../Veir/InstSimplify/IS2623.lean).
- **Theorems:** `Veir.InstSimplify.IS2623.valid`.
- **Details / missing facilities:** Complete scalar source family compiled with poison refinement and kernel proofs; Boolean cases use the kernel int1_cases theorem.

<a id="is2650"></a>

## IS2650 — `extractEquivalentCondition`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2648–2650](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2648-L2650). Kind: schema.
- **Rewrite:** Return the existing CmpInst when predicate, LHS and RHS exactly equal requested predicate and operand order.
- **Matched/replaced opcodes:** `icmp`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — condition of V is a CmpInst; exact predicate and operand pointer identity.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** extractEquivalentCondition is a condition-finding helper, not an independent IR rewrite. It returns an existing compare inside a select for the min/max callers; concrete semantic rewrites are separately inventoried at IS3675/3677/3689/3691/3749/3751/3763/3765.

<a id="is2653"></a>

## IS2653 — `extractEquivalentCondition`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2651–2653](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2651-L2653). Kind: schema.
- **Rewrite:** Return the existing CmpInst when its predicate is the requested predicate’s swapped form and its operands are exactly reversed.
- **Matched/replaced opcodes:** `icmp`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — condition of V is a CmpInst; swapped predicate and reversed operand pointer identity.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** extractEquivalentCondition is a condition-finding helper, not an independent IR rewrite. It returns an existing compare inside a select for the min/max callers; concrete semantic rewrites are separately inventoried at IS3675/3677/3689/3691/3749/3751/3763/3765.

<a id="is2803"></a>

## IS2803 — `computePointerICmp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2777–2803](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2777-L2803). Kind: rewrite.
- **Rewrite:** For an unsigned/equality pointer comparison only, strip accumulated constant offsets (allowing non-inbounds GEPs only for equality); when both pointers reduce to the identical base, compare the offsets with the signed-converted predicate and return that boolean constant.
- **Matched/replaced opcodes:** `icmp`, `getelementptr`.
- **Beyond opcode/constant/SSA matching:** Yes — DataLayout pointer index size; accumulated constant GEP offsets.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires DataLayout pointer index-width reasoning and constant-offset stripping.

<a id="is2827"></a>

## IS2827 — `computePointerICmp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2810–2827](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2810-L2827). Kind: rewrite.
- **Rewrite:** For an equality comparison between bases proven to have non-overlapping storage, if both bases have known non-null object sizes and the difference between offsets is strictly within either object (not merely one-past), fold to the predicate's unequal-pointer result.
- **Matched/replaced opcodes:** `icmp`, `getelementptr`, `alloca`.
- **Beyond opcode/constant/SSA matching:** Yes — non-overlapping storage proof; object-size/dereferenceable bytes and nullability; offset distance.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires pointer provenance, storage-disjointness and object-size/nullability analyses.

<a id="is2855"></a>

## IS2855 — `computePointerICmp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2833–2855](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2833-L2855). Kind: rewrite.
- **Rewrite:** For pointer equality, if every underlying object on one side is a noalias allocation call and every underlying object on the other is statically/dispositionally allocation-disjoint (in either operand order), fold to unequal.
- **Matched/replaced opcodes:** `icmp`, `call`, `alloca`.
- **Beyond opcode/constant/SSA matching:** Yes — getUnderlyingObjects; noalias call and allocation-disjoint classification.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires underlying-object provenance and noalias/allocation-disjoint analysis.

<a id="is2895"></a>

## IS2895 — `computePointerICmp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2858–2895](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2858-L2895). Kind: rewrite.
- **Rewrite:** For pointer equality, if an operand is an alloc-like call and the other operand is known nonzero, and the allocation pointer is not captured (except comparisons to a pointer loaded from a global), fold to the predicate's false-when-equal result. Upstream marks this rule FIXME/PR54002 because the fold may not be valid for all comparisons to that address.
- **Matched/replaced opcodes:** `icmp`, `call`, `load`.
- **Beyond opcode/constant/SSA matching:** Yes — TargetLibraryInfo alloc-like classification; known-nonzero; pointer capture tracking.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires target-library allocation recognition, known-nonzero and capture tracking; upstream marks this case FIXME/PR54002.

<a id="is2928"></a>

## IS2928 — `simplifyICmpOfBools`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2921–2928](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2921-L2928). Kind: rewrite.
- **Rewrite:** For i1 operands with RHS 0, fold `icmp ne X, 0`, `icmp ugt X, 0`, or `icmp slt X, 0` to X.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS and RHS are i1 scalar/vector; RHS is zero.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS2928.lean](../../Veir/InstSimplify/IS2928.lean).
- **Theorems:** `Veir.InstSimplify.IS2928_valid`.
- **Details / missing facilities:** Compiled LLVM Puddle validity; all listed scalar i1 predicates and poison behavior covered.

<a id="is2934"></a>

## IS2934 — `simplifyICmpOfBools`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2929–2934](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2929-L2934). Kind: rewrite.
- **Rewrite:** For i1 operands with RHS 0, fold `icmp eq|ule|sge (not X), 0` to X when LHS matches bitwise-not of X.
- **Matched/replaced opcodes:** `icmp`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS is a recognized bitwise not; RHS is zero.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS2934.lean](../../Veir/InstSimplify/IS2934.lean).
- **Theorems:** `Veir.InstSimplify.IS2934_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity; poison included and widths follow upstream constraints.

<a id="is2939"></a>

## IS2939 — `simplifyICmpOfBools`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2935–2939](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2935-L2939). Kind: rewrite.
- **Rewrite:** For i1 operands with RHS 0, `icmp ult X,0` and `icmp sgt X,0` are false.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS and RHS are i1 scalar/vector; RHS is zero.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS2939.lean](../../Veir/InstSimplify/IS2939.lean).
- **Theorems:** `Veir.InstSimplify.IS2939_valid`.
- **Details / missing facilities:** Compiled LLVM Puddle validity; all listed scalar i1 predicates and poison behavior covered.

<a id="is2943"></a>

## IS2943 — `simplifyICmpOfBools`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2940–2943](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2940-L2943). Kind: rewrite.
- **Rewrite:** For i1 operands with RHS 0, `icmp uge X,0` and `icmp sle X,0` are true.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS and RHS are i1 scalar/vector; RHS is zero.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS2943.lean](../../Veir/InstSimplify/IS2943.lean).
- **Theorems:** `Veir.InstSimplify.IS2943_valid`.
- **Details / missing facilities:** Compiled LLVM Puddle validity; all listed scalar i1 predicates and poison behavior covered.

<a id="is2953"></a>

## IS2953 — `simplifyICmpOfBools`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2948–2953](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2948-L2953). Kind: rewrite.
- **Rewrite:** For i1 operands with RHS 1, fold `icmp eq|uge|sle X,1` to X.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS and RHS are i1 scalar/vector; RHS is one.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS2953.lean](../../Veir/InstSimplify/IS2953.lean).
- **Theorems:** `Veir.InstSimplify.IS2953_valid`.
- **Details / missing facilities:** Compiled LLVM Puddle validity; all listed scalar i1 predicates and poison behavior covered.

<a id="is2959"></a>

## IS2959 — `simplifyICmpOfBools`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2954–2959](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2954-L2959). Kind: rewrite.
- **Rewrite:** For i1 operands with RHS 1, fold `icmp ne|ult|sgt (not X),1` to X when LHS matches bitwise-not of X.
- **Matched/replaced opcodes:** `icmp`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS is a recognized bitwise not; RHS is one.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS2959.lean](../../Veir/InstSimplify/IS2959.lean).
- **Theorems:** `Veir.InstSimplify.IS2959_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity; poison included and widths follow upstream constraints.

<a id="is2964"></a>

## IS2964 — `simplifyICmpOfBools`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2960–2964](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2960-L2964). Kind: rewrite.
- **Rewrite:** For i1 operands with RHS 1, `icmp ugt X,1` and `icmp slt X,1` are false.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS and RHS are i1 scalar/vector; RHS is one.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS2964.lean](../../Veir/InstSimplify/IS2964.lean).
- **Theorems:** `Veir.InstSimplify.IS2964_valid`.
- **Details / missing facilities:** Compiled LLVM Puddle validity; all listed scalar i1 predicates and poison behavior covered.

<a id="is2968"></a>

## IS2968 — `simplifyICmpOfBools`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2965–2968](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2965-L2968). Kind: rewrite.
- **Rewrite:** For i1 operands with RHS 1, `icmp ule X,1` and `icmp sge X,1` are true.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS and RHS are i1 scalar/vector; RHS is one.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS2968.lean](../../Veir/InstSimplify/IS2968.lean).
- **Theorems:** `Veir.InstSimplify.IS2968_valid`.
- **Details / missing facilities:** Compiled LLVM Puddle validity; all listed scalar i1 predicates and poison behavior covered.

<a id="is2980"></a>

## IS2980 — `simplifyICmpOfBools`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2974–2980](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2974-L2980). Kind: rewrite.
- **Rewrite:** For i1 operands and predicate UGE, return true when RHS logically implies LHS.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — isImpliedCondition(RHS,LHS) proves implication; i1 operand type.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires isImpliedCondition analysis; Puddle Models currently erases inspectOperation facts and has no semantic analysis certificate interface.

<a id="is2991"></a>

## IS2991 — `simplifyICmpOfBools`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2982–2991](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2982-L2991). Kind: rewrite.
- **Rewrite:** For i1 operands and predicate SGE, return true when LHS logically implies RHS.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — isImpliedCondition(LHS,RHS) proves implication; i1 signed values are 0 and −1.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires isImpliedCondition analysis; Puddle Models currently erases inspectOperation facts and has no semantic analysis certificate interface.

<a id="is2995"></a>

## IS2995 — `simplifyICmpOfBools`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2992–2995](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2992-L2995). Kind: rewrite.
- **Rewrite:** For i1 operands and predicate ULE, return true when LHS logically implies RHS.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — isImpliedCondition(LHS,RHS) proves implication; i1 operand type.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires isImpliedCondition analysis; Puddle Models currently erases inspectOperation facts and has no semantic analysis certificate interface.

<a id="is3000"></a>

## IS3000 — `simplifyICmpOfBools`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:2996–3000](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L2996-L3000). Kind: rewrite.
- **Rewrite:** For i1 operands and predicate SLE, return true when RHS logically implies LHS.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — isImpliedCondition(RHS,LHS) proves implication; i1 signed values are 0 and −1.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires isImpliedCondition analysis; Puddle Models currently erases inspectOperation facts and has no semantic analysis certificate interface.

<a id="is3074"></a>

## IS3074 — `simplifyICmpWithZero`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3060–3074](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3060-L3074). Kind: rewrite.
- **Rewrite:** `icmp ult X,0` is false.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is zero or normalizes equivalently from signed comparison with −1 or comparison with 1 via matchEquivZeroRHS.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3074.lean](../../Veir/InstSimplify/IS3074.lean).
- **Theorems:** `Veir.InstSimplify.IS3074_valid`.
- **Details / missing facilities:** Compiled scalar LLVM comparison Puddle validity; arbitrary widths and all specified predicates/poison behavior.

<a id="is3076"></a>

## IS3076 — `simplifyICmpWithZero`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3075–3076](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3075-L3076). Kind: rewrite.
- **Rewrite:** `icmp uge X,0` is true.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is zero or normalizes equivalently from signed comparison with −1 or comparison with 1 via matchEquivZeroRHS.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3076.lean](../../Veir/InstSimplify/IS3076.lean).
- **Theorems:** `Veir.InstSimplify.IS3076_valid`.
- **Details / missing facilities:** Compiled scalar LLVM comparison Puddle validity; arbitrary widths and all specified predicates/poison behavior.

<a id="is3080"></a>

## IS3080 — `simplifyICmpWithZero`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3077–3080](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3077-L3080). Kind: rewrite.
- **Rewrite:** `icmp eq|ule X,0` is false when X is known nonzero.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is zero or normalizes equivalently from signed comparison with −1 or comparison with 1 via matchEquivZeroRHS; known-nonzero analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires known-nonzero value analysis.

<a id="is3085"></a>

## IS3085 — `simplifyICmpWithZero`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3081–3085](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3081-L3085). Kind: rewrite.
- **Rewrite:** `icmp ne|ugt X,0` is true when X is known nonzero.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is zero or normalizes equivalently from signed comparison with −1 or comparison with 1 via matchEquivZeroRHS; known-nonzero analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires known-nonzero value analysis.

<a id="is3090"></a>

## IS3090 — `simplifyICmpWithZero`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3086–3090](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3086-L3090). Kind: rewrite.
- **Rewrite:** `icmp slt X,0` is true when KnownBits proves X negative.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is zero or normalizes equivalently from signed comparison with −1 or comparison with 1 via matchEquivZeroRHS; KnownBits proves sign bit set.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires KnownBits analysis.

<a id="is3092"></a>

## IS3092 — `simplifyICmpWithZero`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3091–3092](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3091-L3092). Kind: rewrite.
- **Rewrite:** `icmp slt X,0` is false when KnownBits proves X nonnegative.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is zero or normalizes equivalently from signed comparison with −1 or comparison with 1 via matchEquivZeroRHS; KnownBits proves sign bit clear.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires KnownBits analysis.

<a id="is3098"></a>

## IS3098 — `simplifyICmpWithZero`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3093–3098](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3093-L3098). Kind: rewrite.
- **Rewrite:** `icmp sle X,0` is true when KnownBits proves X negative.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is zero or normalizes equivalently from signed comparison with −1 or comparison with 1 via matchEquivZeroRHS; KnownBits proves sign bit set.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires KnownBits analysis.

<a id="is3100"></a>

## IS3100 — `simplifyICmpWithZero`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3099–3100](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3099-L3100). Kind: rewrite.
- **Rewrite:** `icmp sle X,0` is false when KnownBits proves X nonnegative and X is known nonzero.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is zero or normalizes equivalently from signed comparison with −1 or comparison with 1 via matchEquivZeroRHS; KnownBits nonnegative; known-nonzero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires KnownBits and known-nonzero analysis.

<a id="is3106"></a>

## IS3106 — `simplifyICmpWithZero`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3101–3106](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3101-L3106). Kind: rewrite.
- **Rewrite:** `icmp sge X,0` is false when KnownBits proves X negative.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is zero or normalizes equivalently from signed comparison with −1 or comparison with 1 via matchEquivZeroRHS; KnownBits proves sign bit set.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires KnownBits analysis.

<a id="is3108"></a>

## IS3108 — `simplifyICmpWithZero`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3107–3108](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3107-L3108). Kind: rewrite.
- **Rewrite:** `icmp sge X,0` is true when KnownBits proves X nonnegative.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is zero or normalizes equivalently from signed comparison with −1 or comparison with 1 via matchEquivZeroRHS; KnownBits proves sign bit clear.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires KnownBits analysis.

<a id="is3114"></a>

## IS3114 — `simplifyICmpWithZero`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3109–3114](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3109-L3114). Kind: rewrite.
- **Rewrite:** `icmp sgt X,0` is false when KnownBits proves X negative.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is zero or normalizes equivalently from signed comparison with −1 or comparison with 1 via matchEquivZeroRHS; KnownBits proves sign bit set.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires KnownBits analysis.

<a id="is3116"></a>

## IS3116 — `simplifyICmpWithZero`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3115–3116](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3115-L3116). Kind: rewrite.
- **Rewrite:** `icmp sgt X,0` is true when KnownBits proves X nonnegative and X is known nonzero.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is zero or normalizes equivalently from signed comparison with −1 or comparison with 1 via matchEquivZeroRHS; KnownBits nonnegative; known-nonzero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires KnownBits and known-nonzero analysis.

<a id="is3140"></a>

## IS3140 — `simplifyICmpWithConstant`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3133–3140](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3133-L3140). Kind: rewrite.
- **Rewrite:** For `icmp` sign-bit checks on `bitcast(uitofp X)`, return the boolean indicated by `isSignBitCheck(Pred,C,TrueIfSigned)` (the source folds unsigned-to-FP results that cannot be negative).
- **Matched/replaced opcodes:** `icmp`, `uitofp`, `bitcast`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS integer constant; LHS elementwise bitcast of uitofp; predicate/constant recognized as sign-bit check.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires floating conversion sign-bit semantics and isSignBitCheck predicate analysis.

<a id="is3146"></a>

## IS3146 — `simplifyICmpWithConstant`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3143–3146](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3143-L3146). Kind: rewrite.
- **Rewrite:** If the exact ICmp region for constant C is empty, every value fails the comparison, so fold false.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is APInt constant; ConstantRange::makeExactICmpRegion is empty.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary positive width; all integer predicates.
- **Lean:** [Veir/InstSimplify/IS3146.lean](../../Veir/InstSimplify/IS3146.lean).
- **Theorems:** `Veir.InstSimplify.IS3146_valid`.
- **Details / missing facilities:** Compiled exhaustive scalar comparison empty/full-region characterization across all predicates and extrema, for every positive LLVM integer width.

<a id="is3148"></a>

## IS3148 — `simplifyICmpWithConstant`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3143–3148](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3143-L3148). Kind: rewrite.
- **Rewrite:** If the exact ICmp region for constant C is the full set, every value passes, so fold true.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is APInt constant; ConstantRange::makeExactICmpRegion is full.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers of arbitrary positive width; all integer predicates.
- **Lean:** [Veir/InstSimplify/IS3148.lean](../../Veir/InstSimplify/IS3148.lean).
- **Theorems:** `Veir.InstSimplify.IS3148_valid`.
- **Details / missing facilities:** Compiled exhaustive scalar comparison empty/full-region characterization across all predicates and extrema, for every positive LLVM integer width.

<a id="is3153"></a>

## IS3153 — `simplifyICmpWithConstant`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3150–3153](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3150-L3153). Kind: rewrite.
- **Rewrite:** If LHS has a non-full computed range wholly contained in the exact true region of comparison with C, fold true.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS APInt constant; computeConstantRange(LHS,signedness) is not full; RHS region contains LHS range.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires ConstantRange/value-range analysis.

<a id="is3155"></a>

## IS3155 — `simplifyICmpWithConstant`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3154–3155](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3154-L3155). Kind: rewrite.
- **Rewrite:** If LHS has a non-full computed range wholly contained in the inverse region of comparison with C, fold false.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS APInt constant; computeConstantRange(LHS,signedness) is not full; inverse RHS region contains LHS range.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires ConstantRange/value-range analysis.

<a id="is3166"></a>

## IS3166 — `simplifyICmpWithConstant`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3158–3166](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3158-L3166). Kind: rewrite.
- **Rewrite:** For EQ/NE of a nuw or nsw multiplication by nonzero constant MulC against C, fold when C is not divisible by MulC: NE→true and EQ→false.
- **Matched/replaced opcodes:** `icmp`, `mul`.
- **Beyond opcode/constant/SSA matching:** Yes — UseInstrInfo enabled; multiplication carries NUW with unsigned remainder nonzero or NSW with signed remainder nonzero; EQ/NE.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar integers of arbitrary width, with the actual nsw/nuw multiplier guard and nonmultiple literal; equality and inequality predicates, all other flags preserved.
- **Lean:** [Veir/InstSimplify/IS3166.lean](../../Veir/InstSimplify/IS3166.lean).
- **Theorems:** `Veir.InstSimplify.IS3166_valid`.
- **Details / missing facilities:** Proved using actual LLVM mul and icmp semantics; signed/unsigned no-overflow multiplication is divisible by its nonzero multiplier.

<a id="is3169"></a>

## IS3169 — `simplifyICmpWithConstant`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3168–3169](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3168-L3169). Kind: rewrite.
- **Rewrite:** `icmp uge X,1` is true when X is known nonzero.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate UGE; C exactly one; LHS known nonzero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires known-nonzero analysis.

<a id="is3242"></a>

## IS3242 — `simplifyICmpUsingMonotonicValues`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3232–3242](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3232-L3242). Kind: rewrite.
- **Rewrite:** For UGE or ULT, collect depth-at-most-one unsigned lower/upper bounds through OR, saturating add/sub, AND, URem, UDiv, LShr, and nuw multiplication (the latter only when the other factor is known nonzero); if an identical value occurs in both bound sets, fold UGE true or ULT false.
- **Matched/replaced opcodes:** `icmp`, `or`, `and`, `urem`, `udiv`, `lshr`, `mul`, `call`.
- **Beyond opcode/constant/SSA matching:** Yes — depth-limited monotonic-value analysis, saturation intrinsics, nuw flags and known-nonzero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires a value-monotonicity analysis and known-nonzero/nuw reasoning; matching the listed opcode graph is insufficient without those facts.

<a id="is3259"></a>

## IS3259 — `simplifyICmpWithBinOpOnLHS`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3253–3259](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3253-L3259). Kind: rewrite.
- **Rewrite:** For `icmp slt (or X,Y), X`, return true if KnownBits proves X nonnegative and Y negative; for `icmp sge` under the same facts, return false.
- **Matched/replaced opcodes:** `icmp`, `or`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is identical to one OR operand; KnownBits sign facts.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires KnownBits analysis.

<a id="is3261"></a>

## IS3261 — `simplifyICmpWithBinOpOnLHS`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3253–3261](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3253-L3261). Kind: rewrite.
- **Rewrite:** For `icmp slt (or X,Y), X`, return false if X is negative or Y is nonnegative; for `icmp sge` under those facts, return true.
- **Matched/replaced opcodes:** `icmp`, `or`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is identical to one OR operand; KnownBits sign facts.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires KnownBits analysis.

<a id="is3280"></a>

## IS3280 — `simplifyICmpWithBinOpOnLHS`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3265–3280](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3265-L3280). Kind: rewrite.
- **Rewrite:** For `(urem X,Y) == Y`, `(urem X,Y) >u Y`, or `(urem X,Y) >=u Y`, fold false. Also fold signed `>s`/`>=s` false when Y is proven nonnegative.
- **Matched/replaced opcodes:** `icmp`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS equals URem divisor; signed predicates additionally require KnownBits nonnegative for Y.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM arbitrary-width integers; unsigned/equality predicates only.
- **Lean:** [Veir/InstSimplify/IS3280.lean](../../Veir/InstSimplify/IS3280.lean).
- **Theorems:** `Veir.InstSimplify.IS3280_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity; exact native numeric/flag guards and arbitrary bitwidth. Signed remainder variants requiring known-nonnegative analysis are outside the represented domain.

<a id="is3291"></a>

## IS3291 — `simplifyICmpWithBinOpOnLHS`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3281–3291](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3281-L3291). Kind: rewrite.
- **Rewrite:** For `(urem X,Y) != Y`, `(urem X,Y) <u Y`, or `(urem X,Y) <=u Y`, fold true. Also fold signed `<s`/`<=s` true when Y is proven nonnegative.
- **Matched/replaced opcodes:** `icmp`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS equals URem divisor; signed predicates additionally require KnownBits nonnegative for Y.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM arbitrary-width integers; unsigned/equality predicates only.
- **Lean:** [Veir/InstSimplify/IS3291.lean](../../Veir/InstSimplify/IS3291.lean).
- **Theorems:** `Veir.InstSimplify.IS3291_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity; exact native numeric/flag guards and arbitrary bitwidth. Signed remainder variants requiring known-nonnegative analysis are outside the represented domain.

<a id="is3315"></a>

## IS3315 — `simplifyICmpWithBinOpOnLHS`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3295–3315](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3295-L3315). Kind: rewrite.
- **Rewrite:** For nonzero X, fold `(X lshr C) == X`, `(X lshr C) >=u X`, `(X lshr C) >u X`, and corresponding `udiv X,C` comparisons false.
- **Matched/replaced opcodes:** `icmp`, `lshr`, `udiv`.
- **Beyond opcode/constant/SSA matching:** Yes — Shift amount C≠0 for lshr or divisor C≠1 for udiv; RHS X known nonzero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Source lines3306-3320 requires isKnownNonZero(RHS,Q) on the variable X in addition to constant divisor/shift guards. Puddle Models has no semantic known-nonzero certificate, and inspectOperation analysis facts are erased. No restriction to a toy constant-X instance is claimed.

<a id="is3319"></a>

## IS3319 — `simplifyICmpWithBinOpOnLHS`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3295–3319](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3295-L3319). Kind: rewrite.
- **Rewrite:** For nonzero X, fold `(X lshr C) != X`, `(X lshr C) <u X`, `(X lshr C) <=u X`, and corresponding `udiv X,C` comparisons true.
- **Matched/replaced opcodes:** `icmp`, `lshr`, `udiv`.
- **Beyond opcode/constant/SSA matching:** Yes — Shift amount C≠0 for lshr or divisor C≠1 for udiv; RHS X known nonzero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Source lines3306-3320 requires isKnownNonZero(RHS,Q) on the variable X in addition to constant divisor/shift guards. Puddle Models has no semantic known-nonzero certificate, and inspectOperation analysis facts are erased. No restriction to a toy constant-X instance is claimed.

<a id="is3341"></a>

## IS3341 — `simplifyICmpWithBinOpOnLHS`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3324–3341](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3324-L3341). Kind: rewrite.
- **Rewrite:** Fold `icmp ugt E, X` false when E is one of `(X*C1) udiv C2` with C1≤uC2, `(X*C1) lshr C2` with C1≤u2^C2, or `(X shl C1) udiv C2` with 2^C1≤uC2.
- **Matched/replaced opcodes:** `icmp`, `udiv`, `mul`, `lshr`, `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — All constants; APInt unsigned inequalities exactly as stated.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar integers of arbitrary width, including poison and every overflow/exact flag combination permitted by the LLVM guard.
- **Lean:** [Veir/InstSimplify/IS3341.lean](../../Veir/InstSimplify/IS3341.lean), [Veir/InstSimplify/CmpNumericExtra.lean](../../Veir/InstSimplify/CmpNumericExtra.lean).
- **Theorems:** `Veir.InstSimplify.IS3341_valid`.
- **Details / missing facilities:** All three exact upstream shapes proved: multiply/unsigned-divide, multiply/logical-right-shift, and left-shift/unsigned-divide with their respective constant bounds.

<a id="is3343"></a>

## IS3343 — `simplifyICmpWithBinOpOnLHS`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3324–3343](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3324-L3343). Kind: rewrite.
- **Rewrite:** Fold `icmp ule E, X` true when E is one of `(X*C1) udiv C2` with C1≤uC2, `(X*C1) lshr C2` with C1≤u2^C2, or `(X shl C1) udiv C2` with 2^C1≤uC2.
- **Matched/replaced opcodes:** `icmp`, `udiv`, `mul`, `lshr`, `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — All constants; APInt unsigned inequalities exactly as stated.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar integers of arbitrary width, including poison and every overflow/exact flag combination permitted by the LLVM guard.
- **Lean:** [Veir/InstSimplify/IS3343.lean](../../Veir/InstSimplify/IS3343.lean), [Veir/InstSimplify/CmpNumericExtra.lean](../../Veir/InstSimplify/CmpNumericExtra.lean).
- **Theorems:** `Veir.InstSimplify.IS3343_valid`.
- **Details / missing facilities:** All three exact upstream shapes proved: multiply/unsigned-divide, multiply/logical-right-shift, and left-shift/unsigned-divide with their respective constant bounds.

<a id="is3350"></a>

## IS3350 — `simplifyICmpWithBinOpOnLHS`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3346–3350](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3346-L3350). Kind: rewrite.
- **Rewrite:** Fold `(sub C,X) == X` false and `(sub C,X) != X` true when C is an odd APInt constant.
- **Matched/replaced opcodes:** `icmp`, `sub`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is the subtrahend X; C odd; EQ or NE.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3350.lean](../../Veir/InstSimplify/IS3350.lean).
- **Theorems:** `Veir.InstSimplify.IS3350_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM Puddle validity with exact upstream numeric and poison-generating flag guards.

<a id="is3350a"></a>

## IS3350a — `trySimplifyICmpWithAdds`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3370–3385](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3370-L3385). Kind: schema.
- **Rewrite:** Schema: signed relational comparison of X+C1 and X+C2 where exactly the RHS add has NSW (after canonicalizing it to RHS); reduce to comparing C1 and C2 if (C1≤sC2 and C1≥s0) or (C2≤sC1 and C1≤s0).
- **Matched/replaced opcodes:** `icmp`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — NSW flag on one add and signed APInt comparisons.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** trySimplifyICmpWithAdds returns only a Boolean eligibility certificate under UseInstrInfo, signed predicates and NSW/constant guards; it performs no independent IR rewrite. Actual cancellation caller IS3462 requires recursive simplifyICmpInst/result/recursion-budget contract absent from local Puddle Models.

<a id="is3428"></a>

## IS3428 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3397–3428](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3397-L3428). Kind: rewrite.
- **Rewrite:** Reduce `icmp pred (X+Y), X` to the recursive comparison `icmp pred Y, 0` when the addend X matches either add operand and predicate/add flags make wrapping irrelevant.
- **Matched/replaced opcodes:** `icmp`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse>0; equality predicate or add has required NUW for unsigned predicate / NSW for signed predicate; recursive result non-null.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires add flag inspection and recursive ICmp simplification.

<a id="is3435"></a>

## IS3435 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3430–3435](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3430-L3435). Kind: rewrite.
- **Rewrite:** Reduce `icmp pred X, (X+Y)` to recursive `icmp pred 0,Y` when X matches either RHS add operand and predicate/add flags make wrapping irrelevant.
- **Matched/replaced opcodes:** `icmp`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse>0; equality predicate or add has required NUW/NSW; recursive result non-null.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires add flag inspection and recursive ICmp simplification.

<a id="is3462"></a>

## IS3462 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3437–3462](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3437-L3462). Kind: rewrite.
- **Rewrite:** For `icmp pred (A+B),(C+D)` with any one shared add operand, cancel the common term and recursively compare the two remaining addends.
- **Matched/replaced opcodes:** `icmp`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse>0; at least one SSA operand shared; both adds safe for predicate via equality/no-wrap flags or trySimplifyICmpWithAdds; recursive result non-null.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires overflow-flag/signed-add proof and recursive ICmp simplification.

<a id="is3468"></a>

## IS3468 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3466–3468](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3466-L3468). Kind: delegation.
- **Rewrite:** If LHS is a BinaryOperator, delegate comparison simplification to simplifyICmpWithBinOpOnLHS and return its first successful result. The concrete binop rules are separate entries.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse; helper result.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Simple forwarder to separately inventoried helper cases; no distinct transformation or new semantic precondition at this return. Forwards one of the independently inventoried binop rules.

<a id="is3473"></a>

## IS3473 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3470–3473](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3470-L3473). Kind: delegation.
- **Rewrite:** If RHS is a BinaryOperator, swap the ICmp predicate and operands and delegate to simplifyICmpWithBinOpOnLHS; return its first successful result. The concrete binop rules are separate entries.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse; swapped predicate; helper result.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Simple forwarder to separately inventoried helper cases; no distinct transformation or new semantic precondition at this return. Forwards one of the independently inventoried binop rules.

<a id="is3481"></a>

## IS3481 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3475–3481](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3475-L3481). Kind: rewrite.
- **Rewrite:** For signed `icmp slt` or `icmp ne` of `0 - (zext X)` against positive C, return true.
- **Matched/replaced opcodes:** `icmp`, `sub`, `zext`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate signed; C strictly positive.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar positive-width LLVM integer types of every width and signedness; actual extension semantics, all nneg/nsw/nuw flag combinations and poison behavior.
- **Lean:** [Veir/InstSimplify/IS3481.lean](../../Veir/InstSimplify/IS3481.lean), [Veir/InstSimplify/CmpCastSupport.lean](../../Veir/InstSimplify/CmpCastSupport.lean).
- **Theorems:** `Veir.InstSimplify.IS3481_valid`.
- **Details / missing facilities:** Negated zero extension has a nonpositive signed value; matched constant has the exact source strict-positive/nonnegative condition.

<a id="is3483"></a>

## IS3483 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3475–3483](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3475-L3483). Kind: rewrite.
- **Rewrite:** For signed `icmp sge` or `icmp eq` of `0 - (zext X)` against positive C, return false.
- **Matched/replaced opcodes:** `icmp`, `sub`, `zext`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate signed; C strictly positive.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar positive-width LLVM integer types of every width and signedness; actual extension semantics, all nneg/nsw/nuw flag combinations and poison behavior.
- **Lean:** [Veir/InstSimplify/IS3483.lean](../../Veir/InstSimplify/IS3483.lean), [Veir/InstSimplify/CmpCastSupport.lean](../../Veir/InstSimplify/CmpCastSupport.lean).
- **Theorems:** `Veir.InstSimplify.IS3483_valid`.
- **Details / missing facilities:** Negated zero extension has a nonpositive signed value; matched constant has the exact source strict-positive/nonnegative condition.

<a id="is3487"></a>

## IS3487 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3475–3487](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3475-L3487). Kind: rewrite.
- **Rewrite:** For signed `icmp sle` of `0 - (zext X)` against nonnegative C, return true.
- **Matched/replaced opcodes:** `icmp`, `sub`, `zext`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate signed; C nonnegative.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar positive-width LLVM integer types of every width and signedness; actual extension semantics, all nneg/nsw/nuw flag combinations and poison behavior.
- **Lean:** [Veir/InstSimplify/IS3487.lean](../../Veir/InstSimplify/IS3487.lean), [Veir/InstSimplify/CmpCastSupport.lean](../../Veir/InstSimplify/CmpCastSupport.lean).
- **Theorems:** `Veir.InstSimplify.IS3487_valid`.
- **Details / missing facilities:** Negated zero extension has a nonpositive signed value; matched constant has the exact source strict-positive/nonnegative condition.

<a id="is3489"></a>

## IS3489 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3475–3489](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3475-L3489). Kind: rewrite.
- **Rewrite:** For signed `icmp sgt` of `0 - (zext X)` against nonnegative C, return false.
- **Matched/replaced opcodes:** `icmp`, `sub`, `zext`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate signed; C nonnegative.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar positive-width LLVM integer types of every width and signedness; actual extension semantics, all nneg/nsw/nuw flag combinations and poison behavior.
- **Lean:** [Veir/InstSimplify/IS3489.lean](../../Veir/InstSimplify/IS3489.lean), [Veir/InstSimplify/CmpCastSupport.lean](../../Veir/InstSimplify/CmpCastSupport.lean).
- **Theorems:** `Veir.InstSimplify.IS3489_valid`.
- **Details / missing facilities:** Negated zero extension has a nonpositive signed value; matched constant has the exact source strict-positive/nonnegative condition.

<a id="is3512"></a>

## IS3512 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3494–3512](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3494-L3512). Kind: rewrite.
- **Rewrite:** Fold `(C2 shl X) == C` false when C2 is a power of two, C is a non-power-of-two constant, and the shift cannot erase the one bit under the safety guard.
- **Matched/replaced opcodes:** `icmp`, `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — NSW or NUW on shift, or C2==1, or C!=0; predicate EQ.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar integers of arbitrary positive width; every power-of-two bit and non-power-of-two literal, all poison/overflow behavior, with all four exact safety alternatives.
- **Lean:** [Veir/InstSimplify/IS3512.lean](../../Veir/InstSimplify/IS3512.lean), [Veir/InstSimplify/CmpNumericExtra.lean](../../Veir/InstSimplify/CmpNumericExtra.lean).
- **Theorems:** `Veir.InstSimplify.IS3512_valid`.
- **Details / missing facilities:** Proved all upstream safety alternatives separately: nsw, nuw, base one, or nonzero comparison constant. Shift flags otherwise unconstrained.

<a id="is3514"></a>

## IS3514 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3494–3514](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3494-L3514). Kind: rewrite.
- **Rewrite:** Fold `(C2 shl X) != C` true when C2 is a power of two, C is a non-power-of-two constant, and the shift cannot erase the one bit under the safety guard.
- **Matched/replaced opcodes:** `icmp`, `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — NSW or NUW on shift, or C2==1, or C!=0; predicate NE.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar integers of arbitrary positive width; every power-of-two bit and non-power-of-two literal, all poison/overflow behavior, with all four exact safety alternatives.
- **Lean:** [Veir/InstSimplify/IS3514.lean](../../Veir/InstSimplify/IS3514.lean), [Veir/InstSimplify/CmpNumericExtra.lean](../../Veir/InstSimplify/CmpNumericExtra.lean).
- **Theorems:** `Veir.InstSimplify.IS3514_valid`.
- **Details / missing facilities:** Proved all upstream safety alternatives separately: nsw, nuw, base one, or nonzero comparison constant. Shift flags otherwise unconstrained.

<a id="is3523"></a>

## IS3523 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3518–3523](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3518-L3523). Kind: rewrite.
- **Rewrite:** For power-of-two C, `(C shl X) >u signmask` is false.
- **Matched/replaced opcodes:** `icmp`, `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is sign-mask constant; predicate UGT.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar integers of arbitrary width, including poison and every overflow/exact flag combination permitted by the LLVM guard.
- **Lean:** [Veir/InstSimplify/IS3523.lean](../../Veir/InstSimplify/IS3523.lean), [Veir/InstSimplify/CmpNumericExtra.lean](../../Veir/InstSimplify/CmpNumericExtra.lean).
- **Theorems:** `Veir.InstSimplify.IS3523_valid`.
- **Details / missing facilities:** Power-of-two constants are parameterized by every bit below the width; successful shifts remain a single bit or zero, bounded by the unsigned sign mask. Poison shifts refine the literal result.

<a id="is3525"></a>

## IS3525 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3518–3525](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3518-L3525). Kind: rewrite.
- **Rewrite:** For power-of-two C, `(C shl X) <=u signmask` is true.
- **Matched/replaced opcodes:** `icmp`, `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is sign-mask constant; predicate ULE.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar integers of arbitrary width, including poison and every overflow/exact flag combination permitted by the LLVM guard.
- **Lean:** [Veir/InstSimplify/IS3525.lean](../../Veir/InstSimplify/IS3525.lean), [Veir/InstSimplify/CmpNumericExtra.lean](../../Veir/InstSimplify/CmpNumericExtra.lean).
- **Theorems:** `Veir.InstSimplify.IS3525_valid`.
- **Details / missing facilities:** Power-of-two constants are parameterized by every bit below the width; successful shifts remain a single bit or zero, bounded by the unsigned sign mask. Poison shifts refine the literal result.

<a id="is3543"></a>

## IS3543 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3531–3543](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3531-L3543). Kind: rewrite.
- **Rewrite:** For two `shl` results with identical left operand, recursively compare their shift amounts when both shifts have NUW, signed comparisons also have NSW on both, and the common left operand is known nonzero.
- **Matched/replaced opcodes:** `icmp`, `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse>0; both shifts NUW; signed predicates require both NSW; common input known nonzero; recursive result non-null.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires wrap-flag and known-nonzero analysis plus recursive comparison.

<a id="is3563"></a>

## IS3563 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3546–3563](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3546-L3563). Kind: rewrite.
- **Rewrite:** For matching `(X and C1)`/`(X and C2)` or `(X or C1)`/`(X or C2)`, fold ULE true when one constant bitmask is a subset of the other after operand/predicate canonicalization.
- **Matched/replaced opcodes:** `icmp`, `and`, `or`.
- **Beyond opcode/constant/SSA matching:** Yes — Same opcode and first operand; relational predicate; constant masks; C1 subset C2.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3563.lean](../../Veir/InstSimplify/IS3563.lean).
- **Theorems:** `Veir.InstSimplify.IS3563_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM constant-mask comparison for AND and OR with all disjoint flags, subset direction canonicalization, and same-sign guard for signed predicates.

<a id="is3565"></a>

## IS3565 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3546–3565](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3546-L3565). Kind: rewrite.
- **Rewrite:** For matching `(X and C1)`/`(X and C2)` or `(X or C1)`/`(X or C2)`, fold UGT false when one constant bitmask is a subset of the other after operand/predicate canonicalization.
- **Matched/replaced opcodes:** `icmp`, `and`, `or`.
- **Beyond opcode/constant/SSA matching:** Yes — Same opcode and first operand; relational predicate; constant masks; C1 subset C2.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3565.lean](../../Veir/InstSimplify/IS3565.lean).
- **Theorems:** `Veir.InstSimplify.IS3565_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM constant-mask comparison for AND and OR with all disjoint flags, subset direction canonicalization, and same-sign guard for signed predicates.

<a id="is3568"></a>

## IS3568 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3546–3568](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3546-L3568). Kind: rewrite.
- **Rewrite:** For matching AND/OR constant-mask results, fold SLE true when the canonicalized mask constants are subset-related and have the same sign classification.
- **Matched/replaced opcodes:** `icmp`, `and`, `or`.
- **Beyond opcode/constant/SSA matching:** Yes — Same opcode and first operand; relational predicate; constants; subset relation and equal nonnegative/sign-bit status.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3568.lean](../../Veir/InstSimplify/IS3568.lean).
- **Theorems:** `Veir.InstSimplify.IS3568_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM constant-mask comparison for AND and OR with all disjoint flags, subset direction canonicalization, and same-sign guard for signed predicates.

<a id="is3570"></a>

## IS3570 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3546–3570](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3546-L3570). Kind: rewrite.
- **Rewrite:** For matching AND/OR constant-mask results, fold SGT false when the canonicalized mask constants are subset-related and have the same sign classification.
- **Matched/replaced opcodes:** `icmp`, `and`, `or`.
- **Beyond opcode/constant/SSA matching:** Yes — Same opcode and first operand; relational predicate; constants; subset relation and equal nonnegative/sign-bit status.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3570.lean](../../Veir/InstSimplify/IS3570.lean).
- **Theorems:** `Veir.InstSimplify.IS3570_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM constant-mask comparison for AND and OR with all disjoint flags, subset direction canonicalization, and same-sign guard for signed predicates.

<a id="is3590"></a>

## IS3590 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3579–3590](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3579-L3590). Kind: rewrite.
- **Rewrite:** For exact UDiv or LShr results with the same divisor/shift amount, recursively compare their numerators when the predicate is unsigned.
- **Matched/replaced opcodes:** `icmp`, `udiv`, `lshr`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse>0; same opcode and second operand; both instructions exact; predicate unsigned; recursive result non-null.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires exact-flag inspection and recursive comparison.

<a id="is3598"></a>

## IS3598 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3592–3598](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3592-L3598). Kind: rewrite.
- **Rewrite:** For exact SDiv results with the same divisor, recursively compare their numerators only for EQ/NE.
- **Matched/replaced opcodes:** `icmp`, `sdiv`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse>0; same opcode and second operand; both exact; EQ or NE; recursive result non-null.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires exact-flag inspection and recursive comparison.

<a id="is3605"></a>

## IS3605 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3600–3605](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3600-L3605). Kind: rewrite.
- **Rewrite:** For exact AShr results with the same shift amount, recursively compare their inputs.
- **Matched/replaced opcodes:** `icmp`, `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse>0; same opcode and second operand; both exact; recursive result non-null.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires exact-flag inspection and recursive comparison.

<a id="is3616"></a>

## IS3616 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3607–3616](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3607-L3616). Kind: rewrite.
- **Rewrite:** For Shl results with the same shift amount, recursively compare their inputs when both shifts have NUW or both have NSW; signed predicates require NSW on both.
- **Matched/replaced opcodes:** `icmp`, `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse>0; same opcode and second operand; NUW or NSW on both; signed predicates require NSW; recursive result non-null.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires wrap-flag inspection and recursive comparison.

<a id="is3675"></a>

## IS3675 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3670–3675](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3670-L3675). Kind: delegation.
- **Rewrite:** After canonicalizing a signed smax/smin comparison against one of its own operands to `max(A,B) pred A` or its swapped-predicate equivalent for min, when P is EQ/SLE, return the comparison already used as condition by the LHS select if it exactly tests `A EqP B` (EqP is SGE for smax, SLE for smin).
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS is a select with matching predicate/operand orientation.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Bookkeeping/apparent-unreachable: min/max matchers only accept intrinsic calls, but extractEquivalentCondition only accepts select instructions. Existing manifest explains apparent cyclic SSA obstacle; this is not a proved global unreachability claim.

<a id="is3677"></a>

## IS3677 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3676–3677](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3676-L3677). Kind: delegation.
- **Rewrite:** After canonicalizing a signed smax/smin comparison against one of its own operands to `max(A,B) pred A` or its swapped-predicate equivalent for min, when P is EQ/SLE, otherwise reuse a matching `A EqP B` condition from the RHS select.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is a select with matching predicate/operand orientation.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Bookkeeping/apparent-unreachable: min/max matchers only accept intrinsic calls, but extractEquivalentCondition only accepts select instructions. Existing manifest explains apparent cyclic SSA obstacle; this is not a proved global unreachability claim.

<a id="is3681"></a>

## IS3681 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3678–3681](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3678-L3681). Kind: delegation.
- **Rewrite:** After canonicalizing a signed smax/smin comparison against one of its own operands to `max(A,B) pred A` or its swapped-predicate equivalent for min, when P is EQ/SLE, recursively simplify `icmp EqP A,B` and return it if it folds.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse>0; recursive result non-null.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Source returns only the result of a recursive simplifyICmpInst call, not a newly created comparison. Implementing this dispatcher requires a recursive simplification/result certificate and recursion budget contract absent from local Puddle Models; equivalent local comparison-creation schemas are not claimed as actual upstream rewrites.

<a id="is3689"></a>

## IS3689 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3683–3689](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3683-L3689). Kind: delegation.
- **Rewrite:** After canonicalizing a signed smax/smin comparison against one of its own operands to `max(A,B) pred A` or its swapped-predicate equivalent for min, when P is NE/SGT, return the LHS select condition if it exactly tests `A inverse(EqP) B`.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS is a select with matching inverse-predicate operand orientation.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Bookkeeping/apparent-unreachable: min/max matchers only accept intrinsic calls, but extractEquivalentCondition only accepts select instructions. Existing manifest explains apparent cyclic SSA obstacle; this is not a proved global unreachability claim.

<a id="is3691"></a>

## IS3691 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3690–3691](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3690-L3691). Kind: delegation.
- **Rewrite:** After canonicalizing a signed smax/smin comparison against one of its own operands to `max(A,B) pred A` or its swapped-predicate equivalent for min, when P is NE/SGT, otherwise reuse a matching `A inverse(EqP) B` condition from the RHS select.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is a select with matching inverse-predicate operand orientation.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Bookkeeping/apparent-unreachable: min/max matchers only accept intrinsic calls, but extractEquivalentCondition only accepts select instructions. Existing manifest explains apparent cyclic SSA obstacle; this is not a proved global unreachability claim.

<a id="is3695"></a>

## IS3695 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3692–3695](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3692-L3695). Kind: delegation.
- **Rewrite:** After canonicalizing a signed smax/smin comparison against one of its own operands to `max(A,B) pred A` or its swapped-predicate equivalent for min, when P is NE/SGT, recursively simplify `icmp inverse(EqP) A,B` and return it if it folds.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse>0; recursive result non-null.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Source returns only the result of a recursive simplifyICmpInst call, not a newly created comparison. Implementing this dispatcher requires a recursive simplification/result certificate and recursion budget contract absent from local Puddle Models; equivalent local comparison-creation schemas are not claimed as actual upstream rewrites.

<a id="is3700"></a>

## IS3700 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3698–3700](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3698-L3700). Kind: rewrite.
- **Rewrite:** After canonicalizing a signed smax/smin comparison against one of its own operands to `max(A,B) pred A` or its swapped-predicate equivalent for min, when normalized P is SGE, fold true because signed max/min ordering guarantees the selected operand relation.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — P==ICMP_SGE.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3700.lean](../../Veir/InstSimplify/IS3700.lean).
- **Theorems:** `Veir.InstSimplify.IS3700_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM min/max intrinsic comparison with all min/max, shared operand ordering, and comparison-side canonicalizations.

<a id="is3703"></a>

## IS3703 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3701–3703](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3701-L3703). Kind: rewrite.
- **Rewrite:** After canonicalizing a signed smax/smin comparison against one of its own operands to `max(A,B) pred A` or its swapped-predicate equivalent for min, when normalized P is SLT, fold false.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — P==ICMP_SLT.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3703.lean](../../Veir/InstSimplify/IS3703.lean).
- **Theorems:** `Veir.InstSimplify.IS3703_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM min/max intrinsic comparison with all min/max, shared operand ordering, and comparison-side canonicalizations.

<a id="is3749"></a>

## IS3749 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3744–3749](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3744-L3749). Kind: delegation.
- **Rewrite:** After canonicalizing an unsigned umax/umin comparison against one of its own operands to `max(A,B) pred A` or its swapped-predicate equivalent for min, when P is EQ/ULE, return the LHS select condition if it exactly tests `A EqP B` (EqP is UGE for umax, ULE for umin).
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS select condition predicate and operand orientation exactly match.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Bookkeeping/apparent-unreachable: min/max matchers only accept intrinsic calls, but extractEquivalentCondition only accepts select instructions. Existing manifest explains apparent cyclic SSA obstacle; this is not a proved global unreachability claim.

<a id="is3751"></a>

## IS3751 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3750–3751](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3750-L3751). Kind: delegation.
- **Rewrite:** After canonicalizing an unsigned umax/umin comparison against one of its own operands to `max(A,B) pred A` or its swapped-predicate equivalent for min, when P is EQ/ULE, otherwise reuse a matching `A EqP B` condition from the RHS select.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS select condition predicate and operand orientation exactly match.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Bookkeeping/apparent-unreachable: min/max matchers only accept intrinsic calls, but extractEquivalentCondition only accepts select instructions. Existing manifest explains apparent cyclic SSA obstacle; this is not a proved global unreachability claim.

<a id="is3755"></a>

## IS3755 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3752–3755](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3752-L3755). Kind: delegation.
- **Rewrite:** After canonicalizing an unsigned umax/umin comparison against one of its own operands to `max(A,B) pred A` or its swapped-predicate equivalent for min, when P is EQ/ULE, recursively simplify `icmp EqP A,B` and return it if it folds.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse>0; recursive result non-null.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Source returns only the result of a recursive simplifyICmpInst call, not a newly created comparison. Implementing this dispatcher requires a recursive simplification/result certificate and recursion budget contract absent from local Puddle Models; equivalent local comparison-creation schemas are not claimed as actual upstream rewrites.

<a id="is3763"></a>

## IS3763 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3757–3763](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3757-L3763). Kind: delegation.
- **Rewrite:** After canonicalizing an unsigned umax/umin comparison against one of its own operands to `max(A,B) pred A` or its swapped-predicate equivalent for min, when P is NE/UGT, return the LHS select condition if it exactly tests `A inverse(EqP) B`.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS select condition predicate and operand orientation exactly match.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Bookkeeping/apparent-unreachable: min/max matchers only accept intrinsic calls, but extractEquivalentCondition only accepts select instructions. Existing manifest explains apparent cyclic SSA obstacle; this is not a proved global unreachability claim.

<a id="is3765"></a>

## IS3765 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3764–3765](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3764-L3765). Kind: delegation.
- **Rewrite:** After canonicalizing an unsigned umax/umin comparison against one of its own operands to `max(A,B) pred A` or its swapped-predicate equivalent for min, when P is NE/UGT, otherwise reuse a matching `A inverse(EqP) B` condition from the RHS select.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS select condition predicate and operand orientation exactly match.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Bookkeeping/apparent-unreachable: min/max matchers only accept intrinsic calls, but extractEquivalentCondition only accepts select instructions. Existing manifest explains apparent cyclic SSA obstacle; this is not a proved global unreachability claim.

<a id="is3769"></a>

## IS3769 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3766–3769](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3766-L3769). Kind: delegation.
- **Rewrite:** After canonicalizing an unsigned umax/umin comparison against one of its own operands to `max(A,B) pred A` or its swapped-predicate equivalent for min, when P is NE/UGT, recursively simplify `icmp inverse(EqP) A,B` and return it if it folds.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse>0; recursive result non-null.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Source returns only the result of a recursive simplifyICmpInst call, not a newly created comparison. Implementing this dispatcher requires a recursive simplification/result certificate and recursion budget contract absent from local Puddle Models; equivalent local comparison-creation schemas are not claimed as actual upstream rewrites.

<a id="is3773"></a>

## IS3773 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3772–3773](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3772-L3773). Kind: rewrite.
- **Rewrite:** After canonicalizing an unsigned umax/umin comparison against one of its own operands to `max(A,B) pred A` or its swapped-predicate equivalent for min, when normalized P is UGE, fold true because unsigned max/min ordering guarantees the relation.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — P==ICMP_UGE.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3773.lean](../../Veir/InstSimplify/IS3773.lean).
- **Theorems:** `Veir.InstSimplify.IS3773_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM min/max intrinsic comparison with all min/max, shared operand ordering, and comparison-side canonicalizations.

<a id="is3775"></a>

## IS3775 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3774–3775](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3774-L3775). Kind: rewrite.
- **Rewrite:** After canonicalizing an unsigned umax/umin comparison against one of its own operands to `max(A,B) pred A` or its swapped-predicate equivalent for min, when normalized P is ULT, fold false.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — P==ICMP_ULT.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3775.lean](../../Veir/InstSimplify/IS3775.lean).
- **Theorems:** `Veir.InstSimplify.IS3775_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM min/max intrinsic comparison with all min/max, shared operand ordering, and comparison-side canonicalizations.

<a id="is3793"></a>

## IS3793 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3788–3793](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3788-L3793). Kind: rewrite.
- **Rewrite:** For signed `smax(A,B)` versus `smin(C,D)` sharing any operand, `smax(A,B) sge smin(C,D)` is true.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — At least one operand SSA-identical across min and max; predicate SGE.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3793.lean](../../Veir/InstSimplify/IS3793.lean).
- **Theorems:** `Veir.InstSimplify.IS3793_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM min/max intrinsic comparison with all min/max, shared operand ordering, and comparison-side canonicalizations.

<a id="is3796"></a>

## IS3796 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3794–3796](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3794-L3796). Kind: rewrite.
- **Rewrite:** For signed `smax(A,B)` versus `smin(C,D)` sharing any operand, `smax(A,B) slt smin(C,D)` is false.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — At least one operand SSA-identical across min and max; predicate SLT.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3796.lean](../../Veir/InstSimplify/IS3796.lean).
- **Theorems:** `Veir.InstSimplify.IS3796_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM min/max intrinsic comparison with all min/max, shared operand ordering, and comparison-side canonicalizations.

<a id="is3802"></a>

## IS3802 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3797–3802](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3797-L3802). Kind: rewrite.
- **Rewrite:** For unsigned `umax(A,B)` versus `umin(C,D)` sharing any operand, `umax(A,B) uge umin(C,D)` is true.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — At least one operand SSA-identical across min and max; predicate UGE.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3802.lean](../../Veir/InstSimplify/IS3802.lean).
- **Theorems:** `Veir.InstSimplify.IS3802_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM min/max intrinsic comparison with all min/max, shared operand ordering, and comparison-side canonicalizations.

<a id="is3805"></a>

## IS3805 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3803–3805](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3803-L3805). Kind: rewrite.
- **Rewrite:** For unsigned `umax(A,B)` versus `umin(C,D)` sharing any operand, `umax(A,B) ult umin(C,D)` is false.
- **Matched/replaced opcodes:** `icmp`, `call`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — At least one operand SSA-identical across min and max; predicate ULT.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3805.lean](../../Veir/InstSimplify/IS3805.lean).
- **Theorems:** `Veir.InstSimplify.IS3805_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM min/max intrinsic comparison with all min/max, shared operand ordering, and comparison-side canonicalizations.

<a id="is3827"></a>

## IS3827 — `simplifyICmpWithDominatingAssume`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3810–3831](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3810-L3831). Kind: rewrite.
- **Rewrite:** If a dominating, context-valid llvm.assume implies the queried comparison, replace it with the implied boolean result; the compare operands must be among the assumption bases and the assumption must validate for the current context.
- **Matched/replaced opcodes:** `icmp`, `call`.
- **Beyond opcode/constant/SSA matching:** Yes — AssumptionCache and dominance/context-validity analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires context-valid dominating llvm.assume facts, assumption cache and context dominance. Puddle local Models has no CFG context/assumption certificate.

<a id="is3846"></a>

## IS3846 — `simplifyICmpWithIntrinsicOnLHS`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3841–3846](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3841-L3846). Kind: rewrite.
- **Rewrite:** `uadd.sat(X,Y) uge X+Y` folds true.
- **Matched/replaced opcodes:** `icmp`, `call`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS uadd.sat; RHS add of the exact intrinsic arguments; predicate UGE.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3846.lean](../../Veir/InstSimplify/IS3846.lean).
- **Theorems:** `Veir.InstSimplify.IS3846_valid`.
- **Details / missing facilities:** Compiled arbitrary-width saturation-versus-wrapping arithmetic comparison, including all nsw/nuw flags, arithmetic commutation when applicable, and swapped comparison sides.

<a id="is3848"></a>

## IS3848 — `simplifyICmpWithIntrinsicOnLHS`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3841–3848](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3841-L3848). Kind: rewrite.
- **Rewrite:** `uadd.sat(X,Y) ult X+Y` folds false.
- **Matched/replaced opcodes:** `icmp`, `call`, `add`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS uadd.sat; RHS add of the exact intrinsic arguments; predicate ULT.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3848.lean](../../Veir/InstSimplify/IS3848.lean).
- **Theorems:** `Veir.InstSimplify.IS3848_valid`.
- **Details / missing facilities:** Compiled arbitrary-width saturation-versus-wrapping arithmetic comparison, including all nsw/nuw flags, arithmetic commutation when applicable, and swapped comparison sides.

<a id="is3856"></a>

## IS3856 — `simplifyICmpWithIntrinsicOnLHS`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3851–3856](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3851-L3856). Kind: rewrite.
- **Rewrite:** `usub.sat(X,Y) ule X−Y` folds true.
- **Matched/replaced opcodes:** `icmp`, `call`, `sub`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS usub.sat; RHS sub of exact intrinsic arguments; predicate ULE.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3856.lean](../../Veir/InstSimplify/IS3856.lean).
- **Theorems:** `Veir.InstSimplify.IS3856_valid`.
- **Details / missing facilities:** Compiled arbitrary-width saturation-versus-wrapping arithmetic comparison, including all nsw/nuw flags, arithmetic commutation when applicable, and swapped comparison sides.

<a id="is3858"></a>

## IS3858 — `simplifyICmpWithIntrinsicOnLHS`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3851–3858](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3851-L3858). Kind: rewrite.
- **Rewrite:** `usub.sat(X,Y) ugt X−Y` folds false.
- **Matched/replaced opcodes:** `icmp`, `call`, `sub`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS usub.sat; RHS sub of exact intrinsic arguments; predicate UGT.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3858.lean](../../Veir/InstSimplify/IS3858.lean).
- **Theorems:** `Veir.InstSimplify.IS3858_valid`.
- **Details / missing facilities:** Compiled arbitrary-width saturation-versus-wrapping arithmetic comparison, including all nsw/nuw flags, arithmetic commutation when applicable, and swapped comparison sides.

<a id="is3891"></a>

## IS3891 — `simplifyICmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3882–3891](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3882-L3891). Kind: rewrite.
- **Rewrite:** Constant-fold an ICmp when both operands are constants; if the constant folder cannot decide, continue into the remaining ICmp rules.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM constant-folding semantics and DataLayout/TargetLibraryInfo.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integer constants (integer literals, zero, poison); arbitrary widths and predicates.
- **Lean:** [Veir/InstSimplify/IS3891.lean](../../Veir/InstSimplify/IS3891.lean).
- **Theorems:** `Veir.InstSimplify.IS3891_valid`.
- **Details / missing facilities:** Compiled exhaustive scalar comparison constant folding, including integer/zero/poison literal representations and arbitrary widths/predicates.

<a id="is3907"></a>

## IS3907 — `simplifyICmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3903–3907](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3903-L3907). Kind: rewrite.
- **Rewrite:** A poison operand makes any ICmp result poison.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — poison semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3907.lean](../../Veir/InstSimplify/IS3907.lean).
- **Theorems:** `Veir.InstSimplify.IS3907_valid`.
- **Details / missing facilities:** Compiled LLVM scalar Puddle validity with arbitrary bitwidth and poison behavior.

<a id="is3913"></a>

## IS3913 — `simplifyICmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3909–3913](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3909-L3913). Kind: rewrite.
- **Rewrite:** For EQ or NE with an undef RHS, return undef because it can be chosen to make either outcome hold.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is undef; predicate equality.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** LLVM undef is absent from LLVM.Int, and Llvm.interpretOp' has no mlir__undef interpretation. No vacuous validity theorem is claimed.

<a id="is3918"></a>

## IS3918 — `simplifyICmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3915–3918](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3915-L3918). Kind: rewrite.
- **Rewrite:** `icmp pred X,X` folds to the predicate's truth value on equal operands. The distinct undef operand alternative is IS3918u.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS equals RHS or RHS is undef.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS3918.lean](../../Veir/InstSimplify/IS3918.lean).
- **Theorems:** `Veir.InstSimplify.IS3918_valid`.
- **Details / missing facilities:** Compiled scalar LLVM comparison Puddle validity; arbitrary widths and all specified predicates/poison behavior.

<a id="is3918u"></a>

## IS3918u — `simplifyICmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3915–3918](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3915-L3918). Kind: rewrite.
- **Rewrite:** `icmp pred X,undef` folds to the predicate's truth value on equal operands for non-equality predicates. EQ/NE with undef are handled earlier by IS3913.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS equals RHS or RHS is undef.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Details / missing facilities:** LLVM undef is not represented by LLVM.Int and mlir__undef has no successful interpretation in Llvm.interpretOp'. Poison is a distinct value and cannot substitute for undef. No vacuous Pattern.Valid proof from the missing interpreter case is claimed.

<a id="is3921"></a>

## IS3921 — `simplifyICmpOfBools`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3919–3921](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3919-L3921). Kind: delegation.
- **Rewrite:** Delegate to simplifyICmpOfBools and forward its non-null result.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — This return only forwards a non-null helper or analysis result.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Simple forwarder to separately inventoried helper cases; no distinct transformation or new semantic precondition at this return. Requires recursive helper or analysis semantics described in `extra`.

<a id="is3926"></a>

## IS3926 — `simplifyICmpWithZero`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3924–3926](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3924-L3926). Kind: delegation.
- **Rewrite:** Delegate to simplifyICmpWithZero and forward its non-null result.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — This return only forwards a non-null helper or analysis result.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Simple forwarder to separately inventoried helper cases; no distinct transformation or new semantic precondition at this return. Requires recursive helper or analysis semantics described in `extra`.

<a id="is3929"></a>

## IS3929 — `simplifyICmpWithConstant`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3927–3929](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3927-L3929). Kind: delegation.
- **Rewrite:** Delegate to simplifyICmpWithConstant and forward its non-null result.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — This return only forwards a non-null helper or analysis result.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Simple forwarder to separately inventoried helper cases; no distinct transformation or new semantic precondition at this return. Requires recursive helper or analysis semantics described in `extra`.

<a id="is3959"></a>

## IS3959 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3949–3959](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3949-L3959). Kind: delegation.
- **Rewrite:** For `ptrtoint/ptrtoaddr(P)` compared with integer constant C, if cast result type equals pointer address type, recursively compare P with `inttoptr(C)` using same predicate and return the folded result.
- **Matched/replaced opcodes:** `icmp`, `ptrtoint`, `ptrtoaddr`, `inttoptr`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse>0; DataLayout address type matches integer destination; RHS constant; recursive fold succeeds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires address-width/DataLayout pointer cast semantics plus recursive pointer comparison. Llvm.interpretOp' icmp accepts scalar integers only; no vacuous pointer proof is claimed.

<a id="is3966"></a>

## IS3966 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3949–3966](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3949-L3966). Kind: delegation.
- **Rewrite:** For same-address-width `ptrtoint/ptrtoaddr(P)` and `ptrtoint/ptrtoaddr(Q)` with equal source pointer types, recursively compare P and Q with same predicate.
- **Matched/replaced opcodes:** `icmp`, `ptrtoint`, `ptrtoaddr`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse>0; LHS address type matches destination; RHS same ptr cast family and source type exactly matches; recursive fold succeeds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires address-width/DataLayout pointer cast semantics plus recursive pointer comparison. Llvm.interpretOp' icmp accepts scalar integers only; no vacuous pointer proof is claimed.

<a id="is3979"></a>

## IS3979 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3970–3979](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3970-L3979). Kind: delegation.
- **Rewrite:** For `icmp pred (zext X),(zext Y)` with equal source types, recursively compare X and Y using the unsigned form of pred.
- **Matched/replaced opcodes:** `icmp`, `zext`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse>0; both operands zext; source types equal; recursive fold succeeds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Source returns only the result of a recursive simplifyICmpInst call, not a newly created comparison. Implementing this dispatcher requires a recursive simplification/result certificate and recursion budget contract absent from local Puddle Models; equivalent local comparison-creation schemas are not claimed as actual upstream rewrites.

<a id="is3985"></a>

## IS3985 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3981–3985](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3981-L3985). Kind: rewrite.
- **Rewrite:** For same-source `(zext X) ule (sext X)` or `(zext X) sge (sext X)`, fold true.
- **Matched/replaced opcodes:** `icmp`, `zext`, `sext`.
- **Beyond opcode/constant/SSA matching:** Yes — Source SSA value identical; predicate ULE or SGE.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers with arbitrary strict extension widths and signedness; all zext.nneg flags and signed/unsigned source predicates; vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS3985.lean](../../Veir/InstSimplify/IS3985.lean).
- **Theorems:** `Veir.InstSimplify.IS3985.valid`.
- **Details / missing facilities:** Compiled full mixed zero/sign-extension comparison family; source scalar comparison variants and reversed operands are parameterized.

<a id="is3987"></a>

## IS3987 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3981–3987](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3981-L3987). Kind: rewrite.
- **Rewrite:** For same-source `(zext X) ugt (sext X)` or `(zext X) slt (sext X)`, fold false.
- **Matched/replaced opcodes:** `icmp`, `zext`, `sext`.
- **Beyond opcode/constant/SSA matching:** Yes — Source SSA value identical; predicate UGT or SLT.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers with arbitrary strict extension widths and signedness; all zext.nneg flags and signed/unsigned source predicates; vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS3987.lean](../../Veir/InstSimplify/IS3987.lean).
- **Theorems:** `Veir.InstSimplify.IS3987.valid`.
- **Details / missing facilities:** Compiled full mixed zero/sign-extension comparison family; source scalar comparison variants and reversed operands are parameterized.

<a id="is4014"></a>

## IS4014 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:3990–4014](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L3990-L4014). Kind: delegation.
- **Rewrite:** For `(zext X) pred C`, if truncating and re-extending C to the LHS width leaves C unchanged, recursively compare X with truncated C using unsigned pred.
- **Matched/replaced opcodes:** `icmp`, `zext`, `trunc`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS integer constant; re-extension equals C in all lanes; MaxRecurse>0; recursive fold succeeds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Source returns only the result of a recursive simplifyICmpInst call, not a newly created comparison. Implementing this dispatcher requires a recursive simplification/result certificate and recursion budget contract absent from local Puddle Models; equivalent local comparison-creation schemas are not claimed as actual upstream rewrites.

<a id="is4026"></a>

## IS4026 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4016–4026](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4016-L4026). Kind: rewrite.
- **Rewrite:** For `(zext X) pred C` when truncation followed by zext changes C (so RHS has nonzero upper bits), predicates EQ, UGT and UGE are false.
- **Matched/replaced opcodes:** `icmp`, `zext`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS integer constant; truncated/reextended constant differs; predicate EQ/UGT/UGE.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar positive-width LLVM integer types of every width and signedness; actual extension semantics, all nneg/nsw/nuw flag combinations and poison behavior.
- **Lean:** [Veir/InstSimplify/IS4026.lean](../../Veir/InstSimplify/IS4026.lean), [Veir/InstSimplify/CmpCastSupport.lean](../../Veir/InstSimplify/CmpCastSupport.lean).
- **Theorems:** `Veir.InstSimplify.IS4026_valid`.
- **Details / missing facilities:** Exact native truncation/zero-reextension inequality certifies that every extended input is unsigned-less than the constant.

<a id="is4031"></a>

## IS4031 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4028–4031](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4028-L4031). Kind: rewrite.
- **Rewrite:** For `(zext X) pred C` when truncation followed by zext changes C, predicates NE, ULT and ULE are true.
- **Matched/replaced opcodes:** `icmp`, `zext`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS integer constant; truncated/reextended constant differs; predicate NE/ULT/ULE.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar positive-width LLVM integer source types of every width and signedness; actual zext/sext semantics and all modeled flags/poison behavior.
- **Lean:** [Veir/InstSimplify/IS4031.lean](../../Veir/InstSimplify/IS4031.lean), [Veir/InstSimplify/CmpCastSupport.lean](../../Veir/InstSimplify/CmpCastSupport.lean).
- **Theorems:** `Veir.InstSimplify.IS4031_valid`.
- **Details / missing facilities:** The native metadata guard exactly checks truncation followed by zero/sign reextension differs from the constant. The proof establishes the corresponding signed/unsigned range separation and folds every predicate in this branch.

<a id="is4037"></a>

## IS4037 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4033–4037](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4033-L4037). Kind: rewrite.
- **Rewrite:** For `(zext X) sgt|sge C` when C does not fit in source width, return the constant result of `C slt 0` (negative C means true, nonnegative C false).
- **Matched/replaced opcodes:** `icmp`, `zext`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS integer constant; truncated/reextended constant differs; predicate SGT or SGE; constant-fold signed C<0.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar positive-width LLVM integer source types of every width and signedness; actual zext/sext semantics and all modeled flags/poison behavior.
- **Lean:** [Veir/InstSimplify/IS4037.lean](../../Veir/InstSimplify/IS4037.lean), [Veir/InstSimplify/CmpCastSupport.lean](../../Veir/InstSimplify/CmpCastSupport.lean).
- **Theorems:** `Veir.InstSimplify.IS4037_valid`.
- **Details / missing facilities:** The native metadata guard exactly checks truncation followed by zero/sign reextension differs from the constant. The proof establishes signed range separation and folds both strict/non-strict predicates in this branch.

<a id="is4042"></a>

## IS4042 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4040–4042](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4040-L4042). Kind: rewrite.
- **Rewrite:** For `(zext X) slt|sle C` when C does not fit in source width, return the constant result of `C sge 0` (nonnegative C means true, negative C false).
- **Matched/replaced opcodes:** `icmp`, `zext`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS integer constant; truncated/reextended constant differs; predicate SLT or SLE; constant-fold signed C>=0.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar positive-width LLVM integer source types of every width and signedness; actual zext/sext semantics and all modeled flags/poison behavior.
- **Lean:** [Veir/InstSimplify/IS4042.lean](../../Veir/InstSimplify/IS4042.lean), [Veir/InstSimplify/CmpCastSupport.lean](../../Veir/InstSimplify/CmpCastSupport.lean).
- **Theorems:** `Veir.InstSimplify.IS4042_valid`.
- **Details / missing facilities:** The native metadata guard exactly checks truncation followed by zero/sign reextension differs from the constant. The proof establishes signed range separation and folds both strict/non-strict predicates in this branch.

<a id="is4058"></a>

## IS4058 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4050–4058](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4050-L4058). Kind: delegation.
- **Rewrite:** For `icmp pred (sext X),(sext Y)` with equal source types, recursively compare X and Y using the same predicate.
- **Matched/replaced opcodes:** `icmp`, `sext`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse>0; both operands sext; source types equal; recursive fold succeeds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Source returns only the result of a recursive simplifyICmpInst call, not a newly created comparison. Implementing this dispatcher requires a recursive simplification/result certificate and recursion budget contract absent from local Puddle Models; equivalent local comparison-creation schemas are not claimed as actual upstream rewrites.

<a id="is4064"></a>

## IS4064 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4060–4064](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4060-L4064). Kind: rewrite.
- **Rewrite:** For same-source `(sext X) uge (zext X)` or `(sext X) sle (zext X)`, fold true.
- **Matched/replaced opcodes:** `icmp`, `sext`, `zext`.
- **Beyond opcode/constant/SSA matching:** Yes — Source SSA value identical; predicate UGE or SLE.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers with arbitrary strict extension widths and signedness; all zext.nneg flags and signed/unsigned source predicates; vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS4064.lean](../../Veir/InstSimplify/IS4064.lean).
- **Theorems:** `Veir.InstSimplify.IS4064.valid`.
- **Details / missing facilities:** Compiled full mixed zero/sign-extension comparison family; source scalar comparison variants and reversed operands are parameterized.

<a id="is4066"></a>

## IS4066 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4060–4066](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4060-L4066). Kind: rewrite.
- **Rewrite:** For same-source `(sext X) ult (zext X)` or `(sext X) sgt (zext X)`, fold false.
- **Matched/replaced opcodes:** `icmp`, `sext`, `zext`.
- **Beyond opcode/constant/SSA matching:** Yes — Source SSA value identical; predicate ULT or SGT.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers with arbitrary strict extension widths and signedness; all zext.nneg flags and signed/unsigned source predicates; vector extension unmodeled.
- **Lean:** [Veir/InstSimplify/IS4066.lean](../../Veir/InstSimplify/IS4066.lean).
- **Theorems:** `Veir.InstSimplify.IS4066.valid`.
- **Details / missing facilities:** Compiled full mixed zero/sign-extension comparison family; source scalar comparison variants and reversed operands are parameterized.

<a id="is4091"></a>

## IS4091 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4069–4091](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4069-L4091). Kind: delegation.
- **Rewrite:** For `(sext X) pred C`, if truncating and re-extending C to LHS width leaves it unchanged, recursively compare X and truncated C with the same predicate.
- **Matched/replaced opcodes:** `icmp`, `sext`, `trunc`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS integer constant; re-extension equals C; MaxRecurse>0; recursive fold succeeds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Source returns only the result of a recursive simplifyICmpInst call, not a newly created comparison. Implementing this dispatcher requires a recursive simplification/result certificate and recursion budget contract absent from local Puddle Models; equivalent local comparison-creation schemas are not claimed as actual upstream rewrites.

<a id="is4100"></a>

## IS4100 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4093–4100](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4093-L4100). Kind: rewrite.
- **Rewrite:** For `(sext X) eq C` when truncation and re-extension changes C, fold false.
- **Matched/replaced opcodes:** `icmp`, `sext`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS integer constant; truncated/reextended constant differs; preferred predicate EQ.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar positive-width LLVM integer source types of every width and signedness; actual zext/sext semantics and all modeled flags/poison behavior.
- **Lean:** [Veir/InstSimplify/IS4100.lean](../../Veir/InstSimplify/IS4100.lean), [Veir/InstSimplify/CmpCastSupport.lean](../../Veir/InstSimplify/CmpCastSupport.lean).
- **Theorems:** `Veir.InstSimplify.IS4100_valid`.
- **Details / missing facilities:** The native metadata guard exactly checks truncation followed by zero/sign reextension differs from the constant. The proof establishes the corresponding signed/unsigned range separation and folds every predicate in this branch.

<a id="is4102"></a>

## IS4102 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4093–4102](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4093-L4102). Kind: rewrite.
- **Rewrite:** For `(sext X) ne C` when truncation and re-extension changes C, fold true.
- **Matched/replaced opcodes:** `icmp`, `sext`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS integer constant; truncated/reextended constant differs; preferred predicate NE.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar positive-width LLVM integer source types of every width and signedness; actual zext/sext semantics and all modeled flags/poison behavior.
- **Lean:** [Veir/InstSimplify/IS4102.lean](../../Veir/InstSimplify/IS4102.lean), [Veir/InstSimplify/CmpCastSupport.lean](../../Veir/InstSimplify/CmpCastSupport.lean).
- **Theorems:** `Veir.InstSimplify.IS4102_valid`.
- **Details / missing facilities:** The native metadata guard exactly checks truncation followed by zero/sign reextension differs from the constant. The proof establishes the corresponding signed/unsigned range separation and folds every predicate in this branch.

<a id="is4108"></a>

## IS4108 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4104–4108](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4104-L4108). Kind: rewrite.
- **Rewrite:** For `(sext X) sgt|sge C` when C does not fit source width, return the constant result of `C slt 0`.
- **Matched/replaced opcodes:** `icmp`, `sext`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS integer constant; re-extension differs; preferred signed predicate SGT or SGE; constant-fold C<0.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar positive-width LLVM integer source types of every width and signedness; actual zext/sext semantics and all modeled flags/poison behavior.
- **Lean:** [Veir/InstSimplify/IS4108.lean](../../Veir/InstSimplify/IS4108.lean), [Veir/InstSimplify/CmpCastSupport.lean](../../Veir/InstSimplify/CmpCastSupport.lean).
- **Theorems:** `Veir.InstSimplify.IS4108_valid`.
- **Details / missing facilities:** The native metadata guard exactly checks truncation followed by zero/sign reextension differs from the constant. The proof establishes signed range separation and folds both strict/non-strict predicates in this branch.

<a id="is4113"></a>

## IS4113 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4111–4113](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4111-L4113). Kind: rewrite.
- **Rewrite:** For `(sext X) slt|sle C` when C does not fit source width, return the constant result of `C sge 0`.
- **Matched/replaced opcodes:** `icmp`, `sext`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS integer constant; re-extension differs; preferred signed predicate SLT or SLE; constant-fold C>=0.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar positive-width LLVM integer source types of every width and signedness; actual zext/sext semantics and all modeled flags/poison behavior.
- **Lean:** [Veir/InstSimplify/IS4113.lean](../../Veir/InstSimplify/IS4113.lean), [Veir/InstSimplify/CmpCastSupport.lean](../../Veir/InstSimplify/CmpCastSupport.lean).
- **Theorems:** `Veir.InstSimplify.IS4113_valid`.
- **Details / missing facilities:** The native metadata guard exactly checks truncation followed by zero/sign reextension differs from the constant. The proof establishes signed range separation and folds both strict/non-strict predicates in this branch.

<a id="is4126"></a>

## IS4126 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4117–4126](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4117-L4126). Kind: delegation.
- **Rewrite:** For unsigned `(sext X) ugt|uge C` when C does not fit source width, recursively test whether X is signed-negative; that result is the original comparison result.
- **Matched/replaced opcodes:** `icmp`, `sext`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS integer constant; re-extension differs; predicate UGT or UGE; MaxRecurse>0; recursive `icmp slt X,0` succeeds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Source returns only the result of a recursive simplifyICmpInst call, not a newly created comparison. Implementing this dispatcher requires a recursive simplification/result certificate and recursion budget contract absent from local Puddle Models; equivalent local comparison-creation schemas are not claimed as actual upstream rewrites.

<a id="is4135"></a>

## IS4135 — `simplifyICmpInst cast handling`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4128–4135](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4128-L4135). Kind: delegation.
- **Rewrite:** For unsigned `(sext X) ult|ule C` when C does not fit source width, recursively test whether X is signed-nonnegative; that result is the original comparison result.
- **Matched/replaced opcodes:** `icmp`, `sext`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS integer constant; re-extension differs; predicate ULT or ULE; MaxRecurse>0; recursive `icmp sge X,0` succeeds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Source returns only the result of a recursive simplifyICmpInst call, not a newly created comparison. Implementing this dispatcher requires a recursive simplification/result certificate and recursion budget contract absent from local Puddle Models; equivalent local comparison-creation schemas are not claimed as actual upstream rewrites.

<a id="is4148"></a>

## IS4148 — `simplifyICmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4143–4148](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4143-L4148). Kind: rewrite.
- **Rewrite:** For EQ/NE comparisons other than against zero, if value tracking proves operands non-equal, return false for EQ and true for NE.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — isKnownNonEqual value analysis; deliberately skips zero RHS.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires isKnownNonEqual value analysis.

<a id="is4152"></a>

## IS4152 — `simplifyICmpWithBinOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4150–4152](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4150-L4152). Kind: delegation.
- **Rewrite:** Delegate to simplifyICmpWithBinOp and forward its non-null result.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — This return only forwards a non-null helper or analysis result.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Simple forwarder to separately inventoried helper cases; no distinct transformation or new semantic precondition at this return. Requires recursive helper or analysis semantics described in `extra`.

<a id="is4155"></a>

## IS4155 — `simplifyICmpWithMinMax`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4153–4155](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4153-L4155). Kind: delegation.
- **Rewrite:** Delegate to simplifyICmpWithMinMax and forward its non-null result.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — This return only forwards a non-null helper or analysis result.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Simple forwarder to separately inventoried helper cases; no distinct transformation or new semantic precondition at this return. Requires recursive helper or analysis semantics described in `extra`.

<a id="is4158"></a>

## IS4158 — `simplifyICmpWithIntrinsicOnLHS`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4156–4158](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4156-L4158). Kind: delegation.
- **Rewrite:** Delegate with original predicate and operand order to simplifyICmpWithIntrinsicOnLHS; forward its result.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — This return only forwards a non-null helper or analysis result.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Simple forwarder to simplifyICmpWithIntrinsicOnLHS; all concrete saturating-comparison callees IS3846/3848/3856/3858 are separately marked proved.

<a id="is4161"></a>

## IS4161 — `simplifyICmpWithIntrinsicOnLHS`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4159–4161](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4159-L4161). Kind: delegation.
- **Rewrite:** Delegate with swapped predicate and operands to simplifyICmpWithIntrinsicOnLHS; forward its result.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — This return only forwards a non-null helper or analysis result.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Same saturating-comparison helper as IS4158 after operand/predicate swap; all four concrete callees are separately marked proved.

<a id="is4164"></a>

## IS4164 — `simplifyICmpUsingMonotonicValues`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4162–4164](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4162-L4164). Kind: delegation.
- **Rewrite:** Delegate with original predicate and operands to simplifyICmpUsingMonotonicValues; forward its result.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — This return only forwards a non-null helper or analysis result.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Simple forwarder to separately inventoried helper cases; no distinct transformation or new semantic precondition at this return. Requires recursive helper or analysis semantics described in `extra`.

<a id="is4167"></a>

## IS4167 — `simplifyICmpUsingMonotonicValues`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4165–4167](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4165-L4167). Kind: delegation.
- **Rewrite:** Delegate with swapped predicate and operands to simplifyICmpUsingMonotonicValues; forward its result.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — This return only forwards a non-null helper or analysis result.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Simple forwarder to separately inventoried helper cases; no distinct transformation or new semantic precondition at this return. Requires recursive helper or analysis semantics described in `extra`.

<a id="is4170"></a>

## IS4170 — `simplifyICmpWithDominatingAssume`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4168–4170](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4168-L4170). Kind: delegation.
- **Rewrite:** Delegate to simplifyICmpWithDominatingAssume and forward its non-null result.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — This return only forwards a non-null helper or analysis result.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Simple forwarder to separately inventoried helper cases; no distinct transformation or new semantic precondition at this return. Requires recursive helper or analysis semantics described in `extra`.

<a id="is4174"></a>

## IS4174 — `isImpliedByDomCondition`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4172–4174](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4172-L4174). Kind: delegation.
- **Rewrite:** If context dominance analysis proves the ICmp result, return that boolean as an i1 constant.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — This return only forwards a non-null helper or analysis result.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Frozen source lines 4172-4174 convert isImpliedByDomCondition into a boolean; requires a certified dominance/context analysis result, not a recursive comparison contract.

<a id="is4180"></a>

## IS4180 — `simplifyICmpInst pointer comparison delegation`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4176–4180](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4176-L4180). Kind: delegation.
- **Rewrite:** For pointer-typed operands, delegate related-pointer comparison reasoning to computePointerICmp and return its constant result; concrete pointer rewrite branches are inventoried under IS2803, IS2827, IS2855 and IS2895.
- **Matched/replaced opcodes:** `icmp`, `getelementptr`.
- **Beyond opcode/constant/SSA matching:** Yes — DataLayout and computePointerICmp.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Plain computePointerICmp forwarder in frozen source lines 4178-4180. All concrete pointer branches are separately inventoried at IS2803/2827/2855/2895; this return introduces no additional rewrite boundary.

<a id="is4186"></a>

## IS4186 — `simplifyICmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4182–4186](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4182-L4186). Kind: delegation.
- **Rewrite:** If either ICmp operand is a select and threadCmpOverSelect proves both select paths yield the same comparison result, forward that value.
- **Matched/replaced opcodes:** `icmp`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse; select threading helper proves common result.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Frozen helper at lines 433-474 recursively simplifies the comparison on both select arms and combines results; requires recursive/contextual simplification correctness.

<a id="is4192"></a>

## IS4192 — `simplifyICmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4188–4192](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4188-L4192). Kind: delegation.
- **Rewrite:** If either ICmp operand is a PHI and threadCmpOverPHI proves all incoming comparisons yield a common result, forward that value.
- **Matched/replaced opcodes:** `icmp`, `phi`.
- **Beyond opcode/constant/SSA matching:** Yes — MaxRecurse; PHI threading helper proves common result.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Frozen helper at lines 525-567 evaluates PHI incoming operands in predecessor-edge contexts and checks dominance plus recursive common results; missing PHI/CFG semantics is primary.

<a id="is4214"></a>

## IS4214 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4209–4214](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4209-L4214). Kind: rewrite.
- **Rewrite:** When both FCmp operands are constants, return the result of ConstantFoldCompareInstOperands if the constant folder can decide it.
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — ConstantFoldCompareInstOperands with DataLayout, TLI and optional Function.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4225"></a>

## IS4225 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4222–4225](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4222-L4225). Kind: rewrite.
- **Rewrite:** `fcmp false, X, Y` folds to false.
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate FCMP_FALSE.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4227"></a>

## IS4227 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4222–4227](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4222-L4227). Kind: rewrite.
- **Rewrite:** `fcmp true, X, Y` folds to true.
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate FCMP_TRUE.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4232"></a>

## IS4232 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4229–4232](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4229-L4232). Kind: rewrite.
- **Rewrite:** Any FCmp with either operand poison folds to poison.
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — Either operand is PoisonValue.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4239"></a>

## IS4239 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4234–4239](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4234-L4239). Kind: rewrite.
- **Rewrite:** Any FCmp with an undef operand folds to the predicate’s unordered truth value: true for unordered predicates, false for ordered predicates.
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — At least one operand undef; may choose NaN.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4245"></a>

## IS4245 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4242–4245](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4242-L4245). Kind: rewrite.
- **Rewrite:** When comparing a value with itself, fold to true if the FCmp predicate is true when operands are equal.
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS==RHS; predicate true-when-equal classification.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4247"></a>

## IS4247 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4242–4247](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4242-L4247). Kind: rewrite.
- **Rewrite:** When comparing a value with itself, fold to false if the FCmp predicate is false when operands are equal.
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS==RHS; predicate false-when-equal classification.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4260"></a>

## IS4260 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4250–4260](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4250-L4260). Kind: rewrite.
- **Rewrite:** For ORD/UNO comparison, fold to true for ORD or false for UNO when FMF says noNaNs, or both operands are known never NaN.
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate ORD or UNO; noNaNs FMF or KnownFPClass never-NaN facts.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4263"></a>

## IS4263 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4250–4263](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4250-L4263). Kind: rewrite.
- **Rewrite:** For ORD/UNO comparison, fold to false for ORD or true for UNO when either operand is known always NaN.
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate ORD or UNO; KnownFPClass always-NaN.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4268"></a>

## IS4268 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4266–4268](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4266-L4268). Kind: delegation.
- **Rewrite:** If a dominating condition implies the FCmp predicate for these operands, return its implied boolean result.
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — isImpliedByDomCondition succeeds for current context.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4290"></a>

## IS4290 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4283–4290](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4283-L4290). Kind: rewrite.
- **Rewrite:** When function context lets fcmpToClassTest recognize the comparison as an FP-class test, fold false if known LHS classes are disjoint from the tested class.
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS FP constant; function context; class-test recognized; KnownFPClass intersection is empty.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4292"></a>

## IS4292 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4283–4292](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4283-L4292). Kind: rewrite.
- **Rewrite:** When function context lets fcmpToClassTest recognize the comparison as an FP-class test, fold true if every known LHS class belongs to the tested class.
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS FP constant; function context; class-test recognized; no known classes outside ClassTest.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4301"></a>

## IS4301 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4296–4301](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4296-L4301). Kind: rewrite.
- **Rewrite:** For a NaN constant RHS, fold to whether the FCmp predicate is unordered.
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is a NaN APFloat constant.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4319"></a>

## IS4319 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4306–4319](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4306-L4319). Kind: rewrite.
- **Rewrite:** For negative nonzero constant C and predicate UGE, UGT or UNE, fold `X pred C` true when X cannot be an ordered negative value (i.e. is nonnegative or NaN).
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — C negative and not −0; KnownFPClass cannotBeOrderedLessThanZero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4329"></a>

## IS4329 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4322–4329](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4322-L4329). Kind: rewrite.
- **Rewrite:** For negative nonzero constant C and predicate OEQ, OLE or OLT, fold `X pred C` false when X cannot be an ordered negative value.
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — C negative and not −0; KnownFPClass cannotBeOrderedLessThanZero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4349"></a>

## IS4349 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4340–4349](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4340-L4349). Kind: rewrite.
- **Rewrite:** For `fmaxnum/fmaximum(X,C2)` with C2>C, or `fminnum/fminimum(X,C2)` with C2<C, OEQ and UEQ against C fold false.
- **Matched/replaced opcodes:** `fcmp`, `call`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS matches relevant min/max intrinsic with fixed constant C2; strict ordered relation C2>C for max or C2<C for min.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4354"></a>

## IS4354 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4340–4354](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4340-L4354). Kind: rewrite.
- **Rewrite:** Under the same fixed-constant min/max ordering, ONE and UNE against C fold true.
- **Matched/replaced opcodes:** `fcmp`, `call`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS matches relevant min/max intrinsic with fixed constant C2; strict ordered relation.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4363"></a>

## IS4363 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4340–4363](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4340-L4363). Kind: rewrite.
- **Rewrite:** Under the same fixed-constant min/max ordering, OGE/UGE/OGT/UGT against C fold to IsMax: true for max, false for min.
- **Matched/replaced opcodes:** `fcmp`, `call`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS matches relevant min/max intrinsic with fixed constant C2; strict ordered relation.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4372"></a>

## IS4372 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4340–4372](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4340-L4372). Kind: rewrite.
- **Rewrite:** Under the same fixed-constant min/max ordering, OLE/ULE/OLT/ULT against C fold to !IsMax: false for max, true for min.
- **Matched/replaced opcodes:** `fcmp`, `call`.
- **Beyond opcode/constant/SSA matching:** Yes — LHS matches relevant min/max intrinsic with fixed constant C2; strict ordered relation.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4396"></a>

## IS4396 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4382–4396](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4382-L4396). Kind: rewrite.
- **Rewrite:** For RHS either signed zero, OGE X,0 folds true and ULT X,0 folds false when X has no ordered-negative values and is known never NaN or FMF noNaNs.
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is any zero FP constant; KnownFPClass cannotBeOrderedLessThanZero; FMF noNaNs or never-NaN.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4407"></a>

## IS4407 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4399–4407](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4399-L4407). Kind: rewrite.
- **Rewrite:** For RHS either signed zero, UGE X,0 folds true and OLT X,0 folds false when X has no ordered-negative values; NaNs are permitted by these unordered predicates.
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — RHS is any zero FP constant; KnownFPClass cannotBeOrderedLessThanZero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4419"></a>

## IS4419 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4415–4419](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4415-L4419). Kind: delegation.
- **Rewrite:** If either FCmp operand is a select and threadCmpOverSelect proves both select paths yield the same comparison result, forward that value.
- **Matched/replaced opcodes:** `fcmp`, `select`.
- **Beyond opcode/constant/SSA matching:** Yes — FastMathFlags; MaxRecurse; select threading helper proves common result.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4425"></a>

## IS4425 — `simplifyFCmpInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4421–4425](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4421-L4425). Kind: delegation.
- **Rewrite:** If either FCmp operand is a PHI and threadCmpOverPHI proves all incoming comparisons yield a common result, forward that value.
- **Matched/replaced opcodes:** `fcmp`, `phi`.
- **Beyond opcode/constant/SSA matching:** Yes — FastMathFlags; MaxRecurse; PHI threading helper proves common result.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is4450"></a>

## IS4450 — `simplifyWithOpsReplaced`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4443–4450](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4443-L4450). Kind: schema.
- **Rewrite:** When the current value V is exactly a nonconstant replacement key Op, return its replacement RepOp.
- **Matched/replaced opcodes:** `any instruction or SSA value`.
- **Beyond opcode/constant/SSA matching:** Yes — Op is not a Constant; exact SSA identity.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Operand-substitution helper returns its caller-provided RepOp when V equals Op. This is not an independent semantically valid replacement without the condition/substitution context; concrete conditional select callers are inventoried separately.

<a id="is4513"></a>

## IS4513 — `simplifyWithOpsReplaced`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4507–4513](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4507-L4513). Kind: schema.
- **Rewrite:** With refinement disabled, fold a non-FP binary operation `identity op X` to X after operand substitution.
- **Matched/replaced opcodes:** `and`, `or`, `xor`, `add`, `sub`, `mul`, `udiv`, `sdiv`, `urem`, `srem`, `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — BinaryOperator result is not FP; substituted left operand equals opcode identity; no refinement.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Internal simplifyWithOpsReplaced helper branch under caller-provided replacement map and AllowRefinement/DropFlags policy. Replacement keys/values are condition-derived, and operation poison/flag-removal obligations must remain tied to the surrounding select context. It is not an independent local IR rewrite with arbitrary replacement operands. A contextual substitution/result certificate and recursive helper contract are absent from Puddle Models; concrete select callers are inventoried separately.

<a id="is4516"></a>

## IS4516 — `simplifyWithOpsReplaced`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4514–4516](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4514-L4516). Kind: schema.
- **Rewrite:** With refinement disabled, fold a non-FP binary operation `X op identity_rhs` to X after operand substitution.
- **Matched/replaced opcodes:** `and`, `or`, `xor`, `add`, `sub`, `mul`, `udiv`, `sdiv`, `urem`, `srem`, `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — BinaryOperator result is not FP; substituted right operand equals opcode RHS identity; no refinement.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Internal simplifyWithOpsReplaced helper branch under caller-provided replacement map and AllowRefinement/DropFlags policy. Replacement keys/values are condition-derived, and operation poison/flag-removal obligations must remain tied to the surrounding select context. It is not an independent local IR rewrite with arbitrary replacement operands. A contextual substitution/result certificate and recursive helper contract are absent from Puddle Models; concrete select callers are inventoried separately.

<a id="is4530"></a>

## IS4530 — `simplifyWithOpsReplaced`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4519–4530](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4519-L4530). Kind: schema.
- **Rewrite:** With refinement disabled, fold `X and X` or `X or X` to X after substitution; if the operation is disjoint-flagged OR, only do so when DropFlags is provided and the flag is queued for removal.
- **Matched/replaced opcodes:** `and`, `or`.
- **Beyond opcode/constant/SSA matching:** Yes — Both substituted operands identical; disjoint OR requires DropFlags and queues BO.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Internal simplifyWithOpsReplaced helper branch under caller-provided replacement map and AllowRefinement/DropFlags policy. Replacement keys/values are condition-derived, and operation poison/flag-removal obligations must remain tied to the surrounding select context. It is not an independent local IR rewrite with arbitrary replacement operands. A contextual substitution/result certificate and recursive helper contract are absent from Puddle Models; concrete select callers are inventoried separately.

<a id="is4539"></a>

## IS4539 — `simplifyWithOpsReplaced`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4533–4539](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4533-L4539). Kind: schema.
- **Rewrite:** With refinement disabled, fold `X−X` or `X xor X` to zero after substitution when X is a replacement value.
- **Matched/replaced opcodes:** `sub`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — Both substituted operands identical and equal a replacement RepOp; no refinement; expression never wraps for Sub.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Internal simplifyWithOpsReplaced helper branch under caller-provided replacement map and AllowRefinement/DropFlags policy. Replacement keys/values are condition-derived, and operation poison/flag-removal obligations must remain tied to the surrounding select context. It is not an independent local IR rewrite with arbitrary replacement operands. A contextual substitution/result certificate and recursive helper contract are absent from Puddle Models; concrete select callers are inventoried separately.

<a id="is4552"></a>

## IS4552 — `simplifyWithOpsReplaced`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4541–4552](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4541-L4552). Kind: schema.
- **Rewrite:** With refinement disabled, replace a binary operation by its absorber constant after substitution when one operand is the absorber and some replaced operand implies poison for the original operation (so removing the select cannot expose extra poison).
- **Matched/replaced opcodes:** `and`, `or`, `xor`, `add`, `sub`, `mul`, `udiv`, `sdiv`, `urem`, `srem`, `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — One substituted operand is getBinOpAbsorber; impliesPoison(BO, original replacement key) for some Ops entry.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Internal simplifyWithOpsReplaced helper branch under caller-provided replacement map and AllowRefinement/DropFlags policy. Replacement keys/values are condition-derived, and operation poison/flag-removal obligations must remain tied to the surrounding select context. It is not an independent local IR rewrite with arbitrary replacement operands. A contextual substitution/result certificate and recursive helper contract are absent from Puddle Models; concrete select callers are inventoried separately.

<a id="is4568"></a>

## IS4568 — `simplifyWithOpsReplaced`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4555–4568](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4555-L4568). Kind: schema.
- **Rewrite:** With refinement disabled, `scmp(X,X)` or `ucmp(X,X)` after substitution folds to zero; if the intrinsic has poison-generating annotations, require DropFlags and queue the intrinsic for flag removal.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — Intrinsic is scmp or ucmp; substituted args equal; poison annotations handled by DropFlags.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Internal simplifyWithOpsReplaced helper branch under caller-provided replacement map and AllowRefinement/DropFlags policy. Replacement keys/values are condition-derived, and operation poison/flag-removal obligations must remain tied to the surrounding select context. It is not an independent local IR rewrite with arbitrary replacement operands. A contextual substitution/result certificate and recursive helper contract are absent from Puddle Models; concrete select callers are inventoried separately.

<a id="is4588"></a>

## IS4588 — `simplifyWithOpsReplaced`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4571–4588](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4571-L4588). Kind: schema.
- **Rewrite:** With refinement disabled, an integer min/max intrinsic with one substituted argument equal to its identity returns the other argument; poison annotations require and record DropFlags.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — MinMaxIntrinsic identity; substituted operand matches identity; poison annotations handled by DropFlags.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Internal simplifyWithOpsReplaced helper branch under caller-provided replacement map and AllowRefinement/DropFlags policy. Replacement keys/values are condition-derived, and operation poison/flag-removal obligations must remain tied to the surrounding select context. It is not an independent local IR rewrite with arbitrary replacement operands. A contextual substitution/result certificate and recursive helper contract are absent from Puddle Models; concrete select callers are inventoried separately.

<a id="is4597"></a>

## IS4597 — `simplifyWithOpsReplaced`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4593–4597](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4593-L4597). Kind: schema.
- **Rewrite:** With refinement disabled, `getelementptr X, 0` folds to X, including inbounds GEP because zero offset is non-poison.
- **Matched/replaced opcodes:** `getelementptr`.
- **Beyond opcode/constant/SSA matching:** Yes — Instruction is GEP; exactly two operands; substituted index is zero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Internal simplifyWithOpsReplaced helper branch under caller-provided replacement map and AllowRefinement/DropFlags policy. Replacement keys/values are condition-derived, and operation poison/flag-removal obligations must remain tied to the surrounding select context. It is not an independent local IR rewrite with arbitrary replacement operands. A contextual substitution/result certificate and recursive helper contract are absent from Puddle Models; concrete select callers are inventoried separately. Additionally, scalar pointer GEP memory semantics are outside this integer comparison port.

<a id="is4613"></a>

## IS4613 — `simplifyWithOpsReplaced`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4599–4613](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4599-L4613). Kind: delegation.
- **Rewrite:** With refinement enabled, simplify the instruction with substituted operands and return the result unless it is the original value itself.
- **Matched/replaced opcodes:** `any instruction`.
- **Beyond opcode/constant/SSA matching:** Yes — AllowRefinement=true; recursive simplifyInstructionWithOperands; result differs from V.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Internal simplifyWithOpsReplaced helper branch under caller-provided replacement map and AllowRefinement/DropFlags policy. Replacement keys/values are condition-derived, and operation poison/flag-removal obligations must remain tied to the surrounding select context. It is not an independent local IR rewrite with arbitrary replacement operands. A contextual substitution/result certificate and recursive helper contract are absent from Puddle Models; concrete select callers are inventoried separately.

<a id="is4666"></a>

## IS4666 — `simplifyWithOpsReplaced`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4636–4666](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4636-L4666). Kind: delegation.
- **Rewrite:** With refinement disabled and all substituted operands constant, constant-fold the instruction only if it cannot produce poison, except abs is allowed when its argument is not signed minimum; if DropFlags applies, poison-generating annotations are queued for removal.
- **Matched/replaced opcodes:** `any constant-foldable instruction`.
- **Beyond opcode/constant/SSA matching:** Yes — All operands constant; canCreatePoison constraints; abs signed-min guard; ConstantFoldInstOperands; optional DropFlags.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Internal simplifyWithOpsReplaced helper branch under caller-provided replacement map and AllowRefinement/DropFlags policy. Replacement keys/values are condition-derived, and operation poison/flag-removal obligations must remain tied to the surrounding select context. It is not an independent local IR rewrite with arbitrary replacement operands. A contextual substitution/result certificate and recursive helper contract are absent from Puddle Models; concrete select callers are inventoried separately.

<a id="is4669"></a>

## IS4669 — `simplifyWithOpsReplaced`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4667–4669](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4667-L4669). Kind: delegation.
- **Rewrite:** With refinement enabled and all substituted operands constant, return ConstantFoldInstOperands result with nondeterministic folding disabled.
- **Matched/replaced opcodes:** `any constant-foldable instruction`.
- **Beyond opcode/constant/SSA matching:** Yes — All operands constant; ConstantFoldInstOperands allow nondeterministic=false.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Internal simplifyWithOpsReplaced helper branch under caller-provided replacement map and AllowRefinement/DropFlags policy. Replacement keys/values are condition-derived, and operation poison/flag-removal obligations must remain tied to the surrounding select context. It is not an independent local IR rewrite with arbitrary replacement operands. A contextual substitution/result certificate and recursive helper contract are absent from Puddle Models; concrete select callers are inventoried separately.

<a id="is4705"></a>

## IS4705 — `simplifySelectBitTest`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4701–4705](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4701-L4705). Kind: rewrite.
- **Rewrite:** For a bit test `(X & Y)==0` or `!=0`, if false arm is X and true arm is `X & C` with `Y == ~C`, choose X when the tested condition is true-when-unset, otherwise choose `X & C`.
- **Matched/replaced opcodes:** `select`, `icmp`, `and`.
- **Beyond opcode/constant/SSA matching:** Yes — exact X SSA match; APInt mask complement; TrueWhenUnset derived from EQ/NE.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS4705.lean](../../Veir/InstSimplify/IS4705.lean).
- **Theorems:** `Veir.InstSimplify.IS4705_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar bit-test select with all complement/power-of-two, polarity, and disjoint guards.

<a id="is4711"></a>

## IS4711 — `simplifySelectBitTest`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4707–4711](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4707-L4711). Kind: rewrite.
- **Rewrite:** For a bit test `(X & Y)==0` or `!=0`, if true arm is X and false arm is `X & C` with `Y == ~C`, choose `X & C` when the tested condition is true-when-unset, otherwise choose X.
- **Matched/replaced opcodes:** `select`, `icmp`, `and`.
- **Beyond opcode/constant/SSA matching:** Yes — exact X SSA match; APInt mask complement; TrueWhenUnset derived from EQ/NE.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS4711.lean](../../Veir/InstSimplify/IS4711.lean).
- **Theorems:** `Veir.InstSimplify.IS4711_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar bit-test select with all complement/power-of-two, polarity, and disjoint guards.

<a id="is4721"></a>

## IS4721 — `simplifySelectBitTest`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4713–4721](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4713-L4721). Kind: rewrite.
- **Rewrite:** For power-of-two mask Y, false arm X and true arm `X|Y`, choose the OR when true means the tested bit is unset, otherwise choose X.
- **Matched/replaced opcodes:** `select`, `icmp`, `and`, `or`.
- **Beyond opcode/constant/SSA matching:** Yes — Y is power of two; exact X match; Y equals OR constant; reject disjoint OR when returning it for TrueWhenUnset.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS4721.lean](../../Veir/InstSimplify/IS4721.lean).
- **Theorems:** `Veir.InstSimplify.IS4721_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM Puddle validity with exact upstream numeric and poison-generating flag guards.

<a id="is4731"></a>

## IS4731 — `simplifySelectBitTest`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4724–4731](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4724-L4731). Kind: rewrite.
- **Rewrite:** For power-of-two mask Y, true arm X and false arm `X|Y`, choose X when true means the tested bit is unset, otherwise choose the OR.
- **Matched/replaced opcodes:** `select`, `icmp`, `and`, `or`.
- **Beyond opcode/constant/SSA matching:** Yes — Y is power of two; exact X match; Y equals OR constant; reject disjoint OR when returning it for !TrueWhenUnset.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS4731.lean](../../Veir/InstSimplify/IS4731.lean).
- **Theorems:** `Veir.InstSimplify.IS4731_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM Puddle validity with exact upstream numeric and poison-generating flag guards.

<a id="is4785"></a>

## IS4785 — `simplifyCmpSelOfMaxMin`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4768–4785](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4768-L4785). Kind: rewrite.
- **Rewrite:** For `(X pred Y) ? X : max/min(X,Y)`, return the min/max intrinsic when its predicate equals `getStrictPredicate(pred)`; this also allows the recognized select-shuffle case.
- **Matched/replaced opcodes:** `select`, `icmp`, `call`, `shufflevector`.
- **Beyond opcode/constant/SSA matching:** Yes — true arm canonicalized to X; false arm min/max(X,Y); MMI predicate equals strict predicate.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS4785.lean](../../Veir/InstSimplify/IS4785.lean).
- **Theorems:** `Veir.InstSimplify.IS4785_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM Puddle validity, all upstream scalar canonicalization variants and predicates.

<a id="is4793"></a>

## IS4793 — `simplifyCmpSelOfMaxMin`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4791–4793](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4791-L4793). Kind: rewrite.
- **Rewrite:** For `(X == Y) ? X : max/min(X,Y)`, return the min/max intrinsic.
- **Matched/replaced opcodes:** `select`, `icmp`, `call`.
- **Beyond opcode/constant/SSA matching:** Yes — Canonicalized X/Y arms; no select-shuffle peek-through.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS4793.lean](../../Veir/InstSimplify/IS4793.lean).
- **Theorems:** `Veir.InstSimplify.IS4793_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM Puddle validity, all upstream scalar canonicalization variants and predicates.

<a id="is4797"></a>

## IS4797 — `simplifyCmpSelOfMaxMin`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4795–4797](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4795-L4797). Kind: rewrite.
- **Rewrite:** For `(X != Y) ? X : max/min(X,Y)`, return X.
- **Matched/replaced opcodes:** `select`, `icmp`, `call`.
- **Beyond opcode/constant/SSA matching:** Yes — Canonicalized X/Y arms; no select-shuffle peek-through.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS4797.lean](../../Veir/InstSimplify/IS4797.lean).
- **Theorems:** `Veir.InstSimplify.IS4797_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM Puddle validity, all upstream scalar canonicalization variants and predicates.

<a id="is4805"></a>

## IS4805 — `simplifyCmpSelOfMaxMin`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4799–4805](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4799-L4805). Kind: rewrite.
- **Rewrite:** For `(X pred Y) ? X : max/min(X,Y)`, return X when the min/max predicate equals the strict predicate of the inverse compare predicate.
- **Matched/replaced opcodes:** `select`, `icmp`, `call`.
- **Beyond opcode/constant/SSA matching:** Yes — Canonicalized X/Y arms; no select-shuffle peek-through.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS4805.lean](../../Veir/InstSimplify/IS4805.lean).
- **Theorems:** `Veir.InstSimplify.IS4805_valid`.
- **Details / missing facilities:** Compiled arbitrary-width scalar LLVM Puddle validity, all upstream scalar canonicalization variants and predicates.

<a id="is4815"></a>

## IS4815 — `simplifySelectWithBitTest`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4810–4818](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4810-L4818). Kind: delegation.
- **Rewrite:** If decomposeBitTest recognizes the condition as a bit test, delegate to simplifySelectBitTest with the decomposed X, mask, and equality polarity; the concrete select equations and disjoint-OR guards are inventoried separately under IS4705.
- **Matched/replaced opcodes:** `select`, `icmp`, `and`, `or`.
- **Beyond opcode/constant/SSA matching:** Yes — decomposeBitTest analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires decomposeBitTest correctness before forwarding; underlying bit-test select equations IS4705/4711/4721/4731 are proved.

<a id="is4841"></a>

## IS4841 — `simplifySelectWithEquivalence`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4835–4843](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4835-L4843). Kind: schema.
- **Rewrite:** Given condition-derived operand replacements, simplify both select arms after replacement; return the original false arm if the resulting arms are identical. False arm uses no-undef and no-refinement simplification; true arm permits refinement; only exact pointer-equality replacements allowed by caller.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive operand substitution, refinement/undef semantics, pointer equality legality.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Depends on recursive substitution and poison/refinement handling; pointer replacement additionally requires equality legality analysis.

<a id="is4858"></a>

## IS4858 — `simplifySelectWithICmpCond`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4857–4858](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4857-L4858). Kind: delegation.
- **Rewrite:** Delegate the condition/arms to simplifyCmpSelOfMaxMin; return its value if its min/max relationship patterns match.
- **Matched/replaced opcodes:** `select`, `icmp`, `call`.
- **Beyond opcode/constant/SSA matching:** Yes — MinMaxIntrinsic pattern helper succeeds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Simple forwarder to simplifyCmpSelOfMaxMin; IS4785/4793/4797/4805 are separately marked proved.

<a id="is4879"></a>

## IS4879 — `simplifySelectWithICmpCond`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4866–4879](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4866-L4879). Kind: delegation.
- **Rewrite:** Fold a min/max-limit select to X: after decomposing the select pattern, if its flavor is a min or max, the condition predicate is the pattern’s canonical min/max predicate, and the other arm equals the inverse-flavor limit constant, return X.
- **Matched/replaced opcodes:** `select`, `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — integer or integer-vector arms; matchDecomposedSelectPattern; select pattern/min-max predicate and scalar bit width.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires SelectPattern analysis and limit computation.

<a id="is4889"></a>

## IS4889 — `simplifySelectWithICmpCond`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4883–4889](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4883-L4889). Kind: delegation.
- **Rewrite:** For equality-to-zero condition `(X & Y)==0`, delegate the select arms to the bit-test select simplifier with X, mask Y and TrueWhenUnset=true.
- **Matched/replaced opcodes:** `select`, `icmp`, `and`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate EQ; RHS zero; LHS matches and(X,Y); bit-test helper succeeds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Simple forwarder to simplifySelectBitTest for an explicit zero equality test; concrete IS4705/4711/4721/4731 are separately marked proved.

<a id="is4898"></a>

## IS4898 — `simplifySelectWithICmpCond`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4891–4898](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4891-L4898). Kind: rewrite.
- **Rewrite:** `(ShAmt==0) ? fshl(X,*,ShAmt) : X` and `(ShAmt==0) ? fshr(*,X,ShAmt) : X` fold to X.
- **Matched/replaced opcodes:** `select`, `icmp`, `call`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate EQ and compare RHS zero; true arm has matching fshl/fshr shift operand; false arm exactly X; compare LHS exactly ShAmt.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths (positive width for abs guards), all relevant intrinsic/negation flags, both equality operand orders and both funnel directions where applicable; normalized zero APInts.
- **Lean:** [Veir/InstSimplify/IS4898.lean](../../Veir/InstSimplify/IS4898.lean).
- **Theorems:** `Veir.InstSimplify.IS4898_valid`.
- **Details / missing facilities:** Own actual LLVM patterns with exact retained false-arm/source operand and kernel-checked validity. Independent abs occurrences retain independent INT_MIN flags.

<a id="is4912"></a>

## IS4912 — `simplifySelectWithICmpCond`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4900–4912](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4900-L4912). Kind: rewrite.
- **Rewrite:** `(ShAmt==0) ? X : fshl(X,X,ShAmt)` and the corresponding fshr form fold to the rotate intrinsic.
- **Matched/replaced opcodes:** `select`, `icmp`, `call`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate EQ and RHS zero; false arm is fshl/fshr with both data operands X; true arm exactly X; compare LHS exactly ShAmt.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths (positive width for abs guards), all relevant intrinsic/negation flags, both equality operand orders and both funnel directions where applicable; normalized zero APInts.
- **Lean:** [Veir/InstSimplify/IS4912.lean](../../Veir/InstSimplify/IS4912.lean).
- **Theorems:** `Veir.InstSimplify.IS4912_valid`.
- **Details / missing facilities:** Own actual LLVM patterns with exact retained false-arm/source operand and kernel-checked validity. Independent abs occurrences retain independent INT_MIN flags.

<a id="is4923"></a>

## IS4923 — `simplifySelectWithICmpCond`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4913–4923](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4913-L4923). Kind: rewrite.
- **Rewrite:** For a zero-guarded fshl/fshr rotate, remove the guard when compare expression is `(ShAmt & (BW−1))` and BW is a power of two.
- **Matched/replaced opcodes:** `select`, `icmp`, `call`, `and`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate EQ, RHS zero; false arm rotate fshl/fshr(X,X,ShAmt); true arm X; BW power-of-two; compare LHS matches exact ShAmt and BW−1 mask.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All positive scalar integer widths equal to 2^k for arbitrary k, both funnel directions, both comparison orders and both AND orders; every normalized APInt width-minus-one mask.
- **Lean:** [Veir/InstSimplify/IS4923.lean](../../Veir/InstSimplify/IS4923.lean).
- **Theorems:** `Veir.InstSimplify.IS4923_valid`.
- **Details / missing facilities:** Own LLVM select/icmp/and-or-urem/funnel pattern; kernel-checked exact retained rotate result, including poison operands.

<a id="is4927"></a>

## IS4927 — `simplifySelectWithICmpCond`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4924–4927](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4924-L4927). Kind: rewrite.
- **Rewrite:** For a zero-guarded fshl/fshr rotate, remove the guard when compare expression is `ShAmt urem BW`.
- **Matched/replaced opcodes:** `select`, `icmp`, `call`, `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate EQ, RHS zero; false arm rotate fshl/fshr(X,X,ShAmt); true arm X; compare LHS matches exact ShAmt and scalar bitwidth BW.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths via width parameter, both funnel directions and equality operand orders; every normalized APInt width constant; operational urem division-by-zero excluded by successful interpretation.
- **Lean:** [Veir/InstSimplify/IS4927.lean](../../Veir/InstSimplify/IS4927.lean).
- **Theorems:** `Veir.InstSimplify.IS4927_valid`.
- **Details / missing facilities:** Own LLVM select/icmp/and-or-urem/funnel pattern; kernel-checked exact retained rotate result, including poison operands.

<a id="is4934"></a>

## IS4934 — `simplifySelectWithICmpCond`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4930–4934](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4930-L4934). Kind: rewrite.
- **Rewrite:** `(X==0) ? abs(X) : -abs(X)` folds to `-abs(X)`.
- **Matched/replaced opcodes:** `select`, `icmp`, `call`, `sub`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate EQ and RHS zero; abs operand exactly compare LHS; false arm is negation of matching abs.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths (positive width for abs guards), all relevant intrinsic/negation flags, both equality operand orders and both funnel directions where applicable; normalized zero APInts.
- **Lean:** [Veir/InstSimplify/IS4934.lean](../../Veir/InstSimplify/IS4934.lean).
- **Theorems:** `Veir.InstSimplify.IS4934_valid`.
- **Details / missing facilities:** Own actual LLVM patterns with exact retained false-arm/source operand and kernel-checked validity. Independent abs occurrences retain independent INT_MIN flags.

<a id="is4938"></a>

## IS4938 — `simplifySelectWithICmpCond`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4935–4938](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4935-L4938). Kind: rewrite.
- **Rewrite:** `(X==0) ? -abs(X) : abs(X)` folds to `abs(X)`.
- **Matched/replaced opcodes:** `select`, `icmp`, `call`, `sub`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate EQ and RHS zero; abs operand exactly compare LHS; true arm negation and false arm matching abs.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths (positive width for abs guards), all relevant intrinsic/negation flags, both equality operand orders and both funnel directions where applicable; normalized zero APInts.
- **Lean:** [Veir/InstSimplify/IS4938.lean](../../Veir/InstSimplify/IS4938.lean).
- **Theorems:** `Veir.InstSimplify.IS4938_valid`.
- **Details / missing facilities:** Own actual LLVM patterns with exact retained false-arm/source operand and kernel-checked validity. Independent abs occurrences retain independent INT_MIN flags.

<a id="is4949"></a>

## IS4949 — `simplifySelectWithICmpCond`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4941–4949](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4941-L4949). Kind: delegation.
- **Rewrite:** For scalar equality `CmpLHS==CmpRHS`, replace CmpLHS by CmpRHS in both select arms and fold when safe simplification makes the arms identical.
- **Matched/replaced opcodes:** `select`, `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate EQ; integer operands or canReplacePointersIfEqual(CmpLHS,CmpRHS); recursive substitution result identical.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires recursive operand substitution and pointer-equality legality.

<a id="is4954"></a>

## IS4954 — `simplifySelectWithICmpCond`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4950–4954](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4950-L4954). Kind: delegation.
- **Rewrite:** For scalar equality `CmpLHS==CmpRHS`, replace CmpRHS by CmpLHS in both select arms and fold when safe simplification makes the arms identical.
- **Matched/replaced opcodes:** `select`, `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate EQ; integer operands or canReplacePointersIfEqual(CmpRHS,CmpLHS); recursive substitution result identical.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires recursive operand substitution and pointer-equality legality.

<a id="is4964"></a>

## IS4964 — `simplifySelectWithICmpCond`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4956–4964](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4956-L4964). Kind: delegation.
- **Rewrite:** For condition `(X|Y)==0`, use the implication that both X and Y equal zero; substitute both into the arms and fold if safe simplification makes the arms identical.
- **Matched/replaced opcodes:** `select`, `icmp`, `or`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate EQ; compare RHS zero; LHS is OR; recursive substitutions of X and Y both equal zero yield identical arms.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires recursive operand substitution and poison/refinement-safe equivalence.

<a id="is4973"></a>

## IS4973 — `simplifySelectWithICmpCond`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4967–4973](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4967-L4973). Kind: delegation.
- **Rewrite:** For condition `(X&Y)==allones`, use the implication that both X and Y equal allones; substitute both into the arms and fold if safe simplification makes the arms identical.
- **Matched/replaced opcodes:** `select`, `icmp`, `and`.
- **Beyond opcode/constant/SSA matching:** Yes — Predicate EQ; compare RHS all-ones; LHS is AND; recursive substitutions of X and Y both all-ones yield identical arms.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires recursive operand substitution and poison/refinement-safe equivalence.

<a id="is5003"></a>

## IS5003 — `simplifySelectWithFCmp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4998–5003](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4998-L5003). Kind: delegation.
- **Rewrite:** For an FCmp equivalence condition, substitute CmpLHS with CmpRHS in the select arms and fold if recursive safe simplification makes them identical.
- **Matched/replaced opcodes:** `select`, `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — FCmp is equivalence (including inverted equivalence after arm swap); substitution helper proves arms identical.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is5006"></a>

## IS5006 — `simplifySelectWithFCmp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:4998–5006](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L4998-L5006). Kind: delegation.
- **Rewrite:** For an FCmp equivalence condition, substitute CmpRHS with CmpLHS in the select arms and fold if recursive safe simplification makes them identical.
- **Matched/replaced opcodes:** `select`, `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — FCmp is equivalence (including inverted equivalence after arm swap); substitution helper proves arms identical.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is5020"></a>

## IS5020 — `simplifySelectWithFCmp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5016–5020](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5016-L5020). Kind: rewrite.
- **Rewrite:** With noSignedZeros, `(T == F) ? T : F` folds to F when compare operands are exactly T and F.
- **Matched/replaced opcodes:** `select`, `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — CmpLHS=T, CmpRHS=F after optional swap; FMF noSignedZeros; predicate OEQ.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is5024"></a>

## IS5024 — `simplifySelectWithFCmp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5022–5024](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5022-L5024). Kind: rewrite.
- **Rewrite:** With noSignedZeros, `(T != F) ? T : F` folds to T when compare operands are exactly T and F.
- **Matched/replaced opcodes:** `select`, `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — CmpLHS=T, CmpRHS=F after optional swap; FMF noSignedZeros; predicate UNE.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Floating-point comparison semantics is absent from Llvm.interpretOp'; no vacuous validity theorem is claimed.

<a id="is5122"></a>

## IS5122 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5114–5122](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5114-L5122). Kind: rewrite.
- **Rewrite:** When condition, true arm, and false arm are constants, fold the select with ConstantFoldSelectInstruction if it can produce a constant result.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — all three operands Constant; LLVM constant-folding semantics.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS5122.lean](../../Veir/InstSimplify/IS5122.lean).
- **Theorems:** `Veir.InstSimplify.IS5122_valid`.
- **Details / missing facilities:** Compiled scalar literal selection across integer, zero and poison constants at arbitrary result width.

<a id="is5126"></a>

## IS5126 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5124–5126](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5124-L5126). Kind: rewrite.
- **Rewrite:** `select poison, T, F` folds to poison.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — condition is poison.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS5126.lean](../../Veir/InstSimplify/IS5126.lean).
- **Theorems:** `Veir.InstSimplify.IS5126_valid`.
- **Details / missing facilities:** Compiled LLVM scalar Puddle validity with arbitrary bitwidth and poison behavior.

<a id="is5130"></a>

## IS5130 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5128–5130](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5128-L5130). Kind: rewrite.
- **Rewrite:** `select undef, T, F` chooses F when F is any Constant; otherwise chooses T.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — condition is undef; this is a permitted undef choice.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Llvm.interpretOp' has no mlir__undef denotation and LLVM.Int has no undef constructor. No vacuous Pattern.Valid proof is claimed.

<a id="is5137"></a>

## IS5137 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5133–5137](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5133-L5137). Kind: rewrite.
- **Rewrite:** `select true, T, F` folds to T, including vector condition constants matching defined lanes.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — condition matches all-ones constant.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS5137.lean](../../Veir/InstSimplify/IS5137.lean).
- **Theorems:** `Veir.InstSimplify.IS5137_valid`.
- **Details / missing facilities:** Compiled LLVM scalar Puddle validity with arbitrary bitwidth and poison behavior.

<a id="is5139"></a>

## IS5139 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5133–5139](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5133-L5139). Kind: rewrite.
- **Rewrite:** `select false, T, F` folds to F, including vector condition constants matching defined lanes.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — condition matches zero constant.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS5139.lean](../../Veir/InstSimplify/IS5139.lean).
- **Theorems:** `Veir.InstSimplify.IS5139_valid`.
- **Details / missing facilities:** Compiled LLVM scalar Puddle validity with arbitrary bitwidth and poison behavior.

<a id="is5150"></a>

## IS5150 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5144–5150](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5144-L5150). Kind: rewrite.
- **Rewrite:** For i1 select values, `select Cond, true, false` folds to Cond.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — condition and arm types are equal i1.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar i1 LLVM integers with all property flags.
- **Lean:** [Veir/InstSimplify/IS5150.lean](../../Veir/InstSimplify/IS5150.lean).
- **Theorems:** `Veir.InstSimplify.IS5150_valid`.
- **Details / missing facilities:** Compiled scalar i1 Puddle validity including poison.

<a id="is5154"></a>

## IS5154 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5152–5154](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5152-L5154). Kind: rewrite.
- **Rewrite:** For i1 logical values, `(X && Y) ? X : Y` folds to Y, with either commutative ordering.
- **Matched/replaced opcodes:** `select`, `and`.
- **Beyond opcode/constant/SSA matching:** Yes — condition matches logical-and of the exact true and false arms.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar i1 LLVM integers with all property flags.
- **Lean:** [Veir/InstSimplify/IS5154.lean](../../Veir/InstSimplify/IS5154.lean).
- **Theorems:** `Veir.InstSimplify.IS5154_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity, including poison, every commutative operand ordering, bitwise and logical-select forms where applicable.

<a id="is5158"></a>

## IS5158 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5156–5158](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5156-L5158). Kind: rewrite.
- **Rewrite:** For i1 logical values, `(X || Y) ? X : Y` folds to X, with either commutative ordering.
- **Matched/replaced opcodes:** `select`, `or`.
- **Beyond opcode/constant/SSA matching:** Yes — condition matches logical-or of the exact true and false arms.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar i1 LLVM integers with all property flags.
- **Lean:** [Veir/InstSimplify/IS5158.lean](../../Veir/InstSimplify/IS5158.lean).
- **Theorems:** `Veir.InstSimplify.IS5158_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity, including poison, every commutative operand ordering, bitwise and logical-select forms where applicable.

<a id="is5163"></a>

## IS5163 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5161–5163](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5161-L5163). Kind: rewrite.
- **Rewrite:** For i1 values, `(X || Y) ? false : X` folds to false, with either commutative OR ordering.
- **Matched/replaced opcodes:** `select`, `or`.
- **Beyond opcode/constant/SSA matching:** Yes — true arm zero; condition OR contains false arm.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar i1 LLVM integers with all property flags.
- **Lean:** [Veir/InstSimplify/IS5163.lean](../../Veir/InstSimplify/IS5163.lean).
- **Theorems:** `Veir.InstSimplify.IS5163_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity, including poison, every commutative operand ordering, bitwise and logical-select forms where applicable.

<a id="is5169"></a>

## IS5169 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5166–5169](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5166-L5169). Kind: rewrite.
- **Rewrite:** For i1 values, `!(X || Y) ? X : false` folds to false, with either OR ordering and bitwise/select logical OR forms.
- **Matched/replaced opcodes:** `select`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — false arm zero; condition is logical not of OR containing true arm.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar i1 LLVM integers with all property flags.
- **Lean:** [Veir/InstSimplify/IS5169.lean](../../Veir/InstSimplify/IS5169.lean).
- **Theorems:** `Veir.InstSimplify.IS5169_valid`.
- **Details / missing facilities:** Compiled complete scalar forms. Inventory originally reversed the true and false arms in its description.

<a id="is5172"></a>

## IS5172 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5170–5172](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5170-L5172). Kind: rewrite.
- **Rewrite:** For i1 values, `X ? !(X || Y) : false` folds to false.
- **Matched/replaced opcodes:** `select`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — false arm zero; true arm logical not of OR containing condition.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar i1 LLVM integers with all property flags.
- **Lean:** [Veir/InstSimplify/IS5172.lean](../../Veir/InstSimplify/IS5172.lean).
- **Theorems:** `Veir.InstSimplify.IS5172_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity, including poison, every commutative operand ordering, bitwise and logical-select forms where applicable.

<a id="is5176"></a>

## IS5176 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5174–5176](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5174-L5176). Kind: rewrite.
- **Rewrite:** For i1 values, `(X || Y) ? X : false` folds to X, with either OR operand ordering.
- **Matched/replaced opcodes:** `select`, `or`.
- **Beyond opcode/constant/SSA matching:** Yes — false arm zero; condition OR contains true arm.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar i1 LLVM integers with all property flags.
- **Lean:** [Veir/InstSimplify/IS5176.lean](../../Veir/InstSimplify/IS5176.lean).
- **Theorems:** `Veir.InstSimplify.IS5176_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity, including poison, every commutative operand ordering, bitwise and logical-select forms where applicable.

<a id="is5179"></a>

## IS5179 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5178–5179](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5178-L5179). Kind: rewrite.
- **Rewrite:** For i1 values, `Y ? (X || Y) : false` folds to Y.
- **Matched/replaced opcodes:** `select`, `or`.
- **Beyond opcode/constant/SSA matching:** Yes — false arm zero; true arm logical OR contains condition.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar i1 LLVM integers with all property flags.
- **Lean:** [Veir/InstSimplify/IS5179.lean](../../Veir/InstSimplify/IS5179.lean).
- **Theorems:** `Veir.InstSimplify.IS5179_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity, including poison, every commutative operand ordering, bitwise and logical-select forms where applicable.

<a id="is5185"></a>

## IS5185 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5182–5185](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5182-L5185). Kind: rewrite.
- **Rewrite:** For i1 values, `(X || !Y) ? (X || Y) : false` folds to X.
- **Matched/replaced opcodes:** `select`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — false arm zero; both ORs share exact X and Y operands.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar i1 LLVM integers with all property flags.
- **Lean:** [Veir/InstSimplify/IS5185.lean](../../Veir/InstSimplify/IS5185.lean).
- **Theorems:** `Veir.InstSimplify.IS5185_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity, including poison, every commutative operand ordering, bitwise and logical-select forms where applicable.

<a id="is5188"></a>

## IS5188 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5186–5188](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5186-L5188). Kind: rewrite.
- **Rewrite:** For i1 values, `(X || Y) ? (X || !Y) : false` folds to X.
- **Matched/replaced opcodes:** `select`, `or`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — false arm zero; both ORs share exact X and Y operands.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS5188.lean](../../Veir/InstSimplify/IS5188.lean).
- **Theorems:** `Veir.InstSimplify.IS5188_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity, including poison, every commutative operand ordering, bitwise and logical-select forms where applicable.

<a id="is5195"></a>

## IS5195 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5192–5195](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5192-L5195). Kind: rewrite.
- **Rewrite:** For i1 values, `!(F && Y) ? true : F` folds to true.
- **Matched/replaced opcodes:** `select`, `and`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — true arm one; condition logical not of AND containing false arm.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar i1 LLVM integers with all property flags.
- **Lean:** [Veir/InstSimplify/IS5195.lean](../../Veir/InstSimplify/IS5195.lean).
- **Theorems:** `Veir.InstSimplify.IS5195_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity, including poison, every commutative operand ordering, bitwise and logical-select forms where applicable.

<a id="is5198"></a>

## IS5198 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5196–5198](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5196-L5198). Kind: rewrite.
- **Rewrite:** For i1 values, `Cond ? true : !(Cond && Y)` folds to true.
- **Matched/replaced opcodes:** `select`, `and`, `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — true arm one; false arm logical not of AND containing condition.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar i1 LLVM integers with all property flags.
- **Lean:** [Veir/InstSimplify/IS5198.lean](../../Veir/InstSimplify/IS5198.lean).
- **Theorems:** `Veir.InstSimplify.IS5198_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity, including poison, every commutative operand ordering, bitwise and logical-select forms where applicable.

<a id="is5202"></a>

## IS5202 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5200–5202](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5200-L5202). Kind: rewrite.
- **Rewrite:** For i1 values, `(F && Y) ? true : F` folds to F, with either AND operand ordering.
- **Matched/replaced opcodes:** `select`, `and`.
- **Beyond opcode/constant/SSA matching:** Yes — true arm one; condition logical AND contains false arm.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar i1 LLVM integers with all property flags.
- **Lean:** [Veir/InstSimplify/IS5202.lean](../../Veir/InstSimplify/IS5202.lean).
- **Theorems:** `Veir.InstSimplify.IS5202_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity, including poison, every commutative operand ordering, bitwise and logical-select forms where applicable.

<a id="is5205"></a>

## IS5205 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5204–5205](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5204-L5205). Kind: rewrite.
- **Rewrite:** For i1 values, `Cond ? true : (Cond && Y)` folds to Cond.
- **Matched/replaced opcodes:** `select`, `and`.
- **Beyond opcode/constant/SSA matching:** Yes — true arm one; false arm logical AND contains condition.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar i1 LLVM integers with all property flags.
- **Lean:** [Veir/InstSimplify/IS5205.lean](../../Veir/InstSimplify/IS5205.lean).
- **Theorems:** `Veir.InstSimplify.IS5205_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity, including poison, every commutative operand ordering, bitwise and logical-select forms where applicable.

<a id="is5211"></a>

## IS5211 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5209–5211](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5209-L5211). Kind: rewrite.
- **Rewrite:** `select Cond, X, X` folds to X for any condition and any result type.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — TrueVal and FalseVal are the identical SSA value.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS5211.lean](../../Veir/InstSimplify/IS5211.lean).
- **Theorems:** `Veir.InstSimplify.IS5211_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity, including poison, every commutative operand ordering, bitwise and logical-select forms where applicable.

<a id="is5216"></a>

## IS5216 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5214–5216](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5214-L5216). Kind: rewrite.
- **Rewrite:** For i1, `select X, X, false` folds to X.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — condition equals true arm; false arm zero.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar i1 LLVM integers with all property flags.
- **Lean:** [Veir/InstSimplify/IS5216.lean](../../Veir/InstSimplify/IS5216.lean).
- **Theorems:** `Veir.InstSimplify.IS5216_valid`.
- **Details / missing facilities:** Compiled scalar i1 Puddle validity including poison.

<a id="is5219"></a>

## IS5219 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5217–5219](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5217-L5219). Kind: rewrite.
- **Rewrite:** For i1, `select X, X, true` folds to true.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — condition equals true arm; false arm one.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar i1 LLVM integers with all property flags.
- **Lean:** [Veir/InstSimplify/IS5219.lean](../../Veir/InstSimplify/IS5219.lean).
- **Theorems:** `Veir.InstSimplify.IS5219_valid`.
- **Details / missing facilities:** Compiled scalar i1 Puddle validity including poison.

<a id="is5224"></a>

## IS5224 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5222–5224](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5222-L5224). Kind: rewrite.
- **Rewrite:** For i1, `select X, true, X` folds to X.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — condition equals false arm; true arm one.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar i1 LLVM integers with all property flags.
- **Lean:** [Veir/InstSimplify/IS5224.lean](../../Veir/InstSimplify/IS5224.lean).
- **Theorems:** `Veir.InstSimplify.IS5224_valid`.
- **Details / missing facilities:** Compiled scalar i1 Puddle validity including poison.

<a id="is5227"></a>

## IS5227 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5225–5227](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5225-L5227). Kind: rewrite.
- **Rewrite:** For i1, `select X, false, X` folds to false.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — condition equals false arm; true arm zero.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar i1 LLVM integers with all property flags.
- **Lean:** [Veir/InstSimplify/IS5227.lean](../../Veir/InstSimplify/IS5227.lean).
- **Theorems:** `Veir.InstSimplify.IS5227_valid`.
- **Details / missing facilities:** Compiled scalar i1 Puddle validity including poison.

<a id="is5237a"></a>

## IS5237a — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5234–5237](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5234-L5237). Kind: rewrite.
- **Rewrite:** `select Cond, poison, F` folds to F.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — TrueVal is PoisonValue.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS5237a.lean](../../Veir/InstSimplify/IS5237a.lean).
- **Theorems:** `Veir.InstSimplify.IS5237a_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity, including poison, every commutative operand ordering, bitwise and logical-select forms where applicable.

<a id="is5237b"></a>

## IS5237b — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5235–5237](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5235-L5237). Kind: rewrite.
- **Rewrite:** `select Cond, undef, F` folds to F when F is poison whenever Cond is true, so selecting the undef arm cannot make the result more defined.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — TrueVal is undef; impliesPoison(FalseVal,Cond) holds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires nondeterministic LLVM undef semantics and a certified impliesPoison(FalseVal, Cond) analysis fact. The undef opcode exists but is not interpreted by the validity semantics.

<a id="is5242a"></a>

## IS5242a — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5239–5242](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5239-L5242). Kind: rewrite.
- **Rewrite:** `select Cond, T, poison` folds to T.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — FalseVal is PoisonValue.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Lean:** [Veir/InstSimplify/IS5242a.lean](../../Veir/InstSimplify/IS5242a.lean).
- **Theorems:** `Veir.InstSimplify.IS5242a_valid`.
- **Details / missing facilities:** Compiled scalar LLVM Puddle validity, including poison, every commutative operand ordering, bitwise and logical-select forms where applicable.

<a id="is5242b"></a>

## IS5242b — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5240–5242](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5240-L5242). Kind: rewrite.
- **Rewrite:** `select Cond, T, undef` folds to T when T is poison whenever Cond is false, so selecting the undef arm cannot make the result more defined.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — FalseVal is undef; impliesPoison(TrueVal,Cond) holds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires nondeterministic LLVM undef semantics and a certified impliesPoison(TrueVal, Cond) analysis fact. The undef opcode exists but is not interpreted by the validity semantics.

<a id="is5278"></a>

## IS5278 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5275–5278](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5275-L5278). Kind: delegation.
- **Rewrite:** Delegate a select with ICmp condition to simplifySelectWithICmpCond and return its result when successful.
- **Matched/replaced opcodes:** `select`, `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — ICmp condition; helper succeeds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Simple forwarder to separately inventoried helper cases; no distinct transformation or new semantic precondition at this return. Forwards separately inventoried ICmp-conditioned select rules.

<a id="is5281"></a>

## IS5281 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5279–5281](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5279-L5281). Kind: delegation.
- **Rewrite:** Delegate a select to simplifySelectWithBitTest and return its result when bit-test analysis succeeds.
- **Matched/replaced opcodes:** `select`, `icmp`, `and`.
- **Beyond opcode/constant/SSA matching:** Yes — bit-test condition decomposition succeeds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Simple forwarder to separately inventoried helper cases; no distinct transformation or new semantic precondition at this return. Forwards separately inventoried bit-test select rules.

<a id="is5285"></a>

## IS5285 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5282–5285](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5282-L5285). Kind: delegation.
- **Rewrite:** Delegate a select with FCmp condition to simplifySelectWithFCmp and return its result when successful.
- **Matched/replaced opcodes:** `select`, `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — FCmp condition; FastMathFlags; helper succeeds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Plain simplifySelectWithFCmp forwarder in frozen source lines 5282-5285. Concrete FP-conditioned select branches are separately inventoried; this return introduces no additional rewrite boundary.

<a id="is5289"></a>

## IS5289 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5287–5289](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5287-L5289). Kind: delegation.
- **Rewrite:** If current condition is implied true/false by a dominating condition, choose the true/false arm accordingly.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — isImpliedByDomCondition succeeds in current context.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires dominating-condition implication analysis.

<a id="is5294"></a>

## IS5294 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5290–5294](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5290-L5294). Kind: rewrite.
- **Rewrite:** For two PHIs in the same block, if isSelectWithIdenticalPHI proves the true PHI is inductively identical to the false PHI, replace the select with the false PHI.
- **Matched/replaced opcodes:** `select`, `phi`.
- **Beyond opcode/constant/SSA matching:** Yes — Both arms PHI; 2 incoming values; identical entry edge; backedge select conditions same and one arm matches; induction shape recognized.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires loop-PHI induction pattern analysis.

<a id="is5296"></a>

## IS5296 — `simplifySelectInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5295–5296](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5295-L5296). Kind: rewrite.
- **Rewrite:** Symmetric case: if isSelectWithIdenticalPHI proves the false PHI is inductively identical to the true PHI, replace the select with the true PHI.
- **Matched/replaced opcodes:** `select`, `phi`.
- **Beyond opcode/constant/SSA matching:** Yes — Both arms PHI; same strict induction-shape guards as the symmetric helper check.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Scalar LLVM integers, arbitrary widths unless upstream requires i1; vector/FP/undef cases excluded as unmodeled.
- **Details / missing facilities:** Requires loop-PHI induction pattern analysis.

<a id="is5317"></a>

## IS5317 — `simplifyGEPInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5317–5317](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5317). Kind: rewrite.
- **Rewrite:** An index-free getelementptr returns its pointer operand unchanged, preserving the original pointer value and type.
- **Matched/replaced opcodes:** `getelementptr`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Modeled LLVM scalar pointers with 64-bit addresses and object identity; empty decoded GEP indices. Any elem_type is permitted because empty gepOffsets performs no DataLayout queries. GEP flags are interpreted according to current VeIR semantics; vector pointers absent.
- **Lean:** [Veir/InstSimplify/IS5317.lean](../../Veir/InstSimplify/IS5317.lean).
- **Theorems:** `Veir.InstSimplify.IS5317_valid`.
- **Details / missing facilities:** Own llvm.getelementptr pattern and exact pointer-identity operational theorem; no layout/type failure or fallback is used.

<a id="is5335"></a>

## IS5335 — `simplifyGEPInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5325–5335](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5325-L5335). Kind: rewrite.
- **Rewrite:** Return the base pointer when pointer result type is unchanged and every GEP index is zero (the all-zero GEP no-op).
- **Matched/replaced opcodes:** `getelementptr`.
- **Beyond opcode/constant/SSA matching:** Yes — vector result type must equal the pointer type; prevents erasing a vector splat.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar pointer GEPs with zero ConstantInt indices: every finite static/dynamic index count, arbitrary independent integer widths/signedness and zero-bit payload encodings, arbitrary array/struct nesting, and all modeled no-wrap flags; actual RV64 data-layout interpreter.
- **Lean:** [Veir/InstSimplify/IS5335.lean](../../Veir/InstSimplify/IS5335.lean), [Veir/InstSimplify/GEPZeroSchema.lean](../../Veir/InstSimplify/GEPZeroSchema.lean), [Veir/InstSimplify/GEPZeroInterp.lean](../../Veir/InstSimplify/GEPZeroInterp.lean), [Veir/InstSimplify/GEPZeroSupport.lean](../../Veir/InstSimplify/GEPZeroSupport.lean).
- **Theorems:** `Veir.InstSimplify.IS5335_valid`, `Veir.InstSimplify.IS5335_static_valid`.
- **Details / missing facilities:** Full list-parameterized Puddle builder and structural/semantic induction proved; raw static indices are zero, dynamic slots match normalized llvm.mlir__constant integer encoding whose interpreted bits are zero. Generic decoder/layout/address-loop proofs establish pointer preservation. The empty raw-index case also overlaps the earlier source5317 identity branch, with identical replacement; no branch-priority equivalence is claimed.

<a id="is5340"></a>

## IS5340 — `simplifyGEPInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5338–5340](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5338-L5340). Kind: rewrite.
- **Rewrite:** A GEP with a poison base pointer or any poison index yields poison of the computed GEP result type.
- **Matched/replaced opcodes:** `getelementptr`.
- **Beyond opcode/constant/SSA matching:** Yes — poison propagation; result type computation.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar pointer GEPs with a syntactic poison base or any syntactic poison integer index: every finite dynamic arity and position, independent integer widths/signedness, arbitrary interspersed static indices and valid layout nesting, and all modeled no-wrap flags; actual RV64 data-layout interpreter.
- **Lean:** [Veir/InstSimplify/IS5340.lean](../../Veir/InstSimplify/IS5340.lean), [Veir/InstSimplify/GEPDynamicSchema.lean](../../Veir/InstSimplify/GEPDynamicSchema.lean), [Veir/InstSimplify/GEPPoisonSchema.lean](../../Veir/InstSimplify/GEPPoisonSchema.lean), [Veir/InstSimplify/GEPPoisonIndexSupport.lean](../../Veir/InstSimplify/GEPPoisonIndexSupport.lean), [Veir/InstSimplify/GEPSupport.lean](../../Veir/InstSimplify/GEPSupport.lean).
- **Theorems:** `Veir.InstSimplify.IS5340_valid`, `Veir.InstSimplify.gepPoisonBaseFamily_valid`, `Veir.InstSimplify.gepPoisonIndexFamily_valid`, `Veir.InstSimplify.IS5340_static_valid`.
- **Details / missing facilities:** Complete arity-parameterized Puddle patterns cover both source causes. A Nat parameter captures every poison-base dynamic arity; arbitrary before/after Nat parameters cover every poison-index position. Generic binder/handle proofs establish Pattern.Valid, and decoder/layout/address-loop proofs establish poison propagation without extra layout narrowing. The reused poison-base value is the same modeled pointer poison; the zero-index poison-base case may overlap the earlier5317 identity with identical value.

<a id="is5344"></a>

## IS5344 — `simplifyGEPInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5342–5344](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5342-L5344). Kind: rewrite.
- **Rewrite:** If the base pointer is undef, produce undef of the computed GEP result type.
- **Matched/replaced opcodes:** `getelementptr`.
- **Beyond opcode/constant/SSA matching:** Yes — undef semantics; result type computation.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** The mlir__undef opcode exists, but Llvm.interpretOp' has no nondeterministic undef semantics (poison is distinct).

<a id="is5359"></a>

## IS5359 — `simplifyGEPInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5351–5359](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5351-L5359). Kind: rewrite.
- **Rewrite:** For a non-scalable, sized source element type with exactly one GEP index, return the pointer when the type's allocation size is zero and the pointer result type is unchanged.
- **Matched/replaced opcodes:** `getelementptr`.
- **Beyond opcode/constant/SSA matching:** Yes — DataLayout allocation size; reject scalable source/index vectors.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar LLVM pointer GEPs with exactly one index; both raw static indices and dynamic scalar integers of arbitrary width, every no-wrap flag, including poison.
- **Lean:** [Veir/InstSimplify/IS5359.lean](../../Veir/InstSimplify/IS5359.lean), [Veir/InstSimplify/GEPSupport.lean](../../Veir/InstSimplify/GEPSupport.lean).
- **Theorems:** `Veir.InstSimplify.IS5359_static_valid`, `Veir.InstSimplify.IS5359_dynamic_valid`.
- **Details / missing facilities:** Exact source allocation-size-zero metadata guard; both possible index encodings proved using actual DataLayout.riscv64 GEP offset calculation and LLVM pointer interpretation. The dynamic semantic theorem includes runtime-poison SSA indices by refinement; the proof pattern may also overlap syntactic poison constants that the upstream pass handles earlier at5340. It does not claim identical branch-priority choices for that overlap.

<a id="is5375"></a>

## IS5375 — `simplifyGEPInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5363–5375](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5363-L5375). Kind: rewrite.
- **Rewrite:** Fold gep(base, sub(ptrtoint(P), ptrtoint(base))) to P when the source element allocation size is 1, index scalar width is at least address width, P has the GEP result type, and P/base have the same underlying object.
- **Matched/replaced opcodes:** `getelementptr`, `sub`, `ptrtoint`.
- **Beyond opcode/constant/SSA matching:** Yes — DataLayout allocation/address widths; underlying-object/provenance analysis; pointer casts.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Underlying-object and pointer provenance analysis plus target DataLayout

<a id="is5383"></a>

## IS5383 — `simplifyGEPInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5379–5383](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5379-L5383). Kind: rewrite.
- **Rewrite:** Fold gep(base, ashr(sub(ptrtoint(P), ptrtoint(base)), C)) to P when allocation size equals 2^C, index width covers address width, P's type equals the GEP result type, and P/base have the same underlying object.
- **Matched/replaced opcodes:** `getelementptr`, `ashr`, `sub`, `ptrtoint`.
- **Beyond opcode/constant/SSA matching:** Yes — DataLayout; underlying-object/provenance analysis; shift amount must select exact allocation-size power of two.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** DataLayout, power-of-two reasoning, and underlying-object/provenance analysis

<a id="is5391"></a>

## IS5391 — `simplifyGEPInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5387–5391](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5387-L5391). Kind: rewrite.
- **Rewrite:** Fold gep(base, sdiv(sub(ptrtoint(P), ptrtoint(base)), allocation_size)) to P when there is one index, the element is sized and non-scalable, index width covers address width, P has the result type, and P/base have the same underlying object.
- **Matched/replaced opcodes:** `getelementptr`, `sdiv`, `sub`, `ptrtoint`.
- **Beyond opcode/constant/SSA matching:** Yes — DataLayout allocation/address widths; underlying-object/provenance analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** DataLayout and underlying-object/provenance analysis

<a id="is5414"></a>

## IS5414 — `simplifyGEPInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5398–5414](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5398-L5414). Kind: rewrite.
- **Rewrite:** For a non-scalable GEP whose final indexed type has allocation size 1, whose preceding indices are zero, and whose last index width equals the pointer index width, fold gep(gep(V,C), sub(0, ptrtoint(strippedBase))) to inttoptr(accumulatedBaseOffset); require nonzero accumulated offset.
- **Matched/replaced opcodes:** `getelementptr`, `sub`, `ptrtoint`, `inttoptr`.
- **Beyond opcode/constant/SSA matching:** Yes — DataLayout type/index size; strip and accumulate inbounds constant offsets; pointer provenance caveat: avoid inttoptr zero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Pointer-offset accumulation and provenance-aware pointer/integer conversion

<a id="is5421"></a>

## IS5421 — `simplifyGEPInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5398–5421](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5398-L5421). Kind: rewrite.
- **Rewrite:** Under the same unit-sized final type, zero preceding indices, and matching index width conditions, fold gep(gep(V,C), xor(ptrtoint(strippedBase), -1)) to inttoptr(accumulatedBaseOffset - 1); require accumulated offset not equal to one.
- **Matched/replaced opcodes:** `getelementptr`, `xor`, `ptrtoint`, `inttoptr`.
- **Beyond opcode/constant/SSA matching:** Yes — DataLayout type/index size; strip and accumulate inbounds constant offsets; pointer provenance caveat: avoid inttoptr zero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Pointer-offset accumulation and provenance-aware pointer/integer conversion

<a id="is5435"></a>

## IS5435 — `simplifyGEPInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5426–5435](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5426-L5435). Kind: rewrite.
- **Rewrite:** When base pointer and all indices are constants, build a constant GEP and use ConstantFoldGetElementPtr if ConstantExpr construction fails.
- **Matched/replaced opcodes:** `getelementptr`.
- **Beyond opcode/constant/SSA matching:** Yes — constant folding; DataLayout; GEP no-wrap flags.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Constant GEP evaluator and LLVM DataLayout/GEP flag semantics

<a id="is5438"></a>

## IS5438 — `simplifyGEPInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5426–5438](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5426-L5438). Kind: rewrite.
- **Rewrite:** When base pointer and all indices are constants and ConstantExpr construction succeeds, fold the resulting constant expression with ConstantFoldConstant.
- **Matched/replaced opcodes:** `getelementptr`.
- **Beyond opcode/constant/SSA matching:** Yes — constant folding; DataLayout; GEP no-wrap flags.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM constant-expression evaluator and GEP flag semantics

<a id="is5453"></a>

## IS5453 — `simplifyInsertValueInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5451–5453](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5451-L5453). Kind: rewrite.
- **Rewrite:** For constant aggregate and constant inserted value, constant-fold insertvalue at the specified index path.
- **Matched/replaced opcodes:** `insertvalue`.
- **Beyond opcode/constant/SSA matching:** Yes — aggregate constant folding; index path.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM insertvalue enum/verifier declarations exist, but Llvm.interpretOp′ has no semantics for these aggregate/vector operations. Interpreter failure is not counted as a proof.

<a id="is5459"></a>

## IS5459 — `simplifyInsertValueInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5455–5459](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5455-L5459). Kind: rewrite.
- **Rewrite:** insertvalue(Agg, poison, indices) returns Agg; if inserted value is undef, also return Agg only when Agg is guaranteed non-poison.
- **Matched/replaced opcodes:** `insertvalue`.
- **Beyond opcode/constant/SSA matching:** Yes — poison/undef semantics; isGuaranteedNotToBePoison analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM insertvalue enum/verifier declarations exist, but Llvm.interpretOp′ has no semantics for these aggregate/vector operations. Interpreter failure is not counted as a proof.

<a id="is5470"></a>

## IS5470 — `simplifyInsertValueInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5462–5470](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5462-L5470). Kind: rewrite.
- **Rewrite:** Cancel insertvalue(Agg, extractvalue(Y, indices), indices) to Y when aggregate operand types and index paths match and Agg is poison, or Agg is undef while Y is guaranteed non-poison.
- **Matched/replaced opcodes:** `insertvalue`, `extractvalue`.
- **Beyond opcode/constant/SSA matching:** Yes — matching aggregate type and full index path; poison/undef analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM insertvalue, extractvalue enum/verifier declarations exist, but Llvm.interpretOp′ has no semantics for these aggregate/vector operations. Interpreter failure is not counted as a proof.

<a id="is5474"></a>

## IS5474 — `simplifyInsertValueInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5462–5474](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5462-L5474). Kind: rewrite.
- **Rewrite:** Cancel insertvalue(Agg, extractvalue(Agg, indices), indices) to Agg when aggregate operand type and index paths match and both use the identical SSA aggregate.
- **Matched/replaced opcodes:** `insertvalue`, `extractvalue`.
- **Beyond opcode/constant/SSA matching:** Yes — matching aggregate type and index path.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM insertvalue, extractvalue enum/verifier declarations exist, but Llvm.interpretOp′ has no semantics for these aggregate/vector operations. Interpreter failure is not counted as a proof.

<a id="is5493"></a>

## IS5493 — `simplifyInsertElementInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5490–5493](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5490-L5493). Kind: rewrite.
- **Rewrite:** For constant vector, value, and lane index, fold insertelement as a constant expression.
- **Matched/replaced opcodes:** `insertelement`.
- **Beyond opcode/constant/SSA matching:** Yes — constant folding; fixed/scalable vector lane semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM insertelement enum/verifier declarations exist, but Llvm.interpretOp′ has no semantics for these aggregate/vector operations. Interpreter failure is not counted as a proof.

<a id="is5499"></a>

## IS5499 — `simplifyInsertElementInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5496–5499](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5496-L5499). Kind: rewrite.
- **Rewrite:** For a fixed-length vector, a constant lane index greater than or equal to its element count makes insertelement poison.
- **Matched/replaced opcodes:** `insertelement`.
- **Beyond opcode/constant/SSA matching:** Yes — fixed vector bounds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM insertelement enum/verifier declarations exist, but Llvm.interpretOp′ has no semantics for these aggregate/vector operations. Interpreter failure is not counted as a proof.

<a id="is5504"></a>

## IS5504 — `simplifyInsertElementInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5502–5504](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5502-L5504). Kind: rewrite.
- **Rewrite:** An undef insertelement lane index may choose an out-of-range index, so the result is poison.
- **Matched/replaced opcodes:** `insertelement`.
- **Beyond opcode/constant/SSA matching:** Yes — undef-index semantics; fixed vector bounds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM insertelement enum/verifier declarations exist, but Llvm.interpretOp′ has no semantics for these aggregate/vector operations. Interpreter failure is not counted as a proof.

<a id="is5510"></a>

## IS5510 — `simplifyInsertElementInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5507–5510](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5507-L5510). Kind: rewrite.
- **Rewrite:** insertelement(Vec, poison, Idx) returns Vec; undef inserted value also returns Vec only if Vec is guaranteed non-poison.
- **Matched/replaced opcodes:** `insertelement`.
- **Beyond opcode/constant/SSA matching:** Yes — poison/undef analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM insertelement enum/verifier declarations exist, but Llvm.interpretOp′ has no semantics for these aggregate/vector operations. Interpreter failure is not counted as a proof.

<a id="is5514"></a>

## IS5514 — `simplifyInsertElementInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5512–5514](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5512-L5514). Kind: rewrite.
- **Rewrite:** If the constant input vector is a splat of the constant inserted value, inserting that same value at any lane returns the original vector.
- **Matched/replaced opcodes:** `insertelement`.
- **Beyond opcode/constant/SSA matching:** Yes — constant splat recognition.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM insertelement enum/verifier declarations exist, but Llvm.interpretOp′ has no semantics for these aggregate/vector operations. Interpreter failure is not counted as a proof.

<a id="is5520"></a>

## IS5520 — `simplifyInsertElementInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5517–5520](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5517-L5520). Kind: rewrite.
- **Rewrite:** Cancel insertelement(Vec, extractelement(Vec, Idx), Idx) to Vec when both vector and index operands are the same SSA values.
- **Matched/replaced opcodes:** `insertelement`, `extractelement`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM insertelement enum/verifier declarations exist, but Llvm.interpretOp′ has no semantics for these aggregate/vector operations. Interpreter failure is not counted as a proof.

<a id="is5530"></a>

## IS5530 — `simplifyExtractValueInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5528–5530](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5528-L5530). Kind: rewrite.
- **Rewrite:** For a constant aggregate, constant-fold extractvalue at the specified index path.
- **Matched/replaced opcodes:** `extractvalue`.
- **Beyond opcode/constant/SSA matching:** Yes — aggregate constant folding; index path.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM extractvalue enum/verifier declarations exist, but Llvm.interpretOp′ has no semantics for these aggregate/vector operations. Interpreter failure is not counted as a proof.

<a id="is5547"></a>

## IS5547 — `simplifyExtractValueInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5539–5547](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5539-L5547). Kind: rewrite.
- **Rewrite:** For extractvalue of a chain of insertvalue operations, return the inserted value when the extract path exactly matches the inserted path; stop if a common prefix is a proper prefix of either path.
- **Matched/replaced opcodes:** `extractvalue`, `insertvalue`.
- **Beyond opcode/constant/SSA matching:** Yes — index path prefix comparison; cycle guard for unreachable IR.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM extractvalue, insertvalue enum/verifier declarations exist, but Llvm.interpretOp′ has no semantics for these aggregate/vector operations. Interpreter failure is not counted as a proof.

<a id="is5560"></a>

## IS5560 — `simplifyExtractValueInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5552–5560](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5552-L5560). Kind: rewrite.
- **Rewrite:** For extractvalue(umul_with_overflow(X,1), 0), return X; requires a single aggregate index selecting result element zero and either multiplication operand to be one.
- **Matched/replaced opcodes:** `extractvalue`, `call`.
- **Beyond opcode/constant/SSA matching:** Yes — intrinsic identity matching; index must equal 0.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM extractvalue enum/verifier declarations exist, but Llvm.interpretOp′ has no semantics for these aggregate/vector operations. Interpreter failure is not counted as a proof.

<a id="is5562"></a>

## IS5562 — `simplifyExtractValueInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5552–5562](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5552-L5562). Kind: rewrite.
- **Rewrite:** For extractvalue(umul_with_overflow(X,1), 1), return false of the comparison result type; requires a single aggregate index selecting overflow result element one and either multiplication operand to be one.
- **Matched/replaced opcodes:** `extractvalue`, `call`.
- **Beyond opcode/constant/SSA matching:** Yes — intrinsic identity matching; index must equal 1; comparison result type.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM extractvalue enum/verifier declarations exist, but Llvm.interpretOp′ has no semantics for these aggregate/vector operations. Interpreter failure is not counted as a proof.

<a id="is5580"></a>

## IS5580 — `simplifyExtractElementInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5577–5580](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5577-L5580). Kind: rewrite.
- **Rewrite:** For constant vector and constant lane index, fold extractelement as a constant expression.
- **Matched/replaced opcodes:** `extractelement`.
- **Beyond opcode/constant/SSA matching:** Yes — constant folding; lane bounds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** extractelement is absent from the current LLVM opcode model

<a id="is5583"></a>

## IS5583 — `simplifyExtractElementInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5577–5583](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5577-L5583). Kind: rewrite.
- **Rewrite:** If the vector operand is undef and the index is constant, return undef of the vector element type.
- **Matched/replaced opcodes:** `extractelement`.
- **Beyond opcode/constant/SSA matching:** Yes — constant index; undef semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** extractelement is absent from the current LLVM opcode model

<a id="is5589"></a>

## IS5589 — `simplifyExtractElementInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5587–5589](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5587-L5589). Kind: rewrite.
- **Rewrite:** An undef extractelement index may select an out-of-range lane, so the result is poison of the vector element type.
- **Matched/replaced opcodes:** `extractelement`.
- **Beyond opcode/constant/SSA matching:** Yes — undef-index semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** extractelement is absent from the current LLVM opcode model

<a id="is5597"></a>

## IS5597 — `simplifyExtractElementInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5593–5597](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5593-L5597). Kind: rewrite.
- **Rewrite:** For a fixed-length vector, a constant index out of bounds makes extractelement poison.
- **Matched/replaced opcodes:** `extractelement`.
- **Beyond opcode/constant/SSA matching:** Yes — fixed vector bounds.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** extractelement is absent from the current LLVM opcode model

<a id="is5601"></a>

## IS5601 — `simplifyExtractElementInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5599–5601](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5599-L5601). Kind: rewrite.
- **Rewrite:** For an in-bounds constant lane index, if the input vector is a splat, return its splat element.
- **Matched/replaced opcodes:** `extractelement`.
- **Beyond opcode/constant/SSA matching:** Yes — constant in-bounds lane; splat recognition.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** extractelement and vector splat reasoning are absent

<a id="is5603"></a>

## IS5603 — `simplifyExtractElementInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5602–5603](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5602-L5603). Kind: rewrite.
- **Rewrite:** For a constant lane index, return the scalar previously inserted at that lane when recursive vector inspection finds it.
- **Matched/replaced opcodes:** `extractelement`, `insertelement`.
- **Beyond opcode/constant/SSA matching:** Yes — findScalarElement vector analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM insertelement enum/verifier declarations exist, but Llvm.interpretOp′ has no semantics for these aggregate/vector operations. Interpreter failure is not counted as a proof.

<a id="is5611"></a>

## IS5611 — `simplifyExtractElementInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5607–5611](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5607-L5611). Kind: rewrite.
- **Rewrite:** Cancel extractelement(insertelement(Vec, Elt, Idx), Idx) to Elt when the index is not a constant and the exact same SSA index operand is used.
- **Matched/replaced opcodes:** `extractelement`, `insertelement`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM insertelement enum/verifier declarations exist, but Llvm.interpretOp′ has no semantics for these aggregate/vector operations. Interpreter failure is not counted as a proof.

<a id="is5615"></a>

## IS5615 — `simplifyExtractElementInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5614–5615](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5614-L5615). Kind: rewrite.
- **Rewrite:** For a nonconstant index, if the input vector is a splat, return its splat element.
- **Matched/replaced opcodes:** `extractelement`.
- **Beyond opcode/constant/SSA matching:** Yes — splat recognition.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** extractelement and vector splat reasoning are absent

<a id="is5658"></a>

## IS5658 — `simplifyPHINode`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5630–5658](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5630-L5658). Kind: rewrite.
- **Rewrite:** If all non-self PHI inputs are undef, poison, or equal to the PHI itself, return undef when at least one undef input was seen, otherwise poison.
- **Matched/replaced opcodes:** `phi`.
- **Beyond opcode/constant/SSA matching:** Yes — self-loop inputs ignored; undef/poison distinction.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** PHI is not part of the current LLVM opcode model

<a id="is5672"></a>

## IS5672 — `simplifyPHINode`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5630–5672](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5630-L5672). Kind: rewrite.
- **Rewrite:** When all non-self PHI inputs are one common value plus optional poison/undef, return the common value if it dominates the PHI; if undef inputs exist, also require the value is guaranteed non-poison. With only identical non-poison values, return the common value directly.
- **Matched/replaced opcodes:** `phi`.
- **Beyond opcode/constant/SSA matching:** Yes — dominance tree; isGuaranteedNotToBePoison analysis; undef/poison semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** PHI support and dominator/poison analysis are missing

<a id="is5675"></a>

## IS5675 — `simplifyPHINode`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5630–5675](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5630-L5675). Kind: rewrite.
- **Rewrite:** If all PHI incoming values are the same non-poison, non-undef SSA value (ignoring self references), replace the PHI with that value.
- **Matched/replaced opcodes:** `phi`.
- **Beyond opcode/constant/SSA matching:** Yes — all incoming values identical or self.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** PHI is not part of the current LLVM opcode model

<a id="is5681"></a>

## IS5681 — `simplifyCastInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5680–5681](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5680-L5681). Kind: rewrite.
- **Rewrite:** For a constant source operand, fold the requested cast to its destination type using LLVM constant cast folding. Pointer-address/memory-dependent alternatives are separated as IS5681p.
- **Matched/replaced opcodes:** `trunc`, `zext`, `sext`, `fptrunc`, `fpext`, `fptoui`, `fptosi`, `uitofp`, `sitofp`, `ptrtoint`, `inttoptr`, `bitcast`, `addrspacecast`, `ptrtoaddr`.
- **Beyond opcode/constant/SSA matching:** Yes — constant folding; DataLayout.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar integer trunc/zext/sext for every legal source/destination width and signedness, all relevant flags, normalized APInt payloads plus mlir__zero/mlir__poison encodings; equal-width integer bitcast constants with arbitrary source/destination signedness, and same-type pointer bitcast constants; 64-bit null/poison pointer-to-integer and poison integer-to-pointer. FP/vector and ConstantExpr/global pointer variants are excluded and pointer limitations separately recorded as IS5681p.
- **Lean:** [Veir/InstSimplify/IS5681.lean](../../Veir/InstSimplify/IS5681.lean).
- **Theorems:** `Veir.InstSimplify.IS5681.trunc_valid`, `Veir.InstSimplify.IS5681.zext_valid`, `Veir.InstSimplify.IS5681.sext_valid`, `Veir.InstSimplify.IS5681.bitcast_valid`, `Veir.InstSimplify.IS5681.ptrtoint_null_valid`, `Veir.InstSimplify.IS5681.trunc_zero_valid`, `Veir.InstSimplify.IS5681.trunc_poison_valid`, `Veir.InstSimplify.IS5681.zext_zero_valid`, `Veir.InstSimplify.IS5681.zext_poison_valid`, `Veir.InstSimplify.IS5681.sext_zero_valid`, `Veir.InstSimplify.IS5681.sext_poison_valid`, `Veir.InstSimplify.IS5681.bitcast_int_zero_valid`, `Veir.InstSimplify.IS5681.bitcast_int_poison_valid`, `Veir.InstSimplify.IS5681.bitcast_ptr_zero_valid`, `Veir.InstSimplify.IS5681.bitcast_ptr_poison_valid`, `Veir.InstSimplify.IS5681.inttoptr_poison_valid`, `Veir.InstSimplify.IS5681.ptrtoint_poison_valid`, `Veir.InstSimplify.IS5681.bitcast_integer_valid`, `Veir.InstSimplify.IS5681.bitcast_integer_zero_valid`, `Veir.InstSimplify.IS5681.bitcast_integer_poison_valid`.
- **Details / missing facilities:** Own LLVM cast/constant patterns with kernel-checked validity and exact source numeric-versus-poison output choice. ConstantFoldCastOperand receives no instruction flags; numeric integer constant folds therefore preserve its raw cast result even if source flags produce operational poison.

<a id="is5681p"></a>

## IS5681p — `simplifyCastInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5680–5681](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5680-L5681). Kind: rewrite.
- **Rewrite:** Fold a nontrivial integer-to-pointer constant cast to the corresponding LLVM pointer ConstantExpr; this is the pointer-address constant alternative of the generic constant-cast fold.
- **Matched/replaced opcodes:** `inttoptr`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM ConstantExpr representation; DataLayout; pointer address/provenance semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** 64-bit scalar integer-to-pointer constant-expression casts, including zero and nonzero; global-address pointer constants. FP/vector casts separately excluded from scalar scope.
- **Lean:** [Veir/InstSimplify/IS5693p.lean](../../Veir/InstSimplify/IS5693p.lean).
- **Details / missing facilities:** Integer-to-pointer constant folding produces a ConstantExpr/pointer-address constant, whose syntax is absent from VeIR. For nonpoison input the operational inttoptr result is memory-dependent through objectOfAddress, whereas Puddle InterpretsTo requires one memory-uniform result; even integer-zero does not uniformly encode the distinguished null pointer for arbitrary MemoryState. Global-address constant folding also has no local memory/symbol certificate. No identity re-creation or vacuous pure proof is counted.

<a id="is5693"></a>

## IS5693 — `simplifyCastInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5684–5693](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5684-L5693). Kind: rewrite.
- **Rewrite:** Cancel a two-cast chain to its original source when LLVM's isEliminableCastPair says the pair is equivalent to a bitcast and the original source type equals the requested destination type. Pointer-address/memory-dependent alternatives are separated as IS5693p.
- **Matched/replaced opcodes:** `trunc`, `zext`, `sext`, `fptrunc`, `fpext`, `fptoui`, `fptosi`, `uitofp`, `sitofp`, `ptrtoint`, `inttoptr`, `bitcast`, `addrspacecast`, `ptrtoaddr`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM cast-pair legality; source/mid/destination types; DataLayout.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Scalar integer zext/sext followed by trunc back to the exact original type, every strict width pair and all source flags; integer bitcast pairs through any equal-width intermediate signedness and same-type pointer bitcast pairs, plus identity in VeIR byte representation. Pointer/integer cast pairs separately unsupported in IS5693p; FP/vector cast pairs have no corresponding interpreter semantics.
- **Lean:** [Veir/InstSimplify/IS5693.lean](../../Veir/InstSimplify/IS5693.lean).
- **Theorems:** `Veir.InstSimplify.IS5693_extend_trunc_valid`, `Veir.InstSimplify.IS5693_bitcast_int_valid`, `Veir.InstSimplify.IS5693_bitcast_ptr_valid`, `Veir.InstSimplify.IS5693_bitcast_byte_valid`.
- **Details / missing facilities:** Own LLVM cast-pair patterns return the exact original SSA input; kernel-checked validity, including source flag poison. No proof from missing semantics or memory-uniformity vacuity is included.

<a id="is5693p"></a>

## IS5693p — `simplifyCastInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5684–5693](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5684-L5693). Kind: rewrite.
- **Rewrite:** Cancel an eliminable integer/pointer round trip when isEliminableCastPair returns BitCast and the original source type equals the destination type; this entry isolates the memory-dependent pointer/integer alternatives.
- **Matched/replaced opcodes:** `ptrtoint`, `inttoptr`.
- **Beyond opcode/constant/SSA matching:** Yes — LLVM cast-pair legality; pointer/index widths from DataLayout; memory-dependent pointer provenance.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** 64-bit pointer-to-integer-to-pointer and integer-to-pointer-to-integer cast-pair variants; pointer provenance/object identity and memory-dependent decoding.
- **Lean:** [Veir/InstSimplify/IS5693p.lean](../../Veir/InstSimplify/IS5693p.lean).
- **Theorems:** `Veir.InstSimplify.IS5693p.pointer_to_integer`, `Veir.InstSimplify.IS5693p.integer_to_pointer_empty`, `Veir.InstSimplify.IS5693p.integer_to_pointer_allocated`, `Veir.InstSimplify.IS5693p.operational_roundtrip_differs`, `Veir.InstSimplify.IS5693p.no_memory_uniform_result`.
- **Details / missing facilities:** Pointer/integer cast-pair cancellation cannot be faithfully expressed using the current pure local InterpretsTo judgment: inttoptr depends on memory.decode/objectOfAddress, but InterpretsTo demands the same intermediate result for every memory. Checked operational witnesses show integer1 decodes to pointer object0/address1 in empty memory and object1/address1 in witnessMemory; ptrtoint of object1/address1 loses its object identifier. This is a model correspondence limitation, not an LLVM bug or a false Pattern.Valid witness. Neither direction is counted using vacuity.

<a id="is5700"></a>

## IS5700 — `simplifyCastInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5697–5700](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5697-L5700). Kind: rewrite.
- **Rewrite:** A bitcast from a value to its identical type returns the operand.
- **Matched/replaced opcodes:** `bitcast`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled same-type integer, byte and pointer bitcasts. Floating/vector bitcasts lack interpreter semantics.
- **Lean:** [Veir/InstSimplify/IS5700.lean](../../Veir/InstSimplify/IS5700.lean).
- **Theorems:** `Veir.InstSimplify.IS5700_int_valid`, `Veir.InstSimplify.IS5700_byte_valid`, `Veir.InstSimplify.IS5700_ptr_valid`.
- **Details / missing facilities:** Own actual LLVM patterns with kernel-checked validity; generic call_intrinsic fallback is never used.

<a id="is5713"></a>

## IS5713 — `simplifyCastInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5704–5713](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5704-L5713). Kind: rewrite.
- **Rewrite:** Cancel ptrtoaddr(ptradd(Ptr, sub(X, ptrtoint-or-ptrtoaddr(Ptr)))) to X when X has the requested type and that type is the pointer's DataLayout index type.
- **Matched/replaced opcodes:** `ptrtoaddr`, `ptradd`, `sub`, `ptrtoint`.
- **Beyond opcode/constant/SSA matching:** Yes — same pointer SSA operand; DataLayout index type.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** ptrtoaddr and ptradd are not represented in the current LLVM opcode model

<a id="is5722"></a>

## IS5722 — `simplifyCastInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5716–5722](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5716-L5722). Kind: rewrite.
- **Rewrite:** Cancel zext(trunc(X)) to X when X has the final destination type and trunc has nuw; cancel sext(trunc(X)) under the same type condition when trunc has nsw.
- **Matched/replaced opcodes:** `zext`, `sext`, `trunc`.
- **Beyond opcode/constant/SSA matching:** Yes — trunc nuw for zext; trunc nsw for sext.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer source/destination widths with strict narrowing then extension; trunc nuw for zext or nsw for sext. Remaining trunc flag and zext nneg arbitrary.
- **Lean:** [Veir/InstSimplify/IS5722.lean](../../Veir/InstSimplify/IS5722.lean).
- **Theorems:** `Veir.InstSimplify.IS5722_valid`.
- **Details / missing facilities:** Own LLVM trunc/zext/sext pattern with exact source result x and kernel-checked validity; no unsupported-opcode fallback.

<a id="is5740"></a>

## IS5740 — `simplifyAddrSpaceCastInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5735–5740](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5735-L5740). Kind: rewrite.
- **Rewrite:** An addrspacecast marked nonnull from null becomes poison when function context exists and null pointers are not defined in the source address space.
- **Matched/replaced opcodes:** `addrspacecast`.
- **Beyond opcode/constant/SSA matching:** Yes — nonnull instruction property; function context; NullPointerIsDefined target/function semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Address-space cast and per-function null-pointer-defined semantics are missing

<a id="is5776"></a>

## IS5776 — `foldIdentityShuffles`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5752–5776](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5752-L5776). Kind: rewrite.
- **Rewrite:** Recursively inspect the selected lane through nested fixed-vector shuffles; return the root source only when every selected root is the same SSA vector and the final lane equals the destination lane. An undef mask lane or recursion exhaustion prevents the fold.
- **Matched/replaced opcodes:** `shufflevector`.
- **Beyond opcode/constant/SSA matching:** Yes — fixed vector lane masks; recursive shuffle traversal; recursion limit.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** shufflevector is absent from the current LLVM opcode model

<a id="is5795"></a>

## IS5795 — `foldIdentityShuffles`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5752–5795](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5752-L5795). Kind: rewrite.
- **Rewrite:** Return the common root vector when the selected lane originates from that same vector and retains its lane number through the shuffle chain.
- **Matched/replaced opcodes:** `shufflevector`.
- **Beyond opcode/constant/SSA matching:** Yes — fixed vector lane masks; recursive shuffle traversal.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** shufflevector is absent from the current LLVM opcode model

<a id="is5803"></a>

## IS5803 — `simplifyShuffleVectorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5800–5803](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5800-L5803). Kind: rewrite.
- **Rewrite:** If every shuffle mask element is poison, the shuffle result is poison of the result vector type.
- **Matched/replaced opcodes:** `shufflevector`.
- **Beyond opcode/constant/SSA matching:** Yes — poison mask semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** shufflevector and poison mask semantics are absent

<a id="is5840"></a>

## IS5840 — `simplifyShuffleVectorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5836–5840](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5836-L5840). Kind: rewrite.
- **Rewrite:** When both input vectors are constants, fold the shuffle constant expression using its mask.
- **Matched/replaced opcodes:** `shufflevector`.
- **Beyond opcode/constant/SSA matching:** Yes — constant vector shuffle folding; mask semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM vector constant shuffle evaluator is missing

<a id="is5873"></a>

## IS5873 — `simplifyShuffleVectorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5850–5873](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5850-L5873). Kind: rewrite.
- **Rewrite:** For a non-scalable shuffle where Op0 is insertelement(_, constant C, constant InsertIndex), Op1 is undef, and every mask element is either InsertIndex or undef (-1), build a constant splat of C, replacing output lanes selected by undef mask entries with poison.
- **Matched/replaced opcodes:** `shufflevector`.
- **Beyond opcode/constant/SSA matching:** Yes — non-scalable vector; constant inserted value and index; undef second vector; mask elements each InsertIndex or -1; undef mask lanes become poison.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** shufflevector mask analysis and vector constant construction are missing

<a id="is5882"></a>

## IS5882 — `simplifyShuffleVectorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5877–5882](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5877-L5882). Kind: rewrite.
- **Rewrite:** For shuffle(Op0, undef), return Op0 when Op0 is itself a shuffle, result type equals input vector type, and every inner shuffle mask lane is equal (a splat shuffle).
- **Matched/replaced opcodes:** `shufflevector`.
- **Beyond opcode/constant/SSA matching:** Yes — Op0 must be ShuffleVectorInst; Op1 undef; RetTy equals input vector type; inner shuffle mask all equal.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** shufflevector mask and scalable-vector semantics are absent

<a id="is5910"></a>

## IS5910 — `simplifyShuffleVectorInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5899–5910](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5899-L5910). Kind: rewrite.
- **Rewrite:** Return the common vector when every output lane is an identity lane recovered by foldIdentityShuffles across nested shuffle operands.
- **Matched/replaced opcodes:** `shufflevector`.
- **Beyond opcode/constant/SSA matching:** Yes — recursive lane provenance; mask analysis; recursion limit.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** shufflevector lane provenance analysis is missing

<a id="is5923"></a>

## IS5923 — `foldConstant`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5921–5923](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5921-L5923). Kind: schema.
- **Rewrite:** Delegate constant unary operation folding to LLVM ConstantFoldUnaryOpOperand; return null for nonconstant or unsupported constants.
- **Matched/replaced opcodes:** `fneg`.
- **Beyond opcode/constant/SSA matching:** Yes — constant operand; DataLayout; external LLVM constant folder.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Only upstream unary operation is fneg; fneg lacks a Llvm.interpretOp′ branch.

<a id="is5932"></a>

## IS5932 — `simplifyFNegInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5929–5932](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5929-L5932). Kind: schema.
- **Rewrite:** Constant-fold fneg when the operand is constant.
- **Matched/replaced opcodes:** `fneg`.
- **Beyond opcode/constant/SSA matching:** Yes — constant folding; DataLayout.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple return from foldConstant(FNeg); the same constant-evaluation boundary is independently inventoried at IS5923.

<a id="is5937"></a>

## IS5937 — `simplifyFNegInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5935–5937](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5935-L5937). Kind: rewrite.
- **Rewrite:** Cancel fneg(fneg(X)) to X.
- **Matched/replaced opcodes:** `fneg`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is5966"></a>

## IS5966 — `propagateNaN`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5947–5966](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5947-L5966). Kind: schema.
- **Rewrite:** For fixed vectors, propagate poison elements; quiet existing NaNs while preserving their payload; replace other or unknown elements by canonical NaN, and return the rebuilt vector.
- **Matched/replaced opcodes:** `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `call`.
- **Beyond opcode/constant/SSA matching:** Yes — fixed vector constants; NaN signaling/payload semantics; elementwise poison handling.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is5972"></a>

## IS5972 — `propagateNaN`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5968–5972](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5968-L5972). Kind: schema.
- **Rewrite:** For a non-fixed-vector NaN constant that is not itself NaN, return canonical NaN of its type.
- **Matched/replaced opcodes:** `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `call`.
- **Beyond opcode/constant/SSA matching:** Yes — NaN classification; scalable vector/splat handling.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is5985"></a>

## IS5985 — `propagateNaN`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5975–5985](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5975-L5985). Kind: schema.
- **Rewrite:** For scalar or scalable-vector NaN constants, preserve NaN sign/payload and quiet a signaling NaN; scalable input must be a NaN splat.
- **Matched/replaced opcodes:** `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `call`.
- **Beyond opcode/constant/SSA matching:** Yes — NaN payload/sign; signaling-to-quiet conversion; scalable splat.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is5998"></a>

## IS5998 — `simplifyFPOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:5994–5998](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L5994-L5998). Kind: schema.
- **Rewrite:** If any FP operation operand is poison, return poison of the first operand type.
- **Matched/replaced opcodes:** `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `fma`, `fmuladd`.
- **Beyond opcode/constant/SSA matching:** Yes — poison propagation.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6009"></a>

## IS6009 — `simplifyFPOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6003–6009](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6003-L6009). Kind: schema.
- **Rewrite:** With nnan, a NaN operand or undef operand yields poison of that operand's type.
- **Matched/replaced opcodes:** `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `fma`, `fmuladd`.
- **Beyond opcode/constant/SSA matching:** Yes — nnan fast-math flag; undef may choose NaN.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6011"></a>

## IS6011 — `simplifyFPOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6003–6011](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6003-L6011). Kind: schema.
- **Rewrite:** With ninf, an infinite operand or undef operand yields poison of that operand's type.
- **Matched/replaced opcodes:** `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `fma`, `fmuladd`.
- **Beyond opcode/constant/SSA matching:** Yes — ninf fast-math flag; undef may choose infinity.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6019"></a>

## IS6019 — `simplifyFPOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6013–6019](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6013-L6019). Kind: schema.
- **Rewrite:** In the default FP environment, an undef operand yields canonical NaN of its type.
- **Matched/replaced opcodes:** `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `fma`, `fmuladd`.
- **Beyond opcode/constant/SSA matching:** Yes — exception behavior and rounding mode must be default.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6021"></a>

## IS6021 — `simplifyFPOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6020–6021](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6020-L6021). Kind: schema.
- **Rewrite:** In the default FP environment, propagate an input NaN constant through the operation via propagateNaN.
- **Matched/replaced opcodes:** `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `fma`, `fmuladd`.
- **Beyond opcode/constant/SSA matching:** Yes — exception behavior and rounding mode must be default; NaN payload/poison vector handling.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6024"></a>

## IS6024 — `simplifyFPOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6022–6024](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6022-L6024). Kind: schema.
- **Rewrite:** With non-strict constrained FP (exception behavior other than strict), propagate NaN constants via propagateNaN; strict exception behavior prevents this fold.
- **Matched/replaced opcodes:** `fadd`, `fsub`, `fmul`, `fdiv`, `frem`, `fma`.
- **Beyond opcode/constant/SSA matching:** Yes — constrained FP exception behavior; NaN payload/poison vector handling.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6039"></a>

## IS6039 — `simplifyFAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6037–6039](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6037-L6039). Kind: schema.
- **Rewrite:** In the default FP environment, constant-fold/commute fadd operands when the constant folder succeeds.
- **Matched/replaced opcodes:** `fadd`.
- **Beyond opcode/constant/SSA matching:** Yes — constant folding; default exception/rounding environment.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple FP constant-fold forwarding through foldOrCommuteConstant; its FP evaluator boundary is inventoried at IS0580.

<a id="is6042"></a>

## IS6042 — `simplifyFAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6041–6042](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6041-L6042). Kind: schema.
- **Rewrite:** Apply shared FP poison/undef/NaN simplifications to fadd before algebraic identities.
- **Matched/replaced opcodes:** `fadd`.
- **Beyond opcode/constant/SSA matching:** Yes — fast-math flags; FP exception behavior; rounding mode.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple forwarding of simplifyFPOp results; the shared poison/undef/NaN rules are independently inventoried at IS5998-IS6024.

<a id="is6053"></a>

## IS6053 — `simplifyFAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6046–6053](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6046-L6053). Kind: rewrite.
- **Rewrite:** Fold fadd(X,-0.0) to X when signaling NaNs may be ignored and either rounding cannot be toward negative or nsz is set.
- **Matched/replaced opcodes:** `fadd`.
- **Beyond opcode/constant/SSA matching:** Yes — sNaN behavior; rounding mode; nsz.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6059"></a>

## IS6059 — `simplifyFAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6055–6059](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6055-L6059). Kind: rewrite.
- **Rewrite:** Fold fadd(X,+0.0) to X when signaling NaNs may be ignored and X cannot be negative zero or nsz is set.
- **Matched/replaced opcodes:** `fadd`.
- **Beyond opcode/constant/SSA matching:** Yes — sNaN behavior; known-negative-zero analysis; nsz.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6067"></a>

## IS6067 — `simplifyFAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6064–6067](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6064-L6067). Kind: rewrite.
- **Rewrite:** With nnan in default FP environment, fadd(X,+/-Inf) returns the infinity operand.
- **Matched/replaced opcodes:** `fadd`.
- **Beyond opcode/constant/SSA matching:** Yes — nnan; operand 1 must be infinity.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6078"></a>

## IS6078 — `simplifyFAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6072–6078](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6072-L6078). Kind: rewrite.
- **Rewrite:** With nnan, fold (-X)+X or X+(-X) to positive zero when either operand is a subtraction from either signed zero of the other operand.
- **Matched/replaced opcodes:** `fadd`, `fsub`.
- **Beyond opcode/constant/SSA matching:** Yes — nnan; commuted pattern; default FP environment.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6082"></a>

## IS6082 — `simplifyFAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6080–6082](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6080-L6082). Kind: rewrite.
- **Rewrite:** With nnan, fold fadd(X,fneg(X)) or fadd(fneg(X),X) to positive zero.
- **Matched/replaced opcodes:** `fadd`, `fneg`.
- **Beyond opcode/constant/SSA matching:** Yes — nnan; commuted pattern; default FP environment.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6091"></a>

## IS6091 — `simplifyFAddInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6087–6091](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6087-L6091). Kind: rewrite.
- **Rewrite:** With nsz and reassociation, fold (X-Y)+Y or Y+(X-Y) to X.
- **Matched/replaced opcodes:** `fadd`, `fsub`.
- **Beyond opcode/constant/SSA matching:** Yes — nsz; reassoc; commuted pattern.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6105"></a>

## IS6105 — `simplifyFSubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6103–6105](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6103-L6105). Kind: schema.
- **Rewrite:** In the default FP environment, constant-fold/commute fsub operands when constant folding succeeds.
- **Matched/replaced opcodes:** `fsub`.
- **Beyond opcode/constant/SSA matching:** Yes — constant folding; default exception/rounding environment.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple FP constant-fold forwarding through foldOrCommuteConstant; its FP evaluator boundary is inventoried at IS0580.

<a id="is6108"></a>

## IS6108 — `simplifyFSubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6107–6108](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6107-L6108). Kind: schema.
- **Rewrite:** Apply shared FP poison/undef/NaN simplifications to fsub before algebraic identities.
- **Matched/replaced opcodes:** `fsub`.
- **Beyond opcode/constant/SSA matching:** Yes — fast-math flags; FP exception behavior; rounding mode.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple forwarding of simplifyFPOp results; the shared poison/undef/NaN rules are independently inventoried at IS5998-IS6024.

<a id="is6115"></a>

## IS6115 — `simplifyFSubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6110–6115](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6110-L6115). Kind: rewrite.
- **Rewrite:** Fold fsub(X,+0.0) to X when signaling NaNs may be ignored and either rounding cannot be toward negative or nsz is set.
- **Matched/replaced opcodes:** `fsub`.
- **Beyond opcode/constant/SSA matching:** Yes — sNaN behavior; rounding mode; nsz.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6121"></a>

## IS6121 — `simplifyFSubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6117–6121](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6117-L6121). Kind: rewrite.
- **Rewrite:** Fold fsub(X,-0.0) to X when signaling NaNs may be ignored and X cannot be negative zero or nsz is set.
- **Matched/replaced opcodes:** `fsub`.
- **Beyond opcode/constant/SSA matching:** Yes — sNaN behavior; known-negative-zero analysis; nsz.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6128"></a>

## IS6128 — `simplifyFSubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6124–6128](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6124-L6128). Kind: rewrite.
- **Rewrite:** When signaling NaNs may be ignored, fold -0.0 - fneg(X) to X.
- **Matched/replaced opcodes:** `fsub`, `fneg`.
- **Beyond opcode/constant/SSA matching:** Yes — sNaN behavior.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6136"></a>

## IS6136 — `simplifyFSubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6131–6136](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6131-L6136). Kind: rewrite.
- **Rewrite:** With nsz and signaling NaNs ignored, fold either signed zero minus (signed zero minus X) or fneg(X) to X.
- **Matched/replaced opcodes:** `fsub`, `fneg`.
- **Beyond opcode/constant/SSA matching:** Yes — nsz; sNaN behavior; any-zero pattern.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6144"></a>

## IS6144 — `simplifyFSubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6142–6144](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6142-L6144). Kind: rewrite.
- **Rewrite:** With nnan in default FP environment, fsub(X,X) is positive zero.
- **Matched/replaced opcodes:** `fsub`.
- **Beyond opcode/constant/SSA matching:** Yes — nnan; default exception/rounding environment.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6148"></a>

## IS6148 — `simplifyFSubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6146–6148](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6146-L6148). Kind: rewrite.
- **Rewrite:** With nnan in default FP environment, fsub(+/-Inf,X) returns the first infinite operand.
- **Matched/replaced opcodes:** `fsub`.
- **Beyond opcode/constant/SSA matching:** Yes — nnan; operand 0 must be infinity.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6152"></a>

## IS6152 — `simplifyFSubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6150–6152](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6150-L6152). Kind: rewrite.
- **Rewrite:** With nnan in default FP environment, fsub(X,+/-Inf) returns fneg of the infinite second operand.
- **Matched/replaced opcodes:** `fsub`, `fneg`.
- **Beyond opcode/constant/SSA matching:** Yes — nnan; operand 1 must be infinity; constant fold fneg.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6160"></a>

## IS6160 — `simplifyFSubInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6156–6160](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6156-L6160). Kind: rewrite.
- **Rewrite:** With nsz and reassociation, fold Y-(Y-X) or (X+Y)-Y to X.
- **Matched/replaced opcodes:** `fsub`, `fadd`.
- **Beyond opcode/constant/SSA matching:** Yes — nsz; reassoc; commuted add pattern.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6170"></a>

## IS6170 — `simplifyFMAFMul`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6168–6170](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6168-L6170). Kind: schema.
- **Rewrite:** Apply shared FP poison/undef/NaN simplifications to fmul before identities.
- **Matched/replaced opcodes:** `fmul`.
- **Beyond opcode/constant/SSA matching:** Yes — fast-math flags; FP exception behavior; rounding mode.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple forwarding of simplifyFPOp results; the shared poison/undef/NaN rules are independently inventoried at IS5998-IS6024.

<a id="is6181"></a>

## IS6181 — `simplifyFMAFMul`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6179–6181](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6179-L6181). Kind: rewrite.
- **Rewrite:** Fold X*1.0 to X in the default FP environment.
- **Matched/replaced opcodes:** `fmul`.
- **Beyond opcode/constant/SSA matching:** Yes — default exception/rounding environment; one constant canonicalized to operand 1.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6186"></a>

## IS6186 — `simplifyFMAFMul`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6183–6186](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6183-L6186). Kind: rewrite.
- **Rewrite:** Fold X*+/-0.0 to positive zero with both nnan and nsz.
- **Matched/replaced opcodes:** `fmul`.
- **Beyond opcode/constant/SSA matching:** Yes — nnan; nsz; default exception/rounding environment.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6192"></a>

## IS6192 — `simplifyFMAFMul`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6188–6192](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6188-L6192). Kind: rewrite.
- **Rewrite:** If X is known finite and non-NaN and either nsz is set or sign is known nonnegative, simplify X*(+/-0) to +0 when nsz is set.
- **Matched/replaced opcodes:** `fmul`.
- **Beyond opcode/constant/SSA matching:** Yes — KnownFPClass excludes inf/nan; known sign; nsz.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6195"></a>

## IS6195 — `simplifyFMAFMul`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6188–6195](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6188-L6195). Kind: rewrite.
- **Rewrite:** If X is known finite and non-NaN with known nonnegative sign and nsz is absent, simplify X*(+/-0) to the zero operand (preserving its sign).
- **Matched/replaced opcodes:** `fmul`.
- **Beyond opcode/constant/SSA matching:** Yes — KnownFPClass excludes inf/nan; known sign is nonnegative.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6198"></a>

## IS6198 — `simplifyFMAFMul`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6188–6198](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6188-L6198). Kind: rewrite.
- **Rewrite:** If X is known finite and non-NaN with known negative sign and nsz is absent, simplify X*(+/-0) to fneg of the zero operand.
- **Matched/replaced opcodes:** `fmul`, `fneg`.
- **Beyond opcode/constant/SSA matching:** Yes — KnownFPClass excludes inf/nan; known negative sign.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6209"></a>

## IS6209 — `simplifyFMAFMul`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6202–6209](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6202-L6209). Kind: rewrite.
- **Rewrite:** With reassoc, nnan, and nsz, fold sqrt(X)*sqrt(X) to X.
- **Matched/replaced opcodes:** `fmul`, `sqrt`.
- **Beyond opcode/constant/SSA matching:** Yes — same SSA sqrt operand; reassoc; nnan; nsz.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6222"></a>

## IS6222 — `simplifyFMulInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6220–6222](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6220-L6222). Kind: schema.
- **Rewrite:** In the default FP environment, constant-fold/commute fmul operands when constant folding succeeds.
- **Matched/replaced opcodes:** `fmul`.
- **Beyond opcode/constant/SSA matching:** Yes — constant folding; default exception/rounding environment.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple FP constant-fold forwarding through foldOrCommuteConstant; its FP evaluator boundary is inventoried at IS0580.

<a id="is6267"></a>

## IS6267 — `simplifyFDivInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6265–6267](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6265-L6267). Kind: schema.
- **Rewrite:** In the default FP environment, constant-fold/commute fdiv operands when constant folding succeeds.
- **Matched/replaced opcodes:** `fdiv`.
- **Beyond opcode/constant/SSA matching:** Yes — constant folding; default exception/rounding environment.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple FP constant-fold forwarding through foldOrCommuteConstant; its FP evaluator boundary is inventoried at IS0580.

<a id="is6270"></a>

## IS6270 — `simplifyFDivInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6269–6270](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6269-L6270). Kind: schema.
- **Rewrite:** Apply shared FP poison/undef/NaN simplifications to fdiv before identities.
- **Matched/replaced opcodes:** `fdiv`.
- **Beyond opcode/constant/SSA matching:** Yes — fast-math flags; FP exception behavior; rounding mode.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple forwarding of simplifyFPOp results; the shared poison/undef/NaN rules are independently inventoried at IS5998-IS6024.

<a id="is6277"></a>

## IS6277 — `simplifyFDivInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6275–6277](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6275-L6277). Kind: rewrite.
- **Rewrite:** In the default FP environment, fold X/1.0 to X.
- **Matched/replaced opcodes:** `fdiv`.
- **Beyond opcode/constant/SSA matching:** Yes — default exception/rounding environment.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6283"></a>

## IS6283 — `simplifyFDivInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6279–6283](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6279-L6283). Kind: rewrite.
- **Rewrite:** With nnan and nsz in the default FP environment, fold 0/X to positive zero.
- **Matched/replaced opcodes:** `fdiv`.
- **Beyond opcode/constant/SSA matching:** Yes — nnan; nsz; default exception/rounding environment.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6289"></a>

## IS6289 — `simplifyFDivInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6286–6289](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6286-L6289). Kind: rewrite.
- **Rewrite:** With nnan, fold X/X to 1.0.
- **Matched/replaced opcodes:** `fdiv`.
- **Beyond opcode/constant/SSA matching:** Yes — same SSA operand; nnan; default exception/rounding environment.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6294"></a>

## IS6294 — `simplifyFDivInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6291–6294](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6291-L6294). Kind: rewrite.
- **Rewrite:** With nnan and reassoc, fold (X*Y)/Y to X.
- **Matched/replaced opcodes:** `fdiv`, `fmul`.
- **Beyond opcode/constant/SSA matching:** Yes — reassoc; nnan; commutative multiply pattern.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6301"></a>

## IS6301 — `simplifyFDivInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6298–6301](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6298-L6301). Kind: rewrite.
- **Rewrite:** With nnan, fold (-X)/X or X/(-X) to -1.0.
- **Matched/replaced opcodes:** `fdiv`, `fneg`.
- **Beyond opcode/constant/SSA matching:** Yes — nsz negative operand pattern; nnan; commuted pattern.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6305"></a>

## IS6305 — `simplifyFDivInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6303–6305](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6303-L6305). Kind: rewrite.
- **Rewrite:** With nnan and ninf, division by either signed zero yields poison.
- **Matched/replaced opcodes:** `fdiv`.
- **Beyond opcode/constant/SSA matching:** Yes — nnan; ninf; divisor is either signed zero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6326"></a>

## IS6326 — `simplifyFRemInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6324–6326](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6324-L6326). Kind: schema.
- **Rewrite:** In the default FP environment, constant-fold/commute frem operands when constant folding succeeds.
- **Matched/replaced opcodes:** `frem`.
- **Beyond opcode/constant/SSA matching:** Yes — constant folding; default exception/rounding environment.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple FP constant-fold forwarding through foldOrCommuteConstant; its FP evaluator boundary is inventoried at IS0580.

<a id="is6329"></a>

## IS6329 — `simplifyFRemInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6328–6329](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6328-L6329). Kind: schema.
- **Rewrite:** Apply shared FP poison/undef/NaN simplifications to frem before signed-zero identities.
- **Matched/replaced opcodes:** `frem`.
- **Beyond opcode/constant/SSA matching:** Yes — fast-math flags; FP exception behavior; rounding mode.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple forwarding of simplifyFPOp results; the shared poison/undef/NaN rules are independently inventoried at IS5998-IS6024.

<a id="is6340"></a>

## IS6340 — `simplifyFRemInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6338–6340](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6338-L6340). Kind: rewrite.
- **Rewrite:** With nnan, +0.0 % X simplifies to a full positive-zero constant, including vector elements.
- **Matched/replaced opcodes:** `frem`.
- **Beyond opcode/constant/SSA matching:** Yes — nnan; vector constant handling.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6343"></a>

## IS6343 — `simplifyFRemInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6341–6343](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6341-L6343). Kind: rewrite.
- **Rewrite:** With nnan, -0.0 % X simplifies to a full negative-zero constant, preserving frem dividend sign.
- **Matched/replaced opcodes:** `frem`.
- **Beyond opcode/constant/SSA matching:** Yes — nnan; vector constant handling; signed zero.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Llvm.interpretOp′ in Veir/Dialects/LLVM/OpInfo.lean has no floating-point operation semantics, so a rewrite proof has no modeled source semantics

<a id="is6576"></a>

## IS6576 — `simplifyRelativeLoad`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6534–6576](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6534-L6576). Kind: rewrite.
- **Rewrite:** Resolve llvm.load.relative to the referenced GlobalValue when Ptr is a constant global plus offset, Offset is a constant integer no wider than 64 bits and divisible by four, the constant load decodes as (optionally trunc'd) ptrtoint(global) minus another constant global address, and both global symbol and offset match Ptr's symbol/offset.
- **Matched/replaced opcodes:** `call`, `load`, `ptrtoint`, `sub`, `trunc`.
- **Beyond opcode/constant/SSA matching:** Yes — constant global offset analysis; constant load folding; DataLayout; relative-load intrinsic semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Constant memory/global relocation analysis is not modeled by the LLVM operation interpreter

<a id="is6585"></a>

## IS6585 — `simplifyLdexp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6581–6585](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6581-L6585). Kind: rewrite.
- **Rewrite:** The helper returns Op0 if either ldexp operand is poison; at the public simplifyIntrinsic entry, the prior intrinsicPropagatesPoison check converts poison in either argument to poison of the return type before reaching this helper.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — ldexp intrinsicPropagatesPoison precheck in simplifyIntrinsic; poison propagation.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** The ldexp helper returns Op0 on either poison operand, but the public simplifyIntrinsic poison precheck runs first and returns poison. This helper return is not an independently reachable public fold; missing FP semantics is also relevant.

<a id="is6589"></a>

## IS6589 — `simplifyLdexp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6587–6589](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6587-L6589). Kind: rewrite.
- **Rewrite:** ldexp(undef, x) yields NaN of the FP operand type.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — undef semantics; ldexp.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** ldexp and FP semantics are not modeled

<a id="is6596"></a>

## IS6596 — `simplifyLdexp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6592–6596](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6592-L6596). Kind: rewrite.
- **Rewrite:** For non-strict ldexp only, ldexp(x, undef) returns x.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — strictness flag; undef semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** ldexp is not modeled and strict FP mode is absent

<a id="is6608"></a>

## IS6608 — `simplifyLdexp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6599–6608](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6599-L6608). Kind: rewrite.
- **Rewrite:** For a constant FP first operand that is either signed zero or signed infinity, ldexp returns that operand even in strict mode.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — FP constant classification; strictness.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** ldexp and FP constant semantics are not modeled

<a id="is6617"></a>

## IS6617 — `simplifyLdexp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6615–6617](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6615-L6617). Kind: rewrite.
- **Rewrite:** For non-strict ldexp with NaN first operand, return the same NaN quieted (this branch is after strict mode was rejected).
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — NaN quieting/payload; strictness.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** ldexp and signaling NaN semantics are not modeled

<a id="is6624"></a>

## IS6624 — `simplifyLdexp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6621–6624](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6621-L6624). Kind: rewrite.
- **Rewrite:** For non-strict ldexp(x, 0), return x.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — integer exponent zero; strict mode already excluded.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** ldexp is not modeled

<a id="is6636"></a>

## IS6636 — `simplifyUnaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6631–6636](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6631-L6636). Kind: schema.
- **Rewrite:** For any intrinsic classified idempotent, remove a repeated application when Op0 is an IntrinsicInst with the same intrinsic ID.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — applies to fabs, floor, ceil, trunc, rint, nearbyint, round, roundeven, canonicalize, arithmetic_fence.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Pinned source classifier isIdempotent (6489–6507) contains only fabs,floor,ceil,trunc,rint,nearbyint,round,roundeven,canonicalize,arithmetic_fence; their FP intrinsic semantics are absent from Llvm.interpretOp′.

<a id="is6647"></a>

## IS6647 — `simplifyUnaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6640–6647](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6640-L6647). Kind: schema.
- **Rewrite:** If the outer intrinsic removes fractional FP bits and Op0 is another such intrinsic or an integer-to-FP cast, eliminate the outer rounding operation.
- **Matched/replaced opcodes:** `call`, `sitofp`, `uitofp`.
- **Beyond opcode/constant/SSA matching:** Yes — floor, ceil, trunc, rint, nearbyint, round, roundeven; intrinsic identity classification.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** FP rounding intrinsics and float semantics are not modeled

<a id="is6655"></a>

## IS6655 — `simplifyUnaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6650–6655](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6650-L6655). Kind: rewrite.
- **Rewrite:** fabs(X) returns X when value tracking proves X has a nonnegative sign bit.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — KnownFPClass sign-bit analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** fabs and KnownFPClass are not modeled

<a id="is6659"></a>

## IS6659 — `simplifyUnaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6657–6659](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6657-L6659). Kind: rewrite.
- **Rewrite:** fabs(X) returns X when X cannot be ordered below zero, is known non-NaN, and nsz is set.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — KnownFPClass sign/NaN analysis; nsz.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** fabs and KnownFPClass are not modeled

<a id="is6666"></a>

## IS6666 — `simplifyUnaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6663–6666](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6663-L6666). Kind: rewrite.
- **Rewrite:** Cancel bswap(bswap(X)) to X.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Modeled scalar LLVM bswap widths16,32,64; other LLVM widths such as128 lack genuine byte-reversal semantics in this interpreter and are excluded. Both applications use actual .intr__bswap.
- **Lean:** [Veir/InstSimplify/IS6666.lean](../../Veir/InstSimplify/IS6666.lean).
- **Theorems:** `Veir.InstSimplify.IS6666_valid`.
- **Details / missing facilities:** Own actual LLVM Pattern OpCode and kernel-checked Pattern.Valid theorem; no fallback interpreter failure.

<a id="is6671"></a>

## IS6671 — `simplifyUnaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6668–6671](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6668-L6671). Kind: rewrite.
- **Rewrite:** Cancel bitreverse(bitreverse(X)) to X.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths and intrinsic flags; all applicable operand commutations and normalized APInt constant spellings.
- **Lean:** [Veir/InstSimplify/IS6671.lean](../../Veir/InstSimplify/IS6671.lean).
- **Theorems:** `Veir.InstSimplify.IS6671_valid`.
- **Details / missing facilities:** Own actual LLVM Pattern OpCode and kernel-checked Pattern.Valid theorem; no fallback interpreter failure.

<a id="is6676"></a>

## IS6676 — `simplifyUnaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6674–6676](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6674-L6676). Kind: rewrite.
- **Rewrite:** Fold ctpop(X) to one when known-bits analysis proves X is a nonzero power of two.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — isKnownToBeAPowerOfTwo; assumption cache; dominator/context.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Requires proof-bearing value-tracking facts (known bits / guaranteed non-poison). MatchProg.inspectOperation facts are erased by Models; no such analysis semantics exist.

<a id="is6682"></a>

## IS6682 — `simplifyUnaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6678–6682](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6678-L6682). Kind: rewrite.
- **Rewrite:** Fold ctpop(X) to X when masked-value analysis proves every bit except the least significant bit is zero.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — MaskedValueIsZero analysis; scalar bit width.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Requires proof-bearing value-tracking facts (known bits / guaranteed non-poison). MatchProg.inspectOperation facts are erased by Models; no such analysis semantics exist.

<a id="is6689"></a>

## IS6689 — `simplifyUnaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6686–6689](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6686-L6689). Kind: rewrite.
- **Rewrite:** With reassoc, fold exp(log(X)) to X.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — reassoc; intrinsic pattern.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** exp/log semantics are not modeled

<a id="is6695"></a>

## IS6695 — `simplifyUnaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6692–6695](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6692-L6695). Kind: rewrite.
- **Rewrite:** With reassoc, fold exp2(log2(X)) to X.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — reassoc.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** exp2/log2 semantics are not modeled

<a id="is6701"></a>

## IS6701 — `simplifyUnaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6698–6701](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6698-L6701). Kind: rewrite.
- **Rewrite:** With reassoc, fold exp10(log10(X)) to X.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — reassoc.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** exp10/log10 semantics are not modeled

<a id="is6707"></a>

## IS6707 — `simplifyUnaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6704–6707](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6704-L6707). Kind: rewrite.
- **Rewrite:** With reassoc, fold log(exp(X)) to X.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — reassoc.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** log/exp semantics are not modeled

<a id="is6715"></a>

## IS6715 — `simplifyUnaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6710–6715](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6710-L6715). Kind: rewrite.
- **Rewrite:** With reassoc, fold log2(exp2(X)) or log2(pow(2.0,X)) to X.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — reassoc; pow base exactly 2.0.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** log2, exp2, and pow semantics are not modeled

<a id="is6724"></a>

## IS6724 — `simplifyUnaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6718–6724](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6718-L6724). Kind: rewrite.
- **Rewrite:** With reassoc, fold log10(exp10(X)) or log10(pow(10.0,X)) to X.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — reassoc; pow base exactly 10.0.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** log10, exp10, and pow semantics are not modeled

<a id="is6729"></a>

## IS6729 — `simplifyUnaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6727–6729](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6727-L6729). Kind: rewrite.
- **Rewrite:** Cancel vector.reverse(vector.reverse(X)) to X.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** vector.reverse semantics are not modeled

<a id="is6732"></a>

## IS6732 — `simplifyUnaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6730–6732](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6730-L6732). Kind: rewrite.
- **Rewrite:** vector.reverse(X) returns X when X is a vector splat.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — vector splat recognition.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** vector.reverse and vector splat reasoning are not modeled

<a id="is6735"></a>

## IS6735 — `simplifyUnaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6734–6735](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6734-L6735). Kind: rewrite.
- **Rewrite:** llvm.structured.gep(X) returns its sole pointer operand unchanged.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** structured_gep intrinsic is not in the LLVM operation model

<a id="is6760"></a>

## IS6760 — `foldMinMaxSharedOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6757–6760](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6757-L6760). Kind: schema.
- **Rewrite:** For max/min nesting with shared X or Y, return the inner min/max call when the inner and outer intrinsic IDs match.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — max/min intrinsic identity; shared operand matching.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar types/widths and instruction flags; all applicable operand commutations; constants compare normalized APInt bits.
- **Lean:** [Veir/InstSimplify/IS6760.lean](../../Veir/InstSimplify/IS6760.lean).
- **Theorems:** `Veir.InstSimplify.IS6760_valid`.
- **Details / missing facilities:** Actual LLVM Pattern OpCode and kernel-checked Pattern.Valid theorem.

<a id="is6763"></a>

## IS6763 — `foldMinMaxSharedOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6757–6763](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6757-L6763). Kind: schema.
- **Rewrite:** For max(min(X,Y),X) or the commuted/shared equivalent, return the shared operand when inner operation is inverse of outer operation.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — max/min intrinsic identity; shared operands; inverse operation.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar types/widths and instruction flags; all applicable operand commutations; constants compare normalized APInt bits.
- **Lean:** [Veir/InstSimplify/IS6763.lean](../../Veir/InstSimplify/IS6763.lean).
- **Theorems:** `Veir.InstSimplify.IS6763_valid`.
- **Details / missing facilities:** Actual LLVM Pattern OpCode and kernel-checked Pattern.Valid theorem.

<a id="is6804"></a>

## IS6804 — `foldMinimumMaximumSharedOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6795–6804](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6795-L6804). Kind: schema.
- **Rewrite:** For a minimum/maximum/minnum/maxnum/minimumnum/maximumnum call m(M0(X,Y),Z), return M0 when Z equals either inner operand.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — floating min/max intrinsic ID matching; shared operand.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM floating min/max intrinsic semantics are not modeled

<a id="is6820"></a>

## IS6820 — `foldMinimumMaximumSharedOp`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6812–6820](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6812-L6820). Kind: schema.
- **Rewrite:** For m(M0(X,Y),M1(X,Y)) with commuted inner operands allowed, return M0 when inner and outer intrinsic IDs match or are inverses.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — floating min/max intrinsic IDs; shared pair; commutation; inverse operation.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM floating min/max intrinsic semantics are not modeled

<a id="is6913"></a>

## IS6913 — `simplifySVEIntReduction`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6909–6913](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6909-L6913). Kind: schema.
- **Rewrite:** For eorv/orv/saddv/uaddv/umaxv, return zero if predicate operand is all false or reduction operand is zero.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — AArch64 SVE reduction; neutral element.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** AArch64 SVE intrinsics are not modeled

<a id="is6918"></a>

## IS6918 — `simplifySVEIntReduction`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6914–6918](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6914-L6918). Kind: schema.
- **Rewrite:** For andv/uminv, return all ones if predicate is all false or input is all ones.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — AArch64 SVE reduction; neutral element; result bit width.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** AArch64 SVE intrinsics are not modeled

<a id="is6922"></a>

## IS6922 — `simplifySVEIntReduction`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6919–6922](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6919-L6922). Kind: schema.
- **Rewrite:** For smaxv, return signed minimum if predicate is all false or input is signed minimum.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — AArch64 SVE reduction; neutral element; result bit width.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** AArch64 SVE intrinsics are not modeled

<a id="is6926"></a>

## IS6926 — `simplifySVEIntReduction`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6923–6926](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6923-L6926). Kind: schema.
- **Rewrite:** For sminv, return signed maximum if predicate is all false or input is signed maximum.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — AArch64 SVE reduction; neutral element; result bit width.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** AArch64 SVE intrinsics are not modeled

<a id="is6941"></a>

## IS6941 — `simplifySVEIntReduction`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6931–6941](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6931-L6941). Kind: schema.
- **Rewrite:** For andv/orv/smaxv/sminv/umaxv/uminv with all-true predicate, reduce a splat vector to its splat scalar value.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — AArch64 SVE reduction; splat vector; result type equality.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** AArch64 SVE intrinsics are not modeled

<a id="is6949"></a>

## IS6949 — `simplifySVEIntReduction`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6944–6949](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6944-L6949). Kind: schema.
- **Rewrite:** For eorv with all-true predicate, reducing a splat vector yields zero.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — AArch64 SVE reduction; splat vector.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** AArch64 SVE intrinsics are not modeled

<a id="is6963"></a>

## IS6963 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6959–6963](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6959-L6963). Kind: rewrite.
- **Rewrite:** llvm.get.active.lane.mask(A,B) is false when B is zero.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — result predicate type.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** get_active_lane_mask intrinsic is not modeled

<a id="is6981"></a>

## IS6981 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6972–6981](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6972-L6981). Kind: rewrite.
- **Rewrite:** If function has finite vscale maximum and return type is scalable, get.active.lane.mask(0, constant B) is all ones when B is at least min-lanes times maximum vscale.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — function vscale_range attribute; scalable vector minimum length; constant threshold.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** get_active_lane_mask and function vscale range analysis are not modeled

<a id="is6990"></a>

## IS6990 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6986–6990](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6986-L6990). Kind: rewrite.
- **Rewrite:** Cancel nested llvm.abs(abs(X, flags), flags2) to the inner abs call, irrespective of nsw on the outer call.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — inner intrinsic ID abs.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths and intrinsic flags; all applicable operand commutations and normalized APInt constant spellings.
- **Lean:** [Veir/InstSimplify/IS6990.lean](../../Veir/InstSimplify/IS6990.lean).
- **Theorems:** `Veir.InstSimplify.IS6990_valid`.
- **Details / missing facilities:** Own actual LLVM Pattern OpCode and kernel-checked Pattern.Valid theorem; no fallback interpreter failure.

<a id="is6996"></a>

## IS6996 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6993–6996](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6993-L6996). Kind: rewrite.
- **Rewrite:** Fold cttz(shl(1,X), is_zero_undef) to X.
- **Matched/replaced opcodes:** `call`, `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — shift base must be one.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths, all shift no-wrap/exact flags and all count intrinsic zero-poison flags; normalized APInt constants.
- **Lean:** [Veir/InstSimplify/IS6996.lean](../../Veir/InstSimplify/IS6996.lean).
- **Theorems:** `Veir.InstSimplify.IS6996_valid`.
- **Details / missing facilities:** Own actual LLVM shift/count pattern with exact returned source operand (or zero for7004) and kernel-checked validity.

<a id="is7002"></a>

## IS7002 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:6999–7002](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L6999-L7002). Kind: rewrite.
- **Rewrite:** The source m_Negative() guard admits every signed-negative constant APInt, not just all-ones; native MSB guard matches this exactly.
- **Matched/replaced opcodes:** `call`, `lshr`.
- **Beyond opcode/constant/SSA matching:** Yes — shift input all ones.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths, all shift no-wrap/exact flags and all count intrinsic zero-poison flags; normalized APInt constants.
- **Lean:** [Veir/InstSimplify/IS7002.lean](../../Veir/InstSimplify/IS7002.lean).
- **Theorems:** `Veir.InstSimplify.IS7002_valid`.
- **Details / missing facilities:** Own actual LLVM shift/count pattern with exact returned source operand (or zero for7004) and kernel-checked validity.

<a id="is7004"></a>

## IS7004 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7002–7004](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7002-L7004). Kind: rewrite.
- **Rewrite:** The source m_Negative() guard admits every signed-negative constant APInt, not just all-ones; native MSB guard matches this exactly.
- **Matched/replaced opcodes:** `call`, `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — shift input all ones.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths, all shift no-wrap/exact flags and all count intrinsic zero-poison flags; normalized APInt constants.
- **Lean:** [Veir/InstSimplify/IS7004.lean](../../Veir/InstSimplify/IS7004.lean).
- **Theorems:** `Veir.InstSimplify.IS7004_valid`.
- **Details / missing facilities:** Own actual LLVM shift/count pattern with exact returned source operand (or zero for7004) and kernel-checked validity.

<a id="is7009"></a>

## IS7009 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7007–7009](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7007-L7009). Kind: rewrite.
- **Rewrite:** llvm.pdep(X,0) returns zero.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** pdep is not represented by an LLVM operation opcode or interpreted intrinsic in the current model

<a id="is7011"></a>

## IS7011 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7010–7011](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7010-L7011). Kind: rewrite.
- **Rewrite:** llvm.pdep(0,M) returns zero.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** pdep is not represented by an LLVM operation opcode or interpreted intrinsic in the current model

<a id="is7013"></a>

## IS7013 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7012–7013](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7012-L7013). Kind: rewrite.
- **Rewrite:** llvm.pdep(X, all_ones) returns X.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** pdep is not represented by an LLVM operation opcode or interpreted intrinsic in the current model

<a id="is7018"></a>

## IS7018 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7016–7018](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7016-L7018). Kind: rewrite.
- **Rewrite:** llvm.pext(X,0) returns zero.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** pext is not represented by a named LLVM operation and the generic intrinsic interpreter does not model it

<a id="is7020"></a>

## IS7020 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7019–7020](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7019-L7020). Kind: rewrite.
- **Rewrite:** llvm.pext(0,M) returns zero.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** pext is not modeled by the Llvm.interpretOp'

<a id="is7022"></a>

## IS7022 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7021–7022](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7021-L7022). Kind: rewrite.
- **Rewrite:** llvm.pext(X, all_ones) returns X.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** pext is not modeled by the Llvm.interpretOp'

<a id="is7029"></a>

## IS7029 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7027–7029](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7027-L7029). Kind: rewrite.
- **Rewrite:** llvm.ptrmask(undef,Mask) or llvm.ptrmask(null,Mask) returns null of pointer type.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — pointer type; provenance note.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** ptrmask intrinsic semantics are not modeled

<a id="is7037"></a>

## IS7037 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7034–7037](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7034-L7037). Kind: rewrite.
- **Rewrite:** llvm.ptrmask(Ptr,ptrtoint-or-ptrtoaddr(Ptr)) returns Ptr when mask width is exactly pointer index width.
- **Matched/replaced opcodes:** `call`, `ptrtoint`, `ptrtoaddr`.
- **Beyond opcode/constant/SSA matching:** Yes — pointer provenance; DataLayout index width.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** ptrmask/ptrtoaddr provenance semantics are not modeled

<a id="is7043"></a>

## IS7043 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7040–7043](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7040-L7043). Kind: rewrite.
- **Rewrite:** llvm.ptrmask(Ptr,Mask) returns Ptr when Mask is all ones or undef; result attributes may be lost by this fold.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — pointer provenance; return attributes caveat.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** ptrmask semantics and call attribute preservation are not modeled

<a id="is7056"></a>

## IS7056 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7047–7056](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7047-L7056). Kind: rewrite.
- **Rewrite:** For an immediate constant ptrmask mask, compute known zero pointer bits and fold to Ptr when all bits cleared by the mask are already known zero from alignment.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — KnownBits/alignment analysis; immediate constant mask; pointer width.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** ptrmask plus KnownBits/alignment pointer analysis

<a id="is7066"></a>

## IS7066 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7063–7066](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7063-L7066). Kind: rewrite.
- **Rewrite:** For integer smax/smin/umax/umin, identical operands return the common operand.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths and intrinsic flags; all applicable operand commutations and normalized APInt constant spellings.
- **Lean:** [Veir/InstSimplify/IS7066.lean](../../Veir/InstSimplify/IS7066.lean).
- **Theorems:** `Veir.InstSimplify.IS7066_valid`.
- **Details / missing facilities:** Own actual LLVM Pattern OpCode and kernel-checked Pattern.Valid theorem; no fallback interpreter failure.

<a id="is7074"></a>

## IS7074 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7070–7074](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7070-L7074). Kind: rewrite.
- **Rewrite:** `smax(X,undef) -> signed_max`, `smin(X,undef) -> signed_min`, `umax(X,undef) -> unsigned_max`, and `umin(X,undef) -> 0`, after moving an immediate constant to the right operand.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — integer width; intrinsic-specific saturation point.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** The mlir__undef opcode exists, but Llvm.interpretOp' has no nondeterministic undef semantics (poison is distinct).

<a id="is7082"></a>

## IS7082 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7077–7082](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7077-L7082). Kind: rewrite.
- **Rewrite:** Clamp integer min/max to its absorbing extremum: `smax(X,signed_max) -> signed_max`, `smin(X,signed_min) -> signed_min`, `umax(X,unsigned_max) -> unsigned_max`, `umin(X,0) -> 0`. Either operand may be the constant; APInt matching permits poison vector lanes.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — poison-allowing constant match; integer width; saturation point.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar types/widths and instruction flags; all applicable operand commutations; constants compare normalized APInt bits.
- **Lean:** [Veir/InstSimplify/IS7082.lean](../../Veir/InstSimplify/IS7082.lean).
- **Theorems:** `Veir.InstSimplify.IS7082_valid`.
- **Details / missing facilities:** Actual LLVM Pattern OpCode and kernel-checked Pattern.Valid theorem.

<a id="is7089"></a>

## IS7089 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7084–7089](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7084-L7089). Kind: rewrite.
- **Rewrite:** Remove the identity extremum: `smax(X,signed_min) -> X`, `smin(X,signed_max) -> X`, `umax(X,0) -> X`, `umin(X,unsigned_max) -> X`. Either operand may be the constant; APInt matching permits poison vector lanes.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — poison-allowing constant match; integer width; inverse intrinsic.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar types/widths and instruction flags; all applicable operand commutations; constants compare normalized APInt bits.
- **Lean:** [Veir/InstSimplify/IS7089.lean](../../Veir/InstSimplify/IS7089.lean).
- **Theorems:** `Veir.InstSimplify.IS7089_valid`.
- **Details / missing facilities:** Actual LLVM Pattern OpCode and kernel-checked Pattern.Valid theorem.

<a id="is7102"></a>

## IS7102 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7092–7102](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7092-L7102). Kind: rewrite.
- **Rewrite:** For nested calls of the same integer min/max intrinsic, remove the outer call when an inner constant operand compares at least as extreme as the outer constant using the non-strict min/max predicate.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — same intrinsic ID; constant operands; predicate comparison; vector undef/splat limitations.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All four modeled scalar integer min/max operations, all widths, both inner/outer commutations and all normalized constant APInt spellings. Outer constants at either saturation boundary excluded to preserve earlier branch choice.
- **Lean:** [Veir/InstSimplify/IS7102.lean](../../Veir/InstSimplify/IS7102.lean).
- **Theorems:** `Veir.InstSimplify.IS7102_valid`.
- **Details / missing facilities:** Own LLVM pattern with native constant-order guard and syntactic inspection of first-inner-constant priority. The proof does not rely on erased inspection facts.

<a id="is7107"></a>

## IS7107 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7105–7107](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7105-L7107). Kind: schema.
- **Rewrite:** Apply foldMinMaxSharedOp in operand order (Op0,Op1) and return its result when non-null.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — nested min/max common operands.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All four modeled scalar integer min/max intrinsic operations; both inner and outer commutations.
- **Lean:** [Veir/InstSimplify/IS6760.lean](../../Veir/InstSimplify/IS6760.lean), [Veir/InstSimplify/IS6763.lean](../../Veir/InstSimplify/IS6763.lean).
- **Theorems:** `Veir.InstSimplify.IS6760_valid`, `Veir.InstSimplify.IS6763_valid`.
- **Shared implementation:** [IS6760](#is6760), [IS6763](#is6763). This caller is not an additional independent port.
- **Details / missing facilities:** Dispatch to foldMinMaxSharedOp, implemented by shared idempotence/absorption patterns parameterized over both operand orders.

<a id="is7109"></a>

## IS7109 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7108–7109](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7108-L7109). Kind: schema.
- **Rewrite:** Apply foldMinMaxSharedOp in commuted operand order (Op1,Op0) and return its result when non-null.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — nested min/max common operands; commuted.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All four modeled scalar integer min/max intrinsic operations; both inner and outer commutations.
- **Lean:** [Veir/InstSimplify/IS6760.lean](../../Veir/InstSimplify/IS6760.lean), [Veir/InstSimplify/IS6763.lean](../../Veir/InstSimplify/IS6763.lean).
- **Theorems:** `Veir.InstSimplify.IS6760_valid`, `Veir.InstSimplify.IS6763_valid`.
- **Shared implementation:** [IS6760](#is6760), [IS6763](#is6763). This caller is not an additional independent port.
- **Details / missing facilities:** Dispatch to foldMinMaxSharedOp, implemented by shared idempotence/absorption patterns parameterized over both operand orders.

<a id="is7114"></a>

## IS7114 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7111–7114](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7111-L7114). Kind: rewrite.
- **Rewrite:** For integer min/max, if value analysis proves Op0 <= Op1 (non-strict operation predicate), return Op0.
- **Matched/replaced opcodes:** `call`, `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — isICmpTrue; Q without undef; recursion limit.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Requires proof-bearing value-tracking ordering facts; inspectOperation facts are erased by MatchProg.Models.

<a id="is7116"></a>

## IS7116 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7115–7116](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7115-L7116). Kind: rewrite.
- **Rewrite:** For integer min/max, if value analysis proves Op1 <= Op0 (non-strict operation predicate), return Op1.
- **Matched/replaced opcodes:** `call`, `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — isICmpTrue; Q without undef; recursion limit.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Requires proof-bearing value-tracking ordering facts; inspectOperation facts are erased by MatchProg.Models.

<a id="is7125"></a>

## IS7125 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7122–7125](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7122-L7125). Kind: rewrite.
- **Rewrite:** For scmp/ucmp, return zero when equality between operands is proven.
- **Matched/replaced opcodes:** `call`, `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — signed or unsigned comparison proof; isICmpTrue.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** scmp/ucmp are not modeled and comparison proof needs analysis

<a id="is7130"></a>

## IS7130 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7128–7130](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7128-L7130). Kind: rewrite.
- **Rewrite:** For scmp/ucmp, return +1 when signed/unsigned greater-than is proven.
- **Matched/replaced opcodes:** `call`, `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — signed or unsigned comparison proof; isICmpTrue.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** scmp/ucmp are not modeled and comparison proof needs analysis

<a id="is7135"></a>

## IS7135 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7133–7135](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7133-L7135). Kind: rewrite.
- **Rewrite:** For scmp/ucmp, return -1 when signed/unsigned less-than is proven.
- **Matched/replaced opcodes:** `call`, `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — signed or unsigned comparison proof; isICmpTrue.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** scmp/ucmp are not modeled and comparison proof needs analysis

<a id="is7144"></a>

## IS7144 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7140–7144](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7140-L7144). Kind: rewrite.
- **Rewrite:** For umulh, or any mul-high operation on a one-bit result, multiplying by one yields zero.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — umulh or result bit width=1.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** umulh/smulh are not modeled by the LLVM interpreter

<a id="is7148"></a>

## IS7148 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7145–7148](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7145-L7148). Kind: rewrite.
- **Rewrite:** For umulh/smulh, if either operand is undef, choose zero because the other operand may be zero.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — undef semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** umulh/smulh are not modeled by the LLVM interpreter

<a id="is7152"></a>

## IS7152 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7150–7152](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7150-L7152). Kind: rewrite.
- **Rewrite:** For umulh/smulh, multiplication by zero yields zero.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** umulh/smulh are not modeled by the LLVM interpreter

<a id="is7160"></a>

## IS7160 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7156–7160](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7156-L7160). Kind: rewrite.
- **Rewrite:** For usub_with_overflow or ssub_with_overflow, X-X or either operand undef yields {0,false}.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — aggregate result layout; overflow result=false.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** overflow aggregate intrinsics are not modeled by the LLVM interpreter

<a id="is7167"></a>

## IS7167 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7163–7167](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7163-L7167). Kind: rewrite.
- **Rewrite:** For uadd_with_overflow or sadd_with_overflow, either operand undef yields {-1,false}.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — aggregate result layout; overflow result=false.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** overflow aggregate intrinsics are not modeled by the LLVM interpreter

<a id="is7178"></a>

## IS7178 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7174–7178](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7174-L7178). Kind: rewrite.
- **Rewrite:** For umul_with_overflow or smul_with_overflow, multiplying by zero yields {0,false}.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — aggregate result layout.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** overflow aggregate intrinsics are not modeled by the LLVM interpreter

<a id="is7182"></a>

## IS7182 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7179–7182](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7179-L7182). Kind: rewrite.
- **Rewrite:** For umul_with_overflow or smul_with_overflow, either undef operand yields {0,false}.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — aggregate result layout; undef semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** overflow aggregate intrinsics are not modeled by the LLVM interpreter

<a id="is7188"></a>

## IS7188 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7185–7188](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7185-L7188). Kind: rewrite.
- **Rewrite:** For uadd_sat, adding all-ones to either operand yields all-ones.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — unsigned saturation.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths and intrinsic flags; all applicable operand commutations and normalized APInt constant spellings.
- **Lean:** [Veir/InstSimplify/IS7188.lean](../../Veir/InstSimplify/IS7188.lean).
- **Theorems:** `Veir.InstSimplify.IS7188_valid`.
- **Details / missing facilities:** Own actual LLVM Pattern OpCode and kernel-checked Pattern.Valid theorem; no fallback interpreter failure.

<a id="is7196"></a>

## IS7196 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7190–7196](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7190-L7196). Kind: rewrite.
- **Rewrite:** For sadd_sat/uadd_sat, either undef operand yields all-ones; for signed add this chooses undef as bitwise complement of the other operand.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — saturating add; undef choice.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** The mlir__undef opcode exists, but Llvm.interpretOp' has no nondeterministic undef semantics (poison is distinct).

<a id="is7200"></a>

## IS7200 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7198–7200](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7198-L7200). Kind: rewrite.
- **Rewrite:** For signed or unsigned saturating add, X+0 returns X.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — zero is right operand.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths and intrinsic flags; all applicable operand commutations and normalized APInt constant spellings.
- **Lean:** [Veir/InstSimplify/IS7200.lean](../../Veir/InstSimplify/IS7200.lean).
- **Theorems:** `Veir.InstSimplify.IS7200_valid`.
- **Details / missing facilities:** Own actual LLVM Pattern OpCode and kernel-checked Pattern.Valid theorem; no fallback interpreter failure.

<a id="is7203"></a>

## IS7203 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7201–7203](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7201-L7203). Kind: rewrite.
- **Rewrite:** For signed or unsigned saturating add, 0+X returns X.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — zero is left operand.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths and intrinsic flags; all applicable operand commutations and normalized APInt constant spellings.
- **Lean:** [Veir/InstSimplify/IS7203.lean](../../Veir/InstSimplify/IS7203.lean).
- **Theorems:** `Veir.InstSimplify.IS7203_valid`.
- **Details / missing facilities:** Own actual LLVM Pattern OpCode and kernel-checked Pattern.Valid theorem; no fallback interpreter failure.

<a id="is7208"></a>

## IS7208 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7205–7208](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7205-L7208). Kind: rewrite.
- **Rewrite:** For usub_sat, 0-X or X-all_ones yields zero.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — unsigned saturation.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths and intrinsic flags; all applicable operand commutations and normalized APInt constant spellings.
- **Lean:** [Veir/InstSimplify/IS7208.lean](../../Veir/InstSimplify/IS7208.lean).
- **Theorems:** `Veir.InstSimplify.IS7208_valid`.
- **Details / missing facilities:** Own actual LLVM Pattern OpCode and kernel-checked Pattern.Valid theorem; no fallback interpreter failure.

<a id="is7213"></a>

## IS7213 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7210–7213](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7210-L7213). Kind: rewrite.
- **Rewrite:** `ssub.sat X,X` and `usub.sat X,X` fold to zero. The undef alternatives sharing this return are IS7213u.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — same operand or undef.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths and intrinsic flags; all applicable operand commutations and normalized APInt constant spellings. X-X branch; undef branch excluded because undef has no interpreter/runtime semantics.
- **Lean:** [Veir/InstSimplify/IS7213.lean](../../Veir/InstSimplify/IS7213.lean).
- **Theorems:** `Veir.InstSimplify.IS7213_valid`.
- **Details / missing facilities:** Own actual LLVM Pattern OpCode and kernel-checked Pattern.Valid theorem; no fallback interpreter failure.

<a id="is7213u"></a>

## IS7213u — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7210–7213](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7210-L7213). Kind: rewrite.
- **Rewrite:** `ssub.sat` or `usub.sat` with either operand undef folds to zero.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — same operand or undef.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Details / missing facilities:** LLVM undef is not represented by LLVM.Int and mlir__undef has no successful interpretation in Llvm.interpretOp'. Poison is a distinct value and cannot substitute for undef. No vacuous Pattern.Valid proof from the missing interpreter case is claimed.

<a id="is7216"></a>

## IS7216 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7215–7216](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7215-L7216). Kind: rewrite.
- **Rewrite:** For signed/unsigned saturating subtract, X-0 returns X.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — zero right operand.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths and intrinsic flags; all applicable operand commutations and normalized APInt constant spellings.
- **Lean:** [Veir/InstSimplify/IS7216.lean](../../Veir/InstSimplify/IS7216.lean).
- **Theorems:** `Veir.InstSimplify.IS7216_valid`.
- **Details / missing facilities:** Own actual LLVM Pattern OpCode and kernel-checked Pattern.Valid theorem; no fallback interpreter failure.

<a id="is7221"></a>

## IS7221 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7218–7221](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7218-L7221). Kind: schema.
- **Rewrite:** For load_relative with two constant operands, return simplifyRelativeLoad's result if its constant relocation/load pattern matches.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — constant operands; global relocation/constant memory analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple constant-argument adapter to simplifyRelativeLoad, whose relative-memory evaluation rule is inventoried at IS6576.

<a id="is7227"></a>

## IS7227 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7224–7227](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7224-L7227). Kind: rewrite.
- **Rewrite:** For powi(X, constant zero), return 1.0.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — constant integer exponent.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** powi/FP semantics are not modeled

<a id="is7230"></a>

## IS7230 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7228–7230](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7228-L7230). Kind: rewrite.
- **Rewrite:** For powi(X, constant one), return X.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — constant integer exponent.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** powi/FP semantics are not modeled

<a id="is7234"></a>

## IS7234 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7232–7234](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7232-L7234). Kind: delegation.
- **Rewrite:** Delegate ldexp to simplifyLdexp in non-strict mode.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — ldexp-specific rules.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple non-strict ldexp forwarding; concrete helper rules are inventoried at IS6585-IS6624.

<a id="is7238"></a>

## IS7238 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7236–7238](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7236-L7238). Kind: rewrite.
- **Rewrite:** For copysign(X,X), return X.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** copysign/FP semantics are not modeled

<a id="is7243"></a>

## IS7243 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7240–7243](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7240-L7243). Kind: rewrite.
- **Rewrite:** For copysign(-X,X) or copysign(X,-X), return the second operand.
- **Matched/replaced opcodes:** `call`, `fneg`.
- **Beyond opcode/constant/SSA matching:** Yes — same SSA operand under fneg.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** copysign/FP semantics are not modeled

<a id="is7249"></a>

## IS7249 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7245–7249](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7245-L7249). Kind: rewrite.
- **Rewrite:** For is_fpclass(X,mask), return true when mask contains every FP class flag.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — constant mask; fcAllFlags.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** is_fpclass and FP class model are not modeled

<a id="is7251"></a>

## IS7251 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7250–7251](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7250-L7251). Kind: rewrite.
- **Rewrite:** For is_fpclass(X,mask), return false when mask contains no FP class flags.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — constant mask.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** is_fpclass is not modeled

<a id="is7253"></a>

## IS7253 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7252–7253](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7252-L7253). Kind: rewrite.
- **Rewrite:** For is_fpclass(undef,mask), return undef unless mask already matched the all-classes or no-classes cases.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — undef semantics; constant mask.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** is_fpclass/FP class semantics are not modeled

<a id="is7271"></a>

## IS7271 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7268–7271](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7268-L7271). Kind: rewrite.
- **Rewrite:** For minnum/minimum/maxnum/maximum/minimumnum/maximumnum with identical operands, return the operand (ignoring NaN quieting).
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — floating min/max intrinsic identity; same SSA operands.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Floating min/max intrinsics are not modeled

<a id="is7327"></a>

## IS7327 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7324–7327](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7324-L7327). Kind: schema.
- **Rewrite:** For floating min/max with a constant operand, return the other operand when OptimizeConstMinMax classifies the constant as UseOtherVal or UseEither; this may ignore NaN quieting.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — min/max intrinsic-specific NaN/infinity/saturation cases; vector constant elementwise restrictions; fast-math flags.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Floating min/max and IEEE NaN semantics are not modeled

<a id="is7329"></a>

## IS7329 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7328–7329](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7328-L7329). Kind: schema.
- **Rewrite:** For floating min/max with a constant operand, return the constructed new constant when OptimizeConstMinMax classifies it UseNewConstVal; quiet NaNs as specified by intrinsic semantics.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — NaN quieting; constant splat or fixed-vector construction; fast-math flags.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Floating min/max and IEEE NaN semantics are not modeled

<a id="is7335"></a>

## IS7335 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7332–7335](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7332-L7335). Kind: schema.
- **Rewrite:** Apply floating minimum/maximum shared-operand fold in (Op0,Op1) order.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — nested min/max pair; shared operands.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple forwarding of foldMinimumMaximumSharedOp, whose concrete min/max rewrites are inventoried at IS6804/IS6820.

<a id="is7337"></a>

## IS7337 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7336–7337](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7336-L7337). Kind: schema.
- **Rewrite:** Apply floating minimum/maximum shared-operand fold in commuted (Op1,Op0) order.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — nested min/max pair; shared operands; commuted.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple commuted forwarding of foldMinimumMaximumSharedOp, whose concrete min/max rewrites are inventoried at IS6804/IS6820.

<a id="is7348"></a>

## IS7348 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7340–7348](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7340-L7348). Kind: rewrite.
- **Rewrite:** For vector_extract(vector_insert(Y,X,0),0), return X when constant extract index is zero and X's type equals the intrinsic return type.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — vector intrinsic identities; constant index zero; type equality.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** vector_extract/vector_insert intrinsics are not modeled

<a id="is7362"></a>

## IS7362 — `simplifyBinaryIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7351–7362](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7351-L7362). Kind: delegation.
- **Rewrite:** Delegate recognized AArch64 SVE integer reductions to simplifySVEIntReduction.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — AArch64 SVE reductions.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple SVE reduction forwarding; concrete helper rules are inventoried at IS6913-IS6949.

<a id="is7395"></a>

## IS7395 — `simplifyIdentityInterleave`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7369–7395](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7369-L7395). Kind: rewrite.
- **Rewrite:** Cancel interleaveN(extractvalue(deinterleaveN(X),0), …, extractvalue(deinterleaveN(X),N-1)) to X when arity equals factor, each single extract index equals its position, and all extracts use the same deinterleave intrinsic call of the matching factor.
- **Matched/replaced opcodes:** `call`, `extractvalue`.
- **Beyond opcode/constant/SSA matching:** Yes — interleave/deinterleave intrinsic factor; same SSA deinterleave call; aggregate extraction.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM extractvalue enum/verifier declarations exist, but Llvm.interpretOp′ has no semantics for these aggregate/vector operations. Interpreter failure is not counted as a proof.

<a id="is7406"></a>

## IS7406 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7400–7406](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7400-L7406). Kind: schema.
- **Rewrite:** If the intrinsic is defined to propagate poison and any argument is poison, return poison of the intrinsic return type.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — intrinsicPropagatesPoison metadata.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths and all intrinsic flags; poison positions or constant argument combinations covered as applicable. Bswap only16/32/64; no claim is made for the identity fallback on other bswap widths.
- **Lean:** [Veir/InstSimplify/IS7406.lean](../../Veir/InstSimplify/IS7406.lean).
- **Theorems:** `Veir.InstSimplify.IS7406.bswap_0_valid`, `Veir.InstSimplify.IS7406.bitreverse_0_valid`, `Veir.InstSimplify.IS7406.ctpop_0_valid`, `Veir.InstSimplify.IS7406.ctlz_0_valid`, `Veir.InstSimplify.IS7406.cttz_0_valid`, `Veir.InstSimplify.IS7406.abs_0_valid`, `Veir.InstSimplify.IS7406.smax_0_valid`, `Veir.InstSimplify.IS7406.smax_1_valid`, `Veir.InstSimplify.IS7406.smin_0_valid`, `Veir.InstSimplify.IS7406.smin_1_valid`, `Veir.InstSimplify.IS7406.umax_0_valid`, `Veir.InstSimplify.IS7406.umax_1_valid`, `Veir.InstSimplify.IS7406.umin_0_valid`, `Veir.InstSimplify.IS7406.umin_1_valid`, `Veir.InstSimplify.IS7406.saddSat_0_valid`, `Veir.InstSimplify.IS7406.saddSat_1_valid`, `Veir.InstSimplify.IS7406.uaddSat_0_valid`, `Veir.InstSimplify.IS7406.uaddSat_1_valid`, `Veir.InstSimplify.IS7406.ssubSat_0_valid`, `Veir.InstSimplify.IS7406.ssubSat_1_valid`, `Veir.InstSimplify.IS7406.usubSat_0_valid`, `Veir.InstSimplify.IS7406.usubSat_1_valid`, `Veir.InstSimplify.IS7406.sshlSat_0_valid`, `Veir.InstSimplify.IS7406.sshlSat_1_valid`, `Veir.InstSimplify.IS7406.ushlSat_0_valid`, `Veir.InstSimplify.IS7406.ushlSat_1_valid`, `Veir.InstSimplify.IS7406.fshl_0_valid`, `Veir.InstSimplify.IS7406.fshl_1_valid`, `Veir.InstSimplify.IS7406.fshl_2_valid`, `Veir.InstSimplify.IS7406.fshr_0_valid`, `Veir.InstSimplify.IS7406.fshr_1_valid`, `Veir.InstSimplify.IS7406.fshr_2_valid`.
- **Details / missing facilities:** Own actual LLVM patterns with kernel-checked validity; generic call_intrinsic fallback is never used.

<a id="is7413"></a>

## IS7413 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7410–7413](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7410-L7413). Kind: schema.
- **Rewrite:** When every intrinsic argument is constant, return the result of LLVM ConstantFoldIntrinsic if it succeeds.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — all-constant args; intrinsic-specific constant evaluation; DataLayout/function context.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** 18 actual interpreted scalar integer intrinsics, all legal modeled widths and properties; bswap restricted to16/32/64 because wider LLVM bswap is unmodeled. LLVM ConstantInt operands use mlir__constant encoding with arbitrary normalized APInt payloads; alternate VeIR mlir__zero encoding is not required for this source port.
- **Lean:** [Veir/InstSimplify/IS7413.lean](../../Veir/InstSimplify/IS7413.lean).
- **Theorems:** `Veir.InstSimplify.IS7413.bswap_valid`, `Veir.InstSimplify.IS7413.bswap_poison_valid`, `Veir.InstSimplify.IS7413.bitreverse_valid`, `Veir.InstSimplify.IS7413.bitreverse_poison_valid`, `Veir.InstSimplify.IS7413.ctpop_valid`, `Veir.InstSimplify.IS7413.ctpop_poison_valid`, `Veir.InstSimplify.IS7413.ctlz_valid`, `Veir.InstSimplify.IS7413.ctlz_poison_valid`, `Veir.InstSimplify.IS7413.cttz_valid`, `Veir.InstSimplify.IS7413.cttz_poison_valid`, `Veir.InstSimplify.IS7413.abs_valid`, `Veir.InstSimplify.IS7413.abs_poison_valid`, `Veir.InstSimplify.IS7413.smax_valid`, `Veir.InstSimplify.IS7413.smax_poison_valid`, `Veir.InstSimplify.IS7413.smin_valid`, `Veir.InstSimplify.IS7413.smin_poison_valid`, `Veir.InstSimplify.IS7413.umax_valid`, `Veir.InstSimplify.IS7413.umax_poison_valid`, `Veir.InstSimplify.IS7413.umin_valid`, `Veir.InstSimplify.IS7413.umin_poison_valid`, `Veir.InstSimplify.IS7413.saddSat_valid`, `Veir.InstSimplify.IS7413.saddSat_poison_valid`, `Veir.InstSimplify.IS7413.uaddSat_valid`, `Veir.InstSimplify.IS7413.uaddSat_poison_valid`, `Veir.InstSimplify.IS7413.ssubSat_valid`, `Veir.InstSimplify.IS7413.ssubSat_poison_valid`, `Veir.InstSimplify.IS7413.usubSat_valid`, `Veir.InstSimplify.IS7413.usubSat_poison_valid`, `Veir.InstSimplify.IS7413.sshlSat_valid`, `Veir.InstSimplify.IS7413.sshlSat_poison_valid`, `Veir.InstSimplify.IS7413.ushlSat_valid`, `Veir.InstSimplify.IS7413.ushlSat_poison_valid`, `Veir.InstSimplify.IS7413.fshl_valid`, `Veir.InstSimplify.IS7413.fshl_poison_valid`, `Veir.InstSimplify.IS7413.fshr_valid`, `Veir.InstSimplify.IS7413.fshr_poison_valid`.
- **Details / missing facilities:** Exact actual LLVM constant-fold outputs:36 patterns split numeric versus poison result class. All constant APInt spellings normalize before evaluation; poison outputs emit mlir__poison.

<a id="is7424"></a>

## IS7424 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7417–7424](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7417-L7424). Kind: rewrite.
- **Rewrite:** For zero-operand vscale, return a constant when function context exists and getVScaleRange has a single known element.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — function vscale range analysis; 64-bit range.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** vscale intrinsic and function range analysis are not modeled

<a id="is7433"></a>

## IS7433 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7430–7433](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7430-L7433). Kind: schema.
- **Rewrite:** Apply simplifyIdentityInterleave to all-arity interleave/deinterleave argument patterns and return its non-null result.
- **Matched/replaced opcodes:** `call`, `extractvalue`.
- **Beyond opcode/constant/SSA matching:** Yes — factor and shared-call matching.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple forwarding of simplifyIdentityInterleave; its concrete rewrite is inventoried at IS7395.

<a id="is7436"></a>

## IS7436 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7435–7436](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7435-L7436). Kind: delegation.
- **Rewrite:** For one-argument intrinsics, delegate to simplifyUnaryIntrinsic with call fast-math flags and query.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — unary intrinsic rule schema.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Source unary-intrinsic delegation: bswap and bitreverse scalar syntax rewrites. CTPOP analysis-only branches unsupported as documented in6676/6682; other source unary operations unmodeled.
- **Lean:** [Veir/InstSimplify/IS6666.lean](../../Veir/InstSimplify/IS6666.lean), [Veir/InstSimplify/IS6671.lean](../../Veir/InstSimplify/IS6671.lean).
- **Theorems:** `Veir.InstSimplify.IS6666_valid`, `Veir.InstSimplify.IS6671_valid`.
- **Shared implementation:** [IS6666](#is6666), [IS6671](#is6671). This caller is not an additional independent port.
- **Details / missing facilities:** Dispatcher shares the concrete unary implementation, with unsupported source forms explicitly excluded.

<a id="is7439"></a>

## IS7439 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7438–7439](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7438-L7439). Kind: delegation.
- **Rewrite:** For two-argument intrinsics, delegate to simplifyBinaryIntrinsic with intrinsic ID, return type, operands, flags, and query.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — binary intrinsic rule schema.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** Dispatcher for represented scalar integer binary intrinsic rules: abs, ctlz/cttz, signed/unsigned minmax, signed/unsigned saturating add/sub. Floating point/vector/undef branches remain explicitly unsupported in their individual records.
- **Lean:** [Veir/InstSimplify/IS6760.lean](../../Veir/InstSimplify/IS6760.lean), [Veir/InstSimplify/IS6763.lean](../../Veir/InstSimplify/IS6763.lean), [Veir/InstSimplify/IS6990.lean](../../Veir/InstSimplify/IS6990.lean), [Veir/InstSimplify/IS6996.lean](../../Veir/InstSimplify/IS6996.lean), [Veir/InstSimplify/IS7002.lean](../../Veir/InstSimplify/IS7002.lean), [Veir/InstSimplify/IS7004.lean](../../Veir/InstSimplify/IS7004.lean), [Veir/InstSimplify/IS7066.lean](../../Veir/InstSimplify/IS7066.lean), [Veir/InstSimplify/IS7082.lean](../../Veir/InstSimplify/IS7082.lean), [Veir/InstSimplify/IS7089.lean](../../Veir/InstSimplify/IS7089.lean), [Veir/InstSimplify/IS7102.lean](../../Veir/InstSimplify/IS7102.lean), [Veir/InstSimplify/IS7188.lean](../../Veir/InstSimplify/IS7188.lean), [Veir/InstSimplify/IS7200.lean](../../Veir/InstSimplify/IS7200.lean), [Veir/InstSimplify/IS7203.lean](../../Veir/InstSimplify/IS7203.lean), [Veir/InstSimplify/IS7208.lean](../../Veir/InstSimplify/IS7208.lean), [Veir/InstSimplify/IS7213.lean](../../Veir/InstSimplify/IS7213.lean), [Veir/InstSimplify/IS7216.lean](../../Veir/InstSimplify/IS7216.lean).
- **Theorems:** `Veir.InstSimplify.IS6760_valid`, `Veir.InstSimplify.IS6763_valid`, `Veir.InstSimplify.IS6990_valid`, `Veir.InstSimplify.IS6996_valid`, `Veir.InstSimplify.IS7002_valid`, `Veir.InstSimplify.IS7004_valid`, `Veir.InstSimplify.IS7066_valid`, `Veir.InstSimplify.IS7082_valid`, `Veir.InstSimplify.IS7089_valid`, `Veir.InstSimplify.IS7102_valid`, `Veir.InstSimplify.IS7188_valid`, `Veir.InstSimplify.IS7200_valid`, `Veir.InstSimplify.IS7203_valid`, `Veir.InstSimplify.IS7208_valid`, `Veir.InstSimplify.IS7213_valid`, `Veir.InstSimplify.IS7216_valid`.
- **Shared implementation:** [IS6990](#is6990), [IS6996](#is6996), [IS7002](#is7002), [IS7004](#is7004), [IS7066](#is7066), [IS7082](#is7082), [IS7089](#is7089), [IS7102](#is7102), [IS6760](#is6760), [IS6763](#is6763), [IS7188](#is7188), [IS7200](#is7200), [IS7203](#is7203), [IS7208](#is7208), [IS7213](#is7213), [IS7216](#is7216). This caller is not an additional independent port.
- **Details / missing facilities:** Source dispatch only; all represented scalar local rewrites are linked to their own proven implementation records.

<a id="is7450"></a>

## IS7450 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7443–7450](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7443-L7450). Kind: rewrite.
- **Rewrite:** For masked_load or masked_gather with mask all zeros or poison, return passthrough argument Args[2].
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — mask operand Args[1]; passthrough Args[2]; masked memory intrinsic semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** masked memory intrinsics are not modeled by the Llvm.interpretOp'

<a id="is7459"></a>

## IS7459 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7453–7459](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7453-L7459). Kind: rewrite.
- **Rewrite:** For fshl/fshr with both data operands undef, return undef of the result type.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — undef semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** The mlir__undef opcode exists, but Llvm.interpretOp' has no nondeterministic undef semantics (poison is distinct).

<a id="is7463"></a>

## IS7463 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7461–7463](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7461-L7463). Kind: rewrite.
- **Rewrite:** For fshl/fshr with undef shift amount, treat the shift as zero and return operand 0 for fshl or operand 1 for fshr.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — undef shift semantics; intrinsic ID selects result operand.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** The mlir__undef opcode exists, but Llvm.interpretOp' has no nondeterministic undef semantics (poison is distinct).

<a id="is7471"></a>

## IS7471 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7466–7471](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7466-L7471). Kind: rewrite.
- **Rewrite:** For constant shift amount, reduce it modulo scalar bit width; if effective shift is zero return operand 0 for fshl or operand 1 for fshr.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — APInt shift width/modulo; intrinsic ID selects result operand.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar types/widths and instruction flags; all applicable operand commutations; constants compare normalized APInt bits.
- **Lean:** [Veir/InstSimplify/IS7471.lean](../../Veir/InstSimplify/IS7471.lean).
- **Theorems:** `Veir.InstSimplify.IS7471_valid`.
- **Details / missing facilities:** Actual LLVM Pattern OpCode and kernel-checked Pattern.Valid theorem.

<a id="is7480"></a>

## IS7480 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7473–7480](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7473-L7480). Kind: rewrite.
- **Rewrite:** Fold fshl((lshr X,C1),(shl X,C2),C1) or fshr((lshr X,C1),(shl X,C2),C2) to X when C1+C2 equals bit width and intrinsic shift amount equals C1 for fshl or C2 for fshr.
- **Matched/replaced opcodes:** `call`, `lshr`, `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — same SSA X; constant shifts; sum equals scalar bit width.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths and signedness, both funnel directions, every normalized APInt shift spelling and all lshr exact/shl nsw/nuw flags; effective shift nonzero preserves the earlier return branch.
- **Lean:** [Veir/InstSimplify/IS7480.lean](../../Veir/InstSimplify/IS7480.lean).
- **Theorems:** `Veir.InstSimplify.IS7480_valid`.
- **Details / missing facilities:** Own LLVM lshr/shl/funnel pattern returns the exact matched shared input; native guard checks source APInt sum and effective selected shift; kernel proof reconstructs bits or refines from operational poison flags.

<a id="is7485"></a>

## IS7485 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7483–7485](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7483-L7485). Kind: rewrite.
- **Rewrite:** For fshl/fshr with both data operands zero, return zero for any shift amount.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths and intrinsic flags; all applicable operand commutations and normalized APInt constant spellings.
- **Lean:** [Veir/InstSimplify/IS7485.lean](../../Veir/InstSimplify/IS7485.lean).
- **Theorems:** `Veir.InstSimplify.IS7485_valid`.
- **Details / missing facilities:** Own actual LLVM Pattern OpCode and kernel-checked Pattern.Valid theorem; no fallback interpreter failure.

<a id="is7489"></a>

## IS7489 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7487–7489](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7487-L7489). Kind: rewrite.
- **Rewrite:** For fshl/fshr with both data operands all ones, return all ones for any shift amount.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** No.
- **Result:** Succeeded — `Pattern.Valid` proven.
- **Port/proof domain:** All modeled scalar integer widths and intrinsic flags; all applicable operand commutations and normalized APInt constant spellings.
- **Lean:** [Veir/InstSimplify/IS7489.lean](../../Veir/InstSimplify/IS7489.lean).
- **Theorems:** `Veir.InstSimplify.IS7489_valid`.
- **Details / missing facilities:** Own actual LLVM Pattern OpCode and kernel-checked Pattern.Valid theorem; no fallback interpreter failure.

<a id="is7494"></a>

## IS7494 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7492–7494](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7492-L7494). Kind: delegation.
- **Rewrite:** Delegate experimental_constrained_fma to shared simplifyFPOp using call exception behavior and rounding mode.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — constrained FP exception behavior; rounding mode.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Floating-point operations and constrained environment are not modeled by Llvm.interpretOp′

<a id="is7497"></a>

## IS7497 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7495–7497](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7495-L7497). Kind: delegation.
- **Rewrite:** Delegate fma/fmuladd to shared simplifyFPOp under ignore-exceptions, nearest-ties-to-even environment.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — default FMF; fixed exception/rounding environment.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple forwarding of unconstrained fma/fmuladd to shared simplifyFPOp under its default FP environment; shared rules are independently inventoried at IS5998-IS6024.

<a id="is7513"></a>

## IS7513 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7508–7513](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7508-L7513). Kind: rewrite.
- **Rewrite:** For smul_fix/smul_fix_sat, canonicalize constants to operand 1 then return zero when that operand is zero.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — constant operand canonicalization; fixed-point scale operand.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** smul_fix and smul_fix_sat are not modeled by the LLVM interpreter

<a id="is7517"></a>

## IS7517 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7515–7517](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7515-L7517). Kind: rewrite.
- **Rewrite:** For smul_fix/smul_fix_sat, return zero when canonicalized operand 1 is undef.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — constant operand canonicalization; undef semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** smul_fix and smul_fix_sat are not modeled by the LLVM interpreter

<a id="is7524"></a>

## IS7524 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7519–7524](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7519-L7524). Kind: rewrite.
- **Rewrite:** For smul_fix/smul_fix_sat, return operand 0 when operand 1 equals 1<<Scale, provided the one-bit constant is nonnegative at result width; Scale is the constant third operand.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — constant scale operand; result scalar width; APInt one-bit construction.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** smul_fix/smul_fix_sat are not modeled

<a id="is7541"></a>

## IS7541 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7532–7541](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7532-L7541). Kind: rewrite.
- **Rewrite:** For vector_insert(Y, vector_extract(X,0),0), return X when Y is undef or the same SSA vector as X, index is constant zero, and X type equals return type.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — vector intrinsic identity; constant index; type match.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** vector_insert/vector_extract intrinsics are not modeled

<a id="is7551"></a>

## IS7551 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7545–7551](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7545-L7551). Kind: rewrite.
- **Rewrite:** Fold vector_splice_right(vector_splice_left(poison,X,Offset),poison,Offset) to X when the inner offset is the identical SSA value and the right passthrough is poison.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — matching offset SSA operand; poison operands.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** vector_splice_left/right intrinsics are not modeled

<a id="is7558"></a>

## IS7558 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7556–7558](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7556-L7558). Kind: rewrite.
- **Rewrite:** For vector_splice_left/right, an undef offset yields poison of the result vector type.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — undef offset; vector result type.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** vector_splice_left/right intrinsics are not modeled

<a id="is7571"></a>

## IS7571 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7560–7571](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7560-L7571). Kind: rewrite.
- **Rewrite:** For vector_splice_left/right, return poison when known unsigned minimum offset exceeds the maximum possible vector element count; scalable count uses function vscale range when available, otherwise full range.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — ConstantRange known bits; vector min element count; scalable vscale range/function context.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** vector_splice and ConstantRange/vscale analysis are not modeled

<a id="is7575"></a>

## IS7575 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7573–7575](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7573-L7575). Kind: rewrite.
- **Rewrite:** For a proven zero splice offset, vector_splice_left(A,B,0) returns A and vector_splice_right(A,B,0) returns B.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — ConstantRange proves singleton zero; intrinsic ID selects operand.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** vector_splice and ConstantRange analysis are not modeled

<a id="is7580"></a>

## IS7580 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7578–7580](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7578-L7580). Kind: delegation.
- **Rewrite:** Delegate constrained fadd to simplifyFAddInst with its FMF, exception behavior, and rounding mode.
- **Matched/replaced opcodes:** `call`, `fadd`.
- **Beyond opcode/constant/SSA matching:** Yes — constrained FP metadata.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Float semantics and constrained FP environment are absent from Llvm.interpretOp′

<a id="is7582"></a>

## IS7582 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7581–7582](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7581-L7582). Kind: delegation.
- **Rewrite:** Delegate constrained fsub to simplifyFSubInst with its FMF, exception behavior, and rounding mode.
- **Matched/replaced opcodes:** `call`, `fsub`.
- **Beyond opcode/constant/SSA matching:** Yes — constrained FP metadata.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Float semantics and constrained FP environment are absent from Llvm.interpretOp′

<a id="is7584"></a>

## IS7584 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7583–7584](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7583-L7584). Kind: delegation.
- **Rewrite:** Delegate constrained fmul to simplifyFMulInst with its FMF, exception behavior, and rounding mode.
- **Matched/replaced opcodes:** `call`, `fmul`.
- **Beyond opcode/constant/SSA matching:** Yes — constrained FP metadata.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Float semantics and constrained FP environment are absent from Llvm.interpretOp′

<a id="is7586"></a>

## IS7586 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7585–7586](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7585-L7586). Kind: delegation.
- **Rewrite:** Delegate constrained fdiv to simplifyFDivInst with its FMF, exception behavior, and rounding mode.
- **Matched/replaced opcodes:** `call`, `fdiv`.
- **Beyond opcode/constant/SSA matching:** Yes — constrained FP metadata.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Float semantics and constrained FP environment are absent from Llvm.interpretOp′

<a id="is7588"></a>

## IS7588 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7587–7588](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7587-L7588). Kind: delegation.
- **Rewrite:** Delegate constrained frem to simplifyFRemInst with its FMF, exception behavior, and rounding mode.
- **Matched/replaced opcodes:** `call`, `frem`.
- **Beyond opcode/constant/SSA matching:** Yes — constrained FP metadata.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Float semantics and constrained FP environment are absent from Llvm.interpretOp′

<a id="is7590"></a>

## IS7590 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7589–7590](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7589-L7590). Kind: delegation.
- **Rewrite:** Delegate constrained ldexp to simplifyLdexp in strict mode.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — strict flag; constrained FP environment.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** ldexp and constrained FP semantics are not modeled

<a id="is7599"></a>

## IS7599 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7595–7599](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7595-L7599). Kind: rewrite.
- **Rewrite:** Cancel vp_reverse(vp_reverse(X, mask1, EVL), mask2, EVL) to X when both use the exact same EVL SSA operand; mask operands may differ.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — same EVL SSA operand; vector predication intrinsic.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** vp_reverse intrinsic semantics are not modeled

<a id="is7603"></a>

## IS7603 — `simplifyIntrinsic`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7601–7603](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7601-L7603). Kind: rewrite.
- **Rewrite:** For vp_reverse(X,mask,EVL), return X unchanged when X is a splat, regardless of mask or EVL.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — splat vector recognition; mask/EVL are irrelevant after splat proof.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** vp_reverse and vector splat semantics are not modeled

<a id="is7626"></a>

## IS7626 — `simplifyIntrinsic(CallBase)`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7622–7626](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7622-L7626). Kind: rewrite.
- **Rewrite:** For gc.relocate, if either derived pointer or base pointer is undef, return undef of the relocation result type.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — GC relocation intrinsic; undef semantics.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** GC relocation semantics are not modeled

<a id="is7635"></a>

## IS7635 — `simplifyIntrinsic(CallBase)`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7629–7635](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7629-L7635). Kind: rewrite.
- **Rewrite:** For gc.relocate returning pointer type, a null derived pointer becomes null of the result pointer type; this assumes most collectors preserve null relocation.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — derived ptr null; collector assumption; result pointer type.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** GC strategy/relocation semantics are not modeled

<a id="is7648"></a>

## IS7648 — `simplifyIntrinsic(CallBase)`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7643–7648](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7643-L7648). Kind: delegation.
- **Rewrite:** For other intrinsic calls, derive FP exception behavior and rounding from constrained call metadata (default ignore/nearest-even), then delegate to simplifyIntrinsic by intrinsic ID and return type.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — constrained FP metadata; function query.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Generic metadata/context adapter and forwarder to the intrinsic-ID simplifier, whose concrete semantic cases are separately inventoried. It has no single additional intrinsic semantics blocker of its own.

<a id="is7673"></a>

## IS7673 — `tryConstantFoldCall`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7660–7673](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7660-L7673). Kind: schema.
- **Rewrite:** When target library analysis says a direct callee can constant-fold and every non-metadata argument is a constant, return LLVM ConstantFoldCall result.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — TargetLibraryInfo; direct function callee; all constant arguments except metadata; operand bundles excluded.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM call constant folder and TargetLibraryInfo semantics are not modeled

<a id="is7689"></a>

## IS7689 — `simplifyCall`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7686–7689](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7686-L7689). Kind: rewrite.
- **Rewrite:** A call through undef or null callee yields poison of call result type, except musttail calls are rejected before this rule.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — musttail exclusion; callee is undef or null.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Call semantics and musttail constraints are not modeled by current rewrite proof semantics

<a id="is7692"></a>

## IS7692 — `simplifyCall`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7691–7692](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7691-L7692). Kind: delegation.
- **Rewrite:** If tryConstantFoldCall succeeds, return its folded result.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — TargetLibraryInfo; constant args.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple forwarding of tryConstantFoldCall result; the call-evaluation boundary is inventoried at IS7673.

<a id="is7697"></a>

## IS7697 — `simplifyCall`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7694–7697](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7694-L7697). Kind: delegation.
- **Rewrite:** For direct intrinsic callee (after call constant folding fails), invoke simplifyIntrinsic(CallBase) and return any non-null simplification.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — direct intrinsic function; intrinsic-specific simplifier.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Generic forwarding return from simplifyCall to simplifyIntrinsic(CallBase); concrete intrinsic cases are separately inventoried and some are modeled. The broad unsupported label does not identify an independent algebraic rule.

<a id="is7706"></a>

## IS7706 — `simplifyConstrainedFPCall`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7703–7706](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7703-L7706). Kind: delegation.
- **Rewrite:** For constrained FP call, first return the constant-folded result if tryConstantFoldCall succeeds.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — constrained FP call; TargetLibraryInfo.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM call constant folder and constrained FP semantics are not modeled

<a id="is7708"></a>

## IS7708 — `simplifyConstrainedFPCall`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7707–7708](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7707-L7708). Kind: delegation.
- **Rewrite:** For constrained FP call, return simplifyIntrinsic(CallBase) result when non-null after constant folding fails.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — constrained FP metadata.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Floating semantics and constrained FP metadata are not modeled

<a id="is7716"></a>

## IS7716 — `simplifyFreezeInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7713–7716](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7713-L7716). Kind: rewrite.
- **Rewrite:** Remove freeze(X) and return X when value tracking proves X is neither undef nor poison.
- **Matched/replaced opcodes:** `freeze`.
- **Beyond opcode/constant/SSA matching:** Yes — isGuaranteedNotToBeUndefOrPoison; assumption/context/dominator analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Requires proof-bearing value-tracking facts (known bits / guaranteed non-poison). MatchProg.inspectOperation facts are erased by Models; no such analysis semantics exist.

<a id="is7731"></a>

## IS7731 — `simplifyLoadInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7725–7731](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7725-L7731). Kind: rewrite.
- **Rewrite:** For nonvolatile load from a constant pointer operand, constant-fold the loaded value from that pointer.
- **Matched/replaced opcodes:** `load`.
- **Beyond opcode/constant/SSA matching:** Yes — nonvolatile load; constant pointer; DataLayout and memory constant folding.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM constant-memory load folder is not modeled

<a id="is7743"></a>

## IS7743 — `simplifyLoadInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7736–7743](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7736-L7743). Kind: rewrite.
- **Rewrite:** If underlying object is a constant global with definitive initializer and ConstantFoldLoadFromUniformValue proves initializer uniform for requested load type, return that constant regardless of offset.
- **Matched/replaced opcodes:** `load`.
- **Beyond opcode/constant/SSA matching:** Yes — constant global; definitive initializer; uniform initializer analysis; DataLayout.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Global initializer/uniform memory analysis is not modeled

<a id="is7754"></a>

## IS7754 — `simplifyLoadInst`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7745–7754](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7745-L7754). Kind: rewrite.
- **Rewrite:** Strip constant offsets through invariant.group while allowing inbounds relaxation; if stripped pointer is the constant global, sign-extend/truncate offset to that address space's index width and constant-fold load from the global initializer.
- **Matched/replaced opcodes:** `load`, `getelementptr`, `addrspacecast`.
- **Beyond opcode/constant/SSA matching:** Yes — constant offset stripping; invariant.group; DataLayout index width; constant global initializer.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Pointer offset/provenance and global constant memory analysis are not modeled

<a id="is7780"></a>

## IS7780 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7772–7780](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7772-L7780). Kind: schema.
- **Rewrite:** For any instruction whose NewOps are all constants and which has no explicit simplifier case, constant-fold the instruction operands; otherwise return null.
- **Matched/replaced opcodes:** `instruction`.
- **Beyond opcode/constant/SSA matching:** Yes — generic constant instruction folder; DataLayout; TargetLibraryInfo.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** LLVM generic ConstantFoldInstOperands is not modeled

<a id="is7784"></a>

## IS7784 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7782–7784](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7782-L7784). Kind: delegation.
- **Rewrite:** Dispatch FNeg instruction to simplifyFNegInst using instruction fast-math flags.
- **Matched/replaced opcodes:** `fneg`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction dispatch; fast-math flags.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple opcode dispatch to simplifyFNegInst; its concrete constant and double-negation cases are inventoried at IS5932/IS5937.

<a id="is7786"></a>

## IS7786 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7785–7786](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7785-L7786). Kind: delegation.
- **Rewrite:** Dispatch FAdd instruction to simplifyFAddInst with instruction fast-math flags.
- **Matched/replaced opcodes:** `fadd`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction dispatch; fast-math flags.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Simple opcode dispatch to simplifyFAddInst; its concrete cases are inventoried at IS6039-IS6091.

<a id="is7789"></a>

## IS7789 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7787–7789](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7787-L7789). Kind: delegation.
- **Rewrite:** Dispatch Add with nsw/nuw flags from instruction-info query to simplifyAddInst.
- **Matched/replaced opcodes:** `add`.
- **Beyond opcode/constant/SSA matching:** Yes — IIQ nsw/nuw flags; instruction dispatch.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS0597](#is0597), [IS0601](#is0601), [IS0605](#is0605), [IS0609](#is0609), [IS0613](#is0613), [IS0621](#is0621), [IS0626](#is0626), [IS0633](#is0633), [IS0637](#is0637), [IS0642](#is0642), [IS0647](#is0647). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyAddInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7793"></a>

## IS7793 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7791–7793](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7791-L7793). Kind: delegation.
- **Rewrite:** Dispatch FSub instruction to simplifyFSubInst with instruction fast-math flags.
- **Matched/replaced opcodes:** `fsub`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction dispatch; fast-math flags.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS6105](#is6105), [IS6108](#is6108), [IS6115](#is6115), [IS6121](#is6121), [IS6128](#is6128), [IS6136](#is6136), [IS6144](#is6144), [IS6148](#is6148), [IS6152](#is6152), [IS6160](#is6160). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyFSubInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7796"></a>

## IS7796 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7794–7796](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7794-L7796). Kind: delegation.
- **Rewrite:** Dispatch Sub with nsw/nuw flags from instruction-info query to simplifySubInst.
- **Matched/replaced opcodes:** `sub`.
- **Beyond opcode/constant/SSA matching:** Yes — IIQ nsw/nuw flags; instruction dispatch.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS0749](#is0749), [IS0754](#is0754), [IS0759](#is0759), [IS0763](#is0763), [IS0767](#is0767), [IS0773](#is0773), [IS0780](#is0780), [IS0783](#is0783), [IS0797](#is0797), [IS0805](#is0805), [IS0819](#is0819), [IS0827](#is0827), [IS0841](#is0841), [IS0854](#is0854), [IS0860](#is0860), [IS0867](#is0867), [IS0879](#is0879), [IS0886](#is0886). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifySubInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7800"></a>

## IS7800 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7798–7800](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7798-L7800). Kind: delegation.
- **Rewrite:** Dispatch FMul instruction to simplifyFMulInst with instruction fast-math flags.
- **Matched/replaced opcodes:** `fmul`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction dispatch; fast-math flags.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS6222](#is6222). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyFMulInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7803"></a>

## IS7803 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7801–7803](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7801-L7803). Kind: delegation.
- **Rewrite:** Dispatch Mul with nsw/nuw flags from instruction-info query to simplifyMulInst.
- **Matched/replaced opcodes:** `mul`.
- **Beyond opcode/constant/SSA matching:** Yes — IIQ nsw/nuw flags; instruction dispatch.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS0902](#is0902), [IS0906](#is0906), [IS0911](#is0911), [IS0915](#is0915), [IS0923](#is0923), [IS0929](#is0929), [IS0934](#is0934), [IS0940](#is0940), [IS0945](#is0945), [IS0952](#is0952), [IS0959](#is0959). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyMulInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7807"></a>

## IS7807 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7805–7807](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7805-L7807). Kind: delegation.
- **Rewrite:** Dispatch SDiv with exact flag from instruction-info query to simplifySDivInst.
- **Matched/replaced opcodes:** `sdiv`.
- **Beyond opcode/constant/SSA matching:** Yes — IIQ exact flag; instruction dispatch.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS1216](#is1216), [IS1218](#is1218). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifySDivInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7811"></a>

## IS7811 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7809–7811](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7809-L7811). Kind: delegation.
- **Rewrite:** Dispatch UDiv with exact flag from instruction-info query to simplifyUDivInst.
- **Matched/replaced opcodes:** `udiv`.
- **Beyond opcode/constant/SSA matching:** Yes — IIQ exact flag; instruction dispatch.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS1230](#is1230). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyUDivInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7815"></a>

## IS7815 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7813–7815](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7813-L7815). Kind: delegation.
- **Rewrite:** Dispatch FDiv instruction to simplifyFDivInst with instruction fast-math flags.
- **Matched/replaced opcodes:** `fdiv`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction dispatch; fast-math flags.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS6267](#is6267), [IS6270](#is6270), [IS6277](#is6277), [IS6283](#is6283), [IS6289](#is6289), [IS6294](#is6294), [IS6301](#is6301), [IS6305](#is6305). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyFDivInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7818"></a>

## IS7818 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7816–7818](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7816-L7818). Kind: delegation.
- **Rewrite:** Dispatch SRem instruction to simplifySRemInst.
- **Matched/replaced opcodes:** `srem`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction dispatch.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS1246](#is1246), [IS1250](#is1250), [IS1252](#is1252). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifySRemInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7820"></a>

## IS7820 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7819–7820](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7819-L7820). Kind: delegation.
- **Rewrite:** Dispatch URem instruction to simplifyURemInst.
- **Matched/replaced opcodes:** `urem`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction dispatch.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS1263](#is1263). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyURemInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7822"></a>

## IS7822 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7821–7822](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7821-L7822). Kind: delegation.
- **Rewrite:** Dispatch FRem instruction to simplifyFRemInst with instruction fast-math flags.
- **Matched/replaced opcodes:** `frem`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction dispatch; fast-math flags.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS6326](#is6326), [IS6329](#is6329), [IS6340](#is6340), [IS6343](#is6343). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyFRemInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7825"></a>

## IS7825 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7823–7825](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7823-L7825). Kind: delegation.
- **Rewrite:** Dispatch Shl with nsw/nuw flags from instruction-info query to simplifyShlInst.
- **Matched/replaced opcodes:** `shl`.
- **Beyond opcode/constant/SSA matching:** Yes — IIQ nsw/nuw flags; instruction dispatch.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS1405](#is1405), [IS1411](#is1411), [IS1417](#is1417), [IS1421](#is1421), [IS1430](#is1430). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyShlInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7829"></a>

## IS7829 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7827–7829](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7827-L7829). Kind: delegation.
- **Rewrite:** Dispatch LShr with exact flag from instruction-info query to simplifyLShrInst.
- **Matched/replaced opcodes:** `lshr`.
- **Beyond opcode/constant/SSA matching:** Yes — IIQ exact flag; instruction dispatch.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS1446](#is1446), [IS1451](#is1451), [IS1466](#is1466). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyLShrInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7833"></a>

## IS7833 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7831–7833](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7831-L7833). Kind: delegation.
- **Rewrite:** Dispatch AShr with exact flag from instruction-info query to simplifyAShrInst.
- **Matched/replaced opcodes:** `ashr`.
- **Beyond opcode/constant/SSA matching:** Yes — IIQ exact flag; instruction dispatch.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS1483](#is1483), [IS1490](#is1490), [IS1495](#is1495), [IS1500](#is1500). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyAShrInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7837"></a>

## IS7837 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7835–7837](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7835-L7837). Kind: delegation.
- **Rewrite:** Dispatch And instruction to simplifyAndInst.
- **Matched/replaced opcodes:** `and`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction dispatch.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS2074](#is2074), [IS2078](#is2078), [IS2082](#is2082), [IS2086](#is2086), [IS2090](#is2090), [IS2094](#is2094), [IS2097](#is2097), [IS2099](#is2099), [IS2102](#is2102), [IS2113](#is2113), [IS2119](#is2119), [IS2132](#is2132), [IS2136](#is2136), [IS2143](#is2143), [IS2145](#is2145), [IS2151](#is2151), [IS2156](#is2156), [IS2161](#is2161), [IS2167](#is2167), [IS2169](#is2169), [IS2176](#is2176), [IS2184](#is2184), [IS2213](#is2213), [IS2215](#is2215), [IS2226](#is2226), [IS2233](#is2233), [IS2239](#is2239), [IS2242](#is2242), [IS2247](#is2247), [IS2250](#is2250), [IS2255](#is2255). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyAndInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7839"></a>

## IS7839 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7838–7839](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7838-L7839). Kind: delegation.
- **Rewrite:** Dispatch Or instruction to simplifyOrInst.
- **Matched/replaced opcodes:** `or`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction dispatch.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS2359](#is2359), [IS2363](#is2363), [IS2369](#is2369), [IS2374](#is2374), [IS2377](#is2377), [IS2379](#is2379), [IS2382](#is2382), [IS2397](#is2397), [IS2406](#is2406), [IS2408](#is2408), [IS2419](#is2419), [IS2423](#is2423), [IS2430](#is2430), [IS2434](#is2434), [IS2438](#is2438), [IS2441](#is2441), [IS2444](#is2444), [IS2450](#is2450), [IS2452](#is2452), [IS2457](#is2457), [IS2462](#is2462), [IS2468](#is2468), [IS2470](#is2470), [IS2477](#is2477), [IS2495](#is2495), [IS2501](#is2501), [IS2510](#is2510), [IS2515](#is2515), [IS2522](#is2522), [IS2525](#is2525), [IS2531](#is2531), [IS2534](#is2534), [IS2539](#is2539). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyOrInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7841"></a>

## IS7841 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7840–7841](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7840-L7841). Kind: delegation.
- **Rewrite:** Dispatch Xor instruction to simplifyXorInst.
- **Matched/replaced opcodes:** `xor`.
- **Beyond opcode/constant/SSA matching:** Yes — instruction dispatch.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS2553](#is2553), [IS2557](#is2557), [IS2561](#is2561), [IS2565](#is2565), [IS2569](#is2569), [IS2573](#is2573), [IS2580](#is2580), [IS2589](#is2589), [IS2594](#is2594), [IS2596](#is2596), [IS2599](#is2599), [IS2604](#is2604), [IS2616](#is2616), [IS2623](#is2623). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyXorInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7843"></a>

## IS7843 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7842–7843](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7842-L7843). Kind: delegation.
- **Rewrite:** Dispatch ICmp using its predicate and two replacement operands to simplifyICmpInst.
- **Matched/replaced opcodes:** `icmp`.
- **Beyond opcode/constant/SSA matching:** Yes — comparison predicate; instruction dispatch.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS3891](#is3891), [IS3907](#is3907), [IS3913](#is3913), [IS3918](#is3918), [IS3959](#is3959), [IS3966](#is3966), [IS3979](#is3979), [IS3985](#is3985), [IS3987](#is3987), [IS4014](#is4014), [IS4026](#is4026), [IS4031](#is4031), [IS4037](#is4037), [IS4042](#is4042), [IS4058](#is4058), [IS4064](#is4064), [IS4066](#is4066), [IS4091](#is4091), [IS4100](#is4100), [IS4102](#is4102), [IS4108](#is4108), [IS4113](#is4113), [IS4126](#is4126), [IS4135](#is4135), [IS4148](#is4148), [IS4180](#is4180), [IS4186](#is4186), [IS4192](#is4192). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyICmpInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7846"></a>

## IS7846 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7844–7846](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7844-L7846). Kind: delegation.
- **Rewrite:** Dispatch FCmp using its predicate, instruction fast-math flags, and replacement operands to simplifyFCmpInst.
- **Matched/replaced opcodes:** `fcmp`.
- **Beyond opcode/constant/SSA matching:** Yes — comparison predicate; fast-math flags; instruction dispatch.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS4214](#is4214), [IS4225](#is4225), [IS4227](#is4227), [IS4232](#is4232), [IS4239](#is4239), [IS4245](#is4245), [IS4247](#is4247), [IS4260](#is4260), [IS4263](#is4263), [IS4268](#is4268), [IS4290](#is4290), [IS4292](#is4292), [IS4301](#is4301), [IS4319](#is4319), [IS4329](#is4329), [IS4349](#is4349), [IS4354](#is4354), [IS4363](#is4363), [IS4372](#is4372), [IS4396](#is4396), [IS4407](#is4407), [IS4419](#is4419), [IS4425](#is4425). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyFCmpInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7852"></a>

## IS7852 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7848–7852](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7848-L7852). Kind: delegation.
- **Rewrite:** Dispatch Select with condition, true/false replacement values, and fast-math flags (when select is FP math operator) to simplifySelectInst.
- **Matched/replaced opcodes:** `select`.
- **Beyond opcode/constant/SSA matching:** Yes — conditional selection; FMF only when FPMathOperator.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS5122](#is5122), [IS5126](#is5126), [IS5130](#is5130), [IS5137](#is5137), [IS5139](#is5139), [IS5150](#is5150), [IS5154](#is5154), [IS5158](#is5158), [IS5163](#is5163), [IS5169](#is5169), [IS5172](#is5172), [IS5176](#is5176), [IS5179](#is5179), [IS5185](#is5185), [IS5188](#is5188), [IS5195](#is5195), [IS5198](#is5198), [IS5202](#is5202), [IS5205](#is5205), [IS5211](#is5211), [IS5216](#is5216), [IS5219](#is5219), [IS5224](#is5224), [IS5227](#is5227), [IS5237a](#is5237a), [IS5237b](#is5237b), [IS5242a](#is5242a), [IS5242b](#is5242b), [IS5278](#is5278), [IS5281](#is5281), [IS5285](#is5285), [IS5289](#is5289), [IS5294](#is5294), [IS5296](#is5296). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifySelectInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7857"></a>

## IS7857 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7854–7857](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7854-L7857). Kind: delegation.
- **Rewrite:** Dispatch GetElementPtr using original source element type and no-wrap flags with replacement pointer/index operands to simplifyGEPInst.
- **Matched/replaced opcodes:** `getelementptr`.
- **Beyond opcode/constant/SSA matching:** Yes — source element type; GEP no-wrap flags.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS5317](#is5317), [IS5335](#is5335), [IS5340](#is5340), [IS5344](#is5344), [IS5359](#is5359), [IS5375](#is5375), [IS5383](#is5383), [IS5391](#is5391), [IS5414](#is5414), [IS5421](#is5421), [IS5435](#is5435), [IS5438](#is5438). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyGEPInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7863"></a>

## IS7863 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7859–7863](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7859-L7863). Kind: delegation.
- **Rewrite:** Dispatch InsertValue with original index path and replacement aggregate/value operands.
- **Matched/replaced opcodes:** `insertvalue`.
- **Beyond opcode/constant/SSA matching:** Yes — aggregate index path.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS5453](#is5453), [IS5459](#is5459), [IS5470](#is5470), [IS5474](#is5474). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyInsertValueInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7867"></a>

## IS7867 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7865–7867](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7865-L7867). Kind: delegation.
- **Rewrite:** Dispatch InsertElement with replacement vector/value/index operands.
- **Matched/replaced opcodes:** `insertelement`.
- **Beyond opcode/constant/SSA matching:** Yes — lane index.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS5493](#is5493), [IS5499](#is5499), [IS5504](#is5504), [IS5510](#is5510), [IS5514](#is5514), [IS5520](#is5520). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyInsertElementInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7870"></a>

## IS7870 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7868–7870](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7868-L7870). Kind: delegation.
- **Rewrite:** Dispatch ExtractValue with original aggregate index path and replacement aggregate operand.
- **Matched/replaced opcodes:** `extractvalue`.
- **Beyond opcode/constant/SSA matching:** Yes — aggregate index path.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS5530](#is5530), [IS5547](#is5547), [IS5560](#is5560), [IS5562](#is5562). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyExtractValueInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7874"></a>

## IS7874 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7872–7874](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7872-L7874). Kind: delegation.
- **Rewrite:** Dispatch ExtractElement with replacement vector and index operands.
- **Matched/replaced opcodes:** `extractelement`.
- **Beyond opcode/constant/SSA matching:** Yes — lane index.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS5580](#is5580), [IS5583](#is5583), [IS5589](#is5589), [IS5597](#is5597), [IS5601](#is5601), [IS5603](#is5603), [IS5611](#is5611), [IS5615](#is5615). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyExtractElementInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7877"></a>

## IS7877 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7875–7877](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7875-L7877). Kind: delegation.
- **Rewrite:** Dispatch ShuffleVector with original mask, result type, and replacement source vectors.
- **Matched/replaced opcodes:** `shufflevector`.
- **Beyond opcode/constant/SSA matching:** Yes — mask; result type.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS5803](#is5803), [IS5840](#is5840), [IS5873](#is5873), [IS5882](#is5882), [IS5910](#is5910). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyShuffleVectorInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7882"></a>

## IS7882 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7881–7882](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7881-L7882). Kind: delegation.
- **Rewrite:** Dispatch PHI using replacement incoming values and original PHI node for dominance checks.
- **Matched/replaced opcodes:** `phi`.
- **Beyond opcode/constant/SSA matching:** Yes — incoming value list; dominance analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS5658](#is5658), [IS5672](#is5672), [IS5675](#is5675). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyPHINode`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7884"></a>

## IS7884 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7883–7884](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7883-L7884). Kind: delegation.
- **Rewrite:** Dispatch Call with the replacement callee and replacement arguments after excluding operand bundle operands.
- **Matched/replaced opcodes:** `call`.
- **Beyond opcode/constant/SSA matching:** Yes — operand bundle slicing; call/intrinsic simplifier.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS7689](#is7689), [IS7692](#is7692), [IS7697](#is7697). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyCall`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7888"></a>

## IS7888 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7887–7888](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7887-L7888). Kind: delegation.
- **Rewrite:** Dispatch Freeze to simplifyFreezeInst on the replacement operand.
- **Matched/replaced opcodes:** `freeze`.
- **Beyond opcode/constant/SSA matching:** Yes — undef/poison guarantee analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS7716](#is7716). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyFreezeInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7893"></a>

## IS7893 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7890–7893](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7890-L7893). Kind: delegation.
- **Rewrite:** Dispatch AddrSpaceCast with replacement operand, original result type, and nonnull property only when instruction info is enabled.
- **Matched/replaced opcodes:** `addrspacecast`.
- **Beyond opcode/constant/SSA matching:** Yes — IIQ UseInstrInfo; nonnull property; function context.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS5740](#is5740). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyAddrSpaceCastInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7899"></a>

## IS7899 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7896–7899](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7896-L7899). Kind: delegation.
- **Rewrite:** Dispatch every remaining cast opcode using replacement source operand and original destination type.
- **Matched/replaced opcodes:** `trunc`, `zext`, `sext`, `fptrunc`, `fpext`, `fptoui`, `fptosi`, `uitofp`, `sitofp`, `ptrtoint`, `inttoptr`, `bitcast`, `ptrtoaddr`.
- **Beyond opcode/constant/SSA matching:** Yes — Instruction.def cast dispatch; AddrSpaceCast handled separately.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS5681](#is5681), [IS5693](#is5693), [IS5700](#is5700), [IS5713](#is5713), [IS5722](#is5722). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyCastInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7905"></a>

## IS7905 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7904–7905](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7904-L7905). Kind: delegation.
- **Rewrite:** Dispatch Load using the original load instruction attributes and replacement pointer operand.
- **Matched/replaced opcodes:** `load`.
- **Beyond opcode/constant/SSA matching:** Yes — load alignment/volatile/atomic attributes; constant global analysis.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS7731](#is7731), [IS7743](#is7743). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyLoadInst`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7914"></a>

## IS7914 — `simplifyInstructionWithOperands`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7911–7914](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7911-L7914). Kind: delegation.
- **Rewrite:** Public wrapper invokes internal instruction simplification with recursion limit after asserting replacement operand count matches instruction operand count.
- **Matched/replaced opcodes:** `instruction`.
- **Beyond opcode/constant/SSA matching:** Yes — recursion limit; operand arity assertion.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Shared implementation:** [IS7780](#is7780), [IS7784](#is7784), [IS7786](#is7786), [IS7789](#is7789), [IS7793](#is7793), [IS7796](#is7796), [IS7800](#is7800), [IS7803](#is7803), [IS7807](#is7807), [IS7811](#is7811), [IS7815](#is7815), [IS7818](#is7818), [IS7820](#is7820), [IS7822](#is7822), [IS7825](#is7825), [IS7829](#is7829), [IS7833](#is7833), [IS7837](#is7837), [IS7839](#is7839), [IS7841](#is7841), [IS7843](#is7843), [IS7846](#is7846), [IS7852](#is7852), [IS7857](#is7857), [IS7863](#is7863), [IS7867](#is7867), [IS7870](#is7870), [IS7874](#is7874), [IS7877](#is7877), [IS7882](#is7882), [IS7884](#is7884), [IS7888](#is7888), [IS7893](#is7893), [IS7899](#is7899), [IS7905](#is7905). This caller is not an additional independent port.
- **Details / missing facilities:** This is dispatch to `simplifyInstructionWithOperands`, not an additional peephole equation. Its source branches and their individual port/proof outcomes are linked here. A complete replacement for this dispatcher would need all callee facilities, including the unsupported domains and analysis-dependent or recursive branches documented there; there is no separate complete Puddle dispatcher implementation.

<a id="is7924"></a>

## IS7924 — `simplifyInstruction`

- **Original code:** [llvm/lib/Analysis/InstructionSimplify.cpp:7917–7924](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Analysis/InstructionSimplify.cpp#L7917-L7924). Kind: schema.
- **Rewrite:** Call simplifyInstructionWithOperands on the instruction's current operands; if unreachable-code simplification returns the instruction itself, return poison of its type.
- **Matched/replaced opcodes:** `instruction`.
- **Beyond opcode/constant/SSA matching:** Yes — unreachable-code self-result guard; result type.
- **Result:** No complete standalone Puddle port — see the reason below.
- **Port/proof domain:** Pinned LLVM source rule; scalar modeled domain where stated.
- **Details / missing facilities:** Outer wrapper substitutes poison if a simplifier returns the input instruction itself in unreachable IR. This is a self-result handling policy requiring reachability/context, not a standalone local scalar algebraic rule; scalar poison itself is modeled.

## Pass-driver dead-instruction deletion

- **Original code:** [InstSimplifyPass.cpp:48–66](https://github.com/llvm/llvm-project/blob/fb3ef86994775a17f4e9f1576d17590e79a8e198/llvm/lib/Transforms/Scalar/InstSimplifyPass.cpp#L48-L66). Kind: pass action / delegation.
- **Rewrite:** Delete an instruction, and recursively its newly dead operands, when `isInstructionTriviallyDead` permits deletion. This also cleans up instructions after their uses are replaced by a simplification result.
- **Matched/replaced opcodes:** Any opcode accepted by LLVM's dead-instruction predicate; deletion has no replacement opcode.
- **Beyond opcode/constant/SSA matching:** Yes — use counts, side effects, memory/volatile behavior, target-library call information, and the pass worklist; unreachable blocks are skipped using the dominator tree.
- **Result:** Cannot implement the full deletion action as a local Puddle result-replacement rule with the present validity contract. It requires a contextual unused-result and effect-safety certificate plus an instruction-erasure correctness theorem.
- **Accounting:** Documented separately from the 800 library source entries and excluded from the peephole implementation/proof totals.
