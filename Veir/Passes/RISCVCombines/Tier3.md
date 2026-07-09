# Task: Tier 3 GlobalISel combines in Veir

Implement the rules below in the RISC-V `Combine.impl` file, in the EXACT style of the existing defs (e.g. `lshr_of_trunc_of_lshr`, `narrow_binop_add`, `sub_to_add`, `SubSmaxSub`, `funnel_shift_right_zero` — all already in the file). These are pure structural integer rewrites.

## Ground rules (unchanged from prior batches — re-read)

1. **Only use matchers that exist in `Matching.lean`.** Confirmed available and used below: `matchAdd matchSub matchMul matchAnd matchOr matchXor matchShl matchLshr matchAshr matchIcmp matchSelect matchSext matchZext matchTrunc matchNot matchConstantIntVal matchConstantZero getDefiningOp matchSmax matchSmin matchUmax matchUmin matchUdiv matchSdiv matchUrem matchSrem matchFshl matchFshr matchBitreverse matchCtlz`. Signatures you'll rely on: `matchBitreverse op ctx : Option ValuePtr` (returns the single source); `matchFshl`/`matchFshr op ctx : Option (ValuePtr × ValuePtr × ValuePtr)` = `(op0, op1, amt)`; `matchUdiv`/`matchUrem`/`matchSdiv op ctx : Option (ValuePtr × ValuePtr × props)`.
2. **Do NOT invent matchers, target ops, or helpers beyond the one `isConstantPowerOfTwo` specified below.** If a rule needs something not present, SKIP it and say so.
3. Style: `set_option warn.sorry false in`, doc comment, `sorry` for proof obligations, thread props per the cloned def, register each new def in the `patterns` array of `Combine.impl` (append before the trailing `,`). Constant build idiom: `let .integerType TY := (v.getType! rewriter.ctx.raw).val | return rewriter` then `LLVMConstantProperties.mk (.integer (IntegerAttr.mk VALUE TY))`. `IntegerAttr` exposes `.value : Int`.
4. **Bitwidth**: two rules below need the integer bit-width as a value (for `C % bw` and `2^k − 1`). Before writing them, GREP for how bit-width is obtained from an `.integerType` / `IntegerType` in this codebase (look in `Matching.lean`, the type definitions, and existing RISC-V defs that mention `width`, `getScalarSizeInBits`, `.width`, or similar). Use whatever accessor exists. If you cannot find a way to get the width as a `Nat`/`Int`, SKIP the two rules that need it (`funnel_shift_overshift`, and the mask form of `urem_pow2_to_mask`) and note it — do NOT hardcode 32 or 64.
5. Add tests for each rewrite under Test/Passes/RISCVCombines.
6. Do not make unnecessary builds. For example you don't need to build after every single rewrite. Group it so you don't make unnecessary build that will make us lose time.

---

## CLUSTER 1 — bitreverse pair (do first; clone `lshr_of_trunc_of_lshr`'s 3-level match shape)

### `bitreverse_shl`  (#26)
`bitreverse(shl(bitreverse x), y) → lshr x, y`.
- `matchBitreverse op` → `rev` (outer). `getDefiningOp rev`; `matchShl` → `(inner, y, shp)`. `getDefiningOp inner`; `matchBitreverse` → `x`.
- Build `.lshr #[x, y]` threading `shp`; `replaceOp!`.
- **DROP** the LLVM `isLegalOrBeforeLegalizer` guard entirely.

### `bitreverse_lshr`  (#27)
Mirror: `bitreverse(lshr(bitreverse x), y) → shl x, y`. Clone `bitreverse_shl`, swap `matchShl`↔`matchLshr` and the built op `.lshr`↔`.shl`.

---

## CLUSTER 2 — power-of-two cluster (write ONE helper, then 3 rules)

### Helper: `isConstantPowerOfTwo`
Add a small helper (near the top of `Combine.impl`, non-`public`) with this contract:
- Input: a `ValuePtr` and `rewriter.ctx`.
- `matchConstantIntVal` it; let `v := attr.value : Int`.
- Return `some k` (the base-2 log as a `Nat`) iff `v > 0 ∧ (v &&& (v - 1) = 0)`; else `none`.
- Compute `k` however is cleanest in this codebase (grep for an existing `log2`/`Nat.log2`/bit-scan; if none, a simple recursive count is fine). Keep it total.

### `udiv_by_pow2`  (#143)   — TRIVIAL, do
`udiv x, 2^k → lshr x, k`.
- `matchUdiv op` → `(x, yv, _)`. `isConstantPowerOfTwo yv` → `k`.
- Build a constant of value `(k : Int)` at `x`'s type; build `.lshr #[x, kConst]`; `replaceOp!`.

### `mul_to_shl`  (#21)   — TRIVIAL, do
`mul x, 2^k → shl x, k`.
- `matchMul op` → `(x, yv, mp)`. `isConstantPowerOfTwo yv` → `k`. (If the constant is the LHS instead, rely on the existing `commute_const_mul` to canonicalize first — only match RHS-constant here.)
- Build const `k` at `x`'s type; build `.shl #[x, kConst]` threading `mp`; `replaceOp!`.

### `urem_pow2_to_mask`  (#61)   — needs bitwidth for the mask (see rule 4)
`urem x, 2^k → and x, (2^k − 1)`.
- `matchUrem op` → `(x, yv, _)`. `isConstantPowerOfTwo yv` → `k`.
- Mask value is `2^k − 1` (an `Int`). Build const mask at `x`'s type; build `.and #[x, maskConst]`; `replaceOp!`.
- NOTE: the mask is `2^k − 1`, computable directly from `k` — you do NOT actually need the type's bit-width for this one (I was over-cautious). Just compute `(2^k - 1 : Int)`. Do it.

### `sdiv_by_pow2`  (#142)   — SKIP (leave for later)
Signed pow2 division needs a round-toward-zero correction sequence, not a plain shift. Do NOT attempt in this batch.

---

## CLUSTER 3 — funnel patterns (matchFshl/matchFshr exist)

### `funnel_shift_overshift`  (#122)   — needs bitwidth (see rule 4)
`fshl x, y, C → fshl x, y, (C % bw)` and same for `fshr`, when `C ≥ bw`. Split into two defs `funnel_shift_overshift_l` (fshl) and `_r` (fshr).
- `matchFshl op` → `(x, y, amt)`. `matchConstantIntVal amt` → `c`. Get `bw` (rule 4). If `c.value < bw` return unchanged (only fire when overshifting). Build const `(c.value % bw)`; rebuild `.intr__fshl #[x, y, newAmt]`; `replaceOp!`.
- If bitwidth can't be obtained, SKIP both and note it.

### `funnel_shift_or_shift_to_funnel_shift_left`  (#123)   — structural, do
`(fshl x, z, y) | (shl x, y) → fshl x, z, y`. G_OR is commutative, so handle both operand orders (two defs, or one def that checks both).
- `matchOr op` → `(o0, o1, _)`. One operand must be an fshl, the other a shl.
- `getDefiningOp` the fshl operand; `matchFshl` → `(fx, fz, fy)`. `getDefiningOp` the shl operand; `matchShl` → `(sx, sy, _)`.
- Require `fx = sx` and `fy = sy`. Then `replaceValue` the OR result with the fshl operand value; `eraseOp`. (No new op needed — the fshl already exists.)

### `funnel_shift_or_shift_to_funnel_shift_right`  (#124)   — structural, do
Mirror: `(fshr z, x, y) | (lshr x, y) → fshr z, x, y`. Clone #123 with `matchFshr` and `matchLshr`. Watch operand positions: for fshr the data operands are `(z, x)`, and the lshr is on `x` — match accordingly (`matchFshr` → `(fz, fx, fy)`, `matchLshr` on the other operand → `(sx, sy, _)`, require `fx = sx`, `fy = sy`).

### `funnel_shift_to_rotate`, `funnel_shift_from_or_shift`, `funnel_shift_from_or_shift_constants_are_legal`  — SKIP
`to_rotate` needs a rotate target op that has no matcher/builder here. The `from_or_shift` pair needs shift-amount-complement reasoning (`C1 + C2 = bw`) that's error-prone under deadline. Do NOT attempt.

---

## STRETCH (only if all clusters above land) — `constant_fold_binop`  (#149)
Fold `binop(C1, C2) → C` for two constant operands. `matchConstantIntVal` BOTH operands; if both constants, compute the result as an `Int` per opcode and build one constant, `replaceOp!`.
- Dispatch on `op.getOpType!`. Cover: `.add .sub .mul .and .or .xor .shl .lshr .ashr .udiv .sdiv .urem .srem .intr__smin .intr__smax .intr__umin .intr__umax`.
- **Guard div/rem by zero**: if the second constant is 0 for `udiv/sdiv/urem/srem`, return unchanged (do not fold).
- Signedness/width: match the semantics the existing lowering uses. If the correct wrapping/width semantics for a given opcode is unclear, OMIT just that opcode rather than guess. Getting add/sub/mul/and/or/xor/shl right is already high-value.

---

## Deliverable
Each new def, registered in `patterns`. At the end print: (a) which rules you implemented, (b) which you SKIPPED and the reason (bitwidth-unavailable / no target op / deadline-scope), (c) whether `isConstantPowerOfTwo` needed a fresh `log2` or reused an existing one.