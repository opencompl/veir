# Task: Implement additional GlobalISel combines in Veir

Implement the LLVM GlobalISel combine rules listed below in the Veir framework, following the EXACT style already used in the existing file (the RISC-V `Combine.impl` file containing `right_identity_zero_add`, `narrow_binop_add`, `trunc_of_zext`, `sub_minus_one`, etc.). These are all pure structural integer rewrites — no known-bits analysis, no legality queries, no FP/vector/memory.

## Ground rules (read first)

1. **Do NOT invent matchers or API.** Only use primitives already witnessed in the existing Veir files: `matchAdd`, `matchSub`, `matchMul`, `matchAnd`, `matchOr`, `matchXor`, `matchShl`, `matchAshr`, `matchLshr`, `matchSelect`, `matchIcmp`, `matchSext`, `matchZext`, `matchTrunc`, `matchNot`, `matchConstantIntVal`, `matchConstantZero`, `matchSmax`, `matchUmax`, `matchOp`, `getDefiningOp`; constructors `createOp!`, `replaceValue`+`eraseOp`, `replaceOp!`; constant building via `LLVMConstantProperties.mk (.integer (IntegerAttr.mk V TY))`; `.integerType TY := (v.getType! ctx.raw).val`; `NswNuwProperties.mk false false`; `IcmpProperties.mk`.
2. **Before implementing any rule marked [GREP-FIRST], grep the codebase** for the matcher it needs. If the matcher does not exist, SKIP that rule and note it — do not fabricate the matcher.
3. Use `set_option warn.sorry false in` and `sorry` for proof obligations, exactly like the existing defs.
4. Follow the property-threading convention: `()` for and/xor/trunc, the matched props var for or/mul/sub/add, etc. — copy from the def you're cloning.
5. After writing each def, **add it to the `patterns` array in `Combine.impl`** (append near the end, before the trailing `,`).
6. Add a `set_option warn.sorry false in` + doc comment header for each, matching existing style.
7. Add tests for each rewrite under Test/Passes/RISCVCombines.
8. Do not make unnecessary builds. For example you don't need to build after every single rewrite. Group it so you don't make unnecessary build that will make us lose time.
9. sometimes trunc->sext sext->sext kind of rewrites might be weird since you might not know what bitwidth you should be truncating or sexting to, for those cases implement it for only 1 case, pick a very simple case.
---

## TIER 1 — implement all of these (each is a near-clone of an existing def)

### 1. `truncate_of_sext`  (LLVM rule #249)
- Clone `trunc_of_zext` (the existing `def trunc_of_zext`). Change `matchZext`→`matchSext`.
- `trunc (sext x)` where trunc result type == x's type → `x`. Keep the same type-equality guard and `replaceValue`+`eraseOp` tail.

### 2. `zext_of_zext`  (LLVM rule #254)
- `zext (zext x) → zext x`. Structural:
  - `matchZext op` to get outer `(v0, _zp)`; `getDefiningOp v0`; `matchZext` inner to get `(x, _)`.
  - Build a new `.zext` from `x` to the OUTER op's result type; `replaceOp!` (or `replaceValue`+`eraseOp`).
- Reuse the outer zext's result type via `(op.getResult 0 : ValuePtr).getType! rewriter.ctx.raw`.

### 3. `sext_of_sext`  (LLVM rule #256)
- Clone `zext_of_zext` with `matchSext` and `.sext`.
- `sext (sext x) → sext x`.

### 4. `sub_to_add`  (LLVM rule #22)
- `(sub x, C) → (add x, -C)` where C is a constant.
- `matchSub op` → `(x, cval, _sp)`; `matchConstantIntVal cval` → `c`; extract integer type of `x`; build a constant with value `-c.value`; build `.add #[x, negConst]`; `replaceOp!`.
- Model the constant-building on `sub_minus_one` / `mul_by_neg_one`.

### 5. `sub_of_mul_const`  (LLVM rule #23)
- `(sub a, (mul x, C)) → (add a, (mul x, -C))`, C constant.
- `matchSub op` → `(a, mulV, _sp)`; `getDefiningOp mulV`; `matchMul` → `(x, cval, mp)`; `matchConstantIntVal cval` → `c`; build negated constant `-c.value`; build new `.mul #[x, negC]`; build `.add #[a, newMul]`; `replaceOp!`.
- NOTE: LLVM has a one-use guard on the mul; OMIT it (the existing reassoc defs omit one-use guards — stay consistent).

### 6. `select_not`  (LLVM rule #47)
- `select (not c), x, y → select c, y, x`.
- `matchSelect op` → `(cond, tv, fv)`; `getDefiningOp cond`; match the not-pattern on that defining op. The "not" is `xor c, -1`: use `matchXor` on the defining op → `(c, m1v, _)`, `matchConstantIntVal m1v` must be `-1`.
- Build new `.select #[c, fv, tv]` (arms swapped); `replaceOp!`.
- **IMPORTANT:** do NOT copy the `matchNot (op.getResult 0)` form used elsewhere — that matches a not wrapping the ROOT. Here the not wraps the select's CONDITION operand, so it's `getDefiningOp cond` then `matchXor`.

### 7. `commute_int_constant_to_rhs`  (LLVM rule #48)
- `(C op x) → (x op C)` — move a constant left-operand to the right.
- Implement as SEPARATE defs per opcode (mirror how `not_cmp_fold` / `select_to_iminmax` are split): `commute_const_add`, `commute_const_mul`, `commute_const_and`, `commute_const_or`, `commute_const_xor`.
- Each: match the binop → `(lhs, rhs, props)`; `matchConstantIntVal lhs` must succeed AND `matchConstantIntVal rhs` must FAIL (only fire when exactly the left is constant, to avoid infinite commuting); rebuild same-opcode op with operands swapped `#[rhs, lhs]`, threading `props`; `replaceOp!`.
- Register all 5 in the patterns array.

---

## Deliverable
For each implemented rule: the new `def`, registered in the `Combine.impl` patterns array. At the end, print a short list: which rules you implemented, and which [GREP-FIRST] ones you SKIPPED because the matcher was missing.