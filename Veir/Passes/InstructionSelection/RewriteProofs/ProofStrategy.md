# Proving `PreservesSemantics` for RISC-V lowerings

This document describes the proof strategy used for the `lowerUnaryWLocal` lowerings
(`ctlz_local`, `cttz_local`, `ctpop_local` in `Veir/Passes/InstructionSelection/RISCV64.lean`)
the `lowerBinaryWLocal` lowerings (`add_local`, `sub_local`, `mul_local`, `xor_local`, …), and
the `lowerBinopNotLocal` lowerings (`andn_local`, `orn_local`, `xnor_local` in
`Veir/Passes/InstructionSelection/RISCV64Sdag.lean`), and how to extend it to the other
`*_local` lowerings (`bswap_local`, `selectBinopImmLocal`, …).

## What we prove

For each lowering `foo_local : LocalRewritePattern OpCode` we prove

```lean
theorem foo_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics foo_local h h₂ h₃ h₄
```

`PreservesSemantics` (`Veir/PatternRewriter/Semantics.lean`) is a one-step forward simulation:

- **Given**: the pattern fired (`hpattern : foo_local ctx op = some (newCtx, some (newOps, newValues))`),
  the matched `op` interpreted successfully in a source state (`interpretOp op state = some (newState, cf)`),
  and a target state `state'` on `newCtx` that refines `state` at `InsertPoint.before op`
  (plus `Dom`/`Verified`/`DefinesDominating` side conditions).
- **Show**: `interpretOpList newOps.toList state'` succeeds with the *same* control flow `cf`,
  the *same* memory, and the values in `newValues` refine the matched op's result values
  (`sourceValues ⊒ targetValues`).

## Architecture: one proof per lowering *shape*, not per lowering

Lowerings sharing a shape are written as instances of a combinator in `RISCV64.lean`, and the
structural proof is done **once per combinator**. Currently:

- `lowerUnaryWLocal match? op64 op32 props64 props32` — match a single-operand LLVM integer op
  on `i64`/`i32`, then emit `castToRegLocal` → `op64` (or its `W` variant `op32` for `i32`) →
  `replaceWithRegLocal`. Its shared correctness proof is
  `lowerUnaryWLocal_preservesSemantics` (`RewriteProofs/LowerUnaryW.lean`).
- `lowerBinaryWLocal match? op64 op32 props64 props32` — the two-operand analogue: match a
  binary LLVM integer op on `i64`/`i32`, emit `castToRegLocal` for each operand → `op64`/`op32`
  applied to the two cast results (in `#[lhs, rhs]` order) → `replaceWithRegLocal`. Instances:
  `add`, `sub`, `mul`, `sdiv`, `udiv`, `srem`, `urem`, `xor`, `shl`, `lshr` (ops without a `W`
  variant, like `xor`, pass the same opcode twice). Its shared correctness proof is
  `lowerBinaryWLocal_preservesSemantics` (`RewriteProofs/LowerBinaryW.lean`), instantiated so
  far for `add`, `sub`, `mul`, `xor`. The div/rem instances cannot use the current proof: their
  LLVM interpretation has UB branches (division by zero, `intMin / -1`), so they do not satisfy
  the total-success `hSemSrc` hypothesis and need a combinator proof variant that propagates UB.
- `lowerBinaryRegLocal match? rop props` — the width-agnostic cousin of `lowerBinaryWLocal`: match
  a binary LLVM integer op whose *result* type is `i64`/`i32`, emit `castToRegLocal` for each
  operand → a *single* `riscv` op `rop` (the same instruction at both bitwidths — no `W` variant,
  because the register already holds the correctly-represented value) → `replaceWithRegLocal`.
  Instances: `umax` (`maxu`), `umin` (`minu`). Its shared correctness proof is
  `lowerBinaryRegLocal_preservesSemantics` (`RewriteProofs/LowerBinaryReg.lean`). Because the
  emitted op is bitwidth-independent, the structural part of the proof is done *once* (no bitwidth
  branch); the two widths diverge only at the final value-refinement step, where the matching
  `hRefine64`/`hRefine32` lemma is chosen. The matcher returns just `(lhs, rhs)` (no properties),
  so `hMatchImplies` omits the properties equation. The signed `smax`/`smin` do *not* fit this
  combinator: for `i32` they sign-extend both operands (`riscv.sextw`) before `max`/`min`, so they
  need the longer-chain `lowerSignedMinMaxLocal` (two extra unary reg ops in the `i32` branch).
- `lowerBitwiseRegLocal match? rop props` — the *bitwise* cousin of `lowerBinaryRegLocal`: match a
  two-operand LLVM bitwise op whose *result* type is `i64`/`i32`/`i8`/`i1`, emit `castToRegLocal`
  for each operand → a *single* bitwise `riscv` op `rop` → `replaceWithRegLocal`. Instances: `and`
  (`riscv.and`), `or` (`riscv.or`). Its shared correctness proof is
  `lowerBitwiseRegLocal_preservesSemantics` (`RewriteProofs/LowerBitwiseReg.lean`). Unlike the other
  combinators, `rop` is correct at *every* legal width with no per-width variant, because a bitwise
  op is bit-parallel: `zeroExtend`ing the operands to 64 bits, `and`/`or`ing, and truncating back to
  `bw` bits gives the `bw`-bit result for *any* `bw ≤ 64`. So the value refinement is discharged by
  a *single width-generic* lemma (`hRefine` takes the disjunction `bw ∈ {64,32,8,1}` and closes each
  width with `bv_decide`) — there is no bitwidth branch anywhere in the proof. The matcher returns
  `(lhs, rhs, props)`; `or`'s `disjoint` flag flows into `srcFn` via `hProps := rfl` (as usual).
  `xor` is bitwise too and would fit here, but currently lowers via `lowerBinaryWLocal` (same opcode
  at both widths). Arithmetic ops (`add`/`sub`/`mul`/shifts) do *not* fit: a carry or shifted bit
  crosses the width boundary, so the `i32` result is not a function of the low 32 bits and a
  sign-extending `W` variant is required.
- `lowerSignedMinMaxLocal match? rop props` — the *signed* min/max cousin of `lowerBinaryRegLocal`:
  match a two-operand LLVM integer op whose result has type `i64`/`i32`, emit `castToRegLocal` for
  each operand → a single signed `riscv` op `rop` (`max`/`min`) → `replaceWithRegLocal`. Instances:
  `smax` (`riscv.max`), `smin` (`riscv.min`). Its shared correctness proof is
  `lowerSignedMinMaxLocal_preservesSemantics` (`RewriteProofs/LowerSignedMinMax.lean`). The catch is
  the `i32` branch: `castToRegLocal` puts the operand into the register *zero-extended*
  (`LLVM.Int.toReg` computes `getValue.zeroExtend 64`), which preserves the *unsigned* order (so the
  unsigned `umax`/`umin` need no fixup and use `lowerBinaryRegLocal`) but breaks the *signed* order,
  so the two register operands are first sign-extended with `riscv.sextw` before the signed compare.
  So unlike `lowerBinaryRegLocal`, the two bitwidths take *different* op chains — four ops for `i64`,
  six for `i32` (two extra `sextw`s) — and the proof `split`s on the bitwidth *after* the two shared
  casts, executing each chain separately (the `i64` branch mirrors `lowerBinaryRegLocal`, the `i32`
  branch threads two extra `interpretOp_riscv_unaryReg_forward` steps and their frame clauses). The
  data lemmas come in `_64`/`_32` pairs, the `_32` one carrying the extra `sextw` (unfold
  `Data.RISCV.max`/`min`, `sextw`, `addiw`, then `veir_bv_decide`).
- `lowerRotateLocal match? op64 op32 props64 props32` — the *rotate* cousin of `lowerBinaryWLocal`:
  match a funnel-shift LLVM op returning `(a, b, amt)`, require `a = b` (so the funnel shift is a
  rotate) and the *result* type to be `i64`/`i32`, emit `castToRegLocal` for the value `a` and the
  amount `amt` → `op64` (or its `W` variant `op32` for `i32`) → `replaceWithRegLocal`. Instances:
  `fshl` (`rol`/`rolw`), `fshr` (`ror`/`rorw`). Its shared correctness proof is
  `lowerRotateLocal_preservesSemantics` (`RewriteProofs/LowerRotate.lean`). The emitted 4-op chain and
  the `W`-variant bitwidth branch are identical to `lowerBinaryWLocal`; the two differences are that
  the source op is *ternary* (three operands — a new `matchTernaryOp_interpretOp_unfold`, the ternary
  analogue of the binary one, and a new `IsVerifiedIntegerTernop` verifier bundle behind
  `Verified.llvm_intr__fshl`/`fshr`) and the type guard reads the *result* type (as in
  `lowerBinaryRegLocal`). The matched `a = b` is derived in a side proof (`rcases Decidable.em`;
  `by_contra` is unavailable) so `hpattern` and its dependents (`state'Wf`) are not reverted; the
  middle operand `b`'s value collapses into `a`'s via `a = b ⇒ xa = xb`, so the data lemmas are stated
  on `srcFn x x c` (the `_64`/`_32` refinement lemmas unfold `Data.RISCV.rol`/`rolw`/…, then
  `veir_bv_decide` — the `getValue_fshl`/`getValue_fshr` `@[veir_bv_normalize]` lemmas already relate
  the funnel shift's modular shift amount to the register op's `extractLsb 5 0`). Because the source
  pattern carries an extra `if a ≠ b` conditional over `lowerSignedMinMaxLocal`, the *frozen* (unpeeled)
  copy of `hpattern` that survives in context sends the structural-fact `grind`s into an exponential
  case-split blowup; the fix is to establish every op-vs-op and `op`-vs-created distinctness fact and
  every `ctx₄` in-bounds witness as an **inline term** (`createOp_new_inBounds`/`inBounds_mono`/
  `createOp_new_not_inBounds`), `clear` the in-bounds hypotheses (they break `grind` by
  non-monotonicity), and pass the in-bounds witnesses explicitly to the forward lemmas — after which
  bare `grind` closes each structural fact by e-matching without touching `hpattern`.
- `lowerBinopNotLocal match? dst props` (`RISCV64Sdag.lean`) — match a two-operand LLVM integer
  op on `i64` one of whose operands is a `not` (`xor _, -1`, via `matchNot`, on either side),
  then emit `castToRegLocal` ×2 → binary reg-reg `dst` → `replaceWithRegLocal`. Its shared
  correctness proof is `lowerBinopNotLocal_preservesSemantics`
  (`RewriteProofs/LowerBinopNot.lean`). This is the first *DAG-matching* proof: it recovers the
  runtime value of the matched `not` from the `EquationLemmaAt` hypothesis (see
  "Matched-subgraph semantics" below).
- `ashr_local` (`RISCV64.lean`) — `llvm.ashr` on `i8`/`i32`/`i64`: two `unrealized_conversion_cast`s
  (operands → registers) → an arithmetic-shift-right riscv op → `unrealized_conversion_cast`. The
  riscv op is width-dependent: `riscv.sra` (`i64`), `riscv.sraw` (`i32`, word arithmetic shift), and
  `riscv.sra` on a `riscv.sextb`-sign-extended value (`i8`, since `castToRegLocal` holds the operand
  *zero*-extended). Standalone proof `ashr_local_preservesSemantics`
  (`RewriteProofs/LowerAshr.lean`); it verifies via `verifyIntegerBinop` (so `Verified.llvm_ashr`
  gives `IsVerifiedIntegerBinop` — both operands and the result share `intType`, no width-derivation
  needed) and its interpreter arm is `.int`-only, so — unlike `shl`/`lshr`, which moved to the
  byte-aware `lowerByteBinaryWLocal` — there is no byte case. Three width branches: `i32`/`i64` are
  4-op chains (like `LowerBinaryW`), `i8` is a 5-op chain threading an extra
  `interpretOp_riscv_unaryReg_forward` step for the `sextb` (like `LowerSignedMinMax`'s `sextw`), with
  the `getOpType!`/`getOperands!`/`getResultTypes!` transports seeded explicitly (4–5 creations deep).
  The three data lemmas (`ashr_isRefinedBy_toInt_sra`/`_sraw`/`_sra_sextb`) are the shift-refinement
  core: the RISC-V op masks the shift amount to the low 5/6 bits while `llvm.ashr` is poison for
  `y ≥ w`, so the proof follows the `ctlz` template (manual `getValue_ashr`/`getValue_eq_getValueD`
  rewrites so `bv_decide` unifies `getValue`/`getValueD`) *and* expands `hnp` via `isPoison_ashr` into
  `getValueD` form to hand `bv_decide` the `y < w` bound it needs for the masked-shift equality.
- `sext_1_local` (`RISCV64Sdag.lean`) — the concrete `llvm.sext %x : i1 to i64` (or `to i32`) ⟶
  `unrealized_conversion_cast` → `riscv.slli _, 63` → `riscv.srai _, 63` →
  `unrealized_conversion_cast` lowering (shifting the low bit to the top and arithmetic-shifting it
  back splats it across the register, realizing the sign extension of an `i1`). Not a combinator: it
  is a *standalone* proof (`sext_1_local_preservesSemantics`, `RewriteProofs/LowerSextOne.lean`)
  modelled on the `lowerExtLocal` single-operand-extension template, reusing
  `matchExtOp_interpretOp_unfold` and the data-level `sextLike_isRefinedBy_toInt` from
  `LowerExt.lean`. It is the first proof of a lowering that emits *immediate*-form riscv ops
  (`slli`/`srai`), via the new generic forward lemma `interpretOp_riscv_unaryReg_imm_forward` (the
  immediate cousin of `interpretOp_riscv_unaryReg_forward`, taking the op's actual property bundle as
  input since the result depends on it). Two notable points: (a) the emitted register chain is
  *identical* for both result widths (`slli 63; srai 63` yields `0`/`-1`, which reads correctly as
  `0`/`-1` at 32 or 64 bits), so there is *no* bitwidth branch — the result width `retW ∈ {32, 64}`
  only enters the cast-back type and the width-generic refinement lemma, and its `∧`-of-`≠` guard
  peels with the *unprimed* `peelSplittableCondition` (unlike a single-`≠` guard, which the initial
  `simp` swaps); (b) the chain has *four* created ops, so the `getOperands!`/`getProperties!`
  structural facts need the transport lemmas seeded explicitly (the "past ~3 creations deep" grind
  limit), and the two `getProperties!` reads use the op-code-agnostic
  `getProperties!_WfRewriter_createOp_ne` chained across the later creations. The only new data lemma
  is the `srai 63 ∘ slli 63` value characterisation (`srai_slli_63_val`).
- `zext_1_local` (`RISCV64Sdag.lean`) — the concrete `llvm.zext %x : i1 to i64` ⟶
  `unrealized_conversion_cast` → `riscv.andi _, 1` → `unrealized_conversion_cast` lowering (masking
  the low bit realizes the zero extension of an `i1`). Not a combinator: it is a *standalone* proof
  (`zext_1_local_preservesSemantics`, `RewriteProofs/LowerZextOne.lean`) modelled on the
  `lowerExtLocal` single-operand-extension template, but at the fixed `i1 → i64` widths and with the
  middle op an *immediate*-form `riscv.andi` rather than a plain unary reg-to-reg op. It *reuses*
  `matchExtOp_interpretOp_unfold` and the data-level `zextLike_isRefinedBy_toInt` from
  `LowerExt.lean`; the only new pieces are the `andi 1` value characterisation (`andi_one_val`) and
  the immediate-op forward lemma `interpretOp_riscv_unaryReg_imm_forward`. It is the first proof of a
  lowering that emits an immediate-form riscv op — the template for the `selectBinopImmLocal` family
  (which additionally needs a `matchConstantIntVal` DAG-matching Layer-3 lemma).
- `selectBinopImmLocal match? dst h width lo hi` (`RISCV64Sdag.lean`) — the *immediate-form binop*
  combinator: match `OP x (const imm)` with `imm ∈ [lo, hi]` and the result of width `width`, then
  emit `castToRegLocal x` → an immediate-form `riscv` op `dst` carrying `imm` → `replaceWithRegLocal`.
  Its shared correctness proof is `selectBinopImmLocal_preservesSemantics`
  (`RewriteProofs/LowerSelectBinopImm.lean`), instantiated for `addi`/`ori`/`andi`/`xori` (`i64`,
  `imm12`), `srai` (`i64`, `uimm6`), `addiw` (`i32`, `imm12`) and `sraiw` (`i32`, `uimm5`). It *fuses*
  the two earlier shapes: the binary-source, match-through-a-defining-op handling of
  `lowerBinopNotLocal` (the source op is binary and one operand is matched through its defining op)
  with the single-operand immediate-emit chain of `zext_1_local`. The right-hand *constant* operand is
  *folded* into the emitted op's immediate rather than cast, so — unlike `lowerBinopNotLocal` — only
  the *left* operand is cast (a three-op chain), and the matched constant's runtime value is pinned
  with the new graph lemma `matchConstantIntVal_getVar?_of_EquationLemmaAt` (`CommonGraphLemmas.lean`),
  the constant analogue of `matchNot_getVar?_of_EquationLemmaAt`. Because `width` is a *parameter* (one
  instance per width), there is *no* bitwidth branch. The data-refinement lemmas confront the symbolic
  immediate: the emitted op *sign-extends* a 12-bit field (or truncates a 5-/6-bit shift amount) while
  the LLVM constant is full-width. The trick is to *bridge* the encodings — `signExtend_ofInt_12_64`
  (for `c ∈ [-2048, 2047]`, `signExtend 64 (ofInt 12 c) = ofInt 64 c`) and `setWidth_ofInt_{5,6}_64`
  (`setWidth k (ofInt 64 c) = ofInt k c`) — then `generalize BitVec.ofInt 64 c = v` so both sides are
  a *single* abstract 64-bit vector `v`, and `veir_bv_decide` closes the rest (the shift lemmas need
  *no* range bound because LLVM's shift-past-width poison makes the refinement trivial there). The
  matched-property equation is *not* needed (the combinator reads `getProperties!` directly). The
  four `shl`/`lshr` immediate instances (`slli`/`srli`/`slliw`/`srliw`) need a *second* combinator
  proof, `selectBinopImmLocal_shift_preservesSemantics`: `llvm.shl`/`llvm.lshr` verify via
  `verifyLLVMShift` (which permits a byte or *different-width* shift operand), so they yield the
  weaker `IsVerifiedLLVMShift` (`Verifier.lean`) rather than `IsVerifiedIntegerBinop` — it pins only
  the result-vs-operand-0 type match and that operand 1 is *some* integer. The operand-width equality
  is instead recovered *dynamically*: `matchShiftOp_interpretOp_unfold` reads the interpreter's own
  width guard out of the successful source interpretation, and `subst`ing it collapses the proof to
  the binop shape (so the same three-op tail and refinement lemmas apply). The `shl`/`lshr` `hSemSrc`
  is discharged by `shl_shiftSem`/`lshr_shiftSem`, which case-split the interpreter's `if bw' ≠ bw`.
- `trunc_local` (`RISCV64.lean`) — `llvm.trunc` on integer *and* byte operands: two
  `unrealized_conversion_cast`s (`operand → reg`, then `reg → result-type`) that keep only the low
  `resBw` bits. Not a combinator: a *standalone* proof (`trunc_local_preservesSemantics`,
  `RewriteProofs/LowerTrunc.lean`). It is the first proof to cover `llvm.byte`-typed values, so it
  adds a whole byte layer paralleling the integer one: the forward lemmas
  `interpretOp_castToReg_byte_forward` / `interpretOp_castBack_byte_forward`
  (`CommonForwardInterpret.lean`) and the refined-operand reader
  `LocalRewritePattern.exists_refined_byte_getVar?` (`CommonBaseLemmas.lean`), plus the
  `conforms_int_type` / `conforms_byte_type` helpers that pin a runtime value's declared type. The
  proof matches on the operand runtime value (`.int` vs `.byte`) and runs the two branches
  symmetrically, each ending in the round-trip refinement data lemma (`trunc_isRefinedBy_toInt` /
  `trunc_isRefinedBy_toByte`). Two notable points: (a) `trunc_local` was *width-limited* to
  `{8, 16, 32, 64}` — the round trip through a 64-bit register is only sound for register-representable
  widths (the width-generic version is genuinely unsound for a result wider than 64 bits), and the
  restriction also makes the widths *concrete* so the data lemmas discharge by `rcases`-ing on the four
  widths and `revert h; veir_bv_decide` at each (the byte lemma additionally `simp only [RISCV.Reg.toByte,
  LLVM.Byte.toReg]` first, since those projections aren't `@[veir_bv_normalize]`); (b) `trunc_local`
  emits the two casts with *raw* `WfRewriter.createOp!` (not the `castToRegLocal`/`replaceWithRegLocal`
  helpers), so the casts peel with `peelOpCreation!` and the type/width guards are resolved by folding
  the type-equality rewrites *into* the `getIntByteTypeBitwidth` unfold
  (`simp only [getIntByteTypeBitwidth, hOperandType, hResInt]`) so both the operand- and result-side
  bitwidth matches reduce before the manual guard splits.

The generic theorem is parameterized over everything opcode-specific:

```lean
theorem lowerUnaryWLocal_preservesSemantics
    (hMatchImplies : …)   -- syntactic facts from a successful match?     (Layer 2)
    (hVerified    : …)   -- Verified op ⇒ IsVerifiedIntegerUnop           (Layer 1)
    (hSemSrc      : …)   -- Llvm.interpretOp' srcOp … = srcFn             (rfl)
    (hSemR64      : …)   -- Riscv.interpretOp' op64 … = f64               (rfl)
    (hSemR32      : …)   -- Riscv.interpretOp' op32 … = f32               (rfl)
    (hRefine64    : …)   -- srcFn x props ⊒ toInt (f64 (toReg xt)) 64     (Layer 0)
    (hRefine32    : …)   -- srcFn x props ⊒ toInt (f32 (toReg xt)) 32     (Layer 0)
    : LocalRewritePattern.PreservesSemantics (lowerUnaryWLocal match? op64 op32 props64 props32) …
```

so instantiating it for a concrete lowering is a single term. The three `hSem*` interpreter
computation facts are discharged by `rfl` at concrete opcodes. Example (`ctlz`):

```lean
theorem ctlz_local_preservesSemantics :
    LocalRewritePattern.PreservesSemantics ctlz_local h h₂ h₃ h₄ :=
  lowerUnaryWLocal_preservesSemantics
    (srcOp := .intr__ctlz)
    (srcFn := fun x props => Data.LLVM.Int.ctlz x props.is_zero_poison)
    (f64 := Data.RISCV.clz) (f32 := Data.RISCV.clzw)
    (fun hMatch => matchCtlz_implies hMatch)
    (fun opVerif hOpType => OperationPtr.Verified.llvm_intr__ctlz opVerif hOpType)
    (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (fun _ _ props h => ctlz_isRefinedBy_toInt_clz props.is_zero_poison h)
    (fun _ _ props h => ctlz_isRefinedBy_toInt_clzw props.is_zero_poison h)
```

The instantiations live in `namespace Example` at the bottom of `LowerUnaryW.lean`.

## The per-lowering layers

### Layer 0 — Pure data refinement lemmas (per lowering, the only real new work)

The mathematical core, stated purely on `Data.LLVM.Int` / `Data.RISCV.Reg` with no IR at all,
one per (bitwidth, RISC-V opcode) branch:

```lean
theorem ctlz_isRefinedBy_toInt_clz {x xt : Data.LLVM.Int 64} (pf : Bool) (h : x ⊒ xt) :
    Data.LLVM.Int.ctlz x pf ⊒ RISCV.Reg.toInt (Data.RISCV.clz (LLVM.Int.toReg xt)) 64
```

i.e. *"round-tripping the (possibly more defined) operand through registers and running the
RISC-V instruction refines the LLVM operation"*.

Proof recipe: unfold refinement with `Data.LLVM.Int.isRefinedBy_iff`, split the
poison/value obligations, reduce the value equality to a bitvector goal, close with
`bv_decide` / `veir_bv_decide`. Poison bookkeeping (`isPoison_ctlz`, `getValueD_eq`, …) usually
falls to `grind`. For binops the statement takes two refined operands
(`h₁ : x ⊒ xt`, `h₂ : y ⊒ yt`).

These lemmas live next to the instantiation (`Example` namespace of `LowerUnaryW.lean`); if they
grow they can move to `Veir/Data/…/Lemmas.lean`.

### Layer 1 — Verifier facts (per LLVM opcode, mostly shared)

A `Verified.*` lemma in `Veir/Verifier.lean` extracting the structural facts the verifier
guarantees for the matched opcode:

```lean
theorem OperationPtr.Verified.llvm_intr__ctlz … : op.IsVerifiedIntegerUnop ctx
```

`IsVerifiedIntegerUnop` / `IsVerifiedIntegerBinop` bundle: operand/result/successor/region
counts, result type = operand type, and that type is an integer type. The heavy lifting is done
once per *shape* (`verifyIntegerUnop_eq_ok` + `verifyIntegerUnop_ok_of_Verified`); the
per-opcode lemma is then a three-liner that just points the dispatcher at the concrete opcode.
These exist for the unops and binops proven or planned so far. Ops with a different verifier
shape (e.g. `icmp`, `select`, `load`/`store`) need their own `IsVerified*` bundle, built the
same way.

### Layer 2 — Matcher facts (per LLVM opcode, mostly exist already)

`matchFoo_implies` in `Veir/Passes/Matching/Lemmas.lean`: what a successful `matchFoo` says
syntactically — op type, number of results, `getOperands! = #[operand…]`, and the properties
equation. These exist for most matchers already; if one is missing, copy an existing one
(the proof is `simp only [matchFoo, bind, Option.bind, pure]` + `grind`).

### Layer 3 — Matched-subgraph semantics (per *matcher*, only for DAG-matching patterns)

Patterns that inspect an operand's *defining op* (`matchNot`, `matchConstantIntVal`,
`getDefiningOp` + `matchShl`/…) match more than the interpreted op, so their proofs need the
*runtime* value of the matched subgraph, not just syntax. `PreservesSemantics` provides exactly
the needed invariant: `state.EquationLemmaAt (InsertPoint.before op)` says every *pure* op
dominating the match point has already been interpreted consistently into the source state.
`RewriteProofs/CommonGraphLemmas.lean` packages this per matcher:

- `OperationPtr.Pure.llvm_xor` / `.llvm_mlir__constant` — per-opcode purity facts (needed to
  invoke `EquationLemmaAt`; one short `split`/`simp` proof per opcode);
- `matchBinaryOp_interpretOp_unfold` / `constantOp_interpretOp_unfold` — unfold one successful
  `interpretOp` of the given shape into its result bindings; applied at `newState := state`
  they unfold an `EquationHolds` fact;
- `matchNot_getVar?_of_EquationLemmaAt` — the packaged lemma: a successful `matchNot v = some y`
  with `v` an operand of `op` yields `getVar? v = xor yv (-1)` where `yv` is `y`'s value, plus
  the structural side conditions (`y`'s type, dominance at `before op`, in-bounds,
  not-a-result-of-`op`) that `exists_refined_int_getVar?` needs.

A new matcher (e.g. `matchConstantIntVal` for the immediate-selection patterns) gets one such
lemma, built the same way: syntactic facts from the `match*_implies` lemma, dominance of the
defining op via `strictlyDominates_of_getDefiningOp!_of_mem_getOperands!` (plus
`strictlyDominates_trans` for deeper chains), purity, then `EquationHolds` unfolding.

## The shared machinery (already written, reused by every combinator proof)

### Source-interpretation unfolding

`matchUnaryOp_interpretOp_unfold` (`LowerUnaryW.lean`) is generic over the source opcode: given
the matcher's syntactic facts, the `hSemSrc` computation fact, and a successful
`interpretOp op state`, it produces

- the operand's runtime value **as an existential** (`∃ x, state.variables.getVar? operand = some (.int bw x)`),
- memory unchanged,
- the result variable bound to `srcFn x props`,
- `cf = none`.

The operand value is *derived* inside the lemma — from `interpretOp_some_iff`, the matcher's
`getOperands!` fact, and `VariableState.getVar?_conforms` + the operand's integer type
(`RuntimeValue.Conforms.integerType` turns "conforms to `i{bw}`" into "`= .int bw x`") — so
callers don't have to supply it. `matchBinaryOp_interpretOp_unfold` (`CommonGraphLemmas.lean`)
is the binop analogue exposing two existentials, via two
`Array.exists_mapM_option_eq_some_iff` reads (indices 0 and 1); it doubles as the
`EquationHolds` unfolder for matched defining binops (Layer 3).

Note: for binops the `hSemSrc` computation fact is *not* `rfl` — the interpreter's binop arms
check the two operand bitwidths against each other (`if h : bw' ≠ bw then none else … rhs.cast …`),
which is stuck on a variable bitwidth. Instantiations discharge it with
`by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp]` instead.

### Forward lemmas for the emitted ops

`CommonForwardInterpret.lean` holds *forward symbolic-execution* lemmas, thin specializations of
the generic `interpretOp_forward` (`Veir/Interpreter/Lemmas.lean`):

- `interpretOp_castToReg_forward` — `unrealized_conversion_cast`, `.int bw x` ↦ `.reg (toReg x)`;
- `interpretOp_castBack_forward` — the reverse cast, `.reg r` ↦ `.int bw (toInt r bw)`;
- `interpretOp_riscv_unaryReg_forward` — **generic over the RISC-V opcode**: any unary
  reg-to-reg op whose `Riscv.interpretOp'` maps `.reg r` to `.reg (f r)` (hypothesis `hSem`,
  discharged by `rfl` at each concrete opcode). Covers `clz`/`clzw`/`ctz`/`ctzw`/`cpop`/`cpopw`
  and any future unary Zbb op with **no new lemma needed**;
- `interpretOp_riscv_binaryReg_forward` — the binary analogue: two register operands mapped to
  `.reg (f r₁ r₂)`. Covers `add`/`sub`/`mul`/… and `andn`/`orn`/`xnor` with no new lemma needed.
  Beware the operand swap: the interpreter applies the data-level op as `RISCV.op op2 op1`, so
  instantiations pass `f := fun r₁ r₂ => RISCV.op r₂ r₁` and the Layer-0 lemmas are stated with
  `(toReg yt)` first.

Each lemma's conclusion gives the successful one-step interpretation, memory unchanged, the
result binding, and a **frame clause** (all non-result variables unchanged). The frame clause
is what lets facts about earlier values survive to later ops in the chain — see the two-cast
prefix of `lowerBinopNotLocal_preservesSemantics`, where the second cast's frame keeps the
first cast's result binding and the first cast's frame keeps `y`'s value; the membership side
conditions (`y ∉ xCastOp.getResults!`, `xCastOp.getResult 0 ∉ yCastOp.getResults!`) are
discharged by `ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds`
(`CommonBaseLemmas.lean`): a value existing *before* a `createOp` is never a result of the
freshly created op. New emitted-op *shapes* (ops with immediates, `li`) need one new
specialization each — ~20 lines of boilerplate: instantiate `interpretOp_forward` with explicit
`vals := #[…]`, `results := #[…]`, `mem' := state.memory`, and discharge the three obligations
with the same `simp` scripts as the existing ones.

### Peel tactics

`CommonTactics.lean` provides macros that mirror the monadic structure of the pattern in
`hpattern`:

- `peelSplittableCondition` / `peelSplittableCondition'` — split an `if`/`match` guard,
  discharge the impossible branch with `grind`;
- `peelOpCreation` / `peelOpCreation!` — peel one op-creation bind, introducing the updated
  context, the new op, and the creation hypothesis (the `!` form also rewrites `createOp!` to
  plain `createOp` and transports a dominance hypothesis into the new context);
- `peelCastToRegLocal` / `peelReplaceWithRegLocal` — same, specialized to the two cast helpers;
- `peelCastToRegLocal₂` / `peelOpCreation!₂` / `peelReplaceWithRegLocal₂` — binary-lowering
  variants that transport *two* dominance hypotheses (one per matched operand) through each
  creation step;
- `cleanupHpattern` — substitute the final `newOps`/`newValues`/`newCtx` equalities.

The matcher itself is peeled inline in the generic proof (case on `match? op ctx.raw`, the
`none` branch contradicts `hpattern`), since the matcher is now a *parameter* rather than a
concrete function.

### Base lemmas

`CommonBaseLemmas.lean` holds the glue: `LocalRewritePattern.exists_refined_int_getVar?`
(read a refined integer operand in the target state), `WfRewriter.createOp!_none_eq`
(reduce `createOp!` at a `none` insertion point to `createOp`), `getProperties!` preservation
lemmas, and the axiom `ValuePtr.dominatesIp_before_WfRewriter_createOp` (dominance is preserved
when creating a detached op — axiomatised because `dominatesIp` is opaque).

## Checklist: proving a new lowering

**If it fits `lowerUnaryWLocal`** (single integer operand, one unary reg-to-reg RISC-V op per
bitwidth): define it as a `lowerUnaryWLocal` instance in `RISCV64.lean`, then in the `Example`
namespace of `LowerUnaryW.lean`:

1. **Layer 0**: `foo_isRefinedBy_toInt_<riscvop>` — one per bitwidth branch.
2. **Layer 1**: check `OperationPtr.Verified.llvm_foo` exists in `Verifier.lean`; add the
   three-liner if missing.
3. **Layer 2**: check `matchFoo_implies` exists in `Matching/Lemmas.lean`; add if missing.
4. Instantiate `lowerUnaryWLocal_preservesSemantics` (the three `hSem*` arguments are `rfl`).
5. **Axiom check**: `#guard_msgs in #print axioms foo_local_preservesSemantics` to pin the
   axiom footprint.

**If it fits `lowerBinaryWLocal`** (two integer operands of the same type, one binary reg-to-reg
RISC-V op per bitwidth, total LLVM interpretation — no UB branches): same recipe against
`lowerBinaryWLocal_preservesSemantics` in `LowerBinaryW.lean`, with the differences:

- Layer-0 lemmas take two refined operands and are stated with the target registers swapped
  (`RISCV.op (toReg yt) (toReg xt)`, matching the interpreter's `RISCV.op op2 op1`);
- `hSemSrc` is `by simp [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp]` (see above),
  `hSemR64`/`hSemR32` stay `rfl` with `f64 := fun r₁ r₂ => RISCV.op64 r₂ r₁` (same for `f32`);
- `matchFoo_implies` returns the two operands (`op.getOperands! ctx = #[lhs, rhs]`), and Layer 1
  is `IsVerifiedIntegerBinop` (`Verified.llvm_add`/`llvm_sub`/… exist for all merged ops).

**If it fits `lowerBinopNotLocal`** (two integer operands with a `not` on one side, one binary
reg-to-reg RISC-V op at `i64`): same steps against `lowerBinopNotLocal_preservesSemantics` in
`LowerBinopNot.lean`, with *two* Layer-0 lemmas (one per `not`-operand orientation; mind the
riscv operand order, see the forward-lemma note above).

**If it needs a new shape** (binop, longer chain, extra guards): first factor the lowering
through a new combinator in `RISCV64.lean`, then prove that combinator's
`PreservesSemantics` once, generic over the opcode-specific parameters, following
`lowerUnaryWLocal_preservesSemantics` as the template. Its proof body is a linear script:
peel the matcher and guards, unfold the source interpretation, peel the op creations (one
`peel*` per created op, in program order), read the refined operand(s) with
`exists_refined_int_getVar?`, establish the structural facts about the created ops (`grind`,
seeded with `*_WfRewriter_createOp` transport lemmas where needed), symbolically execute the
emitted chain with the forward lemmas, and assemble the simulation triple. Then instantiate
per lowering as above.

## Adapting to other lowering shapes

- **Binops**: done — `lowerBinaryWLocal_preservesSemantics` (`LowerBinaryW.lean`). The proof
  follows the unary template with: two `castToRegLocal` peels (via the `peel*₂` macros carrying
  both operands' dominance), two `exists_refined_int_getVar?` reads, two "operand is not a
  result of `op`" facts, `matchBinaryOp_interpretOp_unfold`, and
  `interpretOp_riscv_binaryReg_forward`. Crucially, when executing the chain, the value of `rhs`
  must survive the first cast and the *first* cast's result must survive the *second* cast's
  interpretation: keep the **frame clause** of the forward lemmas (bind it as `hFrame` instead
  of discarding with `-`) and rewrite the earlier bindings through it. The membership side
  conditions (`rhs ∉ lcastOp.getResults! …`, `lcastOp.getResult 0 ∉ rcastOp.getResults! …`) are
  *not* one-shot `grind`s: establish the freshness facts once before the bitwidth split
  (`createOp_new_not_inBounds` + `ValuePtr.inBounds_opResult`) and case on
  `getResults!_not_mem_or_eq_getResult` in each branch (or use
  `ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds` from `CommonBaseLemmas.lean`, as in
  `LowerBinopNot.lean`).
  Ops whose LLVM interpretation can raise UB (`sdiv`, `udiv`, `srem`, `urem`) do not fit the
  total `hSemSrc` hypothesis; they are merged into the combinator *definition* but still need a
  UB-aware proof variant.
- **DAG-matching patterns** (`selectBinopImmLocal`, `bexti_local`, `orcb_local`, …): each
  matcher applied to a *defining op* needs one Layer-3 lemma
  (`match*_getVar?_of_EquationLemmaAt` style, see `matchNot_getVar?_of_EquationLemmaAt`);
  constants additionally reuse `constantOp_interpretOp_unfold` and
  `OperationPtr.Pure.llvm_mlir__constant` as-is.
- **Longer chains** (`bswap_local` 32-bit emits `cast, rev8, srli, castBack`): one extra
  `peelOpCreation!` and one extra forward-lemma application per op; ops with an immediate
  (`srli`) need their forward lemma to take the properties (`RISCVImmediateProperties`) into
  account when unfolding `Riscv.interpretOp'`.
- **Nested branching** (`bswap_local` branches *after* creating `rev8Op`): the `rcases` on the
  bitwidth happens at the point where `hpattern` branches; peel the shared prefix first, split,
  then peel each branch's suffix.
- **Guards other than bitwidth** (e.g. constant-operand checks in `fshrConst_local`): each
  `if c then return (ctx, none)` / `let some … := … | return (ctx, none)` in the pattern is one
  `peelSplittableCondition` / matcher-style peel; the surviving hypothesis feeds the data lemma.

## Gotchas

- **`RewriteProofs` is not in the lake build graph**: nothing under `Veir/` imports these files,
  so `lake build` alone does not check them. Build them explicitly, e.g.
  `lake build Veir.Passes.InstructionSelection.RewriteProofs.LowerUnaryW`.
- **`interpretOp_forward` needs explicit `vals`/`results`/`mem'`** — unification won't infer
  them from the goal.
- **`clear hpattern` inside dischargers**: the `peel*` macros clear `hpattern` in their
  `by grind`/`by simp` side goals so its proof term isn't captured, which would block later
  peels. Keep this if you write new peel macros.
- **`grind` seeding for transport chains**: facts about ops created two contexts ago
  (`retOp`'s result types viewed in `ctx₃`) need the `*_WfRewriter_createOp` transport lemmas
  passed explicitly to `grind [...]`, instantiated at the right creation hypothesis.
- **Bitwidth literals**: destructure `intType` (`obtain ⟨bw⟩ := intType`) and `subst` the
  branch hypothesis before applying the Layer-0 lemmas, which are stated at literal `64`/`32`.
- **Identical guards split together**: in `lowerBinaryWLocal` both operands share `intType`, so
  the two bitwidth guards have syntactically equal conditions and a single
  `peelSplittableCondition` resolves both (a second one fails: nothing left to split).
- **`bv_decide` and multipliers**: the SAT solver times out on 64-bit multiplier equivalence
  (`mul_isRefinedBy_toInt_mul`). Rewrite both sides to the *same* product first
  (`getValue_mul`, `toInt_getValue`, `val_toReg`, `BitVec.setWidth_eq`), so the goal closes by
  `rw`/`rfl` (64-bit) or `bv_decide` sees structurally identical multipliers (32-bit `mulw`).
- **Structural facts through 4 creations**: plain `grind` no longer finds the transports for
  ops created three contexts back; seed `OperationPtr.getOperands!_WfRewriter_createOp` (and the
  `getResultTypes!` analogue) explicitly at each creation hypothesis, as in `LowerBinaryW.lean`.
- **Deep dominance transport / `grind` non-monotonicity** (the pain point of `LowerSignedMinMax`'s
  six-op `i32` chain): the `peelOpCreation!₂` macro discharges its `op.InBounds ctxₙ`,
  operand-in-bounds, and `op ≠ newOp` side goals with `grind`, and those `grind`s *fail past ~3
  creations deep* — worse, adding an `op.InBounds ctxₙ` hypothesis to the context to help them
  *breaks the macro's other `grind`s* (grind is non-monotonic in context size/shape). Fix: peel the
  deep ops **manually** rather than with the `!` macro, and build every `InBounds` witness as an
  *inline term* (never a context hypothesis): `op.InBounds ctxₙ` as a chain of
  `WfRewriter.createOp_inBounds_mono (ptr := .operation op)` from `opInBounds`; `op ≠ newOp` from
  `createOp_new_not_inBounds`; and the `createOp!_none_eq` operand-in-bounds discharge as an inline
  `have hIn … := createOp_new_inBounds/…_mono` + `have hNum : …getNumResults! … = 1` seed pair
  (`grind` won't chain `createOp_new_inBounds` + `inBounds_mono` + `getResult_inBounds` on its own).
  Also seed the `getOpType!` transport per creation when two emitted ops share an opcode (the two
  `sextw`s), or `grind` conflates them.
- **`maxHeartbeats`**: the combinator theorem needs `set_option maxHeartbeats 1000000` (many
  `grind` calls over a large context).
- **Expected axioms**: `#print axioms` will list the dominance axioms
  (`OperationPtr.dominates*`, `ValuePtr.dominatesIp*`,
  `IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates`,
  `ValuePtr.dominatesIp_before_WfRewriter_createOp`; DAG-matching proofs add
  `OperationPtr.strictlyDominates_trans` and
  `ValuePtr.dominatesIp_before_of_strictlyDominates`),
  `OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants`, `floatEqOfToBitsEq`,
  and a `…bv_decide.ax_…` native axiom per `bv_decide`/`veir_bv_decide` use (including
  `MemoryState.llvmLoad._native.bv_decide.ax_8` pulled in by the interpreter) — that's the
  accepted baseline, pin it with `#guard_msgs` (see the end of `LowerBinopNot.lean`).
- **Un-inferable implicits in packaged lemmas**: hypotheses whose only mention of a variable is
  inside a `(by grind)` default argument (e.g. `opInBounds` in
  `matchNot_getVar?_of_EquationLemmaAt`) must be *explicit* — unification cannot recover them
  from proof terms at the call site.
- **`simp` swaps negated `if` branches**: the initial `simp … at hpattern` applies
  `ne_eq`/`ite_not`, so a source-level `if t.bitwidth ≠ 64 then bail else continue` becomes
  `if t.bitwidth = 64 then continue else bail` — split it with
  `split at hpattern; case isFalse hne => simp at hpattern` and `rename_i hBw`, rather than
  assuming the source branch order (this is why `lowerBinopNotLocal_preservesSemantics` does
  not use `peelSplittableCondition` for the bitwidth guard).

## File map

| File | Contents | Growth per new lowering |
|---|---|---|
| `RewriteProofs/LowerUnaryW.lean` | `matchUnaryOp_interpretOp_unfold`, `lowerUnaryWLocal_preservesSemantics`, and per-lowering Layer-0 lemmas + instantiations | two data lemmas + one instantiation (unary); new file per new *shape* |
| `RewriteProofs/LowerBinaryW.lean` | `lowerBinaryWLocal_preservesSemantics`, and per-lowering Layer-0 lemmas + instantiations (`add`, `sub`, `mul`, `xor`) | two data lemmas + one instantiation (binary) |
| `RewriteProofs/LowerBinaryReg.lean` | `lowerBinaryRegLocal_preservesSemantics` (width-agnostic single-op binary) + per-lowering Layer-0 lemmas + instantiations (`umax`, `umin`) | two data lemmas + one instantiation (binary, single op) |
| `RewriteProofs/LowerBitwiseReg.lean` | `lowerBitwiseRegLocal_preservesSemantics` (bitwise single-op binary over `i64`/`i32`/`i8`/`i1`; one width-generic refinement lemma, no bitwidth branch) + instantiations (`and`, `or`) | one width-generic data lemma + one instantiation |
| `RewriteProofs/LowerSignedMinMax.lean` | `lowerSignedMinMaxLocal_preservesSemantics` (signed min/max; `i64` = 4 ops, `i32` = 6 ops with two extra `riscv.sextw`) + `_64`/`_32` data lemmas + instantiations (`smax`, `smin`) | two data lemmas + one instantiation |
| `RewriteProofs/LowerRotate.lean` | `matchTernaryOp_interpretOp_unfold` (ternary source unfold) + `lowerRotateLocal_preservesSemantics` (rotate; ternary source with `a = b`, result-type guard, `W`-variant bitwidth branch) + `_64`/`_32` data lemmas + instantiations (`fshl`, `fshr`) | two data lemmas + one instantiation |
| `RewriteProofs/LowerFshConst.lean` | `fshConstLike_preservesSemantics` (GlobalISel constant word-rotate combinator: `fshl`/`fshr a a (const)` on `i64`/`i32` → `riscv.rori`/`roriw` with the normalized/negated 5-/6-bit amount; ternary `a = b`, constant amount pinned via the graph lemma, immediate-emit single-cast head with a bitwidth branch over the emitted rotate op) + instantiations (`fshrConst`/`fshlConst`), `ofInt_{5,6}_rot{r,l}` mod bridges + `fsh{r,l}_{roriw_32,rori_64}` data lemmas + `#guard_msgs` axiom pins | — (one-off pair) |
| `RewriteProofs/LowerBinopNot.lean` | `lowerBinopNotLocal_preservesSemantics` (the DAG-matching template proof), per-lowering Layer-0 lemmas + instantiations (`andn`/`orn`/`xnor`), `#guard_msgs` axiom pins | two data lemmas + one instantiation (binop-with-not) |
| `RewriteProofs/LowerSelectCzero.lean` | `selectCzeroeqz_local_preservesSemantics` / `selectCzeronez_local_preservesSemantics` (branchless `llvm.select c t 0`/`select c 0 f` → `riscv.czeroeqz`/`czeronez`: `i1` cond + value cast, constant-zero operand dropped via `matchConstantZero`; width-generic, no bitwidth branch) + `matchSelectOp_interpretOp_unfold` (mixed-width ternary unfold, `i1` cond) + `czeroeqz`/`czeronez_isRefinedBy` data lemmas + `#guard_msgs` axiom pins | — (one-off pair) |
| `RewriteProofs/LowerAshr.lean` | `ashr_local_preservesSemantics` (standalone `i8`/`i32`/`i64` `ashr`; three width branches, `i8` adds a `sextb`), `ashr_isRefinedBy_toInt_sra`/`_sraw`/`_sra_sextb` (shift-refinement data lemmas: `ctlz`-style `getValue`→`getValueD` + `isPoison_ashr` `y<w` bound), `#guard_msgs` axiom pin | — (one-off) |
| `RewriteProofs/LowerSextOne.lean` | `sext_1_local_preservesSemantics` (standalone `i1 → i64`/`i32` sext ⟶ `srai (slli _ 63) 63`; four-op chain, no bitwidth branch, first immediate-emitting proof), `srai_slli_63_val` + `sext1_isRefinedBy_toInt_srai_slli` (reusing `matchExtOp_interpretOp_unfold` / `sextLike_isRefinedBy_toInt` from `LowerExt.lean`), `#guard_msgs` axiom pin | — (one-off) |
| `RewriteProofs/LowerZextOne.lean` | `zext_1_local_preservesSemantics` (standalone `i1 → i64` zext ⟶ `andi 1`; first immediate-emitting proof), `andi_one_val` + `zext1_isRefinedBy_toInt_andi` (reusing `matchExtOp_interpretOp_unfold` / `zextLike_isRefinedBy_toInt` from `LowerExt.lean`), `#guard_msgs` axiom pin | — (one-off) |
| `RewriteProofs/LowerSelectBinopImm.lean` | `selectBinopImmLocal_preservesSemantics` (immediate-form binop combinator: cast-lhs → `dst(imm)` → cast-back, constant RHS folded into the immediate; single width, no bitwidth branch) + the shift variant `selectBinopImmLocal_shift_preservesSemantics` (+ `matchShiftOp_interpretOp_unfold`, `shl_shiftSem`/`lshr_shiftSem`) + instantiations (`addi`/`ori`/`andi`/`xori`/`srai`/`addiw`/`sraiw` and `slli`/`srli`/`slliw`/`srliw`), the `signExtend_ofInt_12_64` / `setWidth_ofInt_{5,6}_64` immediate-encoding bridges, per-op `*_isRefinedBy` data lemmas, `#guard_msgs` axiom pins | one data lemma + one instantiation per immediate op |
| `RewriteProofs/CommonGraphLemmas.lean` | `matchBinaryOp_interpretOp_unfold` (shared by the binary combinator proofs) + Layer 3: `OperationPtr.Pure.llvm_*`, `constantOp_interpretOp_unfold`, `matchNot_getVar?_of_EquationLemmaAt`, `matchConstantIntVal_getVar?_of_EquationLemmaAt` | one packaged lemma per new *matcher* used on defining ops |
| `RewriteProofs/CommonForwardInterpret.lean` | forward lemmas (casts + byte casts `interpretOp_castToReg_byte_forward`/`interpretOp_castBack_byte_forward` + generic unary/binary reg-to-reg riscv ops + `interpretOp_riscv_unaryReg_imm_forward` for immediate-form unary ops) | one lemma per new emitted-op *shape* |
| `RewriteProofs/LowerTrunc.lean` | `trunc_local_preservesSemantics` (standalone `llvm.trunc` over integer *and* byte operands, widths `{8,16,32,64}`; two raw-`createOp!` casts, operand-value case split with symmetric int/byte branches), `trunc_isRefinedBy_toInt`/`_toByte` (concrete-width round-trip data lemmas via `revert; veir_bv_decide`), `conforms_int_type`/`conforms_byte_type`, `#guard_msgs` axiom pin | — (one-off; first byte-typed proof) |
| `RewriteProofs/CommonTactics.lean` | `peel*` macros (incl. the two-dominance `peel*₂` variants), `cleanupHpattern` | rarely |
| `RewriteProofs/CommonBaseLemmas.lean` | `exists_refined_int_getVar?`, `exists_refined_byte_getVar?`, `not_mem_getResults!_of_inBounds_of_not_inBounds`, `createOp!` reduction, properties/dominance transport | rarely |
| `RewriteProofs/CommonMatchLemmas.lean` | ctlz-specific unfold/peel lemmas — currently unused (superseded by the generic `matchUnaryOp_interpretOp_unfold`); candidate for deletion | — |
| `Veir/Passes/InstructionSelection/RISCV64.lean` | the GlobalISel lowering combinators (`lowerUnaryWLocal`, `lowerBinaryWLocal`, …) and their instances | one `def` (or a new combinator) |
| `Veir/Passes/InstructionSelection/RISCV64Sdag.lean` | the SelectionDAG lowering combinators (`lowerBinopNotLocal`, `selectBinopImmLocal`, …) and their instances | one `def` (or a new combinator) |
| `Veir/Verifier.lean` | `IsVerified*` bundles (`…IntegerUnop`/`Binop`/`Ternop`/`LLVMShift`/`Select`) + `Verified.llvm_*` extractors (Layer 1; incl. `Verified.llvm_mlir__constant`, `Verified.llvm_shl`/`llvm_lshr`, `Verified.llvm_select`) | one 3-line lemma (unop/binop/ternop/shift/select) |
| `Veir/Passes/Matching/Lemmas.lean` | `match*_implies` (Layer 2) | usually nothing |
| `Veir/Interpreter/Lemmas.lean` | generic `interpretOp_forward`, `interpretOpList_cons` | nothing |
| `Veir/Interpreter/EquationLemma.lean` | `Pure`, `EquationHolds`, `EquationLemmaAt` (the Layer-3 invariant) | nothing |
| `Veir/Dominance.lean` | dominance axioms (incl. `strictlyDominates_trans`, `dominatesIp_before_of_strictlyDominates`) | nothing |
| `Veir/PatternRewriter/Semantics.lean` | `PreservesSemantics` | nothing |
