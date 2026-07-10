import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.LLVM.Int.Bitblast
import Veir.Data.Refinement

import Veir.Meta.BVDecide

/-!
  Correctness proofs for the LLVM-dialect combines in `Combine.lean`.

  `Proofs.lean` covers the combines that rewrite already-selected `riscv` ops; those are
  exact equalities over the total `Data.RISCV.Reg` type. The combines proven here instead
  rewrite `llvm` ops, whose semantics carry poison, so the obligation is a *refinement*
  `source ⊒ target` rather than an equality: the rewritten value may be more defined than
  the original (`poison ⊒ v` for every `v`), but never less.

  Every theorem is named after the combine it justifies and is discharged by
  `veir_bv_decide`. Since `bv_decide` bitblasts, it needs concrete bitwidths; these
  theorems are therefore the `i64` instantiation of combines that are stated generically
  in `Combine.lean`. Width-changing combines use the `i32`/`i64` pair (`sext`/`zext` from
  `i32` to `i64`, `trunc` from `i64` to `i32`), and `i1` for `select` conditions and
  `icmp` results.

  ## Flag threading

  A combine may freely *drop* a flag from an op it rewrites — that only removes poison —
  but it must not *transplant* one onto a created op whose poison condition differs.
  Eighteen of these combines originally did the latter, with an integer-overflow flag
  (`nsw`/`nuw`), an `exact` flag, a `zext`'s `nneg`, or an `or`'s `disjoint`; they have
  since been fixed in `Combine.lean` to clear the offending flag on the op they create.

  The theorems below are stated against the fixed rewrites, so the created op carries a
  literal `false` exactly where `Combine.lean` clears a flag, while every flag read off a
  *matched* op stays a free variable. Each such docstring records the counterexample that
  motivated the clear, so this file doubles as the justification for the flag drops.
-/

namespace Veir.Data.LLVM.Int

private theorem h32_64 : (32 : Nat) < 64 := by omega
private theorem h64_32 : (64 : Nat) > 32 := by omega
private theorem h1_64 : (1 : Nat) < 64 := by omega

/-! ### hoist_logic_op_with_same_opcode_hands

  `(cast X) op (cast Y) → cast (X op Y)`, and the shift/`and` analogues. The rewrite keeps
  the *second* matched inner op's properties on the op it creates and discards the first
  one's, which is why the flag-carrying variants below need care.
-/

/-- `(sext X) & (sext Y) → sext (X & Y)`. `sext` carries no flags and is injective on bit
    positions, so this holds unconditionally. -/
theorem AndSextSext {x y : Int 32} :
    and (sext x 64 h32_64) (sext y 64 h32_64) ⊒ sext (and x y) 64 h32_64 := by
  veir_bv_decide

/-- `(sext X) | (sext Y) → sext (X | Y)`. Sound even with `disjoint`: `sext` neither
    creates nor destroys overlapping set bits, so the two `or`s are poison together. -/
theorem OrSextSext {d : Bool} {x y : Int 32} :
    or (sext x 64 h32_64) (sext y 64 h32_64) d ⊒ sext (or x y d) 64 h32_64 := by
  veir_bv_decide

/-- `(sext X) ^ (sext Y) → sext (X ^ Y)`. -/
theorem XorSextSext {x y : Int 32} :
    xor (sext x 64 h32_64) (sext y 64 h32_64) ⊒ sext (xor x y) 64 h32_64 := by
  veir_bv_decide

/-- `(zext X) & (zext Y) → zext (X & Y)`. Sound with both `nneg` flags free: `(X & Y)`
    has its msb set only if `Y` does, so the created `zext nneg` is poison only when the
    matched `zext y nneg` already was. -/
theorem AndZextZext {n0 n1 : Bool} {x y : Int 32} :
    and (zext x 64 n0 h32_64) (zext y 64 n1 h32_64) ⊒ zext (and x y) 64 n1 h32_64 := by
  veir_bv_decide

/-- `(zext X) | (zext Y) → zext (X | Y)`. The created `zext` must clear `nneg`.

    Keeping `Y`'s `nneg` would be unsound: take `X = -1`, `Y = 0`, `nneg` on `Y`'s `zext`
    only. The source is `0xffffffff` (neither `zext` is poison, since only `Y`'s carries
    `nneg` and `Y ≥ 0`), but `X | Y = -1` has its msb set, so a `zext nneg` of it would be
    poison. -/
theorem OrZextZext {n0 n1 d : Bool} {x y : Int 32} :
    or (zext x 64 n0 h32_64) (zext y 64 n1 h32_64) d ⊒ zext (or x y d) 64 false h32_64 := by
  veir_bv_decide

/-- `(zext X) ^ (zext Y) → zext (X ^ Y)`. The created `zext` must clear `nneg`, for the
    same reason as `OrZextZext`. -/
theorem XorZextZext {n0 n1 : Bool} {x y : Int 32} :
    xor (zext x 64 n0 h32_64) (zext y 64 n1 h32_64) ⊒ zext (xor x y) 64 false h32_64 := by
  veir_bv_decide

/-- `(trunc X) & (trunc Y) → trunc (X & Y)`. The created `trunc` must clear `nsw`, but may
    keep `Y`'s `nuw`: the high bits `X & Y` discards are a subset of `Y`'s.

    Keeping `nsw` would be unsound: `X = 2^31`, `Y = -1`. `trunc nsw Y` is fine (`Y`
    sign-extends back), the source is `0x80000000`, but `trunc nsw (X & Y)` is poison. -/
theorem AndTruncTrunc {s0 u0 s1 u1 : Bool} {x y : Int 64} :
    and (trunc x 32 s0 u0 h64_32) (trunc y 32 s1 u1 h64_32)
      ⊒ trunc (and x y) 32 false u1 h64_32 := by
  veir_bv_decide

/-- `(trunc X) | (trunc Y) → trunc (X | Y)`. The created `trunc` must clear both `nsw` and
    `nuw`, and the created `or` must clear `disjoint`.

    Two independent failures. (i) `nuw`/`nsw`: the high bits of `X | Y` can be nonzero
    because of `X` alone, poisoning the created `trunc` while the source is fine.
    (ii) `disjoint`: `X` and `Y` may overlap only in the discarded high bits, so an
    `or disjoint` of them is poison while the source `or` of the two truncations is not. -/
theorem OrTruncTrunc {s0 u0 s1 u1 d : Bool} {x y : Int 64} :
    or (trunc x 32 s0 u0 h64_32) (trunc y 32 s1 u1 h64_32) d
      ⊒ trunc (or x y false) 32 false false h64_32 := by
  veir_bv_decide

/-- `(trunc X) ^ (trunc Y) → trunc (X ^ Y)`. The created `trunc` must clear both `nsw` and
    `nuw`. Same high-bit argument as `OrTruncTrunc` (i). -/
theorem XorTruncTrunc {s0 u0 s1 u1 : Bool} {x y : Int 64} :
    xor (trunc x 32 s0 u0 h64_32) (trunc y 32 s1 u1 h64_32)
      ⊒ trunc (xor x y) 32 false false h64_32 := by
  veir_bv_decide

/-- `(X << Z) & (Y << Z) → (X & Y) << Z`. The created `shl` must clear `nsw`, but may keep
    `Y`'s `nuw`: the bits `X & Y` shifts out are a subset of `Y`'s.

    Keeping `nsw` would be unsound: `X = 2^62`, `Y = -2^62`, `Z = 1`. `shl nsw Y 1` is
    fine (`Y`'s top two bits agree), the source is `2^63`, but `X & Y = X` and
    `shl nsw X 1` is poison. -/
theorem AndShlShl {s0 u0 s1 u1 : Bool} {x y z : Int 64} :
    and (shl x z s0 u0) (shl y z s1 u1) ⊒ shl (and x y) z false u1 := by
  veir_bv_decide

/-- `(X << Z) | (Y << Z) → (X | Y) << Z`. The created `shl` must clear `nsw` and `nuw`,
    and the created `or` must clear `disjoint`. `X` alone can supply the bits that `X | Y`
    shifts out (breaking `nuw`/`nsw`), and `X`/`Y` can overlap only in bits that both
    shifts discard (breaking `disjoint`). -/
theorem OrShlShl {s0 u0 s1 u1 d : Bool} {x y z : Int 64} :
    or (shl x z s0 u0) (shl y z s1 u1) d ⊒ shl (or x y false) z false false := by
  veir_bv_decide

/-- `(X << Z) ^ (Y << Z) → (X ^ Y) << Z`. The created `shl` must clear `nsw` and `nuw`. -/
theorem XorShlShl {s0 u0 s1 u1 : Bool} {x y z : Int 64} :
    xor (shl x z s0 u0) (shl y z s1 u1) ⊒ shl (xor x y) z false false := by
  veir_bv_decide

/-- `(X >> Z) & (Y >> Z) → (X & Y) >> Z` (logical). Sound with both `exact` flags free:
    the low bits `X & Y` discards are a subset of `Y`'s. -/
theorem AndLshrLshr {e0 e1 : Bool} {x y z : Int 64} :
    and (lshr x z e0) (lshr y z e1) ⊒ lshr (and x y) z e1 := by
  veir_bv_decide

/-- `(X >> Z) | (Y >> Z) → (X | Y) >> Z` (logical). The created `lshr` must clear `exact`
    and the created `or` must clear `disjoint`: `X` alone can supply a nonzero discarded
    low bit, and `X`/`Y` can overlap only in the discarded low bits. -/
theorem OrLshrLshr {e0 e1 d : Bool} {x y z : Int 64} :
    or (lshr x z e0) (lshr y z e1) d ⊒ lshr (or x y false) z false := by
  veir_bv_decide

/-- `(X >> Z) ^ (Y >> Z) → (X ^ Y) >> Z` (logical). The created `lshr` must clear
    `exact`. -/
theorem XorLshrLshr {e0 e1 : Bool} {x y z : Int 64} :
    xor (lshr x z e0) (lshr y z e1) ⊒ lshr (xor x y) z false := by
  veir_bv_decide

/-- `(X >> Z) & (Y >> Z) → (X & Y) >> Z` (arithmetic). Sound with both `exact` flags
    free. -/
theorem AndAshrAshr {e0 e1 : Bool} {x y z : Int 64} :
    and (ashr x z e0) (ashr y z e1) ⊒ ashr (and x y) z e1 := by
  veir_bv_decide

/-- `(X >> Z) | (Y >> Z) → (X | Y) >> Z` (arithmetic). The created `ashr` must clear
    `exact` and the created `or` must clear `disjoint`. -/
theorem OrAshrAshr {e0 e1 d : Bool} {x y z : Int 64} :
    or (ashr x z e0) (ashr y z e1) d ⊒ ashr (or x y false) z false := by
  veir_bv_decide

/-- `(X >> Z) ^ (Y >> Z) → (X ^ Y) >> Z` (arithmetic). The created `ashr` must clear
    `exact`. -/
theorem XorAshrAshr {e0 e1 : Bool} {x y z : Int 64} :
    xor (ashr x z e0) (ashr y z e1) ⊒ ashr (xor x y) z false := by
  veir_bv_decide

/-- `(X & Z) & (Y & Z) → (X & Y) & Z`. No flags anywhere; unconditional. -/
theorem AndAndAnd {x y z : Int 64} :
    and (and x z) (and y z) ⊒ and (and x y) z := by
  veir_bv_decide

/-- `(X & Z) | (Y & Z) → (X | Y) & Z`. The created `or` must clear `disjoint`.

    Keeping it would be unsound: `X = 1`, `Y = -1`, `Z = -2`. The two `and`s are `0` and
    `-2`, which are disjoint, so the source is `-2`; but `X | Y` overlaps in bit 0, so an
    `or disjoint` of them would be poison. -/
theorem OrAndAnd {d : Bool} {x y z : Int 64} :
    or (and x z) (and y z) d ⊒ and (or x y false) z := by
  veir_bv_decide

/-- `(X & Z) ^ (Y & Z) → (X ^ Y) & Z`. `xor` carries no flags; unconditional. -/
theorem XorAndAnd {x y z : Int 64} :
    xor (and x z) (and y z) ⊒ and (xor x y) z := by
  veir_bv_decide

/-! ### sub_add_reg -/

/-- `(x + y) - y → x`. The source's flags only add poison, so they stay free. Stated at both
    widths the guarded pattern admits, since the graph-level proof needs `i32` too. -/
theorem sub_add_reg_x_add_y_sub_y {w : Nat} (hw : w = 64 ∨ w = 32) {as au ss su : Bool}
    {x y : Int w} : sub (add x y as au) y ss su ⊒ x := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `(x + y) - x → y`. -/
theorem sub_add_reg_x_add_y_sub_x {w : Nat} (hw : w = 64 ∨ w = 32) {as au ss su : Bool}
    {x y : Int w} : sub (add x y as au) x ss su ⊒ y := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `x - (y + x) → 0 - y`. The created `sub` must clear `nsw`/`nuw` rather than inherit the
    matched `sub`'s: `0 - y` has a different poison condition. Stated at both widths the guarded
    pattern admits, since the graph-level proof needs `i32` too.

    Keeping `nuw` would be unsound: `x = -1`, `y = 1`. Then `y + x = 0` and `x - 0 = -1`
    does not unsigned-overflow, but `0 - y` does. -/
theorem sub_add_reg_x_sub_y_add_x {w : Nat} (hw : w = 64 ∨ w = 32) {as au ss su : Bool}
    {x y : Int w} : sub x (add y x as au) ss su ⊒ sub (constant w 0) y false false := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `x - (x + y) → 0 - y`. The created `sub` must clear `nsw`/`nuw`, with the same
    counterexample as `sub_add_reg_x_sub_y_add_x`. -/
theorem sub_add_reg_x_sub_x_add_y {w : Nat} (hw : w = 64 ∨ w = 32) {as au ss su : Bool}
    {x y : Int w} : sub x (add x y as au) ss su ⊒ sub (constant w 0) y false false := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-! ### xor_of_and_with_same_reg -/

/-- `(x & y) ^ y → (~x) & y`. Stated at both widths the guarded pattern admits, since the
    graph-level proof needs `i32` too. -/
theorem xor_of_and_with_same_reg {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    xor (and x y) y ⊒ and (xor x (constant w (-1))) y := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-! ### select_to_iminmax

  `(icmp pred X Y) ? X : Y → {u,s}{max,min} X Y`. `select` is strict in its condition, and
  the condition is an `icmp` of both arms, so source and target are poison together.
-/

/-- `(X >u Y) ? X : Y → umax X Y`. -/
theorem select_to_iminmax_ugt {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    select (icmp x y .ugt) x y ⊒ umax x y := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `(X ≥u Y) ? X : Y → umax X Y`. -/
theorem select_to_iminmax_uge {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    select (icmp x y .uge) x y ⊒ umax x y := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `(X >s Y) ? X : Y → smax X Y`. -/
theorem select_to_iminmax_sgt {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    select (icmp x y .sgt) x y ⊒ smax x y := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `(X ≥s Y) ? X : Y → smax X Y`. -/
theorem select_to_iminmax_sge {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    select (icmp x y .sge) x y ⊒ smax x y := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `(X <u Y) ? X : Y → umin X Y`. -/
theorem select_to_iminmax_ult {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    select (icmp x y .ult) x y ⊒ umin x y := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `(X ≤u Y) ? X : Y → umin X Y`. -/
theorem select_to_iminmax_ule {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    select (icmp x y .ule) x y ⊒ umin x y := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `(X <s Y) ? X : Y → smin X Y`. -/
theorem select_to_iminmax_slt {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    select (icmp x y .slt) x y ⊒ smin x y := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `(X ≤s Y) ? X : Y → smin X Y`. -/
theorem select_to_iminmax_sle {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    select (icmp x y .sle) x y ⊒ smin x y := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-! ### cast_of_cast_combines -/

/-- `trunc (zext x) → x` when the `trunc` lands back on `x`'s type. Both casts' flags stay
    free: they can only poison the source, and `poison ⊒ x`. -/
theorem trunc_of_zext {n s u : Bool} {x : Int 32} :
    trunc (zext x 64 n h32_64) 32 s u h64_32 ⊒ x := by
  veir_bv_decide

/-! ### select_of_{zext,truncate} -/

/-- `zext (select c t f) → select c (zext t) (zext f)`. Sound with `nneg` free because
    `select` does not propagate poison from the arm it does not take: if the unselected
    `zext nneg` is poison, the `select` still returns the taken arm. -/
theorem select_of_zext_rw {n : Bool} {c : Int 1} {x y : Int 32} :
    zext (select c x y) 64 n h32_64 ⊒ select c (zext x 64 n h32_64) (zext y 64 n h32_64) := by
  veir_bv_decide

/-- `trunc (select c t f) → select c (trunc t) (trunc f)`. Same non-strictness argument. -/
theorem select_of_truncate_rw {s u : Bool} {c : Int 1} {x y : Int 64} :
    trunc (select c x y) 32 s u h64_32
      ⊒ select c (trunc x 32 s u h64_32) (trunc y 32 s u h64_32) := by
  veir_bv_decide

/-! ### add_shift -/

/-- `A + shl(0 - B, C) → A - shl(B, C)`. Both created ops must clear their flags: the new
    `shl` shifts `B` rather than `0 - B`, and the new `sub` computes `A - shl(B, C)` rather
    than the inner `0 - B` whose flags it would otherwise inherit.

    Keeping `nsw` on the `shl` would be unsound: `A = 0`, `B = 2^62`, `C = 1`.
    `shl nsw (0 - B) 1` is fine, but `shl nsw B 1` is poison. -/
theorem add_shift {as au ns nu ss su : Bool} {a b c : Int 64} :
    add a (shl (sub (constant 64 0) b ss su) c ns nu) as au
      ⊒ sub a (shl b c false false) false false := by
  veir_bv_decide

/-- `shl(0 - B, C) + A → A - shl(B, C)` (operands commuted). Both created ops clear their
    flags, as in `add_shift`. -/
theorem add_shift_commute {as au ns nu ss su : Bool} {a b c : Int 64} :
    add (shl (sub (constant 64 0) b ss su) c ns nu) a as au
      ⊒ sub a (shl b c false false) false false := by
  veir_bv_decide

/-! ### redundant_binop_in_equality

  `((X op Y) cmp X) → (Y cmp 0)` for `op ∈ {+, -, ^}` and `cmp ∈ {==, !=}`. The binop's
  flags are dropped, so they stay free.
-/

/-- `(X + Y) == X → Y == 0`. Stated at both widths the guarded pattern admits, since the
    graph-level proof needs `i32` too. -/
theorem redundant_binop_in_equality_XPlusYEqX {w : Nat} (hw : w = 64 ∨ w = 32)
    {s u : Bool} {x y : Int w} : icmp (add x y s u) x .eq ⊒ icmp y (constant w 0) .eq := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `(X + Y) != X → Y != 0`. -/
theorem redundant_binop_in_equality_XPlusYNeX {w : Nat} (hw : w = 64 ∨ w = 32)
    {s u : Bool} {x y : Int w} : icmp (add x y s u) x .ne ⊒ icmp y (constant w 0) .ne := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `(X - Y) == X → Y == 0`. -/
theorem redundant_binop_in_equality_XMinusYEqX {w : Nat} (hw : w = 64 ∨ w = 32)
    {s u : Bool} {x y : Int w} : icmp (sub x y s u) x .eq ⊒ icmp y (constant w 0) .eq := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `(X - Y) != X → Y != 0`. -/
theorem redundant_binop_in_equality_XMinusYNeX {w : Nat} (hw : w = 64 ∨ w = 32)
    {s u : Bool} {x y : Int w} : icmp (sub x y s u) x .ne ⊒ icmp y (constant w 0) .ne := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `(X ^ Y) == X → Y == 0`. -/
theorem redundant_binop_in_equality_XXorYEqX {w : Nat} (hw : w = 64 ∨ w = 32)
    {x y : Int w} : icmp (xor x y) x .eq ⊒ icmp y (constant w 0) .eq := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `(X ^ Y) != X → Y != 0`. -/
theorem redundant_binop_in_equality_XXorYNeX {w : Nat} (hw : w = 64 ∨ w = 32)
    {x y : Int w} : icmp (xor x y) x .ne ⊒ icmp y (constant w 0) .ne := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-! ### match_selects -/

/-- `select c, 1, 0 → zext c`. Stated at both widths the guarded pattern admits, since the
    graph-level proof needs `i32` too. -/
theorem select_1_0 {w : Nat} (hw : w = 64 ∨ w = 32) {c : Int 1} (hlt : 1 < w) :
    select c (constant w 1) (constant w 0) ⊒ zext c w false hlt := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `select c, -1, 0 → sext c`. -/
theorem select_neg1_0 {w : Nat} (hw : w = 64 ∨ w = 32) {c : Int 1} (hlt : 1 < w) :
    select c (constant w (-1)) (constant w 0) ⊒ sext c w hlt := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `select c, 0, 1 → zext (not c)`. Stated at both widths the guarded pattern admits, since the
    graph-level proof needs `i32` too. -/
theorem select_0_1 {w : Nat} (hw : w = 64 ∨ w = 32) {c : Int 1} (hlt : 1 < w) :
    select c (constant w 0) (constant w 1) ⊒ zext (xor c (constant 1 (-1))) w false hlt := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `select c, 0, -1 → sext (not c)`. -/
theorem select_0_neg1 {w : Nat} (hw : w = 64 ∨ w = 32) {c : Int 1} (hlt : 1 < w) :
    select c (constant w 0) (constant w (-1)) ⊒ sext (xor c (constant 1 (-1))) w hlt := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-! ### not_cmp_fold

  `(icmp pred X Y) ^ -1 → (icmp invPred X Y)`, at the `i1` result of the comparison.
-/

/-- `not (X == Y) → X != Y`. Stated at both widths the guarded pattern admits, since the
    graph-level proof needs `i32` too. -/
theorem not_cmp_fold_eq {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    xor (icmp x y .eq) (constant 1 (-1)) ⊒ icmp x y .ne := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `not (X != Y) → X == Y`. -/
theorem not_cmp_fold_ne {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    xor (icmp x y .ne) (constant 1 (-1)) ⊒ icmp x y .eq := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `not (X >u Y) → X ≤u Y`. -/
theorem not_cmp_fold_ugt {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    xor (icmp x y .ugt) (constant 1 (-1)) ⊒ icmp x y .ule := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `not (X ≥u Y) → X <u Y`. -/
theorem not_cmp_fold_uge {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    xor (icmp x y .uge) (constant 1 (-1)) ⊒ icmp x y .ult := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `not (X >s Y) → X ≤s Y`. -/
theorem not_cmp_fold_sgt {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    xor (icmp x y .sgt) (constant 1 (-1)) ⊒ icmp x y .sle := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `not (X ≥s Y) → X <s Y`. -/
theorem not_cmp_fold_sge {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    xor (icmp x y .sge) (constant 1 (-1)) ⊒ icmp x y .slt := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-! ### double_icmp_zero_combine -/

/-- `(X == 0) & (Y == 0) → (X | Y) == 0`. The created `or` is not `disjoint`. Stated at both
    widths the guarded pattern admits, since the graph-level proof needs `i32` too. -/
theorem double_icmp_zero_and_combine {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    and (icmp x (constant w 0) .eq) (icmp y (constant w 0) .eq)
      ⊒ icmp (or x y false) (constant w 0) .eq := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `(X != 0) | (Y != 0) → (X | Y) != 0`. The created `or` clears `disjoint` (the outer `i1`
    `or`'s flag `d` is free); making the created `or` never-poison only *increases* the target's
    definedness, so the refinement still holds. -/
theorem double_icmp_zero_or_combine {w : Nat} (hw : w = 64 ∨ w = 32) {d : Bool} {x y : Int w} :
    or (icmp x (constant w 0) .ne) (icmp y (constant w 0) .ne) d
      ⊒ icmp (or x y false) (constant w 0) .ne := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-! ### NotAPlusNegOne / sub_one_from_sub -/

/-- `not (X + -1) → 0 - X`, with the `add`'s flags carried onto the `sub`. Sound: at the
    constant `-1` the two ops have the same signed and unsigned overflow conditions
    (`X = intMin` and `X ≠ 0` respectively). Stated at both widths the guarded pattern admits,
    since the graph-level proof needs `i32` too. -/
theorem NotAPlusNegOne_rw {w : Nat} (hw : w = 64 ∨ w = 32) {s u : Bool} {x : Int w} :
    xor (add x (constant w (-1)) s u) (constant w (-1)) ⊒ sub (constant w 0) x s u := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `(A - B) - 1 → (~B) + A`. The created `add` must clear `nsw`/`nuw` rather than inherit
    the outer `sub`'s.

    Keeping `nuw` would be unsound: `A = 5`, `B = 3`. `(5 - 3) - 1 = 1` does not
    unsigned-overflow, but `add nuw (~3) 5` wraps. -/
theorem sub_one_from_sub_rw {w : Nat} (hw : w = 64 ∨ w = 32) {s2 u2 s u : Bool} {x y : Int w} :
    sub (sub x y s2 u2) (constant w 1) s u
      ⊒ add (xor y (constant w (-1))) x false false := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-! ### trivial selects -/

/-- `select c, x, x → x`. -/
theorem select_same_val_self {w : Nat} (hw : w = 64 ∨ w = 32) {c : Int 1} {x : Int w} :
    select c x x ⊒ x := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `select 1, x, y → x`. -/
theorem select_constant_cmp_true {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    select (constant 1 1) x y ⊒ x := by
  rcases hw with rfl | rfl <;> veir_bv_decide

/-- `select 0, x, y → y`. -/
theorem select_constant_cmp_false {w : Nat} (hw : w = 64 ∨ w = 32) {x y : Int w} :
    select (constant 1 0) x y ⊒ y := by
  rcases hw with rfl | rfl <;> veir_bv_decide

end Veir.Data.LLVM.Int
