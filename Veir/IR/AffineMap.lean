module

/-!
  # Affine maps

  This file defines `AffineMapAttr`, the builtin `affine_map<...>` attribute, which
  maps a list of dimensions to a list of affine expressions, e.g.
  `affine_map<(d0, d1) -> (d1, 0)>`.

  Only a subset of MLIR affine maps is supported: results are either dimensions or
  integer constants. Symbols (`[s0]`) and compound expressions (`+`, `-`, `*`,
  `floordiv`, `ceildiv`, `mod`) are not yet supported.
-/

namespace Veir
public section

/--
  An affine expression over `n` dimensions, either the dimension `d<i>` or an
  integer constant.
-/
inductive AffineExpr (n : Nat) where
/-- The dimension `d<i>`. -/
| dim (i : Fin n)
/-- An integer constant. -/
| const (c : Int)
deriving Repr, DecidableEq, Hashable

instance : Inhabited (AffineExpr n) where
  default := .const default

instance : ToString (AffineExpr n) where
  toString
    | .dim i => s!"d{i}"
    | .const c => ToString.toString c

/--
  A builtin affine map attribute, mapping `numDims` dimensions to the affine
  expressions in `results`. For example, `affine_map<(d0, d1) -> (d1, 0)>` is
  represented by `numDims := 2` and `results := #[.dim 1, .const 0]`.
-/
structure AffineMapAttr where
  numDims : Nat
  results : Array (AffineExpr numDims)
deriving Repr, DecidableEq, Hashable

instance : Inhabited AffineMapAttr where
  default := ⟨0, #[]⟩

/-- Print an affine map in MLIR's canonical form, naming the dimensions `d0, d1, ...`. -/
instance : ToString AffineMapAttr where
  toString attr :=
    let dims := String.intercalate ", " ((List.range attr.numDims).map (s!"d{·}"))
    let results := String.intercalate ", " (attr.results.toList.map ToString.toString)
    s!"affine_map<({dims}) -> ({results})>"

end
end Veir
