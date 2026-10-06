module

public import QPFTypes.Meta.QPFExpr.FinTuple
public import QPFTypes.Meta.QPFExpr.Basic
public import QPFTypes.Meta.QPFExpr.AddDecl
public import QPFTypes.Meta.QPFExpr.OfTypeExpr

/-!
# QPFExpr

Main definitions:
  * `QPFExpr u n`, the type of Lean expressions of an `n`-ary type function,
    bundled with a corresponding QPF instance.
  * `QPFTupleExpr u n m`, the type of Lean expressions of an `m`-tuple of
    `n`-ary type functions, with corresponding QPF instances.
  * `QPFExpr.addDecl`, add a type function and its corresponding QPF instance
    to the environment, in both curried and uncurried forms.
  * `QPFExpr.ofTypeExpr`, build a QPFExpr given a Lean expression,
    of type `Type u`, and an array of (live) free variables over which to abstract.
-/
