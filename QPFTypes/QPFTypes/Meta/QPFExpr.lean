module

public import QPFTypes.Meta.QPFExpr.FinTuple
public import QPFTypes.Meta.QPFExpr.Basic
public import QPFTypes.Meta.QPFExpr.AddDecl

/-!
# QPFExpr

Main definitions:
  * `QPFExpr u n`, the type of Lean expressions of an `n`-ary type function,
    with correponding QPF instances.
  * `QPFExpr.addDecl`, add a type function and its corresponding QPF instance
    to the environment, in both curried and uncurried forms.
-/
