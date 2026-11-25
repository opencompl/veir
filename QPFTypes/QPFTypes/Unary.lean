module

public import QPFTypes.Theory.PFunctor.Multivariate.M.Order
public import QPFTypes.Theory.QPF.Cofix.Basic

@[expose] public section

namespace QPFTypes.Unary

/-- A unary type function is a QPF when its uncurried form is a multivariate QPF. -/
abbrev QPF (F : Type u → Type u) := QPFTypes.QPF (@TypeFun.ofCurried 1 F)

/-- The greatest fixed point of a unary QPF. -/
abbrev Cofix (F : Type u → Type u) [QPF F] : Type u :=
  QPFTypes.QPF.Cofix (@TypeFun.ofCurried 1 F) TypeVec.nil

/-- A choice of bottom shape in `F PUnit` for a unary type function. -/
abbrev HasBot (F : Type u → Type u) :=
  QPFTypes.HasBot (@TypeFun.ofCurried 1 F) TypeVec.nil

end QPFTypes.Unary
