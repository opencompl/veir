module

public import Lean

namespace QPFTypes
open Lean

/-! # Meta Utilities -/

/-- Not sure why upstream doesn't define this instance -/
public instance : ToMessageData (FVarId) where
  toMessageData x := toMessageData (Expr.fvar x)
