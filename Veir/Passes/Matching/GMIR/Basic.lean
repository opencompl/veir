module

public import Veir.Passes.Legalization.LegalizerInfo
public import Veir.PatternRewriter.Puddle.Builders

public section

/-! This file contains Puddle matcher fragments for legal GMIR operations. -/

namespace Veir

/--
Puddle matcher for a legal `GMIR.g_add`  according to `info`.
-/
def matchLegalGAdd (info : LegalizerInfo) :
    Puddle.MatchProg.Builder
      (Puddle.Handle OpCode .type × Puddle.Handle OpCode .value × Puddle.Handle OpCode .value) := do
  let type ← Puddle.MatchProg.type (Attr := TypeAttr)
  let lhs ← Puddle.MatchProg.value type
  let rhs ← Puddle.MatchProg.value type
  let _ ← Puddle.MatchProg.root (.gmir .g_add) #[lhs, rhs] #[type]
  Puddle.MatchProg.matchNative type fun type => info.isLegal .g_add #[type]
  return (type, lhs, rhs)

end Veir
