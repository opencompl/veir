module

namespace Veir.Data.FP

/--
Treat a boolean as a sign,
where `true` corresponds to `-1` and `false` corresponds to `1`.
-/
public def signToInt (s : Bool) : Rat :=
  if s then -1 else 1
