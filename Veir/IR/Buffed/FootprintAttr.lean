module

public import Veir.PrePrelude

public section

/-- Grind rule set for the raw-accessor footprint lemmas: rewrites of `read*!`/`write*` to the
`Nat`-indexed `ExArray` shadow operations, plus the shadow read-after-write lemmas. This set is
deliberately frozen — read/write product lemmas must never be added to it. -/
register_grind_attr footprint_grind
