module

namespace Veir.Data.FP

public section

/--
A plain enumeration of the possible states of a floating point value.
We define this separately to enable bitblasting the state of a FP value,
and to enable a shared representation of the FP state across 
packed/unpacked representations.
-/
inductive State
/-- A zero floating point value. -/
| zero
/-- A finite subnormal value. -/
| subnormal
/-- A finite normal value. -/
| normal
/-- An infinite value. -/
| infinite
/-- A not a number (NaN) value. -/
| nan

