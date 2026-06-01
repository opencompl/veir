module

namespace Veir.Data.FP

public section

/-- IEEE-754 rounding modes. -/
inductive RoundingMode
  /-- Round to nearest, tie away from zero. -/
  | RNA
  /-- Round to nearest, tie to even (default IEEE-754 mode). -/
  | RNE
  /-- Round toward negative infinity. -/
  | RTN
  /-- Round toward positive infinity. -/
  | RTP
  /-- Round toward zero. -/
  | RTZ
  deriving DecidableEq, Repr

end -- public section

end Veir.Data.FP
