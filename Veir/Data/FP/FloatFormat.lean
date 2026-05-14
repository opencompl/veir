module

namespace Veir.Data.FP.FloatFormat

public section

/-! # IEEE-754 floating-point format computations

A consolidated namespace for the integer/`BitVec` arithmetic that
describes an IEEE-754 binary format with `e` exponent bits and `s`
trailing-significand bits. Eventually this will become a structure
`FloatFormat` bundling `e` and `s`; for now, each helper takes them
as explicit arguments.

This module currently exposes only the format constants that exist
elsewhere in the codebase. Encoding/decoding arithmetic
(`unbiasedExp`, `biasedExp`, shift helpers, …) will be added here as
the corresponding callers land.
-/

/--
The IEEE-754 exponent bias for `e` exponent bits: `bias e = 2^(e-1) - 1`.

A stored biased exponent `ex` encodes the unbiased exponent `ex - bias e`.
The bias is chosen so the unbiased exponent range is roughly symmetric
around `0`.

For single precision (`e = 8`),  `bias = 127`.
For double precision (`e = 11`), `bias = 1023`.
-/
def bias (e : Nat) : Nat := 2 ^ (e - 1) - 1

-- Single precision: `bias 8 = 2^7 - 1 = 127`.
#guard bias 8 = 127
-- Double precision: `bias 11 = 2^10 - 1 = 1023`.
#guard bias 11 = 1023

end -- public section

end Veir.Data.FP.FloatFormat
