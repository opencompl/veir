import Veir.Dialects.Builtin.Properties

open Veir

-- Exercise directly constructed attributes, bypassing the parser's validation.
private def readI64 (value : Int) : Except String (BitVec 64) :=
  getI64Attr "test" "value" (Std.HashMap.ofArray
    #[("value".toUTF8, .integerAttr (IntegerAttr.mk value (IntegerType.mk 64)))])

#guard readI64 (2 ^ 64) =
  .error "test: 'value' value 18446744073709551616 does not fit in i64"
#guard readI64 (-(2 ^ 63) - 1) =
  .error "test: 'value' value -9223372036854775809 does not fit in i64"
#guard readI64 (-(2 ^ 63)) = .ok 0x8000000000000000
#guard readI64 (2 ^ 64 - 1) = .ok 0xffffffffffffffff
#guard readI64 0 = .ok 0
