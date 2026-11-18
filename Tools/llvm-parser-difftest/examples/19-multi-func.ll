; Several functions of different widths.
define i8 @f8(i8 %x) {
entry:
  %r = xor i8 %x, -1
  ret i8 %r
}

define i16 @f16(i16 %x) {
entry:
  %r = xor i16 %x, -1
  ret i16 %r
}

define i32 @f32() {
entry:
  ret i32 0
}
