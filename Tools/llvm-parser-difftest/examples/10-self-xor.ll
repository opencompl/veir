define i32 @zero(i32 %x) {
entry:
  %r = xor i32 %x, %x
  ret i32 %r
}
