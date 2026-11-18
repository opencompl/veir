define i32 @not(i32 %x) {
entry:
  %r = xor i32 %x, -1
  ret i32 %r
}
