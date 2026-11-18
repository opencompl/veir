define i8 @set_low(i8 %x) {
entry:
  %r = or i8 %x, 1
  ret i8 %r
}
