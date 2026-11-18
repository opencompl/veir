define i64 @minval(i64 %x) {
entry:
  %r = or i64 %x, -9223372036854775808
  ret i64 %r
}
