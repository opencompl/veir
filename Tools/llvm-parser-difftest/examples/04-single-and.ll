define i64 @mask(i64 %x, i64 %y) {
entry:
  %r = and i64 %x, %y
  ret i64 %r
}
