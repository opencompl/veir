; Literal on the left-hand side.
define i32 @lhs(i32 %x) {
entry:
  %r = and i32 255, %x
  ret i32 %r
}
