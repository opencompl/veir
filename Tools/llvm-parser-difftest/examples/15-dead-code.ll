; An unused instruction.
define i32 @dead(i32 %x, i32 %y) {
entry:
  %unused = and i32 %x, %y
  %r = or i32 %x, %y
  ret i32 %r
}
