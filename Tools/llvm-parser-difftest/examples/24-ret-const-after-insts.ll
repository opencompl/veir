; Return a literal although instructions precede it.
define i32 @ignored(i32 %x) {
entry:
  %a = and i32 %x, 3
  ret i32 3
}
