; A literal that does not fit in i8.
define i8 @overflow(i8 %x) {
entry:
  %r = and i8 %x, 300
  ret i8 %r
}
