define i16 @two(i16 %x) {
entry:
  %a = and i16 %x, 15
  %b = or i16 %a, 256
  ret i16 %b
}
