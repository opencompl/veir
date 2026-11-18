define i7 @odd(i7 %x, i7 %y) {
entry:
  %a = and i7 %x, %y
  %b = or i7 %a, 3
  ret i7 %b
}
