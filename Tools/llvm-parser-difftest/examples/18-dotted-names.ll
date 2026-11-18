; Value names with dots, dashes and dollar signs.
define i32 @dotted(i32 %x.in, i32 %y-in) {
entry:
  %tmp.0 = xor i32 %x.in, %y-in
  %$r = and i32 %tmp.0, %x.in
  ret i32 %$r
}
