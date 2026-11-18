; One-bit integers with a literal.
define i1 @flip(i1 %b) {
entry:
  %r = xor i1 %b, 1
  ret i1 %r
}
