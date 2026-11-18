; A literal larger than 64 bits.
define i128 @wide(i128 %x) {
entry:
  %r = xor i128 %x, 340282366920938463463374607431768211455
  ret i128 %r
}
