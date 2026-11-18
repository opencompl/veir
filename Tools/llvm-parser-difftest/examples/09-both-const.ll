; Both operands are literals; the textual parser does not fold.
define i32 @fold() {
entry:
  %r = xor i32 1, 2
  ret i32 %r
}
