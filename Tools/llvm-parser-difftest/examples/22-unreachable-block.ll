; A second, unreachable block. Valid LLVM, but more than one block.
define i32 @two_blocks(i32 %x) {
entry:
  ret i32 %x
dead:
  %r = xor i32 %x, -1
  ret i32 %r
}
