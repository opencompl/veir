; Use before definition inside one block. Not valid LLVM (no dominance).
define i32 @fwd(i32 %x) {
entry:
  %a = xor i32 %b, -1
  %b = and i32 %x, 1
  ret i32 %a
}
