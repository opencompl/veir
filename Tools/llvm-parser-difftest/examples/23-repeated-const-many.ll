; The same literal used many times.
define i32 @repeat(i32 %x) {
entry:
  %a = xor i32 %x, 5
  %b = and i32 %a, 5
  %c = or i32 %b, 5
  %d = xor i32 %c, 5
  ret i32 %d
}
