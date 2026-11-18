; De Morgan's laws, written without applying the simplification.
define i32 @demorgan_or(i32 %p, i32 %q) {
entry:
  %not_p = xor i32 %p, -1
  %not_q = xor i32 %q, -1
  %both_not = and i32 %not_p, %not_q
  %result = xor i32 %both_not, -1
  ret i32 %result
}

define i32 @demorgan_and(i32 %p, i32 %q) {
entry:
  %not_p = xor i32 %p, -1
  %not_q = xor i32 %q, -1
  %either_not = or i32 %not_p, %not_q
  %result = xor i32 %either_not, -1
  ret i32 %result
}
