; A longer dependence chain.
define i32 @chain(i32 %a, i32 %b, i32 %c, i32 %d) {
entry:
  %t0 = xor i32 %a, %b
  %t1 = and i32 %t0, %c
  %t2 = or i32 %t1, %d
  %t3 = xor i32 %t2, %t0
  %t4 = and i32 %t3, %t1
  %t5 = or i32 %t4, %t2
  ret i32 %t5
}
