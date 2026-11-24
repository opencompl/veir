define i32 @toggle(i1 %done) {
entry:
  br label %loop
loop:
  %i = phi i32 [ 0, %entry ], [ %next, %loop ]
  %next = xor i32 %i, 1
  br i1 %done, label %exit, label %loop
exit:
  ret i32 %next
}
