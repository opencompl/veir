define i32 @choose(i1 %condition, i32 %x, i32 %y) {
entry:
  br i1 %condition, label %left, label %right
left:
  br label %merge
right:
  br label %merge
merge:
  %a = phi i32 [ %y, %right ], [ %x, %left ]
  %b = phi i32 [ %x, %right ], [ %y, %left ]
  %result = xor i32 %a, %b
  ret i32 %result
}
