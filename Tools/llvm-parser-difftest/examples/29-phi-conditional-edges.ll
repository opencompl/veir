define i32 @conditional_edges(i1 %condition, i32 %x, i32 %y) {
entry:
  br i1 %condition, label %left, label %right
left:
  %a = phi i32 [ %x, %entry ], [ %combined, %right ]
  ret i32 %a
right:
  %b = phi i32 [ %y, %entry ]
  %c = phi i32 [ %x, %entry ]
  %combined = xor i32 %b, %c
  br label %left
}
