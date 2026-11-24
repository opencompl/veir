define i32 @missing_predecessor(i1 %condition, i32 %x) {
entry:
  br i1 %condition, label %left, label %merge
left:
  br label %merge
merge:
  %result = phi i32 [ %x, %left ]
  ret i32 %result
}
