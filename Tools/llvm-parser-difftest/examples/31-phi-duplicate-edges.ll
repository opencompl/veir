define i8 @duplicate(i1 %c) {
entry:
  br i1 %c, label %merge, label %merge
merge:
  %result = phi i8 [ -1, %entry ], [ 255, %entry ]
  ret i8 %result
}
