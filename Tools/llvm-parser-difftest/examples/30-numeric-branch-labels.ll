define i32 @numbered(i32 %0) {
1:
  br i1 false, label %2, label %3
2:
  br label %3
3:
  %4 = phi i32 [ %0, %1 ], [ 17, %2 ]
  ret i32 %4
}
