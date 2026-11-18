; Block label other than `entry`.
define i32 @start_label(i32 %x) {
start:
  %r = and i32 %x, 7
  ret i32 %r
}
