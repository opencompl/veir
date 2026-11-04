"builtin.module"() ({
  "test.test"(%later#1, %later#0) : (i32, i64) -> ()
  %later:2 = "test.test"() : () -> (i64, i32)
}) : () -> ()
