// RUN: veir-opt %s -p=reconcile-cast | filecheck %s

"builtin.module"() ({
  ^1():
  "func.func"() ({
    ^bb1(%0 : i64):
      %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i64
      
      "test.test"(%1) : (i64) -> ()
      
  }) : () -> ()
  // CHECK: "test.test"(%{{.*}}) : (i64) -> ()

  // ^2():
  // "func.func"() ({
  //   ^bb1(%0 : i64):
  //     %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i32
  //     "test.test"(%1) : (i32) -> ()
   //   // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> i32
    //  // CHECK-NEXT: "test.test"(%{{.*}}) : (i32) -> ()
      
  // }) : () -> ()
  

//   ^3():
//   "func.func"() ({
//     ^bb1(%0 : i64):
//       %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i32
//       %2 = "builtin.unrealized_conversion_cast"(%1) : (i32) -> i64
//       "test.test"(%2) : (i64) -> ()
//   }) : () -> ()
// // ============================================================
// // 4. ROUND-TRIP with intermediate use: intermediate cast must survive
// // ============================================================
// // CHECK-LABEL: "func.func"
// // CHECK: "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> i32
// // CHECK: "test.test"(%{{.*}}) : (i32) -> ()
// // CHECK: "test.test"(%{{.*}}) : (i64) -> ()
//   ^4():
//   "func.func"() ({
//     ^bb1(%0 : i64):
//       %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i32
//       "test.test"(%1) : (i32) -> ()
//       %2 = "builtin.unrealized_conversion_cast"(%1) : (i32) -> i64
//       "test.test"(%2) : (i64) -> ()
//   }) : () -> ()
// // ============================================================
// // 5. CHAIN OF THREE: A -> B -> C -> A (only the last folds)
// // ============================================================
// // CHECK-LABEL: "func.func"
// // CHECK: "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> i32
// // CHECK: "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> i8
// // CHECK-NOT: "builtin.unrealized_conversion_cast"(%{{.*}}) : (i8) -> i64
// // CHECK: "test.test"(%{{.*}}) : (i64) -> ()
//   ^5():
//   "func.func"() ({
//     ^bb1(%0 : i64):
//       %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i32
//       %2 = "builtin.unrealized_conversion_cast"(%1) : (i32) -> i8
//       %3 = "builtin.unrealized_conversion_cast"(%2) : (i8) -> i64
//       "test.test"(%3) : (i64) -> ()
//   }) : () -> ()
// // ============================================================
// // 6. MULTIPLE ROUND-TRIPS in the same block: both fold
// // ============================================================
// // CHECK-LABEL: "func.func"
// // CHECK: "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> i32
// // CHECK: "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> i8
// // CHECK-NOT: "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> i64
// // CHECK-NOT: "builtin.unrealized_conversion_cast"(%{{.*}}) : (i8) -> i64
// // CHECK: "test.test"(%{{.*}}) : (i64) -> ()
// // CHECK: "test.test"(%{{.*}}) : (i64) -> ()
//   ^6():
//   "func.func"() ({
//     ^bb1(%0 : i64):
//       %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i32
//       %2 = "builtin.unrealized_conversion_cast"(%1) : (i32) -> i64
//       %3 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i8
//       %4 = "builtin.unrealized_conversion_cast"(%3) : (i8) -> i64
//       "test.test"(%2) : (i64) -> ()
//       "test.test"(%4) : (i64) -> ()
//   }) : () -> ()
// // ============================================================
// // 7. NO CASTS: nothing changes
// // ============================================================
// // CHECK-LABEL: "func.func"
// // CHECK: "test.test"(%{{.*}}) : (i64) -> ()
// // CHECK: "test.test"(%{{.*}}) : (i64) -> ()
//   ^7():
//   "func.func"() ({
//     ^bb1(%0 : i64):
//       "test.test"(%0) : (i64) -> ()
//       "test.test"(%0) : (i64) -> ()
//   }) : () -> ()
// // ============================================================
// // 8. BLOCK ARGUMENT type matches: identity cast on block arg
// // ============================================================
// // CHECK-LABEL: "func.func"
// // CHECK-NOT: "builtin.unrealized_conversion_cast"
// // CHECK: "test.test"(%{{.*}}) : (i32) -> ()
//   ^8():
//   "func.func"() ({
//     ^bb1(%0 : i32):
//       %1 = "builtin.unrealized_conversion_cast"(%0) : (i32) -> i32
//       "test.test"(%1) : (i32) -> ()
//   }) : () -> ()
// // ============================================================
// // 9. MULTIPLE USES of a round-trip result: all replaced
// // ============================================================
// // CHECK-LABEL: "func.func"
// // CHECK: "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> i32
// // CHECK-NOT: "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> i64
// // CHECK: "test.test"(%{{.*}}) : (i64) -> ()
// // CHECK: "test.test"(%{{.*}}) : (i64) -> ()
// // CHECK: "test.test"(%{{.*}}) : (i64) -> ()
//   ^9():
//   "func.func"() ({
//     ^bb1(%0 : i64):
//       %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i32
//       %2 = "builtin.unrealized_conversion_cast"(%1) : (i32) -> i64
//       "test.test"(%2) : (i64) -> ()
//       "test.test"(%2) : (i64) -> ()
//       "test.test"(%2) : (i64) -> ()
//   }) : () -> ()
}) : () -> ()