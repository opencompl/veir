// RUN: veir-opt %s --print-op-generic -p='apply-patterns{uadd_sat_nested_constants uadd_sat_nested_constants_to_max ctlz_bitreverse umin_cttz_cttz uadd_overflow_constant_flag ctpop_zext_narrow umax_nuw_add_dist_common_left}' | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "saturation", function_type = (i8) -> (i8, i8)}> ({
  ^bb0(%x: i8):
    %a = "llvm.mlir.constant"() <{value = 100 : i8}> : () -> i8
    %b = "llvm.mlir.constant"() <{value = 20 : i8}> : () -> i8
    %c = "llvm.mlir.constant"() <{value = -56 : i8}> : () -> i8
    %l = "llvm.intr.uadd.sat"(%x, %a) : (i8, i8) -> i8
    %r = "llvm.intr.uadd.sat"(%l, %b) : (i8, i8) -> i8
    %l2 = "llvm.intr.uadd.sat"(%x, %a) : (i8, i8) -> i8
    %r2 = "llvm.intr.uadd.sat"(%l2, %c) : (i8, i8) -> i8
    "func.return"(%r, %r2) : (i8, i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "saturation"
  // CHECK: "value" = 120 : i8
  // CHECK: %[[SAT:[0-9]+]] = "llvm.intr.uadd.sat"
  // CHECK: %[[MAX:[0-9]+]] = "llvm.mlir.constant"() <{"value" = -1 : i8}>
  // CHECK: "func.return"(%[[SAT]], %[[MAX]])

  // The LLVM immediate flags become operation properties, including OR when
  // two counts are combined. A zero-defined input must not silently become
  // zero-poison unless the source law permits it.
  "func.func"() <{sym_name = "count_flags", function_type = (i8, i8) -> (i8, i8)}> ({
  ^bb0(%x: i8, %y: i8):
    %rev = "llvm.intr.bitreverse"(%x) : (i8) -> i8
    %clz = "llvm.intr.ctlz"(%rev) <{is_zero_poison = false}> : (i8) -> i8
    %a = "llvm.intr.cttz"(%x) <{is_zero_poison = false}> : (i8) -> i8
    %b = "llvm.intr.cttz"(%y) <{is_zero_poison = true}> : (i8) -> i8
    %r = "llvm.intr.umin"(%b, %a) : (i8, i8) -> i8
    "func.return"(%clz, %r) : (i8, i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "count_flags"
  // CHECK-NOT: "llvm.intr.bitreverse"
  // CHECK: "llvm.intr.cttz"{{.*}}"is_zero_poison" = false
  // CHECK: "llvm.or"
  // CHECK: "llvm.intr.cttz"{{.*}}"is_zero_poison" = true
  // CHECK-NOT: "llvm.intr.umin"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "overflow_flag", function_type = (i8) -> i1}> ({
  ^bb0(%x: i8):
    %c = "llvm.mlir.constant"() <{value = 3 : i8}> : () -> i8
    %pair = "llvm.intr.uadd.with.overflow"(%x, %c) : (i8, i8) -> !llvm.struct<(i8, i1)>
    %flag = "llvm.extractvalue"(%pair) <{position = array<i64: 1>}> : (!llvm.struct<(i8, i1)>) -> i1
    "func.return"(%flag) : (i1) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "overflow_flag"
  // CHECK: "value" = -4 : i8
  // CHECK: "llvm.icmp"{{.*}}"predicate" = 8 : i64
  // CHECK-NOT: "llvm.extractvalue"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "shared_overflow_tuple", function_type = (i8) -> (i8, i1)}> ({
  ^bb0(%x: i8):
    %c = "llvm.mlir.constant"() <{value = 3 : i8}> : () -> i8
    %pair = "llvm.intr.uadd.with.overflow"(%x, %c) : (i8, i8) -> !llvm.struct<(i8, i1)>
    %sum = "llvm.extractvalue"(%pair) <{position = array<i64: 0>}> : (!llvm.struct<(i8, i1)>) -> i8
    %flag = "llvm.extractvalue"(%pair) <{position = array<i64: 1>}> : (!llvm.struct<(i8, i1)>) -> i1
    "func.return"(%sum, %flag) : (i8, i1) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "shared_overflow_tuple"
  // CHECK: "llvm.intr.uadd.with.overflow"
  // CHECK: "llvm.extractvalue"
  // CHECK: "llvm.extractvalue"

  "func.func"() <{sym_name = "narrow_count", function_type = (i3) -> i8}> ({
  ^bb0(%x: i3):
    %ext = "llvm.zext"(%x) : (i3) -> i8
    %r = "llvm.intr.ctpop"(%ext) : (i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "narrow_count"
  // CHECK: "llvm.intr.ctpop"{{.*}} : (i3) -> i3
  // CHECK: "llvm.zext"{{.*}} : (i3) -> i8

  // Only common flags may survive the factored add.
  "func.func"() <{sym_name = "flag_intersection", function_type = (i8, i8, i8) -> i8}> ({
  ^bb0(%common: i8, %x: i8, %y: i8):
    %a = "llvm.add"(%x, %common) <{overflowFlags = 3 : i32}> : (i8, i8) -> i8
    %b = "llvm.add"(%common, %y) <{overflowFlags = 2 : i32}> : (i8, i8) -> i8
    %r = "llvm.intr.umax"(%b, %a) : (i8, i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "flag_intersection"
  // CHECK: "llvm.intr.umax"
  // CHECK: "llvm.add"{{.*}}"overflowFlags" = 2 : i32
  // CHECK-NOT: "llvm.add"
  // CHECK: "func.return"
}) : () -> ()
