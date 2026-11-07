// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// A zero-arm `g_select` on an equality `g_icmp` hands `czero.eqz`/`czero.nez` the difference of the
// `g_icmp` operands directly, as LLVM's `CondOpsPat` (`RISCVInstrInfoZicond.td`) does with
// `riscv_setne`/`riscv_seteq`: `(setcc x, 0)` is `x` and `(setcc x, y)` is `(xor x, y)`.

"builtin.module"() ({
  // select (icmp ne x, 0), t, 0 -> czero.eqz t, x
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "ne_zero_t"}> ({
  ^bb0(%x: i64, %t: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %c = "gmir.g_icmp"(%x, %zero) <{predicate = 1 : i64}> : (i64, i64) -> i64
    %r = "gmir.g_select"(%c, %t, %zero) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @ne_zero_t
  // CHECK-SAME:  (%[[X:.*]]: i64, %[[T:.*]]: i64)
  // CHECK-DAG:   %[[TR:.*]] = "builtin.unrealized_conversion_cast"(%[[T]])
  // CHECK-DAG:   %[[XR:.*]] = "builtin.unrealized_conversion_cast"(%[[X]])
  // CHECK:       "riscv.czeroeqz"(%[[TR]], %[[XR]])

  // select (icmp eq x, 0), t, 0 -> czero.nez t, x
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "eq_zero_t"}> ({
  ^bb0(%x: i64, %t: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %c = "gmir.g_icmp"(%x, %zero) <{predicate = 0 : i64}> : (i64, i64) -> i64
    %r = "gmir.g_select"(%c, %t, %zero) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @eq_zero_t
  // CHECK-SAME:  (%[[X:.*]]: i64, %[[T:.*]]: i64)
  // CHECK-DAG:   %[[TR:.*]] = "builtin.unrealized_conversion_cast"(%[[T]])
  // CHECK-DAG:   %[[XR:.*]] = "builtin.unrealized_conversion_cast"(%[[X]])
  // CHECK:       "riscv.czeronez"(%[[TR]], %[[XR]])

  // select (icmp ne x, 0), 0, f -> czero.nez f, x
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "ne_zero_f"}> ({
  ^bb0(%x: i64, %f: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %c = "gmir.g_icmp"(%x, %zero) <{predicate = 1 : i64}> : (i64, i64) -> i64
    %r = "gmir.g_select"(%c, %zero, %f) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @ne_zero_f
  // CHECK-SAME:  (%[[X:.*]]: i64, %[[F:.*]]: i64)
  // CHECK-DAG:   %[[FR:.*]] = "builtin.unrealized_conversion_cast"(%[[F]])
  // CHECK-DAG:   %[[XR:.*]] = "builtin.unrealized_conversion_cast"(%[[X]])
  // CHECK:       "riscv.czeronez"(%[[FR]], %[[XR]])

  // select (icmp eq x, 0), 0, f -> czero.eqz f, x
  "func.func"() <{function_type = (i64, i64) -> i64, sym_name = "eq_zero_f"}> ({
  ^bb0(%x: i64, %f: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %c = "gmir.g_icmp"(%x, %zero) <{predicate = 0 : i64}> : (i64, i64) -> i64
    %r = "gmir.g_select"(%c, %zero, %f) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @eq_zero_f
  // CHECK-SAME:  (%[[X:.*]]: i64, %[[F:.*]]: i64)
  // CHECK-DAG:   %[[FR:.*]] = "builtin.unrealized_conversion_cast"(%[[F]])
  // CHECK-DAG:   %[[XR:.*]] = "builtin.unrealized_conversion_cast"(%[[X]])
  // CHECK:       "riscv.czeroeqz"(%[[FR]], %[[XR]])

  // select (icmp ne x, y), t, 0 -> czero.eqz t, (xor x, y)
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "ne_t"}> ({
  ^bb0(%x: i64, %y: i64, %t: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %c = "gmir.g_icmp"(%x, %y) <{predicate = 1 : i64}> : (i64, i64) -> i64
    %r = "gmir.g_select"(%c, %t, %zero) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @ne_t
  // CHECK:       %[[D:.*]] = "riscv.xor"
  // CHECK:       "riscv.czeroeqz"(%{{.*}}, %[[D]])

  // select (icmp eq x, y), 0, f -> czero.eqz f, (xor x, y)
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "eq_f"}> ({
  ^bb0(%x: i64, %y: i64, %f: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %c = "gmir.g_icmp"(%x, %y) <{predicate = 0 : i64}> : (i64, i64) -> i64
    %r = "gmir.g_select"(%c, %zero, %f) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @eq_f
  // CHECK:       %[[D:.*]] = "riscv.xor"
  // CHECK:       "riscv.czeroeqz"(%{{.*}}, %[[D]])

  // Negative case: a relational `g_icmp` is still tested through its 0/1 result.
  "func.func"() <{function_type = (i64, i64, i64) -> i64, sym_name = "ult_t"}> ({
  ^bb0(%x: i64, %y: i64, %t: i64):
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    %c = "gmir.g_icmp"(%x, %y) <{predicate = 6 : i64}> : (i64, i64) -> i64
    %r = "gmir.g_select"(%c, %t, %zero) : (i64, i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: func.func @ult_t
  // CHECK:       %[[C:.*]] = "riscv.sltu"
  // CHECK:       %[[CC:.*]] = "builtin.unrealized_conversion_cast"(%[[C]])
  // CHECK:       %[[CR:.*]] = "builtin.unrealized_conversion_cast"(%[[CC]])
  // CHECK:       "riscv.czeroeqz"(%{{.*}}, %[[CR]])
}) : () -> ()
