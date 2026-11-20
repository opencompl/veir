// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i1, i1, i1, i1, i1, i1, i1, i1, i1, i1)}> ({
    %seven = "llvm.mlir.constant"() <{ value = 7 : i8 }> : () -> i8
    %nine = "llvm.mlir.constant"() <{ value = 9 : i8 }> : () -> i8
    %x = "gmir.g_icmp"(%seven, %nine) <{ predicate = 0 : i64 }> : (i8, i8) -> i1
    %y = "gmir.g_icmp"(%seven, %nine) <{ predicate = 1 : i64 }> : (i8, i8) -> i1
    %z = "gmir.g_icmp"(%seven, %nine) <{ predicate = 2 : i64 }> : (i8, i8) -> i1
    %w = "gmir.g_icmp"(%seven, %nine) <{ predicate = 3 : i64 }> : (i8, i8) -> i1
    %v = "gmir.g_icmp"(%seven, %nine) <{ predicate = 4 : i64 }> : (i8, i8) -> i1
    %u = "gmir.g_icmp"(%seven, %nine) <{ predicate = 5 : i64 }> : (i8, i8) -> i1
    %s = "gmir.g_icmp"(%seven, %nine) <{ predicate = 6 : i64 }> : (i8, i8) -> i1
    %p = "gmir.g_icmp"(%seven, %nine) <{ predicate = 7 : i64 }> : (i8, i8) -> i1
    %q = "gmir.g_icmp"(%seven, %nine) <{ predicate = 8 : i64 }> : (i8, i8) -> i1
    %r = "gmir.g_icmp"(%seven, %nine) <{ predicate = 9 : i64 }> : (i8, i8) -> i1
    "func.return"(%x, %y, %z, %w, %v, %u, %s, %p, %q, %r) : (i1, i1, i1, i1, i1, i1, i1, i1, i1, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0#1, 0x1#1, 0x1#1, 0x1#1, 0x0#1, 0x0#1, 0x1#1, 0x1#1, 0x0#1, 0x0#1]
