// RUN: VEIR_ROUNDTRIP
// RUN: %if mlir-min-23 %{ MLIR_ROUNDTRIP %}

// The unsigned high half of the double-width product. Use odd integer widths
// as well as i1 and i13 to exercise the overloaded type.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i32, i32)>, sym_name = "scalar"}> ({
  ^bb0(%a: i32, %b: i32):
    %umulh = "llvm.intr.umulh"(%a, %b) : (i32, i32) -> i32
    // CHECK: "llvm.intr.umulh"({{.*}}) : (i32, i32) -> i32
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void (i1, i1)>, sym_name = "narrow"}> ({
  ^bb0(%a: i1, %b: i1):
    %umulh = "llvm.intr.umulh"(%a, %b) : (i1, i1) -> i1
    // CHECK: "llvm.intr.umulh"({{.*}}) : (i1, i1) -> i1
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void (i129, i129)>, sym_name = "wide"}> ({
  ^bb0(%a: i129, %b: i129):
    %umulh = "llvm.intr.umulh"(%a, %b) : (i129, i129) -> i129
    // CHECK: "llvm.intr.umulh"({{.*}}) : (i129, i129) -> i129
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<void (i13, i13)>, sym_name = "odd"}> ({
  ^bb0(%a: i13, %b: i13):
    %umulh = "llvm.intr.umulh"(%a, %b) : (i13, i13) -> i13
    // CHECK: "llvm.intr.umulh"({{.*}}) : (i13, i13) -> i13
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
