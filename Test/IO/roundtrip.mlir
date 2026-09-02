// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
    "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
        %r = "io.rand"() : () -> !llvm.array<32 x i8>
        "io.send"(%r) : (!llvm.array<32 x i8>) -> ()
        %msg = "io.recv"() : () -> !llvm.array<8 x i8>
        "io.send"(%msg) : (!llvm.array<8 x i8>) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     "func.func"() <{"function_type" = () -> (), "sym_name" = "main"}> ({
// CHECK-NEXT:       ^{{.*}}():
// CHECK-NEXT:         %[[r:.*]] = "io.rand"() : () -> !llvm.array<32 x i8>
// CHECK-NEXT:         "io.send"(%[[r]]) : (!llvm.array<32 x i8>) -> ()
// CHECK-NEXT:         %[[msg:.*]] = "io.recv"() : () -> !llvm.array<8 x i8>
// CHECK-NEXT:         "io.send"(%[[msg]]) : (!llvm.array<8 x i8>) -> ()
// CHECK-NEXT:         "func.return"() : () -> ()
