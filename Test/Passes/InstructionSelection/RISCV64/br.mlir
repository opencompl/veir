// RUN: veir-opt %s -p=isel-br-riscv64 | filecheck %s

"builtin.module"() ({
    "func.func"()  <{"function_type" = (i64) -> (i64), "sym_name" = "a"}> ({
    ^bb0(%a: i64):
        "llvm.br"(%a) [^bb1] : (i64) -> ()

    ^bb1(%b: i64):
        "func.return"(%b) : (i64) -> ()
    }) : () -> ()

    "func.func"()  <{"function_type" = (i64, i1) -> (i64), "sym_name" = "b"}> ({
    ^bb0(%a: i64, %b: i1):
        "llvm.cond_br"(%b, %a, %a) [^bb1, ^bb2] <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()

    ^bb1(%c: i64):
        "func.return"(%c) : (i64) -> ()

    ^bb2(%d: i64):

        "func.return"(%d) : (i64) -> ()
    }) : () -> ()

    "func.func"()  <{function_type = (i64, i1) -> (i64), "sym_name" = "c"}> ({
    ^bb0(%a: i64, %b: i1):
        "llvm.cond_br"(%b, %a, %a) [^bb1, ^bb2] <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()

    ^bb1(%c: i64):
        "llvm.br"(%c) [^bb3] : (i64) -> ()

    ^bb2(%d: i64):
        "llvm.br"(%d) [^bb3]: (i64) -> ()

    ^bb3(%e: i64):
        "func.return"(%e) : (i64) -> ()
    }) : () -> ()

    "func.func"() <{"function_type" = (i32, i64) -> (i32), "sym_name" = "block_arg"}> ({
    ^bb0(%a: i32, %n: i64):
        "llvm.br"(%a) [^bb1] : (i32) -> ()

    ^bb1(%b: i32):
        %c = "llvm.add"(%b, %b) : (i32, i32) -> i32
        "func.return"(%c) : (i32) -> ()
    }) : () -> ()
}) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i64) -> i64, "sym_name" = "a"}> ({
// CHECK-NEXT:   ^6([[AA:%[a-z0-9_]+]] : i64):
// CHECK-NEXT:     [[RA:%[a-z0-9]+]] = "builtin.unrealized_conversion_cast"([[AA]]) : (i64) -> !riscv.reg
// CHECK-NEXT:     "riscv_cf.branch"([[RA]]) [^7] : (!riscv.reg) -> ()
// CHECK-NEXT:   ^7([[AB:%[a-z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:     [[RB:%[a-z0-9]+]] = "builtin.unrealized_conversion_cast"([[AB]]) : (!riscv.reg) -> i64
// CHECK-NEXT:     "func.return"([[RB]]) : (i64) -> ()
// CHECK-NEXT: }) : () -> ()
 
// CHECK:      "func.func"() <{"function_type" = (i64, i1) -> i64, "sym_name" = "b"}> ({
// CHECK-NEXT:   ^12([[AA:%[a-z0-9_]+]] : i64, [[AB:%[a-z0-9_]+]] : i1):
// CHECK-NEXT:     [[CA:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[AB]]) : (i1) -> !riscv.reg
// CHECK-NEXT:     [[CB:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[AA]]) : (i64) -> !riscv.reg
// CHECK-NEXT:     [[CC:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[AA]]) : (i64) -> !riscv.reg
// CHECK-NEXT:     "riscv_cf.bnez"([[CA]], [[CB]], [[CC]]) [^13, ^14] <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:   ^13(%arg13_0 : !riscv.reg):
// CHECK-NEXT:     [[CD:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"(%arg13_0) : (!riscv.reg) -> i64
// CHECK-NEXT:     "func.return"([[CD]]) : (i64) -> ()
// CHECK-NEXT:   ^14(%arg14_0 : !riscv.reg):
// CHECK-NEXT:     [[CE:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"(%arg14_0) : (!riscv.reg) -> i64
// CHECK-NEXT:     "func.return"([[CE]]) : (i64) -> ()
// CHECK-NEXT: }) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i64, i1) -> i64, "sym_name" = "c"}> ({
// CHECK-NEXT:   ^20(%arg20_0 : i64, %arg20_1 : i1):
// CHECK-NEXT:     [[CA:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"(%arg20_1) : (i1) -> !riscv.reg
// CHECK-NEXT:     [[CB:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"(%arg20_0) : (i64) -> !riscv.reg
// CHECK-NEXT:     [[CC:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"(%arg20_0) : (i64) -> !riscv.reg
// CHECK-NEXT:     "riscv_cf.bnez"([[CA]], [[CB]], [[CC]]) [^21, ^22] <{"operandSegmentSizes" = array<i32: 1, 1, 1>}> : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:   ^21(%arg21_0 : !riscv.reg):
// CHECK-NEXT:     [[CD:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"(%arg21_0) : (!riscv.reg) -> i64
// CHECK-NEXT:     [[CE:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[CD]]) : (i64) -> !riscv.reg
// CHECK-NEXT:     "riscv_cf.branch"([[CE]]) [^24] : (!riscv.reg) -> ()
// CHECK-NEXT:   ^22(%arg22_0 : !riscv.reg):
// CHECK-NEXT:     [[CF:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"(%arg22_0) : (!riscv.reg) -> i64
// CHECK-NEXT:     [[CG:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"([[CF]]) : (i64) -> !riscv.reg
// CHECK-NEXT:     "riscv_cf.branch"([[CG]]) [^24] : (!riscv.reg) -> ()
// CHECK-NEXT:   ^24(%arg24_0 : !riscv.reg):
// CHECK-NEXT:     [[CH:%[a-z0-9_]+]] = "builtin.unrealized_conversion_cast"(%arg24_0) : (!riscv.reg) -> i64
// CHECK-NEXT:     "func.return"([[CH]]) : (i64) -> ()
// CHECK-NEXT: }) : () -> ()

// CHECK:      "func.func"() <{"function_type" = (i32, i64) -> i32, "sym_name" = "block_arg"}> ({
// CHECK-NEXT:   ^{{[0-9]+}}([[A:%[a-z0-9_]+]] : i32, %{{[a-z0-9_]+}} : i64):
// CHECK-NEXT:     [[RA:%[a-z0-9]+]] = "builtin.unrealized_conversion_cast"([[A]]) : (i32) -> !riscv.reg
// CHECK-NEXT:     "riscv_cf.branch"([[RA]]) [^[[BB1:[0-9]+]]] : (!riscv.reg) -> ()
// CHECK-NEXT:   ^[[BB1]]([[B:%[a-z0-9_]+]] : !riscv.reg):
// CHECK-NEXT:     [[RB:%[a-z0-9]+]] = "builtin.unrealized_conversion_cast"([[B]]) : (!riscv.reg) -> i32
// CHECK-NEXT:     [[ADD:%[a-z0-9]+]] = "llvm.add"([[RB]], [[RB]]) : (i32, i32) -> i32
// CHECK-NEXT:     "func.return"([[ADD]]) : (i32) -> ()
// CHECK-NEXT: }) : () -> ()
