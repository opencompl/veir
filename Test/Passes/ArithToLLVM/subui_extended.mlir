// RUN: veir-opt %s -p=arith-to-llvm > %t && veir-interpret %t | filecheck %s --check-prefix=EXEC
// RUN: filecheck %s --check-prefix=LOWERED --input-file=%t

// Exercise both results around the i8 borrow boundary:
//   0 - 0       = 0x00, borrow 0
//   0 - 1       = 0xff, borrow 1
//   255 - 255   = 0x00, borrow 0
//   128 - 129   = 0xff, borrow 1
//   129 - 128   = 0x01, borrow 0
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i1, i8, i1, i8, i1, i8, i1, i8, i1)}> ({
    %c0 = "arith.constant"() <{value = 0 : i8}> : () -> i8
    %c1 = "arith.constant"() <{value = 1 : i8}> : () -> i8
    %c128 = "arith.constant"() <{value = 128 : i8}> : () -> i8
    %c129 = "arith.constant"() <{value = 129 : i8}> : () -> i8
    %c255 = "arith.constant"() <{value = 255 : i8}> : () -> i8
    %d0, %b0 = "arith.subui_extended"(%c0, %c0) : (i8, i8) -> (i8, i1)
    %d1, %b1 = "arith.subui_extended"(%c0, %c1) : (i8, i8) -> (i8, i1)
    %d2, %b2 = "arith.subui_extended"(%c255, %c255) : (i8, i8) -> (i8, i1)
    %d3, %b3 = "arith.subui_extended"(%c128, %c129) : (i8, i8) -> (i8, i1)
    %d4, %b4 = "arith.subui_extended"(%c129, %c128) : (i8, i8) -> (i8, i1)
    "func.return"(%d0, %b0, %d1, %b1, %d2, %b2, %d3, %b3, %d4, %b4)
      : (i8, i1, i8, i1, i8, i1, i8, i1, i8, i1) -> ()
  }) : () -> ()
}) : () -> ()

// EXEC: Program output: #[0x00#8, 0x0#1, 0xff#8, 0x1#1, 0x00#8, 0x0#1, 0xff#8, 0x1#1, 0x01#8, 0x0#1]

// LOWERED: "builtin.module"
// LOWERED-NOT: "arith.
