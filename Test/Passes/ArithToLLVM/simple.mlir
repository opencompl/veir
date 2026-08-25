// RUN: veir-opt %s --mlir-print-op-generic -p=arith-to-llvm > %t && veir-interpret %t | filecheck %s --check-prefix=EXEC
// RUN: filecheck %s --check-prefix=LOWERED --input-file=%t

// Exercise direct 1:1 lowerings, including wrapping subtraction and valid
// nsw/nuw/disjoint promises.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8)}> ({
    %c0 = "arith.constant"() <{value = 0 : i8}> : () -> i8
    %c1 = "arith.constant"() <{value = 1 : i8}> : () -> i8
    %c16 = "arith.constant"() <{value = 16 : i8}> : () -> i8
    %c48 = "arith.constant"() <{value = 48 : i8}> : () -> i8
    %wrapped = "arith.subi"(%c0, %c1) : (i8, i8) -> i8
    %difference = "arith.subi"(%c48, %c16)
      <{overflowFlags = #arith.overflow<nsw, nuw>}> : (i8, i8) -> i8
    %combined = "arith.ori"(%difference, %c16) <{disjoint}> : (i8, i8) -> i8
    "func.return"(%wrapped, %combined) : (i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// EXEC: Program output: #[0xff#8, 0x30#8]

// LOWERED: "builtin.module"
// LOWERED-NOT: "arith.
