// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: VEIR_MLIR_SAME_VERDICT

// %x is defined in the loop body but used in the loop header. The header is
// reachable from ^entry without going through ^body, so ^body does not dominate
// the header and the use of %x there is invalid.

"builtin.module"() ({
  "func.func"() <{function_type = () -> i32, sym_name = "main"}> ({
  ^entry():
    "cf.br"() [^header] : () -> ()
  ^body():
    %x = "arith.constant"() <{"value" = 5 : i32}> : () -> i32
    "cf.br"() [^header] : () -> ()
  ^header():
    %y = "arith.addi"(%x, %x) : (i32, i32) -> i32
    %c = "arith.constant"() <{"value" = 1 : i1}> : () -> i1
    "cf.cond_br"(%c) [^body, ^exit] <{"branch_weights" = array<i32>, "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^exit():
    "func.return"(%y) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.addi: operand 0 {{.*}} does not dominate its use
