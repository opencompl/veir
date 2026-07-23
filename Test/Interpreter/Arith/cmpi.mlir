// RUN: veir-interpret %s | filecheck %s

// `arith.cmpi` lowers to `llvm.icmp`; the predicate integer encoding is shared
// (eq=0, ne=1, slt=2, sle=3, sgt=4, sge=5, ult=6, ule=7, ugt=8, uge=9).
// Operands: a = 5, b = -3 (0xfd, i.e. unsigned 253).
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i1, i1, i1, i1, i1, i1)}> ({
    %a = "arith.constant"() <{ "value" = 5 : i8 }> : () -> i8
    %b = "arith.constant"() <{ "value" = -3 : i8 }> : () -> i8
    %eq  = "arith.cmpi"(%a, %b) <{ "predicate" = 0 : i64 }> : (i8, i8) -> i1
    %ne  = "arith.cmpi"(%a, %b) <{ "predicate" = 1 : i64 }> : (i8, i8) -> i1
    %slt = "arith.cmpi"(%a, %b) <{ "predicate" = 2 : i64 }> : (i8, i8) -> i1
    %sgt = "arith.cmpi"(%a, %b) <{ "predicate" = 4 : i64 }> : (i8, i8) -> i1
    %ult = "arith.cmpi"(%a, %b) <{ "predicate" = 6 : i64 }> : (i8, i8) -> i1
    %ugt = "arith.cmpi"(%a, %b) <{ "predicate" = 8 : i64 }> : (i8, i8) -> i1
    "func.return"(%eq, %ne, %slt, %sgt, %ult, %ugt) : (i1, i1, i1, i1, i1, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0#1, 0x1#1, 0x0#1, 0x1#1, 0x1#1, 0x0#1]
