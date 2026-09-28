// Three basic blocks, eight static operations, 10000 loop iterations.
// Expected result: 10000 : i32. Dynamic operations: 30005.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
  ^entry:
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %limit = "llvm.mlir.constant"() <{value = 10000 : i32}> : () -> i32
    "llvm.br"(%zero) [^loop] : (i32) -> ()
  ^loop(%i : i32):
    %next = "llvm.add"(%i, %one) : (i32, i32) -> i32
    %again = "llvm.icmp"(%next, %limit) <{predicate = 6 : i64}> : (i32, i32) -> i1
    "llvm.cond_br"(%again, %next, %next) [^loop, ^exit] <{operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i32, i32) -> ()
  ^exit(%result : i32):
    "llvm.return"(%result) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
