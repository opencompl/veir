// RUN: not veir-opt %s -p=register-allocation-riscv64 2>&1 | filecheck %s

// The module body is a single block that may still declare arguments: nothing can ever pass
// a value to them, since `verifyNoEntryBlockPredecessors` leaves a region's entry block
// without predecessors, but they exist as values the allocator never visits. The function
// here is well-formed, so only the module body's argument can be the cause.
"builtin.module"() ({
^body(%arg0 : !riscv.reg):
  "riscv_cf.func"() <{sym_name = "f", function_type = () -> ()}> ({
    %a = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: register allocation does not support block arguments
