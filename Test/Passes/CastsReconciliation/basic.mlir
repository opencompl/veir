// RUN: veir-opt %s -p=reconcile-cast | filecheck %s

"builtin.module"() ({

  ^1():
    "func.func"()  <{function_type = (i64) -> ()}> ({
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i64
        "test.test"(%1) : (i64) -> ()
        // CHECK:      "test.test"(%{{.*}}) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
    
  ^2():
    "func.func"()  <{function_type = (i64) -> ()}> ({
      ^1(%0 : i64):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        "test.test"(%1) : (!riscv.reg) -> ()
        // CHECK:       "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT:  "test.test"(%{{.*}}) : (!riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
    
  ^3():
    "func.func"()  <{function_type = (i64) -> ()}> ({
      ^1(%0 : i64):
        // the remaining cast is unused 
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i64
        "test.test"(%2) : (i64) -> ()
        // CHECK:       ^{{.*}}([[ARG:%.*]] : i64):
        // CHECK-NEXT:  "test.test"([[ARG]]) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^4():
    "func.func"()  <{function_type = (i64) -> ()}> ({
      ^1(%0 : i64):
        // the remaining cast is used
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        %2 = "test.test"(%1) : (!riscv.reg) -> (!riscv.reg)
        %3 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i64
        "test.test"(%2, %3) : (!riscv.reg, i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : i64):
        // CHECK-NEXT:   %{{.*}} = "builtin.unrealized_conversion_cast"([[ARG]]) : (i64) -> !riscv.reg
        // CHECK-NEXT:   %{{.*}} = "test.test"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:   "test.test"(%{{.*}}, [[ARG]]) : (!riscv.reg, i64) -> ()  
        "func.return"() : () -> ()
    }) : () -> ()
    
  ^5():
    "func.func"()  <{function_type = (i64) -> ()}> ({
      ^1(%0 : i64):
        // identity cast and pairs of casts
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> !riscv.reg
        %3 = "builtin.unrealized_conversion_cast"(%2) : (!riscv.reg) -> i64
        "test.test"(%3) : (i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : i64):
        // CHECK-NEXT:   "test.test"([[ARG]]) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
  
  ^6():
    "func.func"()  <{function_type = (i64) -> ()}> ({
      ^1(%0 : i64):
        // pairs of casts
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        %3 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> !riscv.reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i64
        %4 = "builtin.unrealized_conversion_cast"(%3) : (!riscv.reg) -> i64
        "test.test"(%2, %4) : (i64, i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : i64):
        // CHECK-NEXT:   "test.test"([[ARG]], [[ARG]]) : (i64, i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
    
  ^7():
    "func.func"()  <{function_type = (!riscv.reg) -> ()}> ({
      ^1(%0 : !riscv.reg):
        // identity cast on block argument
        %1 = "builtin.unrealized_conversion_cast"(%0) : (!riscv.reg) -> !riscv.reg
        "test.test"(%1) : (!riscv.reg) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   "test.test"([[ARG]]) : (!riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
  
  ^8():
    "func.func"()  <{function_type = (i8) -> ()}> ({
      ^1(%0 : i8):
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i8) -> i8
        "test.test"(%1) : (i8) -> ()
        // CHECK:        "test.test"(%{{.*}}) : (i8) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
    
  ^9():
    "func.func"()  <{function_type = (i64) -> ()}> ({
      ^1(%0 : i64):
        // pairs of casts
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i256
        %3 = "builtin.unrealized_conversion_cast"(%0) : (i64) -> i128
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i256) -> i64
        %4 = "builtin.unrealized_conversion_cast"(%3) : (i128) -> i64
        "test.test"(%2, %4) : (i64, i64) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : i64):
        // CHECK-NEXT:   "test.test"([[ARG]], [[ARG]]) : (i64, i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^10():
    "func.func"()  <{function_type = (i32) -> ()}> ({
      ^1(%0 : i32):
        // i32 -> reg -> i32 
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i32) -> !riscv.reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i32
        "test.test"(%2) : (i32) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : i32):
        // CHECK-NEXT:   "test.test"([[ARG]]) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^11():
    "func.func"()  <{function_type = (!riscv.reg) -> ()}> ({
      ^1(%0 : !riscv.reg):
        // reg -> i32 -> reg : should not be folded away.
        %1 = "builtin.unrealized_conversion_cast"(%0) : (!riscv.reg) -> i32
        %2 = "builtin.unrealized_conversion_cast"(%1) : (i32) -> !riscv.reg
        "test.test"(%2) : (!riscv.reg) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   %[[C1:.*]] = "builtin.unrealized_conversion_cast"([[ARG]]) : (!riscv.reg) -> i32
        // CHECK-NEXT:   %[[C2:.*]] = "builtin.unrealized_conversion_cast"(%[[C1]]) : (i32) -> !riscv.reg
        // CHECK-NEXT:   "test.test"(%[[C2]]) : (!riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^12():
    "func.func"()  <{function_type = (!llvm.ptr) -> ()}> ({
      ^1(%0 : !llvm.ptr):
        // ptr -> reg -> ptr (64-bit)
        %1 = "builtin.unrealized_conversion_cast"(%0) : (!llvm.ptr) -> !riscv.reg
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> !llvm.ptr
        "test.test"(%2) : (!llvm.ptr) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !llvm.ptr):
        // CHECK-NEXT:   "test.test"([[ARG]]) : (!llvm.ptr) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^13():
    "func.func"()  <{function_type = (!riscv.reg) -> ()}> ({
      ^1(%0 : !riscv.reg):
        // reg -> ptr -> reg (64-bit)
        %1 = "builtin.unrealized_conversion_cast"(%0) : (!riscv.reg) -> !llvm.ptr
        %2 = "builtin.unrealized_conversion_cast"(%1) : (!llvm.ptr) -> !riscv.reg
        "test.test"(%2) : (!riscv.reg) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : !riscv.reg):
        // CHECK-NEXT:   "test.test"([[ARG]]) : (!riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

  ^14():
    "func.func"()  <{function_type = (i32) -> ()}> ({
      ^1(%0 : i32):
        // i32 -> reg -> i32  (reg is also used elsewhere)
        %1 = "builtin.unrealized_conversion_cast"(%0) : (i32) -> !riscv.reg
        %2 = "test.test"(%1) : (!riscv.reg) -> (!riscv.reg)
        %3 = "builtin.unrealized_conversion_cast"(%1) : (!riscv.reg) -> i32
        "test.test"(%2, %3) : (!riscv.reg, i32) -> ()
        // CHECK:        ^{{.*}}([[ARG:%.*]] : i32):
        // CHECK-NEXT:   %{{.*}} = "builtin.unrealized_conversion_cast"([[ARG]]) : (i32) -> !riscv.reg
        // CHECK-NEXT:   %{{.*}} = "test.test"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT:   "test.test"(%{{.*}}, [[ARG]]) : (!riscv.reg, i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
    
    

}) : () -> ()
