// RUN: veir-opt %s -p=simplifycfg | filecheck %s
// RUN: veir-opt %s -p=simplifycfg,simplifycfg | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "self_loop", function_type = !llvm.func<void ()>}> ({
  ^entry:
    "llvm.br"() [^loop] : () -> ()
  ^loop:
    "llvm.br"() [^loop] : () -> ()
  }) : () -> ()

  "llvm.func"() <{sym_name = "cycle", function_type = !llvm.func<void (i32, i32)>}> ({
  ^entry(%a : i32, %b : i32):
    "llvm.br"(%a, %b) [^one] : (i32, i32) -> ()
  ^one(%x : i32, %y : i32):
    "llvm.br"(%y, %x) [^two] : (i32, i32) -> ()
  ^two(%p : i32, %q : i32):
    "llvm.br"(%p, %q) [^one] : (i32, i32) -> ()
  }) : () -> ()

  // A backedge through an empty block can still be forwarded to a nonempty one.
  "llvm.func"() <{sym_name = "backedge", function_type = !llvm.func<void (i32)>}> ({
  ^entry(%a : i32):
    "llvm.br"(%a) [^loop] : (i32) -> ()
  ^loop(%x : i32):
    %sum = "llvm.add"(%x, %x) : (i32, i32) -> i32
    "llvm.br"(%sum) [^empty] : (i32) -> ()
  ^empty(%y : i32):
    "llvm.br"(%y) [^loop] : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "self_loop"
// CHECK: "llvm.br"() [^[[SELF:[a-zA-Z0-9_]+]]]
// CHECK-NEXT: ^[[SELF]]():
// CHECK-NEXT: "llvm.br"() [^[[SELF]]]

// CHECK-LABEL: "sym_name" = "cycle"
// CHECK: "llvm.br"(%{{[a-zA-Z0-9_]+}}, %{{[a-zA-Z0-9_]+}}) [^[[ONE:[a-zA-Z0-9_]+]]]
// CHECK-NEXT: ^[[ONE]](%[[X:[a-zA-Z0-9_]+]] : i32, %[[Y:[a-zA-Z0-9_]+]] : i32):
// CHECK-NEXT: "llvm.br"(%[[Y]], %[[X]]) [^[[TWO:[a-zA-Z0-9_]+]]]
// CHECK-NEXT: ^[[TWO]](%[[P:[a-zA-Z0-9_]+]] : i32, %[[Q:[a-zA-Z0-9_]+]] : i32):
// CHECK-NEXT: "llvm.br"(%[[P]], %[[Q]]) [^[[ONE]]]

// CHECK-LABEL: "sym_name" = "backedge"
// CHECK: "llvm.br"(%{{[a-zA-Z0-9_]+}}) [^[[LOOP:[a-zA-Z0-9_]+]]]
// CHECK-NEXT: ^[[LOOP]](%[[VALUE:[a-zA-Z0-9_]+]] : i32):
// CHECK-NEXT: %[[SUM:[a-zA-Z0-9_]+]] = "llvm.add"(%[[VALUE]], %[[VALUE]])
// CHECK-NEXT: "llvm.br"(%[[SUM]]) [^[[LOOP]]]
