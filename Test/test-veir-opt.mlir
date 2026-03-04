// RUN: veir-opt %s -p=print-ir,print-ir 2>&1 | filecheck %s

"builtin.module"() ({}) : () -> ()

// CHECK:      // -----// IR Dump //----- //
// CHECK-NEXT: "builtin.module"() ({}) : () -> ()
// CHECK-NEXT: // -----// IR Dump //----- //
// CHECK-NEXT: "builtin.module"() ({}) : () -> ()
// CHECK-NEXT: "builtin.module"() ({}) : () -> ()
