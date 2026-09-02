// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "function.def"() <{sym_name = "invalid_containment", function_type = (!array.type<4,3 x !felt.type<"babybear">>, !array.type<2 x !felt.type<"babybear">>) -> ()}> ({
  ^bb0(%array: !array.type<4,3 x !felt.type<"babybear">>, %subarray: !array.type<2 x !felt.type<"babybear">>):
    // CHECK: Error verifying input program: constrain.in: !array.type<2 x !felt.type<"babybear">> is not an element or compatible subarray of !array.type<4,3 x !felt.type<"babybear">>
    "constrain.in"(%array, %subarray) : (!array.type<4,3 x !felt.type<"babybear">>, !array.type<2 x !felt.type<"babybear">>) -> ()
    "function.return"() : () -> ()
  }) {function.allow_constraint} : () -> ()
}) : () -> ()
