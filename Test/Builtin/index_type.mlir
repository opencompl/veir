// RUN: VEIR_ROUNDTRIP

"func.func"() <{
    function_type = (index) -> index,
    sym_name = "identity"
}> ({
^bb0(%arg0 : index):
    "func.return"(%arg0) : (index) -> ()
}) : () -> ()

// CHECK: "func.func"() <{"function_type" = (index) -> index, "sym_name" = "identity"}> ({
// CHECK-NEXT: ^{{.*}}(%[[ARG:.*]] : index):
// CHECK-NEXT:   "func.return"(%{{.*}}) : (index) -> ()