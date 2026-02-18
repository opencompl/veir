// RUN: veir-opt %s | filecheck %s

// --mlir-print-op-generic --mlir-print-local-scope version of llzk-lib/test/Transforms/R1CSLowering/r1cs_lowering_pass.llzk
// See https://github.com/project-llzk/llzk-lib/blob/main/test/Transforms/R1CSLowering/r1cs_lowering_pass.llzk
"builtin.module"() ({
  "builtin.module"() ({
    "struct.def"() <{sym_name = "CmpConstraint"}> ({
      "struct.member"() <{sym_name = "val", type = !felt.type}> {llzk.pub} : () -> ()
      "function.def"() <{function_type = (!felt.type, !felt.type, !felt.type) -> !struct.type<@CmpConstraint>, sym_name = "compute"}> ({
      ^bb0(%arg11: !felt.type, %arg12: !felt.type, %arg13: !felt.type):
        %12 = "struct.new"() : () -> !struct.type<@CmpConstraint>
        "function.return"(%12) : (!struct.type<@CmpConstraint>) -> ()
      }) {function.allow_witness} : () -> ()
      "function.def"() <{arg_attrs = [{}, {llzk.pub}, {}, {}], function_type = (!struct.type<@CmpConstraint>, !felt.type, !felt.type, !felt.type) -> (), sym_name = "constrain"}> ({
      ^bb0(%arg7: !struct.type<@CmpConstraint>, %arg8: !felt.type, %arg9: !felt.type, %arg10: !felt.type):
        %7 = "felt.mul"(%arg8, %arg9) : (!felt.type, !felt.type) -> !felt.type
        %8 = "felt.mul"(%arg9, %arg10) : (!felt.type, !felt.type) -> !felt.type
        %9 = "felt.add"(%8, %7) : (!felt.type, !felt.type) -> !felt.type
        %10 = "struct.readm"(%arg7) <{mapOpGroupSizes = array<i32>, member_name = @val, numDimsPerMap = array<i32>}> : (!struct.type<@CmpConstraint>) -> !felt.type
        "constrain.eq"(%9, %7) : (!felt.type, !felt.type) -> ()
        %11 = "felt.add"(%7, %arg9) : (!felt.type, !felt.type) -> !felt.type
        "constrain.eq"(%10, %11) : (!felt.type, !felt.type) -> ()
        "function.return"() : () -> ()
      }) {function.allow_constraint} : () -> ()
    }) : () -> ()
  }) {llzk.lang} : () -> ()
  "builtin.module"() ({
    "struct.def"() <{sym_name = "CmpConstraint"}> ({
      "struct.member"() <{sym_name = "val", type = !felt.type}> {llzk.pub} : () -> ()
      "function.def"() <{function_type = (!felt.type, !felt.type, !felt.type) -> !struct.type<@CmpConstraint>, sym_name = "compute"}> ({
      ^bb0(%arg4: !felt.type, %arg5: !felt.type, %arg6: !felt.type):
        %6 = "struct.new"() : () -> !struct.type<@CmpConstraint>
        "function.return"(%6) : (!struct.type<@CmpConstraint>) -> ()
      }) {function.allow_witness} : () -> ()
      "function.def"() <{arg_attrs = [{}, {llzk.pub}, {}, {}], function_type = (!struct.type<@CmpConstraint>, !felt.type, !felt.type, !felt.type) -> (), sym_name = "constrain"}> ({
      ^bb0(%arg0: !struct.type<@CmpConstraint>, %arg1: !felt.type, %arg2: !felt.type, %arg3: !felt.type):
        %0 = "felt.mul"(%arg1, %arg2) : (!felt.type, !felt.type) -> !felt.type
        %1 = "felt.mul"(%arg2, %arg3) : (!felt.type, !felt.type) -> !felt.type
        %2 = "felt.sub"(%1, %0) : (!felt.type, !felt.type) -> !felt.type
        %3 = "felt.neg"(%2) : (!felt.type) -> !felt.type
        %4 = "struct.readm"(%arg0) <{mapOpGroupSizes = array<i32>, member_name = @val, numDimsPerMap = array<i32>}> : (!struct.type<@CmpConstraint>) -> !felt.type
        "constrain.eq"(%3, %0) : (!felt.type, !felt.type) -> ()
        %5 = "felt.sub"(%0, %arg2) : (!felt.type, !felt.type) -> !felt.type
        "constrain.eq"(%4, %5) : (!felt.type, !felt.type) -> ()
        "function.return"() : () -> ()
      }) {function.allow_constraint} : () -> ()
    }) : () -> ()
  }) {llzk.lang} : () -> ()
}) : () -> ()
