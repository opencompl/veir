// RUN: veir-opt %s | filecheck %s

// --mlir-print-op-generic --mlir-print-local-scope version of llzk-lib/test/FrontendLang/Circom/circom_example_2.llzk
// See https://github.com/project-llzk/llzk-lib/blob/main/test/FrontendLang/Circom/circom_example_2.llzk
"builtin.module"() ({
  "struct.def"() <{const_params = [@A], sym_name = "GetWeight"}> ({
    "struct.member"() <{sym_name = "out", type = !felt.type}> {llzk.pub} : () -> ()
    "function.def"() <{function_type = (!felt.type) -> !struct.type<@GetWeight<[@A]>>, sym_name = "compute"}> ({
    // CHECK: function.def
    ^bb0(%arg9: !felt.type):
      %23 = "struct.new"() : () -> !struct.type<@GetWeight<[@A]>>
      %24 = "poly.read_const"() <{const_name = @A}> : () -> !felt.type
      %25 = "felt.mul"(%24, %arg9) : (!felt.type, !felt.type) -> !felt.type
      "struct.writem"(%23, %25) <{member_name = @out}> : (!struct.type<@GetWeight<[@A]>>, !felt.type) -> ()
      "function.return"(%23) : (!struct.type<@GetWeight<[@A]>>) -> ()
    }) {function.allow_witness} : () -> ()
    "function.def"() <{function_type = (!struct.type<@GetWeight<[@A]>>, !felt.type) -> (), sym_name = "constrain"}> ({
    ^bb0(%arg7: !struct.type<@GetWeight<[@A]>>, %arg8: !felt.type):
      %20 = "poly.read_const"() <{const_name = @A}> : () -> !felt.type
      %21 = "felt.mul"(%20, %arg8) : (!felt.type, !felt.type) -> !felt.type
      %22 = "struct.readm"(%arg7) <{mapOpGroupSizes = array<i32>, member_name = @out, numDimsPerMap = array<i32>}> : (!struct.type<@GetWeight<[@A]>>) -> !felt.type
      "constrain.eq"(%22, %21) : (!felt.type, !felt.type) -> ()
      "function.return"() : () -> ()
    }) {function.allow_constraint} : () -> ()
  }) : () -> ()
  "struct.def"() <{const_params = [@P], sym_name = "ComputeValue"}> ({
    "struct.member"() <{sym_name = "ws", type = !array.type<@P x !struct.type<@GetWeight<[affine_map<(d0) -> (d0 * 5)>]>>>}> : () -> ()
    "struct.member"() <{sym_name = "ret", type = !array.type<@P x !felt.type>}> {llzk.pub} : () -> ()
    "function.def"() <{function_type = (!array.type<@P x !felt.type>) -> !struct.type<@ComputeValue<[@P]>>, sym_name = "compute"}> ({
    ^bb0(%arg4: !array.type<@P x !felt.type>):
      %10 = "struct.new"() : () -> !struct.type<@ComputeValue<[@P]>>
      %11 = "arith.constant"() <{value = 0 : index}> : () -> index
      %12 = "poly.read_const"() <{const_name = @P}> : () -> index
      %13 = "arith.constant"() <{value = 1 : index}> : () -> index
      %14 = "array.new"() <{mapOpGroupSizes = array<i32>, numDimsPerMap = array<i32>, operandSegmentSizes = array<i32: 0, 0>}> : () -> !array.type<@P x !struct.type<@GetWeight<[affine_map<(d0) -> (d0 * 5)>]>>>
      "scf.for"(%11, %12, %13) ({
      ^bb0(%arg6: index):
        %18 = "array.read"(%arg4, %arg6) : (!array.type<@P x !felt.type>, index) -> !felt.type
        %19 = "function.call"(%18, %arg6) <{callee = @GetWeight::@compute, mapOpGroupSizes = array<i32: 1>, numDimsPerMap = array<i32: 1>, operandSegmentSizes = array<i32: 1, 1>}> : (!felt.type, index) -> !struct.type<@GetWeight<[affine_map<(d0) -> (d0 * 5)>]>>
        "array.write"(%14, %arg6, %19) : (!array.type<@P x !struct.type<@GetWeight<[affine_map<(d0) -> (d0 * 5)>]>>>, index, !struct.type<@GetWeight<[affine_map<(d0) -> (d0 * 5)>]>>) -> ()
        "scf.yield"() : () -> ()
      }) : (index, index, index) -> ()
      "struct.writem"(%10, %14) <{member_name = @ws}> : (!struct.type<@ComputeValue<[@P]>>, !array.type<@P x !struct.type<@GetWeight<[affine_map<(d0) -> (d0 * 5)>]>>>) -> ()
      %15 = "array.new"() <{mapOpGroupSizes = array<i32>, numDimsPerMap = array<i32>, operandSegmentSizes = array<i32: 0, 0>}> : () -> !array.type<@P x !felt.type>
      "scf.for"(%11, %12, %13) ({
      ^bb0(%arg5: index):
        %16 = "array.read"(%14, %arg5) : (!array.type<@P x !struct.type<@GetWeight<[affine_map<(d0) -> (d0 * 5)>]>>>, index) -> !struct.type<@GetWeight<[affine_map<(d0) -> (d0 * 5)>]>>
        %17 = "struct.readm"(%16) <{mapOpGroupSizes = array<i32>, member_name = @out, numDimsPerMap = array<i32>}> : (!struct.type<@GetWeight<[affine_map<(d0) -> (d0 * 5)>]>>) -> !felt.type
        "array.write"(%15, %arg5, %17) : (!array.type<@P x !felt.type>, index, !felt.type) -> ()
        "scf.yield"() : () -> ()
      }) : (index, index, index) -> ()
      "struct.writem"(%10, %15) <{member_name = @ret}> : (!struct.type<@ComputeValue<[@P]>>, !array.type<@P x !felt.type>) -> ()
      "function.return"(%10) : (!struct.type<@ComputeValue<[@P]>>) -> ()
    }) {function.allow_witness} : () -> ()
    "function.def"() <{function_type = (!struct.type<@ComputeValue<[@P]>>, !array.type<@P x !felt.type>) -> (), sym_name = "constrain"}> ({
    ^bb0(%arg0: !struct.type<@ComputeValue<[@P]>>, %arg1: !array.type<@P x !felt.type>):
      %0 = "arith.constant"() <{value = 0 : index}> : () -> index
      %1 = "poly.read_const"() <{const_name = @P}> : () -> index
      %2 = "arith.constant"() <{value = 1 : index}> : () -> index
      %3 = "struct.readm"(%arg0) <{mapOpGroupSizes = array<i32>, member_name = @ws, numDimsPerMap = array<i32>}> : (!struct.type<@ComputeValue<[@P]>>) -> !array.type<@P x !struct.type<@GetWeight<[affine_map<(d0) -> (d0 * 5)>]>>>
      "scf.for"(%0, %1, %2) ({
      ^bb0(%arg3: index):
        %8 = "array.read"(%3, %arg3) : (!array.type<@P x !struct.type<@GetWeight<[affine_map<(d0) -> (d0 * 5)>]>>>, index) -> !struct.type<@GetWeight<[affine_map<(d0) -> (d0 * 5)>]>>
        %9 = "array.read"(%arg1, %arg3) : (!array.type<@P x !felt.type>, index) -> !felt.type
        "function.call"(%8, %9) <{callee = @GetWeight::@constrain, mapOpGroupSizes = array<i32>, numDimsPerMap = array<i32>, operandSegmentSizes = array<i32: 2, 0>}> : (!struct.type<@GetWeight<[affine_map<(d0) -> (d0 * 5)>]>>, !felt.type) -> ()
        "scf.yield"() : () -> ()
      }) : (index, index, index) -> ()
      %4 = "struct.readm"(%arg0) <{mapOpGroupSizes = array<i32>, member_name = @ret, numDimsPerMap = array<i32>}> : (!struct.type<@ComputeValue<[@P]>>) -> !array.type<@P x !felt.type>
      "scf.for"(%0, %1, %2) ({
      ^bb0(%arg2: index):
        %5 = "array.read"(%4, %arg2) : (!array.type<@P x !felt.type>, index) -> !felt.type
        %6 = "array.read"(%3, %arg2) : (!array.type<@P x !struct.type<@GetWeight<[affine_map<(d0) -> (d0 * 5)>]>>>, index) -> !struct.type<@GetWeight<[affine_map<(d0) -> (d0 * 5)>]>>
        %7 = "struct.readm"(%6) <{mapOpGroupSizes = array<i32>, member_name = @out, numDimsPerMap = array<i32>}> : (!struct.type<@GetWeight<[affine_map<(d0) -> (d0 * 5)>]>>) -> !felt.type
        "constrain.eq"(%5, %7) : (!felt.type, !felt.type) -> ()
        "scf.yield"() : () -> ()
      }) : (index, index, index) -> ()
      "function.return"() : () -> ()
    }) {function.allow_constraint} : () -> ()
  }) : () -> ()
}) {llzk.lang = "circom"} : () -> ()
