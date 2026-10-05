// RUN: VEIR_UNREGISTERED_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP
//
// Regression test for parsing LLVM struct types nested inside other LLVM types.
//
// The LLVM dialect has a convenience syntax where types can usually [0] drop
// the `!llvm.` prefix if they're already nested inside another LLVM-dialect
// type.
//
// Structs with a body are modelled as `LLVM.StructType` and printed with the
// full `!llvm.` prefix on nested types, which is also valid syntax.
//
// The first case below is the array-of-identified-struct type from the original
// bug report (originally seen on an `llvm.mlir.global`), plus literal, packed,
// and deeply-nested variants.
//
// [0]: Not always, but in practice this is allowed wherever nested types are
// allowed. See `parseLLVMType` for the exact details.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    ^bb0():
      // Identified struct nested in an array (original bug report).
      "test.named"() <{ty = !llvm.array<23 x struct<"struct.et_info", (i8, i8, i8, i8, i8, i8, i8)>>}> : () -> ()

      // Literal struct nested in an array.
      "test.literal"() <{ty = !llvm.array<2 x struct<(i32, f32)>>}> : () -> ()

      // Packed struct nested in an array.
      "test.packed"() <{ty = !llvm.array<4 x struct<packed (i8, i32)>>}> : () -> ()

      // Deeply nested: struct containing a bare array and a bare struct.
      "test.nested"() <{ty = !llvm.array<2 x struct<(i32, array<3 x i8>, struct<(ptr)>)>>}> : () -> ()

      // Top-level structs: empty, packed identified, and a name needing escapes.
      "test.empty"() <{ty = !llvm.struct<()>}> : () -> ()
      "test.packed_named"() <{ty = !llvm.struct<"packed.s", packed (i8, i64)>}> : () -> ()
      "test.escaped"() <{ty = !llvm.struct<"a\22b", (i8)>}> : () -> ()

      // Opaque structs and bare references to identified structs stay opaque.
      "test.opaque"() <{ty = !llvm.struct<"opaque_t", opaque>}> : () -> ()
      "test.recursive"() <{ty = !llvm.struct<"node", (ptr, struct<"node">)>}> : () -> ()

      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:       "builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}():
// CHECK-NEXT:      "func.func"() <{"function_type" = () -> (), "sym_name" = "main"}> ({
// CHECK-NEXT:        ^{{.*}}():
// CHECK-NEXT:          "test.named"() <{"ty" = !llvm.array<23 x !llvm.struct<"struct.et_info", (i8, i8, i8, i8, i8, i8, i8)>>}> : () -> ()
// CHECK-NEXT:          "test.literal"() <{"ty" = !llvm.array<2 x !llvm.struct<(i32, f32)>>}> : () -> ()
// CHECK-NEXT:          "test.packed"() <{"ty" = !llvm.array<4 x !llvm.struct<packed (i8, i32)>>}> : () -> ()
// CHECK-NEXT:          "test.nested"() <{"ty" = !llvm.array<2 x !llvm.struct<(i32, !llvm.array<3 x i8>, !llvm.struct<(!llvm.ptr)>)>>}> : () -> ()
// CHECK-NEXT:          "test.empty"() <{"ty" = !llvm.struct<()>}> : () -> ()
// CHECK-NEXT:          "test.packed_named"() <{"ty" = !llvm.struct<"packed.s", packed (i8, i64)>}> : () -> ()
// CHECK-NEXT:          "test.escaped"() <{"ty" = !llvm.struct<"a\"b", (i8)>}> : () -> ()
// CHECK-NEXT:          "test.opaque"() <{"ty" = !llvm.struct<"opaque_t", opaque>}> : () -> ()
// CHECK-NEXT:          "test.recursive"() <{"ty" = !llvm.struct<"node", (!llvm.ptr, !llvm.struct<"node">)>}> : () -> ()
// CHECK-NEXT:          "func.return"() : () -> ()
// CHECK-NEXT:      }) : () -> ()
// CHECK-NEXT: }) : () -> ()
