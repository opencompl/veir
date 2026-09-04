// RUN: VEIR_UNREGISTERED_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP
// Expected to fail until an unregistered operation may end a block the way
// MLIR allows; drop the XFAIL with the fix.
// XFAIL: *

// `BlockPtr.verifyBlockTerminator` asks the last operation of every block
// whether it `isTerminator`, and an unregistered operation answers `false`:
// there is no op info for it to answer from. So a block ended by anything
// VeIR does not model is rejected even under --allow-unregistered-dialect,
// where MLIR takes the successor list at face value and accepts the block.
//
// This was the second-largest failure class on the sqlite3 -O3 corpus, 204 of
// 1598 function chunks, and every one of them ended a block with `llvm.switch`
// -- see `afpCheckReservedLock`, whose ^bb5 does. Registering that op cleared
// the class, but not the defect: the next unmodelled terminator brings it back.

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 (i32)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%x: i32):
    "foo.terminate"()[^bb1] : () -> ()
  ^bb1:
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "foo.terminate"() [^{{[0-9]+}}] : () -> ()
// CHECK: "llvm.return"(%{{.*}}) : (i32) -> ()
