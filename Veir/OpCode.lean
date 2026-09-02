module

/-
# Operation Codes

This file defines the `OpCode` inductive type, which represents the set of registered
operation codes in the Veir intermediate representation (IR). Each `OpCode` corresponds
to an operation definition.
-/

import Veir.Meta.OpCode
public import Veir.Dialects.Arith.OpInfo
public import Veir.Dialects.Builtin.OpInfo
public import Veir.Dialects.Func.OpInfo
public import Veir.Dialects.Cf.OpInfo
public import Veir.Dialects.LLVM.OpInfo
public import Veir.Dialects.RISCV.OpInfo
public import Veir.Dialects.RISCV_Cf.OpInfo
public import Veir.Dialects.RISCV_Stack.OpInfo
public import Veir.Dialects.RV64.OpInfo
public import Veir.Dialects.ModArith.OpInfo
public import Veir.Dialects.Datapath.OpInfo
public import Veir.Dialects.Comb.OpInfo
public import Veir.Dialects.HW.OpInfo
public import Veir.Dialects.Verif.OpInfo
public import Veir.Dialects.PDL.OpInfo
public import Veir.Dialects.IO.OpInfo
public import Veir.Dialects.Test.OpInfo
public import Veir.Dialects.LLZK.Felt.OpInfo
public import Veir.Dialects.LLZK.Include.OpInfo
public import Veir.Dialects.LLZK.Function.OpInfo
public import Veir.Dialects.Cir.OpInfo

open Std

namespace Veir

public section

/-
A type class that defines an MLIR dialect and translates from `DialectCode` to
the dialect type.
-/
/-
  An operation code (OpCode) identifies the type of an operation.
  Each OpCode corresponds to a specific operation.
-/
set_option maxRecDepth 100000
#generate_op_codes

end
end Veir
