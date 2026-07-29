import Veir.Interpreter.Purity

/-! Tests for the soundness bridge from fold evaluation to interpretation. -/

open Veir

private def i32 : TypeAttr := IntegerType.mk 32

private def constantProperties : ArithConstantProperties :=
  .mk (IntegerAttr.mk 7 (IntegerType.mk 32))

private def addProperties : ArithIntegerOverflowFlagsProperties :=
  default

private def addOperands : Array RuntimeValue :=
  #[.int 32 (.val 7), .int 32 (.val 8)]

example :
    foldEvaluate (.arith .constant) constantProperties #[i32] #[] =
      some (.ok #[.int 32 (.val 7)]) := by
  rfl

example :
    foldEvaluate (.arith .addi) addProperties #[i32] addOperands =
      some (.ok #[.int 32 (.val 15)]) := by
  rfl

/-- Malformed operand lists remain interpreter failures, rather than becoming UB. -/
example :
    foldEvaluate (.arith .addi) addProperties #[i32]
      #[.int 32 (.val 7)] = none := by
  rfl

/-- A constant with a non-integer result type remains an interpreter failure. -/
example :
    foldEvaluate (.arith .constant) constantProperties
      #[RegisterType.mk] #[] = none := by
  rfl

/--
The fold-evaluation theorem restores the full interpreter result, including
unchanged memory and an absent control-flow action.
-/
example (memory : MemoryState) :
    interpretOp' (.arith .addi) addProperties #[i32] addOperands #[] memory =
      some (.ok (#[.int 32 (.val 15)], memory, none)) := by
  apply (foldEvaluate_eq_ok_iff
    (.arith .addi) addProperties #[i32] addOperands
    #[.int 32 (.val 15)] memory rfl).mp
  rfl

/-- Successful pure results have the expected declared type in the pilot operations. -/
example :
    RuntimeValue.ArrayConforms #[.int 32 (.val 15)] #[i32] := by
  simp [RuntimeValue.ArrayConforms, RuntimeValue.Conforms, i32]
