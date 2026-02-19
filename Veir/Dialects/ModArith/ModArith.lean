import Veir.Interpreter

namespace Veir.Dialects.ModArith

/--
  The (coarse) expected result set for Barrett-reduce output values:
  either `x mod q` or `x mod q + q`.
-/
def BarrettReduceSpec (q x output : RuntimeValue) : Prop :=
  ∃ qInt xInt outInt,
    q.toInt? = some qInt ∧
    x.toInt? = some xInt ∧
    output.toInt? = some outInt ∧
    (outInt = xInt % qInt ∨ outInt = xInt % qInt + qInt)

/--
  The interpreter-level Barrett step (`barrettReduceStep?`) returns a value
  in the expected Barrett-reduce result set.
-/
theorem barretReduceInterpreterSemantics_spec
    {q x output : RuntimeValue} {qInt xInt outInt : Int} :
    q.toInt? = some qInt →
    x.toInt? = some xInt →
    1 < qInt →
    0 ≤ xInt →
    xInt < qInt * qInt →
    Veir.barrettReduceStep? qInt xInt = some outInt →
    output.toInt? = some outInt →
    BarrettReduceSpec q x output := by
  sorry

/-!
  Glue theorem connecting the concrete `interpretOp'` behavior for
  `mod_arith.barrett_reduce` to the high-level Barrett result spec.
-/
theorem modArithBarrettReduceInterpretOpSpec
    {ctx : IRContext} {opPtr : OperationPtr}
    {q x output : RuntimeValue} {qInt xInt outInt : Int} :
    (opIn : opPtr.InBounds ctx) →
    (opPtr.get ctx opIn).opType = .mod_arith_barrett_reduce →
    (opPtr.getProperties! ctx .mod_arith_barrett_reduce).modulus.value = qInt →
    q.toInt? = some qInt →
    x.toInt? = some xInt →
    1 < qInt →
    0 ≤ xInt →
    xInt < qInt * qInt →
    interpretOp' ctx opPtr #[x] (opPtrInBounds := opIn) = some (#[output], .continue) →
    output.toInt? = some outInt →
    BarrettReduceSpec q x output := by
  intro opIn hopType hModulus hq hx hqGtOne hxNonneg hxRange hInterp hOut
  have hStep : Veir.barrettReduceStep? qInt xInt = some outInt := by
    -- Extract the Barrett-step equality from the concrete interpreter execution.
    -- This follows from unfolding `interpretOp'` in the `mod_arith.barrett_reduce` case.
    sorry
  exact barretReduceInterpreterSemantics_spec hq hx hqGtOne hxNonneg hxRange hStep hOut


end Veir.Dialects.ModArith
