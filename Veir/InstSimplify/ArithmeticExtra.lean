import Veir.InstSimplify.LogicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify

theorem sext_width_lt (src dst : IntegerType)
    (p : propertiesOf (.llvm .sext : OpCode)) (x : LLVM.Int src.bitwidth) (v : RuntimeValue)
    (h : InterpretsTo (.llvm .sext) p #[dst] #[.int src.bitwidth x] #[v]) : src.bitwidth < dst.bitwidth := by
  by_cases hl : src.bitwidth < dst.bitwidth
  · exact hl
  have hn : dst.bitwidth ≤ src.bitwidth := by omega
  have h := h.2 MemoryState.empty
  cases src
  cases dst
  simp [interpretOp', Llvm.interpretOp', TypeAttr.of_val, Attribute.of,
    -Attribute.integerType_eq_of, hn] at h

theorem sext_iff (src dst : IntegerType)
    (p : propertiesOf (.llvm .sext : OpCode)) (x : LLVM.Int src.bitwidth) (v : RuntimeValue)
    (hw : src.bitwidth < dst.bitwidth) :
    InterpretsTo (.llvm .sext) p #[dst] #[.int src.bitwidth x] #[v] ↔
      v = .int dst.bitwidth (LLVM.Int.sext x dst.bitwidth hw) := by
  cases src
  cases dst
  simp [InterpretsTo, interpretOp', Llvm.interpretOp', TypeAttr.of_val, Attribute.of,
    -Attribute.integerType_eq_of, RuntimeValue.ArrayConforms, RuntimeValue.Conforms, Nat.not_le_of_gt hw]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind
end Veir.InstSimplify
