import Veir.Dialects.Arith.Puddle

namespace Veir.ArithCanonicalize.CastCounterexampleSupport

open Veir Veir.Data Veir.Puddle

theorem trunci_iff {t : IntegerType.Signedness} (w n : Nat) (h : n < w)
    (props : Veir.propertiesOf (.arith .trunci : OpCode))
    (x : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .trunci) props #[IntegerType.mk n t]
      #[.int w x] #[v] ↔
      v = .int n (LLVM.Int.trunc x n props.attr.nsw props.attr.nuw h) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    simpa only [Attribute.of_def, IsAttr.inject, show ¬ w ≤ n by omega,
      ↓reduceDIte, Interp.bind_ok, Interp.ok.injEq,
      Prod.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true] using (h .empty).symm
  · intro hv
    subst v
    constructor
    · trivial
    · intro memory
      simp only [Attribute.of_def, IsAttr.inject, show ¬ w ≤ n by omega,
        ↓reduceDIte, Interp.bind_ok]

theorem shrsi_iff {s : IntegerType.Signedness} (w : Nat)
    (props : Veir.propertiesOf (.arith .shrsi : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .shrsi) props #[IntegerType.mk w s]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.ashr x y props.exact) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem shrui_iff {s : IntegerType.Signedness} (w : Nat)
    (props : Veir.propertiesOf (.arith .shrui : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .shrui) props #[IntegerType.mk w s]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.lshr x y props.exact) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

end Veir.ArithCanonicalize.CastCounterexampleSupport
