import Veir.Dialects.Arith.Puddle

/-! Shared scalar interpretation and refinement facts for upstream Arith select folds. -/

namespace Veir.ArithCanonicalize.SelectSupport

open Veir Veir.Data Veir.Puddle

/-- VeIR materializes a fully poison integer attribute as `llvm.mlir.poison`. -/
theorem poison_iff {s : IntegerType.Signedness} (w : Nat) (v : RuntimeValue) :
    InterpretsTo (.llvm .mlir__poison) () #[IntegerType.mk w s] #[] #[v] ↔
      v = .int w .poison := by
  simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject]
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms, LLVM.Int.mlir_poison]
  constructor
  · rintro ⟨_, h⟩
    have hh := h .empty
    simp only [Attribute.of_def, IsAttr.inject] at hh
    simpa using hh.symm
  · intro h
    subst v
    constructor
    · simp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject]
    · intro memory
      simp only [Attribute.of_def, IsAttr.inject]

theorem select_iff {s : IntegerType.Signedness} (w : Nat)
    (c : LLVM.Int 1) (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .select) () #[IntegerType.mk w s]
      #[.int 1 c, .int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.select c x y) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem cmpi_iff {s : IntegerType.Signedness} (w : Nat)
    (props : Veir.propertiesOf (.arith .cmpi : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .cmpi) props #[IntegerType.mk 1 s]
      #[.int w x, .int w y] #[v] ↔
      v = .int 1 (LLVM.Int.icmp x y props.predicate) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem same_arms (c : LLVM.Int 1) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select c x x) ⊒ .int w x := by
  cases c <;> simp [LLVM.Int.select, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  grind

theorem true_arm (x y : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (.val (1#1)) x y) ⊒ .int w x := by
  cases x <;> simp [LLVM.Int.select, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem false_arm (x y : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (.val (0#1)) x y) ⊒ .int w y := by
  cases y <;> simp [LLVM.Int.select, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem poison_true_arm (c : LLVM.Int 1) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select c .poison x) ⊒ .int w x := by
  cases x with
  | poison =>
    cases c <;> simp [LLVM.Int.select, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val a =>
  cases c with
  | poison => simp [LLVM.Int.select, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val v =>
    by_cases h : v = 1#1 <;> simp [LLVM.Int.select, h, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem poison_false_arm (c : LLVM.Int 1) (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select c x .poison) ⊒ .int w x := by
  cases x with
  | poison =>
    cases c <;> simp [LLVM.Int.select, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val a =>
  cases c with
  | poison => simp [LLVM.Int.select, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val v =>
    by_cases h : v = 1#1 <;> simp [LLVM.Int.select, h, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem select_bool_identity (c : LLVM.Int 1) :
    RuntimeValue.int 1 (LLVM.Int.select c (.val (1#1)) (.val (0#1))) ⊒ .int 1 c := by
  cases c with
  | poison => simp [LLVM.Int.select, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val v =>
    have h : v = 0#1 ∨ v = 1#1 := by bv_decide
    rcases h with h | h <;> subst v <;>
      simp [LLVM.Int.select, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem select_not_swap (c : LLVM.Int 1) (x y : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.xor c (.val (1#1))) x y) ⊒
      .int w (LLVM.Int.select c y x) := by
  cases c with
  | poison =>
    cases x <;> cases y <;> simp [LLVM.Int.select, LLVM.Int.xor,
      RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val v =>
    have h : v = 0#1 ∨ v = 1#1 := by bv_decide
    rcases h with h | h <;> subst v <;> cases x <;> cases y <;>
      simp [LLVM.Int.select, LLVM.Int.xor, RuntimeValue.isRefinedBy,
        isRefinedBy, Id.run]

theorem select_nested_true (c : LLVM.Int 1) (x y z : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select c (LLVM.Int.select c x y) z) ⊒
      .int w (LLVM.Int.select c x z) := by
  cases c with
  | poison => simp [LLVM.Int.select, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val v =>
    by_cases h : v = 1#1 <;> cases x <;> cases z <;>
      simp [LLVM.Int.select, h, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem select_nested_false (c : LLVM.Int 1) (x y z : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select c x (LLVM.Int.select c y z)) ⊒
      .int w (LLVM.Int.select c x z) := by
  cases c with
  | poison => simp [LLVM.Int.select, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  | val v =>
    by_cases h : v = 1#1 <;> cases x <;> cases z <;>
      simp [LLVM.Int.select, h, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem select_eq_false_arm (x y : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp x y .eq) x y) ⊒ .int w y := by
  cases x with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, RuntimeValue.isRefinedBy,
      isRefinedBy, Id.run]
  | val a =>
    cases y with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, RuntimeValue.isRefinedBy,
        isRefinedBy, Id.run]
    | val b =>
      by_cases h : a = b
      · subst b
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hb : (a == b) = false := beq_eq_false_iff_ne.mpr h
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.IntPred.eval, hb,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem select_ne_true_arm (x y : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp x y .ne) x y) ⊒ .int w x := by
  cases x with
  | poison => simp [LLVM.Int.icmp, LLVM.Int.select, RuntimeValue.isRefinedBy,
      isRefinedBy, Id.run]
  | val a =>
    cases y with
    | poison => simp [LLVM.Int.icmp, LLVM.Int.select, RuntimeValue.isRefinedBy,
        isRefinedBy, Id.run]
    | val b =>
      by_cases h : a = b
      · subst b
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.IntPred.eval,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
      · have hb : (a != b) = true := by
          cases heq : (a != b) with
          | false => exact absurd (bne_eq_false_iff_eq.mp heq) h
          | true => rfl
        simp [LLVM.Int.icmp, LLVM.Int.select, LLVM.IntPred.eval, hb,
          RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem icmp_eq_comm (x y : LLVM.Int w) :
    LLVM.Int.icmp x y .eq = LLVM.Int.icmp y x .eq := by
  cases x <;> cases y <;>
    simp [LLVM.Int.icmp, LLVM.IntPred.eval, Bool.beq_comm, Id.run]

theorem icmp_ne_comm (x y : LLVM.Int w) :
    LLVM.Int.icmp x y .ne = LLVM.Int.icmp y x .ne := by
  cases x <;> cases y <;>
    simp [LLVM.Int.icmp, LLVM.IntPred.eval, bne_comm, Id.run]

theorem select_eq_false_arm_swapped (x y : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp x y .eq) y x) ⊒ .int w x := by
  rw [icmp_eq_comm]
  exact select_eq_false_arm y x

theorem select_ne_true_arm_swapped (x y : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.select (LLVM.Int.icmp x y .ne) y x) ⊒ .int w y := by
  rw [icmp_ne_comm]
  exact select_ne_true_arm y x

theorem minui_iff {s : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .minui) () #[IntegerType.mk w s]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.umin x y) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem minui_self (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.umin x x) ⊒ .int w x := by
  cases x <;> simp [LLVM.Int.umin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem minsi_iff {s : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .minsi) () #[IntegerType.mk w s]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.smin x y) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem minsi_self (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.smin x x) ⊒ .int w x := by
  cases x <;> simp [LLVM.Int.smin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem maxui_iff {s : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .maxui) () #[IntegerType.mk w s]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.umax x y) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem maxui_self (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.umax x x) ⊒ .int w x := by
  cases x <;> simp [LLVM.Int.umax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

theorem maxsi_iff {s : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .maxsi) () #[IntegerType.mk w s]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.smax x y) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem maxsi_self (x : LLVM.Int w) :
    RuntimeValue.int w (LLVM.Int.smax x x) ⊒ .int w x := by
  cases x <;> simp [LLVM.Int.smax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

end Veir.ArithCanonicalize.SelectSupport
