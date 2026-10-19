import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Validity
import Veir.Input
import Veir.Printer
import Veir.Data.LLVM.Int.Lemmas

/-!
# Arith Puddle proofs

Interpretation and refinement lemmas for integer Arith patterns. All widths are
quantified; the statements include poison and operation flags through `LLVM.Int`.
-/

namespace Veir.ArithPuddle

open Veir
open Veir.Data
open Veir.Puddle

/-- Interpret an integer `arith.constant` in a Puddle match. -/
theorem constant_iff (ty : IntegerType)
    (props : Veir.propertiesOf (.arith .constant : OpCode)) (v : RuntimeValue) :
    InterpretsTo (.arith .constant) props #[ty] #[] #[v] ↔
      v = .int ty.bitwidth (.val (BitVec.ofInt ty.bitwidth props.value.value)) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms, List.getElem!_toArray,
    List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one, getElem?_pos,
    List.getElem_cons_zero, Option.getD_some, true_and, interpretOp', Arith.interpretOp',
    List.getElem_toArray, TypeAttr.of_val, Attribute.of, Interp.pure_eq]
  constructor
  · rintro ⟨_, h⟩
    grind [h .empty]
  · grind

/-- Interpret `arith.addi` with matching integer operand and result widths. -/
theorem addi_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : Veir.propertiesOf (.arith .addi : OpCode)) (x y : LLVM.Int w)
    (v : RuntimeValue) :
    InterpretsTo (.arith .addi) props #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.add x y props.attr.nsw props.attr.nuw) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Arith.interpretOp', ne_eq, not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self,
    Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true]
  constructor
  · rintro ⟨_, h⟩
    grind [h .empty]
  · grind

/-- Interpret `arith.subi` with matching integer operand and result widths. -/
theorem subi_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : Veir.propertiesOf (.arith .subi : OpCode)) (x y : LLVM.Int w)
    (v : RuntimeValue) :
    InterpretsTo (.arith .subi) props #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.sub x y props.attr.nsw props.attr.nuw) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

/-- Interpret `arith.muli` with matching integer operand and result widths. -/
theorem muli_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : Veir.propertiesOf (.arith .muli : OpCode)) (x y : LLVM.Int w)
    (v : RuntimeValue) :
    InterpretsTo (.arith .muli) props #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.mul x y props.attr.nsw props.attr.nuw) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

/-- Interpret `arith.andi` with matching integer operand and result widths. -/
theorem andi_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .andi) () #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.and x y) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

/-- Interpret `arith.ori`, preserving its disjointness flag. -/
theorem ori_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : Veir.propertiesOf (.arith .ori : OpCode)) (x y : LLVM.Int w)
    (v : RuntimeValue) :
    InterpretsTo (.arith .ori) props #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.or x y props.disjoint) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

/-- Interpret `arith.xori` with matching integer operand and result widths. -/
theorem xori_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .xori) () #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.xor x y) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

/-- Successful unsigned division excludes a zero or poison divisor. -/
theorem divui_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : Veir.propertiesOf (.arith .divui : OpCode)) (x y : LLVM.Int w)
    (v : RuntimeValue) :
    InterpretsTo (.arith .divui) props #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      LLVM.Int.isUnsignedDivisionUB y = false ∧
        v = .int w (LLVM.Int.udiv x y props.exact) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    grind [h .empty]
  · grind

/-- Successful signed division excludes zero and signed overflow. -/
theorem divsi_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : Veir.propertiesOf (.arith .divsi : OpCode)) (x y : LLVM.Int w)
    (v : RuntimeValue) :
    InterpretsTo (.arith .divsi) props #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      LLVM.Int.isSignedDivisionUB x y = false ∧
        v = .int w (LLVM.Int.sdiv x y props.exact) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    grind [h .empty]
  · grind

/-- Successful unsigned remainder excludes a zero or poison divisor. -/
theorem remui_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .remui) () #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      LLVM.Int.isUnsignedDivisionUB y = false ∧
        v = .int w (LLVM.Int.urem x y) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    grind [h .empty]
  · grind

/-- Successful Arith signed remainder excludes zero and signed overflow. -/
theorem remsi_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .remsi) () #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      LLVM.Int.isSignedDivisionUB x y = false ∧
        v = .int w (LLVM.Int.srem x y) := by
  simp [InterpretsTo, interpretOp', Arith.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    grind [h .empty]
  · grind

/-- A flagged addition by zero refines the input, including poison. -/
theorem add_zero_refines (w : Nat) (x : LLVM.Int w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.add x (.val (BitVec.ofInt w 0)) nsw nuw) ⊒
      .int w x := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.add, isRefinedBy, Id.run, pure]
  grind

/-- A flagged subtraction by zero refines the input. -/
theorem sub_zero_refines (w : Nat) (x : LLVM.Int w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.sub x (.val (BitVec.ofInt w 0)) nsw nuw) ⊒
      .int w x := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.sub, isRefinedBy, Id.run, pure]
  grind

/-- A flagged multiplication by one refines the input. -/
theorem mul_one_refines (w : Nat) (x : LLVM.Int w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.mul x (.val (BitVec.ofInt w 1)) nsw nuw) ⊒
      .int w x := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.mul, isRefinedBy, Id.run, pure]
  grind

/-- Multiplication by zero may produce poison, which zero refines. -/
theorem mul_zero_refines (w : Nat) (x : LLVM.Int w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.mul x (.val (BitVec.ofInt w 0)) nsw nuw) ⊒
      .int w (.val 0) := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.mul, isRefinedBy, Id.run, pure]
  grind

/-- Self-subtraction may produce poison, which zero refines. -/
theorem sub_self_refines (w : Nat) (x : LLVM.Int w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.sub x x nsw nuw) ⊒
      .int w (.val 0) := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.sub, isRefinedBy, Id.run, pure]
  grind

/-- Cancellation of a subtraction followed by addition, with arbitrary flags. -/
theorem add_sub_cancel_refines (w : Nat) (a b : LLVM.Int w)
    (subNsw subNuw addNsw addNuw : Bool) :
    RuntimeValue.int w
      (LLVM.Int.add (LLVM.Int.sub a b subNsw subNuw) b addNsw addNuw) ⊒
      .int w a := by
  cases a <;> cases b <;>
    simp [RuntimeValue.isRefinedBy, LLVM.Int.add, LLVM.Int.sub, isRefinedBy, Id.run, pure]
  grind [BitVec.sub_add_cancel]

/-- The commuted outer addition has the same cancellation refinement. -/
theorem add_sub_cancel_comm_refines (w : Nat) (a b : LLVM.Int w)
    (subNsw subNuw addNsw addNuw : Bool) :
    RuntimeValue.int w
      (LLVM.Int.add b (LLVM.Int.sub a b subNsw subNuw) addNsw addNuw) ⊒
      .int w a := by
  cases a <;> cases b <;>
    simp [RuntimeValue.isRefinedBy, LLVM.Int.add, LLVM.Int.sub, isRefinedBy, Id.run,
      pure]
  grind [BitVec.sub_add_cancel]

/-- Cancellation of an addition followed by subtraction. -/
theorem sub_add_cancel_refines (w : Nat) (a b : LLVM.Int w)
    (addNsw addNuw subNsw subNuw : Bool) :
    RuntimeValue.int w
      (LLVM.Int.sub (LLVM.Int.add a b addNsw addNuw) b subNsw subNuw) ⊒
      .int w a := by
  cases a <;> cases b <;>
    simp [RuntimeValue.isRefinedBy, LLVM.Int.add, LLVM.Int.sub, isRefinedBy, Id.run, pure]
  grind [BitVec.add_sub_cancel]

/-- Subtracting the left input of a sum leaves the right input. -/
theorem sub_add_cancel_left_refines (w : Nat) (a b : LLVM.Int w)
    (addNsw addNuw subNsw subNuw : Bool) :
    RuntimeValue.int w
      (LLVM.Int.sub (LLVM.Int.add a b addNsw addNuw) a subNsw subNuw) ⊒
      .int w b := by
  cases a <;> cases b <;>
    simp [RuntimeValue.isRefinedBy, LLVM.Int.add, LLVM.Int.sub, isRefinedBy, Id.run,
      pure]
  grind [BitVec.add_sub_cancel]

/-- Cancellation of a nested subtraction. -/
theorem sub_sub_cancel_refines (w : Nat) (a b : LLVM.Int w)
    (innerNsw innerNuw outerNsw outerNuw : Bool) :
    RuntimeValue.int w
      (LLVM.Int.sub a (LLVM.Int.sub a b innerNsw innerNuw) outerNsw outerNuw) ⊒
      .int w b := by
  cases a <;> cases b <;>
    simp [RuntimeValue.isRefinedBy, LLVM.Int.sub, isRefinedBy, Id.run, pure]
  grind [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm]

/-- Unsigned division by one refines its dividend, even at zero bit width. -/
theorem udiv_one_refines (w : Nat) (x : LLVM.Int w) (exact : Bool) :
    RuntimeValue.int w (LLVM.Int.udiv x (.val (BitVec.ofInt w 1)) exact) ⊒
      .int w x := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.udiv, isRefinedBy,
    Id.run, pure, BitVec.udiv_one]
  all_goals grind

/-- Signed division by one refines its dividend. -/
theorem sdiv_one_refines (w : Nat) (x : LLVM.Int w) (exact : Bool) :
    RuntimeValue.int w (LLVM.Int.sdiv x (.val (BitVec.ofInt w 1)) exact) ⊒
      .int w x := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.sdiv, isRefinedBy,
    Id.run, pure, BitVec.sdiv_one]
  all_goals grind

/-- Multiplication by two refines an unflagged self-addition. -/
theorem mul_two_refines (w : Nat) (x : LLVM.Int w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.mul x (.val (BitVec.ofInt w 2)) nsw nuw) ⊒
      .int w (LLVM.Int.add x x) := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.mul, LLVM.Int.add,
    isRefinedBy, Id.run, pure, BitVec.mul_two]
  grind

/-- Build a matcher for an integer `arith.constant` of a specified value. -/
def matchConstant (returnType : Handle OpCode .type) (constant : Int) :
    MatchProg.Builder (Handle OpCode .value) := do
  let op ← MatchProg.operation (.arith .constant) #[] #[returnType]
    (fun properties => properties.value.value = constant)
  return op.res[0]!

/-- Create an integer `arith.constant` at a matched or created integer type. -/
def createConstant (returnType : Handle OpCode .type) (value : Int) :
    CreateProg.Builder (Handle OpCode .value) := do
  let props ← CreateProg.applyNative returnType (fun type => do
    let intType ← type.cast? IntegerType
    some (ArithConstantProperties.mk (IntegerAttr.ofInt value intType)))
  let op ← CreateProg.operation (.arith .constant) #[] #[returnType] props
  return op.res[0]!

end Veir.ArithPuddle
