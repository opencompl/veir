import Veir.PatternRewriter.Puddle.Validity
import Veir.Data.LLVM.Int.Lemmas

open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify

/-- A named metadata guard keeps match-congruence auxiliaries shared across consumer modules. -/
def intConstantGuard (p : propertiesOf (.llvm .mlir__constant : OpCode)) (n : Int) : Bool :=
  match p.value with | .integer a => a.value == n | _ => false

/-- Match a scalar LLVM integer constant by its interpreted integer payload. -/
def matchIntConstant (ty : Handle OpCode .type) (n : Int) :
    MatchProg.Builder (Handle OpCode .value) := do
  let op ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    (fun p => intConstantGuard p n)
  return op.res[0]!

def matchZero (ty : Handle OpCode .type) : MatchProg.Builder (Handle OpCode .value) := do
  let op ← MatchProg.operation (.llvm .mlir__zero) #[] #[ty]
  return op.res[0]!

def matchPoison (ty : Handle OpCode .type) : MatchProg.Builder (Handle OpCode .value) := do
  let op ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
  return op.res[0]!

theorem add_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .add : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .add) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.add x y props.nsw props.nuw) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem sub_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .sub : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .sub) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.sub x y props.nsw props.nuw) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem mul_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .mul : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .mul) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.mul x y props.nsw props.nuw) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem xor_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .xor : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .xor) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.xor x y) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem and_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .and : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .and) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.and x y) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem or_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .or : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .or) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.or x y props.disjoint) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem shl_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .shl : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .shl) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.shl x y props.nsw props.nuw) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem lshr_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .lshr : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .lshr) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.lshr x y props.exact) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem ashr_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .ashr : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .ashr) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.ashr x y props.exact) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem zero_iff (ty : IntegerType) (props : propertiesOf (.llvm .mlir__zero : OpCode))
    (v : RuntimeValue) :
    InterpretsTo (.llvm .mlir__zero) props #[ty] #[] #[v] ↔
      v = .int ty.bitwidth (.val (BitVec.ofNat ty.bitwidth 0)) := by
  cases ty
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of, LLVM.Int.mlir_poison,
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem poison_iff (ty : IntegerType) (props : propertiesOf (.llvm .mlir__poison : OpCode))
    (v : RuntimeValue) :
    InterpretsTo (.llvm .mlir__poison) props #[ty] #[] #[v] ↔
      v = .int ty.bitwidth (.poison) := by
  cases ty
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of, LLVM.Int.mlir_poison,
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem constant_iff (ty : IntegerType)
    (props : propertiesOf (.llvm .mlir__constant : OpCode)) (a : IntegerAttr)
    (h : props.value = .integer a) (v : RuntimeValue) :
    InterpretsTo (.llvm .mlir__constant) props #[ty] #[] #[v] ↔
      v = .int ty.bitwidth (.val (BitVec.ofInt ty.bitwidth a.value)) := by
  cases ty
  simp [InterpretsTo, interpretOp', Llvm.interpretOp', h,
    TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of,
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

theorem matched_constant_eq (ty : IntegerType)
    (props : propertiesOf (.llvm .mlir__constant : OpCode)) (n : Int)
    (v : RuntimeValue)
    (h : (match props.value with | .integer a => a.value == n | _ => false) = true)
    (hi : InterpretsTo (.llvm .mlir__constant) props #[ty] #[] #[v]) :
    v = .int ty.bitwidth (.val (BitVec.ofInt ty.bitwidth n)) := by
  cases hp : props.value with
  | integer a =>
    have hn : a.value = n := by simpa [hp] using h
    simpa [hn] using (constant_iff ty props a hp v).mp hi
  | float a => simp [hp] at h
  | dense a => simp [hp] at h
  | string a => simp [hp] at h

theorem sdiv_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .sdiv : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .sdiv) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      LLVM.Int.isSignedDivisionUB x y = false ∧ v = .int w (LLVM.Int.sdiv x y props.exact) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  by_cases h : LLVM.Int.isSignedDivisionUB x y
  · simp [h]
    intro _
    exact ⟨MemoryState.empty, trivial⟩
  · simp [h]
    constructor
    · rintro ⟨_, h⟩
      exact (h .empty).symm
    · grind

theorem udiv_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .udiv : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .udiv) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      LLVM.Int.isUnsignedDivisionUB y = false ∧ v = .int w (LLVM.Int.udiv x y props.exact) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  by_cases h : LLVM.Int.isUnsignedDivisionUB y
  · simp [h]
    intro _
    exact ⟨MemoryState.empty, trivial⟩
  · simp [h]
    constructor
    · rintro ⟨_, h⟩
      exact (h .empty).symm
    · grind

theorem srem_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .srem : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .srem) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      LLVM.Int.isSignedDivisionUB x y = false ∧ v = .int w (LLVM.Int.srem x y) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  by_cases h : LLVM.Int.isSignedDivisionUB x y
  · simp [h]
    intro _
    exact ⟨MemoryState.empty, trivial⟩
  · simp [h]
    constructor
    · rintro ⟨_, h⟩
      exact (h .empty).symm
    · grind

theorem urem_iff {s : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .urem : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .urem) props #[IntegerType.mk w s] #[.int w x, .int w y] #[v] ↔
      LLVM.Int.isUnsignedDivisionUB y = false ∧ v = .int w (LLVM.Int.urem x y) := by
  simp [InterpretsTo, interpretOp', Llvm.interpretOp',
    RuntimeValue.ArrayConforms, RuntimeValue.Conforms]
  by_cases h : LLVM.Int.isUnsignedDivisionUB y
  · simp [h]
    intro _
    exact ⟨MemoryState.empty, trivial⟩
  · simp [h]
    constructor
    · rintro ⟨_, h⟩
      exact (h .empty).symm
    · grind

end Veir.InstSimplify
