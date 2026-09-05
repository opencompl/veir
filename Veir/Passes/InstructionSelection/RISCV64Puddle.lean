import Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.Proofs
import Veir.PatternRewriter.Puddle.Validity
import Veir.PatternRewriter.Puddle.Proofs.Validity
import Veir.Interpreter.Basic
import Veir.IR.Attribute
import Veir.Data.Casting
import Veir.Data.Refinement
import Veir.Data.LLVM.Int.Basic
import Veir.Data.RISCV.Reg.Basic

public section

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-!
# Puddle ports of the RISCV64 instruction-selection rewrites

This file is independent of the existing pass: it does not replace its registration.
Every rewrite family in `RISCV64.lean` is represented here. Names with width suffixes
split the original dispatch; parameterized patterns cover constants, predicates, casts,
selects, GEP element types/strategies, and memory-address forms.

Coverage and proof entry points:
* Arithmetic, bitwise operations, min/max, counts, byte/bit reversal, shifts, rotates,
  general funnel shifts, saturation, abs, extensions, poison, and freeze: `*_valid`.
* All ten comparisons at i8/i32/i64: `icmp_valid`; zero peepholes: `icmpZero_valid`.
* Selects: `selectGeneral_valid`, `selectCzeroeqz_valid`, `selectCzeronez_valid`.
* Integer/byte truncations: `truncInt_valid`, `truncByte_valid`; supported bitcasts:
  the six `bitcast*valid` theorems. The original byte-to-pointer exclusion is retained
  in the proved cases. Width-general theorems include all original supported widths.
* All six GEP sequences: `getelementptr_valid`, using the interpreter's ABI stride.
  `getelementptrChecked` chooses the original ABI sequence and returns its `.Valid`
  certificate only when that condition holds.
* Loads/stores, including folded addresses and volatility: `load` / `store`.
  Their `.Valid` proofs are impossible under the current memory-effect exclusion;
  this is proved by `load_not_valid` / `store_not_valid`.

Incorrect original rewrites found during this port:
* `constant_local` uses the raw integer attribute without decoding its width.
* `fshlConst_local` and `fshrConst_local` likewise use the raw shift attribute.
* `selectAddrRegImm` (used by load/store) inherits the raw-attribute bug.

The `*_counterexample` theorems below check concrete failures. Constant/rotate ports
use decoded values; folded memory patterns also check stride agreement. The original
pass and interpreter remain unchanged. These proofs establish refinement for the
repository's interpreter, including its modeled poison and UB behavior.
-/

namespace Veir.RISCV64Puddle
open Puddle
open Veir.Data

private theorem conformsInteger {type : IntegerType} {value : RuntimeValue}
    (h : value.Conforms (type : TypeAttr)) :
    ∃ x, value = .int type.bitwidth x := RuntimeValue.Conforms.integerType.mp h

@[local simp] private theorem registerType_val (t : RegisterType) :
    (t : TypeAttr).val = .registerType t := rfl

private theorem forall_memoryState (p : Prop) : (∀ _ : MemoryState, p) ↔ p :=
  ⟨fun h => h .empty, fun h _ => h⟩

private theorem exists_checked_eq {α : Type} (a : α) (P Q : α → Prop) :
    (∃ x, P x ∧ a = x ∧ Q x) ↔ P a ∧ Q a := by
  constructor
  · rintro ⟨x, hp, rfl, hq⟩
    exact ⟨hp, hq⟩
  · rintro ⟨hp, hq⟩
    exact ⟨a, hp, rfl, hq⟩

local macro "simpISel" : tactic =>
  `(tactic| (
    try simp (config := { maxSteps := 2000000 }) [TypeAttr.of, InterpretsTo, interpretOp',
      Llvm.interpretOp', Riscv.interpretOp', RISCVImmediateProperties.immField, bind, pure,
      Coe.coe, exists_and_left, forall_memoryState, and_assoc, exists_checked_eq,
      RuntimeValue.ArrayConforms, RuntimeValue.conforms_integerType_iff,
      RuntimeValue.conforms_registerType_iff, RuntimeValue.conforms_byteType_iff,
      RuntimeValue.conforms_pointerType_iff]
    all_goals simp (config := { maxSteps := 2000000 }) [TypeAttr.of, InterpretsTo, interpretOp',
      Llvm.interpretOp', Riscv.interpretOp', RISCVImmediateProperties.immField,
      bind, pure, RuntimeValue.isRefinedBy,
      Coe.coe, and_assoc, exists_and_left] at *))

def lowerUnary (llvmOp : Llvm) (bw : Nat) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp)) : Veir.Puddle.Pattern OpCode :=
  Veir.Puddle.Pattern.Builder
    (do
      let returnType ← Veir.Puddle.MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == bw)
      let x ← Veir.Puddle.MatchProg.value returnType
      let _ ← Veir.Puddle.MatchProg.root (.llvm llvmOp) #[x] #[returnType]
      return (returnType, x))
    (fun (returnType, x) => do
      let regType ← Veir.Puddle.CreateProg.type (RegisterType.mk none)
      let castProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[x] #[regType] castProps
      let riscvOpProps ← Veir.Puddle.CreateProg.property (.riscv riscvOp) riscvProps
      let riscvResOp ← Veir.Puddle.CreateProg.operation (.riscv riscvOp)
          #[castOp.res[0]!] #[regType] riscvOpProps
      let castBackProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castBackOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[riscvResOp.res[0]!] #[returnType] castBackProps
      return castBackOp)
    (fun castBackOp => castBackOp)

def ctlz64 : Pattern OpCode := lowerUnary .intr__ctlz 64 .clz ()

theorem ctlz64_valid : ctlz64.Valid := by
  simp only [ctlz64, lowerUnary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth value hv properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger hv
  simpISel
  rw [← hop.2 MemoryState.empty]
  simpa using (Data.RISCV.ctlz_refinement (x := x))

def ctlz32 : Pattern OpCode := lowerUnary .intr__ctlz 32 .clzw ()

theorem ctlz32_valid : ctlz32.Valid := by
  simp only [ctlz32, lowerUnary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth value hv properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger hv
  simpISel
  rw [← hop.2 MemoryState.empty]
  simpa using (Data.RISCV.ctlz_refinement_32 (x := x))

def cttz64 : Pattern OpCode := lowerUnary .intr__cttz 64 .ctz ()

theorem cttz64_valid : cttz64.Valid := by
  simp only [cttz64, lowerUnary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth value hv properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger hv
  simpISel
  rw [← hop.2 MemoryState.empty]
  simpa using (Data.RISCV.cttz_refinement (x := x))

def cttz32 : Pattern OpCode := lowerUnary .intr__cttz 32 .ctzw ()

theorem cttz32_valid : cttz32.Valid := by
  simp only [cttz32, lowerUnary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth value hv properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger hv
  simpISel
  rw [← hop.2 MemoryState.empty]
  simpa using (Data.RISCV.cttz_refinement_32 (x := x))

def ctpop64 : Pattern OpCode := lowerUnary .intr__ctpop 64 .cpop ()

theorem ctpop64_valid : ctpop64.Valid := by
  simp only [ctpop64, lowerUnary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth value hv properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger hv
  simpISel
  rw [← hop.2 MemoryState.empty]
  simpa using (Data.RISCV.ctpop_refinement (x := x))

def ctpop32 : Pattern OpCode := lowerUnary .intr__ctpop 32 .cpopw ()

theorem ctpop32_valid : ctpop32.Valid := by
  simp only [ctpop32, lowerUnary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth value hv properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger hv
  simpISel
  rw [← hop.2 MemoryState.empty]
  simpa using (Data.RISCV.ctpop_refinement_32 (x := x))

def lowerBinary (llvmOp : Llvm) (typeMatcher : IntegerType → Bool) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp))
    (extend : Option (Σ extOp : Riscv, propertiesOf (OpCode.riscv extOp)) := none) :
    Veir.Puddle.Pattern OpCode :=
  Veir.Puddle.Pattern.Builder
    (do
      let opType ← Veir.Puddle.MatchProg.type (Attr := IntegerType) typeMatcher
      let lhs ← Veir.Puddle.MatchProg.value opType
      let rhs ← Veir.Puddle.MatchProg.value opType
      let _ ← Veir.Puddle.MatchProg.root (.llvm llvmOp) #[lhs, rhs] #[opType]
      return (opType, lhs, rhs))
    (fun (opType, lhs, rhs) => do
      let regType ← Veir.Puddle.CreateProg.type (RegisterType.mk none)
      let lcastProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let lcastOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[lhs] #[regType] lcastProps
      let rcastProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let rcastOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[rhs] #[regType] rcastProps
      let (lval, rval) ← match extend with
        | some ⟨extOp, extProps'⟩ => do
          let extProps ← Veir.Puddle.CreateProg.property (.riscv extOp) extProps'
          let lextOp ← Veir.Puddle.CreateProg.operation (.riscv extOp) #[lcastOp.res[0]!] #[regType] extProps
          let rextOp ← Veir.Puddle.CreateProg.operation (.riscv extOp) #[rcastOp.res[0]!] #[regType] extProps
          pure (lextOp.res[0]!, rextOp.res[0]!)
        | none => pure (lcastOp.res[0]!, rcastOp.res[0]!)
      let riscvOpProps ← Veir.Puddle.CreateProg.property (.riscv riscvOp) riscvProps
      let riscvResOp ← Veir.Puddle.CreateProg.operation (.riscv riscvOp)
          #[lval, rval] #[regType] riscvOpProps
      let castBackProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castBackOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[riscvResOp.res[0]!] #[opType] castBackProps
      return castBackOp)
    (fun castBackOp => castBackOp)


def add64 : Pattern OpCode := lowerBinary .add (fun t => t.bitwidth == 64) .add ()

theorem add64_valid : add64.Valid := by
  simp only [add64, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  veir_bv_decide

def add32 : Pattern OpCode := lowerBinary .add (fun t => t.bitwidth == 32) .addw ()

theorem add32_valid : add32.Valid := by
  simp only [add32, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  apply isRefinedBy_trans ?_ (Data.RISCV.addw_refinement (x := x) (y := y))
  cases x <;> cases y <;> simp [Data.LLVM.Int.add, Id.run, pure, isRefinedBy]
  all_goals grind

def sub64 : Pattern OpCode := lowerBinary .sub (fun t => t.bitwidth == 64) .sub ()

theorem sub64_valid : sub64.Valid := by
  simp only [sub64, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  apply isRefinedBy_trans ?_ (Data.RISCV.sub_refinement (x := x) (y := y))
  cases x <;> cases y <;> simp [Data.LLVM.Int.sub, Id.run, pure, isRefinedBy]
  all_goals grind

def sub32 : Pattern OpCode := lowerBinary .sub (fun t => t.bitwidth == 32) .subw ()

theorem sub32_valid : sub32.Valid := by
  simp only [sub32, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  apply isRefinedBy_trans ?_ (Data.RISCV.subw_refinement (x := x) (y := y))
  cases x <;> cases y <;> simp [Data.LLVM.Int.sub, Id.run, pure, isRefinedBy]
  all_goals grind

def mul64 : Pattern OpCode := lowerBinary .mul (fun t => t.bitwidth == 64) .mul ()

theorem mul64_valid : mul64.Valid := by
  simp only [mul64, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  apply isRefinedBy_trans ?_ (Data.RISCV.mul_refinement (x := x) (y := y))
  cases x <;> cases y <;> simp [Data.LLVM.Int.mul, Id.run, pure, isRefinedBy]
  all_goals grind

def mul32 : Pattern OpCode := lowerBinary .mul (fun t => t.bitwidth == 32) .mulw ()

theorem mul32_valid : mul32.Valid := by
  simp only [mul32, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  apply isRefinedBy_trans ?_ (Data.RISCV.mul_refinement_32 (x := x) (y := y))
  cases x <;> cases y <;> simp [Data.LLVM.Int.mul, Id.run, pure, isRefinedBy]
  all_goals grind

def sdiv64 : Pattern OpCode := lowerBinary .sdiv (fun t => t.bitwidth == 64) .div ()

theorem sdiv64_valid : sdiv64.Valid := by
  simp only [sdiv64, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  have hop := hop.2 MemoryState.empty
  cases hc : Interp.checkSignedDivision x y <;> simp [hc] at hop
  rw [← hop]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  apply isRefinedBy_trans ?_ (Data.RISCV.sdiv_refinement (x := x) (y := y))
  cases x <;> cases y <;> simp [Data.LLVM.Int.sdiv, Id.run, pure, isRefinedBy]
  all_goals grind

def sdiv32 : Pattern OpCode := lowerBinary .sdiv (fun t => t.bitwidth == 32) .divw ()

theorem sdiv32_valid : sdiv32.Valid := by
  simp only [sdiv32, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  have hop := hop.2 MemoryState.empty
  cases hc : Interp.checkSignedDivision x y <;> simp [hc] at hop
  rw [← hop]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  apply isRefinedBy_trans ?_ (Data.RISCV.sdiv_refinement_32 (x := x) (y := y))
  cases x <;> cases y <;> simp [Data.LLVM.Int.sdiv, Id.run, pure, isRefinedBy]
  all_goals grind

def udiv64 : Pattern OpCode := lowerBinary .udiv (fun t => t.bitwidth == 64) .divu ()

theorem udiv64_valid : udiv64.Valid := by
  simp only [udiv64, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  have hop := hop.2 MemoryState.empty
  cases hc : Interp.checkUnsignedDivision y <;> simp [hc] at hop
  rw [← hop]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  apply isRefinedBy_trans ?_ (Data.RISCV.udiv_refinement (x := x) (y := y))
  cases x <;> cases y <;> simp [Data.LLVM.Int.udiv, Id.run, pure, isRefinedBy]
  all_goals grind

def udiv32 : Pattern OpCode := lowerBinary .udiv (fun t => t.bitwidth == 32) .divuw ()

theorem udiv32_valid : udiv32.Valid := by
  simp only [udiv32, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  have hop := hop.2 MemoryState.empty
  cases hc : Interp.checkUnsignedDivision y <;> simp [hc] at hop
  rw [← hop]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  apply isRefinedBy_trans ?_ (Data.RISCV.udiv_refinement_32 (x := x) (y := y))
  cases x <;> cases y <;> simp [Data.LLVM.Int.udiv, Id.run, pure, isRefinedBy]
  all_goals grind

def srem64 : Pattern OpCode := lowerBinary .srem (fun t => t.bitwidth == 64) .rem ()

theorem srem64_valid : srem64.Valid := by
  simp only [srem64, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  have hop := hop.2 MemoryState.empty
  cases hc : Interp.checkSignedDivision x y <;> simp [hc] at hop
  rw [← hop]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.srem_refinement

def srem32 : Pattern OpCode := lowerBinary .srem (fun t => t.bitwidth == 32) .remw ()

theorem srem32_valid : srem32.Valid := by
  simp only [srem32, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  have hop := hop.2 MemoryState.empty
  cases hc : Interp.checkSignedDivision x y <;> simp [hc] at hop
  rw [← hop]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.srem_refinement_32

def urem64 : Pattern OpCode := lowerBinary .urem (fun t => t.bitwidth == 64) .remu ()

theorem urem64_valid : urem64.Valid := by
  simp only [urem64, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  have hop := hop.2 MemoryState.empty
  cases hc : Interp.checkUnsignedDivision y <;> simp [hc] at hop
  rw [← hop]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.urem_refinement

def urem32 : Pattern OpCode := lowerBinary .urem (fun t => t.bitwidth == 32) .remuw ()

theorem urem32_valid : urem32.Valid := by
  simp only [urem32, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  have hop := hop.2 MemoryState.empty
  cases hc : Interp.checkUnsignedDivision y <;> simp [hc] at hop
  rw [← hop]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.urem_refinement_32

def xor64 : Pattern OpCode := lowerBinary .xor (fun t => t.bitwidth == 64) .xor ()

theorem xor64_valid : xor64.Valid := by
  simp only [xor64, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.xor_refinement

def xor32 : Pattern OpCode := lowerBinary .xor (fun t => t.bitwidth == 32) .xor ()

theorem xor32_valid : xor32.Valid := by
  simp only [xor32, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.xor_refinement_32

def smax64 : Pattern OpCode := lowerBinary .intr__smax (fun t => t.bitwidth == 64) .max ()

theorem smax64_valid : smax64.Valid := by
  simp only [smax64, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.smax_refinement

def smax32 : Pattern OpCode := lowerBinary .intr__smax (fun t => t.bitwidth == 32) .max () (extend := some ⟨.sextw, ()⟩)

theorem smax32_valid : smax32.Valid := by
  simp only [smax32, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.smax_refinement_32

def smin64 : Pattern OpCode := lowerBinary .intr__smin (fun t => t.bitwidth == 64) .min ()

theorem smin64_valid : smin64.Valid := by
  simp only [smin64, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.smin_refinement

def smin32 : Pattern OpCode := lowerBinary .intr__smin (fun t => t.bitwidth == 32) .min () (extend := some ⟨.sextw, ()⟩)

theorem smin32_valid : smin32.Valid := by
  simp only [smin32, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.smin_refinement_32

def umax64 : Pattern OpCode := lowerBinary .intr__umax (fun t => t.bitwidth == 64) .maxu ()

theorem umax64_valid : umax64.Valid := by
  simp only [umax64, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.umax_refinement

def umax32 : Pattern OpCode := lowerBinary .intr__umax (fun t => t.bitwidth == 32) .maxu ()

theorem umax32_valid : umax32.Valid := by
  simp only [umax32, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.umax_refinement_32

def umin64 : Pattern OpCode := lowerBinary .intr__umin (fun t => t.bitwidth == 64) .minu ()

theorem umin64_valid : umin64.Valid := by
  simp only [umin64, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.umin_refinement

def umin32 : Pattern OpCode := lowerBinary .intr__umin (fun t => t.bitwidth == 32) .minu ()

theorem umin32_valid : umin32.Valid := by
  simp only [umin32, lowerBinary]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨x, rfl⟩ := conformsInteger ha
  obtain ⟨y, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.umin_refinement_32

/-- Emit one register-producing RISC-V instruction. -/
private def emit (op : Riscv) (args : Array (Handle OpCode .value))
    (props : propertiesOf (OpCode.riscv op)) : CreateProg.Builder (Handle OpCode .value) := do
  let reg ← CreateProg.type (RegisterType.mk none)
  let props ← CreateProg.property (.riscv op) props
  let result ← CreateProg.operation (.riscv op) args #[reg] props
  return result.res[0]!

private def castValue (x : Handle OpCode .value) (ty : Handle OpCode .type) :
    CreateProg.Builder CreatedOpHandle := do
  let props ← CreateProg.property (.builtin .unrealized_conversion_cast) ()
  CreateProg.operation (.builtin .unrealized_conversion_cast) #[x] #[ty] props

/-- Puddle port of the `and64` lowering in `RISCV64.lean`. -/
def and64 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .and) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let r ← emit .and #[a, b] ()
      castValue r ty)
    (fun result => result)

theorem and64_valid : and64.Valid := by
  simp only [and64, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.and_refinement

/-- Puddle port of the `or64` lowering in `RISCV64.lean`. -/
def or64 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .or) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let r ← emit .or #[a, b] ()
      castValue r ty)
    (fun result => result)

theorem or64_valid : or64.Valid := by
  simp only [or64, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  apply isRefinedBy_trans ?_ (Data.RISCV.or_refinement (x := a) (y := b))
  cases a <;> cases b <;> simp [Data.LLVM.Int.or, Id.run, pure, isRefinedBy]
  all_goals grind

/-- Puddle port of the `and32` lowering in `RISCV64.lean`. -/
def and32 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .and) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let r ← emit .and #[a, b] ()
      castValue r ty)
    (fun result => result)

theorem and32_valid : and32.Valid := by
  simp only [and32, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.and_refinement_32

/-- Puddle port of the `or32` lowering in `RISCV64.lean`. -/
def or32 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .or) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let r ← emit .or #[a, b] ()
      castValue r ty)
    (fun result => result)

theorem or32_valid : or32.Valid := by
  simp only [or32, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  apply isRefinedBy_trans ?_ (Data.RISCV.or_refinement_32 (x := a) (y := b))
  cases a <;> cases b <;> simp [Data.LLVM.Int.or, Id.run, pure, isRefinedBy]
  all_goals grind

/-- Puddle port of the `and8` lowering in `RISCV64.lean`. -/
def and8 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 8)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .and) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let r ← emit .and #[a, b] ()
      castValue r ty)
    (fun result => result)

theorem and8_valid : and8.Valid := by
  simp only [and8, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.and_refinement_8

/-- Puddle port of the `or8` lowering in `RISCV64.lean`. -/
def or8 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 8)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .or) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let r ← emit .or #[a, b] ()
      castValue r ty)
    (fun result => result)

theorem or8_valid : or8.Valid := by
  simp only [or8, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  apply isRefinedBy_trans ?_ (Data.RISCV.or_refinement_8 (x := a) (y := b))
  cases a <;> cases b <;> simp [Data.LLVM.Int.or, Id.run, pure, isRefinedBy]
  all_goals grind

/-- Puddle port of the `and1` lowering in `RISCV64.lean`. -/
def and1 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .and) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let r ← emit .and #[a, b] ()
      castValue r ty)
    (fun result => result)

theorem and1_valid : and1.Valid := by
  simp only [and1, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.and_refinement_1

/-- Puddle port of the `or1` lowering in `RISCV64.lean`. -/
def or1 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .or) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let r ← emit .or #[a, b] ()
      castValue r ty)
    (fun result => result)

theorem or1_valid : or1.Valid := by
  simp only [or1, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  apply isRefinedBy_trans ?_ (Data.RISCV.or_refinement_1 (x := a) (y := b))
  cases a <;> cases b <;> simp [Data.LLVM.Int.or, Id.run, pure, isRefinedBy]
  all_goals grind

/-- Puddle port of the `bswap64` lowering in `RISCV64.lean`. -/
def bswap64 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__bswap) #[a] #[ty]
      return (ty, a))
    (fun (ty, a) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let r ← emit .rev8 #[a] ()
      castValue r ty)
    (fun result => result)

theorem bswap64_valid : bswap64.Valid := by
  simp only [bswap64, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.bswap_refinement

/-- Puddle port of the `freeze64` lowering in `RISCV64.lean`. -/
def freeze64 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .freeze) #[a] #[ty]
      return (ty, a))
    (fun (ty, a) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      castValue a ty)
    (fun result => result)

theorem freeze64_valid : freeze64.Valid := by
  simp only [freeze64, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.freeze_refinement

/-- Puddle port of the `fshl64` lowering in `RISCV64.lean`. -/
def fshl64 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let c ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__fshl) #[a, a, c] #[ty]
      return (ty, a, c))
    (fun (ty, a, c) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let cCast ← castValue c reg
      let c := cCast.res[0]!
      let r ← emit .rol #[a, c] ()
      castValue r ty)
    (fun result => result)

theorem fshl64_valid : fshl64.Valid := by
  simp only [fshl64, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha c hc properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨c, rfl⟩ := conformsInteger hc
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.fshl_rol_refinement

/-- Puddle port of the `fshlGeneral64` lowering in `RISCV64.lean`. -/
def fshlGeneral64 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let c ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__fshl) #[a, b, c] #[ty]
      return (ty, a, b, c))
    (fun (ty, a, b, c) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let cCast ← castValue c reg
      let c := cCast.res[0]!
      let nc ← emit .xori #[c] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (-1)))
      let x ← emit .sll #[a, c] ()
      let y ← emit .srli #[b] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (1)))
      let y ← emit .srl #[y, nc] ()
      let r ← emit .or #[x, y] ()
      castValue r ty)
    (fun result => result)

theorem fshlGeneral64_valid : fshlGeneral64.Valid := by
  simp only [fshlGeneral64, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb c hc properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  obtain ⟨c, rfl⟩ := conformsInteger hc
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.or, BitVec.or_comm] using (Data.RISCV.fshlGeneral_refinement (a := a) (b := b) (c := c))

/-- Puddle port of the `fshr64` lowering in `RISCV64.lean`. -/
def fshr64 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let c ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__fshr) #[a, a, c] #[ty]
      return (ty, a, c))
    (fun (ty, a, c) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let cCast ← castValue c reg
      let c := cCast.res[0]!
      let r ← emit .ror #[a, c] ()
      castValue r ty)
    (fun result => result)

theorem fshr64_valid : fshr64.Valid := by
  simp only [fshr64, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha c hc properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨c, rfl⟩ := conformsInteger hc
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.fshr_ror_refinement

/-- Puddle port of the `fshrGeneral64` lowering in `RISCV64.lean`. -/
def fshrGeneral64 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let c ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__fshr) #[a, b, c] #[ty]
      return (ty, a, b, c))
    (fun (ty, a, b, c) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let cCast ← castValue c reg
      let c := cCast.res[0]!
      let nc ← emit .xori #[c] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (-1)))
      let x ← emit .slli #[a] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (1)))
      let x ← emit .sll #[x, nc] ()
      let y ← emit .srl #[b, c] ()
      let r ← emit .or #[x, y] ()
      castValue r ty)
    (fun result => result)

theorem fshrGeneral64_valid : fshrGeneral64.Valid := by
  simp only [fshrGeneral64, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb c hc properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  obtain ⟨c, rfl⟩ := conformsInteger hc
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.or, BitVec.or_comm] using (Data.RISCV.fshrGeneral_refinement (a := a) (b := b) (c := c))

/-- Puddle port of the `bswap32` lowering in `RISCV64.lean`. -/
def bswap32 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
      let a ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__bswap) #[a] #[ty]
      return (ty, a))
    (fun (ty, a) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let r ← emit .rev8 #[a] ()
      let r ← emit .srli #[r] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (32)))
      castValue r ty)
    (fun result => result)

theorem bswap32_valid : bswap32.Valid := by
  simp only [bswap32, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.bswap_refinement_32

/-- Puddle port of the `freeze32` lowering in `RISCV64.lean`. -/
def freeze32 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
      let a ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .freeze) #[a] #[ty]
      return (ty, a))
    (fun (ty, a) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      castValue a ty)
    (fun result => result)

theorem freeze32_valid : freeze32.Valid := by
  simp only [freeze32, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.freeze_refinement_32

/-- Puddle port of the `fshl32` lowering in `RISCV64.lean`. -/
def fshl32 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
      let a ← MatchProg.value ty
      let c ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__fshl) #[a, a, c] #[ty]
      return (ty, a, c))
    (fun (ty, a, c) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let cCast ← castValue c reg
      let c := cCast.res[0]!
      let r ← emit .rolw #[a, c] ()
      castValue r ty)
    (fun result => result)

theorem fshl32_valid : fshl32.Valid := by
  simp only [fshl32, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha c hc properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨c, rfl⟩ := conformsInteger hc
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.fshl_rol_refinement_32

/-- Puddle port of the `fshlGeneral32` lowering in `RISCV64.lean`. -/
def fshlGeneral32 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let c ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__fshl) #[a, b, c] #[ty]
      return (ty, a, b, c))
    (fun (ty, a, b, c) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let cCast ← castValue c reg
      let c := cCast.res[0]!
      let nc ← emit .xori #[c] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (-1)))
      let x ← emit .sllw #[a, c] ()
      let y ← emit .srliw #[b] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (1)))
      let y ← emit .srlw #[y, nc] ()
      let r ← emit .or #[x, y] ()
      castValue r ty)
    (fun result => result)

theorem fshlGeneral32_valid : fshlGeneral32.Valid := by
  simp only [fshlGeneral32, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb c hc properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  obtain ⟨c, rfl⟩ := conformsInteger hc
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.or, BitVec.or_comm] using (Data.RISCV.fshlGeneralw_refinement (a := a) (b := b) (c := c))

/-- Puddle port of the `fshr32` lowering in `RISCV64.lean`. -/
def fshr32 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
      let a ← MatchProg.value ty
      let c ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__fshr) #[a, a, c] #[ty]
      return (ty, a, c))
    (fun (ty, a, c) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let cCast ← castValue c reg
      let c := cCast.res[0]!
      let r ← emit .rorw #[a, c] ()
      castValue r ty)
    (fun result => result)

theorem fshr32_valid : fshr32.Valid := by
  simp only [fshr32, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha c hc properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨c, rfl⟩ := conformsInteger hc
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.fshr_ror_refinement_32

/-- Puddle port of the `fshrGeneral32` lowering in `RISCV64.lean`. -/
def fshrGeneral32 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let c ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__fshr) #[a, b, c] #[ty]
      return (ty, a, b, c))
    (fun (ty, a, b, c) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let cCast ← castValue c reg
      let c := cCast.res[0]!
      let nc ← emit .xori #[c] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (-1)))
      let x ← emit .slliw #[a] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (1)))
      let x ← emit .sllw #[x, nc] ()
      let y ← emit .srlw #[b, c] ()
      let r ← emit .or #[x, y] ()
      castValue r ty)
    (fun result => result)

theorem fshrGeneral32_valid : fshrGeneral32.Valid := by
  simp only [fshrGeneral32, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb c hc properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  obtain ⟨c, rfl⟩ := conformsInteger hc
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.or, BitVec.or_comm] using (Data.RISCV.fshrGeneralw_refinement (a := a) (b := b) (c := c))

/-- Puddle port of the `abs` lowering in `RISCV64.lean`. -/
def abs : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__abs) #[a] #[ty]
      return (ty, a))
    (fun (ty, a) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let neg ← emit .neg #[a] ()
      let r ← emit .max #[a, neg] ()
      castValue r ty)
    (fun result => result)

theorem abs_valid : abs.Valid := by
  simp only [abs, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.abs_refinement

local macro "proveLargeISelValid" : tactic =>
  `(tactic| (
    unfoldPuddleBuilder
    constructor
    · provePuddleSupported
    · cbv
    · cbv
    simp (config := { maxSteps := 2000000 }) only [Pattern.PreservesSemantics, MatchProg.Models,
      MatchProg.bindingDecls, List.partition_eq_filter_filter, List.filter,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      CreateProg.Models, CreateProg.modelsDecls, CreateDecl.Models,
      SemanticAssignment.getValues, SemanticAssignment.bindProperty, List.mapM_cons,
      SemanticAssignment.getValue, SemanticAssignment.bind, Nat.reduceEqDiff, ↓reduceIte,
      List.mapM_nil, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
      SemanticAssignment.getTypes, SemanticAssignment.getType, reduceCtorEq,
      SemanticAssignment.getProperty, ↓reduceDIte, Array.toList_map, Array.toList_range,
      List.range_succ, List.range_zero, List.map_cons, Nat.add_zero, Nat.reduceAdd, List.map_nil,
      and_true, true_and, true_implies, Replacement.RefinesRoot, MatchProg.rootResults?,
      SemanticAssignment.ExistsValues,
      SemanticAssignment.bindValue,
      MatchProg.modelsDecls, MatchDecl.Models, SemanticAssignment.bindType,
      Nat.zero_ne_one, Nat.succ_ne_self, decide_eq_true_eq,
      SemanticAssignment.ForallValues, and_imp, RuntimeValue.arrayIsRefinedBy_cons,
      RuntimeValue.arrayIsRefinedBy_refl]
    simpPuddleSemantics
  ))


/-- Puddle port of the `saddSat` lowering in `RISCV64.lean`. -/
def saddSat : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__sadd__sat) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let m ← emit .li #[] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (-1)))
      let wrapped ← emit .add #[a, b] ()
      let s ← emit .srli #[b] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (63)))
      let c ← emit .slt #[wrapped, a] ()
      let sign ← emit .srai #[wrapped] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (63)))
      let endpt ← emit .slli #[m] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (63)))
      let overflow ← emit .xor #[s, c] ()
      let sat ← emit .xor #[sign, endpt] ()
      let wz ← emit .czeronez #[wrapped, overflow] ()
      let sz ← emit .czeroeqz #[sat, overflow] ()
      let r ← emit .or #[sz, wz] ()
      castValue r ty)
    (fun result => result)

theorem saddSat_valid : saddSat.Valid := by
  simp only [saddSat, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.saddSat_refinement

/-- Puddle port of the `ssubSat` lowering in `RISCV64.lean`. -/
def ssubSat : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__ssub__sat) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let m ← emit .li #[] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (-1)))
      let wrapped ← emit .sub #[a, b] ()
      let s ← emit .slt #[a, b] ()
      let c ← emit .srli #[wrapped] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (63)))
      let sign ← emit .srai #[wrapped] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (63)))
      let endpt ← emit .slli #[m] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (63)))
      let overflow ← emit .xor #[s, c] ()
      let sat ← emit .xor #[sign, endpt] ()
      let wz ← emit .czeronez #[wrapped, overflow] ()
      let sz ← emit .czeroeqz #[sat, overflow] ()
      let r ← emit .or #[sz, wz] ()
      castValue r ty)
    (fun result => result)

theorem ssubSat_valid : ssubSat.Valid := by
  simp only [ssubSat, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.ssubSat_refinement

/-- Puddle port of the `uaddSat` lowering in `RISCV64.lean`. -/
def uaddSat : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__uadd__sat) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let nb ← emit .xori #[b] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (-1)))
      let mn ← emit .minu #[a, nb] ()
      let r ← emit .add #[mn, b] ()
      castValue r ty)
    (fun result => result)

theorem uaddSat_valid : uaddSat.Valid := by
  simp only [uaddSat, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.uaddSat_refinement

/-- Puddle port of the `usubSat` lowering in `RISCV64.lean`. -/
def usubSat : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__usub__sat) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let mx ← emit .maxu #[a, b] ()
      let r ← emit .sub #[mx, b] ()
      castValue r ty)
    (fun result => result)

theorem usubSat_valid : usubSat.Valid := by
  simp only [usubSat, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.usubSat_refinement

/-- Puddle port of the `sshlSat` lowering in `RISCV64.lean`. -/
def sshlSat : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__sshl__sat) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let wrapped ← emit .sll #[a, b] ()
      let m ← emit .li #[] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (-1)))
      let u ← emit .sra #[wrapped, b] ()
      let sign ← emit .srai #[a] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (63)))
      let endpt ← emit .srli #[m] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (1)))
      let overflow ← emit .xor #[a, u] ()
      let sat ← emit .xor #[sign, endpt] ()
      let wz ← emit .czeronez #[wrapped, overflow] ()
      let sz ← emit .czeroeqz #[sat, overflow] ()
      let r ← emit .or #[sz, wz] ()
      castValue r ty)
    (fun result => result)

theorem sshlSat_valid : sshlSat.Valid := by
  simp only [sshlSat, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.sshlSat_refinement

/-- Puddle port of the `ushlSat` lowering in `RISCV64.lean`. -/
def ushlSat : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__ushl__sat) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let wrapped ← emit .sll #[a, b] ()
      let u ← emit .srl #[wrapped, b] ()
      let lost ← emit .xor #[a, u] ()
      let no ← emit .sltiu #[lost] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (1)))
      let mask ← emit .addi #[no] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (-1)))
      let r ← emit .or #[mask, wrapped] ()
      castValue r ty)
    (fun result => result)

theorem ushlSat_valid : ushlSat.Valid := by
  simp only [ushlSat, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact Data.RISCV.ushlSat_refinement

local macro "simpLargeISel" : tactic =>
  `(tactic| (
    try simp (config := { maxSteps := 2000000 }) [TypeAttr.of, InterpretsTo, interpretOp',
      Llvm.interpretOp', Riscv.interpretOp', bind, pure,
      Coe.coe, exists_and_left, forall_memoryState, and_assoc, exists_checked_eq,
      RuntimeValue.ArrayConforms, RuntimeValue.conforms_integerType_iff,
      RuntimeValue.conforms_registerType_iff, RuntimeValue.conforms_byteType_iff,
      RuntimeValue.conforms_pointerType_iff]
    all_goals simp (config := { maxSteps := 2000000 }) [TypeAttr.of, InterpretsTo, interpretOp',
      Llvm.interpretOp', Riscv.interpretOp', bind, pure, RuntimeValue.isRefinedBy,
      Coe.coe, and_assoc, exists_and_left] at *))

/-- Puddle port of the `bitreverse64` lowering in `RISCV64.lean`. -/
def bitreverse64 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__bitreverse) #[a] #[ty]
      return (ty, a))
    (fun (ty, a) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let mask ← emit .li #[] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (0x5555555555555555)))
      let lo ← emit .and #[mask, a] ()
      let lo ← emit .slli #[lo] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (1)))
      let hi ← emit .srli #[a] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (1)))
      let hi ← emit .and #[mask, hi] ()
      let stage0 ← emit .or #[lo, hi] ()
      let mask ← emit .li #[] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (0x3333333333333333)))
      let lo ← emit .and #[mask, stage0] ()
      let lo ← emit .slli #[lo] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (2)))
      let hi ← emit .srli #[stage0] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (2)))
      let hi ← emit .and #[mask, hi] ()
      let stage1 ← emit .or #[lo, hi] ()
      let mask ← emit .li #[] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (0x0f0f0f0f0f0f0f0f)))
      let lo ← emit .and #[mask, stage1] ()
      let lo ← emit .slli #[lo] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (4)))
      let hi ← emit .srli #[stage1] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (4)))
      let hi ← emit .and #[mask, hi] ()
      let stage2 ← emit .or #[lo, hi] ()
      let r ← emit .rev8 #[stage2] ()
      castValue r ty)
    (fun result => result)

theorem bitreverse64_valid : bitreverse64.Valid := by
  simp only [bitreverse64, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth a ha properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  simpLargeISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [RISCVImmediateProperties.immField, Data.RISCV.or, Data.RISCV.and,
    BitVec.or_comm, BitVec.and_comm] using (Data.RISCV.bitreverse_refinement (x := a))

/-- Puddle port of the `bitreverse32` lowering in `RISCV64.lean`. -/
def bitreverse32 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
      let a ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .intr__bitreverse) #[a] #[ty]
      return (ty, a))
    (fun (ty, a) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let mask ← emit .li #[] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (0x55555555)))
      let lo ← emit .and #[mask, a] ()
      let lo ← emit .slli #[lo] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (1)))
      let hi ← emit .srli #[a] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (1)))
      let hi ← emit .and #[mask, hi] ()
      let stage0 ← emit .or #[lo, hi] ()
      let mask ← emit .li #[] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (0x33333333)))
      let lo ← emit .and #[mask, stage0] ()
      let lo ← emit .slli #[lo] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (2)))
      let hi ← emit .srli #[stage0] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (2)))
      let hi ← emit .and #[mask, hi] ()
      let stage1 ← emit .or #[lo, hi] ()
      let mask ← emit .li #[] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (0x0f0f0f0f)))
      let lo ← emit .and #[mask, stage1] ()
      let lo ← emit .slli #[lo] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (4)))
      let hi ← emit .srli #[stage1] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (4)))
      let hi ← emit .and #[mask, hi] ()
      let stage2 ← emit .or #[lo, hi] ()
      let r ← emit .rev8 #[stage2] ()
      let r ← emit .srli #[r] (RISCVImmediateProperties.mk (BitVec.ofInt 64 (32)))
      castValue r ty)
    (fun result => result)

theorem bitreverse32_valid : bitreverse32.Valid := by
  simp only [bitreverse32, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth a ha properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  simpLargeISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [RISCVImmediateProperties.immField, Data.RISCV.or, Data.RISCV.and,
    BitVec.or_comm, BitVec.and_comm] using (Data.RISCV.bitreverse_refinement_32 (x := a))

/-- Puddle port of the `shl64` lowering in `RISCV64.lean`. -/
def shl64 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .shl) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let r ← emit .sll #[a, b] ()
      castValue r ty)
    (fun result => result)

theorem shl64_valid : shl64.Valid := by
  simp only [shl64, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  veir_bv_decide

/-- Puddle port of the `lshr64` lowering in `RISCV64.lean`. -/
def lshr64 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .lshr) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let r ← emit .srl #[a, b] ()
      castValue r ty)
    (fun result => result)

theorem lshr64_valid : lshr64.Valid := by
  simp only [lshr64, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  veir_bv_decide

/-- Puddle port of the `ashr64` lowering in `RISCV64.lean`. -/
def ashr64 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .ashr) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let r ← emit .sra #[a, b] ()
      castValue r ty)
    (fun result => result)

theorem ashr64_valid : ashr64.Valid := by
  simp only [ashr64, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  veir_bv_decide

/-- Puddle port of the `shl32` lowering in `RISCV64.lean`. -/
def shl32 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .shl) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let r ← emit .sllw #[a, b] ()
      castValue r ty)
    (fun result => result)

theorem shl32_valid : shl32.Valid := by
  simp only [shl32, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  veir_bv_decide

/-- Puddle port of the `lshr32` lowering in `RISCV64.lean`. -/
def lshr32 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .lshr) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let r ← emit .srlw #[a, b] ()
      castValue r ty)
    (fun result => result)

theorem lshr32_valid : lshr32.Valid := by
  simp only [lshr32, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  veir_bv_decide

/-- Puddle port of the `ashr32` lowering in `RISCV64.lean`. -/
def ashr32 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .ashr) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let r ← emit .sraw #[a, b] ()
      castValue r ty)
    (fun result => result)

theorem ashr32_valid : ashr32.Valid := by
  simp only [ashr32, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  veir_bv_decide

/-- Puddle port of the `ashr8` lowering in `RISCV64.lean`. -/
def ashr8 : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 8)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .ashr) #[a, b] #[ty]
      return (ty, a, b))
    (fun (ty, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let aCast ← castValue a reg
      let a := aCast.res[0]!
      let bCast ← castValue b reg
      let b := bCast.res[0]!
      let a ← emit .sextb #[a] ()
      let r ← emit .sra #[a, b] ()
      castValue r ty)
    (fun result => result)

theorem ashr8_valid : ashr8.Valid := by
  simp only [ashr8, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth a ha b hb properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  veir_bv_decide

private theorem resize_signExtend (x : BitVec n) (h : w ≤ 64) :
    (x.signExtend 64).setWidth w = x.signExtend w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  by_cases hi : i < w <;> by_cases hn : i < n <;> simp_all <;> omega

def lowerExt (llvmOp : Llvm) (opBw : Nat) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp)) : Veir.Puddle.Pattern OpCode :=
  Veir.Puddle.Pattern.Builder
    (do
      let opType ← Veir.Puddle.MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == opBw)
      let resType ← Veir.Puddle.MatchProg.type (Attr := IntegerType)
          (fun t => opBw < t.bitwidth ∧ t.bitwidth ≤ 64)
      let x ← Veir.Puddle.MatchProg.value opType
      let _ ← Veir.Puddle.MatchProg.root (.llvm llvmOp) #[x] #[resType]
      return (resType, x))
    (fun (resType, x) => do
      let regType ← Veir.Puddle.CreateProg.type (RegisterType.mk none)
      let castProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[x] #[regType] castProps
      let riscvOpProps ← Veir.Puddle.CreateProg.property (.riscv riscvOp) riscvProps
      let riscvResOp ← Veir.Puddle.CreateProg.operation (.riscv riscvOp)
          #[castOp.res[0]!] #[regType] riscvOpProps
      let castBackProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castBackOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[riscvResOp.res[0]!] #[resType] castBackProps
      return castBackOp)
    (fun castBackOp => castBackOp)


/-- Extend i8 to any wider integer fitting in a register. -/
def sext8 : Pattern OpCode := lowerExt .sext 8 .sextb ()

theorem sext8_valid : sext8.Valid := by
  simp only [sext8, lowerExt]
  provePuddleValid
  rintro _ ⟨sw⟩ rfl hsw _ ⟨dw⟩ rfl hdw hupper value hv properties result hop
  dsimp only at hsw hdw hupper
  subst sw
  obtain ⟨x, rfl⟩ := conformsInteger hv
  have hlt : ¬ dw ≤ 8 := by omega
  simpISel
  simp [show ¬ dw ≤ 8 from by omega] at hop
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases x with
  | poison => trivial
  | val x =>
    have hr : (Data.RISCV.sextb (LLVM.Int.toReg (.val x))).val = x.signExtend 64 := by
      veir_bv_decide
    simp only [Data.LLVM.Int.sext, Id.run]
    simp [isRefinedBy, RISCV.Reg.toInt, hr, resize_signExtend x hupper]

/-- Extend i16 to any wider integer fitting in a register. -/
def sext16 : Pattern OpCode := lowerExt .sext 16 .sexth ()

theorem sext16_valid : sext16.Valid := by
  simp only [sext16, lowerExt]
  provePuddleValid
  rintro _ ⟨sw⟩ rfl hsw _ ⟨dw⟩ rfl hdw hupper value hv properties result hop
  dsimp only at hsw hdw hupper
  subst sw
  obtain ⟨x, rfl⟩ := conformsInteger hv
  have hlt : ¬ dw ≤ 16 := by omega
  simpISel
  simp [show ¬ dw ≤ 16 from by omega] at hop
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases x with
  | poison => trivial
  | val x =>
    have hr : (Data.RISCV.sexth (LLVM.Int.toReg (.val x))).val = x.signExtend 64 := by
      veir_bv_decide
    simp only [Data.LLVM.Int.sext, Id.run]
    simp [isRefinedBy, RISCV.Reg.toInt, hr, resize_signExtend x hupper]

/-- Extend i32 to any wider integer fitting in a register. -/
def sext32 : Pattern OpCode := lowerExt .sext 32 .sextw ()

theorem sext32_valid : sext32.Valid := by
  simp only [sext32, lowerExt]
  provePuddleValid
  rintro _ ⟨sw⟩ rfl hsw _ ⟨dw⟩ rfl hdw hupper value hv properties result hop
  dsimp only at hsw hdw hupper
  subst sw
  obtain ⟨x, rfl⟩ := conformsInteger hv
  have hlt : ¬ dw ≤ 32 := by omega
  simpISel
  simp [show ¬ dw ≤ 32 from by omega] at hop
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases x with
  | poison => trivial
  | val x =>
    have hr : (Data.RISCV.sextw (LLVM.Int.toReg (.val x))).val = x.signExtend 64 := by
      veir_bv_decide
    simp only [Data.LLVM.Int.sext, Id.run]
    simp [isRefinedBy, RISCV.Reg.toInt, hr, resize_signExtend x hupper]

private theorem zextb_value (x : BitVec 8) :
    (Data.RISCV.zextb (LLVM.Int.toReg (.val x))).val = x.setWidth 64 := by
  veir_bv_decide

/-- Extend i8 to any wider integer fitting in a register. -/
def zext8 : Pattern OpCode := lowerExt .zext 8 .zextb ()

theorem zext8_valid : zext8.Valid := by
  simp only [zext8, lowerExt]
  provePuddleValid
  rintro _ ⟨sw⟩ rfl hsw _ ⟨dw⟩ rfl hdw hupper value hv properties result hop
  dsimp only at hsw hdw hupper
  subst sw
  obtain ⟨x, rfl⟩ := conformsInteger hv
  have hlt : ¬ dw ≤ 8 := by omega
  simpISel
  simp [show ¬ dw ≤ 8 from by omega] at hop
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases x with
  | poison => trivial
  | val x =>
    have hr : (Data.RISCV.zextb (LLVM.Int.toReg (.val x))).val = x.setWidth 64 := by
      exact zextb_value x
    simp only [Data.LLVM.Int.zext, Id.run, pure]
    split
    · trivial
    · simp [isRefinedBy, RISCV.Reg.toInt, hr, BitVec.setWidth_setWidth_of_le x hupper]

/-- Extend i16 to any wider integer fitting in a register. -/
def zext16 : Pattern OpCode := lowerExt .zext 16 .zexth ()

theorem zext16_valid : zext16.Valid := by
  simp only [zext16, lowerExt]
  provePuddleValid
  rintro _ ⟨sw⟩ rfl hsw _ ⟨dw⟩ rfl hdw hupper value hv properties result hop
  dsimp only at hsw hdw hupper
  subst sw
  obtain ⟨x, rfl⟩ := conformsInteger hv
  have hlt : ¬ dw ≤ 16 := by omega
  simpISel
  simp [show ¬ dw ≤ 16 from by omega] at hop
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases x with
  | poison => trivial
  | val x =>
    have hr : (Data.RISCV.zexth (LLVM.Int.toReg (.val x))).val = x.setWidth 64 := by
      veir_bv_decide
    simp only [Data.LLVM.Int.zext, Id.run, pure]
    split
    · trivial
    · simp [isRefinedBy, RISCV.Reg.toInt, hr, BitVec.setWidth_setWidth_of_le x hupper]

/-- Extend i32 to any wider integer fitting in a register. -/
def zext32 : Pattern OpCode := lowerExt .zext 32 .zextw ()

theorem zext32_valid : zext32.Valid := by
  simp only [zext32, lowerExt]
  provePuddleValid
  rintro _ ⟨sw⟩ rfl hsw _ ⟨dw⟩ rfl hdw hupper value hv properties result hop
  dsimp only at hsw hdw hupper
  subst sw
  obtain ⟨x, rfl⟩ := conformsInteger hv
  have hlt : ¬ dw ≤ 32 := by omega
  simpISel
  simp [show ¬ dw ≤ 32 from by omega] at hop
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases x with
  | poison => trivial
  | val x =>
    have hr : (Data.RISCV.zextw (LLVM.Int.toReg (.val x))).val = x.setWidth 64 := by
      veir_bv_decide
    simp only [Data.LLVM.Int.zext, Id.run, pure]
    split
    · trivial
    · simp [isRefinedBy, RISCV.Reg.toInt, hr, BitVec.setWidth_setWidth_of_le x hupper]

/-- LLVM decodes the attribute at its own width; i1 is zero-extended. -/
def decodedConstant (attr : IntegerAttr) : Int :=
  if attr.type.bitwidth = 1 then (BitVec.ofInt 1 attr.value).toNat
  else (BitVec.ofInt attr.type.bitwidth attr.value).toInt

private def constantBits (attr : IntegerAttr) (w : Nat) : BitVec w :=
  if attr.type.bitwidth = 1 then (BitVec.ofInt attr.type.bitwidth attr.value).setWidth w
  else (BitVec.ofInt attr.type.bitwidth attr.value).signExtend w

/-- Corrected constant lowering, indexed by the matched attribute and result width. -/
def constant (attr : IntegerAttr) (w : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == w)
      let _ ← MatchProg.root (.llvm .mlir__constant) #[] #[ty]
        (fun p => p.value == .integer attr)
      return ty)
    (fun ty => do
      let r ← emit .li #[] (RISCVImmediateProperties.mk
        (BitVec.ofInt 64 (decodedConstant attr)))
      castValue r ty)
    (fun result => result)

theorem constant_valid (attr : IntegerAttr) (w : Nat) (hw : w ≤ 64) :
    (constant attr w).Valid := by
  simp only [constant, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth properties result hp hop
  dsimp only at hwidth
  subst bw
  change LLVMConstantProperties at properties
  obtain ⟨prop⟩ := properties
  dsimp at hp
  subst prop
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const, isRefinedBy, RISCV.Reg.toInt, Data.RISCV.li]
  by_cases h : attr.type.bitwidth = 1
  · simp only [decodedConstant, decodeLLVMIntegerConstant, h, ↓reduceIte, BitVec.ofInt_natCast]
    simp only [BitVec.zeroExtend, BitVec.setWidth_ofNat_of_le hw]
  · simp only [decodedConstant, decodeLLVMIntegerConstant, h, ↓reduceIte]
    change (BitVec.ofInt attr.type.bitwidth attr.value).signExtend w =
      ((BitVec.ofInt attr.type.bitwidth attr.value).signExtend 64).setWidth w
    exact (resize_signExtend _ hw).symm

/-- The old constant sequence returns 255 although the source returns -1. -/
theorem constant_raw_attribute_counterexample :
    ¬ ((Data.LLVM.Int.val ((255#8).signExtend 64)) ⊒
      RISCV.Reg.toInt (Data.RISCV.li (255#64)) 64) := by
  cbv
  decide

/-- An i1 -1 attribute is decoded as 1, not as a rotate amount of 63. -/
theorem fshrConst_raw_attribute_counterexample :
    ¬ ((Data.LLVM.Int.fshr (.val (1#64)) (.val (1#64)) (.val (1#64))) ⊒
      RISCV.Reg.toInt (Data.RISCV.rori (63#6) ⟨1#64⟩) 64) := by
  cbv
  decide

theorem fshlConst_raw_attribute_counterexample :
    ¬ ((Data.LLVM.Int.fshl (.val (1#64)) (.val (1#64)) (.val (1#64))) ⊒
      RISCV.Reg.toInt (Data.RISCV.rori (1#6) ⟨1#64⟩) 64) := by
  cbv
  decide

/-- Lower poison to a concrete zero, at every integer width. -/
def poisonConst : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let _ ← MatchProg.root (.llvm .mlir__poison) #[] #[ty]
      return ty)
    (fun ty => do
      let r ← emit .li #[] (RISCVImmediateProperties.mk (BitVec.ofInt 64 0))
      castValue r ty)
    (fun result => result)

theorem poisonConst_valid : poisonConst.Valid := by
  simp only [poisonConst, emit, castValue]
  provePuddleValid
  intro type properties result hop
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp [Data.LLVM.Int.mlir_poison, isRefinedBy]

/-- All ten integer predicates, with sign extension for narrow comparisons. -/
def icmp (w : Nat) (pred : Data.LLVM.IntPred) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == w)
      let i1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .icmp) #[a, b] #[i1] (fun p => p.predicate == pred)
      return (i1, a, b))
    (fun (i1, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let ac ← castValue a reg
      let bc ← castValue b reg
      let (a, b) ←
        if w = 32 then do
          let a ← emit .sextw #[ac.res[0]!] ()
          let b ← emit .sextw #[bc.res[0]!] ()
          pure (a, b)
        else if w = 8 then do
          let a ← emit .sextb #[ac.res[0]!] ()
          let b ← emit .sextb #[bc.res[0]!] ()
          pure (a, b)
        else pure (ac.res[0]!, bc.res[0]!)
      let one := RISCVImmediateProperties.mk (BitVec.ofInt 64 1)
      let r ← match pred with
        | .eq => do
          let x ← emit .xor #[b, a] ()
          emit .sltiu #[x] one
        | .ne => do
          let x ← emit .xor #[b, a] ()
          let z ← emit .li #[] (RISCVImmediateProperties.mk (BitVec.ofInt 64 0))
          emit .sltu #[z, x] ()
        | .slt => emit .slt #[a, b] ()
        | .sgt => emit .slt #[b, a] ()
        | .ult => emit .sltu #[a, b] ()
        | .ugt => emit .sltu #[b, a] ()
        | .sge => do
          let x ← emit .slt #[a, b] ()
          emit .xori #[x] one
        | .sle => do
          let x ← emit .slt #[b, a] ()
          emit .xori #[x] one
        | .uge => do
          let x ← emit .sltu #[a, b] ()
          emit .xori #[x] one
        | .ule => do
          let x ← emit .sltu #[b, a] ()
          emit .xori #[x] one
      castValue r i1)
    (fun result => result)

theorem icmp64_eq_valid : (icmp 64 .eq).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_eq (x := a) (y := b))


theorem icmp64_ne_valid : (icmp 64 .ne).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_ne (x := a) (y := b))


theorem icmp64_slt_valid : (icmp 64 .slt).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_slt (x := a) (y := b))


theorem icmp64_sle_valid : (icmp 64 .sle).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_sle (x := a) (y := b))


theorem icmp64_sgt_valid : (icmp 64 .sgt).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_sgt (x := a) (y := b))


theorem icmp64_sge_valid : (icmp 64 .sge).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_sge (x := a) (y := b))


theorem icmp64_ult_valid : (icmp 64 .ult).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_ult (x := a) (y := b))


theorem icmp64_ule_valid : (icmp 64 .ule).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_ule (x := a) (y := b))


theorem icmp64_ugt_valid : (icmp 64 .ugt).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_ugt (x := a) (y := b))


theorem icmp64_uge_valid : (icmp 64 .uge).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_uge (x := a) (y := b))


theorem icmp32_eq_valid : (icmp 32 .eq).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_eq_32 (x := a) (y := b))


theorem icmp32_ne_valid : (icmp 32 .ne).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_ne_32 (x := a) (y := b))


theorem icmp32_slt_valid : (icmp 32 .slt).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_slt_32 (x := a) (y := b))


theorem icmp32_sle_valid : (icmp 32 .sle).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_sle_32 (x := a) (y := b))


theorem icmp32_sgt_valid : (icmp 32 .sgt).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_sgt_32 (x := a) (y := b))


theorem icmp32_sge_valid : (icmp 32 .sge).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_sge_32 (x := a) (y := b))


theorem icmp32_ult_valid : (icmp 32 .ult).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_ult_32 (x := a) (y := b))


theorem icmp32_ule_valid : (icmp 32 .ule).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_ule_32 (x := a) (y := b))


theorem icmp32_ugt_valid : (icmp 32 .ugt).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_ugt_32 (x := a) (y := b))


theorem icmp32_uge_valid : (icmp 32 .uge).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_uge_32 (x := a) (y := b))


theorem icmp8_eq_valid : (icmp 8 .eq).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_eq_8 (x := a) (y := b))


theorem icmp8_ne_valid : (icmp 8 .ne).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_ne_8 (x := a) (y := b))


theorem icmp8_slt_valid : (icmp 8 .slt).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_slt_8 (x := a) (y := b))


theorem icmp8_sle_valid : (icmp 8 .sle).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_sle_8 (x := a) (y := b))


theorem icmp8_sgt_valid : (icmp 8 .sgt).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_sgt_8 (x := a) (y := b))


theorem icmp8_sge_valid : (icmp 8 .sge).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_sge_8 (x := a) (y := b))


theorem icmp8_ult_valid : (icmp 8 .ult).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_ult_8 (x := a) (y := b))


theorem icmp8_ule_valid : (icmp 8 .ule).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_ule_8 (x := a) (y := b))


theorem icmp8_ugt_valid : (icmp 8 .ugt).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_ugt_8 (x := a) (y := b))


theorem icmp8_uge_valid : (icmp 8 .uge).Valid := by
  simp only [icmp, emit, castValue]
  proveLargeISelValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha b hb properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa [Data.RISCV.xor, BitVec.xor_comm] using (Data.RISCV.icmp_refinement_uge_8 (x := a) (y := b))


theorem icmp_valid (w : Nat) (pred : Data.LLVM.IntPred)
    (hw : w = 64 ∨ w = 32 ∨ w = 8) : (icmp w pred).Valid := by
  rcases hw with rfl | rfl | rfl <;> cases pred
  all_goals first
    | exact icmp64_eq_valid
    | exact icmp64_ne_valid
    | exact icmp64_slt_valid
    | exact icmp64_sle_valid
    | exact icmp64_sgt_valid
    | exact icmp64_sge_valid
    | exact icmp64_ult_valid
    | exact icmp64_ule_valid
    | exact icmp64_ugt_valid
    | exact icmp64_uge_valid
    | exact icmp32_eq_valid
    | exact icmp32_ne_valid
    | exact icmp32_slt_valid
    | exact icmp32_sle_valid
    | exact icmp32_sgt_valid
    | exact icmp32_sge_valid
    | exact icmp32_ult_valid
    | exact icmp32_ule_valid
    | exact icmp32_ugt_valid
    | exact icmp32_uge_valid
    | exact icmp8_eq_valid
    | exact icmp8_ne_valid
    | exact icmp8_slt_valid
    | exact icmp8_sle_valid
    | exact icmp8_sgt_valid
    | exact icmp8_sge_valid
    | exact icmp8_ult_valid
    | exact icmp8_ule_valid
    | exact icmp8_ugt_valid
    | exact icmp8_uge_valid

private theorem matchedConstant {type : IntegerType} {properties : LLVMConstantProperties}
    {constant : Int} {result : RuntimeValue}
    (hmatch : (match properties.value with
      | .integer value => decodedConstant value == constant
      | _ => false) = true)
    (hop : InterpretsTo (.llvm .mlir__constant) properties #[type] #[] #[result]) :
    result = .int type.bitwidth (Data.LLVM.Int.constant type.bitwidth constant) := by
  obtain ⟨property⟩ := properties
  cases property <;> simp only at hmatch
  all_goals try contradiction
  rename_i attr
  simp only [beq_iff_eq] at hmatch
  have hop := hop.2 MemoryState.empty
  simp [interpretOp', Llvm.interpretOp', pure] at hop
  change RuntimeValue.int type.bitwidth
    (Data.LLVM.Int.constant type.bitwidth (decodedConstant attr)) = result at hop
  simpa only [hmatch] using hop.symm

/-- Match an LLVM integer constant by its decoded value, including attribute-width truncation. -/
private def matchConstant (returnType : Handle OpCode .type) (constant : Int) :
    MatchProg.Builder (Handle OpCode .value) := do
  let op ← MatchProg.operation (.llvm .mlir__constant) #[] #[returnType]
    (fun properties =>
      match properties.value with
      | .integer value => decodedConstant value == constant
      | _ => false)
  return op.res[0]!


/-- Branchless select; the zero-arm variants omit one conditional-zero instruction. -/
def selectGeneral (w : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == w)
      let i1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let c ← MatchProg.value i1
      let a ← MatchProg.value ty
      let b ← MatchProg.value ty
      let _ ← MatchProg.root (.llvm .select) #[c, a, b] #[ty]
      return (ty, c, a, b))
    (fun (ty, c, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let cc ← castValue c reg
      let c := cc.res[0]!
      let ac ← castValue a reg
      let a := ac.res[0]!
      let bc ← castValue b reg
      let b := bc.res[0]!
      let t ← emit .czeroeqz #[a, c] ()
      let f ← emit .czeronez #[b, c] ()
      let r ← emit .or #[t, f] ()
      castValue r ty)
    (fun result => result)

theorem selectGeneral_valid (w : Nat) (hw : w = 64 ∨ w = 32 ∨ w = 1) :
    (selectGeneral w).Valid := by
  rcases hw with rfl | rfl | rfl
  all_goals
    simp only [selectGeneral, emit, castValue]
    proveLargeISelValid
    rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone c hc a ha b hb properties result hop
    dsimp only at hwidth hone
    subst bw one
    obtain ⟨c, rfl⟩ := conformsInteger hc
    obtain ⟨a, rfl⟩ := conformsInteger ha
    obtain ⟨b, rfl⟩ := conformsInteger hb
    simpISel
    rw [← hop.2 MemoryState.empty]
    simp only [Data.LLVM.Int.cast_self, exists_const]
    veir_bv_decide

/-- Branchless select; the zero-arm variants omit one conditional-zero instruction. -/
def selectCzeroeqz (w : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == w)
      let i1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let c ← MatchProg.value i1
      let a ← MatchProg.value ty
      let z ← matchConstant ty 0
      let _ ← MatchProg.root (.llvm .select) #[c, a, z] #[ty]
      return (ty, c, a))
    (fun (ty, c, a) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let cc ← castValue c reg
      let c := cc.res[0]!
      let ac ← castValue a reg
      let a := ac.res[0]!
      let r ← emit .czeroeqz #[a, c] ()
      castValue r ty)
    (fun result => result)

theorem selectCzeroeqz_valid (w : Nat) (hw : w = 64 ∨ w = 32) :
    (selectCzeroeqz w).Valid := by
  rcases hw with rfl | rfl
  all_goals
    simp only [selectCzeroeqz, emit, castValue, matchConstant]
    proveLargeISelValid
    rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone c hc a ha cp z hcz hz properties result hop
    dsimp only at hwidth hone
    subst bw one
    obtain ⟨c, rfl⟩ := conformsInteger hc
    obtain ⟨a, rfl⟩ := conformsInteger ha
    obtain rfl := matchedConstant hcz hz
    simpISel
    rw [← hop.2 MemoryState.empty]
    simp only [Data.LLVM.Int.cast_self, exists_const]
    veir_bv_decide

/-- Branchless select; the zero-arm variants omit one conditional-zero instruction. -/
def selectCzeronez (w : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == w)
      let i1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let c ← MatchProg.value i1
      let a ← MatchProg.value ty
      let z ← matchConstant ty 0
      let _ ← MatchProg.root (.llvm .select) #[c, z, a] #[ty]
      return (ty, c, a))
    (fun (ty, c, a) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let cc ← castValue c reg
      let c := cc.res[0]!
      let ac ← castValue a reg
      let a := ac.res[0]!
      let r ← emit .czeronez #[a, c] ()
      castValue r ty)
    (fun result => result)

theorem selectCzeronez_valid (w : Nat) (hw : w = 64 ∨ w = 32) :
    (selectCzeronez w).Valid := by
  rcases hw with rfl | rfl
  all_goals
    simp only [selectCzeronez, emit, castValue, matchConstant]
    proveLargeISelValid
    rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone c hc a ha cp z hcz hz properties result hop
    dsimp only at hwidth hone
    subst bw one
    obtain ⟨c, rfl⟩ := conformsInteger hc
    obtain ⟨a, rfl⟩ := conformsInteger ha
    obtain rfl := matchedConstant hcz hz
    simpISel
    rw [← hop.2 MemoryState.empty]
    simp only [Data.LLVM.Int.cast_self, exists_const]
    veir_bv_decide

private theorem conformsByte {type : Veir.LLVM.ByteType} {value : RuntimeValue}
    (h : value.Conforms (type : TypeAttr)) :
    ∃ x, value = .byte type.bitwidth x := RuntimeValue.Conforms.byteType h

/-- Truncate through a register; the family includes all source width pairs. -/
def truncInt (src dst : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let st ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == src)
      let dt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == dst)
      let x ← MatchProg.value st
      let _ ← MatchProg.root (.llvm .trunc) #[x] #[dt]
      return (dt, x))
    (fun (dt, x) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let x ← castValue x reg
      castValue x.res[0]! dt)
    (fun result => result)

theorem truncInt_valid (src dst : Nat) (hlt : dst < src) (hs : src ≤ 64) :
    (truncInt src dst).Valid := by
  simp only [truncInt, castValue]
  provePuddleValid
  rintro _ ⟨sw⟩ rfl hsw _ ⟨dw⟩ rfl hdw value hv properties result hop
  dsimp only at hsw hdw
  subst sw dw
  obtain ⟨x, rfl⟩ := conformsInteger hv
  simpISel
  simp [show ¬ dst ≥ src from by omega] at hop
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases x <;> simp [Data.LLVM.Int.trunc, Id.run, pure, LLVM.Int.toReg,
    RISCV.Reg.toInt, isRefinedBy, BitVec.setWidth_setWidth_of_le _ (by omega : dst ≤ 64)]
  all_goals grind
  all_goals grind

/-- Truncate through a register; the family includes all source width pairs. -/
def truncByte (src dst : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let st ← MatchProg.type (Attr := Veir.LLVM.ByteType) (fun t => t.bitwidth == src)
      let dt ← MatchProg.type (Attr := Veir.LLVM.ByteType) (fun t => t.bitwidth == dst)
      let x ← MatchProg.value st
      let _ ← MatchProg.root (.llvm .trunc) #[x] #[dt]
      return (dt, x))
    (fun (dt, x) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let x ← castValue x reg
      castValue x.res[0]! dt)
    (fun result => result)

theorem truncByte_valid (src dst : Nat) (hlt : dst < src) (hs : src ≤ 64) :
    (truncByte src dst).Valid := by
  simp only [truncByte, castValue]
  provePuddleValid
  rintro _ ⟨sw⟩ rfl hsw _ ⟨dw⟩ rfl hdw value hv properties result hop
  dsimp only at hsw hdw
  subst sw dw
  obtain ⟨x, rfl⟩ := conformsByte hv
  simpISel
  simp [show ¬ dst ≥ src from by omega] at hop
  rw [← hop.2 MemoryState.empty]
  simp [Data.LLVM.Byte.cast_self, Data.LLVM.Byte.trunc, LLVM.Byte.toReg,
    RISCV.Reg.toByte, BitVec.setWidth_setWidth_of_le _ (by omega : dst ≤ 64)]

  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp
  bv_decide

private theorem shlByte64_refinement (a : LLVM.Byte 64) (b : LLVM.Int 64) (ex : Bool) :
  (a.shl b ex).isRefinedBy (RISCV.Reg.toByte (RISCV.sll (LLVM.Int.toReg b) (LLVM.Byte.toReg a)) 64) := by
  cases b with
  | poison =>
    simp only [LLVM.Byte.shl, Id.run, LLVM.Byte.allPoison, LLVM.Byte.isRefinedBy]
    bv_decide
  | val b =>
    simp only [LLVM.Byte.shl, Id.run, pure]
    repeat' split
    all_goals try (simp only [LLVM.Byte.allPoison, LLVM.Byte.isRefinedBy]; bv_decide)
    all_goals
      have hb : b.toNat < 64 := by
        simp_all [BitVec.le_def]
      simp only [LLVM.Byte.isRefinedBy, LLVM.Byte.toReg,
        LLVM.Int.toReg, RISCV.Reg.toByte, RISCV.sll]
      simp [Nat.mod_eq_of_lt hb]
      bv_decide

private theorem lshrByte64_refinement (a : LLVM.Byte 64) (b : LLVM.Int 64) (ex : Bool) :
  (a.lshr b ex).isRefinedBy (RISCV.Reg.toByte (RISCV.srl (LLVM.Int.toReg b) (LLVM.Byte.toReg a)) 64) := by
  simp only [LLVM.Byte.lshr]
  split
  · simp only [LLVM.Byte.allPoison, LLVM.Byte.isRefinedBy]
    bv_decide
  · split
    · simp only [LLVM.Byte.allPoison, LLVM.Byte.isRefinedBy]
      bv_decide
    · split
      · simp only [LLVM.Byte.allPoison, LLVM.Byte.isRefinedBy]
        bv_decide
      · cases b with
        | poison => simp [LLVM.Int.isPoison] at *
        | val b =>
          have hb : b.toNat < 64 := by
            rename_i h _ _
            simpa [LLVM.Int.isPoison, LLVM.Int.getValueD, BitVec.le_def] using h
          simp only [LLVM.Byte.isRefinedBy, LLVM.Int.getValueD, LLVM.Byte.toReg,
            LLVM.Int.toReg, RISCV.Reg.toByte, RISCV.srl]
          simp [Nat.mod_eq_of_lt hb]
          bv_decide

private theorem shlByte32_refinement (a : LLVM.Byte 32) (b : LLVM.Int 32) (ex : Bool) :
  (a.shl b ex).isRefinedBy (RISCV.Reg.toByte (RISCV.sllw (LLVM.Int.toReg b) (LLVM.Byte.toReg a)) 32) := by
  cases b with
  | poison =>
    simp only [LLVM.Byte.shl, Id.run, LLVM.Byte.allPoison, LLVM.Byte.isRefinedBy]
    bv_decide
  | val b =>
    simp only [LLVM.Byte.shl, Id.run, pure]
    repeat' split
    all_goals try (simp only [LLVM.Byte.allPoison, LLVM.Byte.isRefinedBy]; bv_decide)
    all_goals
      have hb : b.toNat < 32 := by
        simp_all [BitVec.le_def]
      simp only [LLVM.Byte.isRefinedBy, LLVM.Byte.toReg,
        LLVM.Int.toReg, RISCV.Reg.toByte, RISCV.sllw]
      simp [Nat.mod_eq_of_lt hb]
      bv_decide

private theorem lshrByte32_refinement (a : LLVM.Byte 32) (b : LLVM.Int 32) (ex : Bool) :
  (a.lshr b ex).isRefinedBy (RISCV.Reg.toByte (RISCV.srlw (LLVM.Int.toReg b) (LLVM.Byte.toReg a)) 32) := by
  simp only [LLVM.Byte.lshr]
  split
  · simp only [LLVM.Byte.allPoison, LLVM.Byte.isRefinedBy]
    bv_decide
  · split
    · simp only [LLVM.Byte.allPoison, LLVM.Byte.isRefinedBy]
      bv_decide
    · split
      · simp only [LLVM.Byte.allPoison, LLVM.Byte.isRefinedBy]
        bv_decide
      · cases b with
        | poison => simp [LLVM.Int.isPoison] at *
        | val b =>
          have hb : b.toNat < 32 := by
            rename_i h _ _
            simpa [LLVM.Int.isPoison, LLVM.Int.getValueD, BitVec.le_def] using h
          simp only [LLVM.Byte.isRefinedBy, LLVM.Int.getValueD, LLVM.Byte.toReg,
            LLVM.Int.toReg, RISCV.Reg.toByte, RISCV.srlw]
          simp [Nat.mod_eq_of_lt hb]
          bv_decide

def shlByte64 : Pattern OpCode :=
  Pattern.Builder
    (do
      let bt ← MatchProg.type (Attr := Veir.LLVM.ByteType) (fun t => t.bitwidth == 64)
      let it ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value bt
      let b ← MatchProg.value it
      let _ ← MatchProg.root (.llvm .shl) #[a, b] #[bt]
      return (bt, a, b))
    (fun (bt, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let a ← castValue a reg
      let b ← castValue b reg
      let r ← emit .sll #[a.res[0]!, b.res[0]!] ()
      castValue r bt)
    (fun result => result)

theorem shlByte64_valid : shlByte64.Valid := by
  simp only [shlByte64, castValue, emit]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hbw _ ⟨iw⟩ rfl hiw a ha b hshift properties result hop
  dsimp only at hbw hiw
  subst bw iw
  obtain ⟨a, rfl⟩ := conformsByte ha
  obtain ⟨b, rfl⟩ := conformsInteger hshift
  simpISel
  have hop := hop.2 MemoryState.empty
  split at hop <;> simp_all
  rw [← hop]
  simp only [Data.LLVM.Byte.cast_self, exists_const]
  exact shlByte64_refinement a b properties.nuw

def shlByte32 : Pattern OpCode :=
  Pattern.Builder
    (do
      let bt ← MatchProg.type (Attr := Veir.LLVM.ByteType) (fun t => t.bitwidth == 32)
      let it ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
      let a ← MatchProg.value bt
      let b ← MatchProg.value it
      let _ ← MatchProg.root (.llvm .shl) #[a, b] #[bt]
      return (bt, a, b))
    (fun (bt, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let a ← castValue a reg
      let b ← castValue b reg
      let r ← emit .sllw #[a.res[0]!, b.res[0]!] ()
      castValue r bt)
    (fun result => result)

theorem shlByte32_valid : shlByte32.Valid := by
  simp only [shlByte32, castValue, emit]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hbw _ ⟨iw⟩ rfl hiw a ha b hshift properties result hop
  dsimp only at hbw hiw
  subst bw iw
  obtain ⟨a, rfl⟩ := conformsByte ha
  obtain ⟨b, rfl⟩ := conformsInteger hshift
  simpISel
  have hop := hop.2 MemoryState.empty
  split at hop <;> simp_all
  rw [← hop]
  simp only [Data.LLVM.Byte.cast_self, exists_const]
  exact shlByte32_refinement a b properties.nuw

def lshrByte64 : Pattern OpCode :=
  Pattern.Builder
    (do
      let bt ← MatchProg.type (Attr := Veir.LLVM.ByteType) (fun t => t.bitwidth == 64)
      let it ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value bt
      let b ← MatchProg.value it
      let _ ← MatchProg.root (.llvm .lshr) #[a, b] #[bt]
      return (bt, a, b))
    (fun (bt, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let a ← castValue a reg
      let b ← castValue b reg
      let r ← emit .srl #[a.res[0]!, b.res[0]!] ()
      castValue r bt)
    (fun result => result)

theorem lshrByte64_valid : lshrByte64.Valid := by
  simp only [lshrByte64, castValue, emit]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hbw _ ⟨iw⟩ rfl hiw a ha b hshift properties result hop
  dsimp only at hbw hiw
  subst bw iw
  obtain ⟨a, rfl⟩ := conformsByte ha
  obtain ⟨b, rfl⟩ := conformsInteger hshift
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Byte.cast_self, exists_const]
  exact lshrByte64_refinement a b properties.exact

def lshrByte32 : Pattern OpCode :=
  Pattern.Builder
    (do
      let bt ← MatchProg.type (Attr := Veir.LLVM.ByteType) (fun t => t.bitwidth == 32)
      let it ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
      let a ← MatchProg.value bt
      let b ← MatchProg.value it
      let _ ← MatchProg.root (.llvm .lshr) #[a, b] #[bt]
      return (bt, a, b))
    (fun (bt, a, b) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let a ← castValue a reg
      let b ← castValue b reg
      let r ← emit .srlw #[a.res[0]!, b.res[0]!] ()
      castValue r bt)
    (fun result => result)

theorem lshrByte32_valid : lshrByte32.Valid := by
  simp only [lshrByte32, castValue, emit]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hbw _ ⟨iw⟩ rfl hiw a ha b hshift properties result hop
  dsimp only at hbw hiw
  subst bw iw
  obtain ⟨a, rfl⟩ := conformsByte ha
  obtain ⟨b, rfl⟩ := conformsInteger hshift
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Byte.cast_self, exists_const]
  exact lshrByte32_refinement a b properties.exact

/-- Match the actual result bits of an integer constant, including attribute truncation. -/
private def matchBits (ty : Handle OpCode .type) (bits : BitVec w) :
    MatchProg.Builder (Handle OpCode .value) := do
  let c ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    (fun p => match p.value with
      | .integer attr => constantBits attr w == bits
      | _ => false)
  return c.res[0]!

private theorem matchedBits {ty : IntegerType} {bits : BitVec ty.bitwidth}
    {p : LLVMConstantProperties} {v : RuntimeValue}
    (hp : (match p.value with
      | .integer attr => constantBits attr ty.bitwidth == bits
      | _ => false) = true)
    (hop : InterpretsTo (.llvm .mlir__constant) p #[ty] #[] #[v]) :
    v = .int ty.bitwidth (.val bits) := by
  obtain ⟨p⟩ := p
  cases p <;> simp only at hp
  all_goals try contradiction
  rename_i attr
  simp only [beq_iff_eq] at hp
  have hop := hop.2 MemoryState.empty
  simp [interpretOp', Llvm.interpretOp', pure] at hop
  rw [← hop, ← hp]
  by_cases h : attr.type.bitwidth = 1
  · simp only [constantBits, decodeLLVMIntegerConstant, h, ↓reduceIte,
      BitVec.ofInt_natCast]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp [h]
  · simp only [constantBits, decodeLLVMIntegerConstant, h, ↓reduceIte]
    rfl

/-- Corrected immediate rotate; the matcher checks decoded constant bits. -/
private def fshlConst64Core (bits : BitVec 64) (imm : Int) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let c ← matchBits ty bits
      let _ ← MatchProg.root (.llvm .intr__fshl) #[a, a, c] #[ty]
      return (ty, a))
    (fun (ty, a) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let a ← castValue a reg
      let r ← emit .rori #[a.res[0]!] (RISCVImmediateProperties.mk
        (BitVec.ofInt 64 imm))
      castValue r ty)
    (fun result => result)

private theorem setWidth_ofInt_of_le {n w : Nat} (h : n ≤ w) (value : Int) :
    (BitVec.ofInt w value).setWidth n = BitVec.ofInt n value := by
  cases value with
  | ofNat value => simp [h]
  | negSucc value =>
    change (BitVec.ofInt w (-(↑(value + 1) : Int))).setWidth n =
      BitVec.ofInt n (-(↑(value + 1) : Int))
    simp only [BitVec.ofInt_neg, BitVec.ofInt_natCast,
      BitVec.setWidth_neg_of_le h, BitVec.setWidth_ofNat_of_le h]

private theorem fshlConst64Core_valid (bits : BitVec 64) (imm : Int)
    (himm : BitVec.ofInt 6 imm = (-(bits.extractLsb 5 0))) : (fshlConst64Core bits imm).Valid := by
  simp only [fshlConst64Core, matchBits, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha cp c hc hconst properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain rfl := matchedBits hc hconst
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  rw [setWidth_ofInt_of_le (by decide), himm]
  simpa [LLVM.Int.toReg] using (Data.RISCV.fshl_rori_refinement (a := a) (c := .val bits))

/-- Immediate rotate matched by decoded bits, with its canonical immediate. -/
def fshlConst64 (bits : BitVec 64) : Pattern OpCode :=
  fshlConst64Core bits (-(bits.extractLsb 5 0)).toInt

theorem fshlConst64_valid (bits : BitVec 64) : (fshlConst64 bits).Valid :=
  fshlConst64Core_valid bits _ BitVec.ofInt_toInt

/-- Corrected immediate rotate; the matcher checks decoded constant bits. -/
private def fshrConst64Core (bits : BitVec 64) (imm : Int) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let a ← MatchProg.value ty
      let c ← matchBits ty bits
      let _ ← MatchProg.root (.llvm .intr__fshr) #[a, a, c] #[ty]
      return (ty, a))
    (fun (ty, a) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let a ← castValue a reg
      let r ← emit .rori #[a.res[0]!] (RISCVImmediateProperties.mk
        (BitVec.ofInt 64 imm))
      castValue r ty)
    (fun result => result)

private theorem fshrConst64Core_valid (bits : BitVec 64) (imm : Int)
    (himm : BitVec.ofInt 6 imm = (bits.extractLsb 5 0)) : (fshrConst64Core bits imm).Valid := by
  simp only [fshrConst64Core, matchBits, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha cp c hc hconst properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain rfl := matchedBits hc hconst
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  rw [setWidth_ofInt_of_le (by decide), himm]
  simpa [LLVM.Int.toReg] using (Data.RISCV.fshr_rori_refinement (a := a) (c := .val bits))

/-- Immediate rotate matched by decoded bits, with its canonical immediate. -/
def fshrConst64 (bits : BitVec 64) : Pattern OpCode :=
  fshrConst64Core bits (bits.extractLsb 5 0).toInt

theorem fshrConst64_valid (bits : BitVec 64) : (fshrConst64 bits).Valid :=
  fshrConst64Core_valid bits _ BitVec.ofInt_toInt

/-- Corrected immediate rotate; the matcher checks decoded constant bits. -/
private def fshlConst32Core (bits : BitVec 32) (imm : Int) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
      let a ← MatchProg.value ty
      let c ← matchBits ty bits
      let _ ← MatchProg.root (.llvm .intr__fshl) #[a, a, c] #[ty]
      return (ty, a))
    (fun (ty, a) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let a ← castValue a reg
      let r ← emit .roriw #[a.res[0]!] (RISCVImmediateProperties.mk
        (BitVec.ofInt 64 imm))
      castValue r ty)
    (fun result => result)

private theorem fshlConst32Core_valid (bits : BitVec 32) (imm : Int)
    (himm : BitVec.ofInt 5 imm = (-(bits.extractLsb 4 0))) : (fshlConst32Core bits imm).Valid := by
  simp only [fshlConst32Core, matchBits, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha cp c hc hconst properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain rfl := matchedBits hc hconst
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  rw [setWidth_ofInt_of_le (by decide), himm]
  simpa [LLVM.Int.toReg] using (Data.RISCV.fshl_roriw_refinement (a := a) (c := .val bits))

/-- Immediate rotate matched by decoded bits, with its canonical immediate. -/
def fshlConst32 (bits : BitVec 32) : Pattern OpCode :=
  fshlConst32Core bits (-(bits.extractLsb 4 0)).toInt

theorem fshlConst32_valid (bits : BitVec 32) : (fshlConst32 bits).Valid :=
  fshlConst32Core_valid bits _ BitVec.ofInt_toInt

/-- Corrected immediate rotate; the matcher checks decoded constant bits. -/
private def fshrConst32Core (bits : BitVec 32) (imm : Int) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 32)
      let a ← MatchProg.value ty
      let c ← matchBits ty bits
      let _ ← MatchProg.root (.llvm .intr__fshr) #[a, a, c] #[ty]
      return (ty, a))
    (fun (ty, a) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let a ← castValue a reg
      let r ← emit .roriw #[a.res[0]!] (RISCVImmediateProperties.mk
        (BitVec.ofInt 64 imm))
      castValue r ty)
    (fun result => result)

private theorem fshrConst32Core_valid (bits : BitVec 32) (imm : Int)
    (himm : BitVec.ofInt 5 imm = (bits.extractLsb 4 0)) : (fshrConst32Core bits imm).Valid := by
  simp only [fshrConst32Core, matchBits, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth a ha cp c hc hconst properties result hop
  dsimp only at hwidth
  subst bw
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain rfl := matchedBits hc hconst
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  rw [setWidth_ofInt_of_le (by decide), himm]
  simpa [LLVM.Int.toReg] using (Data.RISCV.fshr_roriw_refinement (a := a) (c := .val bits))

/-- Immediate rotate matched by decoded bits, with its canonical immediate. -/
def fshrConst32 (bits : BitVec 32) : Pattern OpCode :=
  fshrConst32Core bits (bits.extractLsb 4 0).toInt

theorem fshrConst32_valid (bits : BitVec 32) : (fshrConst32 bits).Valid :=
  fshrConst32Core_valid bits _ BitVec.ofInt_toInt

/-- Shared register round trip used by the bitcast lowering. -/
def bitcast (src dst : TypeAttr) : Pattern OpCode :=
  Pattern.Builder
    (do
      let st ← MatchProg.type (Attr := TypeAttr) (· == src)
      let dt ← MatchProg.type (Attr := TypeAttr) (· == dst)
      let x ← MatchProg.value st
      let _ ← MatchProg.root (.llvm .bitcast) #[x] #[dt]
      return (dt, x))
    (fun (dt, x) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let x ← castValue x reg
      castValue x.res[0]! dt)
    (fun result => result)

theorem bitcastIntToInt_valid (w : Nat) (hw : w ≤ 64) :
    (bitcast (IntegerType.mk w) (IntegerType.mk w)).Valid := by
  simp only [bitcast, castValue]
  provePuddleValid
  rintro _ _ rfl rfl _ _ rfl rfl value hv properties result hop
  obtain ⟨x, rfl⟩ := conformsInteger hv
  simpISel
  simp [Attribute.asType] at hop
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases x <;> simp [LLVM.Int.toReg, RISCV.Reg.toInt, isRefinedBy,
    BitVec.setWidth_setWidth_of_le _ hw]

theorem bitcastIntToByte_valid (w : Nat) (hw : w ≤ 64) :
    (bitcast (IntegerType.mk w) (Veir.LLVM.ByteType.mk w)).Valid := by
  simp only [bitcast, castValue]
  provePuddleValid
  rintro _ _ rfl rfl _ _ rfl rfl value hv properties result hop
  obtain ⟨x, rfl⟩ := conformsInteger hv
  simpISel
  simp [Attribute.asType] at hop
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Byte.cast_self, exists_const]
  cases x <;> simp [LLVM.Int.toReg, RISCV.Reg.toByte,
    Data.LLVM.Byte.fromInt, Data.LLVM.Int.isPoison, Data.LLVM.Int.getValue,
    BitVec.setWidth_setWidth_of_le _ hw]
  all_goals
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp

theorem bitcastByteToInt_valid (w : Nat) (hw : w ≤ 64) :
    (bitcast (Veir.LLVM.ByteType.mk w) (IntegerType.mk w)).Valid := by
  simp only [bitcast, castValue]
  provePuddleValid
  rintro _ _ rfl rfl _ _ rfl rfl value hv properties result hop
  obtain ⟨x, rfl⟩ := conformsByte hv
  simpISel
  simp [Attribute.asType] at hop
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simp [Data.LLVM.Byte.toInt, LLVM.Byte.toReg, RISCV.Reg.toInt,
    BitVec.setWidth_setWidth_of_le _ hw]
  split <;> simp_all [isRefinedBy]

theorem bitcastByteToByte_valid (w : Nat) (hw : w ≤ 64) :
    (bitcast (Veir.LLVM.ByteType.mk w) (Veir.LLVM.ByteType.mk w)).Valid := by
  simp only [bitcast, castValue]
  provePuddleValid
  rintro _ _ rfl rfl _ _ rfl rfl value hv properties result hop
  obtain ⟨x, rfl⟩ := conformsByte hv
  simpISel
  simp [Attribute.asType] at hop
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Byte.cast_self, exists_const]
  simp [LLVM.Byte.toReg, RISCV.Reg.toByte, BitVec.setWidth_setWidth_of_le _ hw]
  all_goals
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp

theorem bitcastPtrToPtr_valid :
    (bitcast Veir.LLVM.PointerType.mk Veir.LLVM.PointerType.mk).Valid := by
  simp only [bitcast, castValue]
  provePuddleValid
  rintro _ _ rfl rfl _ _ rfl rfl value hv properties result hop
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.llvmPointerType hv
  simpISel
  simp [Attribute.asType] at hop
  rw [← hop.2 MemoryState.empty]

theorem bitcastPtrToByte_valid :
    (bitcast Veir.LLVM.PointerType.mk (Veir.LLVM.ByteType.mk 64)).Valid := by
  simp only [bitcast, castValue]
  provePuddleValid
  rintro _ _ rfl rfl _ _ rfl rfl value hv properties result hop
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.llvmPointerType hv
  simpISel
  simp [Attribute.asType] at hop
  rw [← hop.2 MemoryState.empty]
  simp [RISCV.Reg.toByte, Data.LLVM.Byte.cast_self]
  bv_decide

/-- Zero-comparison peephole, matching the decoded constant rather than its raw attribute. -/
def icmpZero (w : Nat) (eq : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == w)
      let i1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let a ← MatchProg.value ty
      let b ← matchBits ty (0#w)
      let _ ← MatchProg.root (.llvm .icmp) #[a, b] #[i1]
        (fun p => p.predicate == if eq then .eq else .ne)
      return (i1, a))
    (fun (i1, a) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let ac ← castValue a reg
      let a ← if w = 32 then emit .sextw #[ac.res[0]!] ()
        else if w = 8 then emit .sextb #[ac.res[0]!] ()
        else pure ac.res[0]!
      let r ← if eq then
          emit .sltiu #[a] (RISCVImmediateProperties.mk (BitVec.ofInt 64 1))
        else do
          let z ← emit .li #[] (RISCVImmediateProperties.mk (BitVec.ofInt 64 0))
          emit .sltu #[z, a] ()
      castValue r i1)
    (fun result => result)

theorem icmpZero64_true_valid : (icmpZero 64 true).Valid := by
  simp only [icmpZero, matchBits, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha cp b hc hconst properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain rfl := matchedBits hc hconst
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases a <;> veir_bv_decide

theorem icmpZero64_false_valid : (icmpZero 64 false).Valid := by
  simp only [icmpZero, matchBits, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha cp b hc hconst properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain rfl := matchedBits hc hconst
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases a <;> veir_bv_decide

private theorem icmpZero32_true_refinement (a : LLVM.Int 32) :
    (a.icmp (.val 0#32) .eq) ⊒ (RISCV.Reg.toInt (RISCV.sltiu (1#12) (RISCV.sextw (LLVM.Int.toReg a))) 1) := by
  cases a <;> veir_bv_decide

theorem icmpZero32_true_valid : (icmpZero 32 true).Valid := by
  simp only [icmpZero, matchBits, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha cp b hc hconst properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain rfl := matchedBits hc hconst
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact icmpZero32_true_refinement a

private theorem icmpZero32_false_refinement (a : LLVM.Int 32) :
    (a.icmp (.val 0#32) .ne) ⊒ (RISCV.Reg.toInt (RISCV.sltu (RISCV.sextw (LLVM.Int.toReg a)) (RISCV.li 0#64)) 1) := by
  cases a <;> veir_bv_decide

theorem icmpZero32_false_valid : (icmpZero 32 false).Valid := by
  simp only [icmpZero, matchBits, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha cp b hc hconst properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain rfl := matchedBits hc hconst
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact icmpZero32_false_refinement a

private theorem icmpZero8_true_refinement (a : LLVM.Int 8) :
    (a.icmp (.val 0#8) .eq) ⊒ (RISCV.Reg.toInt (RISCV.sltiu (1#12) (RISCV.sextb (LLVM.Int.toReg a))) 1) := by
  cases a <;> veir_bv_decide

theorem icmpZero8_true_valid : (icmpZero 8 true).Valid := by
  simp only [icmpZero, matchBits, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha cp b hc hconst properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain rfl := matchedBits hc hconst
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact icmpZero8_true_refinement a

private theorem icmpZero8_false_refinement (a : LLVM.Int 8) :
    (a.icmp (.val 0#8) .ne) ⊒ (RISCV.Reg.toInt (RISCV.sltu (RISCV.sextb (LLVM.Int.toReg a)) (RISCV.li 0#64)) 1) := by
  cases a <;> veir_bv_decide

theorem icmpZero8_false_valid : (icmpZero 8 false).Valid := by
  simp only [icmpZero, matchBits, emit, castValue]
  provePuddleValid
  rintro _ ⟨bw⟩ rfl hwidth _ ⟨one⟩ rfl hone a ha cp b hc hconst properties result hp hop
  dsimp only at hwidth hone
  subst bw one
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain rfl := matchedBits hc hconst
  change IcmpProperties at properties
  obtain ⟨p⟩ := properties
  dsimp at hp
  subst p
  simpISel
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  exact icmpZero8_false_refinement a

theorem icmpZero_valid (w : Nat) (eq : Bool) (hw : w = 64 ∨ w = 32 ∨ w = 8) :
    (icmpZero w eq).Valid := by
  rcases hw with rfl | rfl | rfl <;> cases eq
  all_goals first
    | exact icmpZero64_true_valid
    | exact icmpZero64_false_valid
    | exact icmpZero32_true_valid
    | exact icmpZero32_false_valid
    | exact icmpZero8_true_valid
    | exact icmpZero8_false_valid

/-- All six instruction sequences selected by `getelementptr_local`. -/
inductive GepLowering where
  | add | sh1add | sh2add | sh3add
  | shift (immediate : Int)
  | multiply (immediate : Int)

/-- The actual stride encoded by the instruction sequence, modulo the pointer width. -/
def GepLowering.stride : GepLowering → BitVec 64
  | .add => 1
  | .sh1add => 2
  | .sh2add => 4
  | .sh3add => 8
  | .shift k => BitVec.twoPow 64 (BitVec.ofInt 6 k).toNat
  | .multiply k => BitVec.ofInt 64 k

/-- GEP lowering. Its validity uses the interpreter's ABI allocation stride. -/
def getelementptr (elementType : TypeAttr) (lowering : GepLowering) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ptr ← MatchProg.type (Attr := TypeAttr) (· == Veir.LLVM.PointerType.mk)
      let i64 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let base ← MatchProg.value ptr
      let idx ← MatchProg.value i64
      let _ ← MatchProg.root (.llvm .getelementptr) #[base, idx] #[ptr]
        (fun p => (p.elem_type == elementType) && (p.rawConstantIndices.values == #[(-2147483648 : Int)]))
      return (ptr, base, idx))
    (fun (ptr, base, idx) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let pc ← castValue base reg
      let ic ← castValue idx reg
      let p := pc.res[0]!
      let i := ic.res[0]!
      let r ← match lowering with
        | .add => emit .add #[p, i] ()
        | .sh1add => emit .sh1add #[i, p] ()
        | .sh2add => emit .sh2add #[i, p] ()
        | .sh3add => emit .sh3add #[i, p] ()
        | .shift k => do
          let s ← emit .slli #[i] (RISCVImmediateProperties.mk (BitVec.ofInt 64 k))
          emit .add #[p, s] ()
        | .multiply k => do
          let s ← emit .li #[] (RISCVImmediateProperties.mk (BitVec.ofInt 64 k))
          let m ← emit .mul #[i, s] ()
          emit .add #[p, m] ()
      castValue r ptr)
    (fun result => result)

theorem getelementptr_valid (elementType : TypeAttr) (lowering : GepLowering)
    (size : Nat) (hsize : DataLayout.riscv64.getTypeAllocSize elementType.val = some size)
    (hstride : BitVec.ofNat 64 size = lowering.stride) :
    (getelementptr elementType lowering).Valid := by
  cases lowering <;> simp only [getelementptr, emit, castValue]
  all_goals
    provePuddleValid
    rintro _ _ rfl rfl _ ⟨iw⟩ rfl hiw base hb idx hx props result hprops hindices hop
    dsimp only at hiw
    subst iw
    obtain ⟨base, rfl⟩ := RuntimeValue.Conforms.llvmPointerType hb
    obtain ⟨idx, rfl⟩ := conformsInteger hx
    have hs : DataLayout.riscv64.getTypeAllocSize props.elem_type.val = some size := by
      rw [hprops]; exact hsize
    simpISel
    simp [hs] at hop
    have hop := hop.2 MemoryState.empty
    cases idx with
    | poison => simp at hop
    | val idx =>
      simp at hop
      rw [← hop]
      dsimp
      apply UInt64.toBitVec_inj.mp
      change base.toBitVec + idx * BitVec.ofNat 64 size = _
      rw [hstride]
      simp [GepLowering.stride, setWidth_ofInt_of_le (by decide : 6 ≤ 64),
        LLVM.Int.toReg, RISCV.add, RISCV.sh1add,
        RISCV.sh2add, RISCV.sh3add, RISCV.slli, RISCV.mul, RISCV.li,
        BitVec.shiftLeft_eq_mul_twoPow, -BitVec.mul_twoPow_eq_shiftLeft,
        BitVec.add_comm]
      all_goals rfl

/-- The original ABI-stride dispatch, including zero-sized and very large elements. -/
def GepLowering.forScale (scale : Nat) : GepLowering :=
  match scale with
  | 1 => .add
  | 2 => .sh1add
  | 4 => .sh2add
  | 8 => .sh3add
  | _ =>
    if 0 < scale ∧ scale &&& (scale - 1) = 0 ∧ Nat.log2 scale < 64 then
      .shift (Nat.log2 scale)
    else .multiply scale

/-- Select the original GEP instruction sequence and return it with its validity proof.
Returns `none` for unsupported element types or an incompatible ABI stride. -/
def getelementptrChecked (elementType : TypeAttr) : Option {p : Pattern OpCode // p.Valid} :=
  match hsize : DataLayout.riscv64.getTypeAllocSize elementType.val with
  | none => none
  | some size =>
    let lowering := GepLowering.forScale size
    if hstride : BitVec.ofNat 64 size = lowering.stride then
      some ⟨getelementptr elementType lowering,
        getelementptr_valid elementType lowering size hsize hstride⟩
    else none

/-- An i24 has a three-byte type size and a four-byte ABI allocation stride. -/
theorem gep_layout_counterexample :
    DataLayout.riscv64.getTypeSize (.integerType ⟨24⟩) = some 3 ∧
    DataLayout.riscv64.getTypeAllocSize (.integerType ⟨24⟩) = some 4 ∧
    (0 + 1 * 3 : BitVec 64) ≠ (RISCV.sh2add ⟨0⟩ ⟨1⟩).val := by
  decide

/-- With an i8 attribute of 255 used as an i64 index, address folding uses +255
where constant interpretation gives -1. Both offsets fit the signed 12-bit field. -/
theorem folded_address_raw_attribute_counterexample :
    constantBits (IntegerAttr.mk 255 (IntegerType.mk 8)) 64 = BitVec.ofInt 64 (-1) ∧
    (1024#64 + constantBits (IntegerAttr.mk 255 (IntegerType.mk 8)) 64) ≠
      riscvEffectiveAddr 1024#64 255 := by
  cbv
  decide

/-- Direct addressing, or folding a constant-index GEP into a signed 12-bit offset.
The folded port matches decoded bits and uses the interpreter's ABI allocation stride. -/
inductive MemoryAddress where
  | direct
  | folded (elementType : TypeAttr) (index : BitVec 64) (offset : Int)

def MemoryAddress.offset : MemoryAddress → Int
  | .direct => 0
  | .folded _ _ offset => offset

private def matchAddress (pt : Handle OpCode .type) (mode : MemoryAddress) :
    MatchProg.Builder (Handle OpCode .value × Handle OpCode .value) := do
  let base ← MatchProg.value pt
  match mode with
  | .direct => return (base, base)
  | .folded elementType index offset =>
    let it ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
    let idx ← matchBits it index
    let gep ← MatchProg.operation (.llvm .getelementptr) #[base, idx] #[pt]
        (fun p => (p.elem_type == elementType) &&
        (p.rawConstantIndices.values == #[(-2147483648 : Int)]) &&
        match DataLayout.riscv64.getTypeAllocSize p.elem_type.val with
        | some scale => decide (index.toInt * (scale : Int) = offset ∧
            -2048 ≤ offset ∧ offset ≤ 2047)
        | none => false)
    return (gep.res[0]!, base)

/-- Port of load selection, including optional GEP folding and volatility.
Memory operations are outside the current `Pattern.Valid` framework. -/
def load (w : Nat) (volatile : Bool) (address : MemoryAddress := .direct) : Pattern OpCode :=
  Pattern.Builder
    (do
      let pt ← MatchProg.type (Attr := TypeAttr) (· == Veir.LLVM.PointerType.mk)
      let ty ← MatchProg.type (Attr := IntegerType)
        (fun t => (t.bitwidth == w) && decide (w = 64 ∨ w = 32 ∨ w = 8))
      let (ptr, base) ← matchAddress pt address
      let _ ← MatchProg.root (.llvm .load) #[ptr] #[ty] (fun p => p.volatile_ == volatile)
      return (ty, base))
    (fun (ty, base) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let p ← castValue base reg
      let props := RISCVMemProperties.mk (BitVec.ofInt 64 address.offset) volatile
      let r ← if w = 8 then emit .lb #[p.res[0]!] props
        else if w = 32 then emit .lw #[p.res[0]!] props
        else emit .ld #[p.res[0]!] props
      castValue r ty)
    (fun result => result)

/-- Port of store selection, including optional GEP folding and volatility. -/
def store (w : Nat) (volatile : Bool) (address : MemoryAddress := .direct) : Pattern OpCode :=
  Pattern.Builder
    (do
      let pt ← MatchProg.type (Attr := TypeAttr) (· == Veir.LLVM.PointerType.mk)
      let ty ← MatchProg.type (Attr := IntegerType)
        (fun t => (t.bitwidth == w) && decide (w = 64 ∨ w = 32 ∨ w = 8))
      let value ← MatchProg.value ty
      let (ptr, base) ← matchAddress pt address
      let _ ← MatchProg.root (.llvm .store) #[value, ptr] #[] (fun p => p.volatile_ == volatile)
      return (value, base))
    (fun (value, base) => do
      let reg ← CreateProg.type (RegisterType.mk none)
      let p ← castValue base reg
      let v ← castValue value reg
      let props := RISCVMemProperties.mk
        (BitVec.ofInt 64 address.offset) volatile
      if w = 8 then do
        let pr ← CreateProg.property (.riscv .sb) props
        CreateProg.operation (.riscv .sb) #[v.res[0]!, p.res[0]!] #[] pr
      else if w = 32 then do
        let pr ← CreateProg.property (.riscv .sw) props
        CreateProg.operation (.riscv .sw) #[v.res[0]!, p.res[0]!] #[] pr
      else do
        let pr ← CreateProg.property (.riscv .sd) props
        CreateProg.operation (.riscv .sd) #[v.res[0]!, p.res[0]!] #[] pr)
    (fun result => result)

/-- A memory-effect exclusion, not a claim that the load lowering is incorrect. -/
theorem load_not_valid (w : Nat) (volatile : Bool) (address : MemoryAddress) :
    ¬ (load w volatile address).Valid := by
  suffices h : ¬ (load w volatile address).Supported from fun hv => h hv.Supported
  cases address <;> simp only [load, matchAddress, matchBits, emit, castValue]
  all_goals
    unfoldPuddleBuilder
    simp [Pattern.Supported, MatchProg.Supported, MatchDecl.Supported,
      SupportedOpCode, get_effects, is_terminator]
    intro h
    have hf := h (default : propertiesOf (OpCode.llvm .load))
    split at hf <;> contradiction

/-- A memory-effect exclusion, not a claim that the store lowering is incorrect. -/
theorem store_not_valid (w : Nat) (volatile : Bool) (address : MemoryAddress) :
    ¬ (store w volatile address).Valid := by
  suffices h : ¬ (store w volatile address).Supported from fun hv => h hv.Supported
  cases address <;> simp only [store, matchAddress, matchBits, castValue]
  all_goals
    unfoldPuddleBuilder
    simp [Pattern.Supported, MatchProg.Supported, MatchDecl.Supported,
      SupportedOpCode, get_effects, is_terminator]
    intro h
    have hf := h (default : propertiesOf (OpCode.llvm .store))
    split at hf <;> contradiction

end Veir.RISCV64Puddle
