module

public import Veir.Passes.Legalization.LegalizerInfo
public import Veir.PatternRewriter.Puddle.Execution
public import Veir.PatternRewriter.Puddle.Builders
import Veir.Interfaces.ConstantLikeInterfaces

/-!
# Combines

This file implements the target-independent gMIR combines as Puddle patterns. The combines that
depend on the legality of operations take the `LegalizerInfo` of the target. LLVM's
`commute_constant_to_rhs` is the canonicalizer's `commutativeConstantRHS`.

Besides LLVM's `RISCVPostLegalizerCombiner` combines, this file has combines from LLVM's
`all_combines`, which LLVM runs before legalization. Here they run after legalization, so they only
match legal operations, and the operations they create only use the types of the values they match.

TODO: Add the other combines of LLVM's `RISCVPostLegalizerCombiner` (`combines_for_extload` and
`shift_immed_chain`), and the rest of `redundant_and`.

Also see:
https://github.com/llvm/llvm-project/blob/main/llvm/lib/CodeGen/GlobalISel/CombinerHelper.cpp
-/

namespace Veir

open Puddle

public section

/-! ### sub_to_add : (sub x, C) → (add x, -C) -/

/--
`g_sub x, C` becomes `g_add x, -C` if `g_add` and `g_constant` are legal for the type. As in LLVM,
the result drops `nuw`, and drops `nsw` when `C` is the minimum signed value.

https://github.com/llvm/llvm-project/blob/bcb89020f2953e414ff525cbf04e9c35be50ece4/llvm/include/llvm/Target/GlobalISel/Combine.td#L397-L403
https://github.com/llvm/llvm-project/blob/bcb89020f2953e414ff525cbf04e9c35be50ece4/llvm/lib/CodeGen/GlobalISel/CombinerHelper.cpp#L2209
-/
def sub_to_add_pattern (info : LegalizerInfo) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let constant ← MatchProg.operation (.gmir .g_constant) #[] #[type]
      let root ← MatchProg.root (.gmir .g_sub) #[x, constant.res[0]!] #[type]
      MatchProg.matchNative (type, constant.properties) fun (ty, props) =>
        info.isLegal .g_add #[ty] { nsw := false, nuw := false } &&
          info.isLegal .g_constant #[ty] props.neg
      return (type, x, constant.properties, root.properties))
    (fun (type, x, constantProps, subProps) => do
      let negProps ← CreateProg.applyNative
          (Outputs := Handle OpCode (.prop (.gmir .g_constant))) constantProps
          fun props => some props.neg
      let negOp ← CreateProg.operation (.gmir .g_constant) #[] #[type] negProps
      -- `x - C` and `x + -C` wrap as signed integers in the same cases, unless `C` is the
      -- minimum signed value, which is its own negation. As unsigned integers, a nonzero `C`
      -- negates to the large value `2^n - C`, so `x + -C` wraps whenever `x - C` does not, and
      -- `nuw` is dropped.
      let addProps ← CreateProg.applyNative
          (Outputs := Handle OpCode (.prop (.gmir .g_add))) (constantProps, subProps)
          fun (constant, sub) => some { nsw := sub.nsw && !constant.isMinSigned, nuw := false }
      CreateProg.operation (.gmir .g_add) #[x, negOp.res[0]!] #[type] addProps)
    (fun addOp => addOp)

def sub_to_add (info : LegalizerInfo) : CompiledPattern OpCode := (sub_to_add_pattern info).compile

/-! ### redundant_and : (and (icmp x, y), C) → (icmp x, y) -/

/--
`g_and (g_icmp x, y), C` becomes the `g_icmp` when the low bit of `C` is set: the `g_icmp` yields 0
or 1, so the mask keeps it. LLVM's `redundant_and` finds this, and other redundant masks, with known
bits, which we do not have; the `g_icmp` is the case that legalizing a `g_brcond` leaves behind.

https://github.com/llvm/llvm-project/blob/bcb89020f2953e414ff525cbf04e9c35be50ece4/llvm/lib/CodeGen/GlobalISel/CombinerHelper.cpp#L3497
-/
def redundant_and_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let operandType ← MatchProg.type (Attr := TypeAttr)
      let lhs ← MatchProg.value operandType
      let rhs ← MatchProg.value operandType
      let type ← MatchProg.type (Attr := IntegerType)
      let icmp ← MatchProg.operation (.gmir .g_icmp) #[lhs, rhs] #[type]
      let constant ← MatchProg.operation (.gmir .g_constant) #[] #[type]
      MatchProg.matchNative constant.properties fun props => props.value.value % 2 = 1
      let _ ← MatchProg.root (.gmir .g_and) #[icmp.res[0]!, constant.res[0]!] #[type]
      return icmp.res[0]!)
    pure (fun x => x)

def redundant_and : CompiledPattern OpCode := redundant_and_pattern.compile

/-! ### Helpers -/

/-- Match a `g_constant` of `type` whose properties satisfy `pred`. -/
def matchConstant (type : Handle OpCode .type)
    (pred : GMIRConstantProperties → Bool := fun _ => true) :
    MatchProg.Builder (OpHandle (.gmir .g_constant)) :=
  MatchProg.operation (.gmir .g_constant) #[] #[type] pred

/-- Create a `g_constant` of `type` whose value `value` computes from the metadata `inputs`. -/
def createConstantWith {Inputs : Type} [IsMetadataTuple OpCode Inputs]
    (type : Handle OpCode .type) (inputs : Inputs)
    (value : MetadataValues OpCode Inputs → Int) : CreateProg.Builder CreatedOpHandle := do
  let props ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.gmir .g_constant)))
      (type, inputs) fun (type, inputs) => do
        let .integerType type := type.val | none
        return { value := .ofInt (value inputs) type }
  CreateProg.operation (.gmir .g_constant) #[] #[type] props

/-- Create a `g_constant` of `type` with the value `value`. -/
def createConstant (type : Handle OpCode .type) (value : Int) :
    CreateProg.Builder CreatedOpHandle :=
  createConstantWith type () fun () => value

/-! ### identity_combines -/

/-- `x op 0` → `x`, for `op` ∈ {`g_sub`, `g_add`, `g_or`, `g_xor`, `g_shl`, `g_ashr`, `g_lshr`}. -/
def right_identity_zero_pattern (opcode : GMIR) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let rhsType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let zero ← matchConstant rhsType (·.bits = 0)
      let _ ← MatchProg.root (.gmir opcode) #[x, zero.res[0]!] #[type]
      return x)
    pure (fun x => x)

/-- `x * 1` → `x`. -/
def right_identity_one_int_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let one ← matchConstant type (·.bits.toNat = 1)
      let _ ← MatchProg.root (.gmir .g_mul) #[x, one.res[0]!] #[type]
      return x)
    pure (fun x => x)

/-- `x op x` → `x`, for `op` ∈ {`g_and`, `g_or`}. -/
def binop_same_val_pattern (opcode : GMIR) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let _ ← MatchProg.root (.gmir opcode) #[x, x] #[type]
      return x)
    pure (fun x => x)

/-- `x op x` → `0`, for `op` ∈ {`g_sub`, `g_xor`}. -/
def same_val_zero_pattern (opcode : GMIR) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let _ ← MatchProg.root (.gmir opcode) #[x, x] #[type]
      return type)
    (createConstant · 0) (fun zero => zero)

/-- `x * 0` → `0`. -/
def binop_right_to_zero_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let zero ← matchConstant type (·.bits = 0)
      let _ ← MatchProg.root (.gmir .g_mul) #[x, zero.res[0]!] #[type]
      return zero.res[0]!)
    pure (fun zero => zero)

/-- `0 op x` → `0`, for `op` ∈ {`g_shl`, `g_lshr`, `g_ashr`, `g_mul`}. -/
def binop_left_to_zero_pattern (opcode : GMIR) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let rhsType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value rhsType
      let zero ← matchConstant type (·.bits = 0)
      let _ ← MatchProg.root (.gmir opcode) #[zero.res[0]!, x] #[type]
      return zero.res[0]!)
    pure (fun zero => zero)

/-- `x + (y - x)` → `y`. -/
def add_sub_reg_0_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let sub ← MatchProg.operation (.gmir .g_sub) #[y, x] #[type]
      let _ ← MatchProg.root (.gmir .g_add) #[x, sub.res[0]!] #[type]
      return y)
    pure (fun y => y)

/-- `(y - x) + x` → `y`. -/
def add_sub_reg_1_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let sub ← MatchProg.operation (.gmir .g_sub) #[y, x] #[type]
      let _ ← MatchProg.root (.gmir .g_add) #[sub.res[0]!, x] #[type]
      return y)
    pure (fun y => y)

/-! ### sub_add_reg -/

/-- `(x + y) - y` → `x`. -/
def sub_add_reg_x_add_y_sub_y_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let add ← MatchProg.operation (.gmir .g_add) #[x, y] #[type]
      let _ ← MatchProg.root (.gmir .g_sub) #[add.res[0]!, y] #[type]
      return x)
    pure (fun x => x)

/-- `(x + y) - x` → `y`. -/
def sub_add_reg_x_add_y_sub_x_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let add ← MatchProg.operation (.gmir .g_add) #[x, y] #[type]
      let _ ← MatchProg.root (.gmir .g_sub) #[add.res[0]!, x] #[type]
      return y)
    pure (fun y => y)

/-- `x - (y + x)` → `0 - y` when `xFirst` is false, and `x - (x + y)` → `0 - y` when it is set. -/
def sub_add_reg_negate_pattern (xFirst : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let add ← MatchProg.operation (.gmir .g_add) (if xFirst then #[x, y] else #[y, x]) #[type]
      let _ ← MatchProg.root (.gmir .g_sub) #[x, add.res[0]!] #[type]
      return (type, y))
    (fun (type, y) => do
      let zero ← createConstant type 0
      CreateProg.operation (.gmir .g_sub) #[zero.res[0]!, y] #[type])
    (fun op => op)

/-! ### integer_reassoc_combines

The new operations get no overflow flags: the reassociated operations can overflow where the
original ones did not, as in LLVM, which builds them without flags.
-/

/-- `-1 - x` → `x ^ -1`. -/
def sub_minus_one_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let allOnes ← matchConstant type (·.bits = -1)
      let _ ← MatchProg.root (.gmir .g_sub) #[allOnes.res[0]!, x] #[type]
      return (type, x, allOnes.res[0]!))
    (fun (type, x, allOnes) => CreateProg.operation (.gmir .g_xor) #[x, allOnes] #[type])
    (fun op => op)

/-- `(a + (b - c)) - b` → `a - c`. -/
def APlusBMinusCMinusB_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value type
      let b ← MatchProg.value type
      let c ← MatchProg.value type
      let sub ← MatchProg.operation (.gmir .g_sub) #[b, c] #[type]
      let add ← MatchProg.operation (.gmir .g_add) #[a, sub.res[0]!] #[type]
      let _ ← MatchProg.root (.gmir .g_sub) #[add.res[0]!, b] #[type]
      return (type, a, c))
    (fun (type, a, c) => CreateProg.operation (.gmir .g_sub) #[a, c] #[type])
    (fun op => op)

/-- `(a - (b - c)) - c` → `a - b`. -/
def AMinusBMinusCMinusC_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value type
      let b ← MatchProg.value type
      let c ← MatchProg.value type
      let inner ← MatchProg.operation (.gmir .g_sub) #[b, c] #[type]
      let outer ← MatchProg.operation (.gmir .g_sub) #[a, inner.res[0]!] #[type]
      let _ ← MatchProg.root (.gmir .g_sub) #[outer.res[0]!, c] #[type]
      return (type, a, b))
    (fun (type, a, b) => CreateProg.operation (.gmir .g_sub) #[a, b] #[type])
    (fun op => op)

/-- `(0 - a) + b` → `b - a`. -/
def ZeroMinusAPlusB_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value type
      let b ← MatchProg.value type
      let zero ← matchConstant type (·.bits = 0)
      let neg ← MatchProg.operation (.gmir .g_sub) #[zero.res[0]!, a] #[type]
      let _ ← MatchProg.root (.gmir .g_add) #[neg.res[0]!, b] #[type]
      return (type, a, b))
    (fun (type, a, b) => CreateProg.operation (.gmir .g_sub) #[b, a] #[type])
    (fun op => op)

/-- `a + (0 - b)` → `a - b`. -/
def APlusZeroMinusB_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value type
      let b ← MatchProg.value type
      let zero ← matchConstant type (·.bits = 0)
      let neg ← MatchProg.operation (.gmir .g_sub) #[zero.res[0]!, b] #[type]
      let _ ← MatchProg.root (.gmir .g_add) #[a, neg.res[0]!] #[type]
      return (type, a, b))
    (fun (type, a, b) => CreateProg.operation (.gmir .g_sub) #[a, b] #[type])
    (fun op => op)

/-- `(a - b) + (c - a)` → `c - b`. -/
def AMinusBPlusCMinusA_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value type
      let b ← MatchProg.value type
      let c ← MatchProg.value type
      let lhs ← MatchProg.operation (.gmir .g_sub) #[a, b] #[type]
      let rhs ← MatchProg.operation (.gmir .g_sub) #[c, a] #[type]
      let _ ← MatchProg.root (.gmir .g_add) #[lhs.res[0]!, rhs.res[0]!] #[type]
      return (type, b, c))
    (fun (type, b, c) => CreateProg.operation (.gmir .g_sub) #[c, b] #[type])
    (fun op => op)

/-- `(a - b) + (b - c)` → `a - c`. -/
def AMinusBPlusBMinusC_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value type
      let b ← MatchProg.value type
      let c ← MatchProg.value type
      let lhs ← MatchProg.operation (.gmir .g_sub) #[a, b] #[type]
      let rhs ← MatchProg.operation (.gmir .g_sub) #[b, c] #[type]
      let _ ← MatchProg.root (.gmir .g_add) #[lhs.res[0]!, rhs.res[0]!] #[type]
      return (type, a, c))
    (fun (type, a, c) => CreateProg.operation (.gmir .g_sub) #[a, c] #[type])
    (fun op => op)

/-- `a + (b - (a + c))` → `b - c` when `aFirst` is set, and `a + (b - (c + a))` → `b - c`
    otherwise. -/
def APlusBMinusAPlusC_pattern (aFirst : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value type
      let b ← MatchProg.value type
      let c ← MatchProg.value type
      let add ← MatchProg.operation (.gmir .g_add) (if aFirst then #[a, c] else #[c, a]) #[type]
      let sub ← MatchProg.operation (.gmir .g_sub) #[b, add.res[0]!] #[type]
      let _ ← MatchProg.root (.gmir .g_add) #[a, sub.res[0]!] #[type]
      return (type, b, c))
    (fun (type, b, c) => CreateProg.operation (.gmir .g_sub) #[b, c] #[type])
    (fun op => op)

/-- `a - (0 - b)` → `a + b`. -/
def AMinusZeroMinusB_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value type
      let b ← MatchProg.value type
      let zero ← matchConstant type (·.bits = 0)
      let neg ← MatchProg.operation (.gmir .g_sub) #[zero.res[0]!, b] #[type]
      let _ ← MatchProg.root (.gmir .g_sub) #[a, neg.res[0]!] #[type]
      return (type, a, b))
    (fun (type, a, b) => CreateProg.operation (.gmir .g_add) #[a, b] #[type])
    (fun op => op)

/-- `a - (a - b)` → `b`. -/
def AMinusBMinusA_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value type
      let b ← MatchProg.value type
      let sub ← MatchProg.operation (.gmir .g_sub) #[a, b] #[type]
      let _ ← MatchProg.root (.gmir .g_sub) #[a, sub.res[0]!] #[type]
      return b)
    pure (fun b => b)

/-- `a - (b - c)` → `a + (c - b)`. -/
def AMinusBMinusC_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value type
      let b ← MatchProg.value type
      let c ← MatchProg.value type
      let sub ← MatchProg.operation (.gmir .g_sub) #[b, c] #[type]
      let _ ← MatchProg.root (.gmir .g_sub) #[a, sub.res[0]!] #[type]
      return (type, a, b, c))
    (fun (type, a, b, c) => do
      let cMinusB ← CreateProg.operation (.gmir .g_sub) #[c, b] #[type]
      CreateProg.operation (.gmir .g_add) #[a, cMinusB.res[0]!] #[type])
    (fun op => op)

/-- `(x - y) - 1` → `(y ^ -1) + x`. -/
def sub_one_from_sub_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let one ← matchConstant type (·.bits.toInt = 1)
      let sub ← MatchProg.operation (.gmir .g_sub) #[x, y] #[type]
      let _ ← MatchProg.root (.gmir .g_sub) #[sub.res[0]!, one.res[0]!] #[type]
      return (type, x, y))
    (fun (type, x, y) => do
      let allOnes ← createConstant type (-1)
      let not ← CreateProg.operation (.gmir .g_xor) #[y, allOnes.res[0]!] #[type]
      CreateProg.operation (.gmir .g_add) #[not.res[0]!, x] #[type])
    (fun op => op)

/--
A reassociation of two constants `c₁` and `c₂` around `a`: `root (inner a₁ a₂) c₂`, where `a₁ a₂` is
`a c₁` or, when `constFirst` is set, `c₁ a`. It becomes `result a (c₁ ∘ c₂)`, or `result (c₁ ∘ c₂) a`
when `constFirst` is set, where `fold` computes `c₁ ∘ c₂` and `constOuterLeft` puts `c₂` on the
left of `root`.
-/
def constant_reassoc_pattern (root inner result : GMIR) (constFirst constOuterLeft : Bool)
    (fold : Int → Int → Int) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value type
      let c₁ ← matchConstant type
      let c₂ ← matchConstant type
      let innerOp ← MatchProg.operation (.gmir inner)
          (if constFirst then #[c₁.res[0]!, a] else #[a, c₁.res[0]!]) #[type]
      let _ ← MatchProg.root (.gmir root)
          (if constOuterLeft then #[c₂.res[0]!, innerOp.res[0]!]
            else #[innerOp.res[0]!, c₂.res[0]!]) #[type]
      return (type, a, c₁.properties, c₂.properties))
    (fun (type, a, c₁, c₂) => do
      let folded ← createConstantWith type (c₁, c₂) fun (c₁, c₂) =>
        fold c₁.bits.toInt c₂.bits.toInt
      CreateProg.operation (.gmir result)
          (if constFirst then #[folded.res[0]!, a] else #[a, folded.res[0]!]) #[type])
    (fun op => op)

/-- `(a + c₁) - c₂` → `a + (c₁ - c₂)`. -/
def APlusC1MinusC2_pattern : Pattern OpCode :=
  constant_reassoc_pattern .g_sub .g_add .g_add false false (· - ·)

/-- `c₂ - (a + c₁)` → `(c₂ - c₁) - a`. -/
def C2MinusAPlusC1_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value type
      let c₁ ← matchConstant type
      let c₂ ← matchConstant type
      let add ← MatchProg.operation (.gmir .g_add) #[a, c₁.res[0]!] #[type]
      let _ ← MatchProg.root (.gmir .g_sub) #[c₂.res[0]!, add.res[0]!] #[type]
      return (type, a, c₁.properties, c₂.properties))
    (fun (type, a, c₁, c₂) => do
      let folded ← createConstantWith type (c₁, c₂) fun (c₁, c₂) => c₂.bits.toInt - c₁.bits.toInt
      CreateProg.operation (.gmir .g_sub) #[folded.res[0]!, a] #[type])
    (fun op => op)

/-- `(a - c₁) - c₂` → `a - (c₁ + c₂)`. -/
def AMinusC1MinusC2_pattern : Pattern OpCode :=
  constant_reassoc_pattern .g_sub .g_sub .g_sub false false (· + ·)

/-- `(c₁ - a) - c₂` → `(c₁ - c₂) - a`. -/
def C1MinusAMinusC2_pattern : Pattern OpCode :=
  constant_reassoc_pattern .g_sub .g_sub .g_sub true false (· - ·)

/-- `(a - c₁) + c₂` → `a + (c₂ - c₁)`. -/
def AMinusC1PlusC2_pattern : Pattern OpCode :=
  constant_reassoc_pattern .g_add .g_sub .g_add false false (fun c₁ c₂ => c₂ - c₁)

/-- `a - (x * c)` → `a + (x * -c)`. -/
def sub_of_mul_const_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value type
      let x ← MatchProg.value type
      let c ← matchConstant type
      let mul ← MatchProg.operation (.gmir .g_mul) #[x, c.res[0]!] #[type]
      let _ ← MatchProg.root (.gmir .g_sub) #[a, mul.res[0]!] #[type]
      return (type, a, x, c.properties))
    (fun (type, a, x, c) => do
      let negC ← createConstantWith type c fun c => -c.bits.toInt
      let mul ← CreateProg.operation (.gmir .g_mul) #[x, negC.res[0]!] #[type]
      CreateProg.operation (.gmir .g_add) #[a, mul.res[0]!] #[type])
    (fun op => op)

/-- `x * -1` → `0 - x`. `x * -1` overflows as a signed integer exactly when `0 - x` does, for
    `x` the minimum signed value, so `nsw` carries over; `nuw` does not. -/
def mul_by_neg_one_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let allOnes ← matchConstant type (·.bits = -1)
      let root ← MatchProg.root (.gmir .g_mul) #[x, allOnes.res[0]!] #[type]
      return (type, x, root.properties))
    (fun (type, x, mulProps) => do
      let zero ← createConstant type 0
      let subProps ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.gmir .g_sub)))
          mulProps fun props => some { nsw := props.nsw, nuw := false }
      CreateProg.operation (.gmir .g_sub) #[zero.res[0]!, x] #[type] subProps)
    (fun op => op)

/-- `x * 2` → `x + x`. Both overflow in the same cases, so the flags carry over. -/
def mulo_by_2_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let two ← matchConstant type (·.bits.toInt = 2)
      let root ← MatchProg.root (.gmir .g_mul) #[x, two.res[0]!] #[type]
      return (type, x, root.properties))
    (fun (type, x, mulProps) => do
      let addProps ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.gmir .g_add)))
          mulProps fun props => some { nsw := props.nsw, nuw := props.nuw }
      CreateProg.operation (.gmir .g_add) #[x, x] #[type] addProps)
    (fun op => op)

/-- `a + ((0 - b) << c)` → `a - (b << c)`, and the same with the operands of the addition swapped
    when `shiftFirst` is set. -/
def add_shift_pattern (shiftFirst : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let amountType ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value type
      let b ← MatchProg.value type
      let c ← MatchProg.value amountType
      let zero ← matchConstant type (·.bits = 0)
      let neg ← MatchProg.operation (.gmir .g_sub) #[zero.res[0]!, b] #[type]
      let shl ← MatchProg.operation (.gmir .g_shl) #[neg.res[0]!, c] #[type]
      let _ ← MatchProg.root (.gmir .g_add)
          (if shiftFirst then #[shl.res[0]!, a] else #[a, shl.res[0]!]) #[type]
      return (type, a, b, c))
    (fun (type, a, b, c) => do
      let shl ← CreateProg.operation (.gmir .g_shl) #[b, c] #[type]
      CreateProg.operation (.gmir .g_sub) #[a, shl.res[0]!] #[type])
    (fun op => op)

/-- `(x + -1) ^ -1` → `0 - x`. The addition and the subtraction overflow in the same cases, so the
    flags carry over. -/
def NotAPlusNegOne_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let allOnes ← matchConstant type (·.bits = -1)
      let add ← MatchProg.operation (.gmir .g_add) #[x, allOnes.res[0]!] #[type]
      let notOnes ← matchConstant type (·.bits = -1)
      let _ ← MatchProg.root (.gmir .g_xor) #[add.res[0]!, notOnes.res[0]!] #[type]
      return (type, x, add.properties))
    (fun (type, x, addProps) => do
      let zero ← createConstant type 0
      let subProps ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.gmir .g_sub)))
          addProps fun props => some { nsw := props.nsw, nuw := props.nuw }
      CreateProg.operation (.gmir .g_sub) #[zero.res[0]!, x] #[type] subProps)
    (fun op => op)

/-! ### hoist_logic_op_with_same_opcode_hands

The new operations get no flags: the flags of the hands do not hold for the combined operand. For
example, `(x << z) | (y << z)` can be disjoint while `x | y` is not.
-/

/-- `(x hand z) logic (y hand z)` → `(x logic y) hand z`. -/
def hoist_logic_op_pattern (logic hand : GMIR) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let zType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let z ← MatchProg.value zType
      let lhs ← MatchProg.operation (.gmir hand) #[x, z] #[type]
      let rhs ← MatchProg.operation (.gmir hand) #[y, z] #[type]
      let _ ← MatchProg.root (.gmir logic) #[lhs.res[0]!, rhs.res[0]!] #[type]
      return (type, x, y, z))
    (fun (type, x, y, z) => do
      let inner ← CreateProg.operation (.gmir logic) #[x, y] #[type]
      CreateProg.operation (.gmir hand) #[inner.res[0]!, z] #[type])
    (fun op => op)

/-! ### Bitwise combines -/

/-- `(x & y) ^ y` → `(x ^ -1) & y`. -/
def xor_of_and_with_same_reg_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let and ← MatchProg.operation (.gmir .g_and) #[x, y] #[type]
      let _ ← MatchProg.root (.gmir .g_xor) #[and.res[0]!, y] #[type]
      return (type, x, y))
    (fun (type, x, y) => do
      let allOnes ← createConstant type (-1)
      let not ← CreateProg.operation (.gmir .g_xor) #[x, allOnes.res[0]!] #[type]
      CreateProg.operation (.gmir .g_and) #[not.res[0]!, y] #[type])
    (fun op => op)

/-- `(x & (y ^ -1)) | y` → `x | y` for `(outer, inner)` = `(g_or, g_and)`, and
    `(x | (y ^ -1)) & y` → `x & y` for `(g_and, g_or)`. -/
def or_and_xor_to_or_pattern (outer inner : GMIR) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let allOnes ← matchConstant type (·.bits = -1)
      let not ← MatchProg.operation (.gmir .g_xor) #[y, allOnes.res[0]!] #[type]
      let innerOp ← MatchProg.operation (.gmir inner) #[x, not.res[0]!] #[type]
      let _ ← MatchProg.root (.gmir outer) #[innerOp.res[0]!, y] #[type]
      return (type, x, y))
    (fun (type, x, y) => CreateProg.operation (.gmir outer) #[x, y] #[type])
    (fun op => op)

/-- `(x & y) | (y ^ -1)` → `x | (y ^ -1)` for `(outer, inner)` = `(g_or, g_and)`, and
    `(x | y) & (y ^ -1)` → `x & (y ^ -1)` for `(g_and, g_or)`. -/
def or_and_xor_to_xor_or_pattern (outer inner : GMIR) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let allOnes ← matchConstant type (·.bits = -1)
      let not ← MatchProg.operation (.gmir .g_xor) #[y, allOnes.res[0]!] #[type]
      let innerOp ← MatchProg.operation (.gmir inner) #[x, y] #[type]
      let _ ← MatchProg.root (.gmir outer) #[innerOp.res[0]!, not.res[0]!] #[type]
      return (type, x, not.res[0]!))
    (fun (type, x, not) => CreateProg.operation (.gmir outer) #[x, not] #[type])
    (fun op => op)

/-- `(x & y) | x` → `x`. `andLeft` puts the `g_and` on the left of the `g_or`, and `xFirst` puts `x`
    on the left of the `g_and`. -/
def combine_or_of_and_pattern (andLeft xFirst : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let and ← MatchProg.operation (.gmir .g_and) (if xFirst then #[x, y] else #[y, x]) #[type]
      let _ ← MatchProg.root (.gmir .g_or)
          (if andLeft then #[and.res[0]!, x] else #[x, and.res[0]!]) #[type]
      return x)
    pure (fun x => x)

/-! ### simplify_neg_minmax -/

/-- `0 - (max a, (0 - a))` → `min a, (0 - a)` for `(max, min)` an opposite pair of `g_smax`,
    `g_smin`, `g_umax` and `g_umin`. -/
def simplify_neg_minmax_pattern (minmax opposite : GMIR) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value type
      let innerZero ← matchConstant type (·.bits = 0)
      let neg ← MatchProg.operation (.gmir .g_sub) #[innerZero.res[0]!, a] #[type]
      let minmaxOp ← MatchProg.operation (.gmir minmax) #[a, neg.res[0]!] #[type]
      let outerZero ← matchConstant type (·.bits = 0)
      let _ ← MatchProg.root (.gmir .g_sub) #[outerZero.res[0]!, minmaxOp.res[0]!] #[type]
      return (type, a, neg.res[0]!))
    (fun (type, a, neg) => CreateProg.operation (.gmir opposite) #[a, neg] #[type])
    (fun op => op)

/-! ### cmp_combines -/

/-- The predicate of `icmp pred y x` that is equivalent to `icmp pred x y`. -/
def swapIntPred : Data.LLVM.IntPred → Data.LLVM.IntPred
  | .slt => .sgt | .sgt => .slt | .sle => .sge | .sge => .sle
  | .ult => .ugt | .ugt => .ult | .ule => .uge | .uge => .ule
  | pred => pred

/-- `icmp pred c, x` → `icmp (swapIntPred pred) x, c` for a constant `c` and a non-constant `x`. -/
def canonicalize_icmp_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let resType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let c ← matchConstant type
      let root ← MatchProg.root (.gmir .g_icmp) #[c.res[0]!, x] #[resType]
      let () ← MatchProg.inspectOperation (Outputs := Unit) root.op fun ctx op =>
        guard !((op.getOperands! ctx)[1]!.isConstantLike ctx)
      return (resType, x, c.res[0]!, root.properties))
    (fun (resType, x, c, icmpProps) => do
      let swappedProps ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.gmir .g_icmp)))
          icmpProps fun props => some { predicate := swapIntPred props.predicate }
      CreateProg.operation (.gmir .g_icmp) #[x, c] #[resType] swappedProps)
    (fun op => op)

/-- `(icmp pred x, y) ^ true` → `icmp inverse x, y`. A `g_icmp` result wider than `i1` is `0` or `1`,
    so `true` is the constant `1` at any width. -/
def not_cmp_fold_pattern (pred inverse : Data.LLVM.IntPred) : Pattern OpCode :=
  Pattern.Builder
    (do
      let opType ← MatchProg.type (Attr := IntegerType)
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value opType
      let y ← MatchProg.value opType
      let icmp ← MatchProg.operation (.gmir .g_icmp) #[x, y] #[type] (·.predicate = pred)
      let true_ ← matchConstant type (·.bits.toNat = 1)
      let _ ← MatchProg.root (.gmir .g_xor) #[icmp.res[0]!, true_.res[0]!] #[type]
      return (type, x, y))
    (fun (type, x, y) => do
      let props ← CreateProg.property (.gmir .g_icmp) { predicate := inverse }
      CreateProg.operation (.gmir .g_icmp) #[x, y] #[type] props)
    (fun op => op)

/-- `icmp pred (x op y), x` → `icmp pred y, 0` for `op` ∈ {`g_add`, `g_sub`, `g_xor`} and `pred`
    ∈ {`eq`, `ne`}. -/
def redundant_binop_in_equality_pattern (opcode : GMIR) (pred : Data.LLVM.IntPred) :
    Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let resType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let binop ← MatchProg.operation (.gmir opcode) #[x, y] #[type]
      let root ← MatchProg.root (.gmir .g_icmp) #[binop.res[0]!, x] #[resType]
          (·.predicate = pred)
      return (type, resType, y, root.properties))
    (fun (type, resType, y, icmpProps) => do
      let zero ← createConstant type 0
      CreateProg.operation (.gmir .g_icmp) #[y, zero.res[0]!] #[resType] icmpProps)
    (fun op => op)

/-- `(x == 0) & (y == 0)` → `(x | y) == 0` for `(logic, pred)` = `(g_and, eq)`, and
    `(x != 0) | (y != 0)` → `(x | y) != 0` for `(g_or, ne)`. -/
def double_icmp_zero_pattern (logic : GMIR) (pred : Data.LLVM.IntPred) : Pattern OpCode :=
  Pattern.Builder
    (do
      let opType ← MatchProg.type (Attr := IntegerType)
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value opType
      let y ← MatchProg.value opType
      let zeroX ← matchConstant opType (·.bits = 0)
      let zeroY ← matchConstant opType (·.bits = 0)
      let cmpX ← MatchProg.operation (.gmir .g_icmp) #[x, zeroX.res[0]!] #[type]
          (·.predicate = pred)
      let cmpY ← MatchProg.operation (.gmir .g_icmp) #[y, zeroY.res[0]!] #[type]
          (·.predicate = pred)
      let _ ← MatchProg.root (.gmir logic) #[cmpX.res[0]!, cmpY.res[0]!] #[type]
      return (opType, type, x, y, zeroX.res[0]!, cmpX.properties))
    (fun (opType, type, x, y, zero, icmpProps) => do
      let or ← CreateProg.operation (.gmir .g_or) #[x, y] #[opType]
      CreateProg.operation (.gmir .g_icmp) #[or.res[0]!, zero] #[type] icmpProps)
    (fun op => op)

/-! ### cast_of_cast_combines -/

/-- `trunc (ext x)` → `x` when the result has the type of `x`, for `ext` ∈ {`g_zext`, `g_sext`}. -/
def trunc_of_ext_pattern (ext : GMIR) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let wideType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let extOp ← MatchProg.operation (.gmir ext) #[x] #[wideType]
      let _ ← MatchProg.root (.gmir .g_trunc) #[extOp.res[0]!] #[type]
      return x)
    pure (fun x => x)

/-- `ext (ext x)` → `ext x`, for `ext` ∈ {`g_zext`, `g_sext`}. The new extension has no `nneg`: the
    outer extension's `nneg` holds for the already extended operand, not for `x`. -/
def ext_of_ext_pattern (ext : GMIR) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let midType ← MatchProg.type (Attr := IntegerType)
      let resType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let inner ← MatchProg.operation (.gmir ext) #[x] #[midType]
      let _ ← MatchProg.root (.gmir ext) #[inner.res[0]!] #[resType]
      return (resType, x))
    (fun (resType, x) => CreateProg.operation (.gmir ext) #[x] #[resType])
    (fun op => op)

/-! ### bitreverse_shift -/

/-- `bitreverse ((bitreverse x) shift y)` → `x opposite y`, for `(shift, opposite)` =
    `(g_shl, g_lshr)` or `(g_lshr, g_shl)`. -/
def bitreverse_shift_pattern (shift opposite : GMIR) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let amountType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value amountType
      let inner ← MatchProg.operation (.gmir .g_bitreverse) #[x] #[type]
      let shiftOp ← MatchProg.operation (.gmir shift) #[inner.res[0]!, y] #[type]
      let _ ← MatchProg.root (.gmir .g_bitreverse) #[shiftOp.res[0]!] #[type]
      return (type, x, y))
    (fun (type, x, y) => CreateProg.operation (.gmir opposite) #[x, y] #[type])
    (fun op => op)

/-! ### Power-of-two strength reductions -/

/-- `udiv x, 2^k` → `lshr x, k`. -/
def udiv_by_pow2_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let c ← matchConstant type (·.log2?.isSome)
      let _ ← MatchProg.root (.gmir .g_udiv) #[x, c.res[0]!] #[type]
      return (type, x, c.properties))
    (fun (type, x, c) => do
      let k ← createConstantWith type c fun c => c.log2?.get!
      CreateProg.operation (.gmir .g_lshr) #[x, k.res[0]!] #[type])
    (fun op => op)

/-- `x * 2^k` → `x << k`. Both overflow in the same cases, so the flags carry over. -/
def mul_to_shl_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let c ← matchConstant type (·.log2?.isSome)
      let root ← MatchProg.root (.gmir .g_mul) #[x, c.res[0]!] #[type]
      return (type, x, c.properties, root.properties))
    (fun (type, x, c, mulProps) => do
      let k ← createConstantWith type c fun c => c.log2?.get!
      let shlProps ← CreateProg.applyNative (Outputs := Handle OpCode (.prop (.gmir .g_shl)))
          mulProps fun props => some { nsw := props.nsw, nuw := props.nuw }
      CreateProg.operation (.gmir .g_shl) #[x, k.res[0]!] #[type] shlProps)
    (fun op => op)

/-- `urem x, 2^k` → `x & (2^k - 1)`. -/
def urem_pow2_to_mask_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let c ← matchConstant type (·.log2?.isSome)
      let _ ← MatchProg.root (.gmir .g_urem) #[x, c.res[0]!] #[type]
      return (type, x, c.properties))
    (fun (type, x, c) => do
      let mask ← createConstantWith type c fun c => c.bits.toInt - 1
      CreateProg.operation (.gmir .g_and) #[x, mask.res[0]!] #[type])
    (fun op => op)

/-! ### constant_fold_binops -/

/-- `c₁ op c₂` → the constant `fold c₁ c₂`, with both constants read as signed integers. -/
def constant_fold_binop_pattern (opcode : GMIR) (fold : Int → Int → Int) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let c₁ ← matchConstant type
      let c₂ ← matchConstant type
      let _ ← MatchProg.root (.gmir opcode) #[c₁.res[0]!, c₂.res[0]!] #[type]
      return (type, c₁.properties, c₂.properties))
    (fun (type, c₁, c₂) =>
      createConstantWith type (c₁, c₂) fun (c₁, c₂) => fold c₁.bits.toInt c₂.bits.toInt)
    (fun op => op)

/-! ### select_combines

A `g_select` condition wider than `i1` is true when it is nonzero (see `GMIR.selectNonzero`). The
combines that read the condition as a boolean, as LLVM's `match_selects` and `select_not` do, only
match an `i1` condition.
-/

/-- `c ? x : x` → `x`. -/
def select_same_val_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let condType ← MatchProg.type (Attr := IntegerType)
      let c ← MatchProg.value condType
      let x ← MatchProg.value type
      let _ ← MatchProg.root (.gmir .g_select) #[c, x, x] #[type]
      return x)
    pure (fun x => x)

/-- `c ? x : y` → `x` for a nonzero constant `c` when `nonzero` is set, and `0 ? x : y` → `y`
    otherwise. -/
def select_constant_cmp_pattern (nonzero : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let condType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let c ← matchConstant condType fun c => (c.bits != 0) == nonzero
      let _ ← MatchProg.root (.gmir .g_select) #[c.res[0]!, x, y] #[type]
      return if nonzero then x else y)
    pure (fun v => v)

/-- `(icmp pred x, y) ? x : y` → `minmax x, y`, if `minmax` is legal for the type. -/
def select_to_iminmax_pattern (info : LegalizerInfo) (pred : Data.LLVM.IntPred) (minmax : GMIR) :
    Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let condType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let icmp ← MatchProg.operation (.gmir .g_icmp) #[x, y] #[condType] (·.predicate = pred)
      let _ ← MatchProg.root (.gmir .g_select) #[icmp.res[0]!, x, y] #[type]
      MatchProg.matchNative type fun type =>
        info.isLegal minmax #[type] (default : propertiesOf minmax)
      return (type, x, y))
    (fun (type, x, y) => CreateProg.operation (.gmir minmax) #[x, y] #[type])
    (fun op => op)

/-- `cast (c ? x : y)` → `c ? (cast x) : (cast y)` for `cast` ∈ {`g_zext`, `g_trunc`}, if the new
    `g_select` is legal. As in LLVM, the new casts get no flags. Unlike LLVM, the `g_select` may
    have other uses. -/
def select_of_cast_pattern (info : LegalizerInfo) (cast : GMIR) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let srcType ← MatchProg.type (Attr := IntegerType)
      let condType ← MatchProg.type (Attr := IntegerType)
      let c ← MatchProg.value condType
      let x ← MatchProg.value srcType
      let y ← MatchProg.value srcType
      let select ← MatchProg.operation (.gmir .g_select) #[c, x, y] #[srcType]
      let _ ← MatchProg.root (.gmir cast) #[select.res[0]!] #[type]
      MatchProg.matchNative (type, condType) fun (type, condType) =>
        info.isLegal .g_select #[type, condType] ()
      return (type, c, x, y))
    (fun (type, c, x, y) => do
      let castX ← CreateProg.operation (.gmir cast) #[x] #[type]
      let castY ← CreateProg.operation (.gmir cast) #[y] #[type]
      CreateProg.operation (.gmir .g_select) #[c, castX.res[0]!, castY.res[0]!] #[type])
    (fun op => op)

/-- `(c ^ -1) ? x : y` → `c ? y : x` for an `i1` condition `c`. -/
def select_not_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType)
      let condType ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 1)
      let c ← MatchProg.value condType
      let x ← MatchProg.value type
      let y ← MatchProg.value type
      let allOnes ← matchConstant condType (·.bits = -1)
      let not ← MatchProg.operation (.gmir .g_xor) #[c, allOnes.res[0]!] #[condType]
      let _ ← MatchProg.root (.gmir .g_select) #[not.res[0]!, x, y] #[type]
      return (type, c, x, y))
    (fun (type, c, x, y) => CreateProg.operation (.gmir .g_select) #[c, y, x] #[type])
    (fun op => op)

/-- `c ? 1 : 0` → `c` and, when `invert` is set, `c ? 0 : 1` → `c ^ 1`, for an `i1` select of an
    `i1` condition `c`. The `g_xor` must be legal. -/
def select_bool_pattern (info : LegalizerInfo) (invert : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 1)
      let c ← MatchProg.value type
      let t ← matchConstant type (·.bits.toNat = if invert then 0 else 1)
      let f ← matchConstant type (·.bits.toNat = if invert then 1 else 0)
      let _ ← MatchProg.root (.gmir .g_select) #[c, t.res[0]!, f.res[0]!] #[type]
      if invert then
        MatchProg.matchNative type fun type => info.isLegal .g_xor #[type] ()
      return (type, c))
    (fun (type, c) => do
      if invert then
        let one ← createConstant type 1
        let not ← CreateProg.operation (.gmir .g_xor) #[c, one.res[0]!] #[type]
        return not.res[0]!
      return c)
    (fun v => v)

/-- `c ? e : 0` → `ext c` and, when `invert` is set, `c ? 0 : e` → `ext (c ^ 1)`, for an `i1`
    condition `c` and a wider select, where `(ext, e)` is `(g_zext, 1)` or `(g_sext, -1)`. The new
    operations must be legal. -/
def select_of_bool_constants_pattern (info : LegalizerInfo) (ext : GMIR) (invert : Bool) :
    Pattern OpCode :=
  let e : Int := if ext = .g_sext then -1 else 1
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (·.bitwidth > 1)
      let condType ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 1)
      let c ← MatchProg.value condType
      let t ← matchConstant type (·.bits.toInt = if invert then 0 else e)
      let f ← matchConstant type (·.bits.toInt = if invert then e else 0)
      let _ ← MatchProg.root (.gmir .g_select) #[c, t.res[0]!, f.res[0]!] #[type]
      MatchProg.matchNative (type, condType) fun (type, condType) =>
        info.isLegal ext #[type, condType] (default : propertiesOf ext) &&
          (!invert || info.isLegal .g_xor #[condType] ())
      return (type, condType, c))
    (fun (type, condType, c) => do
      let cond ← if invert then do
          let one ← createConstant condType 1
          let not ← CreateProg.operation (.gmir .g_xor) #[c, one.res[0]!] #[condType]
          pure not.res[0]!
        else pure c
      CreateProg.operation (.gmir ext) #[cond] #[type])
    (fun op => op)

/-- The select combines, which take the `LegalizerInfo` of the target. -/
def selectCombines (info : LegalizerInfo) : Array (CompiledPattern OpCode) :=
  let patterns : Array (Pattern OpCode) :=
  #[select_same_val_pattern, select_constant_cmp_pattern true, select_constant_cmp_pattern false,
    select_not_pattern] ++
  #[(Data.LLVM.IntPred.ugt, GMIR.g_umax), (.uge, .g_umax), (.sgt, .g_smax), (.sge, .g_smax),
    (.ult, .g_umin), (.ule, .g_umin), (.slt, .g_smin), (.sle, .g_smin)].map
      (fun (pred, minmax) => select_to_iminmax_pattern info pred minmax) ++
  #[select_of_cast_pattern info .g_zext, select_of_cast_pattern info .g_trunc,
    select_bool_pattern info false, select_bool_pattern info true] ++
  (#[GMIR.g_zext, .g_sext].flatMap fun ext =>
      #[false, true].map (select_of_bool_constants_pattern info ext ·))
  patterns.map (·.compile)

/-! ### Combine list -/

/-- The combines above, in the order the combiner tries them. -/
def combines : Array (CompiledPattern OpCode) :=
  let patterns : Array (Pattern OpCode) :=
  (#[GMIR.g_shl, .g_lshr, .g_ashr, .g_and].flatMap fun hand =>
      #[GMIR.g_and, .g_or, .g_xor].map (hoist_logic_op_pattern · hand)) ++
  #[sub_add_reg_x_add_y_sub_y_pattern, sub_add_reg_x_add_y_sub_x_pattern,
    sub_add_reg_negate_pattern false, sub_add_reg_negate_pattern true,
    xor_of_and_with_same_reg_pattern, trunc_of_ext_pattern .g_zext, mulo_by_2_pattern,
    add_shift_pattern false, add_shift_pattern true] ++
  (#[GMIR.g_add, .g_sub, .g_xor].flatMap fun opcode =>
      #[Data.LLVM.IntPred.eq, .ne].map (redundant_binop_in_equality_pattern opcode ·)) ++
  #[not_cmp_fold_pattern .eq .ne, not_cmp_fold_pattern .ne .eq,
    not_cmp_fold_pattern .ugt .ule, not_cmp_fold_pattern .uge .ult,
    not_cmp_fold_pattern .sgt .sle, not_cmp_fold_pattern .sge .slt,
    double_icmp_zero_pattern .g_and .eq, double_icmp_zero_pattern .g_or .ne,
    NotAPlusNegOne_pattern, sub_one_from_sub_pattern,
    APlusC1MinusC2_pattern, C2MinusAPlusC1_pattern, AMinusC1MinusC2_pattern,
    C1MinusAMinusC2_pattern, AMinusC1PlusC2_pattern,
    or_and_xor_to_xor_or_pattern .g_or .g_and, or_and_xor_to_xor_or_pattern .g_and .g_or,
    combine_or_of_and_pattern true true, combine_or_of_and_pattern true false,
    combine_or_of_and_pattern false true, combine_or_of_and_pattern false false,
    AMinusBMinusC_pattern] ++
  #[GMIR.g_shl, .g_lshr, .g_ashr, .g_mul].map binop_left_to_zero_pattern ++
  #[simplify_neg_minmax_pattern .g_smax .g_smin, simplify_neg_minmax_pattern .g_umax .g_umin,
    simplify_neg_minmax_pattern .g_smin .g_smax, simplify_neg_minmax_pattern .g_umin .g_umax,
    trunc_of_ext_pattern .g_sext, ext_of_ext_pattern .g_zext, ext_of_ext_pattern .g_sext,
    sub_of_mul_const_pattern, canonicalize_icmp_pattern,
    bitreverse_shift_pattern .g_shl .g_lshr, bitreverse_shift_pattern .g_lshr .g_shl,
    udiv_by_pow2_pattern, mul_to_shl_pattern, urem_pow2_to_mask_pattern] ++
  #[(GMIR.g_add, fun a b => a + b), (.g_sub, (· - ·)), (.g_mul, (· * ·)),
    (.g_smin, min), (.g_smax, max)].map (fun (opcode, fold) => constant_fold_binop_pattern opcode fold) ++
  #[sub_minus_one_pattern] ++
  #[GMIR.g_sub, .g_add, .g_or, .g_xor, .g_shl, .g_ashr, .g_lshr].map right_identity_zero_pattern ++
  #[right_identity_one_int_pattern, binop_same_val_pattern .g_and, binop_same_val_pattern .g_or,
    same_val_zero_pattern .g_sub, same_val_zero_pattern .g_xor, binop_right_to_zero_pattern,
    mul_by_neg_one_pattern, or_and_xor_to_or_pattern .g_or .g_and,
    or_and_xor_to_or_pattern .g_and .g_or, add_sub_reg_0_pattern, add_sub_reg_1_pattern,
    APlusBMinusCMinusB_pattern, AMinusBMinusCMinusC_pattern, ZeroMinusAPlusB_pattern,
    APlusZeroMinusB_pattern, AMinusBPlusCMinusA_pattern, AMinusBPlusBMinusC_pattern,
    APlusBMinusAPlusC_pattern true, APlusBMinusAPlusC_pattern false, AMinusZeroMinusB_pattern,
    AMinusBMinusA_pattern]
  patterns.map (·.compile)

end

end Veir
