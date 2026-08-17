module

import Veir.Meta.OpCode

public import Veir.IR.Basic
public import Veir.OpCode

namespace Veir

public section

/--
  A type family that maps an operation code to the type of its properties.
  For operations that do not have any properties, the type is `Unit`.
-/
@[expose, properties_of]
def _propertiesOf (opCode : OpCode) : Type :=
match opCode with
| .arith op => Arith.propertiesOf op
| .llvm op => Llvm.propertiesOf op
| .riscv op => Riscv.propertiesOf op
| .riscv_cf op => Riscv_Cf.propertiesOf op
| .riscv_stack op => Riscv_Stack.propertiesOf op
| .rv64 op => Rv64.propertiesOf op
| .mod_arith op => Mod_Arith.propertiesOf op
| .cf op => Cf.propertiesOf op
| .comb op => Comb.propertiesOf op
| .hw op => HW.propertiesOf op
| .builtin op => Builtin.propertiesOf op
| .func op => Func.propertiesOf op
| .datapath op => Datapath.propertiesOf op
| .pdl op => PDL.propertiesOf op
| .test op => Test.propertiesOf op

/--
  What are the memory effects of an operation with this opcode and these
  properties?
-/
def OpCode.getEffects (opCode : OpCode) (props : _propertiesOf opCode) : MemoryEffects :=
  match opCode, props with
  | .arith op, props => Arith.getEffects op props
  | .llvm op, props => Llvm.getEffects op props
  | .riscv op, props => Riscv.getEffects op props
  | .riscv_cf op, props => Riscv_Cf.getEffects op props
  | .riscv_stack op, props => Riscv_Stack.getEffects op props
  | .rv64 op, props => Rv64.getEffects op props
  | .mod_arith op, props => Mod_Arith.getEffects op props
  | .cf op, props => Cf.getEffects op props
  | .comb op, props => Comb.getEffects op props
  | .hw op, props => HW.getEffects op props
  | .builtin op, props => Builtin.getEffects op props
  | .func op, props => Func.getEffects op props
  | .datapath op, props => Datapath.getEffects op props
  | .pdl op, props => PDL.getEffects op props
  | .test op, props => Test.getEffects op props

inductive RegionKind where
| SSACFG
| Graph
deriving Inhabited, Repr, DecidableEq

/--
  Return the kind of the region with the given index inside this operation.
  This mirrors MLIR's RegionKindInterface default: regions are SSACFG unless
  the operation is known to define graph regions.
-/
def OpCode.getRegionKind (opCode : OpCode) (_index : Nat) : RegionKind :=
  match opCode with
  | .builtin .module
  | .builtin .unregistered
  | .test .test => .Graph
  | _ => .SSACFG

/--
  Whether definitions in the indexed region of this opcode must dominate
  their uses.
-/
def OpCode.hasSSADominance (opCode : OpCode) (index : Nat) : Bool :=
  match opCode with
  | .arith op => Arith.hasSSADominance op index
  | .llvm op => Llvm.hasSSADominance op index
  | .riscv op => Riscv.hasSSADominance op index
  | .riscv_cf op => Riscv_Cf.hasSSADominance op index
  | .riscv_stack op => Riscv_Stack.hasSSADominance op index
  | .rv64 op => Rv64.hasSSADominance op index
  | .mod_arith op => Mod_Arith.hasSSADominance op index
  | .cf op => Cf.hasSSADominance op index
  | .comb op => Comb.hasSSADominance op index
  | .hw op => HW.hasSSADominance op index
  | .builtin op => Builtin.hasSSADominance op index
  | .func op => Func.hasSSADominance op index
  | .datapath op => Datapath.hasSSADominance op index
  | .pdl op => PDL.hasSSADominance op index
  | .test op => Test.hasSSADominance op index

/--
  Whether the indexed region of this opcode is exempt from the requirement
  that each of its blocks ends in a terminator. Dialects that do not say
  otherwise inherit the `HasOpInfo` default of `false`.
-/
def OpCode.hasNoTerminator (opCode : OpCode) (index : Nat) : Bool :=
  match opCode with
  | .arith op => HasOpInfo.hasNoTerminator op index
  | .llvm op => HasOpInfo.hasNoTerminator op index
  | .riscv op => HasOpInfo.hasNoTerminator op index
  | .riscv_cf op => HasOpInfo.hasNoTerminator op index
  | .riscv_stack op => HasOpInfo.hasNoTerminator op index
  | .rv64 op => HasOpInfo.hasNoTerminator op index
  | .mod_arith op => HasOpInfo.hasNoTerminator op index
  | .cf op => HasOpInfo.hasNoTerminator op index
  | .comb op => HasOpInfo.hasNoTerminator op index
  | .hw op => HasOpInfo.hasNoTerminator op index
  | .builtin op => HasOpInfo.hasNoTerminator op index
  | .func op => HasOpInfo.hasNoTerminator op index
  | .datapath op => HasOpInfo.hasNoTerminator op index
  | .pdl op => HasOpInfo.hasNoTerminator op index
  | .test op => HasOpInfo.hasNoTerminator op index

/--
  Does this OpCode count as an MLIR basic block terminator? Dialects that do
  not say otherwise inherit the `HasOpInfo` default of `false`.
-/
def OpCode.isTerminator (opCode : OpCode) : Bool :=
  match opCode with
  | .arith op => HasOpInfo.isTerminator op
  | .llvm op => HasOpInfo.isTerminator op
  | .riscv op => HasOpInfo.isTerminator op
  | .riscv_cf op => HasOpInfo.isTerminator op
  | .riscv_stack op => HasOpInfo.isTerminator op
  | .rv64 op => HasOpInfo.isTerminator op
  | .mod_arith op => HasOpInfo.isTerminator op
  | .cf op => HasOpInfo.isTerminator op
  | .comb op => HasOpInfo.isTerminator op
  | .hw op => HasOpInfo.isTerminator op
  | .builtin op => HasOpInfo.isTerminator op
  | .func op => HasOpInfo.isTerminator op
  | .datapath op => HasOpInfo.isTerminator op
  | .pdl op => HasOpInfo.isTerminator op
  | .test op => HasOpInfo.isTerminator op

/--
  Does this `OpCode` materialize a literal constant value, i.e. an op
  whose single result is a compile-time constant taken from its
  properties, with no SSA operands and no side effects?

  This is the analogue of MLIR's `ConstantLike` op trait, which likewise
  covers `llvm.mlir.poison`: poison is a perfectly good constant.
-/
def OpCode.isConstantLike (opCode : OpCode) : Bool :=
  match opCode with
  | .arith op => Arith.isConstantLike op
  | .llvm op => Llvm.isConstantLike op
  | .riscv op => Riscv.isConstantLike op
  | .riscv_cf op => Riscv_Cf.isConstantLike op
  | .riscv_stack op => Riscv_Stack.isConstantLike op
  | .rv64 op => Rv64.isConstantLike op
  | .mod_arith op => Mod_Arith.isConstantLike op
  | .cf op => Cf.isConstantLike op
  | .comb op => Comb.isConstantLike op
  | .hw op => HW.isConstantLike op
  | .builtin op => Builtin.isConstantLike op
  | .func op => Func.isConstantLike op
  | .datapath op => Datapath.isConstantLike op
  | .pdl op => PDL.isConstantLike op
  | .test op => Test.isConstantLike op

/--
  Does this `OpCode` act like a function, i.e. a symbol whose single
  region is the function body, with the signature carried in a
  `function_type` property?

  Dialects that do not override isFunctionLike default to false
  for all operations.
-/
def OpCode.isFunctionLike (opCode : OpCode) : Bool :=
  match opCode with
  | .arith op => HasOpInfo.isFunctionLike op
  | .llvm op => HasOpInfo.isFunctionLike op
  | .riscv op => HasOpInfo.isFunctionLike op
  | .riscv_cf op => HasOpInfo.isFunctionLike op
  | .riscv_stack op => HasOpInfo.isFunctionLike op
  | .rv64 op => HasOpInfo.isFunctionLike op
  | .mod_arith op => HasOpInfo.isFunctionLike op
  | .cf op => HasOpInfo.isFunctionLike op
  | .comb op => HasOpInfo.isFunctionLike op
  | .hw op => HasOpInfo.isFunctionLike op
  | .builtin op => HasOpInfo.isFunctionLike op
  | .func op => HasOpInfo.isFunctionLike op
  | .datapath op => HasOpInfo.isFunctionLike op
  | .pdl op => HasOpInfo.isFunctionLike op
  | .test op => HasOpInfo.isFunctionLike op

def Properties.fromAttrDict (opCode : OpCode) (attrDict : Std.HashMap ByteArray Attribute) :
    Except String (_propertiesOf opCode) :=
  match opCode with
  | .arith op => Arith.fromAttrDict op attrDict
  | .llvm op => Llvm.fromAttrDict op attrDict
  | .riscv op => Riscv.fromAttrDict op attrDict
  | .riscv_cf op => Riscv_Cf.fromAttrDict op attrDict
  | .riscv_stack op => Riscv_Stack.fromAttrDict op attrDict
  | .rv64 op => Rv64.fromAttrDict op attrDict
  | .mod_arith op => Mod_Arith.fromAttrDict op attrDict
  | .cf op => Cf.fromAttrDict op attrDict
  | .comb op => Comb.fromAttrDict op attrDict
  | .hw op => HW.fromAttrDict op attrDict
  | .builtin op => Builtin.fromAttrDict op attrDict
  | .func op => Func.fromAttrDict op attrDict
  | .datapath op => Datapath.fromAttrDict op attrDict
  | .pdl op => PDL.fromAttrDict op attrDict
  | .test op => Test.fromAttrDict op attrDict

/--
  Converts the properties of an operation into a dictionary of attributes.
-/
def Properties.toAttrDict
    (opCode : OpCode) (props : _propertiesOf opCode) :
    Std.HashMap ByteArray Attribute :=
  match opCode, props with
  | .arith op, props => Arith.toAttrDict op props
  | .llvm op, props => Llvm.toAttrDict op props
  | .riscv op, props => Riscv.toAttrDict op props
  | .riscv_cf op, props => Riscv_Cf.toAttrDict op props
  | .riscv_stack op, props => Riscv_Stack.toAttrDict op props
  | .rv64 op, props => Rv64.toAttrDict op props
  | .mod_arith op, props => Mod_Arith.toAttrDict op props
  | .cf op, props => Cf.toAttrDict op props
  | .comb op, props => Comb.toAttrDict op props
  | .hw op, props => HW.toAttrDict op props
  | .builtin op, props => Builtin.toAttrDict op props
  | .func op, props => Func.toAttrDict op props
  | .datapath op, props => Datapath.toAttrDict op props
  | .pdl op, props => PDL.toAttrDict op props
  | .test op, props => Test.toAttrDict op props

instance : HasOpInfo OpCode where
  fromName := OpCode.fromName
  name := OpCode.name
  propertiesOf := _propertiesOf
  fromAttrDict := Properties.fromAttrDict
  toAttrDict := Properties.toAttrDict
  getEffects := OpCode.getEffects
  isConstantLike := OpCode.isConstantLike
  isFunctionLike := OpCode.isFunctionLike
  hasSSADominance := OpCode.hasSSADominance
  hasNoTerminator := OpCode.hasNoTerminator
  isTerminator := OpCode.isTerminator

#generate_has_dialect_instances OpCode

/--
Ask the dialect of `opCode` how to represent a folded
constant. Dialects without a materializer, and values a dialect cannot
represent, decline to fold.
-/
def OpCode.materializeConstant (opCode : OpCode) (value : RuntimeValue)
    (type : TypeAttr) : Option (Materialized OpCode) := do
  let materialized ←
    match opCode with
    | .arith op => Arith.materializeConstant op value type
    | .comb op => Comb.materializeConstant op value type
    | .hw op => HW.materializeConstant op value type
    | .llvm op => Llvm.materializeConstant op value type
    | .mod_arith op => Mod_Arith.materializeConstant op value type
    | .riscv op => Riscv.materializeConstant op value type
    -- Listed rather than folded into a catch-all so that adding a dialect
    -- fails to compile until it decides how, or whether, to materialize.
    | .riscv_cf _ | .riscv_stack _ | .rv64 _ | .cf _ | .builtin _
    | .func _ | .datapath _ | .pdl _ | .test _ => none
  guard materialized.fst.isConstantLike
  return materialized

/--
  Is this `OpCode` commutative in its operands, i.e. `op x y` always
  computes the same value as `op y x`?
-/
def OpCode.isCommutative (opCode : OpCode) : Bool :=
  match opCode with
  | .arith .addi | .arith .muli
  | .arith .andi | .arith .ori | .arith .xori
  | .arith .maxsi | .arith .maxui | .arith .minsi | .arith .minui
  | .arith .addui_extended
  | .arith .mulsi_extended | .arith .mului_extended
  | .llvm .add | .llvm .mul
  | .llvm .and | .llvm .or | .llvm .xor
  | .llvm .intr__smax | .llvm .intr__smin | .llvm .intr__umax | .llvm .intr__umin
  | .llvm .intr__sadd__sat | .llvm .intr__uadd__sat
  | .llvm .fadd | .llvm .fmul
  | .riscv .add | .riscv .and | .riscv .or | .riscv .xor | .riscv .xnor
  | .riscv .mul | .riscv .mulh | .riscv .mulhu
  | .riscv .max | .riscv .maxu | .riscv .min | .riscv .minu
  | .riscv .addw | .riscv .mulw
  | .mod_arith .add | .mod_arith .mul => true
  | _ => false
