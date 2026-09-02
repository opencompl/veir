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
| .verif op => Verif.propertiesOf op
| .builtin op => Builtin.propertiesOf op
| .func op => Func.propertiesOf op
| .datapath op => Datapath.propertiesOf op
| .pdl op => PDL.propertiesOf op
| .io op => Io.propertiesOf op
| .test op => Test.propertiesOf op
| .felt op => Felt.propertiesOf op
| .cir op => Cir.propertiesOf op

/--
  What are the memory effects of an operation with this opcode and these
  properties?
-/
@[get_effects]
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
  | .verif op, props => Verif.getEffects op props
  | .builtin op, props => Builtin.getEffects op props
  | .func op, props => Func.getEffects op props
  | .datapath op, props => Datapath.getEffects op props
  | .pdl op, props => PDL.getEffects op props
  | .io op, props => Io.getEffects op props
  | .test op, props => Test.getEffects op props
  | .felt op, props => Felt.getEffects op props
  | .cir op, props => Cir.getEffects op props

/--
  Return the kind of the region with the given index inside this operation.
-/
def OpCode.getRegionKind (opCode : OpCode) (index : Nat) : RegionKind :=
  match opCode with
  | .arith op => HasOpInfo.getRegionKind op index
  | .llvm op => HasOpInfo.getRegionKind op index
  | .riscv op => HasOpInfo.getRegionKind op index
  | .riscv_cf op => HasOpInfo.getRegionKind op index
  | .riscv_stack op => HasOpInfo.getRegionKind op index
  | .rv64 op => HasOpInfo.getRegionKind op index
  | .mod_arith op => HasOpInfo.getRegionKind op index
  | .cf op => HasOpInfo.getRegionKind op index
  | .comb op => HasOpInfo.getRegionKind op index
  | .hw op => HasOpInfo.getRegionKind op index
  | .verif op => HasOpInfo.getRegionKind op index
  | .builtin op => HasOpInfo.getRegionKind op index
  | .func op => HasOpInfo.getRegionKind op index
  | .datapath op => HasOpInfo.getRegionKind op index
  | .pdl op => HasOpInfo.getRegionKind op index
  | .io op => HasOpInfo.getRegionKind op index
  | .test op => HasOpInfo.getRegionKind op index
  | .felt op => HasOpInfo.getRegionKind op index
  | .cir op => HasOpInfo.getRegionKind op index

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
  | .verif op => Verif.hasSSADominance op index
  | .builtin op => Builtin.hasSSADominance op index
  | .func op => Func.hasSSADominance op index
  | .datapath op => Datapath.hasSSADominance op index
  | .pdl op => PDL.hasSSADominance op index
  | .io op => Io.hasSSADominance op index
  | .test op => Test.hasSSADominance op index
  | .felt op => Felt.hasSSADominance op index
  | .cir op => Cir.hasSSADominance op index

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
  | .verif op => HasOpInfo.hasNoTerminator op index
  | .builtin op => HasOpInfo.hasNoTerminator op index
  | .func op => HasOpInfo.hasNoTerminator op index
  | .datapath op => HasOpInfo.hasNoTerminator op index
  | .pdl op => HasOpInfo.hasNoTerminator op index
  | .io op => HasOpInfo.hasNoTerminator op index
  | .test op => HasOpInfo.hasNoTerminator op index
  | .felt op => HasOpInfo.hasNoTerminator op index
  | .cir op => HasOpInfo.hasNoTerminator op index

/-- Whether this opcode carries MLIR's `IsolatedFromAbove` trait. -/
def OpCode.isIsolatedFromAbove (opCode : OpCode) : Bool :=
  match opCode with
  | .arith op => HasOpInfo.isIsolatedFromAbove op
  | .llvm op => HasOpInfo.isIsolatedFromAbove op
  | .riscv op => HasOpInfo.isIsolatedFromAbove op
  | .riscv_cf op => HasOpInfo.isIsolatedFromAbove op
  | .riscv_stack op => HasOpInfo.isIsolatedFromAbove op
  | .rv64 op => HasOpInfo.isIsolatedFromAbove op
  | .mod_arith op => HasOpInfo.isIsolatedFromAbove op
  | .cf op => HasOpInfo.isIsolatedFromAbove op
  | .comb op => HasOpInfo.isIsolatedFromAbove op
  | .hw op => HasOpInfo.isIsolatedFromAbove op
  | .verif op => HasOpInfo.isIsolatedFromAbove op
  | .builtin op => HasOpInfo.isIsolatedFromAbove op
  | .func op => HasOpInfo.isIsolatedFromAbove op
  | .datapath op => HasOpInfo.isIsolatedFromAbove op
  | .pdl op => HasOpInfo.isIsolatedFromAbove op
  | .io op => HasOpInfo.isIsolatedFromAbove op
  | .test op => HasOpInfo.isIsolatedFromAbove op
  | .felt op => HasOpInfo.isIsolatedFromAbove op
  | .cir op => HasOpInfo.isIsolatedFromAbove op

/--
  Does this OpCode count as an MLIR basic block terminator? Dialects that do
  not say otherwise inherit the `HasOpInfo` default of `false`.
-/
@[is_terminator]
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
  | .verif op => HasOpInfo.isTerminator op
  | .builtin op => HasOpInfo.isTerminator op
  | .func op => HasOpInfo.isTerminator op
  | .datapath op => HasOpInfo.isTerminator op
  | .pdl op => HasOpInfo.isTerminator op
  | .io op => HasOpInfo.isTerminator op
  | .test op => HasOpInfo.isTerminator op
  | .felt op => HasOpInfo.isTerminator op
  | .cir op => HasOpInfo.isTerminator op

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
  | .verif op => Verif.isConstantLike op
  | .builtin op => Builtin.isConstantLike op
  | .func op => Func.isConstantLike op
  | .datapath op => Datapath.isConstantLike op
  | .pdl op => PDL.isConstantLike op
  | .io op => Io.isConstantLike op
  | .test op => Test.isConstantLike op
  | .felt op => Felt.isConstantLike op
  | .cir op => Cir.isConstantLike op

/--
  Does an operation with this opcode produce a wholly poisoned result whenever
  any one of its operands is wholly poison?
-/
def OpCode.propagatesPoison (opCode : OpCode) : Bool :=
  match opCode with
  | .arith op => HasOpInfo.propagatesPoison op
  | .llvm op => HasOpInfo.propagatesPoison op
  | .riscv op => HasOpInfo.propagatesPoison op
  | .riscv_cf op => HasOpInfo.propagatesPoison op
  | .riscv_stack op => HasOpInfo.propagatesPoison op
  | .rv64 op => HasOpInfo.propagatesPoison op
  | .mod_arith op => HasOpInfo.propagatesPoison op
  | .cf op => HasOpInfo.propagatesPoison op
  | .comb op => HasOpInfo.propagatesPoison op
  | .hw op => HasOpInfo.propagatesPoison op
  | .verif op => HasOpInfo.propagatesPoison op
  | .builtin op => HasOpInfo.propagatesPoison op
  | .func op => HasOpInfo.propagatesPoison op
  | .datapath op => HasOpInfo.propagatesPoison op
  | .pdl op => HasOpInfo.propagatesPoison op
  | .io op => HasOpInfo.propagatesPoison op
  | .test op => HasOpInfo.propagatesPoison op
  | .felt op => HasOpInfo.propagatesPoison op
  | .cir op => HasOpInfo.propagatesPoison op

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
  | .verif op => Verif.fromAttrDict op attrDict
  | .builtin op => Builtin.fromAttrDict op attrDict
  | .func op => Func.fromAttrDict op attrDict
  | .datapath op => Datapath.fromAttrDict op attrDict
  | .pdl op => PDL.fromAttrDict op attrDict
  | .io op => Io.fromAttrDict op attrDict
  | .test op => Test.fromAttrDict op attrDict
  | .felt op => Felt.fromAttrDict op attrDict
  | .cir op => Cir.fromAttrDict op attrDict

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
  | .verif op, props => Verif.toAttrDict op props
  | .builtin op, props => Builtin.toAttrDict op props
  | .func op, props => Func.toAttrDict op props
  | .datapath op, props => Datapath.toAttrDict op props
  | .pdl op, props => PDL.toAttrDict op props
  | .io op, props => Io.toAttrDict op props
  | .test op, props => Test.toAttrDict op props
  | .felt op, props => Felt.toAttrDict op props
  | .cir op, props => Cir.toAttrDict op props

instance : IsOpCode OpCode where
  fromName := OpCode.fromName
  name := OpCode.name
  propertiesOf := _propertiesOf
  fromAttrDict := Properties.fromAttrDict
  toAttrDict := Properties.toAttrDict

/-- Function-interface information assembled from the registered dialects. -/
def OpCode.functionInterface? (opCode : OpCode) : Option (FunctionOpInterface (_propertiesOf opCode)) :=
  match opCode with
  | .arith op => HasOpInfo.functionInterface? op
  | .llvm op => HasOpInfo.functionInterface? op
  | .riscv op => HasOpInfo.functionInterface? op
  | .riscv_cf op => HasOpInfo.functionInterface? op
  | .riscv_stack op => HasOpInfo.functionInterface? op
  | .rv64 op => HasOpInfo.functionInterface? op
  | .mod_arith op => HasOpInfo.functionInterface? op
  | .cf op => HasOpInfo.functionInterface? op
  | .comb op => HasOpInfo.functionInterface? op
  | .hw op => HasOpInfo.functionInterface? op
  | .verif op => HasOpInfo.functionInterface? op
  | .builtin op => HasOpInfo.functionInterface? op
  | .func op => HasOpInfo.functionInterface? op
  | .datapath op => HasOpInfo.functionInterface? op
  | .pdl op => HasOpInfo.functionInterface? op
  | .io op => HasOpInfo.functionInterface? op
  | .test op => HasOpInfo.functionInterface? op
  | .felt op => HasOpInfo.functionInterface? op
  | .cir op => HasOpInfo.functionInterface? op

#generate_has_dialect_instances OpCode

@[expose]
def OpCode.verifyLocalInvariants (opCode : OpCode) (op : OperationPtr)
    (ctx : WfIRContext OpCode) (opIn : op.InBounds ctx.raw) : Except String Unit :=
  match opCode with
  | .builtin opType => Builtin.verifyLocalInvariants opType op ctx opIn
  | .arith opType => Arith.verifyLocalInvariants opType op ctx opIn
  | .datapath opType => Datapath.verifyLocalInvariants opType op ctx opIn
  | .func opType => Func.verifyLocalInvariants opType op ctx opIn
  | .cf opType => Cf.verifyLocalInvariants opType op ctx opIn
  | .pdl opType => PDL.verifyLocalInvariants opType op ctx opIn
  | .test .test => pure ()
  | .llvm opType => Llvm.verifyLocalInvariants opType op ctx opIn
  | .mod_arith opType => Mod_Arith.verifyLocalInvariants opType op ctx opIn
  | .riscv opType => Riscv.verifyLocalInvariants opType op ctx opIn
  | .riscv_cf opType => Riscv_Cf.verifyLocalInvariants opType op ctx opIn
  | .riscv_stack opType => Riscv_Stack.verifyLocalInvariants opType op ctx opIn
  | .rv64 opType => Rv64.verifyLocalInvariants opType op ctx opIn
  | .comb opType => Comb.verifyLocalInvariants opType op ctx opIn
  | .hw opType => HW.verifyLocalInvariants opType op ctx opIn
  | .verif opType => Verif.verifyLocalInvariants opType op ctx opIn
  | .felt opType => Felt.verifyLocalInvariants opType op ctx opIn
  | .cir opType => Cir.verifyLocalInvariants opType op ctx opIn
  | .io opType => Io.verifyLocalInvariants opType op ctx opIn

instance : HasOpInfo OpCode where
  verifyLocalInvariants := OpCode.verifyLocalInvariants
  getEffects := OpCode.getEffects
  isConstantLike := OpCode.isConstantLike
  propagatesPoison := OpCode.propagatesPoison
  functionInterface? := OpCode.functionInterface?
  getRegionKind := OpCode.getRegionKind
  hasSSADominance := OpCode.hasSSADominance
  hasNoTerminator := OpCode.hasNoTerminator
  isTerminator := OpCode.isTerminator
  isIsolatedFromAbove := OpCode.isIsolatedFromAbove

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
    | .felt op => Felt.materializeConstant op value type
    -- Listed rather than folded into a catch-all so that adding a dialect
    -- fails to compile until it decides how, or whether, to materialize.
    | .riscv_cf _ | .riscv_stack _ | .rv64 _ | .cf _ | .builtin _
    | .verif _
    | .func _ | .datapath _ | .pdl _ | .cir _ | .io _ | .test _ => none
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
  | .mod_arith .add | .mod_arith .mul
  | .felt .add | .felt .mul
  | .felt .bit_and | .felt .bit_or | .felt .bit_xor
  | .cir .add | .cir .mul | .cir .and | .cir .or | .cir .xor | .cir .min | .cir .max => true
  | _ => false
