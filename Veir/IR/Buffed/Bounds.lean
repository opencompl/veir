
instance : HAdd Nat (Std.Rco Int) (Std.Rco Int) where
  hAdd x y := (x + y.lower)...(x + y.upper)

section in_bounds
variable [HasOpInfo OpInfo]

/-! ## ValueImpl -/

section value_impl

def ValueImplMPtr.range (ptr : ValueImplMPtr) :=
  ptr.toNat + ValueImpl.range

@[grind]
def ValueImplMPtr.InBoundsBytes (ptr : ValueImplMPtr) (bctx : IRContext OpInfo) :=
  IsIncludedIN ptr.range bctx.mem.range

@[grind, inline]
def ValueImplOPtr.isNone (optr : ValueImplOPtr) := optr = (-1 : UInt64)

@[grind, inline]
def ValueImplOPtr.toM (optr : ValueImplOPtr) : ValueImplMPtr := optr

@[grind]
def ValueImplOPtr.InBoundsBytes (ptr : ValueImplOPtr) (bctx : IRContext OpInfo) : Prop :=
  (¬ ptr.isNone) → ptr.toM.InBoundsBytes bctx

end value_impl

/-! ## OpResult -/

section op_result

def OpResultMPtr.range (ptr : OpResultMPtr) :=
  ptr.toNat + OpResult.range

@[grind]
def OpResultMPtr.InBoundsBytes (ptr : OpResultMPtr) (bctx : IRContext OpInfo) :=
  IsIncludedIN ptr.range bctx.mem.range

@[grind, inline]
def OpResultOPtr.isNone (optr : OpResultOPtr) := optr = (-1 : UInt64)

@[grind, inline]
def OpResultOPtr.toM (optr : OpResultOPtr) : OpResultMPtr := optr

@[grind]
def OpResultOPtr.InBoundsBytes (ptr : OpResultOPtr) (bctx : IRContext OpInfo) : Prop :=
  (¬ ptr.isNone) → ptr.toM.InBoundsBytes bctx

end op_result

/-! ## BlockArgument -/

section block_argument

def BlockArgumentMPtr.range (ptr : BlockArgumentMPtr) :=
  ptr.toNat + BlockArgument.range

@[grind]
def BlockArgumentMPtr.InBoundsBytes (ptr : BlockArgumentMPtr) (bctx : IRContext OpInfo) :=
  IsIncludedIN ptr.range bctx.mem.range

@[grind, inline]
def BlockArgumentOPtr.isNone (optr : BlockArgumentOPtr) := optr = (-1 : UInt64)

@[grind, inline]
def BlockArgumentOPtr.toM (optr : BlockArgumentOPtr) : BlockArgumentMPtr := optr

@[grind]
def BlockArgumentOPtr.InBoundsBytes (ptr : BlockArgumentOPtr) (bctx : IRContext OpInfo) : Prop :=
  (¬ ptr.isNone) → ptr.toM.InBoundsBytes bctx

end block_argument

/-! ## OpOperand -/

section op_operand

def OpOperandMPtr.range (ptr : OpOperandMPtr) :=
  ptr.toNat + OpOperand.range

@[grind]
def OpOperandMPtr.InBoundsBytes (ptr : OpOperandMPtr) (bctx : IRContext OpInfo) :=
  IsIncludedIN ptr.range bctx.mem.range

@[grind, inline]
def OpOperandOPtr.isNone (optr : OpOperandOPtr) := optr = (-1 : UInt64)

@[grind, inline]
def OpOperandOPtr.toM (optr : OpOperandOPtr) : OpOperandMPtr := optr

@[grind]
def OpOperandOPtr.InBoundsBytes (ptr : OpOperandOPtr) (bctx : IRContext OpInfo) : Prop :=
  (¬ ptr.isNone) → ptr.toM.InBoundsBytes bctx

end op_operand

/-! ## BlockOperand -/

section block_operand

def BlockOperandMPtr.range (ptr : BlockOperandMPtr) :=
  ptr.toNat + BlockOperand.range

@[grind]
def BlockOperandMPtr.InBoundsBytes (ptr : BlockOperandMPtr) (bctx : IRContext OpInfo) :=
  IsIncludedIN ptr.range bctx.mem.range

@[grind, inline]
def BlockOperandOPtr.isNone (optr : BlockOperandOPtr) := optr = (-1 : UInt64)

@[grind, inline]
def BlockOperandOPtr.toM (optr : BlockOperandOPtr) : BlockOperandMPtr := optr

@[grind]
def BlockOperandOPtr.InBoundsBytes (ptr : BlockOperandOPtr) (bctx : IRContext OpInfo) : Prop :=
  (¬ ptr.isNone) → ptr.toM.InBoundsBytes bctx

end block_operand

/-! ## Operation -/

section operation

@[grind]
def OperationMPtr.toH (ptr : OperationMPtr) : OperationPtr := ⟨ptr.toNat⟩

def OperationMPtr.range (ptr : OperationMPtr) (ctx : Veir.IRContext OpInfo) (ib : ptr.toH.InBounds ctx := by grind) :=
  ptr.toNat + Operation.range ptr.toH ctx ib

@[grind]
def OperationMPtr.InBoundsBytes (ptr : OperationMPtr) (op : OperationPtr)
    (ctx : Veir.IRContext OpInfo) (ib : op.InBounds ctx) (bctx : IRContext OpInfo) :=
  IsIncludedIN (OperationMPtr.range ptr op ctx ib) bctx.mem.range

@[grind, inline]
def OperationOPtr.isNone (optr : OperationOPtr) := optr = (-1 : UInt64)

@[grind, inline]
def OperationOPtr.toM (optr : OperationOPtr) : OperationMPtr := optr

@[grind]
def OperationOPtr.InBoundsBytes (ptr : OperationOPtr) (op : OperationPtr)
    (ctx : Veir.IRContext OpInfo) (ib : op.InBounds ctx) (bctx : IRContext OpInfo) : Prop :=
  (¬ ptr.isNone) → OperationMPtr.InBoundsBytes (OperationOPtr.toM ptr) op ctx ib bctx

end operation

/-! ## Block -/

section block

def BlockMPtr.range (ptr : BlockMPtr) (bl : BlockPtr)
    (ctx : Veir.IRContext OpInfo) (ib : bl.InBounds ctx) :=
  ptr.toNat + Block.range bl ctx ib

@[grind]
def BlockMPtr.InBoundsBytes (ptr : BlockMPtr) (bl : BlockPtr)
    (ctx : Veir.IRContext OpInfo) (ib : bl.InBounds ctx) (bctx : IRContext OpInfo) :=
  IsIncludedIN (ptr.range bl ctx ib) bctx.mem.range

@[grind, inline]
def BlockOPtr.isNone (optr : BlockOPtr) := optr = (-1 : UInt64)

@[grind, inline]
def BlockOPtr.toM (optr : BlockOPtr) : BlockMPtr := optr

@[grind]
def BlockOPtr.InBoundsBytes (ptr : BlockOPtr) (bl : BlockPtr)
    (ctx : Veir.IRContext OpInfo) (ib : bl.InBounds ctx) (bctx : IRContext OpInfo) : Prop :=
  (¬ ptr.isNone) → BlockMPtr.InBoundsBytes (BlockOPtr.toM ptr) bl ctx ib bctx

end block

/-! ## Region -/

section region

def RegionMPtr.range (ptr : RegionMPtr) :=
  ptr.toNat + Region.range

@[grind]
def RegionMPtr.InBoundsBytes (ptr : RegionMPtr) (bctx : IRContext OpInfo) :=
  IsIncludedIN ptr.range bctx.mem.range

@[grind, inline]
def RegionOPtr.isNone (optr : RegionOPtr) := optr = (-1 : UInt64)

@[grind, inline]
def RegionOPtr.toM (optr : RegionOPtr) : RegionMPtr := optr

@[grind]
def RegionOPtr.InBoundsBytes (ptr : RegionOPtr) (bctx : IRContext OpInfo) : Prop :=
  (¬ ptr.isNone) → ptr.toM.InBoundsBytes bctx

end region

end in_bounds
