module

public import Veir.IR.Attribute
public meta import Veir.IR.Attribute

namespace Veir

public section

namespace RegisterInfo

/--
Registers the allocator never hands out:
- `x0` (`zero`) is hardwired to zero,
- `x2` (`sp`), `x3` (`gp`) and `x4` (`tp`) are the stack, global and thread pointers,
- `x8` (`s0`) is the frame pointer whenever llc needs one, writing it is a silent miscompile.
-/
def reserved : RegisterClass → Array Nat
  | .int => #[0, 2, 3, 4, 8]
  | .stack => #[]

/--
The registers the allocator hands out. In the order of:
- `t0`–`t2` (`x5`–`x7`), `t3`–`t6` (`x28`–`x31`), `a0`–`a7` (`x10`–`x17`): caller-saved,
- `s1` (`x9`), `s2`–`s11` (`x18`–`x27`): callee-saved,
- `ra` (`x1`): saved by llc's prologue, last as it is clobbered by every call.
-/
def allocOrder : RegisterClass → Array Nat
  | .int => #[5, 6, 7, 28, 29, 30, 31, 10, 11, 12, 13, 14, 15, 16, 17,
              9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 1]
  | .stack => #[]

/-- The registers that pass function arguments, in order: `a0`–`a7` (`x10`–`x17`). -/
def argRegisters : RegisterClass → Array Nat
  | .int => #[10, 11, 12, 13, 14, 15, 16, 17]
  | .stack => #[]

/-- The registers a callee must preserve: `s0`–`s11` (`x8`, `x9`, `x18`–`x27`). -/
def calleeSaved : RegisterClass → Array Nat
  | .int => #[8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
  | .stack => #[]

/-! The register sets are consistent with each other. -/

#guard (allocOrder .int).size = 27
#guard (allocOrder .int).all (· ∉ reserved .int)
#guard (List.range 32).all (fun r => r ∈ allocOrder .int || r ∈ reserved .int)
#guard (argRegisters .int).all (· ∈ allocOrder .int)

end RegisterInfo

end

end Veir
