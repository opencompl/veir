module

public import Veir.IR.Attribute

namespace Veir

public section

/--
  Stack data structure for managing registers that the allocater can hand out.
  `cls` determines the type of registers the stack handles
-/
structure RegisterStack (cls : RegisterClass) where
  /-- Indices of the registers released during allocation. -/
  free : List Int := []
  /-- The next virtual register index, used when `free` is empty. -/
  next : Nat
deriving Inhabited, DecidableEq, Repr

namespace RegisterStack

def pop {cls : RegisterClass} (s : RegisterStack cls) : RegisterType × RegisterStack cls :=
  match s.free with
  -- reuse registers in free stack
  | index :: rest => (RegisterType.mk cls (some index), {s with free := rest})
  -- if free stack is empty, get next virtual register index
  | [] => (RegisterType.mk cls (some (-((s.next : Int) + 1))), {s with next := s.next + 1})

def push {cls : RegisterClass} (s : RegisterStack cls) (index : Int) : RegisterStack cls :=
  {s with free := index :: s.free}

end RegisterStack

end

end Veir
