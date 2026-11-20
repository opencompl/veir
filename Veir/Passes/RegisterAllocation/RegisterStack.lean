module

public import Veir.IR.Attribute

namespace Veir

public section

structure RegisterStack where
  /-- Registers released during allocation. -/
  free : List RegisterType
  /-- The next virtual register index, used when `free` is empty. -/
  next : Nat
deriving Inhabited, DecidableEq, Repr

namespace RegisterStack

def pop (s: RegisterStack) : RegisterType × RegisterStack :=
  match s.free with
  -- reuse registers in free stack
  | r :: rest => (r, {s with free := rest})
  -- if free stack is empty, get next virtual register index
  | [] => (RegisterType.mk (some (-((s.next : Int) + 1))), {s with next := s.next + 1})

def push (s: RegisterStack) (r: RegisterType) : RegisterStack :=
  {s with free := r :: s.free}

end RegisterStack

end

end Veir
