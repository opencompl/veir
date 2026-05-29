module

public section

namespace Veir

/--
An algebraic definition of a lattice. In particular, no partial order is defined
on the domain.
-/
class LatticeElement (Domain : Type) extends BEq Domain where
  bottom : Domain
  top : Domain
  join : Domain -> Domain -> Domain
  meet : Domain -> Domain -> Domain

end Veir
