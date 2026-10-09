module

public import Veir.Parser.Parser

public section

namespace Veir.Parser

/-- A textual result group whose indices lie within the operation's result count. -/
structure BoundedResultGroup (size : Nat) where
  name : ByteArray
  count : Nat
  offset : Nat
  pos : Location
  inBounds : offset + count ≤ size

/-- Number the remaining result groups while retaining their bound on the total result count. -/
private def boundResultGroupsFrom (results : List (ByteArray × Nat × Location))
    (size offset : Nat)
    (h : offset + (results.map (fun r => r.2.1)).sum = size)
    (acc : List (BoundedResultGroup size)) : List (BoundedResultGroup size) :=
  match results with
  | [] => acc.reverse
  | (name, count, pos) :: rest =>
    let group : BoundedResultGroup size :=
      { name, count, offset, pos
        inBounds := by
          simp only [List.map_cons, List.sum_cons] at h
          omega }
    boundResultGroupsFrom rest size (offset + count) (by
      simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using h) (group :: acc)

/-- Attach bounds certificates to result groups, preserving textual order. -/
def boundResultGroups (results : Array (ByteArray × Nat × Location)) :
    List (BoundedResultGroup ((results.toList.map (fun r => r.2.1)).sum)) :=
  boundResultGroupsFrom results.toList ((results.toList.map (fun r => r.2.1)).sum) 0 (by simp) []

end Veir.Parser
