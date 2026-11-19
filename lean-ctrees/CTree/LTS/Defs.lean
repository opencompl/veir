module

public section

namespace LTS

inductive label O where
  | tau
  | obs (o : O)

structure LTS where
  observable : Type u
  state : Type u
  trans : label observable → state → state → Prop
      
end LTS

