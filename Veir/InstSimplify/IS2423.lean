import Veir.InstSimplify.IS2419
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
/-- The explicitly commuted upstream return branch. -/
def IS2423 : Pattern OpCode := IS2419 true
theorem IS2423_valid : Pattern.Valid IS2423 := IS2419_valid true
end Veir.InstSimplify
