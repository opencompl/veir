import Veir.InstSimplify.IS2430
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
/-- The explicitly commuted upstream return branch. -/
def IS2434 : Pattern OpCode := IS2430 true
theorem IS2434_valid : Pattern.Valid IS2434 := IS2430_valid true
end Veir.InstSimplify
