import Veir.InstSimplify.IS3985
namespace Veir.InstSimplify.IS4064
def pattern (signed : Bool) : Veir.Puddle.Pattern Veir.OpCode := IS3985.pattern signed true
theorem valid (signed : Bool) : Veir.Puddle.Pattern.Valid (pattern signed) := IS3985.valid signed true
end Veir.InstSimplify.IS4064
