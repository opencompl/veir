import Veir.InstSimplify.IS3987
namespace Veir.InstSimplify.IS4066
def pattern (signed : Bool) : Veir.Puddle.Pattern Veir.OpCode := IS3987.pattern signed true
theorem valid (signed : Bool) : Veir.Puddle.Pattern.Valid (pattern signed) := IS3987.valid signed true
end Veir.InstSimplify.IS4066
