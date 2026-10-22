import Veir.InstSimplify.IS2143
namespace Veir.InstSimplify.IS2145
def pattern : Veir.Puddle.Pattern Veir.OpCode := IS2143.pattern true
theorem valid : Veir.Puddle.Pattern.Valid pattern := IS2143.valid true
end Veir.InstSimplify.IS2145
