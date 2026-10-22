import Veir.InstSimplify.IS2167
namespace Veir.InstSimplify.IS2169
def pattern : Veir.Puddle.Pattern Veir.OpCode := IS2167.pattern true
theorem valid : Veir.Puddle.Pattern.Valid pattern := IS2167.valid true
end Veir.InstSimplify.IS2169
