from xdsl.parser import Parser
from xdsl.printer import Printer
from xdsl.context import Context
from xdsl.rewriter import Rewriter
from xdsl.dialects.builtin import i32, StringAttr

def __main__():
    ctx = Context(allow_unregistered=True)
    with open("sqlite3.mlir", "r") as f:
        module = Parser(ctx, f.read()).parse_module()
    for op in module.walk():
        if "op_name__" not in op.attributes:
            op.attributes = {}
        else:
            name = op.attributes["op_name__"]
            assert isinstance(name, StringAttr)
            new_name = StringAttr("unknown_" + name.data)
            op.attributes = {"op_name__": new_name}
        op.attributes = {k: v for k, v in op.attributes.items() if k == "op_name__"}
        op.properties = {}
        for result in op.results:
            if result.type != i32:
                Rewriter.replace_value_with_new_type(result, i32)
        for operand in op.operands:
            if operand.type != i32:
                Rewriter.replace_value_with_new_type(operand, i32)
    print("Module parsed")
    with open("sqlite3-stripped.mlir", "w") as f:
        Printer(f, print_generic_format=True).print_op(module)

if __name__ == "__main__":
    __main__()