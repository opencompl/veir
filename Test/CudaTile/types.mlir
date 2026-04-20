// RUN: veir-opt %s | filecheck %s
"builtin.module"() ({
^bb0(%arg0: !cuda_tile.ptr<i1>):
}) : () -> ()
