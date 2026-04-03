// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({
^bb0(%arg0: i3, %arg1: i3, %arg2: i3):
  %0, %1 = "datapath.compress"(%arg0, %arg1, %arg2) : (i3, i3, i3) -> (i3, i3)
  %2, %3, %4 = "datapath.partial_product"(%arg0, %arg1) : (i3, i3) -> (i3, i3, i3)
  %5, %6, %7 = "datapath.pos_partial_product"(%arg0, %arg1, %arg2) : (i3, i3, i3) -> (i3, i3, i3)
}) : () -> ()

