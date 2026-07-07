module

public import Lean

public import ExArray.CompilerExtras

public section


public section

register_grind_attr layout_grind
register_simp_attr layout_simp

register_grind_attr unfold_pointers

instance : HAdd UInt64 Int64 UInt64 where
  hAdd x y := x.toInt64 + y |>.toUInt64

instance : HAdd Int64 UInt64 Int64 where
  hAdd x y := x + y.toInt64

-- @[grind =]
theorem UInt64.add_int64_l_def (x : Int64) (y : UInt64) : x + y = x + y.toInt64 := rfl
-- @[grind =]
theorem UInt64.add_int64_r_def (x : UInt64) (y : Int64) : x + y = (x.toInt64 + y).toUInt64 := rfl
