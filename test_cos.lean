import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

namespace ConnectionLaplacian.Cycle
open Real Matrix BigOperators

example (c x y : ℝ) (h : c * x = c * y) (hc : c ≠ 0) : x = y :=
  mul_left_cancel₀ hc h

end ConnectionLaplacian.Cycle
