/-
Split unit of U-1622. This file adds leaves for the elementary identity
logConv_log_cube_split1622 of Linnik1951/SPLIT_log_convolution_estimate1622.lean,
plus the assembly theorem logConv_log_cube_split1622_split. No statement of the
parent file is changed; no definition is added.

Route. The target rewrites n / (log n)^3 as n / (log n)^2 times 1 / log n, for
every n at least 2. It has no analytic content: one algebraic step replaces the
cube by a square times the base, one splits a reciprocal product, and the only
input from the arithmetic side is that the logarithm of n is positive, hence does
not vanish, above n equal to 1. The three leaves below are exactly those steps,
in the order the assembly uses them.
-/
import LeanLab.Linnik1951.SPLIT_log_convolution_estimate1622

namespace LeanLab.Linnik1951

/-- LEAF. Positivity step: for n at least 2 the argument of the logarithm is
greater than 1, so log n is positive and in particular nonzero. This is the only
arithmetic input of the target; without it both denominators could vanish. -/
theorem logConv_log_cube_pos1622 (n : ℕ) (hn : 2 ≤ n) :
    0 < Real.log (n : ℝ) := by
  apply Real.log_pos
  exact_mod_cast (show (1 : ℕ) < n by omega)

/-- LEAF. Pure algebra, exponent step: a cube is a square times the base, for
every real number and with no hypothesis at all. This is the step that opens the
denominator of the target. -/
theorem logConv_log_cube_pow1622 (x : ℝ) :
    x ^ 3 = x ^ 2 * x := by
  ring

/-- LEAF. Pure algebra, division step: dividing by a square times the base is
the same as dividing by the square and then by the base, for every numerator and
every nonzero denominator. This is the step that produces the factor
1 / log n of the target. -/
theorem logConv_log_cube_div1622 (a x : ℝ) (hx : x ≠ 0) :
    a / (x ^ 2 * x) = (a / x ^ 2) * (1 / x) := by
  field_simp [hx]

/-- The target statement of the parent file, assembled from the leaves above
with no remaining gap: rewrite the cube as a square times the base, then split
the division using nonvanishing of the logarithm. -/
theorem logConv_log_cube_split1622_split (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) / Real.log n ^ 3 = ((n : ℝ) / Real.log n ^ 2) * (1 / Real.log n) := by
  have hpos : 0 < Real.log (n : ℝ) := logConv_log_cube_pos1622 n hn
  have hcube : Real.log (n : ℝ) ^ 3 = Real.log (n : ℝ) ^ 2 * Real.log (n : ℝ) :=
    logConv_log_cube_pow1622 (Real.log (n : ℝ))
  rw [hcube]
  exact logConv_log_cube_div1622 (n : ℝ) (Real.log (n : ℝ)) hpos.ne'

end LeanLab.Linnik1951
