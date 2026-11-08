/-
Split unit of Linnik1951/SPLIT-logConv_recip_log_le_sqrt1622.

The parent leaf compares the two relative weights of the convolution estimate: for
n at least 10^3 the reciprocal 1 / log n is dominated by 1 / sqrt (log n). The
route is the elementary one. The logarithm is increasing, so n at least 10^3 gives
log n at least log 10^3, and log 10^3 is at least one; the logarithm is therefore
at least one, hence positive. For a real x at least one the square root is at most
x, because squaring both sides reduces it to x at most x^2, and the reciprocal
reverses that order on positive arguments. No statement of the parent file is
changed and no definition is added.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_log_convolution_estimate1622

namespace LeanLab.Linnik1951

/-- LEAF. The constant step: the logarithm of 10^3 is at least one. This is the
numeric base point of the lower bound for the logarithm; it is a single explicit
constant inequality and carries no variable. -/
theorem logConv_recip_leaf_log_1000_ge_one1622 :
    (1 : ℝ) ≤ Real.log (1000 : ℝ) := by
  sorry

/-- LEAF. The monotonicity step: for n at least 10^3 the logarithm of n is at
least the logarithm of 10^3. The logarithm is increasing on the positive reals and
both arguments are positive. -/
theorem logConv_recip_leaf_log_mono1622 (n : ℕ) (hn : 1000 ≤ n) :
    Real.log (1000 : ℝ) ≤ Real.log (n : ℝ) := by
  sorry

/-- LEAF. The square root step: for a real x at least one, the square root of x is
at most x. Squaring both sides over the nonnegative reals turns this into x at most
x^2, which holds from x at least one. -/
theorem logConv_recip_leaf_sqrt_le_self1622 (x : ℝ) (hx : 1 ≤ x) :
    Real.sqrt x ≤ x := by
  sorry

/-- LEAF. The reciprocal step: on positive reals the map y ↦ 1 / y reverses order,
so a at most b gives 1 / b at most 1 / a. This is the step that turns the square
root comparison into the comparison of the two relative weights. -/
theorem logConv_recip_leaf_one_div_le_one_div1622 (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    1 / b ≤ 1 / a := by
  sorry

/-- The parent statement, assembled from the leaves above with no remaining gap:
the logarithm of n is at least one, its square root lies between one and the
logarithm itself, and the reciprocal reverses that order. -/
theorem logConv_recip_log_le_sqrt1622_split (n : ℕ) (hn : 1000 ≤ n) :
    1 / Real.log n ≤ 1 / Real.sqrt (Real.log n) := by
  have hbase : (1 : ℝ) ≤ Real.log (1000 : ℝ) := logConv_recip_leaf_log_1000_ge_one1622
  have hmono : Real.log (1000 : ℝ) ≤ Real.log (n : ℝ) :=
    logConv_recip_leaf_log_mono1622 n hn
  have hlog : (1 : ℝ) ≤ Real.log (n : ℝ) := le_trans hbase hmono
  have hlogpos : (0 : ℝ) < Real.log (n : ℝ) := lt_of_lt_of_le zero_lt_one hlog
  have hsqrtpos : (0 : ℝ) < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hlogpos
  have hsqrtle : Real.sqrt (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) :=
    logConv_recip_leaf_sqrt_le_self1622 (Real.log (n : ℝ)) hlog
  exact logConv_recip_leaf_one_div_le_one_div1622 _ _ hsqrtpos hsqrtle

end LeanLab.Linnik1951

#print axioms LeanLab.Linnik1951.logConv_recip_log_le_sqrt1622_split
