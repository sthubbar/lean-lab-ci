import LeanLab.OeSHP2014.Task74LogBounds
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-! Table 12, pages 2056 and 2057. Checks use natural logarithms.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
namespace LeanLab.OeSHP2014.Task74

/-- The normalized second order fit at the cutoff ten to the power k. -/
noncomputable def momentFit (a b c : ℝ) (k : ℕ) : ℝ :=
  a + b * (1 / (k * Real.log 10)) + c * (1 / (k * Real.log 10)) ^ 2

/-- A rational interval certificate for evaluating the printed quadratic fits. -/
theorem quadratic_enclosure {a b c y l u : ℝ} (hb : b ≤ 0) (hc : 0 ≤ c)
    (hl : 0 ≤ l) (hy : l ≤ y) (hu : y ≤ u) :
    a + b * u + c * l ^ 2 ≤ a + b * y + c * y ^ 2 ∧
      a + b * y + c * y ^ 2 ≤ a + b * l + c * u ^ 2 := by
  have hyl : l ^ 2 ≤ y ^ 2 := by nlinarith
  have hyu : y ^ 2 ≤ u ^ 2 := by nlinarith
  constructor
  · nlinarith [mul_le_mul_of_nonpos_left hu hb, mul_le_mul_of_nonneg_left hyl hc]
  · nlinarith [mul_le_mul_of_nonpos_left hy hb, mul_le_mul_of_nonneg_left hyu hc]

/-- Rational certificates imply an error bound for the actual natural logarithm. -/
theorem momentFit_error_of_cert (k : ℕ) (hk : 0 < k)
    (a b c v e l u : ℝ) (hb : b ≤ 0) (hc : 0 ≤ c) (hl0 : 0 ≤ l)
    (hl : l ≤ 1 / (k * (2302585092995 / 10^12)))
    (hu : 1 / (k * (2302585092994 / 10^12)) ≤ u)
    (hlo : v - e ≤ a + b * u + c * l ^ 2)
    (hhi : a + b * l + c * u ^ 2 ≤ v + e) :
    |momentFit a b c k - v| ≤ e := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have ht := log10_bounds
  have ht0 : 0 < Real.log 10 := by linarith [ht.1]
  have hylo : 1 / (k * (2302585092995 / 10^12) : ℝ) ≤
      1 / (k * Real.log 10) :=
    one_div_le_one_div_of_le (mul_pos hk0 ht0)
      (mul_le_mul_of_nonneg_left ht.2 hk0.le)
  have hyhi : 1 / (k * Real.log 10) ≤
      1 / (k * (2302585092994 / 10^12) : ℝ) :=
    one_div_le_one_div_of_le (mul_pos hk0 (by norm_num))
      (mul_le_mul_of_nonneg_left ht.1 hk0.le)
  have hq := quadratic_enclosure (a := a) hb hc hl0 (hl.trans hylo) (hyhi.trans hu)
  rw [abs_le]
  dsimp [momentFit]
  constructor <;> linarith [hq.1, hq.2]

end LeanLab.OeSHP2014.Task74
#print axioms LeanLab.OeSHP2014.Task74.quadratic_enclosure

#print axioms LeanLab.OeSHP2014.Task74.momentFit_error_of_cert
