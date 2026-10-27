import LeanLab.ChenDoubleSieve.LogIntegralPanels

/-!
# Rational logarithm panels for the J terms in Wu 2004

Source: https://arxiv.org/pdf/0705.1652, pages 22 and 26.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set Finset MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Wu04Panels
open Wu04Integral (logLower logUpper log_bounds)

/-- The lower logarithm approximation is nonnegative on y at least one. -/
theorem logLower_nonneg (n : ℕ) {y : ℝ} (hy : 1 ≤ y) : 0 ≤ logLower n y := by
  apply mul_nonneg (by norm_num)
  apply sum_nonneg
  intro j hj
  have hr : 0 ≤ (y - 1) / (y + 1) := div_nonneg (by linarith) (by linarith)
  exact div_nonneg (pow_nonneg hr _) (by positivity)

/-- The upper logarithm approximation is nonnegative on the same range. -/
theorem logUpper_nonneg (n : ℕ) {y : ℝ} (hy : 1 ≤ y) : 0 ≤ logUpper n y :=
  (log_nonneg hy).trans (log_bounds n hy).2

/-- Entirely rational expression once a and b are rational. -/
def JLower (n : ℕ) (a b : ℝ) : ℝ :=
  logLower n (a - 1) * logLower n (b / a) +
    ((b - a) - a * logUpper n (b / a)) / (b - 1)

/-- The matching rational upper expression. -/
def JUpper (n : ℕ) (a b : ℝ) : ℝ :=
  logUpper n (a - 1) * logUpper n (b / a) +
    ((b - a) - a * logLower n (b / a)) / (a - 1)

/-- Logarithm interval arithmetic rigorously encloses each actual J panel. -/
theorem J_panel_arithmetic (n : ℕ) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    JLower n a b ≤ (∫ t in a..b, log (t - 1) / t) ∧
    (∫ t in a..b, log (t - 1) / t) ≤ JUpper n a b := by
  have ha0 : 0 < a := by linarith
  have hratio : 1 ≤ b / a := (le_div_iff₀ ha0).mpr (by simpa using hab)
  have hA := log_bounds n (y := a - 1) (by linarith)
  have hW := log_bounds n hratio
  have hPlo := mul_le_mul hA.1 hW.1 (logLower_nonneg n hratio) (log_nonneg (by linarith : 1 ≤ a - 1))
  have hPhi := mul_le_mul hA.2 hW.2 (log_nonneg hratio) (logUpper_nonneg n (by linarith : 1 ≤ a - 1))
  have hVlo : (b - a) - a * logUpper n (b / a) ≤ (b - a) - a * log (b / a) := by
    nlinarith [mul_le_mul_of_nonneg_left hW.2 ha0.le]
  have hVhi : (b - a) - a * log (b / a) ≤ (b - a) - a * logLower n (b / a) := by
    nlinarith [mul_le_mul_of_nonneg_left hW.1 ha0.le]
  have hj := J_panel (by linarith : 1 < a) hab
  constructor
  · exact (add_le_add hPlo (div_le_div_of_nonneg_right hVlo (by linarith))).trans hj.1
  · exact hj.2.trans (add_le_add hPhi (div_le_div_of_nonneg_right hVhi (by linarith)))

/-- The J integrand is integrable on every panel above one. -/
theorem J_integrable {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => log (t - 1) / t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.div
  · apply ContinuousOn.log (by fun_prop)
    intro t ht; linarith [ht.1]
  · exact continuousOn_id
  · intro t ht; change t ≠ 0; linarith [ht.1]

/-- Sum rational panels across any finite increasing partition starting at two or above. -/
theorem J_partition_arithmetic (n m : ℕ) (x : ℕ → ℝ)
    (hx : ∀ j < m, 2 ≤ x j ∧ x j ≤ x (j + 1)) :
    (∑ j ∈ range m, JLower n (x j) (x (j + 1))) ≤
      (∫ t in x 0..x m, log (t - 1) / t) ∧
    (∫ t in x 0..x m, log (t - 1) / t) ≤
      ∑ j ∈ range m, JUpper n (x j) (x (j + 1)) := by
  have hint : ∀ j < m, IntervalIntegrable (fun t => log (t - 1) / t) volume (x j) (x (j + 1)) := by
    intro j hj
    exact J_integrable (by linarith [(hx j hj).1]) (hx j hj).2
  have he := sum_integral_adjacent_intervals hint
  rw [← he]
  constructor
  · exact sum_le_sum fun j hj => (J_panel_arithmetic n (hx j (mem_range.mp hj)).1 (hx j (mem_range.mp hj)).2).1
  · exact sum_le_sum fun j hj => (J_panel_arithmetic n (hx j (mem_range.mp hj)).1 (hx j (mem_range.mp hj)).2).2

end LeanLab.ChenDoubleSieve.Wu04Panels

#print axioms LeanLab.ChenDoubleSieve.Wu04Panels.logLower_nonneg
#print axioms LeanLab.ChenDoubleSieve.Wu04Panels.logUpper_nonneg
#print axioms LeanLab.ChenDoubleSieve.Wu04Panels.J_panel_arithmetic
#print axioms LeanLab.ChenDoubleSieve.Wu04Panels.J_integrable
#print axioms LeanLab.ChenDoubleSieve.Wu04Panels.J_partition_arithmetic
