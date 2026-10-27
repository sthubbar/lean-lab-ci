import LeanLab.ChenDoubleSieve.KPanels
import LeanLab.ChenDoubleSieve.JPanelArithmetic

/-!
# Directed rational arithmetic for Wu's K panels

Source: https://arxiv.org/pdf/0705.1652, pages 22 and 26.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Set Finset MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Wu04Panels
open Wu04Integral (logLower logUpper log_bounds)

/-- Directed bounds for the zeroth K weight moment. -/
def KWLower (n : ℕ) (a b : ℝ) : ℝ := logLower n (b / a) + logLower n ((1 - a) / (1 - b))
def KWUpper (n : ℕ) (a b : ℝ) : ℝ := logUpper n (b / a) + logUpper n ((1 - a) / (1 - b))

/-- Directed lower and upper K panel evaluations. -/
def KLower (n : ℕ) (a b r : ℝ) : ℝ :=
  logLower n (r * a - 1) * KWLower n a b + r / (r * b - 1) *
    (logLower n ((1 - a) / (1 - b)) - a * KWUpper n a b)
def KUpper (n : ℕ) (a b r : ℝ) : ℝ :=
  logUpper n (r * a - 1) * KWUpper n a b + r / (r * a - 1) *
    (logUpper n ((1 - a) / (1 - b)) - a * KWLower n a b)

/-- Every directed K panel encloses its actual integral. -/
theorem K_panel_arithmetic (n : ℕ) {a b r : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hr : 0 < r) (hra : 1 ≤ r * a - 1) :
    KLower n a b r ≤ (∫ t in a..b, log (r * t - 1) / (t * (1 - t))) ∧
    (∫ t in a..b, log (r * t - 1) / (t * (1 - t))) ≤ KUpper n a b r := by
  have hba : 0 < r * b - 1 := by nlinarith
  have hra0 : 0 < r * a - 1 := by linarith
  have hratio1 : 1 ≤ b / a := (le_div_iff₀ ha).mpr (by simpa using hab)
  have hratio2 : 1 ≤ (1 - a) / (1 - b) := (le_div_iff₀ (by linarith)).mpr (by linarith)
  have hA := log_bounds n hra
  have hW1 := log_bounds n hratio1
  have hW2 := log_bounds n hratio2
  let W := log (b / a) + log ((1 - a) / (1 - b))
  have hWL : KWLower n a b ≤ W := add_le_add hW1.1 hW2.1
  have hWU : W ≤ KWUpper n a b := add_le_add hW1.2 hW2.2
  have hWL0 : 0 ≤ KWLower n a b := add_nonneg (logLower_nonneg n hratio1) (logLower_nonneg n hratio2)
  have hW0 : 0 ≤ W := add_nonneg (log_nonneg hratio1) (log_nonneg hratio2)
  have hPlo := mul_le_mul hA.1 hWL hWL0 (log_nonneg hra)
  have hPhi := mul_le_mul hA.2 hWU hW0 (logUpper_nonneg n hra)
  have hVlo : logLower n ((1 - a) / (1 - b)) - a * KWUpper n a b ≤
      log ((1 - a) / (1 - b)) - a * W := by
    nlinarith [mul_le_mul_of_nonneg_left hWU ha.le]
  have hVhi : log ((1 - a) / (1 - b)) - a * W ≤
      logUpper n ((1 - a) / (1 - b)) - a * KWLower n a b := by
    nlinarith [mul_le_mul_of_nonneg_left hWL ha.le]
  have hp := K_panel ha hab hb hr hra0
  constructor
  · exact (add_le_add hPlo (mul_le_mul_of_nonneg_left hVlo (div_nonneg hr.le hba.le))).trans hp.1
  · exact hp.2.trans (add_le_add hPhi (mul_le_mul_of_nonneg_left hVhi (div_nonneg hr.le hra0.le)))

/-- Sum the directed panels over a finite admissible K partition. -/
theorem K_partition_arithmetic (n m : ℕ) (x : ℕ → ℝ) {r : ℝ} (hr : 0 < r)
    (hx : ∀ j < m, 0 < x j ∧ x j ≤ x (j + 1) ∧ x (j + 1) < 1 ∧ 1 ≤ r * x j - 1) :
    (∑ j ∈ range m, KLower n (x j) (x (j + 1)) r) ≤
      (∫ t in x 0..x m, log (r * t - 1) / (t * (1 - t))) ∧
    (∫ t in x 0..x m, log (r * t - 1) / (t * (1 - t))) ≤
      ∑ j ∈ range m, KUpper n (x j) (x (j + 1)) r := by
  have hint : ∀ j < m, IntervalIntegrable (fun t => log (r * t - 1) / (t * (1 - t))) volume (x j) (x (j + 1)) := by
    intro j hj
    obtain ⟨ha, hab, hb, hra⟩ := hx j hj
    exact K_integrable ha hab hb hr (by linarith)
  have he := sum_integral_adjacent_intervals hint
  rw [← he]
  constructor
  · apply sum_le_sum
    intro j hj
    obtain ⟨ha, hab, hb, hra⟩ := hx j (mem_range.mp hj)
    exact (K_panel_arithmetic n ha hab hb hr hra).1
  · apply sum_le_sum
    intro j hj
    obtain ⟨ha, hab, hb, hra⟩ := hx j (mem_range.mp hj)
    exact (K_panel_arithmetic n ha hab hb hr hra).2

end LeanLab.ChenDoubleSieve.Wu04Panels

#print axioms LeanLab.ChenDoubleSieve.Wu04Panels.K_panel_arithmetic
#print axioms LeanLab.ChenDoubleSieve.Wu04Panels.K_partition_arithmetic
