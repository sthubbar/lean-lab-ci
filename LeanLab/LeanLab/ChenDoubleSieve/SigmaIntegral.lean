import Mathlib

/-!
# Certified interval bounds for Wu's sigma integral

Source: https://arxiv.org/pdf/0705.1652, page 14, before Proposition 3.
The integrand is log c/(t-1) divided by t.
Logarithms are bounded by finite rational series with an explicit remainder.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Finset Set MeasureTheory intervalIntegral
namespace LeanLab.ChenDoubleSieve.Wu04Integral

/-- Wu's sigma integral. -/
def sigma (a b c : ℝ) : ℝ := ∫ t in a..b, log (c / (t - 1)) / t

/-- The normalized kernel in Propositions 3 and 4. -/
def sigma0 (t : ℝ) : ℝ := sigma 3 (t + 2) (t + 1) / (1 - sigma 3 5 4)

/-- Finite lower approximation to log y. -/
def logLower (n : ℕ) (y : ℝ) : ℝ :=
  2 * ∑ j ∈ range n, ((y - 1) / (y + 1)) ^ (2 * j + 1) / (2 * j + 1)

/-- Finite upper approximation to log y. -/
def logUpper (n : ℕ) (y : ℝ) : ℝ :=
  logLower n y + 2 * ((y - 1) / (y + 1)) ^ (2 * n + 1) /
    (1 - ((y - 1) / (y + 1)) ^ 2)

/-- Rigorous logarithm enclosure for every real y at least 1. -/
theorem log_bounds (n : ℕ) {y : ℝ} (hy : 1 ≤ y) :
    logLower n y ≤ log y ∧ log y ≤ logUpper n y := by
  let x := (y - 1) / (y + 1)
  have hden : 0 < y + 1 := by linarith
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hden.le
  have hx1 : x < 1 := by dsimp [x]; rw [div_lt_one hden]; linarith
  have hid : (1 + x) / (1 - x) = y := by
    dsimp [x]
    field_simp
    <;> ring
  have hlo := Real.sum_range_le_log_div hx0 hx1 n
  have hhi := Real.log_div_le_sum_range_add hx0 hx1 n
  rw [hid] at hlo hhi
  constructor
  · dsimp [logLower]; linarith
  · dsimp [logUpper, logLower]; dsimp [x] at hhi
    have hh : log y ≤ 2 * ((∑ j ∈ range n, ((y - 1) / (y + 1)) ^ (2 * j + 1) / (2 * j + 1)) + ((y - 1) / (y + 1)) ^ (2 * n + 1) / (1 - ((y - 1) / (y + 1)) ^ 2)) := by linarith
    convert hh using 1 <;> ring

/-- The integrand is continuous on a positive compact interval away from 1. -/
theorem sigma_integrable {a b c : ℝ} (ha : 1 < a) (hab : a ≤ b) (hc : 0 < c) :
    IntervalIntegrable (fun t => log (c / (t - 1)) / t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.div
  · apply ContinuousOn.log
    · apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro t ht; linarith [ht.1]
    · intro t ht
      exact ne_of_gt (div_pos hc (by linarith [ht.1]))
  · exact continuousOn_id
  · intro t ht; linarith [ht.1]

/-- On the nonnegative range, the integrand decreases with t. -/
theorem integrand_antitone {a b c : ℝ} (ha : 1 < a) (hab : a ≤ b) (hc : b - 1 ≤ c) :
    AntitoneOn (fun t => log (c / (t - 1)) / t) (Icc a b) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith [hy.1]
  have hc0 : 0 < c := by linarith
  have hrat : c / (y - 1) ≤ c / (x - 1) :=
    div_le_div_of_nonneg_left hc0.le (by linarith [hx.1]) (by linarith)
  have hlog : log (c / (y - 1)) ≤ log (c / (x - 1)) :=
    log_le_log (div_pos hc0 (by linarith [hy.1])) hrat
  have hnonneg : 0 ≤ log (c / (x - 1)) := by
    apply log_nonneg
    rw [le_div_iff₀ (by linarith [hx.1])]
    linarith [hx.2]
  exact (div_le_div_of_nonneg_right hlog hy0.le).trans
    (div_le_div_of_nonneg_left hnonneg hx0 hxy)

/-- One panel of rigorous interval quadrature. -/
theorem sigma_panel {a b c : ℝ} (ha : 1 < a) (hab : a ≤ b) (hc : b - 1 ≤ c) (n : ℕ) :
    (b - a) * (logLower n (c / (b - 1)) / b) ≤ sigma a b c ∧
      sigma a b c ≤ (b - a) * (logUpper n (c / (a - 1)) / a) := by
  have hc0 : 0 < c := by linarith
  have hi := sigma_integrable ha hab hc0
  have hm := integrand_antitone ha hab hc
  have hb0 : 0 < b := by linarith
  have ha0 : 0 < a := by linarith
  have hlo := (log_bounds n (y := c / (b - 1)) (by
    rw [le_div_iff₀ (by linarith)]; linarith)).1
  have hhi := (log_bounds n (y := c / (a - 1)) (by
    rw [le_div_iff₀ (by linarith)]; linarith)).2
  have hl := integral_mono_on hab intervalIntegrable_const hi
    (fun t ht => (div_le_div_of_nonneg_right hlo hb0.le).trans
      (hm ht ⟨hab, le_rfl⟩ ht.2))
  have hu := integral_mono_on hab hi intervalIntegrable_const
    (fun t ht => (hm ⟨le_rfl, hab⟩ ht ht.1).trans
      (div_le_div_of_nonneg_right hhi ha0.le))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hl hu
  exact ⟨hl, hu⟩

/-- Any finite increasing partition gives a rigorous sigma enclosure. -/
theorem sigma_partition (x : ℕ → ℝ) (m n : ℕ)
    (hx : ∀ j < m, 1 < x j ∧ x j ≤ x (j + 1))
    {c : ℝ} (hc : ∀ j < m, x (j + 1) - 1 ≤ c) :
    (∑ j ∈ range m, (x (j + 1) - x j) * (logLower n (c / (x (j + 1) - 1)) / x (j + 1)))
      ≤ sigma (x 0) (x m) c ∧
    sigma (x 0) (x m) c ≤
      ∑ j ∈ range m, (x (j + 1) - x j) * (logUpper n (c / (x j - 1)) / x j) := by
  have hint : ∀ j < m, IntervalIntegrable (fun t => log (c / (t - 1)) / t) volume (x j) (x (j + 1)) := by
    intro j hj
    exact sigma_integrable (hx j hj).1 (hx j hj).2 (by linarith [(hx j hj).1, (hx j hj).2, hc j hj])
  have heq := sum_integral_adjacent_intervals hint
  change ∑ j ∈ range m, sigma (x j) (x (j + 1)) c = sigma (x 0) (x m) c at heq
  constructor
  · rw [← heq]
    exact sum_le_sum fun j hj => (sigma_panel (hx j (mem_range.mp hj)).1
      (hx j (mem_range.mp hj)).2 (hc j (mem_range.mp hj)) n).1
  · rw [← heq]
    exact sum_le_sum fun j hj => (sigma_panel (hx j (mem_range.mp hj)).1
      (hx j (mem_range.mp hj)).2 (hc j (mem_range.mp hj)) n).2

end LeanLab.ChenDoubleSieve.Wu04Integral

#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.log_bounds
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.sigma_integrable
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.integrand_antitone
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.sigma_panel
#print axioms LeanLab.ChenDoubleSieve.Wu04Integral.sigma_partition
