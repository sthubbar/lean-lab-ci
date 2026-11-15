/-
Jia 1996 pages 261 and 262, the preliminary bounds in Lemma 20.
Source https://doi.org/10.4064/aa-77-3-207-287.
Apply the existing strip propagation to the constructed Buchstab solution.
The sharper global bounds remain separate analytic inputs.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Buchstab578
import LeanLab.Languasco2004.Buchstab565

namespace LeanLab.Languasco2004.Bounds578
open Real intervalIntegral Buchstab578 BuchstabInitial316
noncomputable section

/-- Page 261 display 41: the actual solution satisfies each anchored integral recurrence. -/
theorem buchstab_anchored_recurrence (K u : ℝ) (hK : 2 ≤ K) (hKu : K ≤ u) :
    u * buchstab u = K * buchstab K + ∫ t in (K - 1)..(u - 1), buchstab t := by
  have h1 := buchstab_recurrence u (hK.trans hKu)
  have h2 := buchstab_recurrence K hK
  have h3 := integral_add_adjacent_intervals
    (buchstab_continuous.intervalIntegrable (μ := MeasureTheory.volume) (1 : ℝ) (K - 1))
    (buchstab_continuous.intervalIntegrable (μ := MeasureTheory.volume) (K - 1) (u - 1))
  linarith

/-- Page 261 initial formulas: the constructed solution equals the existing initial segment. -/
theorem buchstab_initial_segment (u : ℝ) (hu1 : 1 ≤ u) (hu3 : u ≤ 3) :
    buchstab u = buchstabInitial u := by
  by_cases hu2 : u ≤ 2
  · rw [buchstab_initial u hu1 hu2, buchstabInitial_eq_inv hu2]
  · rw [buchstab_two_three u (le_of_not_ge hu2) hu3,
      buchstabInitial_eq_log (le_of_not_ge hu2)]

/-- Page 261 proof of Lemma 20: the actual solution lies between 0.5 and 0.5672 above two.
The proof reuses Buchstab565.buchstab_initial_upper and Buchstab565.global_strip_bounds. -/
theorem buchstab_global_initial_bounds (u : ℝ) (hu : 2 ≤ u) :
    0.5 ≤ buchstab u ∧ buchstab u ≤ 0.5672 := by
  apply Buchstab565.global_strip_bounds buchstab 0.5 0.5672
    buchstab_continuous.continuousOn _ _ u hu
  · intro t ht
    rw [buchstab_initial_segment t (by linarith [ht.1]) ht.2]
    exact ⟨by linarith [(buchstabInitial_bounds (by linarith [ht.1]) ht.2).1],
      Buchstab565.buchstab_initial_upper t ht.1 ht.2⟩
  · intro j t ht
    have h := buchstab_anchored_recurrence (3 + (j : ℝ)) t
      (by have := Nat.cast_nonneg (α := ℝ) j; linarith) ht.1
    simpa only [show (3 + (j : ℝ)) - 1 = 2 + (j : ℝ) by ring] using h

/-- Page 261 proof of Lemma 20: the preliminary bound holds on the whole source domain. -/
theorem buchstab_basic_bounds (u : ℝ) (hu : 1 ≤ u) :
    0.5 ≤ buchstab u ∧ buchstab u ≤ 1 := by
  by_cases hu2 : u ≤ 2
  · rw [buchstab_initial_segment u hu (by linarith)]
    have h := buchstabInitial_bounds hu (by linarith : u ≤ 3)
    constructor <;> linarith [h.1, h.2]
  · have h := buchstab_global_initial_bounds u (le_of_not_ge hu2)
    constructor <;> linarith [h.1, h.2]

/-- Page 261 after display 42: the actual derivative has absolute value at most one quarter. -/
theorem buchstab_derivative_quarter (u : ℝ) (hu : 2 < u) :
    |deriv buchstab u| ≤ 1 / 4 := by
  rw [(buchstab_derivative u hu).deriv, abs_div, abs_of_pos (by linarith : 0 < u)]
  apply (div_le_iff₀ (by linarith : 0 < u)).mpr
  have h1 := buchstab_basic_bounds (u - 1) (by linarith)
  have h2 := buchstab_basic_bounds u (by linarith)
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Page 262 proof of Lemma 20: above three the actual derivative is at most 0.0224 in absolute value. -/
theorem buchstab_derivative_0224 (u : ℝ) (hu : 3 ≤ u) :
    |deriv buchstab u| ≤ 0.0224 := by
  rw [(buchstab_derivative u (by linarith)).deriv, abs_div,
    abs_of_pos (by linarith : 0 < u)]
  apply (div_le_iff₀ (by linarith : 0 < u)).mpr
  have h1 := buchstab_global_initial_bounds (u - 1) (by linarith)
  have h2 := buchstab_global_initial_bounds u (by linarith)
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

#print axioms buchstab_anchored_recurrence
#print axioms buchstab_initial_segment
#print axioms buchstab_global_initial_bounds
#print axioms buchstab_basic_bounds
#print axioms buchstab_derivative_quarter
#print axioms buchstab_derivative_0224
end
end LeanLab.Languasco2004.Bounds578
