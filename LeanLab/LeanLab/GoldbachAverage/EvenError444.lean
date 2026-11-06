import LeanLab.GoldbachAverage.NormalizationInstances

/-!
Goldston and Suriajaya, https://arxiv.org/abs/2110.14250v2 page 7 after Theorem 7.
The shift by two N log N forces at least one of the two errors to have that scale.
This does not determine which error has the smaller order.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.EvenError444
open Complex Filter Asymptotics

/-- P0051 page 7 after eq. 37, a displacement of size two x forces one endpoint norm above x. -/
theorem error_shift_max (z : ℂ) (x : ℝ) (hx : 0 ≤ x) :
    x ≤ max ‖z‖ ‖z - (2 * x : ℝ)‖ := by
  have hid : (2 * x : ℂ) = z - (z - (2 * x : ℝ)) := by push_cast; ring
  have hn := norm_sub_le z (z - (2 * x : ℝ))
  rw [← hid] at hn
  have hr : ‖(2 * x : ℂ)‖ = 2 * x := by
    norm_num [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
  rw [hr] at hn
  have h1 := le_max_left ‖z‖ ‖z - (2 * x : ℝ)‖
  have h2 := le_max_right ‖z‖ ‖z - (2 * x : ℝ)‖
  linarith

/-- P0051 page 7 after eq. 37, the maximum of the plain and even error norms is at least N log N. -/
theorem error_max_lower (N : ℕ) (hN : 2 ≤ N) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (N : ℝ) * Real.log N ≤ max ‖EGS N r‖
      ‖EGS N r - (2 * (N : ℝ) * Real.log N : ℝ)‖ := by
  have hh := error_shift_max (EGS N r) ((N : ℝ) * Real.log N)
    (mul_nonneg (Nat.cast_nonneg N) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))))
  simpa only [mul_assoc] using hh

/-- P0051 page 7 after eq. 37, the two displayed errors cannot both be little o of N log N. -/
theorem not_both_errors_small (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ¬ ((fun N : ℕ => EGS N r) =o[atTop] (fun N : ℕ => (N : ℝ) * Real.log N) ∧
      (fun N : ℕ => EGS N r - (2 * (N : ℝ) * Real.log N : ℝ)) =o[atTop]
        (fun N : ℕ => (N : ℝ) * Real.log N)) := by
  rintro ⟨h1, h2⟩
  have hb1 := h1.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hb2 := h2.bound (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨N, hN, hB1, hB2⟩ := ((eventually_ge_atTop (2 : ℕ)).and (hb1.and hb2)).exists
  have hpos : 0 < (N : ℝ) * Real.log N := mul_pos
    (by exact_mod_cast (by omega : 0 < N))
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N)))
  rw [Real.norm_eq_abs, abs_of_pos hpos] at hB1 hB2
  have hmax := max_le hB1 hB2
  have hlo := error_max_lower N hN r hr0 hr1
  linarith

end LeanLab.GoldbachAverage.EvenError444
