/-
P0027 R. Li 2024, On Chen's theorem, Goldbach's conjecture and almost prime twins II,
arXiv 2405.05727v4, Section 4, read from the arXiv LaTeX source, cloud session
20261019T1116Z-cloud23, unit U-5475.

* `final_combination`: the fifteen printed constants of (9) to (34) give
  `3·12.902021 + 6.533916 + 2.421452 + 1.382532 + 0.960457 - (2·10.436523 + 3.311305 +
  0.272301 + 5.259433 + 2.659313 + 2·1.30656 + 3.912436 + 2.835087 + 0.193502 + 0.183611)
  = 7.891266 ≥ 7.8912`, and `7.8912/4 = 1.9728`: MATCH.
* `s6_integral`, `s6_le`: the S₆ bound `(2/e^γ) 11.49 ∫_{57/224}^{1/3} F(11.49(1/2 - t))/t dt`,
  with `F(s) = 2e^γ/s` on `(0, 3]`, where `11.49(1/2 - t)` lies for these `t`, equals
  `8 log(110/57) = 5.2594328 ≤ 5.259433`: MATCH, the printed value rounded up.
The other fourteen constants are numerical integrals of F, f, ω and Lichtman-type levels,
not checked here.

AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
Chen-type results say N = p + P₂; binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Li2024.Numerics
open Real

/-- Li 2024 v4, the final display of Section 4: `4 D_{1,2}(N) ≥ 7.8912 C(N)N/log² N`
from the printed constants, and `D_{1,2}(N) ≥ 1.9728 C(N)N/log² N`. -/
theorem final_combination :
    (7.8912 : ℝ) ≤ (3 * 12.902021 + 6.533916 + 2.421452 + 1.382532 + 0.960457) -
      (2 * 10.436523 + 3.311305 + 0.272301 + 5.259433 + 2.659313 + 2 * 1.30656 + 3.912436 +
        2.835087 + 0.193502 + 0.183611) ∧ (7.8912 : ℝ) / 4 = 1.9728 := by
  constructor <;> norm_num

/-- The integrand of S₆ after `F(s) = 2e^γ/s`: `(2/e^γ) · 11.49 · F(11.49(1/2 - t))/t`. -/
noncomputable def s6f (t : ℝ) : ℝ :=
  2 / Real.exp Real.eulerMascheroniConstant * 11.49 *
    ((2 * Real.exp Real.eulerMascheroniConstant / (11.49 * (1 / 2 - t))) / t)

theorem s6f_eq {t : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) : s6f t = 8 / t + 8 / (1 / 2 - t) := by
  unfold s6f
  have h1 : (0 : ℝ) < 1 / 2 - t := by linarith
  have he := Real.exp_pos Real.eulerMascheroniConstant
  have h3 : (1 - t * 2) ≠ 0 := by linarith
  rw [div_add_div _ _ ht.ne' h1.ne', eq_div_iff (mul_ne_zero ht.ne' h1.ne')]
  field_simp
  have ha : (1 - t * 2)⁻¹ * (1 - t * 2) = 1 := inv_mul_cancel₀ h3
  linear_combination 8 * ha

/-- `F(11.49(1/2 - t))` is evaluated in `(0, 3]` on the range of S₆, where
`F(s) = 2e^γ/s`. -/
theorem s6_arg_range {t : ℝ} (h1 : 57 / 224 ≤ t) (h2 : t ≤ 1 / 3) :
    0 < 11.49 * (1 / 2 - t) ∧ 11.49 * (1 / 2 - t) ≤ 3 := by
  constructor <;> nlinarith

theorem s6_integral :
    ∫ t in (57 / 224 : ℝ)..(1 / 3), s6f t = 8 * Real.log (110 / 57) := by
  have hcongr : Set.EqOn s6f (fun t => 8 / t + 8 / (1 / 2 - t)) (Set.uIcc (57 / 224) (1 / 3)) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    exact s6f_eq (by linarith [ht.1]) (by linarith [ht.2])
  rw [intervalIntegral.integral_congr hcongr]
  have hderiv : ∀ t ∈ Set.uIcc (57 / 224 : ℝ) (1 / 3),
      HasDerivAt (fun t => 8 * Real.log t - 8 * Real.log (1 / 2 - t))
        (8 / t + 8 / (1 / 2 - t)) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have h0 : t ≠ 0 := by linarith [ht.1]
    have h1 : (1 / 2 - t) ≠ 0 := by linarith [ht.2]
    have a := ((Real.hasDerivAt_log h0).const_mul 8)
    have b := (((hasDerivAt_id t).const_sub (1 / 2)).log h1).const_mul 8
    convert a.sub b using 1
    · funext y; simp
    · simp only [id]; field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · have e1 : Real.log (1 / 3) - Real.log (1 / 2 - 1 / 3) = Real.log 2 := by
      rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
    have e2 : Real.log (57 / 224) - Real.log (1 / 2 - 57 / 224) = Real.log (57 / 55) := by
      rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
    have e3 : Real.log (110 / 57) = Real.log 2 - Real.log (57 / 55) := by
      rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
    rw [e3]; linarith
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.add
    · exact continuousOn_const.div continuousOn_id fun t ht => by linarith [ht.1]
    · exact continuousOn_const.div (continuousOn_const.sub continuousOn_id)
        fun t ht => by linarith [ht.2]

/-- `8 log(110/57) ≤ 5.259433`, from `log(110/57) = log 2 + log(1 - 2/57)` and six terms of
the series for `log(1 - y)`. -/
theorem s6_le : 8 * Real.log (110 / 57) ≤ 5.259433 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 2 / 57) (by norm_num) 6
  have e : Real.log (110 / 57) = Real.log 2 + Real.log (1 - 2 / 57) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  have := Real.log_two_lt_d9
  rw [e]
  norm_num
  linarith [h.2]

/-- **Li's S₆ bound, (24)**: the printed `5.259433` holds. -/
theorem s6_bound :
    ∫ t in (57 / 224 : ℝ)..(1 / 3), s6f t ≤ 5.259433 := by
  rw [s6_integral]; exact s6_le

/-- Li 2024 v4, Section 5, Theorem 1.3: the sixteen terms of Lemma 3.2 with the printed
constants of (35) to (53), `S'₈` and `S'₁₁` being `O(ε)`, give
`27.299195 - 22.195306 = 5.103889 ≥ 5.1036`, and `5.1036/4 = 1.2759`. The printed final display
also subtracts `S'₁₇`, `S'₁₈`, `S'₁₉`, which Lemma 3.2 does not define. -/
theorem final_combination_t13 :
    (5.1036 : ℝ) ≤ (3 * 6.737439 + 4.011646 + 0.875194 + 1.917212 + 0.282826) -
      (2 * 7.410929 + 2 * 0.925271 + 0.111039 + 1.169696 + 1.960955 + 1.699112 +
        2 * 0.152213 + 0.031709 + 0.245969) ∧ (5.1036 : ℝ) / 4 = 1.2759 := by
  constructor <;> norm_num

end LeanLab.Li2024.Numerics
