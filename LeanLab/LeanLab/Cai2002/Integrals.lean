/-
P0044, Cai 2002: the constant of (4.15), `8/(2θ-1) ∫₂^{2.29} log(t-1)/t dt ≤ 0.1564` at θ = 0.95,
proved from Mathlib's Taylor remainder bound for `log` and an exact polynomial integral.
AI-written Lean code, Claude, run 20261018T2303Z-8776. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Cai2002.Statements

open Finset Real intervalIntegral

namespace LeanLab.Cai2002

/-- Upper polynomial for `log(1+u)` on `[0, 0.29]`: Taylor to degree 6 plus `u⁷/0.71`. -/
noncomputable def Lp (u : ℝ) : ℝ :=
  u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4 + u ^ 5 / 5 - u ^ 6 / 6 + u ^ 7 / (71 / 100)

/-- Upper polynomial for `1/(2+u)`, `u ≥ 0`: `(1 - x + x² - x³ + x⁴)/2` with `x = u/2`. -/
noncomputable def Qp (u : ℝ) : ℝ := (1 - u / 2 + (u / 2) ^ 2 - (u / 2) ^ 3 + (u / 2) ^ 4) / 2

/-- Coefficients of `Lp · Qp`. -/
noncomputable def cP (k : ℕ) : ℝ :=
  [0, 1/2, -1/2, 5/12, -1/3, 4/15, -193/960, 54319/68160, -53609/136320, 821/4260,
    -1271/13632, 25/568].getD k 0

lemma LpQp_eq (u : ℝ) : Lp u * Qp u = ∑ k ∈ range 12, cP k * u ^ k := by
  simp [Lp, Qp, cP, Finset.sum_range_succ]
  ring

lemma log_le_Lp {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 0.29) : Real.log (1 + u) ≤ Lp u := by
  have hx : |(-u)| < 1 := by rw [abs_neg, abs_of_nonneg h0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 6
  rw [abs_neg, abs_of_nonneg h0, sub_neg_eq_add, add_comm 1 u] at h
  have h2 := (abs_le.mp h).2
  have h7 : u ^ 7 / (1 - u) ≤ u ^ 7 / (71 / 100) :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h2
  rw [add_comm 1 u]
  unfold Lp
  norm_num at h2
  nlinarith [h2, h7]

lemma inv_le_Qp {u : ℝ} (h0 : 0 ≤ u) : 1 / (2 + u) ≤ Qp u := by
  have hpos : 0 < 2 + u := by linarith
  rw [div_le_iff₀ hpos]
  have : Qp u * (2 + u) = 1 + (u / 2) ^ 5 := by unfold Qp; ring
  rw [this]
  have : 0 ≤ (u / 2) ^ 5 := by positivity
  linarith

lemma integrand_le {t : ℝ} (ht : t ∈ Set.Icc (2 : ℝ) 2.29) :
    Real.log (t - 1) / t ≤ Lp (t - 2) * Qp (t - 2) := by
  obtain ⟨h2, h229⟩ := ht
  have hu0 : 0 ≤ t - 2 := by linarith
  have hlog : Real.log (t - 1) ≤ Lp (t - 2) := by
    have := log_le_Lp hu0 (by linarith)
    rwa [show 1 + (t - 2) = t - 1 by ring] at this
  have hlog0 : 0 ≤ Real.log (t - 1) := Real.log_nonneg (by linarith)
  have hinv : 1 / t ≤ Qp (t - 2) := by
    have := inv_le_Qp hu0
    rwa [show 2 + (t - 2) = t by ring] at this
  rw [div_eq_mul_one_div]
  exact mul_le_mul hlog hinv (by positivity) (hlog0.trans hlog)

lemma integral_LpQp : ∫ u in (0 : ℝ)..0.29, Lp u * Qp u =
    ∑ k ∈ range 12, cP k * ((0.29 : ℝ) ^ (k + 1) / (k + 1)) := by
  simp_rw [LpQp_eq]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  · intro k _
    exact (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _

/-- (4.15) at θ = 0.95: `8/(2θ-1) ∫₂^{2.29} log(t-1)/t dt ≤ 0.1564`. The bound proved here is
`0.15633`; the true value is `0.156286`. -/
theorem eq415 : Eq415Const := by
  unfold Eq415Const
  simp only
  have hcont : ContinuousOn (fun t : ℝ => Real.log (t - 1) / t) (Set.uIcc 2 2.29) := by
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.div
    · apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro t ht; show t - 1 ≠ 0; have := ht.1; intro h'; linarith
    · exact continuousOn_id
    · intro t ht; have := ht.1; intro h'; linarith
  have hI : ∫ t in (2 : ℝ)..2.29, Real.log (t - 1) / t ≤
      ∫ t in (2 : ℝ)..2.29, Lp (t - 2) * Qp (t - 2) := by
    apply intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable)
    · apply Continuous.intervalIntegrable
      unfold Lp Qp; fun_prop
    · intro t ht; exact integrand_le ht
  have hJ : ∫ t in (2 : ℝ)..2.29, Lp (t - 2) * Qp (t - 2) =
      ∫ u in (0 : ℝ)..0.29, Lp u * Qp u := by
    rw [intervalIntegral.integral_comp_sub_right (fun u => Lp u * Qp u)]
    norm_num
  rw [hJ, integral_LpQp] at hI
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cP] at hI
  norm_num at hI
  have h8 : (0 : ℝ) < 8 / (2 * 0.95 - 1) := by norm_num
  calc 8 / (2 * (0.95 : ℝ) - 1) * ∫ t in (2 : ℝ)..2.29, Real.log (t - 1) / t
      ≤ 8 / (2 * 0.95 - 1) * (∫ t in (2 : ℝ)..2.29, Real.log (t - 1) / t) := le_refl _
    _ ≤ 0.1564 := by
      have := mul_le_mul_of_nonneg_left hI h8.le
      norm_num at this ⊢
      linarith

end LeanLab.Cai2002
