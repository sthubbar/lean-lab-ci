import LeanLab.PNTPort.LargeSieve.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# P0058 Languasco-Zaccagnini 2016, Lemma 4, explicit

Lab proof, unit U-5858, CLOUD 20261020T0014Z-cloud30. AI wrote this file. No cited input.
Binary Goldbach is OPEN.

Paper, arXiv 1606.00869 v2 p. 3, (6) and Lemma 4, quoting Lemma 2.4 of their 2012 paper:
`V(α) = ∑_{m ≥ 1} e^{−m/N} e(mα) = ∑_{m ≥ 1} e^{−mz} = 1/(e^z − 1)` and `V(α) = z⁻¹ + O(1)`,
`z = 1/N − 2πiα`, `α ∈ [−1/2, 1/2]`.

* `norm_exp_sub_one_ge`: `‖e^w − 1‖ ≥ (2/π)‖w‖` when `Re w ≥ 0` and `|Im w| ≤ π`;
* `V_eq`: `∑_{m ≥ 1} e^{−mz} = 1/(e^z − 1)` for `Re z > 0`;
* `lemma4`: `‖V(α) − 1/z‖ ≤ π/2 + 1` for every real `N > 0` and `|α| ≤ 1/2`.
-/

namespace LeanLab.LZCesaroShort

open Complex Real

/-- `|e^w − 1| ≥ (2/π)|w|` on the half strip `Re w ≥ 0`, `|Im w| ≤ π`. -/
theorem norm_exp_sub_one_ge {w : ℂ} (h0 : 0 ≤ w.re) (ht : |w.im| ≤ π) :
    2 / π * ‖w‖ ≤ ‖Complex.exp w - 1‖ := by
  have hπ := Real.pi_pos
  -- `‖e^w − 1‖² = (e^w.re − 1)² + 4 e^w.re sin²(w.im/2)`
  have hsq : ‖Complex.exp w - 1‖ ^ 2
      = (Real.exp w.re - 1) ^ 2 + 4 * Real.exp w.re * Real.sin (w.im / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.exp_re,
      Complex.exp_im, sub_zero]
    have hc : Real.cos w.im = 1 - 2 * Real.sin (w.im / 2) ^ 2 := by
      have := Real.cos_sq_add_sin_sq (w.im / 2)
      rw [show w.im = 2 * (w.im / 2) by ring, Real.cos_two_mul]
      rw [show 2 * (w.im / 2) / 2 = w.im / 2 by ring]
      linarith
    have hp := Real.sin_sq_add_cos_sq w.im
    calc (Real.exp w.re * Real.cos w.im - 1) * (Real.exp w.re * Real.cos w.im - 1)
          + Real.exp w.re * Real.sin w.im * (Real.exp w.re * Real.sin w.im)
        = Real.exp w.re ^ 2 * (Real.sin w.im ^ 2 + Real.cos w.im ^ 2)
          - 2 * Real.exp w.re * Real.cos w.im + 1 := by ring
      _ = _ := by rw [hp, hc]; ring
  -- `|sin(w.im/2)| ≥ |w.im|/π`
  have hs : |w.im| / π ≤ |Real.sin (w.im / 2)| := by
    have hb : |w.im / (2 * π)| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), div_le_iff₀ (by positivity)]
      linarith
    have := LeanLab.PNTPort.LargeSieve.two_abs_le_abs_sin hb
    rw [show π * (w.im / (2 * π)) = w.im / 2 by field_simp, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at this
    rw [div_le_iff₀ hπ]
    calc |w.im| = 2 * (|w.im| / (2 * π)) * π := by field_simp
      _ ≤ |Real.sin (w.im / 2)| * π := by nlinarith
  have hs2 : w.im ^ 2 / π ^ 2 ≤ Real.sin (w.im / 2) ^ 2 := by
    have h1 : 0 ≤ |w.im| / π := by positivity
    have := pow_le_pow_left₀ h1 hs 2
    rwa [div_pow, sq_abs, sq_abs] at this
  have he1 : w.re ≤ Real.exp w.re - 1 := by linarith [Real.add_one_le_exp w.re]
  have he0 : 1 ≤ Real.exp w.re := Real.one_le_exp h0
  have hw2 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hπ4 : 4 / π ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.two_le_pi]
  have key : (2 / π * ‖w‖) ^ 2 ≤ ‖Complex.exp w - 1‖ ^ 2 := by
    rw [hsq, mul_pow, hw2, div_pow]
    have h4 : (2 : ℝ) ^ 2 / π ^ 2 * (w.re ^ 2 + w.im ^ 2)
        = 4 / π ^ 2 * w.re ^ 2 + 4 * (w.im ^ 2 / π ^ 2) := by ring
    rw [h4]
    have hw.re2 : w.re ^ 2 ≤ (Real.exp w.re - 1) ^ 2 := pow_le_pow_left₀ h0 he1 2
    have hw.re : 4 / π ^ 2 * w.re ^ 2 ≤ w.re ^ 2 := by nlinarith [sq_nonneg w.re]
    nlinarith [sq_nonneg (Real.sin (w.im / 2))]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp key

/-- `∑_{m ≥ 1} e^{−mz} = 1/(e^z − 1)` for `Re z > 0`. -/
theorem V_eq {z : ℂ} (hz : 0 < z.re) :
    ∑' m : ℕ, Complex.exp (-((m + 1 : ℕ) * z)) = 1 / (Complex.exp z - 1) := by
  have hlt : ‖Complex.exp (-z)‖ < 1 := by
    rw [Complex.norm_exp, Complex.neg_re]
    calc Real.exp (-z.re) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hne : Complex.exp z - 1 ≠ 0 := by
    intro h
    have : ‖Complex.exp z‖ = 1 := by rw [sub_eq_zero.mp h, norm_one]
    rw [Complex.norm_exp, Real.exp_eq_one_iff] at this; linarith
  have hterm : ∀ m : ℕ, Complex.exp (-((m + 1 : ℕ) * z))
      = Complex.exp (-z) * Complex.exp (-z) ^ m := by
    intro m
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hlt]
  have h1 : Complex.exp (-z) * Complex.exp z = 1 := by rw [← Complex.exp_add]; simp
  field_simp
  have h2 : 1 - Complex.exp (-z) ≠ 0 := by
    intro h; apply hne
    have : Complex.exp (-z) = 1 := (sub_eq_zero.mp h).symm
    rw [this, one_mul] at h1; rw [h1, sub_self]
  rw [div_eq_one_iff_eq h2]
  linear_combination h1

/-- **Lemma 4, explicit.** With `z = 1/N − 2πiα`, `N > 0` and `|α| ≤ 1/2`,
`‖∑_{m ≥ 1} e^{−mz} − 1/z‖ ≤ π/2 + 1`. -/
theorem lemma4 {N α : ℝ} (hN : 0 < N) (hα : |α| ≤ 1 / 2) :
    ‖(∑' m : ℕ, Complex.exp (-((m + 1 : ℕ) * (((1 / N : ℝ) : ℂ) - 2 * π * α * I))))
      - 1 / (((1 / N : ℝ) : ℂ) - 2 * π * α * I)‖ ≤ π / 2 + 1 := by
  set z : ℂ := ((1 / N : ℝ) : ℂ) - 2 * π * α * I with hzdef
  have hzre : z.re = 1 / N := by simp [hzdef]
  have hzim : z.im = -(2 * π * α) := by simp [hzdef]
  have hre : 0 < z.re := by rw [hzre]; positivity
  have him : |z.im| ≤ π := by
    rw [hzim, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    nlinarith [Real.pi_pos]
  have hz0 : z ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [V_eq hre]
  have hlow := norm_exp_sub_one_ge hre.le him
  have hπ := Real.pi_pos
  have hden : 0 < ‖Complex.exp z - 1‖ := lt_of_lt_of_le (by positivity) hlow
  have hne : Complex.exp z - 1 ≠ 0 := norm_pos_iff.mp hden
  rcases le_or_gt ‖z‖ 1 with h1 | h1
  · -- `‖e^z − 1 − z‖ ≤ ‖z‖²`
    have hnum := Complex.norm_exp_sub_one_sub_id_le h1
    have heq : 1 / (Complex.exp z - 1) - 1 / z
        = -(Complex.exp z - 1 - z) / (z * (Complex.exp z - 1)) := by
      field_simp; ring
    rw [heq, norm_div, norm_neg, norm_mul, div_le_iff₀ (by positivity)]
    calc ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 2 := hnum
      _ = π / 2 * (‖z‖ * (2 / π * ‖z‖)) := by field_simp
      _ ≤ π / 2 * (‖z‖ * ‖Complex.exp z - 1‖) := by gcongr
      _ ≤ (π / 2 + 1) * (‖z‖ * ‖Complex.exp z - 1‖) := by
          gcongr; linarith
  · calc ‖1 / (Complex.exp z - 1) - 1 / z‖
        ≤ ‖1 / (Complex.exp z - 1)‖ + ‖1 / z‖ := norm_sub_le _ _
      _ = 1 / ‖Complex.exp z - 1‖ + 1 / ‖z‖ := by rw [norm_div, norm_div, norm_one]
      _ ≤ 1 / (2 / π * ‖z‖) + 1 := by
          have ha : 1 / ‖Complex.exp z - 1‖ ≤ 1 / (2 / π * ‖z‖) :=
            one_div_le_one_div_of_le (by positivity) hlow
          have hb : 1 / ‖z‖ ≤ 1 := by rw [div_le_one hzn]; exact h1.le
          linarith
      _ ≤ π / 2 + 1 := by
          have : 1 / (2 / π * ‖z‖) ≤ π / 2 := by
            rw [div_le_iff₀ (by positivity)]
            have : 2 / π * ‖z‖ * (π / 2) = ‖z‖ := by field_simp
            nlinarith
          linarith
end LeanLab.LZCesaroShort
