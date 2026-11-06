import LeanLab.ChirreHagen2025.Decomp377d

/-!
Audit of the inherited DecompJ966.leaf_eq_2_4 statement against P0075
page 3 equation 2.4. The inherited domain includes the pole s = 1.
This is a QUESTION about the Lean transcription, not the paper.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.FractionalAudit429
open Filter Topology

/-- P0075 page 3 pole exclusion, tested with Mathlib's total derivative. -/
theorem zeta_deriv_one : deriv riemannZeta 1 = 0 := by
  apply deriv_zero_of_not_differentiableAt
  intro hd
  have hc : ContinuousAt (fun s : ℂ => (s - 1) * riemannZeta s) 1 :=
    (continuousAt_id.sub continuousAt_const).mul hd.continuousAt
  have hzero : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s)
      (𝓝[≠] 1) (𝓝 0) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  exact one_ne_zero (tendsto_nhds_unique riemannZeta_residue_one hzero)

/-- P0075 page 4 argument at s = 1, with the composed derivative factor. -/
theorem gamma_composed_one :
    (deriv (fun z => Complex.Gamma (z / 2 + 1)) 1 / Complex.Gamma ((1 : ℂ) / 2 + 1)).re =
      1 - Real.log 2 - Real.eulerMascheroniConstant / 2 := by
  have hp : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have hh := congrArg Complex.re h
    norm_num at hh
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hd : (deriv Complex.Gamma ((1 : ℂ) / 2 + 1) /
      Complex.Gamma ((1 : ℂ) / 2 + 1)).re =
      2 - 2 * Real.log 2 - Real.eulerMascheroniConstant := by
    change (Complex.digamma ((1 : ℂ) / 2 + 1)).re = _
    rw [Complex.digamma_apply_add_one _ hp, Complex.digamma_one_half]
    norm_num [Complex.log_re]
    ring
  rw [Decomp377d.gamma_chain 1 (by norm_num), hd]
  ring

/-- P0075 page 3 equation 2.4 transcription audit at the excluded pole.
The critical-zero sum is nonnegative even without a summability assumption. -/
theorem fractional_identity_fails_at_one :
    (deriv riemannZeta (1 : ℂ) / riemannZeta (1 : ℂ)).re ≠
      (∑' ρ : {z : ℂ // riemannZeta z = 0 ∧ z.re = 1 / 2},
        (analyticOrderNatAt riemannZeta ρ : ℝ) * ((1 : ℂ).re - 1 / 2) /
        (((1 : ℂ).re - 1 / 2) ^ 2 + ((1 : ℂ).im - (ρ : ℂ).im) ^ 2)) -
      (1 / 2 * (deriv (fun z => Complex.Gamma (z / 2 + 1)) 1 /
        Complex.Gamma ((1 : ℂ) / 2 + 1)).re) +
      1 - Real.log Real.pi / 2 +
        ((1 : ℂ).re - 1) / (((1 : ℂ).re - 1) ^ 2 + (1 : ℂ).im ^ 2) := by
  have hsum : 0 ≤ ∑' ρ : {z : ℂ // riemannZeta z = 0 ∧ z.re = 1 / 2},
        (analyticOrderNatAt riemannZeta ρ : ℝ) * ((1 : ℂ).re - 1 / 2) /
        (((1 : ℂ).re - 1 / 2) ^ 2 + ((1 : ℂ).im - (ρ : ℂ).im) ^ 2) := by
    apply tsum_nonneg
    intro ρ
    simp only [Complex.one_re, Complex.one_im]
    positivity
  have hlog : Real.log (2 : ℝ) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hpi : Real.log Real.pi ≤ 2 * Real.log 2 := by
    have hh := Real.log_le_log Real.pi_pos Real.pi_lt_four.le
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  rw [zeta_deriv_one, zero_div, Complex.zero_re, gamma_composed_one]
  simp only [Complex.one_re, Complex.one_im, sub_self, zero_pow (by decide : 2 ≠ 0),
    add_zero, div_zero, sub_zero]
  intro h
  simp only [Complex.one_re, Complex.one_im] at hsum
  nlinarith [Real.one_half_lt_eulerMascheroniConstant]

/-- Exact negation of the inherited universal DecompJ966.leaf_eq_2_4 statement.
Its witness is s = 1, which belongs to the inherited stated domain. -/
theorem not_inherited_leaf_eq_2_4 : ¬ (∀ (s : ℂ) (hs : s.re > 1 / 2),
    (deriv riemannZeta s / riemannZeta s).re =
    (∑' ρ : {z : ℂ // riemannZeta z = 0 ∧ z.re = 1 / 2},
      (analyticOrderNatAt riemannZeta ρ : ℝ) * (s.re - 1 / 2) /
      ((s.re - 1 / 2) ^ 2 + (s.im - (ρ : ℂ).im) ^ 2)) -
    (1 / 2 * (deriv (fun z => Complex.Gamma (z / 2 + 1)) s / Complex.Gamma (s / 2 + 1)).re) +
    1 - Real.log Real.pi / 2 + (s.re - 1) / ((s.re - 1) ^ 2 + s.im ^ 2)) := by
  intro h
  exact fractional_identity_fails_at_one (h 1 (by norm_num))

end LeanLab.ChirreHagen2025.FractionalAudit429
