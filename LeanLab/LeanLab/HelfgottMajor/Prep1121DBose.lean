import LeanLab.HelfgottMajor.Prep1121VIPointwiseA

/-!
PREP 2026-11-21 deepening pass p2, route step `MainLemma41Split123.vertical_integral_bound`.
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 34, display 4.10,
lines two to five. The parent leaves `Prep1121VIPointwiseA.bose_integral` and
`Prep1121VIPointwiseA.binet_remainder_le` are proved here with their exact statements.
The Bose integral ∫_0^∞ t/(e^{2πt} - 1) dt = Γ(2)ζ(2)/(2π)² = 1/24 of the paper is done
by expanding u/(e^u - 1) = Σ_{n ≥ 1} u e^{-nu}, integrating termwise with Mathlib's Gamma
integral, and Mathlib's ζ(2) = π²/6, then the substitution u = 2πt.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121DBose
open Real MeasureTheory Set Filter

/-- P0014 page 34, display 4.10, the Γ(2) step: ∫_0^∞ u e^{-(n+1)u} du = 1/(n+1)². From
`Real.integral_rpow_mul_exp_neg_mul_Ioi` with a = 2 and `Real.Gamma_two`. -/
theorem bose_term (n : ℕ) :
    ∫ u in Ioi (0 : ℝ), u * Real.exp (-(((n : ℝ) + 1) * u)) = 1 / ((n : ℝ) + 1) ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := (n : ℝ) + 1)
    (by norm_num) (by positivity)
  rw [Real.Gamma_two, mul_one, Real.rpow_two, one_div_pow] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]

/-- P0014 page 34, display 4.10, the geometric expansion: for u > 0,
Σ_{n ≥ 0} u e^{-(n+1)u} = u/(e^u - 1). From `tsum_geometric_of_lt_one`. -/
theorem bose_geom (u : ℝ) (hu : 0 < u) :
    ∑' n : ℕ, u * Real.exp (-(((n : ℝ) + 1) * u)) = u / (Real.exp u - 1) := by
  have hq0 : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
  have hq1 : Real.exp (-u) < 1 := by
    have := Real.exp_lt_exp.mpr (show -u < 0 by linarith)
    simpa using this
  have hterm : ∀ n : ℕ, u * Real.exp (-(((n : ℝ) + 1) * u)) =
      u * Real.exp (-u) * Real.exp (-u) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    congr 2; ring
  simp only [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
  have he : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu
  have hne : Real.exp u - 1 ≠ 0 := by linarith
  have hne' : 1 - Real.exp (-u) ≠ 0 := by linarith
  rw [Real.exp_neg] at hne' ⊢
  field_simp

/-- P0014 page 34, display 4.10: ∫_0^∞ u/(e^u - 1) du = Γ(2)ζ(2) = π²/6, by termwise
integration, `integral_tsum_of_summable_integral_norm`, and `hasSum_zeta_two`. -/
theorem bose_unit : ∫ u in Ioi (0 : ℝ), u / (Real.exp u - 1) = π ^ 2 / 6 := by
  set F : ℕ → ℝ → ℝ := fun n u => u * Real.exp (-(((n : ℝ) + 1) * u)) with hF
  have hint : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioi 0)) := by
    intro n
    refine Integrable.of_integral_ne_zero ?_
    rw [hF, bose_term n]; positivity
  have hnorm : ∀ n : ℕ, ∫ u in Ioi (0 : ℝ), ‖F n u‖ = 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    rw [← bose_term n]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    simp only [hF, Real.norm_eq_abs]
    exact abs_of_nonneg (mul_nonneg (le_of_lt hu) (Real.exp_pos _).le)
  have hz := hasSum_zeta_two
  have hz1 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hz
    simpa [Finset.sum_range_one] using this
  have hsum : Summable fun n : ℕ => ∫ u in Ioi (0 : ℝ), ‖F n u‖ := by
    simp only [hnorm]; exact hz1.summable
  have key := integral_tsum_of_summable_integral_norm hint hsum
  rw [show (∫ u in Ioi (0 : ℝ), u / (Real.exp u - 1)) =
      ∫ u in Ioi (0 : ℝ), ∑' n, F n u from
    setIntegral_congr_fun measurableSet_Ioi (fun u hu => (bose_geom u hu).symm)]
  rw [← key]
  simp only [hF, bose_term]
  exact hz1.tsum_eq

/-- P0014 page 34, display 4.10, fourth line: exact statement of the parent leaf
`Prep1121VIPointwiseA.bose_integral`, by the substitution u = 2πt in `bose_unit`. -/
theorem bose_integral :
    ∫ t in Ioi (0 : ℝ), t / (Real.exp (2 * Real.pi * t) - 1) = 1 / 24 := by
  have hb : 0 < 2 * Real.pi := by positivity
  have h := integral_comp_mul_left_Ioi (fun u : ℝ => u / (Real.exp u - 1)) 0 hb
  simp only [mul_zero, smul_eq_mul] at h
  rw [bose_unit] at h
  have he : (fun t : ℝ => t / (Real.exp (2 * Real.pi * t) - 1)) =
      fun t => (2 * Real.pi)⁻¹ * ((2 * Real.pi * t) / (Real.exp (2 * Real.pi * t) - 1)) := by
    funext t
    rw [← mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hb.ne', one_mul]
  rw [he, integral_const_mul, h]
  field_simp
  ring

/-- P0014 page 34, display 4.10, second to fifth lines: exact statement of the parent leaf
`Prep1121VIPointwiseA.binet_remainder_le`. The Bose integral is nonzero, so its integrand is
integrable, and the Binet integrand is dominated by (4/9) t/(e^{2πt} - 1) on t > 0. -/
theorem binet_remainder_le (z : ℂ) (hz : z.re = 3 / 2)
    (hden : ∀ t : ℝ, 9 / 4 ≤ ‖(t : ℂ) ^ 2 + z ^ 2‖)
    (hbose : ∫ t in Ioi (0 : ℝ), t / (Real.exp (2 * Real.pi * t) - 1) = 1 / 24) :
    ‖2 * ∫ t in Ioi (0 : ℝ),
        (t : ℂ) / (((t : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * Real.pi * t) : ℂ) - 1))‖ ≤
      1 / 27 := by
  set g : ℝ → ℝ := fun t => t / (Real.exp (2 * Real.pi * t) - 1) with hg
  have hgi : Integrable g (volume.restrict (Ioi 0)) :=
    Integrable.of_integral_ne_zero (by rw [hg, hbose]; norm_num)
  have hbound : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(t : ℂ) / (((t : ℂ) ^ 2 + z ^ 2) * ((Real.exp (2 * Real.pi * t) : ℂ) - 1))‖ ≤
        (4 / 9) * g t := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht
    have hE : 0 < Real.exp (2 * Real.pi * t) - 1 := by
      have : 1 < Real.exp (2 * Real.pi * t) := Real.one_lt_exp_iff.mpr (by positivity)
      linarith
    have hc : ((Real.exp (2 * Real.pi * t) : ℂ) - 1) =
        ((Real.exp (2 * Real.pi * t) - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hc, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos ht0, abs_of_pos hE, hg]
    have hd := hden t
    have hp : 0 < ‖(t : ℂ) ^ 2 + z ^ 2‖ := by linarith
    rw [div_le_iff₀ (by positivity)]
    have : (4 / 9) * (t / (Real.exp (2 * Real.pi * t) - 1)) *
        (‖(t : ℂ) ^ 2 + z ^ 2‖ * (Real.exp (2 * Real.pi * t) - 1)) =
        t * ((4 / 9) * ‖(t : ℂ) ^ 2 + z ^ 2‖) := by
      have hne : Real.exp (2 * Real.pi * t) - 1 ≠ 0 := hE.ne'
      field_simp
      exact div_self (by rw [show t * 2 * Real.pi = 2 * Real.pi * t by ring]; exact hne)
    rw [this]
    nlinarith
  have hI := norm_integral_le_of_norm_le (hgi.const_mul (4 / 9)) hbound
  rw [integral_const_mul, hg, hbose] at hI
  rw [norm_mul, Complex.norm_two]
  linarith

end LeanLab.HelfgottMajor.Prep1121DBose
