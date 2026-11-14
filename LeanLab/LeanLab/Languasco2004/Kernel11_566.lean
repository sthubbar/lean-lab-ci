/-
Jia 1996 page 270, the two integrals for Omega11 in Lemma 24.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
These are numerical kernel estimates with no prime distribution premise.
-/
import LeanLab.Languasco2004.Midpoint566
import LeanLab.Languasco2004.Numeric548
import LeanLab.Languasco2004.Numeric30_548

namespace LeanLab.Languasco2004.Kernel11_566
open Real Set intervalIntegral Kernel548 Numeric548 Numeric30_548 MovingIntegral548
noncomputable section
set_option maxHeartbeats 0

/-- Page 270: the complete Omega11 domain has positive denominators. -/
theorem domain_bounds (t u : ℝ) (htl : 17 / 63 ≤ t) (htu : t ≤ 17 / 57)
    (hul : 17 / 30 - 6 / 5 * t ≤ u) (huu : u ≤ 7 / 24 - t / 8) :
    0 < t ∧ 0 < u ∧ 0 < 1 - t - u ∧
      u ≤ 65 / 252 ∧ 1 - t - u ≤ 281 / 570 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Page 270: below the internal split the initial Buchstab formula is logarithmic. -/
theorem logarithmic_kernel (t u : ℝ) (htl : 17 / 63 ≤ t) (htu : t ≤ 17 / 57)
    (hul : 17 / 30 - 6 / 5 * t ≤ u) (huu : u ≤ (1 - t) / 3) :
    BuchstabInitial316.buchstabInitial ((1 - t - u) / u) / (t * u ^ 2) =
      (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)) := by
  have huU : u ≤ 7 / 24 - t / 8 := by linarith
  obtain ⟨ht, hu, hv, _, _⟩ := domain_bounds t u htl htu hul huU
  apply initial_kernel_high t u ht hu hv
  apply (le_div_iff₀ hu).mpr
  linarith

/-- Page 270: above the internal split the initial Buchstab formula is rational. -/
theorem rational_kernel (t u : ℝ) (htl : 17 / 63 ≤ t) (htu : t ≤ 17 / 57)
    (hul : (1 - t) / 3 ≤ u) (huu : u ≤ 7 / 24 - t / 8) :
    BuchstabInitial316.buchstabInitial ((1 - t - u) / u) / (t * u ^ 2) =
      1 / (t * u * (1 - t - u)) := by
  have huL : 17 / 30 - 6 / 5 * t ≤ u := by linarith
  obtain ⟨ht, hu, hv, _, _⟩ := domain_bounds t u htl htu huL huu
  apply initial_kernel_low t u ht hu hv
  apply (div_le_iff₀ hu).mpr
  linarith

/-- Page 270 numerical support: two odd terms from Mathlib minorize log y for y at least one. -/
theorem log_odd_lower (y : ℝ) (hy : 1 ≤ y) :
    2 * ((y - 1) / (y + 1)) + 2 / 3 * ((y - 1) / (y + 1)) ^ 3 ≤ Real.log y := by
  have hden : 0 < y + 1 := by linarith
  have hz : 0 ≤ (y - 1) / (y + 1) := div_nonneg (by linarith) hden.le
  have hz1 : (y - 1) / (y + 1) < 1 := (div_lt_one hden).mpr (by linarith)
  have h := Real.sum_range_le_log_div hz hz1 2
  have he : (1 + (y - 1) / (y + 1)) / (1 - (y - 1) / (y + 1)) = y := by
    field_simp
    <;> ring
  rw [he] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- Page 270 numerical support: the rational polynomial for the logarithmic piece. -/
def logPolynomial (t u : ℝ) : ℝ :=
  invPoly3 t (17 / 57) * invPoly5 u (46 / 189) * invPoly3 (1 - t - u) (281 / 570) *
    (1 + 2 * (1 - t - 3 * u) * invPoly3 (1 - t - u) (281 / 570) +
      2 / 3 * ((1 - t - 3 * u) * Midpoint566.invPoly1 (1 - t - u) (281 / 570)) ^ 3)

/-- Page 270 numerical support: the rational polynomial for the upper piece. -/
def ratPolynomial (t u : ℝ) : ℝ :=
  invPoly5 t (17 / 57) * invPoly5 u (65 / 252) * invPoly5 (1 - t - u) (92 / 189)

/-- LEAF. Page 270: the logarithmic polynomial minorizes the exact integrand. -/
theorem logPolynomial_le (t u : ℝ) (htl : 17 / 63 ≤ t) (htu : t ≤ 17 / 57)
    (hul : 17 / 30 - 6 / 5 * t ≤ u) (huu : u ≤ (1 - t) / 3) :
    logPolynomial t u ≤
      (1 + Real.log ((1 - t) / u - 2)) / (t * u * (1 - t - u)) := by
  obtain ⟨ht, hu, hv, _, hvU⟩ := domain_bounds t u htl htu hul (by linarith)
  have huU : u ≤ 46 / 189 := by linarith
  have hw : 0 ≤ 1 - t - 3 * u := by linarith
  obtain ⟨pt0, pt⟩ := invPoly3_bounds t (17 / 57) ht (by norm_num) htu
  obtain ⟨pu0, pu⟩ := invPoly5_bounds u (46 / 189) hu (by norm_num) huU
  obtain ⟨pv0, pv⟩ := invPoly3_bounds (1 - t - u) (281 / 570) hv (by norm_num) hvU
  have hp := mul_le_mul (mul_le_mul pt pu pu0 (by positivity : (0 : ℝ) ≤ 1 / t))
    pv pv0 (by positivity : (0 : ℝ) ≤ 1 / t * (1 / u))
  have hz := mul_le_mul_of_nonneg_left pv hw
  have hz0 : 0 ≤ (1 - t - 3 * u) * invPoly3 (1 - t - u) (281 / 570) := mul_nonneg hw pv0
  obtain ⟨pl0, pl⟩ := Midpoint566.invPoly1_midpoint (1 - t - u) (281 / 570) hv (by norm_num) (by linarith)
  have hzh := mul_le_mul_of_nonneg_left pl hw
  have hzh0 : 0 ≤ (1 - t - 3 * u) * Midpoint566.invPoly1 (1 - t - u) (281 / 570) := mul_nonneg hw pl0
  have hz3 := pow_le_pow_left₀ hzh0 hzh 3
  have hy : 1 ≤ (1 - t) / u - 2 := by
    apply (le_sub_iff_add_le).mpr
    apply (le_div_iff₀ hu).mpr
    linarith
  have he : (((1 - t) / u - 2) - 1) / (((1 - t) / u - 2) + 1) =
      (1 - t - 3 * u) * (1 / (1 - t - u)) := by
    have hd : (1 - t) / u - 2 + 1 ≠ 0 := by linarith
    apply (div_eq_iff hd).mpr
    field_simp [hu.ne', hv.ne']
    <;> ring
  have hl := log_odd_lower ((1 - t) / u - 2) hy
  rw [he] at hl
  have hn : 1 + 2 * ((1 - t - 3 * u) * invPoly3 (1 - t - u) (281 / 570)) +
      2 / 3 * ((1 - t - 3 * u) * Midpoint566.invPoly1 (1 - t - u) (281 / 570)) ^ 3 ≤
      1 + Real.log ((1 - t) / u - 2) := by linarith
  have hn0 : 0 ≤ 1 + 2 * ((1 - t - 3 * u) * invPoly3 (1 - t - u) (281 / 570)) +
      2 / 3 * ((1 - t - 3 * u) * Midpoint566.invPoly1 (1 - t - u) (281 / 570)) ^ 3 := by positivity
  have hm := mul_le_mul hp hn hn0
    (by positivity : (0 : ℝ) ≤ 1 / t * (1 / u) * (1 / (1 - t - u)))
  calc logPolynomial t u ≤
      (1 / t * (1 / u) * (1 / (1 - t - u))) * (1 + Real.log ((1 - t) / u - 2)) := by
        simpa only [logPolynomial, mul_assoc, mul_left_comm, mul_comm] using hm
       _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- Page 270: the rational polynomial minorizes the exact integrand. -/
theorem ratPolynomial_le (t u : ℝ) (htl : 17 / 63 ≤ t) (htu : t ≤ 17 / 57)
    (hul : (1 - t) / 3 ≤ u) (huu : u ≤ 7 / 24 - t / 8) :
    ratPolynomial t u ≤ 1 / (t * u * (1 - t - u)) := by
  obtain ⟨ht, hu, hv, huU, _⟩ := domain_bounds t u htl htu (by linarith) huu
  have hvU : 1 - t - u ≤ 92 / 189 := by linarith
  obtain ⟨pt0, pt⟩ := invPoly5_bounds t (17 / 57) ht (by norm_num) htu
  obtain ⟨pu0, pu⟩ := invPoly5_bounds u (65 / 252) hu (by norm_num) huU
  obtain ⟨pv0, pv⟩ := invPoly5_bounds (1 - t - u) (92 / 189) hv (by norm_num) hvU
  have hm := mul_le_mul (mul_le_mul pt pu pu0 (by positivity : (0 : ℝ) ≤ 1 / t))
    pv pv0 (by positivity : (0 : ℝ) ≤ 1 / t * (1 / u))
  calc ratPolynomial t u ≤ 1 / t * (1 / u) * (1 / (1 - t - u)) := hm
       _ = _ := by simp only [one_div, mul_inv_rev]; ring

#print axioms domain_bounds
#print axioms logarithmic_kernel
#print axioms rational_kernel
#print axioms log_odd_lower
#print axioms logPolynomial_le
#print axioms ratPolynomial_le
end
end LeanLab.Languasco2004.Kernel11_566
