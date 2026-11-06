import LeanLab.RamareSaouter2003.PowerReturns359

/-!
Rosser 1941 p. 224, the circle bound and the center bound in Theorem 19.
The center recurrence is already proved in PowerReturns359.
The circle estimate remains a cited OPEN leaf.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp378c
open Real Decomp359g

/-- LEAF. Rosser 1941 p. 224, the circle upper bounds from Backlund
pp. 361 to 369, followed by the remaining steps of his proof.
This is the circle and gamma contribution alone, before the center is subtracted.
The ideal center cost uses the actual zeta modulus before taking powers.
No actual zero count, recurrence or free epsilon occurs in this leaf. -/
theorem circle_gamma_bound (A T : ℝ) (hA : 1400 ≤ A)
    (hFA : (A / (2 * π) * Real.log (A / (2 * π)) - A / (2 * π) + 7 / 8) = 1041)
    (hT : A ≤ T) (N : ℕ) (hN : 0 < N) :
    (∫ φ in (0 : ℝ)..π,
      Real.log ‖poweredZeta T N ((1.32 : ℂ) * Complex.exp (φ * Complex.I))‖) /
        (2 * π * Real.log (4 * 1.32 / 3) * N) +
      1 / 2 + 4 / (π * T) + |gammaRemainder T| / π ≤
        0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 + Real.log ‖riemannZeta (5 / 4 + T * Complex.I)‖ /
            (2 * Real.log (4 * 1.32 / 3)) := by
  sorry

/-- Rosser 1941 p. 224, passing from a normalized returning center to its logarithm.
The logarithmic loss is log two. No numerical modulus bound is used. -/
theorem center_log_lower (T : ℝ) (N : ℕ)
    (hret : |(poweredZeta T N 0).re /
      ‖riemannZeta (5 / 4 + T * Complex.I)‖ ^ N - 1| < (1 / 2 : ℝ)) :
    (N : ℝ) * Real.log ‖riemannZeta (5 / 4 + T * Complex.I)‖ - Real.log 2 ≤
      Real.log ‖poweredZeta T N 0‖ := by
  let z := riemannZeta (5 / 4 + T * Complex.I)
  have hzp : 0 < ‖z‖ := norm_pos_iff.mpr
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hden : 0 < ‖z‖ ^ N := pow_pos hzp _
  have hhalf : (1 / 2 : ℝ) < (poweredZeta T N 0).re / ‖z‖ ^ N := by
    have hh := (abs_lt.mp hret).1
    dsimp only [z] at hden ⊢
    linarith
  have hnorm : ‖z‖ ^ N / 2 ≤ ‖poweredZeta T N 0‖ := by
    have hh := (lt_div_iff₀ hden).mp hhalf
    have hr := Complex.re_le_norm (poweredZeta T N 0)
    linarith
  have hlog := Real.log_le_log (by positivity : 0 < ‖z‖ ^ N / 2) hnorm
  rw [Real.log_div (by positivity : ‖z‖ ^ N ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_pow] at hlog
  exact hlog

/-- Rosser 1941 p. 224, exactly the existing powered_jensen_estimate target.
CONDITIONAL ON the OPEN circle_gamma_bound leaf in this file.
The large returning power and both small remainder estimates are proved. -/
theorem powered_jensen_estimate (A T : ℝ) (hA : 1400 ≤ A)
    (hFA : (A / (2 * π) * Real.log (A / (2 * π)) - A / (2 * π) + 7 / 8) = 1041)
    (hT : A ≤ T) (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ K ≤ (N : ℝ) * ε ∧ poweredZeta T N 0 ≠ 0 ∧
      jensenFunctional T N ≤
        0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 + ε := by
  let q := Real.log (4 * 1.32 / 3)
  have hq : 0 < q := Real.log_pos (by norm_num)
  obtain ⟨L, hL⟩ := exists_nat_gt (max (K / ε) (Real.log 2 / (2 * q * ε)))
  obtain ⟨N, hN, hG, hret⟩ := PowerReturns359.powered_center_return T L (1 / 2) (by norm_num)
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hLN : (L : ℝ) < N := by exact_mod_cast hN
  have hKN : K ≤ (N : ℝ) * ε := by
    have hk := (le_max_left (K / ε) (Real.log 2 / (2 * q * ε))).trans hL.le
    have hh := (div_le_iff₀ hε).mp hk
    nlinarith
  have hsmall : Real.log 2 / (2 * q * N) ≤ ε := by
    have hk := (le_max_right (K / ε) (Real.log 2 / (2 * q * ε))).trans hL.le
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * q * ε)).mp hk
    apply (div_le_iff₀ (by positivity : 0 < 2 * q * N)).mpr
    have hm := mul_le_mul_of_nonneg_right hLN.le (by positivity : 0 ≤ 2 * q * ε)
    calc _ ≤ (L : ℝ) * (2 * q * ε) := hh
         _ ≤ (N : ℝ) * (2 * q * ε) := hm
         _ = _ := by ring
  have hcenter := center_log_lower T N hret
  have hcircle := circle_gamma_bound A T hA hFA hT N hN0
  have hdiv := div_le_div_of_nonneg_right (neg_le_neg hcenter)
    (by positivity : 0 ≤ 2 * q * N)
  have hcancel : (-(N : ℝ) * Real.log ‖riemannZeta (5 / 4 + T * Complex.I)‖ + Real.log 2) /
        (2 * q * N) =
      -Real.log ‖riemannZeta (5 / 4 + T * Complex.I)‖ / (2 * q) +
        Real.log 2 / (2 * q * N) := by
    field_simp [hq.ne', hNR.ne']
  refine ⟨N, hN0, hKN, hG, ?_⟩
  unfold jensenFunctional
  dsimp only [q] at hq hsmall hdiv hcancel
  rw [show -((N : ℝ) * Real.log ‖riemannZeta (5 / 4 + T * Complex.I)‖ - Real.log 2) =
    -(N : ℝ) * Real.log ‖riemannZeta (5 / 4 + T * Complex.I)‖ + Real.log 2 by ring,
    hcancel] at hdiv
  simp only [neg_div] at hdiv
  linarith

end LeanLab.RamareSaouter2003.Decomp378c
#print axioms LeanLab.RamareSaouter2003.Decomp378c.circle_gamma_bound
#print axioms LeanLab.RamareSaouter2003.Decomp378c.center_log_lower
#print axioms LeanLab.RamareSaouter2003.Decomp378c.powered_jensen_estimate
