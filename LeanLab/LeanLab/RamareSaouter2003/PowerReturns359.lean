import LeanLab.RamareSaouter2003.Decomp359g

/-!
Rosser 1941 p. 224, the choice of arbitrarily large powers with positive center.
This is the elementary phase recurrence behind that step.
Mathlib supplies Dirichlet approximation and the Lipschitz bound for cosine.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.PowerReturns359

/-- Rosser p. 224, elementary phase step in choosing the powers of zeta.
For every phase, lower bound and positive tolerance there is a larger
natural power whose cosine is within that tolerance of one. -/
theorem phase_return (θ : ℝ) (L : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, L < N ∧ |Real.cos ((N : ℝ) * θ) - 1| < ε := by
  have hpi : 0 < 2 * Real.pi := by positivity
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hε hpi)
  let ξ := ((L + 1 : ℕ) : ℝ) * θ / (2 * Real.pi)
  obtain ⟨k, hk, _, happrox⟩ := Real.exists_nat_abs_mul_sub_round_le ξ
    (by omega : 0 < n + 1)
  let N := k * (L + 1)
  let j : ℤ := round ((k : ℝ) * ξ)
  refine ⟨N, ?_, ?_⟩
  · dsimp [N]
    nlinarith
  · have hsmall : 1 / ((n + 1 : ℕ) + 1 : ℝ) < ε / (2 * Real.pi) := by
      apply lt_of_le_of_lt _ hn
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      linarith
    have hid : (N : ℝ) * θ - (j : ℝ) * (2 * Real.pi) =
        (2 * Real.pi) * ((k : ℝ) * ξ - (j : ℝ)) := by
      dsimp [N, ξ]
      push_cast
      field_simp
    have hdist : |(N : ℝ) * θ - (j : ℝ) * (2 * Real.pi)| < ε := by
      rw [hid, abs_mul, abs_of_pos hpi]
      have hb := mul_lt_mul_of_pos_left (happrox.trans_lt hsmall) hpi
      have hc : (2 * Real.pi) * (ε / (2 * Real.pi)) = ε := by field_simp
      rwa [hc] at hb
    have hcos := Real.abs_cos_sub_cos_le ((N : ℝ) * θ - (j : ℝ) * (2 * Real.pi)) 0
    simp only [Real.cos_sub_int_mul_two_pi, Real.cos_zero, sub_zero] at hcos
    exact hcos.trans_lt hdist

/-- Rosser p. 224, the normalized real part of large powers can approach one.
This is the polar form of phase_return and contains no zero-count estimate. -/
theorem normalized_power_return (z : ℂ) (hz : z ≠ 0) (L : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, L < N ∧ |(z ^ N).re / ‖z‖ ^ N - 1| < ε := by
  obtain ⟨N, hN, hcos⟩ := phase_return z.arg L ε hε
  refine ⟨N, hN, ?_⟩
  have hp : z ^ N = ((‖z‖ ^ N : ℝ) : ℂ) *
      Complex.exp ((((N : ℝ) * z.arg : ℝ) : ℂ) * Complex.I) := by
    calc
      z ^ N = ((‖z‖ : ℂ) * Complex.exp (z.arg * Complex.I)) ^ N := by
        rw [Complex.norm_mul_exp_arg_mul_I]
      _ = _ := by
        rw [mul_pow, ← Complex.exp_nat_mul, Complex.ofReal_pow]
        congr 2
        push_cast
        ring
  have hre : (z ^ N).re = ‖z‖ ^ N * Real.cos ((N : ℝ) * z.arg) := by
    rw [hp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_ofReal_mul_I_re]
  have hn : ‖z‖ ^ N ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hz)
  have hratio : (z ^ N).re / ‖z‖ ^ N = Real.cos ((N : ℝ) * z.arg) := by
    rw [hre]
    field_simp
  rwa [hratio]

/-- Rosser p. 224, G at zero equals the real part of the zeta power.
The conjugation identity is supplied by Mathlib for the actual zeta function. -/
theorem powered_center_eq (T : ℝ) (N : ℕ) :
    Decomp359g.poweredZeta T N 0 =
      (((riemannZeta (5 / 4 + T * Complex.I) ^ N).re : ℝ) : ℂ) := by
  have hc : (5 / 4 - T * Complex.I : ℂ) =
      starRingEnd ℂ (5 / 4 + T * Complex.I) := by
    have hq : (5 / 4 : ℂ) = ((5 / 4 : ℝ) : ℂ) := by norm_num
    simp only [hq, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, sub_eq_add_neg]
  unfold Decomp359g.poweredZeta
  simp only [zero_add, hc, riemannZeta_conj]
  rw [← map_pow, Complex.add_conj]
  push_cast
  ring

/-- Rosser p. 224, a concrete version of the succession of powers.
There are arbitrarily large powers with nonzero center and normalized
real center arbitrarily close to one. No contour bound is included. -/
theorem powered_center_return (T : ℝ) (L : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, L < N ∧ Decomp359g.poweredZeta T N 0 ≠ 0 ∧
      |(Decomp359g.poweredZeta T N 0).re /
        ‖riemannZeta (5 / 4 + T * Complex.I)‖ ^ N - 1| < ε := by
  let z := riemannZeta (5 / 4 + T * Complex.I)
  have hz : z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  obtain ⟨N, hN, hret⟩ := normalized_power_return z hz L (min ε (1 / 2)) (by positivity)
  have hden : 0 < ‖z‖ ^ N := pow_pos (norm_pos_iff.mpr hz) _
  have hlo := (abs_lt.mp hret).1
  have hmin : min ε (1 / 2) ≤ (1 / 2 : ℝ) := min_le_right _ _
  have hratio : 0 < (z ^ N).re / ‖z‖ ^ N := by linarith
  have hpos : 0 < (z ^ N).re := by
    have h := mul_pos hratio hden
    rwa [div_mul_cancel₀ _ hden.ne'] at h
  refine ⟨N, hN, ?_, ?_⟩
  · rw [powered_center_eq]
    exact Complex.ofReal_ne_zero.mpr hpos.ne'
  · rw [powered_center_eq, Complex.ofReal_re]
    exact hret.trans_le (min_le_left _ _)

end LeanLab.RamareSaouter2003.PowerReturns359

#print axioms LeanLab.RamareSaouter2003.PowerReturns359.phase_return

#print axioms LeanLab.RamareSaouter2003.PowerReturns359.normalized_power_return
#print axioms LeanLab.RamareSaouter2003.PowerReturns359.powered_center_eq
#print axioms LeanLab.RamareSaouter2003.PowerReturns359.powered_center_return
