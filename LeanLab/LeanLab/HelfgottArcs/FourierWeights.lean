/-
Elementary Fourier weight bounds from Helfgott, arXiv 1205.5252v4.
Source: page 73, Lemma A.1 and equation A.1.
AI wrote this Lean code for CODEX task62. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.WeightBounds

namespace LeanLab.HelfgottArcs
open MeasureTheory Set Real

/-- A rational polynomial certificate for the unit circle bound in Lemma A.1. -/
theorem unit_jump_polynomial_norm_le (z : ℂ) (hz : ‖z‖ = 1) :
    ‖4 * z - 4 * z ^ 2 + z ^ 4‖ ≤ 7.87052 := by
  have hu : z.re ^ 2 + z.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, pow_two, hz] using (Complex.sq_norm z).symm
  have heq : ‖4 * z - 4 * z ^ 2 + z ^ 4‖ ^ 2 =
      41 - 56 * z.re - 16 * z.re ^ 2 + 32 * z.re ^ 3 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply, pow_succ, Complex.mul_re, Complex.mul_im]
    linear_combination
      (z.re ^ 6 + 3 * z.re ^ 4 * z.im ^ 2 - 7 * z.re ^ 4 + 8 * z.re ^ 3 +
        3 * z.re ^ 2 * z.im ^ 4 + 2 * z.re ^ 2 * z.im ^ 2 + 9 * z.re ^ 2 -
        24 * z.re * z.im ^ 2 - 56 * z.re + z.im ^ 6 + 9 * z.im ^ 4 +
        25 * z.im ^ 2 + 41) * hu
  have ha : -1 ≤ z.re ∧ z.re ≤ 1 := by
    have h := Complex.abs_re_le_norm z
    rw [hz] at h
    exact abs_le.mp h
  have hc : 0 ≤ (z.re + 0.6150693) ^ 2 * (55.3644352 - 32 * z.re) :=
    mul_nonneg (sq_nonneg _) (by linarith [ha.2])
  have hb : 41 - 56 * z.re - 16 * z.re ^ 2 + 32 * z.re ^ 3 ≤ (7.87052 : ℝ) ^ 2 := by
    nlinarith only [hc, ha.1, ha.2]
  nlinarith only [heq, hb, norm_nonneg (4 * z - 4 * z ^ 2 + z ^ 4)]

/-- The normalized exponential phase has norm one. -/
theorem norm_e (t : ℝ) : ‖e t‖ = 1 := by
  unfold e
  rw [Complex.norm_exp]
  simp

/-- Helfgott Lemma A.1, with exactly the exponential phases of equation A.1. -/
theorem norm_fourier_jump_le (t : ℝ) :
    ‖4 * e (-t / 4) - 4 * e (-t / 2) + e (-t)‖ ≤ 7.87052 := by
  have h2 : e (-t / 2) = e (-t / 4) ^ 2 := by
    unfold e
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h4 : e (-t) = e (-t / 4) ^ 4 := by
    unfold e
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h2, h4]
  exact unit_jump_polynomial_norm_le _ (norm_e _)

/-- A strict form of Lemma A.4, from convexity between the two endpoint polynomials. -/
theorem norm_fourier_log_jump_lt {ρ : ℝ} (hρ : 4 ≤ ρ) (t : ℝ) :
    ‖(4 * e (-t / 4) - 4 * e (-t / 2) + e (-t)) * (Real.log ρ : ℂ) -
      (2 * e (-t / 4) - e (-t / 2)) * (4 * Real.log 2 : ℂ)‖ <
        7.87052 * Real.log ρ := by
  let G := 4 * e (-t / 4) - 4 * e (-t / 2) + e (-t)
  let K := 2 * e (-t / 4) - e (-t / 2)
  have hG : ‖G‖ ≤ 7.87052 := norm_fourier_jump_le t
  have hGK : ‖G - 2 * K‖ ≤ 3 := by
    have heq : G - 2 * K = e (-t) - 2 * e (-t / 2) := by dsimp [G, K]; ring
    rw [heq]
    calc ‖e (-t) - 2 * e (-t / 2)‖ ≤ ‖e (-t)‖ + ‖2 * e (-t / 2)‖ := norm_sub_le _ _
      _ = 3 := by rw [norm_mul, norm_e, norm_e]; norm_num
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hL : 2 * Real.log 2 ≤ Real.log ρ := by
    rw [← hl4]
    exact Real.log_le_log (by norm_num) hρ
  let A := Real.log ρ - 2 * Real.log 2
  let B := 2 * Real.log 2
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hB : 0 < B := by dsimp [B]; linarith
  have heq : G * (Real.log ρ : ℂ) - K * (4 * Real.log 2 : ℂ) =
      G * (A : ℂ) + (G - 2 * K) * (B : ℂ) := by
    dsimp [A, B]
    push_cast
    ring
  change ‖G * (Real.log ρ : ℂ) - K * (4 * Real.log 2 : ℂ)‖ < _
  rw [heq]
  calc ‖G * (A : ℂ) + (G - 2 * K) * (B : ℂ)‖
      ≤ ‖G * (A : ℂ)‖ + ‖(G - 2 * K) * (B : ℂ)‖ := norm_add_le _ _
    _ = ‖G‖ * A + ‖G - 2 * K‖ * B := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hA, abs_of_pos hB]
    _ ≤ 7.87052 * A + 3 * B := by
      exact add_le_add (mul_le_mul_of_nonneg_right hG hA)
        (mul_le_mul_of_nonneg_right hGK hB.le)
    _ < 7.87052 * Real.log ρ := by dsimp [A, B]; nlinarith

/-- The Fourier transform norm is bounded by the L1 norm of a real weight. -/
theorem norm_fhat_le_integral_abs (f : ℝ → ℝ) (δ : ℝ) :
    ‖fhat f δ‖ ≤ ∫ t, |f t| := by
  unfold fhat
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    rw [norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- The Fourier transform of eta2 is bounded by one at every real frequency. -/
theorem norm_fhat_eta2_le_one (δ : ℝ) : ‖fhat eta2 δ‖ ≤ 1 := by
  have h := norm_fhat_le_integral_abs eta2 δ
  have heq : (fun t => |eta2 t|) = eta2 := funext fun t => abs_of_nonneg (eta2_nonneg t)
  rw [heq, integral_eta2] at h
  exact h

/-- The eta2 Fourier bound is attained at frequency zero. -/
theorem fhat_eta2_zero : fhat eta2 0 = 1 := by
  unfold fhat
  have he : ∀ y : ℝ, e (-(y * 0)) = 1 := by intro y; simp [e]
  simp only [he, one_mul]
  rw [integral_complex_ofReal, integral_eta2]
  norm_num

/-- The strict L1 estimate also bounds the Fourier transform of eta2rho. -/
theorem norm_fhat_eta2rho_lt {ρ : ℝ} (hρ : 4 ≤ ρ) (δ : ℝ) :
    ‖fhat (eta2rho ρ) δ‖ < Real.log ρ :=
  (norm_fhat_le_integral_abs (eta2rho ρ) δ).trans_lt (integral_abs_eta2rho_lt hρ)

end LeanLab.HelfgottArcs
