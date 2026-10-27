/-
Tao 2012, arXiv 1201.6656v4, P0007, page 12, Lemma 3.3.
CODEX task137, track T1. AI wrote this Lean code. Goldbach is open.
The positive phase integral is the Mathlib Fourier transform at negative frequency.
The multiplicative form includes zero frequency without division by zero.
-/
import Mathlib

namespace LeanLab.Tao2012.Decomp137

open Real MeasureTheory
open scoped FourierTransform ContDiff

/-- CITED. Tao 2012, page 12, Lemma 3.3, with the denominator multiplied across.
For a smooth compactly supported function, the positive phase Fourier integral times
`(2π|α|)^k` is bounded in norm by the L1 norm of its kth derivative. -/
def Lemma3_3 : Prop :=
  ∀ (F : ℝ → ℂ), ContDiff ℝ ∞ F → HasCompactSupport F →
    ∀ (k : ℕ) (α : ℝ),
      (2 * π * |α|) ^ k * ‖𝓕 F (-α)‖ ≤ ∫ y, ‖iteratedDeriv k F y‖

/-- LEAF. Tao 2012, page 12, Lemma 3.3. Smooth compact support gives
integrability of every derivative used in integration by parts. -/
theorem derivatives_integrable (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) (k : ℕ) : Integrable (iteratedDeriv k F) := by
  have hc : ∀ j : ℕ, HasCompactSupport (iteratedDeriv j F) := by
    intro j
    induction j with
    | zero => simpa using hFc
    | succ j hj => simpa [iteratedDeriv_succ] using hj.deriv
  exact (hF.continuous_iteratedDeriv k (by simp)).integrable_of_hasCompactSupport (hc k)

/-- LEAF. Tao 2012, page 12, proof of Lemma 3.3. Iterating integration by parts
multiplies the Fourier transform by the kth power of `2πi` times the frequency. -/
theorem iterated_parts (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hFi : ∀ k : ℕ, Integrable (iteratedDeriv k F)) (k : ℕ) (α : ℝ) :
    𝓕 (iteratedDeriv k F) (-α) =
      (2 * π * Complex.I * (-α : ℝ)) ^ k • 𝓕 F (-α) := by
  exact congrFun (Real.fourier_iteratedDeriv (N := ⊤) hF (fun j _ => hFi j) (by simp)) (-α)

/-- LEAF. Tao 2012, page 12, proof of Lemma 3.3. The triangle inequality
bounds a Fourier integral by the integral of the norm. This is the k equals zero step. -/
theorem integral_norm_bound (G : ℝ → ℂ) (α : ℝ) :
    ‖𝓕 G (-α)‖ ≤ ∫ y, ‖G y‖ := by
  exact Real.norm_fourier_le_integral_norm G (-α)

/-- Lemma 3.3 assembled from its leaves. No cited result outside Tao is assumed. -/
theorem lemma3_3 : Lemma3_3 := by
  intro F hF hFc k α
  have hFi := derivatives_integrable F hF hFc
  have hp := iterated_parts F hF hFi k α
  have hb := integral_norm_bound (iteratedDeriv k F) α
  rw [hp, norm_smul, norm_pow] at hb
  simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos pi_pos] using hb

/-- The paper's positive phase integral equals the Mathlib transform at negative frequency.
Tao 2012, page 12, Lemma 3.3. -/
theorem positive_phase_eq (F : ℝ → ℂ) (α : ℝ) :
    𝓕 F (-α) = ∫ y : ℝ, F y * Complex.exp (2 * π * Complex.I * (α * y : ℝ)) := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with y
  simp only [RCLike.inner_apply, conj_trivial, smul_eq_mul]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring

/-- Tao 2012, page 12, Lemma 3.3, the printed quotient at nonzero frequency. -/
theorem lemma3_3_div (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) (k : ℕ) (α : ℝ) (hα : α ≠ 0) :
    ‖∫ y : ℝ, F y * Complex.exp (2 * π * Complex.I * (α * y : ℝ))‖ ≤
      (∫ y, ‖iteratedDeriv k F y‖) / (2 * π * |α|) ^ k := by
  rw [← positive_phase_eq]
  apply (le_div_iff₀ (by positivity : 0 < (2 * π * |α|) ^ k)).mpr
  simpa [mul_comm] using lemma3_3 F hF hFc k α

end LeanLab.Tao2012.Decomp137
