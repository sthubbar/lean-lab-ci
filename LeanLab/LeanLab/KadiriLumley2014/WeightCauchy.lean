/-
P0059 arXiv 1407.7902v1 page 10, Cauchy Schwarz step in Lemma 3.1.
Journal INTEGERS 14 A61 page 13.
AI wrote this Lean code, CODEX task64, 2026-10-25.
-/
import Mathlib

namespace LeanLab.KadiriLumley2014.Task64
open Real Set MeasureTheory intervalIntegral

/-- Cauchy Schwarz on the unit interval for continuous real functions. -/
theorem integral_mul_sq_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    (∫ t in (0 : ℝ)..1, f t * g t) ^ 2 ≤
      (∫ t in (0 : ℝ)..1, f t ^ 2) * (∫ t in (0 : ℝ)..1, g t ^ 2) := by
  have hi : IntervalIntegrable (fun t => f t ^ 2) volume 0 1 := (hf.pow 2).intervalIntegrable _ _
  have hj : IntervalIntegrable (fun t => g t ^ 2) volume 0 1 := (hg.pow 2).intervalIntegrable _ _
  have hk : IntervalIntegrable (fun t => f t * g t) volume 0 1 := (hf.mul hg).intervalIntegrable _ _
  have hquad : ∀ c : ℝ, 0 ≤
      (∫ t in (0 : ℝ)..1, f t ^ 2) * (c * c) +
      (-2 * (∫ t in (0 : ℝ)..1, f t * g t)) * c +
      (∫ t in (0 : ℝ)..1, g t ^ 2) := by
    intro c
    have hn : 0 ≤ ∫ t in (0 : ℝ)..1, (c * f t - g t) ^ 2 :=
      intervalIntegral.integral_nonneg (by norm_num) (fun t _ => sq_nonneg _)
    have heq : (fun t : ℝ => (c * f t - g t) ^ 2) =
        (fun t => c ^ 2 * f t ^ 2 - (2 * c) * (f t * g t) + g t ^ 2) := by ext t; ring
    rw [heq, intervalIntegral.integral_add ((hi.const_mul _).sub (hk.const_mul _)) hj,
      intervalIntegral.integral_sub (hi.const_mul _) (hk.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hn
    nlinarith
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith

/-- The square root form used for the higher derivative bound. -/
theorem integral_mul_le_sqrt {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    (∫ t in (0 : ℝ)..1, f t * g t) ≤
      Real.sqrt (∫ t in (0 : ℝ)..1, f t ^ 2) *
      Real.sqrt (∫ t in (0 : ℝ)..1, g t ^ 2) := by
  have hi : 0 ≤ ∫ t in (0 : ℝ)..1, f t ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t _ => sq_nonneg _)
  have hj : 0 ≤ ∫ t in (0 : ℝ)..1, g t ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t _ => sq_nonneg _)
  have h := integral_mul_sq_le hf hg
  have hs1 := Real.sq_sqrt hi
  have hs2 := Real.sq_sqrt hj
  have hs0 := mul_nonneg (Real.sqrt_nonneg (∫ t in (0 : ℝ)..1, f t ^ 2))
    (Real.sqrt_nonneg (∫ t in (0 : ℝ)..1, g t ^ 2))
  nlinarith [sq_nonneg ((∫ t in (0 : ℝ)..1, f t * g t) -
    Real.sqrt (∫ t in (0 : ℝ)..1, f t ^ 2) * Real.sqrt (∫ t in (0 : ℝ)..1, g t ^ 2))]

/-- Integral of the affine power in Lemma 3.1. -/
theorem integral_affine_pow (n : ℕ) {δ : ℝ} (hδ : δ ≠ 0) :
    (∫ t in (0 : ℝ)..1, (1 + δ * t) ^ n) =
      ((1 + δ) ^ (n + 1) - 1) / (δ * (n + 1)) := by
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => (1 + δ * t) ^ (n + 1) / (δ * (n + 1))) ((1 + δ * t) ^ n) t := by
    intro t
    have h := (((hasDerivAt_id t).const_mul δ).const_add 1).pow (n + 1)
    have h' := h.div_const (δ * (n + 1))
    convert h' using 1
    · rfl
    · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, id_eq, mul_one]
      field_simp
  have hi : IntervalIntegrable (fun t : ℝ => (1 + δ * t) ^ n) volume 0 1 :=
    (by fun_prop : Continuous (fun t : ℝ => (1 + δ * t) ^ n)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hi]
  simp only [mul_zero, add_zero, one_pow, mul_one]
  ring

end LeanLab.KadiriLumley2014.Task64
