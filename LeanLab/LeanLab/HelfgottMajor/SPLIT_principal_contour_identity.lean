import LeanLab.HelfgottMajor.Decomp457a
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
Split of `principal_contour_identity` in `Decomp457a.lean`.

The one identity of the target combines four analytic steps.  This file cuts it along
exactly those steps, each carried on its own vertical contour, in the sign convention of
the logarithmic derivative, which is minus the Dirichlet series of the weighted von
Mangoldt sum:

1. the weighted prime sum is minus the vertical integral at real part two of the
   logarithmic derivative of the L-function against the shifted Gaussian transform and
   the scale factor (Dirichlet series to contour);
2. moving that line from real part two down to real part minus one half, in one step as
   P0014 Lemma 4.1 does at page 33 display 4.7, crosses the pole at one, whose residue is
   minus the main term, every nontrivial zero, which gives the two zero sums split at the
   height `T`, and the pole at zero, which gives log of two pi; the main term exists only
   at conductor one, which is the branching guard;
3. retired by U-1648: the first cut stopped at real part one half, which is not a contour,
   since the logarithmic derivative has a non integrable pole at every zero on that line;
4. at conductor one the L-function is the Riemann zeta function, so that last contour is
   the principal contour of the target.

Each leaf is one of those steps, so no leaf restates the target; the assembly at the end
chains the three live leaves and its own argument is rewriting and ring only.

Degenerate values.  Every contour below is an integral over all of `ℝ` on a line at real
part two or minus one half, where the integrand is continuous, so the integration variable
never divides.  The only division is the
fixed factor `1 / (2 * π)`, and `2 * π` is not zero.  The branching term `if q = 1` is
kept verbatim in every statement that has it, so it is the main term at `q = 1` and zero
otherwise.  At `δ = 0` the shift term `-δ` is `0`, the transform is the plain Gaussian and
the height hypothesis `max (4 * π ^ 2 * |δ|) 100 ≤ T` reads `100 ≤ T`, so no leaf
degenerates at the unshifted frequency.  The scale hypothesis is only `1 ≤ x`, so the
admissible range is `x ≥ 1`: no negative and no zero scale occurs, every power
`(x : ℂ) ^ s` is taken at positive base, and at `x = 1` the scale factor is `1` unless the
exponent is `0`.
-/

namespace LeanLab.HelfgottMajor.SPLIT_principal_contour_identity
open Real MeasureTheory LeanLab.HelfgottArcs Decomp123 Decomp269a Contour457

open scoped ArithmeticFunction

/-- The complex `enorm` is the `ofReal` of the norm. -/
private theorem wip_enorm_eq_ofReal (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [ENNReal.ofReal, Real.toNNReal_of_nonneg (norm_nonneg z)]
  rfl

/-- The von Mangoldt function vanishes at zero. -/
private theorem wip_vonMangoldt_zero : ArithmeticFunction.vonMangoldt 0 = 0 := by
  rw [ArithmeticFunction.vonMangoldt_apply, if_neg not_isPrimePow_zero]

/-! ### A. Integrability on the line of real part two -/

/-- The uniform bound of the Gaussian Mellin transform on a vertical line, at natural
real part. -/
private theorem gaussian_line_norm_le (δ : ℝ) (m : ℕ) (t : ℝ) :
    ‖gaussianMellin δ ((m : ℂ) + t * Complex.I)‖ ≤
      ∫ x in Set.Ioi (0 : ℝ), x ^ ((m : ℝ) - 1) * exp (-x ^ 2 / 2) := by
  have h := Gaussian269.mellin_norm_le δ ((m : ℂ) + t * Complex.I)
  simpa using h

/-- One recurrence step at natural real part: a factor `m + it` is gained. -/
private theorem gaussian_line_step (δ : ℝ) (m : ℕ) (hm : 0 < m) (t : ℝ) :
    ‖gaussianMellin δ ((m : ℂ) + t * Complex.I)‖ * ‖((m : ℂ) + t * Complex.I)‖ ≤
      ‖gaussianMellin δ (((m + 2 : ℕ) : ℂ) + t * Complex.I)‖ +
        ‖(2 * π * Complex.I * δ : ℂ)‖ *
          ‖gaussianMellin δ (((m + 1 : ℕ) : ℂ) + t * Complex.I)‖ := by
  have hrec := Continuation457.gaussian_mellin_recurrence δ ((m : ℂ) + t * Complex.I)
    (by simpa using hm)
  have e2 : ((m : ℂ) + t * Complex.I) + 2 = ((m + 2 : ℕ) : ℂ) + t * Complex.I := by
    push_cast; ring
  have e1 : ((m : ℂ) + t * Complex.I) + 1 = ((m + 1 : ℕ) : ℂ) + t * Complex.I := by
    push_cast; ring
  rw [e2, e1] at hrec
  have hnorm : ‖((m : ℂ) + t * Complex.I) * gaussianMellin δ ((m : ℂ) + t * Complex.I)‖
      = ‖gaussianMellin δ ((m : ℂ) + t * Complex.I)‖ * ‖((m : ℂ) + t * Complex.I)‖ := by
    rw [norm_mul, mul_comm]
  rw [← hnorm, hrec]
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [norm_mul]

/-- `‖m + it‖` dominates `sqrt (1 + t^2)` for real part at least one. -/
private theorem gaussian_line_norm_sqrt (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    sqrt (1 + t ^ 2) ≤ ‖((m : ℂ) + t * Complex.I)‖ := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hsq : ‖((m : ℂ) + t * Complex.I)‖ ^ 2 = (m : ℝ) ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    ring
  have hrew : sqrt ((m : ℝ) ^ 2 + t ^ 2) = ‖((m : ℂ) + t * Complex.I)‖ := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [← hrew]
  apply sqrt_le_sqrt
  nlinarith

/-- The decay bound on the line of real part two. -/
private theorem gaussian_line_decay (δ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖gaussianMellin δ (2 + t * Complex.I)‖ ≤ C / (1 + t ^ 2) := by
  set c : ℝ := ‖(2 * π * Complex.I * δ : ℂ)‖ with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact norm_nonneg _
  set B2 : ℝ := ∫ x in Set.Ioi (0 : ℝ), x ^ ((2 : ℝ) - 1) * exp (-x ^ 2 / 2) with hB2
  set B3 : ℝ := ∫ x in Set.Ioi (0 : ℝ), x ^ ((3 : ℝ) - 1) * exp (-x ^ 2 / 2) with hB3
  set B4 : ℝ := ∫ x in Set.Ioi (0 : ℝ), x ^ ((4 : ℝ) - 1) * exp (-x ^ 2 / 2) with hB4
  set B5 : ℝ := ∫ x in Set.Ioi (0 : ℝ), x ^ ((5 : ℝ) - 1) * exp (-x ^ 2 / 2) with hB5
  set B6 : ℝ := ∫ x in Set.Ioi (0 : ℝ), x ^ ((6 : ℝ) - 1) * exp (-x ^ 2 / 2) with hB6
  have hB40 : 0 ≤ B4 := by
    rw [hB4]
    exact setIntegral_nonneg measurableSet_Ioi fun x hx => by
      exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le
  have hB50 : 0 ≤ B5 := by
    rw [hB5]
    exact setIntegral_nonneg measurableSet_Ioi fun x hx => by
      exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le
  have hB60 : 0 ≤ B6 := by
    rw [hB6]
    exact setIntegral_nonneg measurableSet_Ioi fun x hx => by
      exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le
  refine ⟨B6 + c * B5 + c * (B5 + c * B4), ?_, fun t => ?_⟩
  · have h1 : 0 ≤ B6 + c * B5 := by nlinarith
    have h2 : 0 ≤ B5 + c * B4 := by nlinarith
    nlinarith
  · have hsq : (0 : ℝ) < sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have h5' : ‖gaussianMellin δ (((3 + 2 : ℕ) : ℂ) + t * Complex.I)‖ ≤ B5 := by
      have h5 := gaussian_line_norm_le δ 5 t
      rw [hB5]
      simpa using h5
    have h4' : ‖gaussianMellin δ (((3 + 1 : ℕ) : ℂ) + t * Complex.I)‖ ≤ B4 := by
      have h4 := gaussian_line_norm_le δ 4 t
      rw [hB4]
      simpa using h4
    have s3 : ‖gaussianMellin δ ((3 : ℂ) + t * Complex.I)‖ * ‖((3 : ℂ) + t * Complex.I)‖
        ≤ B5 + c * B4 := by
      have hraw := gaussian_line_step δ 3 (by norm_num) t
      rw [← hc] at hraw
      have hcd : c * ‖gaussianMellin δ (((3 + 1 : ℕ) : ℂ) + t * Complex.I)‖ ≤ c * B4 :=
        mul_le_mul_of_nonneg_left h4' hc0
      calc ‖gaussianMellin δ ((3 : ℂ) + t * Complex.I)‖ * ‖((3 : ℂ) + t * Complex.I)‖
          ≤ ‖gaussianMellin δ (((3 + 2 : ℕ) : ℂ) + t * Complex.I)‖ +
            c * ‖gaussianMellin δ (((3 + 1 : ℕ) : ℂ) + t * Complex.I)‖ := hraw
        _ ≤ B5 + c * B4 := by linarith
    have h6'' : ‖gaussianMellin δ (((4 + 2 : ℕ) : ℂ) + t * Complex.I)‖ ≤ B6 := by
      have h6 := gaussian_line_norm_le δ 6 t
      rw [hB6]
      simpa using h6
    have h5'' : ‖gaussianMellin δ (((4 + 1 : ℕ) : ℂ) + t * Complex.I)‖ ≤ B5 := by
      have h5 := gaussian_line_norm_le δ 5 t
      rw [hB5]
      simpa using h5
    have s4 : ‖gaussianMellin δ ((4 : ℂ) + t * Complex.I)‖ * ‖((4 : ℂ) + t * Complex.I)‖
        ≤ B6 + c * B5 := by
      have hraw := gaussian_line_step δ 4 (by norm_num) t
      rw [← hc] at hraw
      have hcd : c * ‖gaussianMellin δ (((4 + 1 : ℕ) : ℂ) + t * Complex.I)‖ ≤ c * B5 :=
        mul_le_mul_of_nonneg_left h5'' hc0
      calc ‖gaussianMellin δ ((4 : ℂ) + t * Complex.I)‖ * ‖((4 : ℂ) + t * Complex.I)‖
          ≤ ‖gaussianMellin δ (((4 + 2 : ℕ) : ℂ) + t * Complex.I)‖ +
            c * ‖gaussianMellin δ (((4 + 1 : ℕ) : ℂ) + t * Complex.I)‖ := hraw
        _ ≤ B6 + c * B5 := by linarith
    have hs3 : (0 : ℝ) < ‖((3 : ℂ) + t * Complex.I)‖ :=
      lt_of_lt_of_le hsq (gaussian_line_norm_sqrt 3 (by norm_num) t)
    have hs4 : (0 : ℝ) < ‖((4 : ℂ) + t * Complex.I)‖ :=
      lt_of_lt_of_le hsq (gaussian_line_norm_sqrt 4 (by norm_num) t)
    have sq3 := gaussian_line_norm_sqrt 3 (by norm_num) t
    have sq4 := gaussian_line_norm_sqrt 4 (by norm_num) t
    have sq2 := gaussian_line_norm_sqrt 2 (by norm_num) t
    have d3 : ‖gaussianMellin δ ((3 : ℂ) + t * Complex.I)‖ ≤ (B5 + c * B4) / sqrt (1 + t ^ 2) := by
      have h1 : ‖gaussianMellin δ ((3 : ℂ) + t * Complex.I)‖ ≤
          (B5 + c * B4) / ‖((3 : ℂ) + t * Complex.I)‖ := by
        rw [le_div_iff₀ hs3]; linarith
      exact h1.trans (div_le_div_of_nonneg_left (by nlinarith) hsq sq3)
    have d4 : ‖gaussianMellin δ ((4 : ℂ) + t * Complex.I)‖ ≤ (B6 + c * B5) / sqrt (1 + t ^ 2) := by
      have h1 : ‖gaussianMellin δ ((4 : ℂ) + t * Complex.I)‖ ≤
          (B6 + c * B5) / ‖((4 : ℂ) + t * Complex.I)‖ := by
        rw [le_div_iff₀ hs4]; linarith
      exact h1.trans (div_le_div_of_nonneg_left (by nlinarith) hsq sq4)
    have hraw := gaussian_line_step δ 2 (by norm_num) t
    rw [← hc] at hraw
    have d3' : ‖gaussianMellin δ (((2 + 1 : ℕ) : ℂ) + t * Complex.I)‖ ≤
        (B5 + c * B4) / sqrt (1 + t ^ 2) := d3
    have d4' : ‖gaussianMellin δ (((2 + 2 : ℕ) : ℂ) + t * Complex.I)‖ ≤
        (B6 + c * B5) / sqrt (1 + t ^ 2) := d4
    have hprod : ‖gaussianMellin δ ((2 : ℂ) + t * Complex.I)‖ * ‖((2 : ℂ) + t * Complex.I)‖
        ≤ (B6 + c * B5 + c * (B5 + c * B4)) / sqrt (1 + t ^ 2) := by
      have hcd : c * ‖gaussianMellin δ (((2 + 1 : ℕ) : ℂ) + t * Complex.I)‖ ≤
          c * ((B5 + c * B4) / sqrt (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left d3' hc0
      have heq : (B6 + c * B5) / sqrt (1 + t ^ 2) +
          c * ((B5 + c * B4) / sqrt (1 + t ^ 2)) =
          (B6 + c * B5 + c * (B5 + c * B4)) / sqrt (1 + t ^ 2) := by
        field_simp
      calc ‖gaussianMellin δ ((2 : ℂ) + t * Complex.I)‖ * ‖((2 : ℂ) + t * Complex.I)‖
          ≤ ‖gaussianMellin δ (((2 + 2 : ℕ) : ℂ) + t * Complex.I)‖ +
            c * ‖gaussianMellin δ (((2 + 1 : ℕ) : ℂ) + t * Complex.I)‖ := hraw
        _ ≤ (B6 + c * B5) / sqrt (1 + t ^ 2) +
            c * ((B5 + c * B4) / sqrt (1 + t ^ 2)) := add_le_add d4' hcd
        _ = _ := heq
    have key : ‖gaussianMellin δ ((2 : ℂ) + t * Complex.I)‖ * (1 + t ^ 2) ≤
        B6 + c * B5 + c * (B5 + c * B4) := by
      have h1 : ‖gaussianMellin δ ((2 : ℂ) + t * Complex.I)‖ *
          ‖((2 : ℂ) + t * Complex.I)‖ * sqrt (1 + t ^ 2) ≤
          B6 + c * B5 + c * (B5 + c * B4) := by
        have h := mul_le_mul_of_nonneg_right hprod hsq.le
        rwa [div_mul_cancel₀ _ hsq.ne'] at h
      have h3 : sqrt (1 + t ^ 2) * sqrt (1 + t ^ 2) = 1 + t ^ 2 :=
        Real.mul_self_sqrt (by positivity)
      have h4 : sqrt (1 + t ^ 2) * sqrt (1 + t ^ 2)
          ≤ ‖((2 : ℂ) + t * Complex.I)‖ * sqrt (1 + t ^ 2) :=
        mul_le_mul_of_nonneg_right sq2 hsq.le
      rw [h3] at h4
      calc ‖gaussianMellin δ ((2 : ℂ) + t * Complex.I)‖ * (1 + t ^ 2)
          ≤ ‖gaussianMellin δ ((2 : ℂ) + t * Complex.I)‖ *
            (‖((2 : ℂ) + t * Complex.I)‖ * sqrt (1 + t ^ 2)) :=
            mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
        _ = ‖gaussianMellin δ ((2 : ℂ) + t * Complex.I)‖ *
            ‖((2 : ℂ) + t * Complex.I)‖ * sqrt (1 + t ^ 2) := by ring
        _ ≤ _ := h1
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 1 + t ^ 2)]
    simpa using key

/-- The Gaussian Mellin transform is integrable on the line of real part two. -/
private theorem gaussian_line_integrable (δ : ℝ) :
    Integrable (fun t : ℝ => gaussianMellin δ (2 + t * Complex.I)) := by
  obtain ⟨C, hC0, hC⟩ := gaussian_line_decay δ
  have hcont : Continuous (fun t : ℝ => gaussianMellin δ (2 + t * Complex.I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hpos : 0 < ((2 : ℂ) + t * Complex.I).re := by simp
    exact ContinuousAt.comp (f := fun t : ℝ => (2 : ℂ) + t * Complex.I)
      (Continuation457.gaussian_mellin_differentiable δ _ hpos).continuousAt (by fun_prop)
  refine Integrable.mono' (g := fun t : ℝ => C * (1 + t ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul C) hcont.aestronglyMeasurable ?_
  filter_upwards with t
  simpa [div_eq_mul_inv] using hC t

/-! ### B. The logarithmic derivative as the twisted von Mangoldt series -/

/-- `logDeriv (LFunction χ) s` is minus the Dirichlet series of `χ * Λ` on `Re s > 1`. -/
private theorem logDeriv_LFunction_eq_series {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.LFunction χ) s =
      - LSeries ((fun n : ℕ => (χ ((n : ℕ) : ZMod q) : ℂ)) *
          fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s := by
  have h1 : logDeriv (DirichletCharacter.LFunction χ) s =
      deriv (LSeries (χ ·)) s / LSeries (χ ·) s := by
    rw [logDeriv, Pi.div_apply, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
      DirichletCharacter.LFunction_eq_LSeries χ hs]
  have htw := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have htw2 : LSeries ((fun n : ℕ => (χ ((n : ℕ) : ZMod q) : ℂ)) *
      fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s =
      - deriv (LSeries (χ ·)) s / LSeries (χ ·) s := by
    simpa using htw
  rw [h1]
  have hneg : deriv (LSeries (χ ·)) s / LSeries (χ ·) s =
      - LSeries ((fun n : ℕ => (χ ((n : ℕ) : ZMod q) : ℂ)) *
          fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) s := by
    have h2 := congrArg Neg.neg htw2
    simp only [neg_div, neg_neg] at h2
    exact h2.symm
  exact hneg

/-! ### C. Pointwise Mellin inversion at real part two -/

/-- `(x / n) ^ s = ((n / x)) ^ (-s)` for positive `x` and `n`. -/
private theorem cpow_div_neg (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 0 < n) (s : ℂ) :
    ((x / n : ℝ) : ℂ) ^ s = (((n : ℝ) / x : ℝ) : ℂ) ^ (-s) := by
  have hz : ((x / n : ℝ) : ℂ) = (((n : ℝ) / x : ℝ) : ℂ)⁻¹ := by
    have hreal : (x / (n : ℝ) : ℝ) = ((n : ℝ) / x)⁻¹ := by field_simp
    rw [hreal]
    push_cast
    ring
  rw [hz, Complex.inv_cpow_ofReal_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) / x) s,
    Complex.cpow_neg]

/-- The pointwise Mellin inversion: the vertical integral at real part two recovers the
Gaussian weight at `n / x`, up to the factor `2 * π`. -/
private theorem mellin_inversion_line (δ : ℝ) (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 0 < n) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ, gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
        ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I) =
      (exp (-((n : ℝ) / x) ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x)) := by
  have hy : (0 : ℝ) < (n : ℝ) / x := by positivity
  have hcont2 : Continuous (fun u : ℝ => (exp (-u ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * u)) := by
    unfold LeanLab.HelfgottArcs.e
    fun_prop
  have hinv := mellinInv_mellin_eq 2 (fun u : ℝ => (exp (-u ^ 2 / 2) : ℂ) * LeanLab.HelfgottArcs.e (δ * u)) hy
    (Gaussian269.mellin_integrable δ 2 (by norm_num)) (gaussian_line_integrable δ) hcont2.continuousAt
  have hpt : ∀ t : ℝ, (((n : ℝ) / x : ℝ) : ℂ) ^ (-(((2 : ℕ) : ℂ) + t * Complex.I)) =
      ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I) := by
    intro t
    have h := cpow_div_neg x hx n hn (((2 : ℕ) : ℂ) + t * Complex.I)
    rw [h]
  have hgoal : (1 / (2 * π) : ℂ) * ∫ t : ℝ, gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
        ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)
      = (1 / (2 * π) : ℂ) * ∫ t : ℝ, (((n : ℝ) / x : ℝ) : ℂ) ^ (-(((2 : ℕ) : ℂ) + t * Complex.I)) *
          gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) := by
    congr 1
    congr 1
    funext t
    rw [hpt t]
    ring
  rw [hgoal]
  simpa [mellinInv, gaussianMellin] using hinv

/-! ### D. Interchange of the sum over `n` and the integral over `t` -/

/-- `x ^ s * n ^ (-s) = (x / n) ^ s` for positive `x` and `n`. -/
private theorem cpow_div_eq (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 0 < n) (s : ℂ) :
    (x : ℂ) ^ s * (n : ℂ) ^ (-s) = ((x / n : ℝ) : ℂ) ^ s := by
  have h1 : ((x / n : ℝ) : ℂ) ^ s =
      (x : ℂ) ^ s * (((1 : ℝ) / n : ℝ) : ℂ) ^ s := by
    rw [show (x / n : ℝ) = x * (1 / (n : ℝ)) by ring]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx.le (by positivity) s]
  have h2 : (((1 : ℝ) / n : ℝ) : ℂ) ^ s = ((n : ℂ) ^ s)⁻¹ := by
    rw [show ((1 : ℝ) / n : ℝ) = ((n : ℝ))⁻¹ by ring]
    rw [Complex.ofReal_inv]
    exact Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg n) s
  rw [h1, h2, Complex.cpow_neg]

/-- The pure interchange: no constant is pulled out of any integral. -/
private theorem series_integral_swap (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) :
    (∫ t : ℝ, ∑' n : ℕ, -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))) =
      ∑' n : ℕ, ∫ t : ℝ, -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I))) := by
  have hx0 : 0 < x := by linarith
  have hGc : Continuous (fun t : ℝ => gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hpos : 0 < ((((2 : ℕ) : ℂ) + t * Complex.I)).re := by simp
    exact ContinuousAt.comp (f := fun t : ℝ => (((2 : ℕ) : ℂ) + t * Complex.I))
      (Continuation457.gaussian_mellin_differentiable δ _ hpos).continuousAt (by fun_prop)
  have hGint : Integrable (fun t : ℝ => ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖) := by
    simpa using (gaussian_line_integrable δ).norm
  have hGfin : ∫⁻ t : ℝ,
      ENNReal.ofReal ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ < ⊤ := by
    have h := hGint.hasFiniteIntegral
    rw [HasFiniteIntegral] at h
    simpa [Real.enorm_eq_ofReal_abs, abs_of_nonneg (norm_nonneg _)] using h
  have hmaj : ∀ (n : ℕ) (t : ℝ),
      ‖-(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))‖ ≤
      (Λ n : ℝ) * (x / n) ^ 2 * ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ := by
    intro n t
    by_cases hn : n = 0
    · simp [hn]
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hxn : (0 : ℝ) < x / n := div_pos hx0 hnpos
      have hchi : ‖(χ ((n : ℕ) : ZMod q) : ℂ)‖ ≤ 1 :=
        DirichletCharacter.norm_le_one (χ := χ) ((n : ℕ) : ZMod q)
      have hcp : ‖((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)‖ = (x / n) ^ 2 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxn]
        norm_num
      have hΛ : (0 : ℝ) ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
      have hstep : ‖(χ ((n : ℕ) : ZMod q) : ℂ)‖ * (x / n) ^ 2 *
          ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ ≤
          1 * (x / n) ^ 2 * ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ := by
        have hz : (0 : ℝ) ≤ (x / n) ^ 2 * ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ := by
          positivity
        nlinarith [norm_nonneg (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I))]
      rw [norm_neg, norm_mul, norm_mul, norm_mul, hcp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hΛ]
      nlinarith [hstep, hΛ]
  have hbase : Summable (fun n : ℕ => (Λ n : ℝ) / (n : ℝ) ^ 2) := by
    have hC : Summable (fun n : ℕ => ((Λ n : ℝ) : ℂ) / (n : ℂ) ^ (2 : ℂ)) := by
      have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (2 : ℂ)) (by norm_num)
      rw [LSeriesSummable] at h
      unfold LSeries.term at h
      exact h.congr fun n => by
        by_cases hn : n = 0
        · simp [hn]
        · simp only [hn, ite_false]
    have hL : Summable (fun n : ℕ => ‖((Λ n : ℝ) : ℂ) / (n : ℂ) ^ (2 : ℂ)‖) := hC.norm
    have heq : ∀ n : ℕ, ‖((Λ n : ℝ) : ℂ) / (n : ℂ) ^ (2 : ℂ)‖ =
        (Λ n : ℝ) / (n : ℝ) ^ 2 := by
      intro n
      rcases eq_or_ne n 0 with h0 | h0
      · subst h0
        simp [wip_vonMangoldt_zero]
      · have hΛ : (0 : ℝ) ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
        rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) from by norm_num, Complex.cpow_natCast, norm_div,
          norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hΛ]
    simpa only [heq] using hL
  have hcoef : Summable (fun n : ℕ => (Λ n : ℝ) * (x / n) ^ 2) := by
    have h2 : Summable (fun n : ℕ => (x : ℝ) ^ 2 * ((Λ n : ℝ) / (n : ℝ) ^ 2)) :=
      hbase.mul_left _
    refine h2.congr fun n => ?_
    by_cases hn : n = 0
    · simp [hn]
    · field_simp
  have hcoef0 : ∀ n : ℕ, (0 : ℝ) ≤ (Λ n : ℝ) * (x / n) ^ 2 := by
    intro n
    have hΛ : (0 : ℝ) ≤ (Λ n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    positivity
  have hmaj2 : ∀ n : ℕ, ∫⁻ t : ℝ, ENNReal.ofReal ‖-(((Λ n : ℝ) : ℂ) *
        (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))‖ ≤
      ENNReal.ofReal ((Λ n : ℝ) * (x / n) ^ 2) *
        ∫⁻ t : ℝ, ENNReal.ofReal ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ := by
    intro n
    calc ∫⁻ t : ℝ, ENNReal.ofReal ‖-(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
          (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
            ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))‖
        ≤ ∫⁻ t : ℝ, ENNReal.ofReal ((Λ n : ℝ) * (x / n) ^ 2) *
            ENNReal.ofReal ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ := by
          refine lintegral_mono fun t => ?_
          calc ENNReal.ofReal ‖-(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
                (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
                  ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))‖
              ≤ ENNReal.ofReal ((Λ n : ℝ) * (x / n) ^ 2 *
                  ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖) :=
                ENNReal.ofReal_le_ofReal (hmaj n t)
            _ = ENNReal.ofReal ((Λ n : ℝ) * (x / n) ^ 2) *
                  ENNReal.ofReal ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ :=
                ENNReal.ofReal_mul (hcoef0 n)
      _ = ENNReal.ofReal ((Λ n : ℝ) * (x / n) ^ 2) *
            ∫⁻ t : ℝ, ENNReal.ofReal ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ :=
          lintegral_const_mul'' _ (hGc.aemeasurable.norm.ennreal_ofReal)
  have hf : ∀ n : ℕ, AEStronglyMeasurable (fun t : ℝ =>
      -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))) := by
    intro n
    by_cases hn : n = 0
    · have hzero : (fun t : ℝ => -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
          (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
            ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))) = fun _ => 0 := by
        funext t
        simp [hn]
      rw [hzero]
      exact aestronglyMeasurable_const
    · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hxn : (0 : ℝ) < x / n := div_pos hx0 hnpos
      have hcc : Continuous fun t : ℝ =>
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I) := by
        refine Continuous.comp ?_ (by fun_prop : Continuous fun t : ℝ => (((2 : ℕ) : ℂ) + t * Complex.I))
        exact continuous_iff_continuousAt.mpr fun z =>
          continuousAt_const_cpow (by exact_mod_cast hxn.ne')
      exact ((hGc.mul hcc).const_mul _).neg.aestronglyMeasurable
  have hf' : (∑' n : ℕ, ∫⁻ t : ℝ, ‖-(((Λ n : ℝ) : ℂ) *
        (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))‖ₑ) ≠ ⊤ := by
    have hof : (∑' n : ℕ, ∫⁻ t : ℝ, ENNReal.ofReal ‖-(((Λ n : ℝ) : ℂ) *
          (χ ((n : ℕ) : ZMod q) : ℂ) *
          (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
            ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))‖) ≠ ⊤ := by
      have hsum : ∑' n : ℕ, ENNReal.ofReal ((Λ n : ℝ) * (x / n) ^ 2) ≠ ⊤ := by
        have h := ENNReal.ofReal_tsum_of_nonneg (f := fun n : ℕ => (Λ n : ℝ) * (x / n) ^ 2)
          hcoef0 hcoef
        rw [← h]
        exact ENNReal.ofReal_ne_top
      refine ne_of_lt ?_
      calc ∑' n : ℕ, ∫⁻ t : ℝ, ENNReal.ofReal ‖-(((Λ n : ℝ) : ℂ) *
            (χ ((n : ℕ) : ZMod q) : ℂ) *
            (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
              ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))‖
          ≤ ∑' n : ℕ, ENNReal.ofReal ((Λ n : ℝ) * (x / n) ^ 2) *
              ∫⁻ t : ℝ, ENNReal.ofReal ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ :=
            ENNReal.tsum_le_tsum hmaj2
        _ = (∑' n : ℕ, ENNReal.ofReal ((Λ n : ℝ) * (x / n) ^ 2)) *
              ∫⁻ t : ℝ, ENNReal.ofReal ‖gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I)‖ :=
            ENNReal.tsum_mul_right
        _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hsum) hGfin
    simpa only [wip_enorm_eq_ofReal] using hof
  rw [integral_tsum hf hf']

/-! ### E. The per-`n` value of the vertical integral, and the leaf -/

/-- `etaHeart` is the plain Gaussian on the positive half line. -/
private theorem etaHeart_eq_exp {y : ℝ} (hy : 0 < y) :
    etaHeart y = Real.exp (-y ^ 2 / 2) := by
  rw [etaHeart, if_pos hy]

/-- The `n`-th vertical integral: the `2 π` times the Gaussian weight at `n / x`. -/
private theorem integral_summand (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) (n : ℕ) :
    (∫ t : ℝ, -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))) =
      -(2 * π * (((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
        ((etaHeart ((n : ℝ) / x) : ℂ) * LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x))))) := by
  rcases eq_or_ne n 0 with h0 | h0
  · subst h0
    simp [wip_vonMangoldt_zero]
  · have hn : 0 < n := Nat.pos_of_ne_zero h0
    have hx0 : (0 : ℝ) < x := by linarith
    have hpi : (2 * π : ℂ) ≠ 0 := by
      have h : (0 : ℝ) < 2 * π := by positivity
      exact_mod_cast ne_of_gt h
    have hpull : (∫ t : ℝ, -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))) =
        (-(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ))) *
          ∫ t : ℝ, gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
            ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I) := by
      rw [show (fun t : ℝ => -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
            (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
              ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)))) =
          (fun t : ℝ => (-(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ))) *
            (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
              ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I))) from by
        funext t
        ring]
      rw [integral_const_mul]
    have hI : (∫ t : ℝ, gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)) =
        2 * π * ((Real.exp (-((n : ℝ) / x) ^ 2 / 2) : ℂ) *
          LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x))) := by
      have h := mellin_inversion_line δ x hx0 n hn
      have hinv : (1 / (2 * π) : ℂ)⁻¹ = 2 * π := by
        rw [one_div, inv_inv]
      have hne : (1 / (2 * π) : ℂ) ≠ 0 := by
        rw [one_div]
        exact inv_ne_zero hpi
      calc (∫ t : ℝ, gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
            ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I))
          = (1 / (2 * π) : ℂ)⁻¹ * ((1 / (2 * π) : ℂ) *
              ∫ t : ℝ, gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
                ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
        _ = (1 / (2 * π) : ℂ)⁻¹ * ((Real.exp (-((n : ℝ) / x) ^ 2 / 2) : ℂ) *
              LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x))) := by rw [h]
        _ = 2 * π * ((Real.exp (-((n : ℝ) / x) ^ 2 / 2) : ℂ) *
              LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x))) := by rw [hinv]
    rw [hpull, hI, ← etaHeart_eq_exp (by positivity : (0 : ℝ) < (n : ℝ) / x)]
    ring

/-- The pointwise expansion of the integrand as the twisted von Mangoldt series. -/
private theorem integrand_tsum (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) (t : ℝ) :
    logDeriv (DirichletCharacter.LFunction χ) (((2 : ℕ) : ℂ) + t * Complex.I) *
        gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
        (x : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I) =
      ∑' n : ℕ, -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
        (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I))) := by
  set s : ℂ := ((2 : ℕ) : ℂ) + t * Complex.I with hsv
  have hs : 1 < s.re := by simp [s]
  have hx0 : (0 : ℝ) < x := by linarith
  have hterm : ∀ n : ℕ,
      LSeries.term ((fun n : ℕ => (χ ((n : ℕ) : ZMod q) : ℂ)) *
          fun n : ℕ => ((Λ n : ℝ) : ℂ)) s n =
        (χ ((n : ℕ) : ZMod q) : ℂ) * ((Λ n : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
    intro n
    unfold LSeries.term
    by_cases hn : n = 0
    · simp [hn, wip_vonMangoldt_zero]
    · simp only [hn, if_false, Pi.mul_apply, div_eq_mul_inv]
      rw [← Complex.cpow_neg]
      try ring
  have hkey : logDeriv (DirichletCharacter.LFunction χ) s =
      ∑' n : ℕ, -((χ ((n : ℕ) : ZMod q) : ℂ) * ((Λ n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) := by
    rw [logDeriv_LFunction_eq_series (q := q) χ hs]
    rw [show -LSeries ((fun n : ℕ => (χ ((n : ℕ) : ZMod q) : ℂ)) *
        fun n : ℕ => ((Λ n : ℝ) : ℂ)) s = -(∑' n : ℕ,
        (χ ((n : ℕ) : ZMod q) : ℂ) * ((Λ n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) from by
      unfold LSeries
      exact congrArg Neg.neg (tsum_congr hterm)]
    rw [← tsum_neg]
  rw [hkey, ← tsum_mul_right, ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · simp [hn, wip_vonMangoldt_zero]
  · have hnn : 0 < n := Nat.pos_of_ne_zero hn
    rw [show -((χ ((n : ℕ) : ZMod q) : ℂ) * ((Λ n : ℝ) : ℂ) * (n : ℂ) ^ (-s)) *
          gaussianMellin δ s * (x : ℂ) ^ s =
        -(((χ ((n : ℕ) : ZMod q) : ℂ) * ((Λ n : ℝ) : ℂ)) * gaussianMellin δ s *
          ((x : ℂ) ^ s * (n : ℂ) ^ (-s))) from by ring]
    rw [cpow_div_eq x hx0 n hnn s]
    ring

/-- LEAF. Step one, the Dirichlet series as a contour integral.  The weighted prime sum
`Schi` is minus the vertical integral at real part two of the logarithmic derivative of
the L-function times the shifted Gaussian transform times the scale factor.  The line at
real part two lies in the half plane of absolute convergence, no zero of the L-function
lies on it, and this step moves no contour: it only writes the sum as an integral. -/
theorem principal_prime_sum_mellin_contour (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ : ℝ) :
    Schi etaHeart χ δ x =
      -((1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
          gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((2 : ℂ) + t * Complex.I)) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hint : (∫ t : ℝ,
      logDeriv (DirichletCharacter.LFunction χ) (((2 : ℕ) : ℂ) + t * Complex.I) *
        gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
        (x : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I)) =
      -(2 * π * Schi etaHeart χ δ x) := by
    calc (∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) (((2 : ℕ) : ℂ) + t * Complex.I) *
          gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
          (x : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I))
        = ∫ t : ℝ, ∑' n : ℕ, -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
            (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
              ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I))) := by
          simp only [integrand_tsum x hx q χ δ]
      _ = ∑' n : ℕ, ∫ t : ℝ, -(((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
            (gaussianMellin δ (((2 : ℕ) : ℂ) + t * Complex.I) *
              ((x / n : ℝ) : ℂ) ^ (((2 : ℕ) : ℂ) + t * Complex.I))) :=
          series_integral_swap x hx q χ δ
      _ = ∑' n : ℕ, -(2 * π * (((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
            ((etaHeart ((n : ℝ) / x) : ℂ) * LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x))))) :=
          tsum_congr fun n => integral_summand x hx q χ δ n
      _ = -(2 * π * ∑' n : ℕ, (((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
            ((etaHeart ((n : ℝ) / x) : ℂ) * LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x))))) := by
          rw [tsum_neg, tsum_mul_left]
      _ = -(2 * π * Schi etaHeart χ δ x) := by
          rw [show Schi etaHeart χ δ x = ∑' n : ℕ,
              (((Λ n : ℝ) : ℂ) * (χ ((n : ℕ) : ZMod q) : ℂ) *
                ((etaHeart ((n : ℝ) / x) : ℂ) *
                  LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x)))) from by
            unfold Schi
            refine tsum_congr fun n => ?_
            have he : LeanLab.HelfgottArcs.e (δ * ((n : ℝ) / x)) =
                LeanLab.HelfgottArcs.e (δ * (n : ℝ) / x) := by
              congr 1
              ring
            rw [he]
            ring]
  simp only [Nat.cast_ofNat] at hint ⊢
  rw [hint]
  have h3 : -((1 / (2 * π) : ℂ) * -(2 * π * Schi etaHeart χ δ x)) =
      Schi etaHeart χ δ x := by
    have hpi : (2 * π : ℂ) ≠ 0 := by
      have h : (0 : ℝ) < 2 * π := by positivity
      exact_mod_cast ne_of_gt h
    field_simp
  rw [h3]


/-- LEAF. Step two, the whole contour shift, P0014 Lemma 4.1, page 33 display 4.7, at
conductor one.  Moving the vertical line from real part two down to real part minus one
half crosses the pole at one, whose residue is minus the main term, which is the guarded
term; every nontrivial zero with its analytic multiplicity, which gives the two zero sums
split at the height `T` with the plus sign they carry in the target; and the pole at zero,
where the logarithmic derivative of zeta is log of two pi and the continued transform has
residue one.  No zero hypothesis is needed: the two zero sums together run over every zero
in the strip.  U-1648 replaced the former leaves `principal_contour_line_shift_pole_at_one`
and `principal_contour_zero_band_crossing` by this one; both were false, since their line
at real part one half meets zeros of zeta, the integrand is not integrable there and the
Lean integral on that line is zero. -/
theorem principal_contour_shift_two_to_minus_half (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (δ T : ℝ) (hq : q = 1) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
          gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((2 : ℂ) + t * Complex.I) =
      ((1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
          continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)) +
        (log (2 * π) : ℂ) + lowZeros χ δ x T + highZeros χ δ x T -
        (if q = 1 then fhat etaHeart (-δ) * x else 0) := by
  sorry

/-- LEAF. Step four, the conductor one identification.  At conductor one the character is
the trivial one and its L-function is the Riemann zeta function, so the contour at real
part minus one half written with the L-function is literally the principal contour of the
target, which is written with the zeta function.  This step is a naming step: no contour
moves and no sum occurs. -/
theorem principal_contour_conductor_one (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : q = 1) (δ : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ t : ℝ,
        logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
          continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
          (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I) =
      principalContour δ x := by
  subst hq
  unfold principalContour
  congr 1
  congr
  funext t
  congr 2
  have h_triv : χ = 1 := Subsingleton.elim χ 1
  rw [h_triv, DirichletCharacter.LFunction_modOne_eq]

/-- The conductor one contour identity, assembled from the four steps above by rewriting
and ring only.  The target statement is unchanged; the assembly has no sorry of its own
and does not use the target theorem.  Since U-1648 it chains three leaves, and its binders
`hχ`, `hT` and `hzeros` are kept only so that its type stays the target's. -/
theorem principal_contour_identity_split (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ) (hq : q = 1)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
      lowZeros χ δ x T + highZeros χ δ x T =
        -(log (2 * π) : ℂ) - principalContour δ x := by
  let A : ℂ := (1 / (2 * π) : ℂ) * ∫ t : ℝ,
    logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
      gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
      (x : ℂ) ^ ((2 : ℂ) + t * Complex.I)
  let C : ℂ := (1 / (2 * π) : ℂ) * ∫ t : ℝ,
    logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
      continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
      (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I)
  have hA : A = (1 / (2 * π) : ℂ) * ∫ t : ℝ,
      logDeriv (DirichletCharacter.LFunction χ) ((2 : ℂ) + t * Complex.I) *
        gaussianMellin δ ((2 : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((2 : ℂ) + t * Complex.I) := rfl
  have hC : C = (1 / (2 * π) : ℂ) * ∫ t : ℝ,
      logDeriv (DirichletCharacter.LFunction χ) ((-1 / 2 : ℂ) + t * Complex.I) *
        continuedGaussian δ ((-1 / 2 : ℂ) + t * Complex.I) *
        (x : ℂ) ^ ((-1 / 2 : ℂ) + t * Complex.I) := rfl
  have h1 := principal_prime_sum_mellin_contour x hx q χ δ
  have h2 := principal_contour_shift_two_to_minus_half x hx q χ δ T hq
  have h4 := principal_contour_conductor_one x hx q χ hq δ
  have e1 : Schi etaHeart χ δ x = -A := by
    rw [hA]; exact h1
  have e2 : A = C + (log (2 * π) : ℂ) + lowZeros χ δ x T + highZeros χ δ x T -
      (if q = 1 then fhat etaHeart (-δ) * x else 0) := by
    rw [hA, hC]; exact h2
  have e4 : C = principalContour δ x := by
    rw [hC]; exact h4
  rw [e1, e2, e4]
  ring

end LeanLab.HelfgottMajor.SPLIT_principal_contour_identity

#print axioms LeanLab.HelfgottMajor.SPLIT_principal_contour_identity.principal_contour_identity_split
#print axioms LeanLab.HelfgottMajor.SPLIT_principal_contour_identity.principal_contour_conductor_one
#print axioms LeanLab.HelfgottMajor.SPLIT_principal_contour_identity.principal_prime_sum_mellin_contour
