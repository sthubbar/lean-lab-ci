import LeanLab.HelfgottMajor.Energy669
import LeanLab.HelfgottMajor.Prep1121VIPointwise
import LeanLab.HelfgottMajor.Prep1121VIIntegral

/-!
PREP 2026-11-21, route step `MainLemma41Split123.vertical_integral_bound`, part F.
P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, pages 34 and 35,
displays 4.12 to 4.15. `Energy669.vertical_integral_bound_of_log_energy` already proves the
step CONDITIONAL ON hL and hbudget. This file supplies hL and hbudget from the pointwise
bound `Prep1121VIPointwise.pointwise_4_12`, the certified integral
`Prep1121VIIntegral.certified_integral` and three leaves, and proves the step's exact
statement in `vertical_integral_bound_of_leaves`.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121VIBudget
open Real Complex MeasureTheory Set

/-- LEAF: P0014 page 34, the integrand of 4.13 is defined on all of re s = -1/2: for
primitive χ, τ ↦ L'/L(-1/2 + iτ, χ) is continuous, because L(s, χ) is holomorphic away
from s = 1 and has no zero on re s = -1/2, `LeanLab.Linnik.ExplicitFormula.no_zero_left_line`.
Class MEDIUM: analyticity of `DirichletCharacter.LFunction` off 1 gives a continuous
derivative; one Mathlib search. -/
theorem logDeriv_line_continuous {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) :
    Continuous (fun τ : ℝ => deriv χ.LFunction ((-1 / 2 : ℂ) + τ * I) /
      χ.LFunction ((-1 / 2 : ℂ) + τ * I)) := by
  sorry

/-- LEAF: P0014 page 35, the two functions of the Minkowski split after 4.12 are square
integrable on the line: for real A and K, τ ↦ ((1/2) log(τ² + 9/4) + K)/√(1/4 + τ²) and
τ ↦ A/√(1/4 + τ²) are in L². Class MEDIUM: continuity and an O(log τ / τ) bound, or
`memLp_two_iff_integrable_sq_norm` with integrability of log²/(1/4 + τ²). -/
theorem memLp_split (A K : ℝ) :
    MemLp (fun τ : ℝ => A / Real.sqrt (1 / 4 + τ ^ 2)) 2 ∧
      MemLp (fun τ : ℝ => ((1 / 2) * Real.log (τ ^ 2 + 9 / 4) + K) /
        Real.sqrt (1 / 4 + τ ^ 2)) 2 := by
  sorry

/-- LEAF: P0014 page 35, the Minkowski step after 4.12 in L²(ℝ): if ‖F‖ ≤ u + v pointwise
with u, v in L² and F measurable, then F is in L² and √∫‖F‖² ≤ √∫u² + √∫v².
Class MEDIUM: `MemLp.of_le` and `lpNorm_add_le`, as in `Energy669.gaussian_numerator_L2_sharp`.
PROVED here. -/
theorem l2_triangle (F : ℝ → ℂ) (u v : ℝ → ℝ) (hF : AEStronglyMeasurable F volume)
    (hu : MemLp u 2) (hv : MemLp v 2) (hpt : ∀ τ, ‖F τ‖ ≤ u τ + v τ) :
    MemLp F 2 ∧ Real.sqrt (∫ τ, ‖F τ‖ ^ 2) ≤
      Real.sqrt (∫ τ, u τ ^ 2) + Real.sqrt (∫ τ, v τ ^ 2) := by
  have huv : MemLp (u + v) 2 := hu.add hv
  have hle : ∀ τ, ‖F τ‖ ≤ ‖(u + v) τ‖ := fun τ =>
    (hpt τ).trans ((le_abs_self _).trans_eq (Real.norm_eq_abs _).symm)
  have hFm : MemLp F 2 := huv.of_le hF (Filter.Eventually.of_forall hle)
  refine ⟨hFm, ?_⟩
  have hnorm (w : ℝ → ℝ) (hw : MemLp w 2) :
      lpNorm w 2 volume = Real.sqrt (∫ τ, w τ ^ 2) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hw.aestronglyMeasurable]
    simp only [Real.norm_eq_abs, sq_abs]
    norm_num [Real.sqrt_eq_rpow]
  have hmin := lpNorm_add_le (g := v) hu (by norm_num : (1 : ENNReal) ≤ 2)
  rw [hnorm _ huv, hnorm _ hu, hnorm _ hv] at hmin
  refine le_trans ?_ hmin
  apply Real.sqrt_le_sqrt
  have hi : Integrable (fun τ => ((u + v) τ) ^ 2) :=
    (memLp_two_iff_integrable_sq huv.aestronglyMeasurable).mp huv
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun τ => by positivity) hi
  refine Filter.Eventually.of_forall fun τ => ?_
  have h0 := norm_nonneg (F τ)
  have h1 := hle τ
  rw [Real.norm_eq_abs] at h1
  simp only
  nlinarith [abs_nonneg ((u + v) τ), sq_abs ((u + v) τ)]

/-- The norm of s = -1/2 + iτ. -/
theorem norm_line (τ : ℝ) : ‖(-1 / 2 : ℂ) + τ * I‖ = Real.sqrt (1 / 4 + τ ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp; ring

/-- P0014 pages 34 and 35, display 4.12 and the integral after it: hL and hbudget of
`Energy669.vertical_integral_bound_of_log_energy`, for primitive χ. -/
theorem log_energy {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    MemLp (fun τ : ℝ =>
      (deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
        DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I)) /
          (-1 / 2 + τ * Complex.I)) 2 ∧
    Real.sqrt (∫ τ : ℝ,
      ‖(deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
        DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I)) /
          (-1 / 2 + τ * Complex.I)‖ ^ 2) ≤ Real.sqrt (2 * π) * (Real.log q + 6.01) := by
  set K : ℝ := 4.1396 + Real.log π with hK
  set u : ℝ → ℝ := fun τ => Real.log q / Real.sqrt (1 / 4 + τ ^ 2) with hu
  set v : ℝ → ℝ := fun τ => ((1 / 2) * Real.log (τ ^ 2 + 9 / 4) + K) /
    Real.sqrt (1 / 4 + τ ^ 2) with hv
  obtain ⟨hu2, hv2⟩ := memLp_split (Real.log q) K
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlpi : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hcont := logDeriv_line_continuous hχ
  have hmeas : AEStronglyMeasurable (fun τ : ℝ =>
      (deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
        DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I)) /
          (-1 / 2 + τ * Complex.I)) volume := by
    refine (hcont.div (by fun_prop) ?_).aestronglyMeasurable
    intro τ h
    have := congrArg Complex.re h
    simp at this
  have hpt : ∀ τ : ℝ, ‖(deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
        DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I)) /
          (-1 / 2 + τ * Complex.I)‖ ≤ u τ + v τ := by
    intro τ
    have hP := Prep1121VIPointwise.pointwise_4_12 hχ τ
    have habs : |Real.log (q / π)| ≤ Real.log q + Real.log π := by
      rw [Real.log_div (by positivity) (by positivity)]
      rw [abs_le]; constructor <;> linarith
    have hs : 0 < Real.sqrt (1 / 4 + τ ^ 2) := Real.sqrt_pos.mpr (by positivity)
    rw [norm_div, norm_line, hu, hv, ← add_div]
    apply div_le_div_of_nonneg_right _ hs.le
    rw [hK]; linarith
  obtain ⟨hL, hB⟩ := l2_triangle _ u v hmeas hu2 hv2 hpt
  refine ⟨hL, hB.trans ?_⟩
  have hw := Prep1121VIIntegral.integral_weight
  have hsq : ∀ τ : ℝ, Real.sqrt (1 / 4 + τ ^ 2) ^ 2 = 1 / 4 + τ ^ 2 := fun τ =>
    Real.sq_sqrt (by positivity)
  have hU : ∫ τ, u τ ^ 2 = Real.log q ^ 2 * (2 * π) := by
    simp only [hu, div_pow, hsq]
    rw [← hw, ← integral_const_mul]
    congr 1; funext τ; ring
  have hV : ∫ τ, v τ ^ 2 = ∫ τ : ℝ, ((1 / 2) * Real.log (τ ^ 2 + 9 / 4) + (4.1396 + Real.log π)) ^ 2 /
        (1 / 4 + τ ^ 2) := by
    simp only [hv, div_pow, hsq, hK]
  have hI := Prep1121VIIntegral.certified_integral
  rw [hU, hV]
  have h1 : Real.sqrt (Real.log q ^ 2 * (2 * π)) = Real.log q * Real.sqrt (2 * π) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hlq]
  have h2 : Real.sqrt (∫ τ : ℝ, ((1 / 2) * Real.log (τ ^ 2 + 9 / 4) + (4.1396 + Real.log π)) ^ 2 /
        (1 / 4 + τ ^ 2)) ≤ Real.sqrt (2 * π) * 6.01 := by
    calc _ ≤ Real.sqrt (2 * π * 6.01 ^ 2) := Real.sqrt_le_sqrt hI
      _ = Real.sqrt (2 * π) * 6.01 := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [h1]
  nlinarith [h2]

/-- P0014 Lemma 4.1, pages 34 and 35, displays 4.10 to 4.15: the exact statement of
`MainLemma41Split123.vertical_integral_bound`, proved from the leaves of the six
Prep1121VI files through `Energy669.vertical_integral_bound_of_log_energy`. -/
theorem vertical_integral_bound_of_leaves (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ : ℝ) :
    (2 * π)⁻¹ * ∫ τ : ℝ,
        ‖deriv (DirichletCharacter.LFunction χ) (-1 / 2 + τ * Complex.I) /
            DirichletCharacter.LFunction χ (-1 / 2 + τ * Complex.I) *
          MainLemma41Split123.contMellin δ (-1 / 2 + τ * Complex.I)‖ ≤
      (Real.log q + 6.01) * (Real.sqrt (Real.sqrt π / 4) + 2 * π * |δ| *
        Real.sqrt LeanLab.HelfgottMajor.Sec45.nTwo) := by
  obtain ⟨hL, hB⟩ := log_energy hχ
  exact Energy669.vertical_integral_bound_of_log_energy q χ δ hL hB

end LeanLab.HelfgottMajor.Prep1121VIBudget
