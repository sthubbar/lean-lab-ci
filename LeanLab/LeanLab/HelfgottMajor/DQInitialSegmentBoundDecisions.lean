/-
CITED WALL, step initial_segment_bound of Decomp639Contour, session CLOUD-cited-initial_segment_bound,
2026-11-20. P0014, Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4,
pages 24 and 25, displays 3.58 to 3.63, and Appendix page 67, display A.33.

DECISION. The leaf `Decomp639Contour.initial_segment_bound` rests on two different inputs.
1. Display A.33 on page 67 is a computer check, the bisection method on [0.1, 25] with
   24 iterations, plus hand bounds for small and large rho. It becomes the named hypothesis
   `HelfgottA33` below. A float scan of 400001 points on [1e-6, 1e6] gives the maxima
   0.0763896 near rho = 3.60 and 0.49929 at rho = 1e6, in line with the paper.
2. The rest is the integration by parts of pages 24 and 25 on the segment C1. It stays one
   LEAF, `initial_ibp_bound`, stated with the exact exponent l r / sqrt 2 of display 3.60.
The two consequences of A.33 used on page 24, the phase cost and display 3.61, are proved
here from the hypothesis, and `initial_segment_bound_of_A33` assembles the leaf statement
from the hypothesis and the new LEAF with no sorry.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottMajor.Decomp639Contour

namespace LeanLab.HelfgottMajor.DQInitialSegmentBound

open Real MeasureTheory Set LeanLab.HelfgottMajor.Decomp511a
  LeanLab.HelfgottMajor.Decomp639Contour

/-- NAMED HYPOTHESIS, cited computation. P0014 page 67, display A.33, both lines:
`max_{ρ ≥ 0} (c0 - 1/√2)/(√2 c1 ρ) ≤ 0.0763896` and `sup_{ρ ≥ 0} (c0 - 1/√2)/(c1 √ρ) ≤ 1/2`,
obtained there by the bisection method on [0.1, 25] together with hand bounds for
rho at most 0.1 and at least 25. Stated for positive rho, the only range used. -/
def HelfgottA33 : Prop :=
  ∀ ρ : ℝ, 0 < ρ →
    (c0 ρ - 1 / sqrt 2) / (sqrt 2 * c1 ρ * ρ) ≤ 0.0763896 ∧
    (c0 ρ - 1 / sqrt 2) / (c1 ρ * sqrt ρ) ≤ 1 / 2

/-- P0014 page 24, the display after 3.60: by A.33, `ℓ r₋ / √2 ≤ 0.07639 ℓ² ρ`, and
`ℓ² ρ = 4 |τ|`, so the phase cost is at most `0.30556 |τ|`. CONDITIONAL ON `HelfgottA33`. -/
theorem initialRadius_phase_of_A33 (hA : HelfgottA33) (δ τ : ℝ) (hδ : δ ≠ 0)
    (hτ : 0 < |τ|) :
    ell δ * initialRadius δ τ / sqrt 2 ≤ 0.30556 * |τ| := by
  have hρ := rho_pos δ τ hδ hτ
  have hc := c1_pos _ hρ
  have hL := ell_pos δ hδ
  have hs : 0 < sqrt (2:ℝ) := by positivity
  have hs2 : sqrt (2:ℝ) * sqrt 2 = 2 := mul_self_sqrt (by norm_num)
  have hX := (hA _ hρ).1
  rw [div_le_iff₀ (by positivity)] at hX
  have he := ell_sq_mul_rho δ τ hδ
  have hkey : ell δ * initialRadius δ τ / sqrt 2 =
      ell δ ^ 2 * (c0 (rho δ τ) - 1 / sqrt 2) / (c1 (rho δ τ) * sqrt 2) := by
    unfold initialRadius
    field_simp
  have hb : ell δ ^ 2 * (c0 (rho δ τ) - 1 / sqrt 2) / (c1 (rho δ τ) * sqrt 2) ≤
      ell δ ^ 2 * (0.0763896 * (sqrt 2 * c1 (rho δ τ) * rho δ τ)) /
        (c1 (rho δ τ) * sqrt 2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hX (by positivity)
  have hc2 : ell δ ^ 2 * (0.0763896 * (sqrt 2 * c1 (rho δ τ) * rho δ τ)) /
        (c1 (rho δ τ) * sqrt 2) = 0.0763896 * (ell δ ^ 2 * rho δ τ) := by
    field_simp
  rw [hkey]
  calc _ ≤ _ := hb
    _ = _ := hc2
    _ ≤ _ := by rw [he]; nlinarith

/-- P0014 page 24, display 3.61: `r₋ ≤ √ρ ℓ / 2 ≤ √τ`, from 3.58 and the second line of A.33.
CONDITIONAL ON `HelfgottA33`. -/
theorem initialRadius_le_sqrt_of_A33 (hA : HelfgottA33) (δ τ : ℝ) (hδ : δ ≠ 0)
    (hτ : 0 < |τ|) :
    initialRadius δ τ ≤ sqrt |τ| := by
  have hρ := rho_pos δ τ hδ hτ
  have hc := c1_pos _ hρ
  have hL := ell_pos δ hδ
  have hsr : 0 < sqrt (rho δ τ) := sqrt_pos.mpr hρ
  have hX := (hA _ hρ).2
  rw [div_le_iff₀ (by positivity)] at hX
  have hm := ell_mul_sqrt_rho δ τ hδ
  have hkey : initialRadius δ τ = ell δ / c1 (rho δ τ) * (c0 (rho δ τ) - 1 / sqrt 2) := rfl
  rw [hkey]
  calc _ ≤ ell δ / c1 (rho δ τ) * (1 / 2 * (c1 (rho δ τ) * sqrt (rho δ τ))) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = ell δ * sqrt (rho δ τ) / 2 := by field_simp
    _ = _ := by rw [hm]; ring

/-- LEAF: P0014 pages 24 and 25, displays 3.59, 3.60 and 3.63 with the bounds after 3.63.
Integration by parts on C1 from 0 to `w r₋`: the boundary term is at most
`r₋^σ / τ · e^{ℓ r₋ / √2 - π τ / 4}`, and the two integrals of display 3.63 are at most
`(r₋^{σ+2} + √2 r₋^σ) / τ · e^{ℓ r₋ / √2 - π τ / 4}` by `|s| ≥ τ` and
`∫_0^{r₋} e^{ℓ t / √2} dt ≤ min(√2 / ℓ, r₋) e^{ℓ r₋ / √2}`.
The exponent keeps the `√2` of display 3.60; the printed `ℓ r₋ / 2` on page 25 is a typo
that the paper's final line does not use. -/
theorem initial_ibp_bound (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖initialIntegral δ s‖ ≤
      (initialRadius δ s.im ^ (s.re + 2) + (1 + sqrt 2) * initialRadius δ s.im ^ s.re) /
        |s.im| * exp (ell δ * initialRadius δ s.im / sqrt 2 - π / 4 * |s.im|) := by
  sorry

/-- P0014 page 25, the conclusion after display 3.63, assembled with no sorry from the
named hypothesis A.33 and the LEAF `initial_ibp_bound`. The statement after the hypothesis
is word for word that of `Decomp639Contour.initial_segment_bound`.
CONDITIONAL ON `HelfgottA33` and on the LEAF `initial_ibp_bound`. -/
theorem initial_segment_bound_of_A33 (hA : HelfgottA33) (δ : ℝ) (s : ℂ)
    (hσ0 : 0 < s.re) (hσ1 : s.re ≤ 1) (ht : 100 ≤ |s.im|)
    (hsign : δ * s.im < 0) :
    ‖initialIntegral δ s‖ ≤ firstCoefficient s.re |s.im| *
      exp (-0.4798 * |s.im|) := by
  have hd : δ ≠ 0 := by intro h; simp [h] at hsign
  have hτ : 0 < |s.im| := by linarith
  have hr := initialRadius_pos δ s.im hd hτ
  have hphase := initialRadius_phase_of_A33 hA δ s.im hd hτ
  have hrad := initialRadius_le_sqrt_of_A33 hA δ s.im hd hτ
  have hpre := initial_radius_prefactor s.re |s.im| (initialRadius δ s.im) hσ0.le hτ hr hrad
  have hexp := initial_phase_cost |s.im| (ell δ) (initialRadius δ s.im) (abs_nonneg _) hphase
  have hpre0 : 0 ≤ (initialRadius δ s.im ^ (s.re + 2) +
      (1 + sqrt 2) * initialRadius δ s.im ^ s.re) / |s.im| := by positivity
  have hF0 : 0 ≤ firstCoefficient s.re |s.im| := by
    unfold firstCoefficient; positivity
  calc _ ≤ _ := initial_ibp_bound δ s hσ0 hσ1 ht hsign
    _ ≤ _ := mul_le_mul hpre hexp (exp_pos _).le hF0

/-- Twin check: the conditional assembly has exactly the type of the sealed leaf
`Decomp639Contour.initial_segment_bound` once the hypothesis is supplied. -/
theorem initial_segment_bound_twin (hA : HelfgottA33) :
    type_of% @Decomp639Contour.initial_segment_bound :=
  initial_segment_bound_of_A33 hA

end LeanLab.HelfgottMajor.DQInitialSegmentBound
