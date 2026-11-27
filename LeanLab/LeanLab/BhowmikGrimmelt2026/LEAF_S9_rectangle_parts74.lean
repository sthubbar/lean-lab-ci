/-
Two pieces of the corrected contour step `leaf_contour_rectangle74`, P0029 page 27,
display 7.12: the residue theorem on the rectangle with the right edge truncated at
height `T`, and the split of the full line `re s = 2` into the window `|t| ≤ T` and
its complement.  With the proved right line formula `arithmetic_right_line469` they give
`leaf_contour_rectangle74`.  The split is PROVED here; the residue identity stays a
LEAF.

AI wrote the Lean code.  Binary Goldbach is OPEN.
-/
import LeanLab.BhowmikGrimmelt2026.SPLIT_lemma74

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-- LEAF: P0029 page 27, display 7.12, the residue theorem on the rectangle. Class HARD.

With the same hypotheses as `leaf_contour_rectangle74`, the right edge `re s = 2`,
`|Im s| ≤ T`, divided by `2 π i`, equals the residues inside, the pole term at `s = 1`
minus the zeros with analytic multiplicity times the Mellin transform, plus the left
edge, plus `1 / (2 π i)` times the top edge minus the bottom edge, all for the function
`-L'/L(s) * mellinR Ψ s`.  This is Cauchy's residue theorem for a counterclockwise
rectangle; the residues are the proved local results `weighted_pole_residue469` and
`weighted_zero_residue469`. -/
theorem leaf_rectangle_residue74 (B T : ℝ) (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r)
    (S : ℝ) (Ψ : ℝ → ℝ) (hB : 0 < B) (hT : 0 < T)
    (hS : 1 ≤ S) (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hcs : HasCompactSupport Ψ) (hsupp : tsupport Ψ ⊆ Set.Ioi S)
    (hχ : χ.IsPrimitive)
    (hvert : ∀ t : ℝ, |t| ≤ T →
      DirichletCharacter.LFunction χ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hhor : ∀ σ : ℝ, -B ≤ σ → σ ≤ 2 →
      DirichletCharacter.LFunction χ ((σ : ℂ) + (T : ℂ) * Complex.I) ≠ 0 ∧
      DirichletCharacter.LFunction χ ((σ : ℂ) - (T : ℂ) * Complex.I) ≠ 0) :
    (1 / (2 * Real.pi)) * (∫ t in (-T)..T,
        (-(logDeriv (DirichletCharacter.LFunction χ))) (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          mellinR Ψ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
    (if χ = 1 then ∫ t in Set.Ioi (0 : ℝ), (Ψ t : ℂ) else 0) -
      (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ -B < ρ.re ∧ |ρ.im| ≤ T},
        (mult χ ρ : ℂ) * mellinR Ψ ρ) +
    ((1 / (2 * Real.pi)) * (∫ t in (-T)..T,
        (-(logDeriv (DirichletCharacter.LFunction χ))) (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          mellinR Ψ (((-B : ℝ) : ℂ) + (t : ℂ) * Complex.I)) +
      (1 / (2 * Real.pi * Complex.I)) * (∫ σ in (-B)..(2 : ℝ),
        ((-(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) + (T : ℂ) * Complex.I) *
            mellinR Ψ ((σ : ℂ) + (T : ℂ) * Complex.I) -
          (-(logDeriv (DirichletCharacter.LFunction χ))) ((σ : ℂ) - (T : ℂ) * Complex.I) *
            mellinR Ψ ((σ : ℂ) - (T : ℂ) * Complex.I)))) := by
  sorry

/-- On the line `re s = 2` the logarithmic derivative of a Dirichlet L-function is bounded
by the convergent series of `Λ(n) / n ^ 2`. Standard, used for display 7.12, P0029 page 27. -/
theorem logDeriv_right_bound74 (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) :
    ∃ K : ℝ, ∀ t : ℝ, ‖-(logDeriv (DirichletCharacter.LFunction χ)
        (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ ≤ K := by
  have hsum : Summable (fun n => ‖LSeries.term (fun n => (vonMangoldt n : ℂ)) 2 n‖) :=
    summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := 2) (by norm_num))
  refine ⟨∑' n, ‖LSeries.term (fun n => (vonMangoldt n : ℂ)) 2 n‖, fun t => ?_⟩
  have hs : 1 < (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re := by simp
  rw [← logDeriv_dirichlet_series469 r χ _ hs]
  apply tsum_of_norm_bounded hsum.hasSum
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [LSeries.term_of_ne_zero hn.ne', norm_div, norm_div, norm_mul,
      Complex.norm_natCast_cpow_of_pos hn, Complex.norm_natCast_cpow_of_pos hn]
    have hχ : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
    have hre : (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = (2 : ℂ).re := by simp
    rw [hre]
    have hpos : 0 < (n : ℝ) ^ (2 : ℂ).re := by positivity
    gcongr
    calc ‖(vonMangoldt n : ℂ)‖ * ‖χ n‖ ≤ ‖(vonMangoldt n : ℂ)‖ * 1 :=
          mul_le_mul_of_nonneg_left hχ (norm_nonneg _)
      _ = _ := mul_one _


/-- P0029 page 27, display 7.12, the split of the line `re s = 2` at height `T`.

The function `-L'/L(2 + it) * mellinR Ψ (2 + it)` is integrable on the real line,
because `-L'/L` is bounded there by `logDeriv_right_bound74` and the Mellin transform of a
smooth compactly supported kernel is integrable on vertical lines,
`mellinR_vertical_integrable469`; so its integral over the line is the integral over
`[-T, T]` plus the integral over `|t| > T`. PROVED. -/
theorem leaf_right_line_split74 (T : ℝ) (hT : 0 < T) (r : ℕ) [NeZero r]
    (χ : DirichletCharacter ℂ r)
    (S : ℝ) (Ψ : ℝ → ℝ) (hS : 1 ≤ S) (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ)
    (hcs : HasCompactSupport Ψ) (hsupp : tsupport Ψ ⊆ Set.Ioi S) :
    (∫ t : ℝ, -(logDeriv (DirichletCharacter.LFunction χ)
        (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
        mellinR Ψ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ t in (-T)..T,
        (-(logDeriv (DirichletCharacter.LFunction χ))) (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          mellinR Ψ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) +
      (∫ t in {t : ℝ | T < |t|},
        (-(logDeriv (DirichletCharacter.LFunction χ))) (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) *
          mellinR Ψ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) := by
  have hS0 : 0 < S := by linarith
  have hL : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
    intro z hz
    exact (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl (by simpa using hz))).differentiableWithinAt
  have hline : Continuous (fun t : ℝ => ((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  have hmaps : ∀ t : ℝ, ((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I ∈ ({1}ᶜ : Set ℂ) := by
    intro t h
    have := congrArg Complex.re (Set.mem_singleton_iff.mp h)
    simp at this
  have hne : ∀ t : ℝ, DirichletCharacter.LFunction χ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (hmaps t)) (by simp)
  have hg : Continuous (fun t : ℝ => -(logDeriv (DirichletCharacter.LFunction χ)
      (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I))) := by
    have h1 : Continuous (fun t : ℝ => deriv (DirichletCharacter.LFunction χ)
        (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
      hL.deriv.continuousOn.comp_continuous hline hmaps
    have h2 : Continuous (fun t : ℝ => DirichletCharacter.LFunction χ
        (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
      hL.continuousOn.comp_continuous hline hmaps
    simp only [logDeriv_apply]
    exact (h1.div h2 hne).neg
  obtain ⟨K, hK⟩ := logDeriv_right_bound74 r χ
  have hm : Integrable (fun t : ℝ => mellinR Ψ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
    mellinR_vertical_integrable469 Ψ S hS0 hsm hcs hsupp 2
  have hF : Integrable (fun t : ℝ => -(logDeriv (DirichletCharacter.LFunction χ)
      (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) *
      mellinR Ψ (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
    hm.bdd_mul hg.aestronglyMeasurable (Filter.Eventually.of_forall hK)
  have hset : ({t : ℝ | T < |t|} : Set ℝ) = (Set.Icc (-T) T)ᶜ := by
    ext t
    rw [Set.mem_compl_iff, Set.mem_Icc, ← abs_le, not_le]
    rfl
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc, hset]
  simp only [Pi.neg_apply]
  exact (integral_add_compl measurableSet_Icc hF).symm

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.logDeriv_right_bound74
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_right_line_split74
