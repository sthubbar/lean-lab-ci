import LeanLab.HelfgottMajor.Decomp431a

/-!
Split of the LEAF `stieltjes_positive_zero_sum` in
`LeanLab.HelfgottMajor.SPLIT_positive_mass_norm_sum_integral_stieltjes`, following the proof of
book Lemma 16.9, displays 16.20 and 16.21 on book pages 431 and 432 of P0014 Part IV, as applied
in the proof of Lemma 16.10 on book page 433 with `y = 1` and `f t = |G_δ (1/2 + i t)|`.

Notation in the doc comments: `G t` is the norm of `gaussianMellin δ` at `1/2 + i t`, `N t` the
multiplicity weighted count of zeros with `0 < re < 1` and `0 < im ≤ t`, and
`M t = t / (2 π) * log (q t / (2 π e))`.  The leaves are the Stieltjes integration by parts
against `dN`, the fundamental theorem of calculus for `G`, the integration by parts against `dM`,
and the integrability facts that let the integral of `G' * (N + c - M)` be split linearly.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF: proof of book Lemma 16.9, page 431, the first integration by parts
`∑_{1 < γ ≤ T} f(γ) = ∫_{1+}^{T} f dN = f(T) N(T) - f(1) N(1) - ∫_1^T f'(t) N(t) dt` for
`f t = G t`, the norm of `G_δ (1/2 + i t)` as in the proof of Lemma 16.10, page 433.  Under
`hzeros` each summand `‖mellinMassTerm χ δ ρ‖` is the multiplicity of `ρ` times `G (im ρ)`.
`G` is Lipschitz on `[1, T]`, so it is absolutely continuous there.  Class HARD. -/
theorem stieltjes_sum_by_parts_N (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) =
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℝ) * Complex.I)‖ *
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T},
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) -
      ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)‖ *
        (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ (1 : ℝ)},
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) -
      ∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) := by
  sorry

/-- LEAF: proof of book Lemma 16.9, page 431, the fact used to absorb the constant shift `c`:
`∫_1^T f'(t) dt = f(T) - f(1)` for `f t = G t`, the norm of `G_δ (1/2 + i t)`, which is
Lipschitz on `[1, T]` as the norm of a function holomorphic near the segment.  Class MEDIUM. -/
theorem norm_gaussianMellin_ftc (δ T : ℝ) (hT : 1 ≤ T) :
    (∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t) =
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℝ) * Complex.I)‖ -
        ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)‖ := by
  sorry

/-- LEAF: proof of book Lemma 16.9, page 431, the second integration by parts
`∫_1^T f'(t) M(t) dt = f(T) M(T) - f(1) M(1) - ∫_1^T f(t) M'(t) dt` with
`M'(t) = (1 / 2 π) log (q t / 2 π)`, for `f t = G t`.  Class MEDIUM. -/
theorem main_term_by_parts (q : ℕ) [NeZero q] (δ T : ℝ) (hT : 1 ≤ T) :
    (∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          (t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1)))) =
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℝ) * Complex.I)‖ *
          (T / (2 * π) * log ((q : ℝ) * T / (2 * π * exp 1))) -
        ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)‖ *
          ((1 : ℝ) / (2 * π) * log ((q : ℝ) * (1 : ℝ) / (2 * π * exp 1))) -
        (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
          ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
            log ((q : ℝ) * t / (2 * π))) := by
  sorry

/-- LEAF: regularity in the proof of book Lemma 16.9, page 431: on `[1, T]` the functions
`f' N`, `f'` and `f' M` are integrable, for `f t = G t` Lipschitz and `N` monotone and bounded,
so the integral of `f' (N + c - M)` splits linearly.  Class MEDIUM. -/
theorem stieltjes_integrability (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) (hT : 1 ≤ T) :
    IntervalIntegrable (fun t : ℝ =>
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)))
        MeasureTheory.volume 1 T ∧
      IntervalIntegrable (fun t : ℝ =>
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t)
        MeasureTheory.volume 1 T ∧
      IntervalIntegrable (fun t : ℝ =>
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          (t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1))))
        MeasureTheory.volume 1 T := by
  sorry

end LeanLab.HelfgottMajor.Decomp431a
