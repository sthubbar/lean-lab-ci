/-
P0068 Zhan 1991, the LEAF `byParts_leaf_ps` of PartialSum1122d.lean, page 264 the display after
"Hence", step S2 first half, split into two cited LEAF steps: the derivative of the line integral
`Vline` in `u`, and the continuity of that derivative. The integration by parts itself, with
`Vline(N - A) = 0`, is PROVED here from the two LEAFs as `byParts_of_leaves_bp`.
AI-written Lean code, Claude, unit S8-30 of burst-20261124. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.PartialSum1122d

namespace LeanLab.Zhan1991
open Finset Real

noncomputable section

/-- LEAF: page 264, the display after "The inner integral above can be estimated by Lemma 1":
differentiation of `Vline` under the integral sign in `u > 0`,
`∂_u (1/2π) ∫ F(s) (u^s - (N-A)^s) s⁻¹ dt = (1/2π) ∫ F(s) u^{s-1} dt` on `Re s = 1/2`, `|t| ≤ T`.
Class MEDIUM. -/
theorem vline_hasDeriv_leaf_bp {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) (N : ℕ)
    (A T u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun v => Vline_ps Nv χ N A (1 / 2) T v)
      ((1 / (2 * π) : ℂ) * ∫ t in (-T)..T, Fprod Nv χ (((1 / 2 : ℝ) : ℂ) + t * Complex.I) *
        (u : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * Complex.I - 1)) u := by
  sorry

/-- LEAF: page 264, the same display: the derivative `(1/2π) ∫_{-T}^{T} F(1/2+it) u^{-1/2+it} dt`
is continuous in `u > 0`, the integrand being continuous in `(t, u)` on the compact range of `t`.
Class EASY. -/
theorem vline_deriv_continuous_leaf_bp {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q)
    (T : ℝ) :
    ContinuousOn (fun u : ℝ => (1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
        Fprod Nv χ (((1 / 2 : ℝ) : ℂ) + t * Complex.I) *
          (u : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * Complex.I - 1)) (Set.Ioi 0) := by
  sorry

theorem hasDerivAt_ee_lin_bp (lam t : ℝ) :
    HasDerivAt (fun u : ℝ => ee (lam * u)) (2 * π * Complex.I * lam * ee (lam * t)) t := by
  have h1 : HasDerivAt (fun u : ℝ => ((lam * u : ℝ) : ℂ)) (lam : ℂ) t := by
    have := ((hasDerivAt_id t).const_mul lam).ofReal_comp
    simpa using this
  have h2 := (h1.const_mul (2 * π * Complex.I)).cexp
  unfold ee
  convert h2 using 1
  ring

/-- PROVED from the two LEAFs: `ByParts_ps`, integration by parts on `[N - A, N]` with
`Vline(N - A) = 0`, page 264. -/
theorem byParts_of_leaves_bp : ByParts_ps := by
  refine ⟨2, ?_⟩
  intro N A lam T q χ Nv hN hA1 hA2 hT
  have hN2 : (2 : ℝ) ≤ N := hN
  have hAN : A < N := by
    refine lt_of_le_of_lt hA2 ?_
    have := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < N by linarith)
      (show (2 / 3 : ℝ) < 1 by norm_num)
    rwa [Real.rpow_one] at this
  have ha : 0 < (N : ℝ) - A := by linarith
  have hab : (N : ℝ) - A ≤ N := by linarith
  set V : ℝ → ℂ := fun v => Vline_ps Nv χ N A (1 / 2) T v with hV
  set D : ℝ → ℂ := fun u => (1 / (2 * π) : ℂ) * ∫ t in (-T)..T,
    Fprod Nv χ (((1 / 2 : ℝ) : ℂ) + t * Complex.I) *
      (u : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * Complex.I - 1) with hD
  set w : ℝ → ℂ := fun u => 2 * π * Complex.I * lam * ee (lam * u) with hw
  have hpos : ∀ x ∈ Set.uIcc ((N : ℝ) - A) N, 0 < x := by
    intro x hx; rw [Set.uIcc_of_le hab] at hx; linarith [hx.1]
  have hVd : ∀ x ∈ Set.uIcc ((N : ℝ) - A) N, HasDerivAt V (D x) x :=
    fun x hx => vline_hasDeriv_leaf_bp Nv χ N A T x (hpos x hx)
  have hed : ∀ x ∈ Set.uIcc ((N : ℝ) - A) N, HasDerivAt (fun u => ee (lam * u)) (w x) x :=
    fun x _ => hasDerivAt_ee_lin_bp lam x
  have hVc : ContinuousOn V (Set.uIcc ((N : ℝ) - A) N) :=
    fun x hx => (hVd x hx).continuousAt.continuousWithinAt
  have hwc : Continuous w := by simp only [hw, ee]; fun_prop
  have hDc : ContinuousOn D (Set.uIcc ((N : ℝ) - A) N) :=
    (vline_deriv_continuous_leaf_bp Nv χ T).mono (fun x hx => hpos x hx)
  have hVw : IntervalIntegrable (fun u => V u * w u) MeasureTheory.volume ((N : ℝ) - A) N :=
    (hVc.mul hwc.continuousOn).intervalIntegrable
  refine ⟨hVw, ?_⟩
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hVd hed
    hDc.intervalIntegrable hwc.continuousOn.intervalIntegrable
  have hV0 : V ((N : ℝ) - A) = 0 := by simp [hV, Vline_ps]
  have hderiv : ∫ u in ((N : ℝ) - A)..N, deriv V u * ee (lam * u)
      = ∫ u in ((N : ℝ) - A)..N, D u * ee (lam * u) :=
    intervalIntegral.integral_congr fun x hx => by simp only [(hVd x hx).deriv]
  change V N * ee (lam * N) - ∫ u in ((N : ℝ) - A)..N, V u * w u
    = ∫ u in ((N : ℝ) - A)..N, deriv V u * ee (lam * u)
  rw [hderiv, hibp, hV0]
  ring

/-- `byParts_leaf_ps` of PartialSum1122d.lean, from the two LEAFs above. -/
theorem byParts_split_bp : ByParts_ps := byParts_of_leaves_bp

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.hasDerivAt_ee_lin_bp
#print axioms LeanLab.Zhan1991.byParts_of_leaves_bp
