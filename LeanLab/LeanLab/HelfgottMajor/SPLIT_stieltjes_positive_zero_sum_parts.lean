import LeanLab.HelfgottMajor.Decomp431a
import LeanLab.HelfgottMajor.Continuation457

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

/-- Helper, proved: a function with a derivative continuous on `uIcc a b` is absolutely continuous there. -/
theorem stparts_ac_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} {a b : ℝ} (hf : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x)
    (hc : ContinuousOn f' (Set.uIcc a b)) : AbsolutelyContinuousOnInterval f a b := by
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hc
  have hL : LipschitzOnWith C.toNNReal f (Set.uIcc a b) :=
    (convex_uIcc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (hf x hx).hasDerivWithinAt) (fun x hx => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
        exact (hC x hx).trans (le_max_left _ _))
  exact hL.absolutelyContinuousOnInterval

/-- Helper, proved: the norm of the Gaussian Mellin transform on the critical line is absolutely continuous
on `[1, T]`. -/
theorem stparts_norm_gaussianMellin_ac (δ T : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) 1 T := by
  set U : Set ℂ := {s : ℂ | 0 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hD : DifferentiableOn ℂ (gaussianMellin δ) U := fun s hs =>
    (Continuation457.gaussian_mellin_differentiable δ s hs).differentiableWithinAt
  have hA : AnalyticOnNhd ℂ (gaussianMellin δ) U := hD.analyticOnNhd hU
  have hdc : ContinuousOn (deriv (gaussianMellin δ)) U := hA.deriv.continuousOn
  have hmem : ∀ u : ℝ, (1 / 2 : ℂ) + (u : ℂ) * Complex.I ∈ U := by
    intro u; simp [U]
  have hφ : ∀ u : ℝ, HasDerivAt (fun u : ℝ => gaussianMellin δ ((1 / 2 : ℂ) + (u : ℂ) * Complex.I))
      (deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (u : ℂ) * Complex.I) * Complex.I) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => (1 / 2 : ℂ) + (u : ℂ) * Complex.I) Complex.I u := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := u)).mul_const Complex.I).const_add (1 / 2 : ℂ)
    have h2 := (Continuation457.gaussian_mellin_differentiable δ _ (hmem u)).hasDerivAt
    exact h2.comp u h1
  have hφac : AbsolutelyContinuousOnInterval
      (fun u : ℝ => gaussianMellin δ ((1 / 2 : ℂ) + (u : ℂ) * Complex.I)) 1 T := by
    refine stparts_ac_of_hasDerivAt (fun x _ => hφ x) ?_
    refine ContinuousOn.mul ?_ continuousOn_const
    refine hdc.comp (Continuous.continuousOn (by fun_prop)) (fun u _ => hmem u)
  exact lipschitzWith_one_norm.comp_absolutelyContinuousOnInterval hφac

/-- Helper, proved: the main term `M t = t / (2 π) * log (q t / (2 π e))` has derivative
`(1 / 2 π) log (q t / 2 π)` for `t > 0`. -/
theorem stparts_hasDerivAt_main (q : ℕ) [NeZero q] (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1)))
      ((1 / (2 * π)) * log ((q : ℝ) * t / (2 * π))) t := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hpos : (q : ℝ) * t / (2 * π * exp 1) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => (q : ℝ) * t / (2 * π * exp 1))
      ((q : ℝ) / (2 * π * exp 1)) t := by
    simpa using ((hasDerivAt_id t).const_mul (q : ℝ)).div_const (2 * π * exp 1)
  have h2 := h1.log hpos
  have h3 := ((hasDerivAt_id t).div_const (2 * π)).mul h2
  convert h3 using 1
  · funext x; simp
  have hl : log ((q : ℝ) * t / (2 * π * exp 1)) = log ((q : ℝ) * t / (2 * π)) - 1 := by
    rw [show (q : ℝ) * t / (2 * π * exp 1) = (q : ℝ) * t / (2 * π) / exp 1 by
      field_simp, Real.log_div (by positivity) (by positivity), Real.log_exp]
  rw [hl]
  simp only [id]
  field_simp
  ring

/-- Helper, proved: the zero count `N t` with `0 < im ≤ t` is monotone in `t`, because each such zero set is
finite. -/
theorem stparts_zeroCount_monotone (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) :
    Monotone (fun t : ℝ => ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) := by
  set w : ℂ → ℝ := fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
  set S : ℝ → Set ℂ := fun t => {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t}
  have key : ∀ t, (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) =
      ∑' ρ : ℂ, (S t).indicator w ρ := fun t => tsum_subtype (S t) w
  have hfin : ∀ t, (S t).Finite := fun t =>
    (ZeroCount1623.stripZeros_finite χ t).subset (fun ρ hρ => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hρ
      exact ⟨h1, h2, h3, by rw [abs_of_pos h4]; exact h5⟩)
  have hsum : ∀ t, Summable ((S t).indicator w) := fun t =>
    summable_of_ne_finset_zero (s := (hfin t).toFinset)
      (fun b hb => Set.indicator_of_notMem (by simpa using hb) _)
  intro s t hst
  simp only [key]
  refine Summable.tsum_le_tsum (fun ρ => ?_) (hsum s) (hsum t)
  refine Set.indicator_le_indicator_of_subset (fun ρ hρ => ?_) (fun ρ => ?_) ρ
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hρ
    exact ⟨h1, h2, h3, h4, h5.trans hst⟩
  · exact Nat.cast_nonneg _

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
  exact (stparts_norm_gaussianMellin_ac δ T).integral_deriv_eq_sub

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
  set G : ℝ → ℝ := fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖ with hG
  set M : ℝ → ℝ := fun t : ℝ => t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1)) with hMdef
  have hpos : ∀ x ∈ Set.uIcc (1 : ℝ) T, 0 < x := by
    intro x hx; rw [Set.uIcc_of_le hT] at hx; linarith [hx.1]
  have hM : AbsolutelyContinuousOnInterval M 1 T := by
    refine stparts_ac_of_hasDerivAt (fun x hx => stparts_hasDerivAt_main q x (hpos x hx)) ?_
    have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.log (by fun_prop) (fun x hx => ?_)
    have := hpos x hx; positivity
  have hGac := stparts_norm_gaussianMellin_ac δ T
  have hibp := hM.integral_mul_deriv_eq_deriv_mul hGac
  have e1 : (∫ t in (1 : ℝ)..T, deriv G t * M t) = ∫ t in (1 : ℝ)..T, M t * deriv G t := by
    congr 1; ext t; ring
  have e2 : (∫ t in (1 : ℝ)..T, deriv M t * G t) =
      (1 / (2 * π)) * ∫ t in (1 : ℝ)..T, G t * log ((q : ℝ) * t / (2 * π)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [(stparts_hasDerivAt_main q x (hpos x hx)).deriv]
    ring
  change (∫ t in (1 : ℝ)..T, deriv G t * M t) = G T * M T - G 1 * M 1 -
    (1 / (2 * π)) * ∫ t in (1 : ℝ)..T, G t * log ((q : ℝ) * t / (2 * π))
  rw [e1, hibp, e2]
  ring

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
  have hd := (stparts_norm_gaussianMellin_ac δ T).intervalIntegrable_deriv
  refine ⟨?_, hd, ?_⟩
  · set N := fun t : ℝ => ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) with hN
    have hmono : Monotone N := stparts_zeroCount_monotone q χ
    have hN0 : ∀ t, 0 ≤ N t := fun t => tsum_nonneg (fun _ => Nat.cast_nonneg _)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT] at hd ⊢
    exact MeasureTheory.Integrable.mul_bdd (c := N T) hd
      hmono.measurable.aestronglyMeasurable
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => by
        rw [Real.norm_of_nonneg (hN0 x)]; exact hmono hx.2)
  · refine hd.mul_continuousOn ?_
    have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    refine ContinuousOn.mul (by fun_prop) (ContinuousOn.log (by fun_prop) (fun x hx => ?_))
    rw [Set.uIcc_of_le hT] at hx
    have : 0 < x := by linarith [hx.1]
    positivity

end LeanLab.HelfgottMajor.Decomp431a
