import LeanLab.HelfgottMajor.Decomp431a
import LeanLab.HelfgottMajor.Continuation457

/-!
Faithful Stieltjes split of `positive_mass_norm_sum_integral` in
`LeanLab.HelfgottMajor.SPLIT_positive_sampling_raw`, following the proof of book Lemma 16.9,
display 16.20 and 16.21 on book pages 431 and 432 of P0014 Part IV, as applied in the proof of
Lemma 16.10 on book pages 433 and 434 with `y = 1` and `f t = |G_δ (1/2 + i t)|` on `[1, T]`.

Notation used in the doc comments, all spelled out in the Lean statements:
* `G t` is the norm of `gaussianMellin δ` at `1/2 + i t`;
* `N t` is the multiplicity weighted count of zeros of `L(s, χ)` with `0 < re < 1` and
  `0 < im ≤ t`;
* `M t = t / (2 π) * log (q t / (2 π e))` is the main term of the zero counting function;
* `g t = 0.15 log (q t) + 3.389` is the explicit error bound of display 16.21.

The three leaves are: the integration by parts identity of the proof of Lemma 16.9, the zero
counting bound of book display 3.95 in the per sign form used through display 16.21, and the
estimate of the error integral by `∫ |f'| g`.

IMPORTANT, a QUESTION for a reviewer. Integration by parts on `[1, T]` produces a boundary
term `G T * R T` at the top height `T`, where `R = N + c - M`.  The book removes it by
truncating `f` to zero above `T0` and applying Lemma 16.9 on `[1, ∞)`; but that truncated `f` is
not continuous, Lemma 16.9 assumes continuity, and the jump at `T0` contributes
`|G_δ (1/2 + i T0)| g(T0)` to `∫ |f'| g`, which display 16.26 then drops when it replaces
`|f'|` by `|G_δ'|`.  The statement `positive_mass_norm_sum_integral` follows display 16.26 and
has no term at height `T`.  So the faithful assembly below proves the parent bound PLUS the
endpoint term `G T * g T`, and does not close the parent.  The parent is not wired.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp431a
open Real LeanLab.HelfgottArcs Decomp269a Decomp269b Decomp389b

/-- LEAF: proof of book Lemma 16.9, pages 431 and 432, the Stieltjes integration by parts
`∑_{1 < γ ≤ T} f(γ) = ∫_{1+}^{T} f dN` with `N = M + R - c`, followed by the second integration
by parts that turns `∫ f dM` into `(1 / 2 π) ∫ f(t) log (q t / 2 π) dt`, since
`M'(t) = (1 / 2 π) log (q t / 2 π)`.  Here `f t = G t = |G_δ (1/2 + i t)|` as in the proof of
Lemma 16.10, page 433, but kept continuous on `[1, T]`, so the boundary terms at `1` and at `T`
both remain.  The constant shift `c` is arbitrary because `G T - G 1 = ∫ G'`.  Under `hzeros`
every summand `‖gaussianMellin δ ρ‖` equals `G (im ρ)`.  `G` is Lipschitz on `[1, T]` as the norm
of a holomorphic function on a compact segment, so the fundamental theorem of calculus holds with
`deriv`.  Class HARD. -/
theorem stieltjes_positive_zero_sum (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T c : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) =
      (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℝ) * Complex.I)‖ *
        ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T},
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
          T / (2 * π) * log ((q : ℝ) * T / (2 * π * exp 1))) -
      ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)‖ *
        ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
            0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ (1 : ℝ)},
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
          (1 : ℝ) / (2 * π) * log ((q : ℝ) * (1 : ℝ) / (2 * π * exp 1))) -
      (∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
            t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1)))) := by
  sorry

/-- LEAF: the zero counting bound of book display 3.95, section 3.7.3.3, in the per sign form
`N(t, χ) = (t / 2 π) log (q t / 2 π e) + O*(g_χ(t))` with `g_χ(t) = 0.15 log q t + 3.389`,
display 16.21 page 431, used for every `t ≥ y = 1` in the proof of Lemma 16.9 and at `t = 1` in
the proof of Lemma 16.10, page 433.  The book's `N(t, χ)` counts zeros with `0 ≤ im ≤ t` and
gives half weight to zeros of height exactly `0` and `t`; here the count is over `0 < im ≤ t`
with full weight at `t`, so the half weight of the zeros at height `0` is the constant `c`, and
full weight at `t` follows from the half weight form by right continuity, since the bound is a
closed inequality with continuous right side.  Class HARD, a cited explicit zero counting
result. -/
theorem zero_count_error_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) :
    ∃ c : ℝ, ∀ t : ℝ, 1 ≤ t →
      |(∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
        t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1))| ≤
        0.15 * log ((q : ℝ) * t) + 3.389 := by
  sorry

/-- LEAF: the error integral step of the proof of Lemma 16.9, page 431, the bound
`∫ f'(T) (N(T, χ) - main) dT = O*(∫ |f'(T)| g_χ(T) dT)`, together with `|f'| ≤ |G_δ'|` used in
display 16.26, page 434: for `f t = |G_δ (1/2 + i t)|` one has `|f'(t)| ≤ |G_δ'(1/2 + i t)|`
wherever `f` is differentiable, and `deriv f t = 0` elsewhere.  The hypothesis is the bound of
display 3.95 on `[1, T]`.  Class MEDIUM. -/
theorem error_integral_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T c : ℝ) (hT : 1 ≤ T)
    (hR : ∀ t ∈ Set.Icc (1 : ℝ) T,
      |(∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
        t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1))| ≤
        0.15 * log ((q : ℝ) * t) + 3.389) :
    -(∫ t in (1 : ℝ)..T,
        deriv (fun u : ℝ => ‖gaussianMellin δ ((1 / 2 : ℂ) + (u : ℝ) * Complex.I)‖) t *
          ((∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
              0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ t},
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ)) + c -
            t / (2 * π) * log ((q : ℝ) * t / (2 * π * exp 1)))) ≤
      ∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389) := by
  -- AI wrote this proof.
  set F : ℂ → ℂ := gaussianMellin δ with hFdef
  set γ : ℝ → ℂ := fun u => (1 / 2 : ℂ) + (u : ℂ) * Complex.I with hγdef
  have hγre : ∀ u : ℝ, 0 < (γ u).re := by
    intro u; simp [γ]
  have hFd : ∀ u : ℝ, DifferentiableAt ℂ F (γ u) := fun u =>
    Continuation457.gaussian_mellin_differentiable δ (γ u) (hγre u)
  have hγd : ∀ u : ℝ, HasDerivAt γ Complex.I u := by
    intro u
    have h := (((hasDerivAt_id u).ofReal_comp).mul_const Complex.I).const_add (1 / 2 : ℂ)
    simpa [γ] using h
  have hg : ∀ u : ℝ, HasDerivAt (fun v => F (γ v)) (deriv F (γ u) * Complex.I) u :=
    fun u => (hFd u).hasDerivAt.comp u (hγd u)
  -- pointwise: the derivative of the norm is bounded by the norm of the derivative
  have hpt : ∀ u : ℝ, |deriv (fun v : ℝ => ‖F (γ v)‖) u| ≤ ‖deriv F (γ u)‖ := by
    intro u
    by_cases hdf : DifferentiableAt ℝ (fun v : ℝ => ‖F (γ v)‖) u
    · have h1 := hdf.hasDerivAt.tendsto_slope
      have h2 := (hg u).tendsto_slope
      have h1' := (continuous_abs.tendsto _).comp h1
      have h2' := (continuous_norm.tendsto _).comp h2
      have hle : ∀ᶠ v in nhdsWithin u {u}ᶜ,
          (fun x => |x|) (slope (fun v : ℝ => ‖F (γ v)‖) u v) ≤
            (fun x => ‖x‖) (slope (fun v => F (γ v)) u v) := by
        refine Filter.Eventually.of_forall (fun v => ?_)
        simp only [slope_def_field, slope_def_module]
        rw [abs_div, norm_smul, norm_inv, Real.norm_eq_abs, div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le _ _)
          (inv_nonneg.mpr (abs_nonneg _))
      have := le_of_tendsto_of_tendsto h1' h2' hle
      simpa [norm_mul] using this
    · rw [deriv_zero_of_not_differentiableAt hdf, abs_zero]
      exact norm_nonneg _
  have key : ∀ R : ℝ → ℝ, (∀ t ∈ Set.Icc (1 : ℝ) T,
      |R t| ≤ 0.15 * log ((q : ℝ) * t) + 3.389) →
      -(∫ t in (1 : ℝ)..T, deriv (fun u : ℝ => ‖F (γ u)‖) t * R t) ≤
        ∫ t in (1 : ℝ)..T, ‖deriv F (γ t)‖ * (0.15 * log ((q : ℝ) * t) + 3.389) := by
    intro R hR
    have hq : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hcont : ContinuousOn
        (fun t : ℝ => ‖deriv F (γ t)‖ * (0.15 * log ((q : ℝ) * t) + 3.389))
        (Set.uIcc (1 : ℝ) T) := by
      have hdd : DifferentiableOn ℂ F {s : ℂ | 0 < s.re} := fun s hs =>
        (Continuation457.gaussian_mellin_differentiable δ s hs).differentiableWithinAt
      have hopen : IsOpen {s : ℂ | 0 < s.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      have hD : DifferentiableOn ℂ (deriv F) {s : ℂ | 0 < s.re} := hdd.deriv hopen
      have hγc : Continuous γ := by simp only [γ]; fun_prop
      have hc1 : Continuous (fun t : ℝ => deriv F (γ t)) := by
        rw [continuous_iff_continuousAt]
        intro t
        exact ((hD.differentiableAt (hopen.mem_nhds (hγre t))).continuousAt).comp
          hγc.continuousAt
      refine (hc1.norm.continuousOn).mul ?_
      refine ContinuousOn.add (ContinuousOn.mul continuousOn_const ?_) continuousOn_const
      refine ContinuousOn.log (continuousOn_const.mul continuousOn_id) ?_
      intro t ht
      rw [Set.uIcc_of_le hT] at ht
      have : (0 : ℝ) < (q : ℝ) * t := by nlinarith [ht.1]
      exact this.ne'
    have hRint : IntervalIntegrable
        (fun t : ℝ => ‖deriv F (γ t)‖ * (0.15 * log ((q : ℝ) * t) + 3.389))
        MeasureTheory.volume (1 : ℝ) T := hcont.intervalIntegrable
    have hptw : ∀ t ∈ Set.Icc (1 : ℝ) T,
        -(deriv (fun u : ℝ => ‖F (γ u)‖) t * R t) ≤
          ‖deriv F (γ t)‖ * (0.15 * log ((q : ℝ) * t) + 3.389) := by
      intro t ht
      have h1 := hpt t
      have h2 := hR t ht
      calc -(deriv (fun u : ℝ => ‖F (γ u)‖) t * R t)
          ≤ |deriv (fun u : ℝ => ‖F (γ u)‖) t * R t| := neg_le_abs _
        _ = |deriv (fun u : ℝ => ‖F (γ u)‖) t| * |R t| := abs_mul _ _
        _ ≤ ‖deriv F (γ t)‖ * (0.15 * log ((q : ℝ) * t) + 3.389) :=
          mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    by_cases hint : IntervalIntegrable
        (fun t : ℝ => deriv (fun u : ℝ => ‖F (γ u)‖) t * R t) MeasureTheory.volume (1 : ℝ) T
    · rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_mono_on hT hint.neg hRint hptw
    · rw [intervalIntegral.integral_undef hint, neg_zero]
      refine intervalIntegral.integral_nonneg hT (fun t ht => ?_)
      exact mul_nonneg (norm_nonneg _) ((abs_nonneg _).trans (hR t ht))
  exact key _ hR

/-- The faithful assembly of the three leaves: the bound of `positive_mass_norm_sum_integral`
plus the boundary term at height `T`, namely `G T * g T`, which integration by parts on `[1, T]`
leaves and which the parent statement omits; see the module doc.  Sorry free given the leaves. -/
theorem positive_mass_norm_sum_integral_endpoint_of_leaves (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ T : ℝ) (hT : 1 ≤ T)
    (hzeros : ∀ s : ℂ, DirichletCharacter.LFunction χ s = 0 → 0 < s.re → s.re < 1 →
      |s.im| ≤ T → s.re = 1 / 2) :
    (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T},
        Set.indicator {ρ | 1 < ρ.val.im} (fun ρ => ‖mellinMassTerm χ δ ρ.val‖) ρ) ≤
      (1 / (2 * π)) * (∫ t in (1 : ℝ)..T,
        ‖gaussianMellin δ ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          log ((q : ℝ) * t / (2 * π))) +
      (∫ t in (1 : ℝ)..T,
        ‖deriv (gaussianMellin δ) ((1 / 2 : ℂ) + (t : ℝ) * Complex.I)‖ *
          (0.15 * log ((q : ℝ) * t) + 3.389)) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ * (0.15 * log (q : ℝ) + 3.389) +
      ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℝ) * Complex.I)‖ *
        (0.15 * log ((q : ℝ) * T) + 3.389) := by
  obtain ⟨c, hc⟩ := zero_count_error_bound q χ hχ
  rw [stieltjes_positive_zero_sum q χ δ T c hT hzeros]
  have hE := error_integral_le q χ δ T c hT (fun t ht => hc t ht.1)
  have hTb := abs_le.mp (hc T hT)
  have h1b := abs_le.mp (hc 1 le_rfl)
  have hGT : 0 ≤ ‖gaussianMellin δ ((1 / 2 : ℂ) + (T : ℝ) * Complex.I)‖ := norm_nonneg _
  have hG1eq : ‖gaussianMellin δ ((1 / 2 : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)‖ =
      ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ := by
    simp only [Complex.ofReal_one, one_mul]
  have hG1 : 0 ≤ ‖gaussianMellin δ ((1 / 2 : ℂ) + Complex.I)‖ := norm_nonneg _
  rw [hG1eq]
  simp only [mul_one] at h1b ⊢
  nlinarith [mul_le_mul_of_nonneg_left hTb.2 hGT, mul_le_mul_of_nonneg_left h1b.1 hG1]

end LeanLab.HelfgottMajor.Decomp431a
