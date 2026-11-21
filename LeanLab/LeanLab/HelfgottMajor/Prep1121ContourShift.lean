import LeanLab.HelfgottMajor.MainLemma41Split123
import LeanLab.HelfgottMajor.PrincipalRoute669
import LeanLab.Linnik.ExplicitFormula.Heights
import LeanLab.HelfgottMajor.Prep1121ContourRect

/-!
PREP split 2026-11-21, session CLAUDE-prep1121, route step
`MainLemma41Split123.contour_shift`.

P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, proof of Lemma 4.1,
pages 32 and 33, displays 4.4 and 4.7: Mellin inversion on a line in the half plane of
absolute convergence, then "We shift the line of integration in (4.4) to Re s = -1/2",
crossing the pole of ζ at s = 1 for q = 1, the non-trivial zeros, and s = 0, where the residue
R is taken as a circle integral.

The paper gives the shift in one sentence. The standard proof, Davenport ch. 17 and 19, that
the leaves below follow: a rectangle [-1/2, 2] × [-T', T'] at heights T' that avoid zeros,
the residue formula in the rectangle with the circle at 0 cut out, decay of the horizontal
sides, and convergence of the truncated vertical integrals and of the zero sum.

The conductor one case is already PROVED, `PrincipalRoute669.contour_shift_conductor_one`.
For q above 1 the zero avoiding heights are PROVED in the lab for every primitive χ,
`Linnik.ExplicitFormula.good_heights`, Davenport ch. 17, with |L'/L| at most C log²(T + 2) on
the horizontal sides; so no zero count hypothesis such as `MainHyps123.BookZeroCount` is
needed. The rectangle step is split further in `Prep1121ContourRect`. Two steps are PROVED here: the line of real part two, from
`SPLIT_principal_contour_identity.principal_prime_sum_mellin_contour`, and the integrability
on the line of real part -1/2, from `principal_half_line_integrable`.

The final result `contour_shift_of_leaves` has the exact statement of
`MainLemma41Split123.contour_shift` and no sorry of its own.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121ContourShift
open Real MeasureTheory Set Filter LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123
open LeanLab.HelfgottMajor.MainLemma41Split123
open scoped Topology

/-- PROVED. P0014 page 32, display 4.4, on the line Re s = 2 that display 4.7 uses: the twisted
prime sum is minus the vertical integral of L'/L(s, χ) G_δ(s) x^s, with s = 2 + iτ and
(1/2πi) ds = (1/2π) dτ. From `principal_prime_sum_mellin_contour` and G_δ = contMellin on
Re s above 0. -/
theorem line_two_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ) {x : ℝ}
    (hx : 1 ≤ x) :
    Schi etaHeart χ δ x =
      -((2 * π : ℂ)⁻¹ * ∫ τ : ℝ, contourIntegrand χ δ x ((2 : ℂ) + τ * Complex.I)) := by
  rw [SPLIT_principal_contour_identity.principal_prime_sum_mellin_contour x hx q χ δ, one_div]
  congr 2
  apply integral_congr_ae
  filter_upwards with τ
  rw [contourIntegrand, logDeriv_apply,
    Route669.contMellin_eq_gaussianMellin δ _ (by simp)]

/-- LEAF: P0014 page 32, display 4.4, the line Re s = 2 of display 4.7. The integrand
L'/L(s, χ) G_δ(s) x^s is integrable on Re s = 2: there L'/L is bounded by -ζ'/ζ(2), G_δ is
the Gaussian Mellin transform, which decays like (1 + τ²)⁻¹, and |x^s| = x². EASY: the same
bound as the private `gaussian_line_integrable` of SPLIT_principal_contour_identity times a
constant. -/
theorem line_two_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ) {x : ℝ}
    (hx : 1 ≤ x) :
    Integrable (fun τ : ℝ => contourIntegrand χ δ x ((2 : ℂ) + τ * Complex.I)) := by
  sorry

/-- PROVED. P0014 page 33, display 4.7, the line Re s = -1/2: the integrand is integrable
there, from `principal_half_line_integrable` and contMellin = continuedGaussian on
Re s above -1. -/
theorem line_minus_half_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ)
    {x : ℝ} (hx : 1 ≤ x) :
    Integrable (fun τ : ℝ => contourIntegrand χ δ x (-1 / 2 + τ * Complex.I)) := by
  refine (SPLIT_principal_contour_identity.principal_half_line_integrable x hx q χ δ).congr ?_
  filter_upwards with τ
  rw [contourIntegrand, logDeriv_apply, Route669.contMellin_eq δ _ (by norm_num)]

/-- PROVED. P0014 page 33, display 4.7, the residue R at s = 0 as a circle integral. For a
primitive χ of conductor q above 1, L(s, χ) is entire and not identically zero, so its zeros
are isolated, and G_δ = contMellin is holomorphic on Re s above -1 except at 0; hence some
radius r below 1/2 gives a closed punctured disc on which L'/L(s, χ) G_δ(s) x^s is
holomorphic. Isolated zeros plus `Route669.contMellin_differentiableAt`, as in
`PrincipalRoute669.small_disc_conductor_one`. -/
theorem small_disc {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
      DifferentiableOn ℂ (contourIntegrand χ δ x) (Metric.closedBall 0 r \ {0}) := by
  have hχ1 := LeanLab.Linnik.ExplicitFormula.ne_one_of_isPrimitive hχ hq
  have hent : Differentiable ℂ χ.LFunction := DirichletCharacter.differentiable_LFunction hχ1
  have hA : AnalyticAt ℂ χ.LFunction 0 :=
    LeanLab.Linnik.ExplicitFormula.analyticAt_LFunction χ (Or.inr hχ1)
  have hx0 : 0 < x := by linarith
  rcases hA.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd (analyticOrderAt_eq_top.mpr h)
      (LeanLab.Linnik.ExplicitFormula.analyticOrderAt_LFunction_ne_top χ (by norm_num))
  have hsmall : ∀ᶠ s : ℂ in 𝓝[≠] (0 : ℂ), -1 < s.re :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num))
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp (h.and hsmall)
  refine ⟨min (ε / 2) (1 / 4), by positivity, by
    have := min_le_right (ε / 2) (1 / 4); linarith, ?_⟩
  intro s hs
  have hsb : s ∈ Metric.ball (0 : ℂ) ε := by
    have h1 := Metric.mem_closedBall.mp hs.1
    have h2 := min_le_left (ε / 2) (1 / 4)
    exact Metric.mem_ball.mpr (by linarith)
  have hs0 : s ≠ 0 := by simpa only [mem_singleton_iff] using hs.2
  obtain ⟨hL, hre⟩ := hsub ⟨hsb, hs0⟩
  have hdL : DifferentiableAt ℂ (deriv χ.LFunction) s :=
    ((hent.analyticAt s).deriv).differentiableAt
  have hd := ((hdL.div (hent s) hL).mul (Route669.contMellin_differentiableAt δ s hre hs0)).mul
    (differentiableAt_id.const_cpow (c := (x : ℂ)) (Or.inl (by exact_mod_cast hx0.ne')))
  exact hd.differentiableWithinAt

/-- PROVED from the leaves of `Prep1121ContourRect`. P0014 page 33, display 4.7, residues on
one rectangle. For primitive χ, q above 1, T' ≥ 1 with no zero of L(s, χ) on the horizontal
sides of [-1/2, 2] × [-T', T'], and a punctured disc of radius r < 1/2 where F is holomorphic:
the rectangle integral of F over 2πi, as two vertical and two horizontal sides, is the circle
integral R over 2πi plus the residues m(ρ) G_δ(ρ) x^ρ at the zeros with 0 < Re ρ < 1,
|Im ρ| ≤ T', that is `lowZeros χ δ x T'`. -/
theorem rect_identity {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : q ≠ 1) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {T' r : ℝ} (hT' : 1 ≤ T') (hr : 0 < r)
    (hr2 : r < 1 / 2)
    (hF : DifferentiableOn ℂ (contourIntegrand χ δ x) (Metric.closedBall 0 r \ {0}))
    (hbd : ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ τ ∈ ({T', -T'} : Set ℝ),
      χ.LFunction (σ + τ * Complex.I) ≠ 0) :
    (2 * π : ℂ)⁻¹ * (∫ τ in -T'..T', contourIntegrand χ δ x ((2 : ℂ) + τ * Complex.I)) -
        (2 * π : ℂ)⁻¹ * (∫ τ in -T'..T', contourIntegrand χ δ x (-1 / 2 + τ * Complex.I)) +
        (2 * π * Complex.I)⁻¹ *
          ((∫ σ in (-1 / 2 : ℝ)..2,
              contourIntegrand χ δ x ((σ : ℂ) + ((-T' : ℝ) : ℂ) * Complex.I)) -
            ∫ σ in (-1 / 2 : ℝ)..2,
              contourIntegrand χ δ x ((σ : ℂ) + (T' : ℂ) * Complex.I)) =
      (2 * π * Complex.I)⁻¹ * circleIntegral (contourIntegrand χ δ x) 0 r +
        lowZeros χ δ x T' := by
  exact Prep1121ContourRect.rect_identity χ hχ hq δ hx hT' hr hr2 hF hbd

/-- LEAF: P0014 page 32, the continuation of G_δ: s G_δ(s) = M(-t f'(t))(s), display 4.14,
decays in the strip -1/2 ≤ Re s ≤ 2 at least like (1 + y²)⁻¹ in the height y, for |y| ≥ 1.
MEDIUM: the same three step recurrence as the private `pcsB_cont_decay_strip` of
SPLIT_principal_contour_identity, for `continuedGaussian`, with `Route669.contMellin_eq`. -/
theorem contMellin_decay_strip (δ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ y : ℝ, 1 ≤ |y| →
      ‖contMellin δ ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ K / (1 + y ^ 2) := by
  sorry

/-- LEAF: P0014 page 33, display 4.7, the horizontal sides vanish. At heights Y n in
[max n 5, max n 5 + 1] where |L'/L| is at most C log²(max n 5 + 2) on both horizontal sides,
and with the decay of G_δ, the horizontal integrals are O(x² log² n / n²) and tend to 0.
MEDIUM: one bound and `log² T / T² → 0`, as `pcsB_horiz_tendsto` for ζ. -/
theorem horizontal_tendsto {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ) {x : ℝ}
    (hx : 1 ≤ x)
    (hdec : ∃ K : ℝ, 0 < K ∧ ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ y : ℝ, 1 ≤ |y| →
      ‖contMellin δ ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤ K / (1 + y ^ 2))
    {C : ℝ} (hC : 0 ≤ C) (Y : ℕ → ℝ)
    (hYI : ∀ n : ℕ, Y n ∈ Icc (max (n : ℝ) 5) (max (n : ℝ) 5 + 1))
    (hB : ∀ n : ℕ, ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ τ ∈ ({Y n, -Y n} : Set ℝ),
      ‖deriv χ.LFunction (σ + τ * Complex.I) / χ.LFunction (σ + τ * Complex.I)‖ ≤
        C * Real.log (max (n : ℝ) 5 + 2) ^ 2) :
    Tendsto (fun n : ℕ => ∫ σ in (-1 / 2 : ℝ)..2,
        contourIntegrand χ δ x ((σ : ℂ) + (Y n : ℂ) * Complex.I)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫ σ in (-1 / 2 : ℝ)..2,
        contourIntegrand χ δ x ((σ : ℂ) + ((-Y n : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
  sorry

/-- LEAF: P0014 page 31, display 4.1, convergence of the zero sum. The terms m(ρ) G_δ(ρ) x^ρ
over the zeros with 0 < Re ρ < 1 are summable: |G_δ(ρ)| ≪ 1/|(ρ + 1)(ρ + 2)| in the strip
and the sum of m(ρ)/|(ρ + 1)(ρ + 2)| converges, `Linnik.ExplicitFormula.zero_sum_total`.
MEDIUM: as `Linnik.ExplicitFormula.summable_zterm` with the Gaussian decay in the strip. -/
theorem zero_sum_summable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1} => zeroTerm χ δ x ρ.val) := by
  sorry

/-- PROVED. P0014 page 31, display 4.1 split at height T as in Lemmas 4.4 and 4.5: for a
summable family the zeros of height at most T and above T together give the full zero sum. -/
theorem zero_sum_split {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ x T : ℝ)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1} => zeroTerm χ δ x ρ.val)) :
    lowZeros χ δ x T + highZeros χ δ x T =
      ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
        zeroTerm χ δ x ρ.val := by
  rw [← hs.tsum_subtype_add_tsum_subtype_compl {ρ | |ρ.val.im| ≤ T}]
  congr 1
  · exact (Equiv.tsum_eq ((Equiv.subtypeSubtypeEquivSubtypeInter
        (fun ρ : ℂ => DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1)
        (fun ρ : ℂ => |ρ.im| ≤ T)).trans
          (Equiv.subtypeEquivRight (fun ρ => by simp only [and_assoc])))
        (fun ρ => zeroTerm χ δ x ρ.val)).symm
  · exact (Equiv.tsum_eq ((Equiv.subtypeSubtypeEquivSubtypeInter
        (fun ρ : ℂ => DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1)
        (fun ρ : ℂ => ¬ |ρ.im| ≤ T)).trans
          (Equiv.subtypeEquivRight (fun ρ => by simp only [and_assoc, not_le])))
        (fun ρ => zeroTerm χ δ x ρ.val)).symm

/-- PROVED. P0014 page 33, display 4.7, the zeros inside the rectangles exhaust all zeros: for
heights Y n tending to infinity the zero sums up to Y n tend to the full zero sum, by
dominated convergence for sums, `tendsto_tsum_of_dominated_convergence`. -/
theorem low_zeros_tendsto {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ x : ℝ)
    (hs : Summable (fun ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1} => zeroTerm χ δ x ρ.val))
    (Y : ℕ → ℝ) (hY : Tendsto Y atTop atTop) :
    Tendsto (fun n : ℕ => lowZeros χ δ x (Y n)) atTop
      (𝓝 (∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
        zeroTerm χ δ x ρ.val)) := by
  have heq : ∀ T : ℝ, lowZeros χ δ x T =
      ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
        ({ρ | |ρ.val.im| ≤ T} : Set {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧
          0 < ρ.re ∧ ρ.re < 1}).indicator (fun ρ => zeroTerm χ δ x ρ.val) ρ := by
    intro T
    rw [← tsum_subtype]
    exact (Equiv.tsum_eq ((Equiv.subtypeSubtypeEquivSubtypeInter
        (fun ρ : ℂ => DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1)
        (fun ρ : ℂ => |ρ.im| ≤ T)).trans
          (Equiv.subtypeEquivRight (fun ρ => by simp only [and_assoc])))
        (fun ρ => zeroTerm χ δ x ρ.val)).symm
  simp_rw [heq]
  refine tendsto_tsum_of_dominated_convergence (bound := fun ρ => ‖zeroTerm χ δ x ρ.val‖)
    (summable_norm_iff.mpr hs) (fun ρ => ?_)
    (Eventually.of_forall fun n ρ => norm_indicator_le_norm_self _ _)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hY.eventually_ge_atTop |ρ.val.im|] with n hn
  exact (Set.indicator_of_mem (s := ({ρ | |ρ.val.im| ≤ Y n} : Set {ρ : ℂ //
    DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}))
    (f := fun ρ => zeroTerm χ δ x ρ.val) hn).symm

/-- Assembly, no sorry of its own. P0014 proof of Lemma 4.1, pages 32 and 33, displays 4.4
and 4.7: the exact statement of `MainLemma41Split123.contour_shift`, from the PROVED conductor
one case, the PROVED zero avoiding heights of `Linnik.ExplicitFormula.good_heights`, and the
leaves above. -/
theorem contour_shift_of_leaves (x : ℝ) (hx : 1 ≤ x) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (δ T : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      DifferentiableOn ℂ (contourIntegrand χ δ x) (Metric.closedBall 0 r \ {0}) ∧
      Schi etaHeart χ δ x - (if q = 1 then fhat etaHeart (-δ) * x else 0) +
          lowZeros χ δ x T + highZeros χ δ x T +
          (2 * π * Complex.I)⁻¹ * circleIntegral (contourIntegrand χ δ x) 0 r =
        -((2 * π : ℂ)⁻¹ *
          ∫ τ : ℝ, contourIntegrand χ δ x (-1 / 2 + τ * Complex.I)) := by
  rcases eq_or_ne q 1 with hq | hq
  · subst hq
    obtain ⟨r, hr, hF, h⟩ := PrincipalRoute669.contour_shift_conductor_one x hx χ δ T
    exact ⟨r, hr, hF, by rw [if_pos rfl]; exact h⟩
  obtain ⟨r, hr, hr2, hF⟩ := small_disc χ hχ hq δ hx
  refine ⟨r, hr, hF, ?_⟩
  rw [if_neg hq]
  obtain ⟨C, hC, hgood⟩ := Linnik.ExplicitFormula.good_heights hχ
  choose! Tf hTfI hTf using hgood
  have hT5 : ∀ n : ℕ, (5 : ℝ) ≤ max (n : ℝ) 5 := fun n => le_max_right _ _
  have hYI : ∀ n : ℕ, Tf (max (n : ℝ) 5) ∈ Icc (max (n : ℝ) 5) (max (n : ℝ) 5 + 1) :=
    fun n => hTfI _ (hT5 n)
  have hYge : ∀ n : ℕ, (n : ℝ) ≤ Tf (max (n : ℝ) 5) :=
    fun n => (le_max_left _ _).trans (hYI n).1
  have hY1 : ∀ n : ℕ, 1 ≤ Tf (max (n : ℝ) 5) := fun n => by linarith [(hYI n).1, hT5 n]
  have hYtop : Tendsto (fun n : ℕ => Tf (max (n : ℝ) 5)) atTop atTop :=
    tendsto_atTop_mono hYge tendsto_natCast_atTop_atTop
  have hrect := fun n : ℕ => rect_identity χ hχ hq δ hx (hY1 n) hr hr2 hF
    (fun σ hσ τ hτ => (hTf _ (hT5 n) σ hσ τ hτ).1)
  have hA := intervalIntegral_tendsto_integral (line_two_integrable χ δ hx)
    (tendsto_neg_atTop_atBot.comp hYtop) hYtop
  have hB := intervalIntegral_tendsto_integral (line_minus_half_integrable χ δ hx)
    (tendsto_neg_atTop_atBot.comp hYtop) hYtop
  obtain ⟨hH1, hH2⟩ := horizontal_tendsto χ δ hx (contMellin_decay_strip δ) hC
    (fun n : ℕ => Tf (max (n : ℝ) 5)) hYI (fun n σ hσ τ hτ => (hTf _ (hT5 n) σ hσ τ hτ).2)
  have hs := zero_sum_summable χ hχ δ hx
  have hL := low_zeros_tendsto χ δ x hs _ hYtop
  have hlhs := ((hA.const_mul (2 * π : ℂ)⁻¹).sub (hB.const_mul (2 * π : ℂ)⁻¹)).add
    ((hH2.sub hH1).const_mul (2 * π * Complex.I)⁻¹)
  have hrhs : Tendsto (fun n : ℕ => (2 * π * Complex.I)⁻¹ *
      circleIntegral (contourIntegrand χ δ x) 0 r + lowZeros χ δ x (Tf (max (n : ℝ) 5)))
      atTop (𝓝 ((2 * π * Complex.I)⁻¹ * circleIntegral (contourIntegrand χ δ x) 0 r +
        ∑' ρ : {ρ : ℂ // DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1},
          zeroTerm χ δ x ρ.val)) :=
    tendsto_const_nhds.add hL
  have heq := tendsto_nhds_unique (hlhs.congr (fun n => hrect n)) hrhs
  have hline := line_two_eq χ δ hx
  have hsplit := zero_sum_split χ δ x T hs
  linear_combination hline - heq + hsplit

end LeanLab.HelfgottMajor.Prep1121ContourShift

#print axioms LeanLab.HelfgottMajor.Prep1121ContourShift.line_two_eq
#print axioms LeanLab.HelfgottMajor.Prep1121ContourShift.line_minus_half_integrable
#print axioms LeanLab.HelfgottMajor.Prep1121ContourShift.small_disc
#print axioms LeanLab.HelfgottMajor.Prep1121ContourShift.rect_identity
#print axioms LeanLab.HelfgottMajor.Prep1121ContourShift.zero_sum_split
#print axioms LeanLab.HelfgottMajor.Prep1121ContourShift.low_zeros_tendsto
#print axioms LeanLab.HelfgottMajor.Prep1121ContourShift.contour_shift_of_leaves
