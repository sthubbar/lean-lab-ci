import LeanLab.HelfgottMajor.Prep1121ContourRect

/-!
PREP deepening 2026-11-21, session CLAUDE-prep1121 HM-contour-p2. Pieces for five leaves of
`Prep1121ContourRect`: `integrand_meromorphicOn`, `poles_off_origin`,
`simple_poles_off_origin`, `residue_at_zero_point` and `residue_sum_reindex`.

P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 32, the
continuation of G_δ by display 4.14, and page 33, display 4.7, the poles crossed when the line
of integration moves to Re s = -1/2. Davenport ch. 17 for the residue of L'/L at a zero.

The integrand F(s) = L'/L(s, χ) G_δ(s) x^s is the product of the logarithmic derivative of the
entire L(s, χ), for primitive χ of conductor above 1, with the kernel G_δ(s) x^s, which is
holomorphic on Re s above -1 except at s = 0. Each final result below, named after its
parent leaf with suffix `_of_pieces`, has the parent's exact statement and no sorry.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121DCtPoles
open Real MeasureTheory Set Filter LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123
open LeanLab.HelfgottMajor.MainLemma41Split123 LeanLab.Linnik.ExplicitFormula
open scoped Topology

/-- PROVED. P0014 page 32: the continuation G_δ = contMellin is analytic at every s ≠ 0 with
Re s above -1, from `Route669.contMellin_differentiableAt` on an open set. -/
theorem contMellin_analyticAt (δ : ℝ) {z : ℂ} (hz : -1 < z.re) (hz0 : z ≠ 0) :
    AnalyticAt ℂ (contMellin δ) z := by
  have hU : IsOpen ({s : ℂ | -1 < s.re} ∩ {0}ᶜ) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton
  have hD : DifferentiableOn ℂ (contMellin δ) ({s : ℂ | -1 < s.re} ∩ {0}ᶜ) :=
    fun s hs => (Route669.contMellin_differentiableAt δ s hs.1 hs.2).differentiableWithinAt
  exact hD.analyticAt (hU.mem_nhds ⟨hz, hz0⟩)

/-- PROVED. P0014 page 32 before display 4.6: G_δ is meromorphic at s = 0, since near 0 it is
the regular numerator M(-t f'(t))(s), analytic on Re s above -1, divided by s. -/
theorem contMellin_meromorphicAt_zero (δ : ℝ) : MeromorphicAt (contMellin δ) 0 := by
  set N : ℂ → ℂ := fun s => Decomp269a.gaussianMellin δ (s + 2) -
    (2 * π * Complex.I * δ) * Decomp269a.gaussianMellin δ (s + 1) with hN
  have hU : IsOpen {s : ℂ | -1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hD : DifferentiableOn ℂ N {s : ℂ | -1 < s.re} := by
    intro s hs
    have hs' : -1 < s.re := hs
    have h2 := (Continuation457.gaussian_mellin_differentiable δ (s + 2)
      (by simp; linarith)).comp s (differentiableAt_id.add_const 2)
    have h1 := (Continuation457.gaussian_mellin_differentiable δ (s + 1)
      (by simp; linarith)).comp s (differentiableAt_id.add_const 1)
    exact (h2.sub (h1.const_mul _)).differentiableWithinAt
  have hA : AnalyticAt ℂ N 0 := hD.analyticAt (hU.mem_nhds (by norm_num))
  have hM : MeromorphicAt (fun s => N s / s) 0 :=
    hA.meromorphicAt.div analyticAt_id.meromorphicAt
  refine hM.congr ?_
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds (show (0 : ℂ) ∈ {s : ℂ | -1 < s.re} by
    norm_num))] with s hs
  rw [Route669.contMellin_eq δ s hs, Contour457.continuedGaussian]

/-- PROVED. P0014 page 32: the kernel G_δ(s) x^s is meromorphic at every s with Re s above -1. -/
theorem kernel_meromorphicAt (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {z : ℂ} (hz : -1 < z.re) :
    MeromorphicAt (fun s => contMellin δ s * (x : ℂ) ^ s) z := by
  have hx0 : 0 < x := by linarith
  have hc : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s) z :=
    analyticAt_const.cpow analyticAt_id (Complex.ofReal_mem_slitPlane.mpr hx0)
  rcases eq_or_ne z 0 with rfl | hz0
  · exact (contMellin_meromorphicAt_zero δ).mul hc.meromorphicAt
  · exact ((contMellin_analyticAt δ hz hz0).mul hc).meromorphicAt

/-- PROVED. P0014 page 32: the kernel G_δ(s) x^s is analytic at s ≠ 0 with Re s above -1. -/
theorem kernel_analyticAt (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {z : ℂ} (hz : -1 < z.re) (hz0 : z ≠ 0) :
    AnalyticAt ℂ (fun s => contMellin δ s * (x : ℂ) ^ s) z := by
  have hx0 : 0 < x := by linarith
  exact (contMellin_analyticAt δ hz hz0).mul
    (analyticAt_const.cpow analyticAt_id (Complex.ofReal_mem_slitPlane.mpr hx0))

/-- PROVED. The integrand factors as L'/L times the kernel. -/
theorem integrand_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ x : ℝ) :
    contourIntegrand χ δ x = fun s => deriv χ.LFunction s / χ.LFunction s *
      (contMellin δ s * (x : ℂ) ^ s) := by
  funext s; simp only [contourIntegrand]; ring

/-- PROVED. P0014 page 33, display 4.7: F is meromorphic at every s with Re s above -1. -/
theorem integrand_meromorphicAt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ : ℝ)
    {x : ℝ} (hx : 1 ≤ x) {z : ℂ} (hz : -1 < z.re) :
    MeromorphicAt (contourIntegrand χ δ x) z := by
  rw [integrand_eq]
  have hL := meromorphicAt_LFunction χ z
  exact (hL.deriv.div hL).mul (kernel_meromorphicAt δ hx hz)

/-- PROVED. Points of the rectangle [-1/2, 2] × [-T', T'] have real part above -1. -/
theorem re_of_mem_rect {T' : ℝ} {p : ℂ}
    (hp : p ∈ Complex.Rectangle (⟨-1 / 2, -T'⟩ : ℂ) (⟨2, T'⟩ : ℂ)) : -1 / 2 ≤ p.re := by
  have h := hp.1
  simp only [Set.mem_preimage] at h
  rw [Set.uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 2)] at h
  exact h.1

/-- PROVED, the exact statement of `Prep1121ContourRect.integrand_meromorphicOn`.
P0014 page 32, display 4.14, with page 33, display 4.7. -/
theorem integrand_meromorphicOn_of_pieces {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) (T' : ℝ) :
    MeromorphicOn (contourIntegrand χ δ x)
      (Complex.Rectangle (⟨-1 / 2, -T'⟩ : ℂ) (⟨2, T'⟩ : ℂ)) := by
  intro p hp
  exact integrand_meromorphicAt χ δ hx (by linarith [re_of_mem_rect hp])

/-- PROVED. P0014 page 33, display 4.7: off the zeros of L(s, χ), F is analytic at s ≠ 0 with
Re s above -1, for χ ≠ 1. -/
theorem integrand_analyticAt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {z : ℂ} (hz : -1 < z.re) (hz0 : z ≠ 0)
    (hL : χ.LFunction z ≠ 0) : AnalyticAt ℂ (contourIntegrand χ δ x) z := by
  rw [integrand_eq]
  have hA := analyticAt_LFunction χ (s := z) (Or.inr hχ1)
  exact (hA.deriv.div hA hL).mul (kernel_analyticAt δ hx hz hz0)

/-- PROVED. P0014 page 33, display 4.7: a pole p ≠ 0 of F in the rectangle is a zero of L with
0 < Re p < 1. The height bound is left to `poles_off_origin_of_nonneg`. -/
theorem poles_off_origin_re {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) (T' : ℝ) {p : ℂ}
    (hp : p ∈ Complex.Rectangle (⟨-1 / 2, -T'⟩ : ℂ) (⟨2, T'⟩ : ℂ)) (hp0 : p ≠ 0)
    (hneg : meromorphicOrderAt (contourIntegrand χ δ x) p < 0) :
    χ.LFunction p = 0 ∧ 0 < p.re ∧ p.re < 1 := by
  have hχ1 := ne_one_of_isPrimitive hχ hq
  have hre := re_of_mem_rect hp
  have hLz : χ.LFunction p = 0 := by
    by_contra hL
    exact absurd (integrand_analyticAt χ hχ1 δ hx (by linarith) hp0 hL).meromorphicOrderAt_nonneg
      (not_le.mpr hneg)
  have hp1 : p ≠ 1 := by
    rintro rfl; exact DirichletCharacter.LFunction_apply_one_ne_zero hχ1 hLz
  refine ⟨hLz, ?_, re_lt_one_of_zero χ hLz hp1⟩
  by_contra h
  exact hp0 (zero_left_strip hχ hLz hre (not_lt.mp h))

/-- PROVED. `Prep1121ContourRect.poles_off_origin` under the extra hypothesis 0 ≤ T', which
every use of it has, since `rect_identity` and `residue_sum_reindex` assume 1 ≤ T'. Without it
the parent statement looks false, see the QUESTION in the notes: for T' below 0 the rectangle
is [-1/2, 2] × [T', -T'] and still holds the zeros of height at most -T', while the conclusion
asks |Im p| ≤ T' < 0. -/
theorem poles_off_origin_of_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {T' : ℝ} (hT : 0 ≤ T')
    {p : ℂ}
    (hp : p ∈ Complex.Rectangle (⟨-1 / 2, -T'⟩ : ℂ) (⟨2, T'⟩ : ℂ)) (hp0 : p ≠ 0)
    (hneg : meromorphicOrderAt (contourIntegrand χ δ x) p < 0) :
    χ.LFunction p = 0 ∧ 0 < p.re ∧ p.re < 1 ∧ |p.im| ≤ T' := by
  obtain ⟨h1, h2, h3⟩ := poles_off_origin_re χ hχ hq δ hx T' hp hp0 hneg
  exact ⟨h1, h2, h3, abs_le.mpr ((Prep1121ContourRect.mem_rect hT).mp hp).2⟩

/-- PROVED, the exact statement of `Prep1121ContourRect.simple_poles_off_origin`. P0014 page 33,
display 4.7: at p ≠ 0 with Re p above -1 the kernel is analytic and L'/L has order at least -1. -/
theorem simple_poles_off_origin_of_pieces {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) (T' : ℝ) :
    HasSimplePolesOn (contourIntegrand χ δ x)
      (Complex.Rectangle (⟨-1 / 2, -T'⟩ : ℂ) (⟨2, T'⟩ : ℂ) \ {0}) := by
  intro z hz
  have hre := re_of_mem_rect hz.1
  have hz0 : z ≠ 0 := by simpa only [mem_singleton_iff] using hz.2
  have hk := kernel_analyticAt δ hx (z := z) (by linarith) hz0
  have hzL := meromorphicAt_LFunction χ z
  have hLd : MeromorphicAt (logDeriv χ.LFunction) z := hzL.deriv.div hzL
  have hF : contourIntegrand χ δ x = logDeriv χ.LFunction *
      (fun s : ℂ => contMellin δ s * (x : ℂ) ^ s) := by
    rw [integrand_eq]; funext s; simp [logDeriv_apply]
  rw [hF, meromorphicOrderAt_mul hLd hk.meromorphicAt]
  have hlog : -1 ≤ meromorphicOrderAt (logDeriv χ.LFunction) z := by
    by_cases h : meromorphicOrderAt χ.LFunction z = 0
    · refine le_trans ?_ (meromorphicOrderAt_logDeriv_nonneg hzL h)
      exact WithTop.coe_le_coe.mpr (show (-1 : ℤ) ≤ 0 by norm_num)
    · rw [meromorphicOrderAt_logDeriv_eq_neg_one hzL h (order_LFunction_ne_top hχ z)]
  calc ((-1 : ℤ) : WithTop ℤ) = -1 + 0 := by simp
    _ ≤ _ := add_le_add hlog hk.meromorphicOrderAt_nonneg

/-- PROVED, the exact statement of `Prep1121ContourRect.residue_at_zero_point`. P0014 page 31,
display 4.1, with page 33, display 4.7: (s - ρ) L'/L(s) tends to m(ρ), and the kernel is
continuous at ρ with value G_δ(ρ) x^ρ, as `Linnik.ExplicitFormula.residue_Fchi_of_ne_one`. -/
theorem residue_at_zero_point_of_pieces {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {ρ : ℂ} (hρ : χ.LFunction ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    residue (contourIntegrand χ δ x) ρ = zeroTerm χ δ x ρ := by
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at h1
  have hρ0 : ρ ≠ 0 := by rintro rfl; simp at h0
  have hL := LeanLab.PNTPort.ExplicitPsi1.tendsto_mul_logDeriv_mero
    (meromorphicAt_LFunction χ ρ) (order_LFunction_of_ne_one χ hρ1)
  have hk := ((kernel_analyticAt δ hx (z := ρ) (by linarith) hρ0).continuousAt.tendsto).mono_left
    (nhdsWithin_le_nhds (s := {ρ}ᶜ))
  apply residue_eq_of_tendsto
  have := hL.mul hk
  rw [Route669.contMellin_eq_gaussianMellin δ ρ h0] at this
  have hz : zeroTerm χ δ x ρ =
      ((mult χ ρ : ℤ) : ℂ) * (gaussianMellin δ ρ * (x : ℂ) ^ ρ) := by
    simp only [zeroTerm, mult, nsmul_eq_mul, Int.cast_natCast]
  rw [hz]
  refine this.congr (fun s => ?_)
  simp only [contourIntegrand]; ring

/-- PROVED, the exact statement of `Prep1121ContourRect.residue_sum_reindex`. P0014 page 33,
display 4.7: both residue sums are sums over ℂ of indicator functions, and the two indicators
agree, since every pole off 0 is a zero of height at most T', and a zero that is not a pole has
residue 0. -/
theorem residue_sum_reindex_of_pieces {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {T' : ℝ} (hT' : 1 ≤ T') :
    sumResiduesIn (contourIntegrand χ δ x)
        ((Complex.Rectangle (⟨-1 / 2, -T'⟩ : ℂ) (⟨2, T'⟩ : ℂ) ∩
          {p | meromorphicOrderAt (contourIntegrand χ δ x) p < 0}) \ {0}) =
      ∑' ρ : {ρ : ℂ // χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T'},
        residue (contourIntegrand χ δ x) ρ.val := by
  set F := contourIntegrand χ δ x
  set S : Set ℂ := (Complex.Rectangle (⟨-1 / 2, -T'⟩ : ℂ) (⟨2, T'⟩ : ℂ) ∩
    {p | meromorphicOrderAt F p < 0}) \ {0}
  set Z : Set ℂ := {ρ | χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T'}
  have hT0 : (0 : ℝ) ≤ T' := by linarith
  have hZ : (∑' ρ : {ρ : ℂ // χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T'},
      residue F ρ.val) = ∑' ρ : Z, residue F ρ := rfl
  rw [hZ, sumResiduesIn, tsum_subtype S (residue F), tsum_subtype Z (residue F)]
  congr 1
  funext z
  by_cases hzS : z ∈ S
  · have hzZ : z ∈ Z := poles_off_origin_of_nonneg χ hχ hq δ hx hT0 hzS.1.1
      (by simpa only [mem_singleton_iff] using hzS.2) hzS.1.2
    rw [Set.indicator_of_mem hzS, Set.indicator_of_mem hzZ]
  · rw [Set.indicator_of_notMem hzS]
    by_cases hzZ : z ∈ Z
    · rw [Set.indicator_of_mem hzZ]
      obtain ⟨-, hre0, hre1, him⟩ := hzZ
      have hz0 : z ≠ 0 := by rintro rfl; simp at hre0
      have hzR : z ∈ Complex.Rectangle (⟨-1 / 2, -T'⟩ : ℂ) (⟨2, T'⟩ : ℂ) :=
        (Prep1121ContourRect.mem_rect hT0).mpr
          ⟨⟨by linarith, by linarith⟩, abs_le.mp him⟩
      have hnp : 0 ≤ meromorphicOrderAt F z := by
        by_contra h
        exact hzS ⟨⟨hzR, not_le.mp h⟩, by simpa only [mem_singleton_iff] using hz0⟩
      exact (residue_eq_zero_of_not_pole_of_meromorphicAt
        (integrand_meromorphicAt χ δ hx (by linarith)) hnp).symm
    · rw [Set.indicator_of_notMem hzZ]

end LeanLab.HelfgottMajor.Prep1121DCtPoles

#print axioms LeanLab.HelfgottMajor.Prep1121DCtPoles.integrand_meromorphicOn_of_pieces
#print axioms LeanLab.HelfgottMajor.Prep1121DCtPoles.poles_off_origin_re
#print axioms LeanLab.HelfgottMajor.Prep1121DCtPoles.poles_off_origin_of_nonneg
#print axioms LeanLab.HelfgottMajor.Prep1121DCtPoles.simple_poles_off_origin_of_pieces
#print axioms LeanLab.HelfgottMajor.Prep1121DCtPoles.residue_at_zero_point_of_pieces
#print axioms LeanLab.HelfgottMajor.Prep1121DCtPoles.residue_sum_reindex_of_pieces
