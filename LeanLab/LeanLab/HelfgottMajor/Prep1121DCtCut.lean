import LeanLab.HelfgottMajor.Prep1121ContourRect

/-!
PREP deepening 2026-11-21, session CLAUDE-prep1121 HM-contour-p2. Pieces for the HARD leaf
`Prep1121ContourRect.rect_cut_origin`.

P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, page 33, display 4.7:
the shift of the line of integration crosses s = 0, where for even χ the integrand has a double
pole, and the paper keeps the residue there as the circle integral R. The PNTPort residue
formula `RectangleIntegral'_eq_sumResiduesIn` covers simple poles only, so the standard
argument, Ahlfors ch. 4 and Davenport ch. 17, is split as follows. Subtract the principal part
P(s) = Σ_{k < N} a_k s^(-(k+1)) of f at 0. Then f - P has no pole at 0 and the same simple poles
and residues as f elsewhere, so the PNTPort formula applies to it; its circle integral about 0
vanishes; and the rectangle integral of P over 2πi and the circle integral of P over 2πi are
both a_0, since s^(-(k+1)) has a primitive off 0 for k ≥ 1.

The final result `rect_cut_origin_of_pieces` has the exact statement of
`Prep1121ContourRect.rect_cut_origin` and no sorry of its own. Generic complex analysis, no
L-function. AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121DCtCut
open Real MeasureTheory Set Filter
open scoped Topology Interval

/-- The principal part Σ_{k < N} a_k s^(-(k+1)) at s = 0, a finite Laurent polynomial. -/
local notation "PP" N "," a => fun s : ℂ => ∑ k ∈ Finset.range N, a k * s ^ (-((k : ℤ) + 1))

/-- LEAF: Ahlfors ch. 4 §3.2, the Laurent principal part at a pole, used at s = 0 on P0014
page 33, display 4.7. A function meromorphic at 0 differs from some finite Laurent polynomial
Σ_{k < N} a_k s^(-(k+1)) by a function meromorphic at 0 with no pole there. MEDIUM: write
f = s^n h with h analytic, `meromorphicOrderAt_eq_int_iff`, and take the first -n Taylor
coefficients of h, `HasFPowerSeriesAt`. -/
theorem principal_part_at_origin {f : ℂ → ℂ} (hf : MeromorphicAt f 0) :
    ∃ (N : ℕ) (a : ℕ → ℂ), MeromorphicAt (f - PP N, a) 0 ∧
      0 ≤ meromorphicOrderAt (f - PP N, a) 0 := by
  sorry

/-- PROVED. A finite Laurent polynomial in s^(-1) is holomorphic off 0. -/
theorem principal_differentiableAt (N : ℕ) (a : ℕ → ℂ) {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (PP N, a) s := by
  have h := DifferentiableAt.sum (u := Finset.range N)
    (A := fun k (t : ℂ) => a k * t ^ (-((k : ℤ) + 1))) (x := s)
    (fun k _ => (differentiableAt_zpow.mpr (Or.inl hs)).const_mul _)
  convert h using 1
  funext t
  simp only [Finset.sum_apply]

/-- PROVED here, in the repair of the FREE unit `free-ms-leanstral/task2211`: Cauchy for a
removable singularity in circle integral form. If `g` is differentiable on the punctured open
ball of radius `r` about 0 and `Function.update g 0 w` is continuous on the closed ball, then the
circle integral of `g` about 0 vanishes. This is the statement the FREE unit proved; it is kept
as the private step of `circle_removable`. Cauchy-Goursat with the countable exceptional set
`{0}` applies to the updated function, and the circle integral only sees the sphere. -/
private theorem circleIntegral_eq_zero_of_punctured {g : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (w : ℂ)
    (hcont : ContinuousOn (Function.update g 0 w) (Metric.closedBall 0 r))
    (hdiff : ∀ z ∈ Metric.ball (0 : ℂ) r \ {(0 : ℂ)}, DifferentiableAt ℂ g z) :
    circleIntegral g 0 r = 0 := by
  have hs : ({(0 : ℂ)} : Set ℂ).Countable := countable_singleton _
  have hd : ∀ z ∈ Metric.ball (0 : ℂ) r \ {(0 : ℂ)},
      DifferentiableAt ℂ (Function.update g 0 w) z := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz.2
    refine (hdiff z hz).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hz0] with x hx
    exact Function.update_of_ne (by simpa using hx) w g
  have hzero : circleIntegral (Function.update g 0 w) 0 r = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le hs hcont hd
  have heq : EqOn g (Function.update g 0 w) (Metric.sphere 0 r) := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      have hdist : dist z (0 : ℂ) = r := hz
      rw [h, dist_self] at hdist
      exact hr.ne' hdist.symm
    rw [Function.update_of_ne hz0]
  calc circleIntegral g 0 r = circleIntegral (Function.update g 0 w) 0 r :=
        circleIntegral.integral_congr hr.le heq
    _ = 0 := hzero

/-- PROVED, P0014 page 33, display 4.7: Cauchy's theorem for a removable singularity. If `g` is
holomorphic on the closed punctured disc of radius `r` about 0 and meromorphic at 0 with
nonnegative order there, its circle integral about 0 vanishes. Riemann's removable singularity
step `MeromorphicAt.meromorphicOrderAt_nonneg_iff` gives a function `G` analytic at 0 and equal
to `g` off 0; then `Function.update g 0 (G 0)` is continuous on the closed disc, and
`circleIntegral_eq_zero_of_punctured` applies to it. -/
theorem circle_removable {g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (Metric.closedBall 0 r \ {0})) (hm : MeromorphicAt g 0)
    (h0 : 0 ≤ meromorphicOrderAt g 0) : circleIntegral g 0 r = 0 := by
  obtain ⟨G, hGan, hGg⟩ := (MeromorphicAt.meromorphicOrderAt_nonneg_iff hm).1 h0
  set w : ℂ := G 0 with hw
  have hGc : ContinuousAt G 0 := hGan.continuousAt
  have hupd : Function.update g 0 w =ᶠ[𝓝 (0 : ℂ)] G := by
    rw [show 𝓝 (0 : ℂ) = 𝓝[≠] (0 : ℂ) ⊔ pure (0 : ℂ) from (nhdsNE_sup_pure (0 : ℂ)).symm]
    show ∀ᶠ y in (𝓝[≠] (0 : ℂ) ⊔ pure (0 : ℂ)), Function.update g 0 w y = G y
    rw [eventually_sup]
    constructor
    · filter_upwards [hGg, self_mem_nhdsWithin] with y hEq hy
      rw [Function.update_of_ne (by simpa using hy)]
      exact hEq
    · simp [hw]
  have hcont0 : ContinuousAt (Function.update g 0 w) 0 := hGc.congr hupd.symm
  have h1 : ContinuousOn (Function.update g 0 w) (Metric.closedBall 0 r \ {0}) := by
    refine hg.continuousOn.congr ?_
    intro z hz
    exact Function.update_of_ne (by simpa using hz.2) w g
  have hcont : ContinuousOn (Function.update g 0 w) (Metric.closedBall 0 r) := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · exact hcont0.continuousWithinAt
    · have hc1 : ContinuousWithinAt (Function.update g 0 w) (Metric.closedBall 0 r \ {0}) z :=
        h1 z ⟨hz, by simpa using hz0⟩
      refine ContinuousWithinAt.mono_of_mem_nhdsWithin hc1 ?_
      rw [Metric.mem_nhdsWithin_iff]
      refine ⟨‖z‖, norm_pos_iff.mpr hz0, ?_⟩
      rintro x ⟨hx1, hx2⟩
      refine ⟨hx2, ?_⟩
      intro hx0
      rw [hx0] at hx1
      simp at hx1
  have hdiff : ∀ z ∈ Metric.ball (0 : ℂ) r \ {(0 : ℂ)}, DifferentiableAt ℂ g z := by
    intro z hz
    have hcl : Metric.closedBall (0 : ℂ) r ∈ 𝓝 z :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz.1) Metric.ball_subset_closedBall
    have hz0 : z ≠ 0 := by simpa using hz.2
    have hcl' : Metric.closedBall (0 : ℂ) r \ {0} ∈ 𝓝 z := by
      have : ({0} : Set ℂ)ᶜ ∈ 𝓝 z := isOpen_compl_singleton.mem_nhds (by simpa using hz0)
      simpa [Set.sdiff_eq] using Filter.inter_mem hcl this
    exact hg.differentiableAt hcl'
  exact circleIntegral_eq_zero_of_punctured hr w hcont hdiff

/-- PROVED. P0014 page 33, display 4.7, the circle integral of the principal part:
∮ s^(-(k+1)) ds over |s| = r is 2πi for k = 0 and 0 for k ≥ 1, from
`circleIntegral.integral_sub_zpow_of_ne` and `circleIntegral.integral_sub_center_inv`, with
linearity over the finite sum. -/
theorem circle_integral_principal (N : ℕ) (a : ℕ → ℂ) {r : ℝ} (hr : 0 < r) :
    circleIntegral (PP N, a) 0 r =
      2 * π * Complex.I * ∑ k ∈ Finset.range N, if k = 0 then a k else 0 := by
  have hsph : ∀ s ∈ Metric.sphere (0 : ℂ) r, s ≠ 0 := by
    intro s hs h0
    rw [h0, mem_sphere_iff_norm, sub_zero, norm_zero] at hs
    linarith
  have hint : ∀ M : ℕ, CircleIntegrable (PP M, a) 0 r := fun M =>
    ContinuousOn.circleIntegrable hr.le (fun s hs =>
      (principal_differentiableAt M a (hsph s hs)).continuousAt.continuousWithinAt)
  have hti : ∀ k : ℕ, CircleIntegrable (fun s : ℂ => a k * s ^ (-((k : ℤ) + 1))) 0 r :=
    fun k => ContinuousOn.circleIntegrable hr.le (fun s hs =>
      ((differentiableAt_zpow.mpr (Or.inl (hsph s hs))).const_mul (a k)
        ).continuousAt.continuousWithinAt)
  have hterm : ∀ k : ℕ, circleIntegral (fun s : ℂ => a k * s ^ (-((k : ℤ) + 1))) 0 r =
      2 * π * Complex.I * (if k = 0 then a k else 0) := by
    intro k
    rw [circleIntegral.integral_const_mul]
    rcases eq_or_ne k 0 with rfl | hk
    · have h := circleIntegral.integral_sub_center_inv (0 : ℂ) hr.ne'
      simp only [sub_zero] at h
      simp only [Nat.cast_zero, zero_add, zpow_neg_one, if_true, h]
      ring
    · have h := circleIntegral.integral_sub_zpow_of_ne (n := -((k : ℤ) + 1))
        (by omega) (0 : ℂ) 0 r
      simp only [sub_zero] at h
      rw [h, if_neg hk]
      ring
  induction N with
  | zero => simp [circleIntegral]
  | succ n ih =>
    have hsplit : (PP (n + 1), a) = fun s : ℂ =>
        (∑ k ∈ Finset.range n, a k * s ^ (-((k : ℤ) + 1))) + a n * s ^ (-((n : ℤ) + 1)) := by
      funext s; rw [Finset.sum_range_succ]
    rw [hsplit, circleIntegral.integral_add (hint n) (hti n), ih, hterm n,
      Finset.sum_range_succ]
    ring

/-- LEAF: P0014 page 33, display 4.7, the rectangle integral of the principal part, for a
rectangle with 0 strictly inside: the normalized rectangle integral of s^(-(k+1)) is 1 for
k = 0 and 0 for k ≥ 1. MEDIUM: for k = 0, `RectanglePullToNhdOfPole` and the residue 1 of
1/s, or the explicit side integrals of 1/s; for k ≥ 1, s^(-k)/(-k) is a primitive on the
border, so each side is a difference of values and the four differences cancel. -/
theorem rect_integral_principal (N : ℕ) (a : ℕ → ℂ) {z w : ℂ} {r : ℝ} (hr : 0 < r)
    (hzr : z.re < -r) (hzi : z.im < -r) (hwr : r < w.re) (hwi : r < w.im) :
    RectangleIntegral' (PP N, a) z w = ∑ k ∈ Finset.range N, if k = 0 then a k else 0 := by
  sorry

/-- PROVED, P0014 page 33, display 4.7, used for the rectangle side integrals: if two functions
agree on a set codiscrete within `R` and a non-constant analytic path maps `[a, b]` into `R`,
their integrals along the path agree. The argument of the private
`intervalIntegral_congr_ae_of_codiscreteWithin_along_path` of PNTPort ResidueCalcOnRectangles,
restated here because that lemma is private. -/
theorem intervalIntegral_congr_codiscrete_along_path {f g : ℂ → ℂ} {R : Set ℂ}
    (heq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    {a b : ℝ} {p : ℝ → ℂ}
    (hp_an : AnalyticOnNhd ℝ p (Set.uIcc a b))
    (hp_nonconst : ∀ x ∈ Set.uIcc a b, ¬Filter.EventuallyConst p (𝓝 x))
    (hp_maps : Set.MapsTo p (Set.uIcc a b) R) :
    ∫ x in a..b, f (p x) = ∫ x in a..b, g (p x) := by
  refine intervalIntegral.integral_congr_ae_restrict (μ := volume) ?_
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  change {x : ℝ | f (p x) = g (p x)} ∈ Filter.codiscreteWithin (Set.uIoc a b)
  simpa [Set.preimage] using Filter.codiscreteWithin_mono Set.uIoc_subset_uIcc
    (hp_an.preimage_mem_codiscreteWithin hp_nonconst
      (Filter.codiscreteWithin_mono
        (by intro s hs; rcases hs with ⟨x, hx, rfl⟩; exact hp_maps hx) heq))

/-- PROVED. Horizontal paths `x ↦ x + h i` are nowhere locally constant. -/
theorem horizontalPath_not_eventuallyConst' (h : ℝ) (x : ℝ) :
    ¬Filter.EventuallyConst (fun r : ℝ ↦ (r : ℂ) + (h : ℂ) * Complex.I) (𝓝 x) := by
  intro hc
  obtain ⟨c, hc⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.1 hc
  have hpath : HasDerivAt (fun r : ℝ ↦ (r : ℂ) + (h : ℂ) * Complex.I) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((h : ℂ) * Complex.I)
  have hconst : HasDerivAt (fun r : ℝ ↦ (r : ℂ) + (h : ℂ) * Complex.I) 0 x :=
    (hasDerivAt_const x c).congr_of_eventuallyEq hc
  exact one_ne_zero (hpath.unique hconst)

/-- PROVED, P0014 page 33, display 4.7: the rectangle integral only sees a function up to a set
codiscrete within the closed rectangle, since each side meets the complement in a null set. -/
theorem rectangleIntegral_congr_codiscrete {f g : ℂ → ℂ} {z w : ℂ}
    (h : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin (Complex.Rectangle z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  have hH : ∀ c : ℝ, (∀ x ∈ Set.uIcc z.re w.re, (↑x + ↑c * Complex.I) ∈ Complex.Rectangle z w) →
      HIntegral f z.re w.re c = HIntegral g z.re w.re c := fun c hm => by
    unfold HIntegral
    exact intervalIntegral_congr_codiscrete_along_path h
      (by intro x _; exact (Complex.ofRealCLM.analyticAt x).add analyticAt_const)
      (fun x _ ↦ horizontalPath_not_eventuallyConst' c x) hm
  have hV : ∀ c : ℝ, (∀ y ∈ Set.uIcc z.im w.im, (↑c + ↑y * Complex.I) ∈ Complex.Rectangle z w) →
      VIntegral f c z.im w.im = VIntegral g c z.im w.im := fun c hm => by
    unfold VIntegral; congr 1
    exact intervalIntegral_congr_codiscrete_along_path h
      (by intro y _; exact analyticAt_const.add ((Complex.ofRealCLM.analyticAt y).mul analyticAt_const))
      (fun x _ ↦ verticalPath_not_eventuallyConst c x) hm
  unfold RectangleIntegral
  rw [hH z.im (mapsTo_rectangle_left_im z w), hH w.im (mapsTo_rectangle_right_im z w),
    hV w.re (mapsTo_rectangle_right_re z w), hV z.re (mapsTo_rectangle_left_re z w)]

/-- PROVED. With z.re < 0 < w.re, the origin is not on the rectangle border. -/
theorem zero_not_mem_border {z w : ℂ} (hzr : z.re < 0) (hzi : z.im < 0) (hwr : 0 < w.re)
    (hwi : 0 < w.im) : (0 : ℂ) ∉ RectangleBorder z w := by
  rintro (((h | h) | h) | h) <;>
    simp only [Complex.mem_reProdIm, Set.mem_singleton_iff, Complex.zero_re,
      Complex.zero_im] at h <;> obtain ⟨h1, h2⟩ := h <;> linarith

/-- PROVED. Off 0 the principal part is analytic. -/
theorem principal_analyticAt (N : ℕ) (a : ℕ → ℂ) {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ (PP N, a) s :=
  DifferentiableOn.analyticAt (s := {0}ᶜ)
    (fun _ ht => (principal_differentiableAt N a ht).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)

/-- PROVED here, burst-20261122 unit P1122-0051, formerly a LEAF. P0014 page 33, display 4.7,
linearity of the rectangle integral: subtracting the principal part splits the rectangle
integral. Proof plan, as followed: P is continuous on the border, which
avoids 0; f has no pole on the border, so along each side it agrees off a finite set with a
continuous function, as in the private `intervalIntegral_congr_ae_of_codiscreteWithin_along_path`
of ResidueCalcOnRectangles; then `intervalIntegral.integral_sub` on the four sides. -/
theorem rect_integral_add_principal {f : ℂ → ℂ} {z w : ℂ} {r : ℝ} (hr : 0 < r)
    (hzr : z.re < -r) (hzi : z.im < -r) (hwr : r < w.re) (hwi : r < w.im)
    (hmero : MeromorphicOn f (Complex.Rectangle z w))
    (hbd : Disjoint (RectangleBorder z w) {p | meromorphicOrderAt f p < 0}) (N : ℕ)
    (a : ℕ → ℂ) :
    RectangleIntegral' f z w =
      RectangleIntegral' (f - PP N, a) z w + RectangleIntegral' (PP N, a) z w := by
  set P : ℂ → ℂ := PP N, a with hPdef
  set F : ℂ → ℂ := toMeromorphicNFOn f (Complex.Rectangle z w) with hFdef
  have h0B := zero_not_mem_border (z := z) (w := w) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have hPc : ContinuousOn P (RectangleBorder z w) := fun s hs =>
    (principal_differentiableAt N a (fun h => h0B (h ▸ hs))).continuousAt.continuousWithinAt
  have hFc : ContinuousOn F (RectangleBorder z w) := fun s hs => by
    have hsR : s ∈ Complex.Rectangle z w := rectangleBorder_subset_rectangle z w hs
    have hnf := meromorphicNFOn_toMeromorphicNFOn (f := f) (U := Complex.Rectangle z w) hsR
    have hord : 0 ≤ meromorphicOrderAt F s := by
      rw [hFdef, meromorphicOrderAt_toMeromorphicNFOn hmero hsR]
      exact not_lt.1 (fun h => Set.disjoint_left.1 hbd hs h)
    exact (hnf.meromorphicOrderAt_nonneg_iff_analyticAt.1 hord).continuousAt.continuousWithinAt
  have hcod : {s : ℂ | f s = F s} ∈ Filter.codiscreteWithin (Complex.Rectangle z w) :=
    toMeromorphicNFOn_eqOn_codiscrete hmero
  have hcod2 : {s : ℂ | (f - P) s = (F - P) s} ∈ Filter.codiscreteWithin (Complex.Rectangle z w) :=
    Filter.mem_of_superset hcod (fun s hs => by
      simp only [Set.mem_setOf_eq, Pi.sub_apply] at hs ⊢
      rw [hs])
  have e1 := rectangleIntegral_congr_codiscrete hcod
  have e2 := rectangleIntegral_congr_codiscrete hcod2
  have hadd := RectangleBorderIntegrable.add (hFc.sub hPc).rectangleBorder_integrable
    hPc.rectangleBorder_integrable
  rw [sub_add_cancel] at hadd
  simp only [RectangleIntegral']
  rw [e1, e2, hadd, smul_add]

/-- PROVED here, burst-20261122 unit P1122-0052, formerly a LEAF. P0014 page 33, display 4.7,
the residue formula for f - P. With the principal part at 0 removed, f - P is meromorphic on the
rectangle with finitely many poles, none on the border, all simple, and its poles and residues
are those of f away from 0. Proof plan, as followed: apply
`RectangleIntegral'_eq_sumResiduesIn` to f - P; off 0, P is analytic, so the order of f - P
equals that of f where f has a pole and (s - p)P(s) → 0 gives equal residues;
`sumResiduesIn_inter_eq_of_set_eq` for the index sets. -/
theorem rect_residue_sub_principal {f : ℂ → ℂ} {z w : ℂ} {r : ℝ} (hr : 0 < r)
    (hzr : z.re < -r) (hzi : z.im < -r) (hwr : r < w.re) (hwi : r < w.im)
    (hmero : MeromorphicOn f (Complex.Rectangle z w))
    (hbd : Disjoint (RectangleBorder z w) {p | meromorphicOrderAt f p < 0})
    (hfin : (Complex.Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}).Finite)
    (hsimple : HasSimplePolesOn f (Complex.Rectangle z w \ {0})) (N : ℕ) (a : ℕ → ℂ)
    (hPm : MeromorphicAt (f - PP N, a) 0) (hP0 : 0 ≤ meromorphicOrderAt (f - PP N, a) 0) :
    RectangleIntegral' (f - PP N, a) z w =
      sumResiduesIn f ((Complex.Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}) \ {0}) := by
  set P : ℂ → ℂ := PP N, a with hPdef
  set R : Set ℂ := Complex.Rectangle z w with hRdef
  have h0B := zero_not_mem_border (z := z) (w := w) (by linarith) (by linarith) (by linarith)
    (by linarith)
  -- off 0, subtracting the analytic P keeps a pole's order and keeps a non-pole a non-pole
  have hord : ∀ p : ℂ, p ≠ 0 → MeromorphicAt f p →
      (meromorphicOrderAt f p < 0 → meromorphicOrderAt (f - P) p = meromorphicOrderAt f p) ∧
      (0 ≤ meromorphicOrderAt f p → 0 ≤ meromorphicOrderAt (f - P) p) := by
    intro p hp hfm
    have hnan : AnalyticAt ℂ (-P) p := (principal_analyticAt N a hp).neg
    have hnn : 0 ≤ meromorphicOrderAt (-P) p := hnan.meromorphicOrderAt_nonneg
    rw [sub_eq_add_neg]
    refine ⟨fun h => meromorphicOrderAt_add_eq_left_of_lt hnan.meromorphicAt
      (lt_of_lt_of_le h hnn), fun h => le_trans (le_min h hnn)
        (meromorphicOrderAt_add hfm hnan.meromorphicAt)⟩
  have hset : R ∩ {p | meromorphicOrderAt (f - P) p < 0} =
      (R ∩ {p | meromorphicOrderAt f p < 0}) \ {0} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
    by_cases hp : p = 0
    · subst hp
      simp only [not_true_eq_false, and_false, iff_false, not_and, not_lt]
      exact fun _ => hP0
    · have hfm := hmero p
      constructor
      · rintro ⟨hpR, hg⟩
        refine ⟨⟨hpR, ?_⟩, hp⟩
        by_contra hc
        exact absurd hg (not_lt.2 ((hord p hp (hfm hpR)).2 (not_lt.1 hc)))
      · rintro ⟨⟨hpR, hf⟩, -⟩
        exact ⟨hpR, by rw [(hord p hp (hfm hpR)).1 hf]; exact hf⟩
  have hgm : MeromorphicOn (f - P) R := by
    intro p hpR
    by_cases hp : p = 0
    · subst hp; exact hPm
    · exact (hmero p hpR).sub (principal_analyticAt N a hp).meromorphicAt
  have hgbd : Disjoint (RectangleBorder z w) {p | meromorphicOrderAt (f - P) p < 0} := by
    refine Set.disjoint_left.2 fun p hpB hpg => ?_
    have hmem : p ∈ R ∩ {p | meromorphicOrderAt (f - P) p < 0} :=
      ⟨rectangleBorder_subset_rectangle z w hpB, hpg⟩
    rw [hset] at hmem
    exact Set.disjoint_left.1 hbd hpB hmem.1.2
  have hgfin : (R ∩ {p | meromorphicOrderAt (f - P) p < 0}).Finite := by
    rw [hset]; exact hfin.subset Set.diff_subset
  have hm1 : ((-1 : ℤ) : WithTop ℤ) ≤ 0 := by exact_mod_cast (show (-1 : ℤ) ≤ 0 by norm_num)
  have hgsimple : HasSimplePolesOn (f - P) R := by
    intro p hpR
    by_cases hp : p = 0
    · subst hp; exact le_trans hm1 hP0
    · by_cases hf : meromorphicOrderAt f p < 0
      · rw [(hord p hp (hmero p hpR)).1 hf]
        exact hsimple p ⟨hpR, hp⟩
      · exact le_trans hm1 ((hord p hp (hmero p hpR)).2 (not_lt.1 hf))
  have hzw1 : z.re ≤ w.re := by linarith
  have hzw2 : z.im ≤ w.im := by linarith
  have hmain := RectangleIntegral'_eq_sumResiduesIn hzw1 hzw2 hgm hgbd hgfin hgsimple
  rw [hmain, hset]
  unfold sumResiduesIn
  refine tsum_congr fun q => ?_
  obtain ⟨⟨hqR, hqneg⟩, hq0⟩ := q.2
  have hq0' : (q : ℂ) ≠ 0 := by simpa using hq0
  have hfm : MeromorphicAt f q := hmero q hqR
  have hsq : ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f q := hsimple q ⟨hqR, hq0⟩
  -- the limit of (s - q) f(s) exists, since (s - q) f(s) has order at least 0
  have hmul_mero : MeromorphicAt (fun s : ℂ ↦ (s - q) * f s) q :=
    (by fun_prop : MeromorphicAt (fun s : ℂ ↦ s - q) q).mul hfm
  have hmul_nonneg : 0 ≤ meromorphicOrderAt (fun s : ℂ ↦ (s - q) * f s) q := by
    change 0 ≤ meromorphicOrderAt ((fun s ↦ s - (q : ℂ)) * f) q
    rw [meromorphicOrderAt_mul (by fun_prop : MeromorphicAt (fun s : ℂ ↦ s - q) q) hfm,
      meromorphicOrderAt_id_sub_const]
    lift meromorphicOrderAt f q to ℤ using hqneg.ne_top with n hn
    have hn1 : (-1 : ℤ) ≤ n := by exact_mod_cast hsq
    exact_mod_cast (show (0 : ℤ) ≤ 1 + n by omega)
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hmul_mero hmul_nonneg
  have hsub : Filter.Tendsto (fun s : ℂ ↦ s - q) (𝓝[{(q : ℂ)}ᶜ] (q : ℂ)) (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.mpr (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hPt : Filter.Tendsto P (𝓝[{(q : ℂ)}ᶜ] (q : ℂ)) (𝓝 (P q)) :=
    (principal_analyticAt N a hq0').continuousAt.continuousWithinAt.tendsto
  have hgt : Filter.Tendsto (fun s : ℂ ↦ (s - q) * (f - P) s) (𝓝[{(q : ℂ)}ᶜ] (q : ℂ))
      (𝓝 (c - 0 * P q)) := by
    have := hc.sub (hsub.mul hPt)
    refine this.congr fun s => ?_
    simp only [Pi.sub_apply]; ring
  rw [residue_eq_of_tendsto hgt, residue_eq_of_tendsto hc]
  ring

/-- PROVED. Points of the closed disc of radius r about 0 lie in the rectangle when
z.re < -r, z.im < -r, r < w.re and r < w.im. -/
theorem closedBall_subset_rect {z w : ℂ} {r : ℝ} (hzr : z.re < -r) (hzi : z.im < -r)
    (hwr : r < w.re) (hwi : r < w.im) : Metric.closedBall (0 : ℂ) r ⊆ Complex.Rectangle z w := by
  intro s hs
  have hn : ‖s‖ ≤ r := by simpa using hs
  have h1 : |s.re| ≤ r := (Complex.abs_re_le_norm s).trans hn
  have h2 : |s.im| ≤ r := (Complex.abs_im_le_norm s).trans hn
  rw [abs_le] at h1 h2
  refine ⟨?_, ?_⟩
  · simp only [mem_preimage]
    rw [Set.uIcc_of_le (by linarith)]
    exact ⟨by linarith, by linarith⟩
  · simp only [mem_preimage]
    rw [Set.uIcc_of_le (by linarith)]
    exact ⟨by linarith, by linarith⟩

/-- Assembly, no sorry of its own: the exact statement of
`Prep1121ContourRect.rect_cut_origin`. P0014 page 33, display 4.7. -/
theorem rect_cut_origin_of_pieces {f : ℂ → ℂ} {z w : ℂ} {r : ℝ} (hr : 0 < r) (hzr : z.re < -r)
    (hzi : z.im < -r) (hwr : r < w.re) (hwi : r < w.im)
    (hmero : MeromorphicOn f (Complex.Rectangle z w))
    (hbd : Disjoint (RectangleBorder z w) {p | meromorphicOrderAt f p < 0})
    (hfin : (Complex.Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}).Finite)
    (hsimple : HasSimplePolesOn f (Complex.Rectangle z w \ {0}))
    (hdisc : DifferentiableOn ℂ f (Metric.closedBall 0 r \ {0})) :
    RectangleIntegral' f z w =
      (2 * π * Complex.I)⁻¹ * circleIntegral f 0 r +
        sumResiduesIn f ((Complex.Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}) \ {0}) := by
  have h0R : (0 : ℂ) ∈ Complex.Rectangle z w :=
    closedBall_subset_rect hzr hzi hwr hwi (Metric.mem_closedBall_self hr.le)
  obtain ⟨N, a, hPm, hP0⟩ := principal_part_at_origin (hmero 0 h0R)
  set P : ℂ → ℂ := PP N, a with hPdef
  have hPd : DifferentiableOn ℂ P (Metric.closedBall 0 r \ {0}) := fun s hs =>
    (principal_differentiableAt N a (by simpa only [mem_singleton_iff] using hs.2)
      ).differentiableWithinAt
  have hsph : Metric.sphere (0 : ℂ) r ⊆ Metric.closedBall 0 r \ {0} := by
    intro s hs
    refine ⟨Metric.sphere_subset_closedBall hs, ?_⟩
    intro h0
    rw [mem_singleton_iff] at h0
    rw [h0, mem_sphere_iff_norm, sub_zero, norm_zero] at hs
    linarith
  have hfc : CircleIntegrable f 0 r :=
    ContinuousOn.circleIntegrable hr.le (hdisc.continuousOn.mono hsph)
  have hPc : CircleIntegrable P 0 r :=
    ContinuousOn.circleIntegrable hr.le (hPd.continuousOn.mono hsph)
  have hcirc : circleIntegral f 0 r = circleIntegral (f - P) 0 r + circleIntegral P 0 r := by
    have h := circleIntegral.integral_sub hfc hPc
    have heq : (fun s => f s - P s) = f - P := rfl
    rw [heq] at h
    rw [h]; ring
  have hgz : circleIntegral (f - P) 0 r = 0 :=
    circle_removable hr (hdisc.sub hPd) hPm hP0
  rw [rect_integral_add_principal hr hzr hzi hwr hwi hmero hbd N a,
    rect_residue_sub_principal hr hzr hzi hwr hwi hmero hbd hfin hsimple N a hPm hP0,
    rect_integral_principal N a hr hzr hzi hwr hwi, hcirc, hgz,
    circle_integral_principal N a hr]
  have hI : (2 * π * Complex.I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero
  field_simp
  ring

end LeanLab.HelfgottMajor.Prep1121DCtCut

#print axioms LeanLab.HelfgottMajor.Prep1121DCtCut.principal_differentiableAt
#print axioms LeanLab.HelfgottMajor.Prep1121DCtCut.closedBall_subset_rect
#print axioms LeanLab.HelfgottMajor.Prep1121DCtCut.circle_integral_principal
#print axioms LeanLab.HelfgottMajor.Prep1121DCtCut.rect_cut_origin_of_pieces
#print axioms LeanLab.HelfgottMajor.Prep1121DCtCut.rectangleIntegral_congr_codiscrete
#print axioms LeanLab.HelfgottMajor.Prep1121DCtCut.principal_analyticAt
#print axioms LeanLab.HelfgottMajor.Prep1121DCtCut.rect_integral_add_principal
#print axioms LeanLab.HelfgottMajor.Prep1121DCtCut.rect_residue_sub_principal
