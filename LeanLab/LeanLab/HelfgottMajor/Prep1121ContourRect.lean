import LeanLab.HelfgottMajor.MainLemma41Split123
import LeanLab.PNTPort.StrongPNT.ResidueCalcOnRectangles
import LeanLab.Linnik.ExplicitFormula.Residues
import LeanLab.Linnik.ExplicitFormula.LeftHalf

/-!
PREP split 2026-11-21, session CLAUDE-prep1121, route step
`MainLemma41Split123.contour_shift`, the rectangle part.

P0014 Helfgott, Major arcs for Goldbach's problem, arXiv 1305.2897v4, proof of Lemma 4.1,
page 33, display 4.7: "We shift the line of integration in (4.4) to Re s = -1/2". On one
rectangle [-1/2, 2] × [-T', T'] whose horizontal sides avoid the zeros of L(s, χ), the
residue formula gives the four sides as the residue R at s = 0, taken as a circle integral,
plus the residues m(ρ) G_δ(ρ) x^ρ at the non-trivial zeros. For even χ the pole at 0 is
double, so the PNTPort residue formula for simple poles, `RectangleIntegral'_eq_sumResiduesIn`,
is used after the disc about 0 is cut out, leaf `rect_cut_origin`.

The final result `rect_identity` is the rectangle step used by
`Prep1121ContourShift.contour_shift_of_leaves`, with no sorry of its own.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121ContourRect
open Real MeasureTheory Set Filter LeanLab.HelfgottArcs LeanLab.HelfgottMajor.SplitGaussian123
open LeanLab.HelfgottMajor.MainLemma41Split123
open scoped Topology Interval

/-- The corners of the rectangle [-1/2, 2] × [-T', T'] of display 4.7, page 33. -/
local notation "zc" T' => (⟨-1 / 2, -T'⟩ : ℂ)
local notation "wc" T' => (⟨2, T'⟩ : ℂ)

/-! ## Private helpers: the continued Mellin factor `G_δ = contMellin δ`

P0014 page 32, displays 4.6 and 4.14: `contMellin δ` equals the explicit continued Gaussian
`Contour457.continuedGaussian δ` on `Re s > -1`, which is a quotient of two shifted Gaussian
Mellin transforms by `s`. Hence `G_δ` is meromorphic in `Re s > -1`, with a simple pole at 0 as
its only singularity, and holomorphic off 0. -/

/-- P0014 page 32: `contMellin δ = G_δ` agrees with `continuedGaussian δ` near any point of
`Re s > -1`. -/
private lemma contMellin_eventuallyEq_continuedGaussian (δ : ℝ) {z : ℂ} (hz : -1 < z.re) :
    contMellin δ =ᶠ[𝓝 z] LeanLab.HelfgottMajor.Contour457.continuedGaussian δ := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
  exact LeanLab.HelfgottMajor.Route669.contMellin_eq δ w hw

/-- `Re (z + 2) > 0` when `Re z > -1`. -/
private lemma re_add_two_pos {z : ℂ} (hz : -1 < z.re) : 0 < (z + 2).re := by
  have h : (z + 2).re = z.re + 2 := by simp
  linarith

/-- `Re (z + 1) > 0` when `Re z > -1`. -/
private lemma re_add_one_pos {z : ℂ} (hz : -1 < z.re) : 0 < (z + 1).re := by
  have h : (z + 1).re = z.re + 1 := by simp
  linarith

/-- The explicit continued Gaussian `G_δ` is differentiable at `z` for `Re z > -1`, `z ≠ 0`:
numerator holomorphic, quotient by `s`. -/
private lemma differentiableAt_continuedGaussian (δ : ℝ) {z : ℂ} (hz : -1 < z.re)
    (hz0 : z ≠ 0) :
    DifferentiableAt ℂ (LeanLab.HelfgottMajor.Contour457.continuedGaussian δ) z := by
  have h2 : DifferentiableAt ℂ (fun s : ℂ => gaussianMellin δ (s + 2)) z :=
    (LeanLab.HelfgottMajor.Continuation457.gaussian_mellin_differentiable δ (z + 2)
      (re_add_two_pos hz)).comp z (differentiableAt_id.add_const 2)
  have h1 : DifferentiableAt ℂ (fun s : ℂ => gaussianMellin δ (s + 1)) z :=
    (LeanLab.HelfgottMajor.Continuation457.gaussian_mellin_differentiable δ (z + 1)
      (re_add_one_pos hz)).comp z (differentiableAt_id.add_const 1)
  unfold LeanLab.HelfgottMajor.Contour457.continuedGaussian
  exact (h2.sub (h1.const_mul _)).div differentiableAt_id hz0

/-- `G_δ` is meromorphic in `Re s > -1`. -/
private lemma meromorphicAt_continuedGaussian (δ : ℝ) {z : ℂ} (hz : -1 < z.re) :
    MeromorphicAt (LeanLab.HelfgottMajor.Contour457.continuedGaussian δ) z := by
  have hnum : MeromorphicAt (fun s : ℂ => gaussianMellin δ (s + 2) -
      (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)) z := by
    have h2 : MeromorphicAt (fun s : ℂ => gaussianMellin δ (s + 2)) z := by
      have hd : DifferentiableOn ℂ (fun s : ℂ => gaussianMellin δ (s + 2))
          {w : ℂ | -1 < w.re} :=
        fun w hw => ((LeanLab.HelfgottMajor.Continuation457.gaussian_mellin_differentiable δ
          (w + 2) (re_add_two_pos hw)).comp w (differentiableAt_id.add_const 2)
          ).differentiableWithinAt
      exact (hd.analyticAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)).meromorphicAt
    have h1 : MeromorphicAt (fun s : ℂ => gaussianMellin δ (s + 1)) z := by
      have hd : DifferentiableOn ℂ (fun s : ℂ => gaussianMellin δ (s + 1))
          {w : ℂ | -1 < w.re} :=
        fun w hw => ((LeanLab.HelfgottMajor.Continuation457.gaussian_mellin_differentiable δ
          (w + 1) (re_add_one_pos hw)).comp w (differentiableAt_id.add_const 1)
          ).differentiableWithinAt
      exact (hd.analyticAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)).meromorphicAt
    have hc : MeromorphicAt (fun s : ℂ =>
        (2 * π * Complex.I * δ) * gaussianMellin δ (s + 1)) z :=
      h1.const_smul (2 * π * Complex.I * δ)
    exact h2.sub hc
  unfold LeanLab.HelfgottMajor.Contour457.continuedGaussian
  exact hnum.div (MeromorphicAt.id z)

/-- `contMellin δ` is meromorphic in `Re s > -1`: a simple pole at 0, holomorphic elsewhere. -/
private lemma meromorphicAt_contMellin (δ : ℝ) {z : ℂ} (hz : -1 < z.re) :
    MeromorphicAt (contMellin δ) z :=
  (meromorphicAt_continuedGaussian δ hz).congr
    ((contMellin_eventuallyEq_continuedGaussian δ hz).filter_mono nhdsWithin_le_nhds).symm

/-- `contMellin δ` is holomorphic off `0` in `Re s > -1`. -/
private lemma analyticAt_contMellin (δ : ℝ) {z : ℂ} (hz : -1 < z.re) (hz0 : z ≠ 0) :
    AnalyticAt ℂ (contMellin δ) z := by
  have hd : DifferentiableOn ℂ (LeanLab.HelfgottMajor.Contour457.continuedGaussian δ)
      {w : ℂ | -1 < w.re ∧ w ≠ 0} :=
    fun w hw => (differentiableAt_continuedGaussian δ hw.1 hw.2).differentiableWithinAt
  have hmem : {w : ℂ | -1 < w.re ∧ w ≠ 0} ∈ 𝓝 z :=
    inter_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
      (isOpen_ne.mem_nhds hz0)
  exact (hd.analyticAt hmem).congr
    (show LeanLab.HelfgottMajor.Contour457.continuedGaussian δ =ᶠ[𝓝 z] contMellin δ from
      (contMellin_eventuallyEq_continuedGaussian δ hz).symm)

/-- Membership in `[-1/2, 2] × [-T', T']` bounds the imaginary part, for `T' ≥ 0`. -/
private lemma im_abs_le_of_mem_rect {T' : ℝ} (hT : 0 ≤ T') {z : ℂ}
    (hz : z ∈ Complex.Rectangle (zc T') (wc T')) : |z.im| ≤ T' := by
  have h := (Complex.mem_reProdIm.mp hz).2
  rw [Set.mem_uIcc] at h
  rcases h with h | h
  · exact abs_le.mpr ⟨h.1, h.2⟩
  · exact abs_le.mpr ⟨by linarith [h.1, h.2, hT], by linarith [h.1, h.2, hT]⟩

/-- Membership in `[-1/2, 2] × [-T', T']` bounds the real part, for any `T'`. -/
private lemma re_bounds_of_mem_rect {T' : ℝ} {z : ℂ}
    (hz : z ∈ Complex.Rectangle (zc T') (wc T')) : (-1 / 2 : ℝ) ≤ z.re ∧ z.re ≤ 2 := by
  have h := (Complex.mem_reProdIm.mp hz).1
  rw [Set.mem_uIcc] at h
  rcases h with h | h <;> constructor <;> linarith [h.1, h.2]

/-- `x^s` is meromorphic everywhere for `x > 0`. -/
private lemma meromorphicAt_cpow_const {x : ℝ} (hx : 0 < x) (z : ℂ) :
    MeromorphicAt (fun s : ℂ => (x : ℂ) ^ s) z :=
  (analyticAt_const.cpow analyticAt_id (Complex.ofReal_mem_slitPlane.mpr hx)).meromorphicAt

/-- The contour integrand is meromorphic in `Re s > -1`, as a product of three meromorphic
factors. -/
private lemma meromorphicAt_contourIntegrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {z : ℂ} (hz : -1 < z.re) :
    MeromorphicAt (contourIntegrand χ δ x) z := by
  have hL := Linnik.ExplicitFormula.meromorphicAt_LFunction χ z
  have hA : MeromorphicAt (fun s : ℂ =>
      deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) z :=
    hL.deriv.div hL
  have hG : MeromorphicAt (contMellin δ) z := meromorphicAt_contMellin δ hz
  have hX : MeromorphicAt (fun s : ℂ => (x : ℂ) ^ s) z :=
    meromorphicAt_cpow_const (by linarith : (0 : ℝ) < x) z
  have h : MeromorphicAt ((fun s : ℂ =>
      deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) *
      contMellin δ * fun s : ℂ => (x : ℂ) ^ s) z := (hA.mul hG).mul hX
  unfold contourIntegrand
  exact h

/-- Off the zeros of `L(s, χ)` the contour integrand is holomorphic, in `Re s > -1`. -/
private lemma analyticAt_contourIntegrand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {z : ℂ} (hz : -1 < z.re) (hz0 : z ≠ 0)
    (h1 : z ≠ 1 ∨ χ ≠ 1) (hLz : χ.LFunction z ≠ 0) :
    AnalyticAt ℂ (contourIntegrand χ δ x) z := by
  have hA : AnalyticAt ℂ (DirichletCharacter.LFunction χ) z :=
    Linnik.ExplicitFormula.analyticAt_LFunction χ h1
  have hlog : AnalyticAt ℂ (fun s : ℂ =>
      deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) z :=
    hA.deriv.div hA hLz
  have hG : AnalyticAt ℂ (contMellin δ) z := analyticAt_contMellin δ hz hz0
  have hX : AnalyticAt ℂ (fun s : ℂ => (x : ℂ) ^ s) z :=
    analyticAt_const.cpow analyticAt_id (Complex.ofReal_mem_slitPlane.mpr (by linarith : (0:ℝ) < x))
  have h : AnalyticAt ℂ ((fun s : ℂ =>
      deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) *
      contMellin δ * fun s : ℂ => (x : ℂ) ^ s) z := (hlog.mul hG).mul hX
  unfold contourIntegrand
  exact h

/-- PROVED. P0014 page 33, display 4.7: the four sides of the rectangle, right side up, left
side down, bottom and top, over 2πi, are the PNTPort normalized rectangle integral. With
s = σ + iτ, (1/2πi) ∫ ds on a vertical side is (1/2π) ∫ dτ. -/
theorem rect_sides_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (δ x T' : ℝ) :
    (2 * π : ℂ)⁻¹ * (∫ τ in -T'..T', contourIntegrand χ δ x ((2 : ℂ) + τ * Complex.I)) -
        (2 * π : ℂ)⁻¹ * (∫ τ in -T'..T', contourIntegrand χ δ x (-1 / 2 + τ * Complex.I)) +
        (2 * π * Complex.I)⁻¹ *
          ((∫ σ in (-1 / 2 : ℝ)..2,
              contourIntegrand χ δ x ((σ : ℂ) + ((-T' : ℝ) : ℂ) * Complex.I)) -
            ∫ σ in (-1 / 2 : ℝ)..2,
              contourIntegrand χ δ x ((σ : ℂ) + (T' : ℂ) * Complex.I)) =
      RectangleIntegral' (contourIntegrand χ δ x) (zc T') (wc T') := by
  simp only [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
  have h2 : ((2 : ℝ) : ℂ) = (2 : ℂ) := by norm_num
  have hh : ((-1 / 2 : ℝ) : ℂ) = (-1 / 2 : ℂ) := by push_cast; ring
  rw [h2, hh]
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- LEAF: P0014 page 33, display 4.7, the shift past the double pole at s = 0. A function
meromorphic on a rectangle with finitely many poles, none on the border, simple poles away
from 0, and holomorphic on a closed punctured disc about 0 inside the rectangle: its
normalized rectangle integral is the circle integral about 0 over 2πi plus the residues at
the other poles. HARD: subtract the principal part Σ a_k s^(-k) at 0, whose rectangle and
circle integrals agree, `circleIntegral.integral_sub_zpow_of_ne` and the antiderivative of
s^(-k) for k ≥ 2, then apply `RectangleIntegral'_eq_sumResiduesIn` to the rest. Generic
complex analysis, no L-function. -/
theorem rect_cut_origin {f : ℂ → ℂ} {z w : ℂ} {r : ℝ} (hr : 0 < r) (hzr : z.re < -r)
    (hzi : z.im < -r) (hwr : r < w.re) (hwi : r < w.im)
    (hmero : MeromorphicOn f (Complex.Rectangle z w))
    (hbd : Disjoint (RectangleBorder z w) {p | meromorphicOrderAt f p < 0})
    (hfin : (Complex.Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}).Finite)
    (hsimple : HasSimplePolesOn f (Complex.Rectangle z w \ {0}))
    (hdisc : DifferentiableOn ℂ f (Metric.closedBall 0 r \ {0})) :
    RectangleIntegral' f z w =
      (2 * π * Complex.I)⁻¹ * circleIntegral f 0 r +
        sumResiduesIn f ((Complex.Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}) \ {0}) := by
  sorry

/-- LEAF: P0014 page 32, the continuation of G_δ by display 4.14, with page 33, display 4.7.
For primitive χ of conductor q above 1, F(s) = L'/L(s, χ) G_δ(s) x^s is meromorphic on the
rectangle [-1/2, 2] × [-T', T']: L is entire, G_δ = contMellin = M(-t f'(t))(s)/s with the
Mellin transform holomorphic on Re s above -1, and x^s is entire. MEDIUM: products and
quotients of analytic functions, `Linnik.ExplicitFormula.analyticAt_LFunction`. -/
theorem integrand_meromorphicOn {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) (T' : ℝ) :
    MeromorphicOn (contourIntegrand χ δ x) (Complex.Rectangle (zc T') (wc T')) := by
  intro z hz
  exact meromorphicAt_contourIntegrand χ δ hx (by
    have h := (re_bounds_of_mem_rect hz).1
    linarith)

/-- P0014 page 33, display 4.7, the zero part of the pole analysis: a pole of `F` in the
rectangle off the origin is a nontrivial zero of `L(s, χ)`. Off the zeros of `L` the integrand
is holomorphic (`analyticAt_contourIntegrand`), so the order there is nonnegative, and
`Linnik.ExplicitFormula.zero_left_strip` and Mathlib's nonvanishing on `Re s ≥ 1` give the
location. -/
private lemma LFunction_eq_zero_of_pole {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {T' : ℝ} {p : ℂ}
    (hp : p ∈ Complex.Rectangle (zc T') (wc T')) (hp0 : p ≠ 0)
    (hneg : meromorphicOrderAt (contourIntegrand χ δ x) p < 0) :
    χ.LFunction p = 0 ∧ 0 < p.re ∧ p.re < 1 := by
  have hre := re_bounds_of_mem_rect hp
  have hne : χ ≠ 1 := Linnik.ExplicitFormula.ne_one_of_isPrimitive hχ hq
  have hLzero : χ.LFunction p = 0 := by
    by_contra hL
    have hAna := analyticAt_contourIntegrand χ δ hx (by linarith [hre.1]) hp0
      (Or.inr hne) hL
    exact absurd hAna.meromorphicOrderAt_nonneg (not_le.mpr hneg)
  refine ⟨hLzero, ?_, ?_⟩
  · by_cases h : p.re ≤ 0
    · have hz := Linnik.ExplicitFormula.zero_left_strip hχ hLzero (by linarith [hre.1]) h
      exact absurd hz hp0
    · push Not at h
      exact h
  · rcases lt_or_ge p.re 1 with h | h
    · exact h
    · exact absurd hLzero (by
        intro h0
        exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) h h0)

/-- LEAF: P0014 page 33, display 4.7, the poles crossed by the shift. A pole p ≠ 0 of F in
the rectangle is a zero of L(s, χ) with 0 < Re p < 1 and |Im p| ≤ T': off the zeros of L,
F is holomorphic on Re s above -1 away from 0; there is no zero with Re s ≥ 1, Mathlib
`LFunction_ne_zero_of_one_le_re`, and the only zero with -1/2 ≤ Re s ≤ 0 is 0,
`Linnik.ExplicitFormula.zero_left_strip`. MEDIUM. -/
theorem poles_off_origin {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) (T' : ℝ) {p : ℂ}
    (hp : p ∈ Complex.Rectangle (zc T') (wc T')) (hp0 : p ≠ 0)
    (hneg : meromorphicOrderAt (contourIntegrand χ δ x) p < 0) :
    χ.LFunction p = 0 ∧ 0 < p.re ∧ p.re < 1 ∧ |p.im| ≤ T' := by
  sorry

/-- LEAF: P0014 page 33, display 4.7, the poles off 0 are simple. At p ≠ 0 with Re p above -1
the factor G_δ(s) x^s is holomorphic and L'/L has at most a simple pole, so the meromorphic
order of F at p is at least -1. MEDIUM: order of a logarithmic derivative,
`PNTPort.ExplicitPsi1.tendsto_mul_logDeriv_mero` or `Linnik.ExplicitFormula.order_Fchi_ge`. -/
theorem simple_poles_off_origin {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) (T' : ℝ) :
    HasSimplePolesOn (contourIntegrand χ δ x) (Complex.Rectangle (zc T') (wc T') \ {0}) := by
  intro z hz
  obtain ⟨hzR, hz0⟩ := hz
  have hzre : -1 < z.re := by have h := (re_bounds_of_mem_rect hzR).1; linarith
  have hL := Linnik.ExplicitFormula.meromorphicAt_LFunction χ z
  have hA : MeromorphicAt (logDeriv (DirichletCharacter.LFunction χ)) z := hL.deriv.div hL
  have hG : MeromorphicAt (contMellin δ) z := meromorphicAt_contMellin δ hzre
  have hX : MeromorphicAt (fun s : ℂ => (x : ℂ) ^ s) z :=
    meromorphicAt_cpow_const (by linarith : (0:ℝ) < x) z
  have hmul : meromorphicOrderAt (contourIntegrand χ δ x) z =
      meromorphicOrderAt (logDeriv (DirichletCharacter.LFunction χ)) z +
      meromorphicOrderAt (contMellin δ) z +
      meromorphicOrderAt (fun s : ℂ => (x : ℂ) ^ s) z := by
    change meromorphicOrderAt (logDeriv (DirichletCharacter.LFunction χ) * contMellin δ *
      fun s : ℂ => (x : ℂ) ^ s) z = _
    rw [meromorphicOrderAt_mul (hA.mul hG) hX, meromorphicOrderAt_mul hA hG]
  have hordA : (-1 : WithTop ℤ) ≤
      meromorphicOrderAt (logDeriv (DirichletCharacter.LFunction χ)) z := by
    by_cases h : meromorphicOrderAt (DirichletCharacter.LFunction χ) z = 0
    · refine le_trans ?_ (meromorphicOrderAt_logDeriv_nonneg hL h)
      exact WithTop.coe_le_coe.mpr (by norm_num : (-1:ℤ) ≤ 0)
    · rw [meromorphicOrderAt_logDeriv_eq_neg_one hL h
        (Linnik.ExplicitFormula.order_LFunction_ne_top hχ z)]
  have hordG : (0 : WithTop ℤ) ≤ meromorphicOrderAt (contMellin δ) z :=
    (analyticAt_contMellin δ hzre hz0).meromorphicOrderAt_nonneg
  have hordX : (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun s : ℂ => (x : ℂ) ^ s) z :=
    (analyticAt_const.cpow analyticAt_id
      (Complex.ofReal_mem_slitPlane.mpr (by linarith : (0:ℝ) < x))).meromorphicOrderAt_nonneg
  rw [hmul]
  calc (-1 : WithTop ℤ) = (-1 : WithTop ℤ) + 0 + 0 := by simp
    _ ≤ _ := add_le_add (add_le_add hordA hordG) hordX

/-- LEAF: P0014 page 31, display 4.1, with page 33, display 4.7: the residue of F at a
non-trivial zero ρ is m(ρ) G_δ(ρ) x^ρ, the zero term. L'/L has residue m(ρ) at ρ, and
G_δ = gaussianMellin on Re s above 0, `Route669.contMellin_eq_gaussianMellin`. MEDIUM: as
`Linnik.ExplicitFormula.residue_Fchi_of_ne_one` with the kernel G_δ(s) x^s. -/
theorem residue_at_zero_point {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {ρ : ℂ} (hρ : χ.LFunction ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    residue (contourIntegrand χ δ x) ρ = zeroTerm χ δ x ρ := by
  have hρ1 : ρ ≠ 1 := by rintro rfl; norm_num at h1
  have hρ0 : ρ ≠ 0 := by rintro rfl; norm_num at h0
  have hm : MeromorphicAt (DirichletCharacter.LFunction χ) ρ :=
    Linnik.ExplicitFormula.meromorphicAt_LFunction χ ρ
  have hL := LeanLab.PNTPort.ExplicitPsi1.tendsto_mul_logDeriv_mero hm
    (Linnik.ExplicitFormula.order_LFunction_of_ne_one χ hρ1)
  have hG : Tendsto (contMellin δ) (𝓝[≠] ρ) (𝓝 (contMellin δ ρ)) :=
    ((analyticAt_contMellin δ (by linarith) hρ0).continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds
  have hX : Tendsto (fun s : ℂ => (x : ℂ) ^ s) (𝓝[≠] ρ) (𝓝 ((x : ℂ) ^ ρ)) := by
    have hx0 : (x : ℂ) ≠ 0 := by
      exact_mod_cast (show (x : ℝ) ≠ 0 by linarith)
    exact (continuousAt_const_cpow hx0).tendsto.mono_left nhdsWithin_le_nhds
  have hmul := (hL.mul hG).mul hX
  have hGeq : contMellin δ ρ = gaussianMellin δ ρ :=
    LeanLab.HelfgottMajor.Route669.contMellin_eq_gaussianMellin δ ρ h0
  have hval : ((Linnik.ExplicitFormula.mult χ ρ : ℤ) : ℂ) * contMellin δ ρ * (x : ℂ) ^ ρ =
      zeroTerm χ δ x ρ := by
    rw [hGeq]
    simp only [zeroTerm, Linnik.ExplicitFormula.mult, Int.cast_natCast, nsmul_eq_mul]
    ring
  rw [hval] at hmul
  refine residue_eq_of_tendsto (c := zeroTerm χ δ x ρ) ?_
  refine Tendsto.congr (fun s => ?_) hmul
  simp only [contourIntegrand, Pi.mul_apply]
  ring

/-- LEAF: P0014 page 33, display 4.7, the residue sum is a sum over zeros. The sum of the
residues of F over its poles in the rectangle other than 0 equals the sum of residue F ρ over
the zeros ρ of L with 0 < Re ρ < 1 and |Im ρ| ≤ T': both index sets are finite, every pole is
such a zero by `poles_off_origin`, and a zero that is not a pole of F has residue 0.
MEDIUM: reindexing two finite tsums. -/
theorem residue_sum_reindex {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (δ : ℝ) {x : ℝ} (hx : 1 ≤ x) {T' : ℝ} (hT' : 1 ≤ T') :
    sumResiduesIn (contourIntegrand χ δ x)
        ((Complex.Rectangle (zc T') (wc T') ∩
          {p | meromorphicOrderAt (contourIntegrand χ δ x) p < 0}) \ {0}) =
      ∑' ρ : {ρ : ℂ // χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T'},
        residue (contourIntegrand χ δ x) ρ.val := by
  have hT0 : (0 : ℝ) ≤ T' := by linarith
  have hset : ((Complex.Rectangle (zc T') (wc T') ∩
      {p | meromorphicOrderAt (contourIntegrand χ δ x) p < 0}) \ {0}) ∩
      {p | meromorphicOrderAt (contourIntegrand χ δ x) p < 0}
      = {ρ : ℂ | χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T'} ∩
        {p | meromorphicOrderAt (contourIntegrand χ δ x) p < 0} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨⟨hzR, hzP⟩, hz0⟩, -⟩
      obtain ⟨hLz, h0z, h1z⟩ := LFunction_eq_zero_of_pole χ hχ hq δ hx hzR hz0 hzP
      have him : |z.im| ≤ T' := im_abs_le_of_mem_rect hT0 hzR
      exact ⟨⟨hLz, h0z, h1z, him⟩, hzP⟩
    · rintro ⟨⟨hL, h0, h1, him⟩, hzP⟩
      have hz0 : z ≠ 0 := by rintro rfl; simp at h0
      refine ⟨⟨⟨?_, hzP⟩, hz0⟩, hzP⟩
      have hzR' : z ∈ Complex.Rectangle (zc T') (wc T') := by
        have hm := (Complex.mem_reProdIm (z := z) (s := Set.uIcc (-1 / 2 : ℝ) 2)
          (t := Set.uIcc (-T') T'))
        refine hm.mpr ⟨?_, ?_⟩
        · rw [Set.mem_uIcc]; exact Or.inl ⟨by linarith [h0], by linarith [h1]⟩
        · rw [Set.mem_uIcc]; exact Or.inl ⟨abs_le.mp him |>.1, abs_le.mp him |>.2⟩
      exact hzR'
  have hzero : ∀ s ∈ {ρ : ℂ | χ.LFunction ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T'},
      s ∉ {p | meromorphicOrderAt (contourIntegrand χ δ x) p < 0} →
      residue (contourIntegrand χ δ x) s = 0 := by
    intro s hs hsP
    exact residue_eq_zero_of_not_pole_of_meromorphicAt
      (meromorphicAt_contourIntegrand χ δ hx (by linarith [hs.2.1])) (not_lt.mp hsP)
  have hPP : ((Complex.Rectangle (zc T') (wc T') ∩
      {p | meromorphicOrderAt (contourIntegrand χ δ x) p < 0}) \ {0}) ∩
      {p | meromorphicOrderAt (contourIntegrand χ δ x) p < 0} =
      (Complex.Rectangle (zc T') (wc T') ∩
        {p | meromorphicOrderAt (contourIntegrand χ δ x) p < 0}) \ {0} :=
    Set.inter_eq_left.mpr (fun z hz => hz.1.2)
  rw [← hPP, sumResiduesIn_inter_eq_of_set_eq (F := contourIntegrand χ δ x) hset hzero]
  rfl

/-- PROVED. Membership in the rectangle [-1/2, 2] × [-T', T']. -/
theorem mem_rect {T' : ℝ} (hT : 0 ≤ T') {p : ℂ} :
    p ∈ Complex.Rectangle (zc T') (wc T') ↔ (-1 / 2 ≤ p.re ∧ p.re ≤ 2) ∧ (-T' ≤ p.im ∧ p.im ≤ T') :=
  Linnik.ExplicitFormula.mem_rect2 (c := 2) (by norm_num) hT

/-- Assembly, no sorry of its own. P0014 page 33, display 4.7, residues on one rectangle.
For primitive χ, q above 1, T' ≥ 1 with no zero of L(s, χ) on the horizontal sides of
[-1/2, 2] × [-T', T'], and a punctured disc of radius r < 1/2 where F is holomorphic: the
rectangle integral of F over 2πi is the circle integral R over 2πi plus the zero sum
`lowZeros χ δ x T'`. -/
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
  have hT0 : (0 : ℝ) ≤ T' := by linarith
  have hmem := fun p : ℂ => mem_rect hT0 (p := p)
  -- the poles in the rectangle lie in {0} together with the non-trivial zeros
  have hpoles : ∀ p ∈ Complex.Rectangle (zc T') (wc T'),
      meromorphicOrderAt (contourIntegrand χ δ x) p < 0 →
        p = 0 ∨ (χ.LFunction p = 0 ∧ 0 < p.re ∧ p.re < 1 ∧ |p.im| ≤ T') := by
    intro p hp hneg
    by_cases hp0 : p = 0
    · exact Or.inl hp0
    · exact Or.inr (poles_off_origin χ hχ hq δ hx T' hp hp0 hneg)
  have hfin : (Complex.Rectangle (zc T') (wc T') ∩
      {p | meromorphicOrderAt (contourIntegrand χ δ x) p < 0}).Finite := by
    have hcpt : IsCompact (Complex.Rectangle (zc T') (wc T')) :=
      isCompact_uIcc.reProdIm isCompact_uIcc
    have hZ := Linnik.ExplicitFormula.zeros_compact_finite_of_ne_one
      (Linnik.ExplicitFormula.ne_one_of_isPrimitive hχ hq) hcpt
    refine ((hZ.insert 0)).subset ?_
    rintro p ⟨hp, hneg⟩
    rcases hpoles p hp hneg with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hp, by simpa using h.1⟩
  have hbd' : Disjoint (RectangleBorder (zc T') (wc T'))
      {p | meromorphicOrderAt (contourIntegrand χ δ x) p < 0} := by
    rw [Set.disjoint_left]
    intro p hpB hneg
    have hpR : p ∈ Complex.Rectangle (zc T') (wc T') := rectangleBorder_subset_rectangle _ _ hpB
    have hpR' := (hmem p).mp hpR
    rcases hpoles p hpR hneg with h0 | ⟨hL, hre0, hre1, him⟩
    · -- 0 is not on the border
      subst h0
      simp only [RectangleBorder, mem_union, Complex.mem_reProdIm, mem_singleton_iff,
        Complex.zero_re, Complex.zero_im] at hpB
      rcases hpB with ((h | h) | h) | h <;> norm_num at h <;> first | linarith | linarith [h.1, h.2]
    · simp only [RectangleBorder, mem_union, Complex.mem_reProdIm, mem_singleton_iff] at hpB
      rcases hpB with ((⟨-, h⟩ | ⟨h, -⟩) | ⟨-, h⟩) | ⟨h, -⟩
      · apply hbd p.re ⟨by linarith, by linarith⟩ (-T') (by simp)
        have : p = (p.re : ℂ) + ((-T' : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext <;> simp [h]
        rw [← this]; exact hL
      · norm_num at h; linarith
      · apply hbd p.re ⟨by linarith, by linarith⟩ T' (by simp)
        have : p = (p.re : ℂ) + (T' : ℂ) * Complex.I := by
          apply Complex.ext <;> simp [h]
        rw [← this]; exact hL
      · norm_num at h; linarith
  rw [rect_sides_eq, rect_cut_origin (z := zc T') (w := wc T') hr (by simp; linarith)
    (by simp; linarith) (by simp; linarith) (by simp; linarith)
    (integrand_meromorphicOn χ hχ hq δ hx T') hbd' hfin
    (simple_poles_off_origin χ hχ hq δ hx T') hF,
    residue_sum_reindex χ hχ hq δ hx hT']
  congr 1
  unfold lowZeros
  exact tsum_congr fun ρ => residue_at_zero_point χ hχ δ hx ρ.2.1 ρ.2.2.1 ρ.2.2.2.1

end LeanLab.HelfgottMajor.Prep1121ContourRect

#print axioms LeanLab.HelfgottMajor.Prep1121ContourRect.rect_sides_eq
#print axioms LeanLab.HelfgottMajor.Prep1121ContourRect.mem_rect
#print axioms LeanLab.HelfgottMajor.Prep1121ContourRect.rect_identity
