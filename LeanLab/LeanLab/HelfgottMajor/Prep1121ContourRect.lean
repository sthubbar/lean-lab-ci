import LeanLab.HelfgottMajor.CircleResidue669
import LeanLab.HelfgottMajor.Lemma41Kernel669
import LeanLab.HelfgottMajor.Lemma41Leaf123
import LeanLab.HelfgottMajor.Norm389
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


/-! ## Private development for the rectangle-with-disc residue theorem of display 4.7

P0014 page 33, display 4.7: the shift to `Re s = -1/2` cuts a disc about `s = 0` out of the
rectangle, because the pole of `G_δ` at `0` can be of order two. The lemmas below assemble that
step from Mathlib's Cauchy-Goursat theorem for a disc, the residue theorem for a rectangle
(`RectangleIntegral'_eq_sumResiduesIn`, already in the imports), the normal form of a meromorphic
function and the Laurent order reduction at the origin. No new definitions are introduced: every
auxiliary statement is a private theorem. -/
section RectCutPort

open Complex MeasureTheory Filter

/-- The rectangle integral of a function with an antiderivative on the border vanishes. -/
private theorem rectIntegral_eq_zero_of_hasDerivAt {f F : ℂ → ℂ} {z w : ℂ}
    (hd : ∀ s ∈ RectangleBorder z w, HasDerivAt F (f s) s)
    (hint : RectangleBorderIntegrable f z w) :
    RectangleIntegral f z w = 0 := by
  have hH : ∀ y : ℝ, (∀ x ∈ Set.uIcc z.re w.re, ((x : ℂ) + y * I) ∈ RectangleBorder z w) →
      IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + y * I)) volume z.re w.re →
      HIntegral f z.re w.re y = F ((w.re : ℂ) + y * I) - F ((z.re : ℂ) + y * I) := by
    intro y hb hy
    have hder : ∀ x ∈ Set.uIcc z.re w.re, HasDerivAt (fun x : ℝ => F ((x : ℂ) + y * I))
        (f ((x : ℂ) + y * I)) x := by
      intro x hx
      have hG := (hd _ (hb x hx)).comp_add_const ((x : ℂ)) ((y : ℂ) * I)
      have h5 := hG.comp_ofReal (z := x)
      simpa [Function.comp] using h5
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hder hy
  have hV : ∀ x : ℝ, (∀ y ∈ Set.uIcc z.im w.im, ((x : ℂ) + y * I) ∈ RectangleBorder z w) →
      IntervalIntegrable (fun y : ℝ => f ((x : ℂ) + y * I)) volume z.im w.im →
      VIntegral f x z.im w.im = F ((x : ℂ) + (w.im : ℂ) * I) - F ((x : ℂ) + (z.im : ℂ) * I) := by
    intro x hb hy
    have hder : ∀ y ∈ Set.uIcc z.im w.im, HasDerivAt (fun y : ℝ => F ((x : ℂ) + (y : ℂ) * I))
        (I * f ((x : ℂ) + (y : ℂ) * I)) y := by
      intro y hy'
      have hinner : HasDerivAt (fun z : ℂ => (x : ℂ) + z * I) I ((y : ℂ)) := by
        have h2 : HasDerivAt (fun z : ℂ => z * I) (1 * I) ((y : ℂ)) :=
          (hasDerivAt_id ((y : ℂ))).mul_const I
        have h3 : HasDerivAt (fun z : ℂ => z * I + (x : ℂ)) I ((y : ℂ)) := by
          simpa using h2.add_const (x : ℂ)
        simpa [add_comm] using h3
      have h4 := HasDerivAt.comp (x := ((y : ℂ))) (hd _ (hb y hy')) hinner
      have h5 := h4.comp_ofReal (z := y)
      simpa [Function.comp, mul_comm] using h5
    rw [VIntegral, smul_eq_mul, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hy.const_mul I)
  rw [RectangleIntegral,
    hH z.im (fun x hx => mapsTo_rectangleBorder_left_im z w hx) hint.1,
    hH w.im (fun x hx => mapsTo_rectangleBorder_right_im z w hx) hint.2.1,
    hV w.re (fun y hy => mapsTo_rectangleBorder_right_re z w hy) hint.2.2.1,
    hV z.re (fun y hy => mapsTo_rectangleBorder_left_re z w hy) hint.2.2.2]
  ring

/-- `0` is an interior point of the rectangle with the four strict inequalities. -/
private theorem rectangle_mem_nhds_zero {z w : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    Rectangle z w ∈ 𝓝 (0 : ℂ) := by
  rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm]
  refine ⟨?_, ?_⟩
  · exact Set.mem_uIoo_of_lt (by simpa using h1) (by simpa using h3)
  · exact Set.mem_uIoo_of_lt (by simpa using h2) (by simpa using h4)

/-- The circle integral of `s^{-j}`. -/
private theorem circleIntegral_zpow_neg (j : ℕ) (hj : 1 ≤ j) {r : ℝ} (hr : r ≠ 0) :
    circleIntegral (fun s : ℂ => s ^ (-(j : ℤ))) 0 r = if j = 1 then 2 * Real.pi * I else 0 := by
  rcases eq_or_ne j 1 with rfl | hj1
  · rw [if_pos rfl]
    simpa using circleIntegral.integral_sub_center_inv (c := (0 : ℂ)) hr
  · rw [if_neg hj1]
    have hn : (-(j : ℤ)) ≠ -1 := by omega
    simpa using circleIntegral.integral_sub_zpow_of_ne (c := (0 : ℂ)) (w := (0 : ℂ)) (R := r) hn

/-- The normalized rectangle integral of `s^{-1}` about the origin. -/
private theorem rectangleIntegral'_inv {z w : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral' (fun s : ℂ => s ^ (-(1 : ℤ))) z w = 1 := by
  have h0in := rectangle_mem_nhds_zero h1 h2 h3 h4
  have h := ResidueTheoremInRectangle (c := (1 : ℂ)) (p := (0 : ℂ))
    (by linarith) (by linarith) h0in
  simpa using h

/-- The normalized rectangle integral of `s^{-j}`, `j ≥ 2`, vanishes. -/
private theorem rectangleIntegral'_zpow_neg_more {z w : ℂ} {j : ℕ} (hj : 2 ≤ j)
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral' (fun s : ℂ => s ^ (-(j : ℤ))) z w = 0 := by
  have hm : ((1 : ℤ) - (j : ℤ)) ≠ 0 := by omega
  have h0in := rectangle_mem_nhds_zero h1 h2 h3 h4
  have h0b : (0 : ℂ) ∉ RectangleBorder z w := not_mem_rectangleBorder_of_rectangle_mem_nhds h0in
  have hd : ∀ s ∈ RectangleBorder z w, HasDerivAt (fun s : ℂ =>
      s ^ ((1 : ℤ) - (j : ℤ)) / ((((1 : ℤ) - (j : ℤ)) : ℤ) : ℂ)) (s ^ (-(j : ℤ))) s := by
    intro s hs
    have hs0 : s ≠ 0 := fun h => h0b (h ▸ hs)
    have h := (hasDerivAt_zpow ((1 : ℤ) - (j : ℤ)) s (Or.inl hs0)).div_const
      ((((1 : ℤ) - (j : ℤ)) : ℤ) : ℂ)
    convert h using 1
    have hexp : ((1 : ℤ) - (j : ℤ)) - 1 = -(j : ℤ) := by omega
    rw [hexp]
    field_simp
  have hint : RectangleBorderIntegrable (fun s : ℂ => s ^ (-(j : ℤ))) z w := by
    refine ContinuousOn.rectangleBorder_integrable ?_
    intro s hs
    have hs0 : s ≠ 0 := fun h => h0b (h ▸ hs)
    exact (differentiableAt_zpow.mpr (Or.inl hs0)).continuousAt.continuousWithinAt
  rw [RectangleIntegral', rectIntegral_eq_zero_of_hasDerivAt hd hint, smul_zero]




/-- Additivity of the normalized rectangle integral. -/
private theorem rectangleIntegral'_add {f g : ℂ → ℂ} {z w : ℂ}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral' (f + g) z w = RectangleIntegral' f z w + RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral', RectangleIntegral',
    RectangleBorderIntegrable.add hf hg, smul_add]

/-- `(s - p) * f s` tends to the residue at a simple pole. -/
private theorem tendsto_sub_mul_of_order_neg_one {f : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p) (hord : meromorphicOrderAt f p = -1) :
    Tendsto (fun s => (s - p) * f s) (𝓝[≠] p) (𝓝 (residue f p)) := by
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hord
  have hgt : Tendsto g (𝓝[≠] p) (𝓝 (g p)) := hg_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have heq : (fun s => (s - p) * f s) =ᶠ[𝓝[≠] p] g := by
    filter_upwards [hfg, self_mem_nhdsWithin] with s hs hsp
    simp only [smul_eq_mul] at hs
    rw [hs, zpow_neg_one]
    have hne : s - p ≠ 0 := sub_ne_zero.mpr hsp
    field_simp
  have htend : Tendsto (fun s => (s - p) * f s) (𝓝[≠] p) (𝓝 (g p)) := hgt.congr' heq.symm
  rw [residue_eq_of_tendsto htend]
  exact htend

/-- Adding an analytic function does not change the residue at a simple pole. -/
private theorem residue_add_analyticAt {f g : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p) (hord : meromorphicOrderAt f p = -1) (hg : AnalyticAt ℂ g p) :
    residue (f + g) p = residue f p := by
  have h1 := tendsto_sub_mul_of_order_neg_one hf hord
  have h2 : Tendsto (fun s => (s - p) * g s) (𝓝[≠] p) (𝓝 0) := by
    have hs : Tendsto (fun s : ℂ => s - p) (𝓝[≠] p) (𝓝 0) :=
      tendsto_sub_nhds_zero_iff.mpr (tendsto_id.mono_left nhdsWithin_le_nhds)
    simpa using hs.mul (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have h3 : Tendsto (fun s => (s - p) * (f + g) s) (𝓝[≠] p) (𝓝 (residue f p)) := by
    have := h1.add h2
    rw [add_zero] at this
    refine this.congr (fun s => ?_)
    simp only [Pi.add_apply]
    ring
  exact residue_eq_of_tendsto h3

/-- A function differentiable on a punctured closed disc with nonnegative order at the centre has
vanishing circle integral there. -/
private theorem circleIntegral_eq_zero_of_diffOn_punctured {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : MeromorphicAt f 0) (hord : 0 ≤ meromorphicOrderAt f 0)
    (hdisc : DifferentiableOn ℂ f (Metric.closedBall 0 r \ {0})) :
    circleIntegral f 0 r = 0 := by
  obtain ⟨g, hg_an, hfg⟩ := MeromorphicAt.meromorphicOrderAt_nonneg_iff hf |>.1 hord
  have hfg' : ∀ᶠ s in 𝓝 (0:ℂ), s ≠ 0 → f s = g s := eventually_nhdsWithin_iff.mp hfg
  set F : ℂ → ℂ := Function.update f 0 (g 0) with hF
  have upd : ∀ w : ℂ, w ≠ 0 → F w = f w := by
    intro w hw
    rw [hF, Function.update_apply, if_neg hw]
  have hFeq : F =ᶠ[𝓝 (0:ℂ)] g := by
    filter_upwards [hfg'] with s hs
    by_cases h : s = 0
    · subst h
      rw [hF, Function.update_apply, if_pos rfl]
    · rw [upd s h]
      exact hs h
  -- continuity of `s ↦ s * F s` on the punctured closed disc
  have hcont : ContinuousOn (fun s : ℂ => s * F s) (Metric.closedBall 0 r \ {0}) := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz.2
    have hfe : ∀ y ∈ Metric.closedBall 0 r \ {0}, F y = f y :=
      fun y hy => upd y (by simpa using hy.2)
    have hcf : ContinuousWithinAt f (Metric.closedBall 0 r \ {0}) z := (hdisc z hz).continuousWithinAt
    have hc1 : ContinuousWithinAt F (Metric.closedBall 0 r \ {0}) z :=
      hcf.congr hfe (upd z hz0)
    exact continuousWithinAt_id.mul hc1
  -- differentiability of `s ↦ s * F s` on the punctured open disc
  have hd : ∀ z ∈ Metric.ball (0:ℂ) r \ {0}, DifferentiableAt ℂ (fun s : ℂ => s * F s) z := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz.2
    have hnb : Metric.closedBall (0:ℂ) r \ {0} ∈ 𝓝 z :=
      Filter.mem_of_superset
        (inter_mem (Metric.isOpen_ball.mem_nhds hz.1) (isOpen_ne.mem_nhds hz0))
        (fun w hw => ⟨Metric.ball_subset_closedBall hw.1, hw.2⟩)
    have hdf : DifferentiableAt ℂ f z := hdisc.differentiableAt hnb
    have hfe : F =ᶠ[𝓝 z] f := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
      exact upd w hw
    exact differentiableAt_id.mul (hdf.congr_of_eventuallyEq hfe)
  -- the limit at the centre
  have hy : Tendsto (fun s : ℂ => s * F s) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
    have heq : (fun s : ℂ => s * F s) =ᶠ[𝓝[≠] (0:ℂ)] (fun s : ℂ => s * g s) := by
      filter_upwards [hFeq.filter_mono nhdsWithin_le_nhds] with s hs
      rw [hs]
    have hlim : Tendsto (fun s : ℂ => s * g s) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
      have hid : Tendsto (fun s : ℂ => s) (𝓝[≠] (0:ℂ)) (𝓝 (0:ℂ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have := hid.mul (hg_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      simpa using this
    exact hlim.congr' heq.symm
  have hcircle := Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
    (c := (0 : ℂ)) (R := r) (f := fun s : ℂ => s * F s) (y := 0) (s := ∅) hr countable_empty hcont
    (fun z hz => hd z hz.1) (by simpa using hy)
  have hcircle' : circleIntegral (fun z : ℂ => (z - 0)⁻¹ * (z * F z)) 0 r = 0 := by
    simpa using hcircle
  have heqc : circleIntegral F 0 r =
      circleIntegral (fun z : ℂ => (z - 0)⁻¹ * (z * F z)) 0 r := by
    refine circleIntegral.integral_congr hr.le ?_
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst h
      have h' : dist (0:ℂ) 0 = r := by simpa [Metric.mem_sphere] using hz
      rw [dist_self] at h'
      linarith
    rw [hF]
    field_simp
    ring
  have hzero : circleIntegral F 0 r = 0 := by
    rw [heqc, hcircle']
  have hsame : circleIntegral F 0 r = circleIntegral f 0 r := by
    refine circleIntegral.integral_congr hr.le ?_
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst h
      have h' : dist (0:ℂ) 0 = r := by simpa [Metric.mem_sphere] using hz
      rw [dist_self] at h'
      linarith
    exact upd z hz0
  rw [← hsame, hzero]




/-- A codiscrete-in-`R` equality becomes an a.e. equality along an analytic non-constant path. -/
private theorem preimage_codiscrete_ae {f g : ℂ → ℂ} {R : Set ℂ} {a b : ℝ} {p : ℝ → ℂ}
    (heq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    (hp_an : AnalyticOnNhd ℝ p (Set.uIcc a b))
    (hp_nonconst : ∀ x ∈ Set.uIcc a b, ¬Filter.EventuallyConst p (nhds x))
    (hp_maps : Set.MapsTo p (Set.uIcc a b) R) :
    (fun x => f (p x)) =ᵐ[volume.restrict (Set.uIoc a b)] (fun x => g (p x)) := by
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  change {x : ℝ | f (p x) = g (p x)} ∈ Filter.codiscreteWithin (Set.uIoc a b)
  simpa [Set.preimage] using Filter.codiscreteWithin_mono Set.uIoc_subset_uIcc
    (hp_an.preimage_mem_codiscreteWithin hp_nonconst
      (Filter.codiscreteWithin_mono
        (by intro s hs; rcases hs with ⟨x, hx, rfl⟩; exact hp_maps hx) heq))

/-- Integrals along an analytic non-constant path agree for codiscretely equal integrands. -/
private theorem intervalIntegral_congr_ae_of_codiscreteWithin_along_path {f g : ℂ → ℂ} {R : Set ℂ}
    (heq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    {a b : ℝ} {p : ℝ → ℂ}
    (hp_an : AnalyticOnNhd ℝ p (Set.uIcc a b))
    (hp_nonconst : ∀ x ∈ Set.uIcc a b, ¬Filter.EventuallyConst p (nhds x))
    (hp_maps : Set.MapsTo p (Set.uIcc a b) R) :
    ∫ x in a..b, f (p x) = ∫ x in a..b, g (p x) :=
  intervalIntegral.integral_congr_ae_restrict (μ := volume)
    (preimage_codiscrete_ae heq hp_an hp_nonconst hp_maps)

/-- Non-constancy of horizontal paths `x ↦ x + h * I`. -/
private theorem horizontalPath_not_eventuallyConst (h : ℝ) (x : ℝ) :
    ¬Filter.EventuallyConst (fun r : ℝ => (r : ℂ) + (h : ℂ) * Complex.I) (nhds x) := by
  intro hc
  obtain ⟨c, hc⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.1 hc
  have hpath : HasDerivAt (fun r : ℝ => (r : ℂ) + (h : ℂ) * Complex.I) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((h : ℂ) * Complex.I)
  have hconst : HasDerivAt (fun r : ℝ => (r : ℂ) + (h : ℂ) * Complex.I) 0 x :=
    (hasDerivAt_const x c).congr_of_eventuallyEq hc
  exact one_ne_zero (hpath.unique hconst)

/-- Non-constancy of vertical paths `y ↦ r + y * I`. -/
private theorem verticalPath_not_eventuallyConst (r : ℝ) (x : ℝ) :
    ¬Filter.EventuallyConst (fun y : ℝ => (r : ℂ) + (y : ℂ) * Complex.I) (nhds x) := by
  intro hc
  obtain ⟨c, hc⟩ := Filter.eventuallyConst_iff_exists_eventuallyEq.1 hc
  have hpath : HasDerivAt (fun y : ℝ => (r : ℂ) + (y : ℂ) * Complex.I) Complex.I x := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).mul_const Complex.I).const_add (r : ℂ)
  have hconst : HasDerivAt (fun y : ℝ => (r : ℂ) + (y : ℂ) * Complex.I) 0 x :=
    (hasDerivAt_const x c).congr_of_eventuallyEq hc
  exact Complex.I_ne_zero (hpath.unique hconst)

/-- Horizontal side: codiscretely equal integrands have equal horizontal integrals. -/
private theorem HIntegral_congr_codiscreteWithin {f g : ℂ → ℂ} {R : Set ℂ} {a b c : ℝ}
    (h_eq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    (hmaps : ∀ x ∈ Set.uIcc a b, ((x : ℂ) + (c : ℂ) * Complex.I) ∈ R) :
    HIntegral f a b c = HIntegral g a b c := by
  unfold HIntegral
  exact intervalIntegral_congr_ae_of_codiscreteWithin_along_path h_eq
    (by intro x _; exact (Complex.ofRealCLM.analyticAt x).add analyticAt_const)
    (fun x _ => horizontalPath_not_eventuallyConst c x) hmaps

/-- Vertical side: codiscretely equal integrands have equal vertical integrals. -/
private theorem VIntegral_congr_codiscreteWithin {f g : ℂ → ℂ} {R : Set ℂ} {c a b : ℝ}
    (h_eq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    (hmaps : ∀ y ∈ Set.uIcc a b, ((c : ℂ) + (y : ℂ) * Complex.I) ∈ R) :
    VIntegral f c a b = VIntegral g c a b := by
  unfold VIntegral
  simp only [smul_eq_mul]
  congr 1
  exact intervalIntegral_congr_ae_of_codiscreteWithin_along_path h_eq
    (by intro y _; exact analyticAt_const.add ((Complex.ofRealCLM.analyticAt y).mul analyticAt_const))
    (fun x _ => verticalPath_not_eventuallyConst c x) hmaps

/-- The normalized rectangle integral only depends on the codiscrete class of the integrand. -/
private theorem rectangleIntegral'_toMeromorphicNFOn_eq {f : ℂ → ℂ} {z w : ℂ}
    (f_mero : MeromorphicOn f (Rectangle z w)) :
    RectangleIntegral' f z w = RectangleIntegral' (toMeromorphicNFOn f (Rectangle z w)) z w := by
  classical
  let R : Set ℂ := Rectangle z w
  let fNF : ℂ → ℂ := toMeromorphicNFOn f R
  have h_eq : {s : ℂ | f s = fNF s} ∈ Filter.codiscreteWithin R := by
    simpa [Filter.EventuallyEq, Filter.Eventually, fNF] using
      (toMeromorphicNFOn_eqOn_codiscrete (f := f) (U := R) f_mero)
  have hbot := HIntegral_congr_codiscreteWithin h_eq (fun x hx => mapsTo_rectangle_left_im z w hx)
  have htop := HIntegral_congr_codiscreteWithin h_eq (fun x hx => mapsTo_rectangle_right_im z w hx)
  have hright := VIntegral_congr_codiscreteWithin h_eq (fun y hy => mapsTo_rectangle_right_re z w hy)
  have hleft := VIntegral_congr_codiscreteWithin h_eq (fun y hy => mapsTo_rectangle_left_re z w hy)
  unfold RectangleIntegral'
  congr 1
  unfold RectangleIntegral
  rw [hbot, htop, hright, hleft]

/-- Interval integrability transfers across a codiscrete equality along a border line. -/
private theorem intervalIntegrable_congr_ae_of_codiscreteWithin_along_path {f g : ℂ → ℂ} {R : Set ℂ}
    (heq : {s : ℂ | f s = g s} ∈ Filter.codiscreteWithin R)
    {a b : ℝ} {p : ℝ → ℂ}
    (hp_an : AnalyticOnNhd ℝ p (Set.uIcc a b))
    (hp_nonconst : ∀ x ∈ Set.uIcc a b, ¬Filter.EventuallyConst p (nhds x))
    (hp_maps : Set.MapsTo p (Set.uIcc a b) R) :
    IntervalIntegrable (fun x => f (p x)) volume a b ↔
      IntervalIntegrable (fun x => g (p x)) volume a b :=
  intervalIntegrable_congr_ae (preimage_codiscrete_ae heq hp_an hp_nonconst hp_maps)

/-- A meromorphic function with no poles on the border of the rectangle is border integrable. -/
private theorem rectangleBorderIntegrable_of_meromorphicOn {f : ℂ → ℂ} {z w : ℂ}
    (hmero : MeromorphicOn f (Rectangle z w))
    (hbd : Disjoint (RectangleBorder z w) {p | meromorphicOrderAt f p < 0}) :
    RectangleBorderIntegrable f z w := by
  classical
  let R : Set ℂ := Rectangle z w
  let fNF : ℂ → ℂ := toMeromorphicNFOn f R
  have hcod : {s : ℂ | f s = fNF s} ∈ Filter.codiscreteWithin R := by
    simpa [Filter.EventuallyEq, Filter.Eventually, fNF] using
      (toMeromorphicNFOn_eqOn_codiscrete (f := f) (U := R) hmero)
  have hNFnf : MeromorphicNFOn fNF R := by
    simpa [fNF] using meromorphicNFOn_toMeromorphicNFOn (f := f) (U := R)
  have hNFcont : ContinuousOn fNF (RectangleBorder z w) := by
    intro p hp
    have hpR : p ∈ R := by simpa [R] using rectangleBorder_subset_rectangle z w hp
    have hnot : ¬ meromorphicOrderAt f p < 0 := fun h => (Set.disjoint_left.mp hbd hp) h
    have hord : 0 ≤ meromorphicOrderAt fNF p := by
      have h1 : meromorphicOrderAt fNF p = meromorphicOrderAt f p :=
        meromorphicOrderAt_toMeromorphicNFOn (f := f) (U := R) hmero hpR
      rw [h1]
      exact not_lt.mp hnot
    have hnf : MeromorphicNFAt fNF p := hNFnf hpR
    exact ((MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt hnf).1
      hord).continuousAt.continuousWithinAt
  have hNFint : RectangleBorderIntegrable fNF z w :=
    ContinuousOn.rectangleBorder_integrable hNFcont
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (intervalIntegrable_congr_ae_of_codiscreteWithin_along_path hcod
      (by intro x _; exact (Complex.ofRealCLM.analyticAt x).add analyticAt_const)
      (fun x _ => horizontalPath_not_eventuallyConst z.im x)
      (fun x hx => mapsTo_rectangle_left_im z w hx)).mpr hNFint.1
  · exact (intervalIntegrable_congr_ae_of_codiscreteWithin_along_path hcod
      (by intro x _; exact (Complex.ofRealCLM.analyticAt x).add analyticAt_const)
      (fun x _ => horizontalPath_not_eventuallyConst w.im x)
      (fun x hx => mapsTo_rectangle_right_im z w hx)).mpr hNFint.2.1
  · exact (intervalIntegrable_congr_ae_of_codiscreteWithin_along_path hcod
      (by intro y _; exact analyticAt_const.add ((Complex.ofRealCLM.analyticAt y).mul analyticAt_const))
      (fun x _ => verticalPath_not_eventuallyConst w.re x)
      (fun y hy => mapsTo_rectangle_right_re z w hy)).mpr hNFint.2.2.1
  · exact (intervalIntegrable_congr_ae_of_codiscreteWithin_along_path hcod
      (by intro y _; exact analyticAt_const.add ((Complex.ofRealCLM.analyticAt y).mul analyticAt_const))
      (fun x _ => verticalPath_not_eventuallyConst z.re x)
      (fun y hy => mapsTo_rectangle_left_re z w hy)).mpr hNFint.2.2.2




/-- Laurent order reduction at the origin: if the order of `f` at `0` is exactly `-(m+1)`, then
subtracting the leading term `c s^{-(m+1)}` raises the order at least to `-m`. The difference is
`s^{-m}` times the divided slope of the analytic factor of `f`, which is analytic at `0`. -/
private theorem peel_order {f : ℂ → ℂ} {m : ℕ} (hf : MeromorphicAt f 0)
    (hord : meromorphicOrderAt f 0 = -((m : ℤ) + 1)) :
    ∃ c : ℂ, -((m : ℤ)) ≤
      meromorphicOrderAt (f - fun s : ℂ => c * s ^ (-((m : ℤ) + 1))) 0 := by
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hord
  refine ⟨g 0, ?_⟩
  have hds : AnalyticAt ℂ (dslope g 0) 0 := by
    obtain ⟨p, hp⟩ := hg_an
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  have hgerm : (f - fun s : ℂ => g 0 * s ^ (-((m : ℤ) + 1))) =ᶠ[𝓝[≠] (0 : ℂ)]
      fun s : ℂ => s ^ (-((m : ℤ))) * dslope g 0 s := by
    rw [eventually_nhdsWithin_iff] at hfg
    filter_upwards [Eventually.filter_mono nhdsWithin_le_nhds hfg, self_mem_nhdsWithin]
      with s hs hs0
    have hne : s ≠ 0 := by simpa using hs0
    have h1 : f s = s ^ (-((m : ℤ) + 1)) * g s := by
      simpa [smul_eq_mul] using hs hne
    have h2 : (s - 0) * dslope g 0 s = g s - g 0 := by
      simpa using sub_smul_dslope g (0 : ℂ) s
    simp only [Pi.sub_apply]
    calc f s - g 0 * s ^ (-((m : ℤ) + 1))
        = s ^ (-((m : ℤ) + 1)) * g s - g 0 * s ^ (-((m : ℤ) + 1)) := by rw [h1]
      _ = s ^ (-((m : ℤ) + 1)) * (g s - g 0) := by ring
      _ = s ^ (-((m : ℤ) + 1)) * ((s - 0) * dslope g 0 s) := by rw [← h2]
      _ = s ^ (-((m : ℤ))) * dslope g 0 s := by
        rw [show (-((m : ℤ))) = -((m : ℤ) + 1) + 1 by ring, zpow_add₀ hne, zpow_one]
        ring
  rw [meromorphicOrderAt_congr hgerm]
  have hm1 : MeromorphicAt (fun s : ℂ => s ^ (-((m : ℤ)))) 0 := by
    have h : MeromorphicAt (fun s : ℂ => (s ^ m)⁻¹) 0 :=
      ((MeromorphicAt.id (0 : ℂ)).pow m).inv
    simpa only [zpow_neg, zpow_natCast] using h
  change -((m : ℤ)) ≤ meromorphicOrderAt ((fun s : ℂ => s ^ (-((m : ℤ)))) * dslope g 0) 0
  rw [meromorphicOrderAt_mul hm1 hds.meromorphicAt]
  have hzp : meromorphicOrderAt (fun s : ℂ => s ^ (-((m : ℤ)))) 0 = -((m : ℤ)) := by
    have h := meromorphicOrderAt_zpow_id_sub_const (x := (0 : ℂ)) (n := -((m : ℤ)))
    have h' : ((fun x : ℂ => x - 0) ^ (-((m : ℤ)))) = fun s : ℂ => s ^ (-((m : ℤ))) := by
      funext s
      simp
    rw [h'] at h
    simpa using h
  rw [hzp]
  exact le_add_of_nonneg_right hds.meromorphicOrderAt_nonneg




/-- `c * s ^ n` is analytic at every nonzero point. -/
private theorem analyticAt_const_mul_zpow {c : ℂ} {n : ℤ} {p : ℂ} (hp : p ≠ 0) :
    AnalyticAt ℂ (fun s : ℂ => c * s ^ n) p := by
  have hd : DifferentiableOn ℂ (fun s : ℂ => c * s ^ n) {w : ℂ | w ≠ 0} :=
    fun w hw => ((differentiableAt_zpow.mpr (Or.inl hw)).const_mul c).differentiableWithinAt
  exact hd.analyticAt (isOpen_ne.mem_nhds hp)

/-- `c * s ^ n` is meromorphic everywhere. -/
private theorem meromorphicAt_const_mul_zpow (c : ℂ) (n : ℤ) (p : ℂ) :
    MeromorphicAt (fun s : ℂ => c * s ^ n) p :=
  (MeromorphicAt.const c p).mul ((MeromorphicAt.id p).zpow n)

/-- Subtracting a function analytic at `p` does not change whether the order at `p` is negative. -/
private theorem order_neg_iff_sub_analyticAt {f g : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p) (hg : AnalyticAt ℂ g p) :
    meromorphicOrderAt (f - g) p < 0 ↔ meromorphicOrderAt f p < 0 := by
  have hgm : (0 : WithTop ℤ) ≤ meromorphicOrderAt g p := hg.meromorphicOrderAt_nonneg
  have hsub : MeromorphicAt (f - g) p := hf.sub hg.meromorphicAt
  have hfg : f = (f - g) + g := by funext s; simp
  constructor
  · intro h
    have hlt : meromorphicOrderAt (f - g) p < meromorphicOrderAt g p := lt_of_lt_of_le h hgm
    have heq : meromorphicOrderAt ((f - g) + g) p = meromorphicOrderAt (f - g) p :=
      meromorphicOrderAt_add_eq_left_of_lt hg.meromorphicAt hlt
    rw [hfg, heq]
    exact h
  · intro h
    by_contra hcon
    push Not at hcon
    have hle : (0 : WithTop ℤ) ≤ meromorphicOrderAt f p := by
      rw [hfg]
      by_cases hab : meromorphicOrderAt (f - g) p = meromorphicOrderAt g p
      · have hmin : (0 : WithTop ℤ) ≤
            min (meromorphicOrderAt (f - g) p) (meromorphicOrderAt g p) := le_min hcon hgm
        rw [hab, min_self] at hmin
        have h2 := meromorphicOrderAt_add hsub hg.meromorphicAt
        rw [hab, min_self] at h2
        exact le_trans hmin h2
      · rw [meromorphicOrderAt_add_of_ne hsub hg.meromorphicAt hab]
        exact le_min hcon hgm
    exact absurd hle (not_le.mpr h)

/-- Subtracting a function analytic at `p` preserves the bound `-1` on the order. -/
private theorem order_ge_neg_one_sub_analyticAt {f g : ℂ → ℂ} {p : ℂ}
    (hf : MeromorphicAt f p) (hg : AnalyticAt ℂ g p)
    (h : (-1 : WithTop ℤ) ≤ meromorphicOrderAt f p) :
    (-1 : WithTop ℤ) ≤ meromorphicOrderAt (f - g) p := by
  have hgm : (0 : WithTop ℤ) ≤ meromorphicOrderAt g p := hg.meromorphicOrderAt_nonneg
  have hfg : f = (f - g) + g := by funext s; simp
  by_contra hcon
  push Not at hcon
  have hlt : meromorphicOrderAt (f - g) p < meromorphicOrderAt g p :=
    lt_of_lt_of_le hcon (le_trans (WithTop.coe_le_coe.mpr (by norm_num : (-1:ℤ) ≤ 0)) hgm)
  have heq : meromorphicOrderAt f p = meromorphicOrderAt (f - g) p := by
    conv_lhs => rw [hfg]
    exact meromorphicOrderAt_add_eq_left_of_lt hg.meromorphicAt hlt
  rw [heq] at h
  exact absurd h (not_le.mpr hcon)

/-- The normalized rectangle integral of `s^{-j}`. -/
private theorem rectangleIntegral'_zpow_neg {z w : ℂ} {j : ℕ} (hj : 1 ≤ j)
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral' (fun s : ℂ => s ^ (-(j : ℤ))) z w = if j = 1 then 1 else 0 := by
  rcases eq_or_ne j 1 with rfl | hj1
  · simpa using rectangleIntegral'_inv h1 h2 h3 h4
  · rw [if_neg hj1]
    exact rectangleIntegral'_zpow_neg_more (by omega) h1 h2 h3 h4

/-- The normalized rectangle integral of a constant multiple of `s^{-j}`. -/
private theorem rectangleIntegral'_const_mul_zpow {z w : ℂ} {j : ℕ} (hj : 1 ≤ j) (c : ℂ)
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral' (fun s : ℂ => c * s ^ (-(j : ℤ))) z w = c * (if j = 1 then 1 else 0) := by
  rw [show (fun s : ℂ => c * s ^ (-(j : ℤ))) = (fun s : ℂ => c • s ^ (-(j : ℤ))) from rfl,
    RectangleIntegral.const_mul']
  rw [rectangleIntegral'_zpow_neg hj h1 h2 h3 h4]
  simp [smul_eq_mul]

/-- The circle integral of a constant multiple of `s^{-j}`. -/
private theorem circleIntegral_const_mul_zpow {r : ℝ} {j : ℕ} (hj : 1 ≤ j) (c : ℂ) (hr : r ≠ 0) :
    circleIntegral (fun s : ℂ => c * s ^ (-(j : ℤ))) 0 r =
      c * (if j = 1 then 2 * Real.pi * Complex.I else 0) := by
  rw [show (fun s : ℂ => c * s ^ (-(j : ℤ))) =
      (fun s : ℂ => c * (fun t : ℂ => t ^ (-(j : ℤ))) s) from rfl,
    circleIntegral.integral_const_mul, circleIntegral_zpow_neg j hj hr]



/-- P0014 page 33 display 4.7 with the disc at `0` cut out, reduced to a pole order bound at `0`:
for every `m`, a function meromorphic on the rectangle, with simple poles off the origin, whose
order at `0` is at least `-(m+1)`, satisfies the shifted residue identity. -/
private theorem rect_cut_aux : ∀ (m : ℕ) (f : ℂ → ℂ) (z w : ℂ) (r : ℝ),
    (0 < r) → z.re < -r → z.im < -r → r < w.re → r < w.im →
    MeromorphicOn f (Rectangle z w) →
    Disjoint (RectangleBorder z w) {p | meromorphicOrderAt f p < 0} →
    (Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}).Finite →
    HasSimplePolesOn f (Rectangle z w \ {0}) →
    DifferentiableOn ℂ f (Metric.closedBall 0 r \ {0}) →
    -((m : ℤ)) ≤ meromorphicOrderAt f 0 →
    RectangleIntegral' f z w = (2 * Real.pi * Complex.I)⁻¹ * circleIntegral f 0 r +
      sumResiduesIn f ((Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}) \ {0}) := by
  intro m
  induction m with
  | zero =>
    intro f z w r hr hzr hzi hwr hwi hmero hbd hfin hsimple hdisc hord
    have hzrw : z.re ≤ w.re := by linarith
    have hziw : z.im ≤ w.im := by linarith
    have h0R : (0 : ℂ) ∈ Rectangle z w := by
      rw [mem_Rect hzrw hziw]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Complex.zero_re, Complex.zero_im] <;> linarith
    have hmero0 : MeromorphicAt f 0 := hmero 0 h0R
    have hnotneg : ¬ meromorphicOrderAt f 0 < 0 := not_lt.mpr hord
    have hsimpleR : HasSimplePolesOn f (Rectangle z w) := by
      intro x hx
      by_cases hx0 : x = 0
      · subst hx0
        exact le_trans (WithTop.coe_le_coe.mpr (by norm_num : (-1:ℤ) ≤ 0)) hord
      · exact hsimple x ⟨hx, hx0⟩
    have hres := RectangleIntegral'_eq_sumResiduesIn (f := f) (z := z) (w := w) hzrw hziw
      hmero hbd hfin hsimpleR
    have hcirc := circleIntegral_eq_zero_of_diffOn_punctured hr hmero0 hord hdisc
    have hnotin : (0 : ℂ) ∉ (Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}) :=
      fun h => absurd hord (not_le_of_gt h.2)
    rw [hres, hcirc, Set.sdiff_singleton_eq_self hnotin]
    simp
  | succ m ih =>
    intro f z w r hr hzr hzi hwr hwi hmero hbd hfin hsimple hdisc hord
    by_cases hle : -((m : ℤ)) ≤ meromorphicOrderAt f 0
    · exact ih f z w r hr hzr hzi hwr hwi hmero hbd hfin hsimple hdisc hle
    · have hzrw : z.re ≤ w.re := by linarith
      have hziw : z.im ≤ w.im := by linarith
      have h0R : (0 : ℂ) ∈ Rectangle z w := by
        rw [mem_Rect hzrw hziw]
        refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Complex.zero_re, Complex.zero_im] <;> linarith
      have h0in : Rectangle z w ∈ 𝓝 (0 : ℂ) :=
        rectangle_mem_nhds_zero (by linarith) (by linarith) (by linarith) (by linarith)
      have hmero0 : MeromorphicAt f 0 := hmero 0 h0R
      -- the order at `0` is exactly `-(m+1)`
      have hne_top : meromorphicOrderAt f 0 ≠ ⊤ := by
        intro h
        exact hle (by rw [h]; exact le_top)
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne_top
      have h1 : -((m : ℤ) + 1) ≤ k := by
        rw [← hk] at hord
        have h2 : (((m + 1 : ℕ)) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
        rw [h2] at hord
        exact WithTop.coe_le_coe.mp hord
      have h2 : ¬ (-((m : ℤ)) ≤ k) := by
        intro hc
        exact hle (by rw [← hk]; exact WithTop.coe_le_coe.mpr hc)
      have hkval : k = -((m : ℤ) + 1) := by omega
      have hord0 : meromorphicOrderAt f 0 = -((m : ℤ) + 1) := by
        rw [← hk, hkval]
        simp
      -- the Laurent reduction
      obtain ⟨c, hc⟩ := peel_order hmero0 hord0
      set P : ℂ → ℂ := fun s : ℂ => c * s ^ (-((m : ℤ) + 1)) with hP
      set f' : ℂ → ℂ := f - P with hf'
      have hsplit : f = f' + P := by funext s; simp [hf']
      have hord' : -((m : ℤ)) ≤ meromorphicOrderAt f' 0 := by
        simpa only [hf', hP] using hc
      have hPm : ∀ p : ℂ, MeromorphicAt P p := fun p => meromorphicAt_const_mul_zpow c _ p
      have hPan : ∀ p : ℂ, p ≠ 0 → AnalyticAt ℂ P p := fun p hp => analyticAt_const_mul_zpow hp
      have hmero' : MeromorphicOn f' (Rectangle z w) := by
        intro p hp
        exact (hmero p hp).sub (hPm p)
      have hbd' : Disjoint (RectangleBorder z w) {p | meromorphicOrderAt f' p < 0} := by
        rw [Set.disjoint_left]
        intro p hpb hneg
        have hpR : p ∈ Rectangle z w := rectangleBorder_subset_rectangle z w hpb
        have hp0 : p ≠ 0 := fun h => not_mem_rectangleBorder_of_rectangle_mem_nhds h0in (h ▸ hpb)
        exact (Set.disjoint_left.mp hbd hpb)
          ((order_neg_iff_sub_analyticAt (hmero p hpR) (hPan p hp0)).mp (by simpa [hf'] using hneg))
      have hfin' : (Rectangle z w ∩ {p | meromorphicOrderAt f' p < 0}).Finite := by
        refine Set.Finite.subset (hfin.insert (0 : ℂ)) ?_
        rintro p ⟨hpR, hpneg⟩
        by_cases hp0 : p = 0
        · exact Set.mem_insert_iff.mpr (Or.inl hp0)
        · refine Set.mem_insert_iff.mpr (Or.inr ⟨hpR, ?_⟩)
          exact (order_neg_iff_sub_analyticAt (hmero p hpR) (hPan p hp0)).mp (by simpa [hf'] using hpneg)
      have hsimple' : HasSimplePolesOn f' (Rectangle z w \ {0}) := by
        intro p hp
        exact order_ge_neg_one_sub_analyticAt (hmero p hp.1) (hPan p hp.2) (hsimple p hp)
      have hdisc' : DifferentiableOn ℂ f' (Metric.closedBall 0 r \ {0}) := by
        intro s hs
        have hs0 : s ≠ 0 := by simpa using hs.2
        have hPs : DifferentiableAt ℂ P s :=
          (differentiableAt_zpow.mpr (Or.inl hs0)).const_mul c
        exact (hdisc s hs).sub hPs.differentiableWithinAt
      have ih' := ih f' z w r hr hzr hzi hwr hwi hmero' hbd' hfin' hsimple' hdisc' hord'
      -- integrability of the two pieces
      have hf'int : RectangleBorderIntegrable f' z w :=
        rectangleBorderIntegrable_of_meromorphicOn hmero' hbd'
      have hPint : RectangleBorderIntegrable P z w := by
        refine ContinuousOn.rectangleBorder_integrable ?_
        intro s hs
        have hs0 : s ≠ 0 := fun h => not_mem_rectangleBorder_of_rectangle_mem_nhds h0in (h ▸ hs)
        exact (hPan s hs0).continuousAt.continuousWithinAt
      -- splitting the two integrals
      have hrectsplit : RectangleIntegral' f z w =
          RectangleIntegral' f' z w + RectangleIntegral' P z w := by
        rw [hsplit]
        exact rectangleIntegral'_add hf'int hPint
      have hcircsplit : circleIntegral f 0 r = circleIntegral f' 0 r + circleIntegral P 0 r := by
        rw [hsplit]
        refine circleIntegral.integral_add ?_ ?_
        · refine ContinuousOn.circleIntegrable' ?_
          rw [abs_of_pos hr]
          intro s hs
          have hs0 : s ≠ 0 := by
            intro h
            subst h
            have h' : dist (0:ℂ) 0 = r := by simpa [Metric.mem_sphere] using hs
            rw [dist_self] at h'
            linarith
          refine ContinuousWithinAt.mono
            (hdisc' s ⟨Metric.sphere_subset_closedBall hs, by simpa using hs0⟩).continuousWithinAt ?_
          intro z hz
          exact ⟨Metric.sphere_subset_closedBall hz, by
            intro h
            rw [h] at hz
            simp only [Metric.mem_sphere, dist_self, abs_of_pos hr] at hz
            linarith⟩
        · refine ContinuousOn.circleIntegrable' ?_
          rw [abs_of_pos hr]
          intro s hs
          have hs0 : s ≠ 0 := by
            intro h
            subst h
            have h' : dist (0:ℂ) 0 = r := by simpa [Metric.mem_sphere] using hs
            rw [dist_self] at h'
            linarith
          exact (hPan s hs0).continuousAt.continuousWithinAt
      -- the pole sets off the origin agree
      have hE : (Rectangle z w ∩ {p | meromorphicOrderAt f' p < 0}) \ {0}
          = (Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}) \ {0} := by
        ext p
        simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨⟨hpR, hpneg⟩, hp0⟩
          exact ⟨⟨hpR, (order_neg_iff_sub_analyticAt (hmero p hpR) (hPan p hp0)).mp
            (by simpa [hf'] using hpneg)⟩, hp0⟩
        · rintro ⟨⟨hpR, hpneg⟩, hp0⟩
          exact ⟨⟨hpR, (order_neg_iff_sub_analyticAt (hmero p hpR) (hPan p hp0)).mpr hpneg⟩, hp0⟩
      have hS : sumResiduesIn f' ((Rectangle z w ∩ {p | meromorphicOrderAt f' p < 0}) \ {0})
          = sumResiduesIn f ((Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}) \ {0}) := by
        rw [hE]
        refine tsum_congr (fun p => ?_)
        have hpR : (p : ℂ) ∈ Rectangle z w := p.2.1.1
        have hp0 : (p : ℂ) ≠ 0 := p.2.2
        have hnegf : meromorphicOrderAt f (p : ℂ) < 0 := p.2.1.2
        have hneg' : meromorphicOrderAt f' (p : ℂ) < 0 :=
          (order_neg_iff_sub_analyticAt (hmero (p : ℂ) hpR) (hPan (p : ℂ) hp0)).mpr hnegf
        have hnt : meromorphicOrderAt f' (p : ℂ) ≠ ⊤ := by
          intro h
          rw [h] at hneg'
          exact absurd hneg' (by simp)
        have hge : (-1 : WithTop ℤ) ≤ meromorphicOrderAt f' (p : ℂ) :=
          hsimple' (p : ℂ) ⟨hpR, hp0⟩
        obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hnt
        have hge' : (-1 : ℤ) ≤ n := by
          rw [← hn] at hge
          exact WithTop.coe_le_coe.mp hge
        have hlt' : n < 0 := by
          rw [← hn] at hneg'
          exact_mod_cast hneg'
        have hn1 : n = -1 := by omega
        have hord1 : meromorphicOrderAt f' (p : ℂ) = -1 := by
          rw [← hn, hn1]
          norm_num
        have hres := residue_add_analyticAt (hmero' (p : ℂ) hpR) hord1 (hPan (p : ℂ) hp0)
        rw [show f' + P = f from hsplit.symm] at hres
        exact hres.symm
      -- the monomial values
      have hPref : RectangleIntegral' P z w = c * (if m + 1 = 1 then (1:ℂ) else 0) := by
        have h := rectangleIntegral'_const_mul_zpow (j := m + 1) (by omega) c
          (by linarith : z.re < 0) (by linarith) (by linarith) (by linarith)
        simpa only [hP, Nat.cast_add, Nat.cast_one] using h
      have hPcirc : (2 * Real.pi * Complex.I)⁻¹ * circleIntegral P 0 r =
          c * (if m + 1 = 1 then (1:ℂ) else 0) := by
        have h1 : circleIntegral P 0 r =
            c * (if m + 1 = 1 then 2 * Real.pi * Complex.I else 0) := by
          have h := circleIntegral_const_mul_zpow (j := m + 1) (by omega) c hr.ne'
          simpa only [hP, Nat.cast_add, Nat.cast_one] using h
        rw [h1]
        by_cases h : m + 1 = 1
        · rw [if_pos h, if_pos h]
          field_simp
        · rw [if_neg h, if_neg h]
          ring
      rw [hrectsplit, hcircsplit, ih', hS, hPref, mul_add, hPcirc]
      ring



/-- The leaf `rect_cut_origin`: the residue theorem on a rectangle with the closed disc of
radius `r` about `0` cut out, the circle integral carrying the principal part at `0`. -/
private theorem rect_cut_origin_main {f : ℂ → ℂ} {z w : ℂ} {r : ℝ} (hr : 0 < r) (hzr : z.re < -r)
    (hzi : z.im < -r) (hwr : r < w.re) (hwi : r < w.im)
    (hmero : MeromorphicOn f (Rectangle z w))
    (hbd : Disjoint (RectangleBorder z w) {p | meromorphicOrderAt f p < 0})
    (hfin : (Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}).Finite)
    (hsimple : HasSimplePolesOn f (Rectangle z w \ {0}))
    (hdisc : DifferentiableOn ℂ f (Metric.closedBall 0 r \ {0})) :
    RectangleIntegral' f z w = (2 * Real.pi * Complex.I)⁻¹ * circleIntegral f 0 r +
      sumResiduesIn f ((Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}) \ {0}) := by
  by_cases htop : meromorphicOrderAt f 0 = ⊤
  · exact rect_cut_aux 0 f z w r hr hzr hzi hwr hwi hmero hbd hfin hsimple hdisc
      (by rw [htop]; exact le_top)
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp htop
    refine rect_cut_aux k.natAbs f z w r hr hzr hzi hwr hwi hmero hbd hfin hsimple hdisc ?_
    rw [← hk]
    refine WithTop.coe_le_coe.mpr ?_
    have h0 : (0 : ℤ) ≤ (k.natAbs : ℤ) := Nat.cast_nonneg _
    obtain hn | hn := Int.natAbs_eq k
    · linarith
    · linarith

end RectCutPort

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
        sumResiduesIn f ((Complex.Rectangle z w ∩ {p | meromorphicOrderAt f p < 0}) \ {0}) :=
  rect_cut_origin_main hr hzr hzi hwr hwi hmero hbd hfin hsimple hdisc

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
    · obtain ⟨h1, h2, h3⟩ := LFunction_eq_zero_of_pole χ hχ hq δ hx hp hp0 hneg
      exact Or.inr ⟨h1, h2, h3, im_abs_le_of_mem_rect hT0 hp⟩
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
