/-
P0013 page 74 equations A.3 and A.4.
The interpolation estimate is derived from Mathlib's second derivative convexity theorem.
This is an elementary input to the compact Fourier verification on page 75.
The sample values and their quadrature certificates remain separate inputs.
AI wrote the Lean code for CODEX task119. Binary Goldbach is open.
-/
import Mathlib

namespace LeanLab.HelfgottArcs.Interpolation119
open Set

/-- Page 74 equation A.4, the real scalar interpolation estimate. -/
theorem real_interpolation_bound (f f' f'' : ℝ → ℝ) (a b t M B : ℝ)
    (hab : a < b) (ht : t ∈ Icc a b) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hf'' : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x ∈ Ioo a b, -M ≤ f'' x) (ha : f a ≤ B) (hb : f b ≤ B) :
    f t ≤ B + M * (b - a) ^ 2 / 8 := by
  let g : ℝ → ℝ := fun x => f x + M / 2 * x ^ 2
  have hg : ConvexOn ℝ (Icc a b) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fun x => f' x + M * x)
      (f'' := fun x => f'' x + M) (convex_Icc a b)
    · exact hf.add (by fun_prop)
    · intro x hx
      rw [interior_Icc] at hx
      have hh := (hf' x hx).add (((hasDerivAt_id x).pow 2).const_mul (M / 2))
      convert hh.hasDerivWithinAt using 1 <;> first | rfl | (dsimp [g]; ring)
    · intro x hx
      rw [interior_Icc] at hx
      have hh := (hf'' x hx).add ((hasDerivAt_id x).const_mul M)
      convert hh.hasDerivWithinAt using 1 <;> first | rfl | simp
    · intro x hx
      rw [interior_Icc] at hx
      linarith [hbound x hx]
  let u := (b - t) / (b - a)
  let v := (t - a) / (b - a)
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr ht.2) (sub_pos.mpr hab).le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr hab).le
  have huv : u + v = 1 := by dsimp [u, v]; field_simp; ring
  have huv_t : u * a + v * b = t := by dsimp [u, v]; field_simp; ring
  have hj := hg.2 (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hu hv huv
  simp only [smul_eq_mul, huv_t] at hj
  have hdiff : (b - a) * (u * g a + v * g b - g t) =
      (b - t) * (f a - f t) + (t - a) * (f b - f t) +
        M / 2 * (b - a) * (t - a) * (b - t) := by
    dsimp [g, u, v]
    field_simp
    ring
  have hj0 := mul_nonneg (sub_pos.mpr hab).le (sub_nonneg.mpr hj)
  rw [hdiff] at hj0
  have hleft := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha)
  have hright := mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hb)
  have hparabola : f t ≤ B + M / 2 * (t - a) * (b - t) := by
    nlinarith
  nlinarith [mul_nonneg hM (sq_nonneg (a + b - 2 * t))]

/-- Page 74 equation A.4 for complex functions, proved by real projection. -/
theorem complex_interpolation_bound (f f' f'' : ℝ → ℂ) (a b t M : ℝ)
    (hab : a < b) (ht : t ∈ Icc a b) (hM : 0 ≤ M)
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hf'' : ∀ x ∈ Ioo a b, HasDerivAt f' (f'' x) x)
    (hbound : ∀ x ∈ Ioo a b, ‖f'' x‖ ≤ M) :
    ‖f t‖ ≤ max ‖f a‖ ‖f b‖ + M * (b - a) ^ 2 / 8 := by
  let z := starRingEnd ℂ (f t)
  let r : ℝ → ℝ := fun x => (z * f x).re
  let r' : ℝ → ℝ := fun x => (z * f' x).re
  let r'' : ℝ → ℝ := fun x => (z * f'' x).re
  have hz : ‖z‖ = ‖f t‖ := by simp [z]
  have hr : ContinuousOn r (Icc a b) :=
    Complex.continuous_re.comp_continuousOn (continuous_const.continuousOn.mul hf)
  have hr' : ∀ x ∈ Ioo a b, HasDerivAt r (r' x) x := by
    intro x hx
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x ((hf' x hx).const_mul z)
  have hr'' : ∀ x ∈ Ioo a b, HasDerivAt r' (r'' x) x := by
    intro x hx
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x ((hf'' x hx).const_mul z)
  have hrr : ∀ x ∈ Ioo a b, -(‖f t‖ * M) ≤ r'' x := by
    intro x hx
    have hh := (Complex.abs_re_le_norm (z * f'' x))
    rw [norm_mul, hz] at hh
    have hh' := mul_le_mul_of_nonneg_left (hbound x hx) (norm_nonneg (f t))
    dsimp [r'']
    have hl := (abs_le.mp (hh.trans hh')).1
    exact hl
  have hA : r a ≤ ‖f t‖ * max ‖f a‖ ‖f b‖ := by
    calc
      _ ≤ ‖z * f a‖ := Complex.re_le_norm _
      _ = ‖f t‖ * ‖f a‖ := by rw [norm_mul, hz]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)
  have hB : r b ≤ ‖f t‖ * max ‖f a‖ ‖f b‖ := by
    calc
      _ ≤ ‖z * f b‖ := Complex.re_le_norm _
      _ = ‖f t‖ * ‖f b‖ := by rw [norm_mul, hz]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)
  have hh := real_interpolation_bound r r' r'' a b t (‖f t‖ * M)
    (‖f t‖ * max ‖f a‖ ‖f b‖) hab ht (mul_nonneg (norm_nonneg _) hM)
    hr hr' hr'' hrr hA hB
  have heq : r t = ‖f t‖ ^ 2 := by
    dsimp [r, z]
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.mul_re]
  rw [heq] at hh
  rcases eq_or_lt_of_le (norm_nonneg (f t)) with hzero | hpos
  · rw [← hzero]
    exact add_nonneg (le_trans (norm_nonneg (f a)) (le_max_left _ _)) (by positivity)
  · nlinarith

end LeanLab.HelfgottArcs.Interpolation119
