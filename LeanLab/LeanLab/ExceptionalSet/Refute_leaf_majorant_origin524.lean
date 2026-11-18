import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Refutation of the two origin leaves of
`LeanLab/ExceptionalSet/SPLIT_leaf_majorant_small_width524.lean`,
`leaf_majorant_origin_narrow524` and `leaf_majorant_origin_wide524`.

A real cosine polynomial `T x = c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 π h x)` is even
and has period one. If it dominates the indicator of `[0, w)` on the circle it
is at least one on `(0, w)` and, by evenness and periodicity, on `(1 - w, 1)`
too, and it is nonnegative everywhere. Its mean over a period is `c₀`, because
every cosine with `h ≥ 1` integrates to zero. Hence `2 * w ≤ c₀`. The leaves ask
for `c₀ ≤ w + 4 / (H + 1)`, which fails as soon as `w > 4 / (H + 1)`; the
hypotheses of the leaves allow that, for example `H = 100` with `w = 1 / 6` or
`w = 1 / 4`.

This file states no new definition and uses Mathlib only. AI wrote this code.
-/

namespace LeanLab.ExceptionalSet.Decomp524a

open Real Finset

/-- The mean of a cosine with a positive integer frequency over one period is
zero. Standard. -/
theorem integral_cos_two_pi_nat_mul524 (h : ℕ) (hh : 1 ≤ h) :
    ∫ x in (0 : ℝ)..1, cos (2 * π * ((h : ℝ) * x)) = 0 := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hc : (2 * π * (h : ℝ)) ≠ 0 := by positivity
  have e : (fun x : ℝ => cos (2 * π * ((h : ℝ) * x)))
      = fun x : ℝ => cos ((2 * π * (h : ℝ)) * x) := by
    funext x; congr 1; ring
  rw [e, intervalIntegral.integral_comp_mul_left (fun y => cos y) hc, integral_cos]
  have h1 : sin (2 * π * (h : ℝ) * 1) = 0 := by
    have : 2 * π * (h : ℝ) * 1 = ((2 * h : ℕ) : ℝ) * π := by push_cast; ring
    rw [this, Real.sin_nat_mul_pi]
  rw [h1]; simp

/-- Any real cosine polynomial that dominates the indicator of `[0, w)` on the
circle, with `0 < w ≤ 1 / 2`, has constant term at least `2 * w`: the mean
value argument described in the file header. -/
theorem two_mul_width_le_const_of_cos_majorant524 (w c₀ : ℝ) (H : ℕ) (A : ℕ → ℝ)
    (hw0 : 0 < w) (hw2 : w ≤ 1 / 2)
    (hdom : ∀ x : ℝ, (if 0 ≤ Int.fract x ∧ Int.fract x < w then (1 : ℝ) else 0) ≤
      c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * x))) :
    2 * w ≤ c₀ := by
  set T : ℝ → ℝ := fun x => c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * x))
    with hT
  have hTc : Continuous T := by
    rw [hT]; fun_prop
  have hint : ∀ a b : ℝ, IntervalIntegrable T MeasureTheory.volume a b :=
    fun a b => hTc.intervalIntegrable a b
  -- the mean of `T` is `c₀`
  have hmean : ∫ x in (0 : ℝ)..1, T x = c₀ := by
    have hsumint : ∀ h ∈ Icc 1 H, IntervalIntegrable
        (fun x : ℝ => A h * cos (2 * π * ((h : ℝ) * x))) MeasureTheory.volume 0 1 := by
      intro h _
      exact (by fun_prop : Continuous
        (fun x : ℝ => A h * cos (2 * π * ((h : ℝ) * x)))).intervalIntegrable 0 1
    have hsumc : IntervalIntegrable
        (fun x : ℝ => ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * x)))
        MeasureTheory.volume 0 1 :=
      (by fun_prop : Continuous
        (fun x : ℝ => ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * x)))).intervalIntegrable 0 1
    rw [hT]
    rw [intervalIntegral.integral_add intervalIntegrable_const hsumc,
      intervalIntegral.integral_finsetSum hsumint]
    have hz : ∑ h ∈ Icc 1 H, ∫ x in (0 : ℝ)..1, A h * cos (2 * π * ((h : ℝ) * x)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro h hh
      rw [intervalIntegral.integral_const_mul,
        integral_cos_two_pi_nat_mul524 h (Finset.mem_Icc.mp hh).1, mul_zero]
    rw [hz]; simp
  -- pointwise lower bounds
  have hnn : ∀ x, 0 ≤ T x := by
    intro x
    refine le_trans ?_ (hdom x)
    split_ifs <;> norm_num
  have hone : ∀ x, 0 < x → x < w → 1 ≤ T x := by
    intro x hx0 hxw
    have hfr : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx0.le, by linarith⟩
    have := hdom x
    rwa [hfr, if_pos ⟨hx0.le, hxw⟩] at this
  have hsymm : ∀ x, T (1 - x) = T x := by
    intro x
    simp only [hT]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro h _
    congr 1
    have : 2 * π * ((h : ℝ) * (1 - x)) = -(2 * π * ((h : ℝ) * x)) + (h : ℝ) * (2 * π) := by
      ring
    rw [this, Real.cos_add_nat_mul_two_pi, Real.cos_neg]
  -- split the period into three pieces
  have hsplit : ∫ x in (0 : ℝ)..1, T x
      = (∫ x in (0 : ℝ)..w, T x) + (∫ x in w..(1 - w), T x) + ∫ x in (1 - w)..1, T x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint 0 w) (hint w (1 - w)),
      intervalIntegral.integral_add_adjacent_intervals (hint 0 (1 - w)) (hint (1 - w) 1)]
  have h1 : w ≤ ∫ x in (0 : ℝ)..w, T x := by
    have := intervalIntegral.integral_mono_on_of_le_Ioo (μ := MeasureTheory.volume)
      hw0.le (intervalIntegrable_const (c := (1 : ℝ))) (hint 0 w)
      (fun x hx => hone x hx.1 hx.2)
    simpa using this
  have h2 : 0 ≤ ∫ x in w..(1 - w), T x :=
    intervalIntegral.integral_nonneg (by linarith) (fun x _ => hnn x)
  have h3 : w ≤ ∫ x in (1 - w)..1, T x := by
    have := intervalIntegral.integral_mono_on_of_le_Ioo (μ := MeasureTheory.volume)
      (by linarith : 1 - w ≤ 1) (intervalIntegrable_const (c := (1 : ℝ))) (hint (1 - w) 1)
      (fun x hx => by
        rw [← hsymm x]
        exact hone (1 - x) (by linarith [hx.2]) (by linarith [hx.1]))
    simpa using this
  linarith

/-- The statement of `leaf_majorant_origin_narrow524` is false: `w = 1 / 6`,
`H = 100` meets every hypothesis, yet any admissible majorant would need
`1 / 3 ≤ c₀ ≤ 1 / 6 + 4 / 101`. -/
theorem leaf_majorant_origin_narrow524_false :
    ¬ ∀ (w : ℝ) (H : ℕ), 0 < w → w ≤ 1 / 6 → 4 ≤ H → w + 4 / ((H : ℝ) + 1) < 1 →
      (w + 4 / ((H : ℝ) + 1)) * (1 + cos (π * w)) < 1 →
      ∃ c₀ : ℝ, ∃ A : ℕ → ℝ,
        c₀ ≤ w + 4 / ((H : ℝ) + 1) ∧
        (∀ h ∈ Icc 1 H, |A h| ≤ 4 / (h : ℝ)) ∧
        ∀ x : ℝ, (if 0 ≤ Int.fract x ∧ Int.fract x < w then (1 : ℝ) else 0) ≤
          c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * x)) := by
  intro hall
  have hcos : cos (π * (1 / 6 : ℝ)) ≤ 1 := Real.cos_le_one _
  obtain ⟨c₀, A, hc₀, -, hdom⟩ := hall (1 / 6) 100 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by push_cast; nlinarith)
  have := two_mul_width_le_const_of_cos_majorant524 (1 / 6) c₀ 100 A (by norm_num)
    (by norm_num) hdom
  push_cast at hc₀
  norm_num at hc₀ this
  linarith

/-- The statement of `leaf_majorant_origin_wide524` is false: `w = 1 / 4`,
`H = 100` meets every hypothesis, yet any admissible majorant would need
`1 / 2 ≤ c₀ ≤ 1 / 4 + 4 / 101`. -/
theorem leaf_majorant_origin_wide524_false :
    ¬ ∀ (w : ℝ) (H : ℕ), 0 < w → 1 / 6 < w → w ≤ 1 / 3 → 4 ≤ H →
      w + 4 / ((H : ℝ) + 1) < 1 →
      (w + 4 / ((H : ℝ) + 1)) * (1 + cos (π * w)) < 1 →
      ∃ c₀ : ℝ, ∃ A : ℕ → ℝ,
        c₀ ≤ w + 4 / ((H : ℝ) + 1) ∧
        (∀ h ∈ Icc 1 H, |A h| ≤ 4 / (h : ℝ)) ∧
        ∀ x : ℝ, (if 0 ≤ Int.fract x ∧ Int.fract x < w then (1 : ℝ) else 0) ≤
          c₀ + ∑ h ∈ Icc 1 H, A h * cos (2 * π * ((h : ℝ) * x)) := by
  intro hall
  have hcos : cos (π * (1 / 4 : ℝ)) ≤ 1 := Real.cos_le_one _
  obtain ⟨c₀, A, hc₀, -, hdom⟩ := hall (1 / 4) 100 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by push_cast; nlinarith)
  have := two_mul_width_le_const_of_cos_majorant524 (1 / 4) c₀ 100 A (by norm_num)
    (by norm_num) hdom
  push_cast at hc₀
  norm_num at hc₀ this
  linarith

end LeanLab.ExceptionalSet.Decomp524a
