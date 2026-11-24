import LeanLab.ExceptionalSet.SPLIT_leaf_one_sided_majorant

/-!
Feed of `LeanLab.ExceptionalSet.Decomp523a.leaf_fejer_sum_representation`,
burst-20261122 session S90.

Finding: the leaf is FALSE as written. Its right side integrates
`K (x - t) * g (x - t)` over a full period, which by periodicity does not depend
on `x`, while its left side is a nonconstant trigonometric polynomial in `x`.
At `H = 2`, `a = 0`, `b = 1 / 2`, `s = 0` the left side is
`(12 / π) * sin (2 * π * x)`, so the values at `x = 1 / 4` and `x = 3 / 4`
differ while the right side is the same. The intended identity has `g t` in
place of `g (x - t)`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp523a

open Real Finset
open LeanLab.ExceptionalSet.U1539 (eC)

theorem feed1122_eC_add (u v : ℝ) : eC (u + v) = eC u * eC v := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem feed1122_eC_nat (n : ℕ) : eC (n : ℝ) = 1 := by
  unfold eC
  rw [show (2 * (π : ℂ) * Complex.I * ((n : ℝ) : ℂ)) = (n : ℂ) * (2 * π * Complex.I) by
    push_cast; ring]
  exact Complex.exp_nat_mul_two_pi_mul_I n

theorem feed1122_eC_quarter : eC (1 / 4) = Complex.I := by
  unfold eC
  rw [show (2 * (π : ℂ) * Complex.I * (((1 / 4 : ℝ)) : ℂ)) = ((π / 2 : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem feed1122_eC_half : eC (1 / 2) = -1 := by
  unfold eC
  rw [show (2 * (π : ℂ) * Complex.I * (((1 / 2 : ℝ)) : ℂ)) = π * Complex.I by
    push_cast; ring]
  exact Complex.exp_pi_mul_I

theorem feed1122_eC_neg_half : eC (-(1 / 2)) = -1 := by
  have h := feed1122_eC_add (-(1 / 2)) 1
  rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by ring, feed1122_eC_half] at h
  have h1 : eC 1 = 1 := by simpa using feed1122_eC_nat 1
  rw [h1, mul_one] at h
  exact h.symm

theorem feed1122_hasDerivAt_eC_neg (y : ℝ) :
    HasDerivAt (fun z : ℝ => eC (-z)) (-(2 * (π : ℂ) * Complex.I) * eC (-y)) y := by
  have h1 : HasDerivAt (fun z : ℝ => ((-z : ℝ) : ℂ)) ((-1 : ℝ) : ℂ) y := by
    simpa using ((hasDerivAt_id y).neg).ofReal_comp
  have h2 := (h1.const_mul (2 * (π : ℂ) * Complex.I)).cexp
  unfold eC
  convert h2 using 1
  push_cast; ring

/-- `2 π i` times the first Fourier coefficient of the indicator of `[0, 1 / 2)`
equals `2`. -/
theorem feed1122_coeff_half :
    (2 * (π : ℂ) * Complex.I) *
      (∫ y in (0 : ℝ)..1, (if Int.fract y < 1 / 2 then (1 : ℂ) else 0) * eC (-y)) = 2 := by
  have hc : Continuous fun y : ℝ => eC (-y) := by unfold eC; fun_prop
  have hmeas : Measurable fun y : ℝ => (if Int.fract y < 1 / 2 then (1 : ℂ) else 0) * eC (-y) :=
    (Measurable.ite (measurableSet_lt measurable_fract measurable_const) measurable_const
      measurable_const).mul hc.measurable
  have hint : ∀ A B : ℝ, IntervalIntegrable
      (fun y : ℝ => (if Int.fract y < 1 / 2 then (1 : ℂ) else 0) * eC (-y))
      MeasureTheory.volume A B := by
    intro A B
    refine IntervalIntegrable.mono_fun (f := fun _ : ℝ => (1 : ℂ)) intervalIntegrable_const
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun y => ?_))
    have hn : ‖eC (-y)‖ = 1 := by
      unfold eC
      rw [show (2 * (π : ℂ) * Complex.I * ((-y : ℝ) : ℂ)) = ((2 * π * (-y) : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    simp only
    split_ifs <;> simp [hn]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 (1 / 2)) (hint (1 / 2) 1)]
  have hA : ∫ y in (0 : ℝ)..(1 / 2), (if Int.fract y < 1 / 2 then (1 : ℂ) else 0) * eC (-y)
      = ∫ y in (0 : ℝ)..(1 / 2), eC (-y) := by
    apply intervalIntegral.integral_congr_uIoo
    intro y hy
    rw [Set.uIoo_of_le (by norm_num)] at hy
    have hf : Int.fract y = y := Int.fract_eq_self.mpr ⟨hy.1.le, by linarith [hy.2]⟩
    simp only
    rw [hf, if_pos hy.2, one_mul]
  have hB : ∫ y in (1 / 2 : ℝ)..1, (if Int.fract y < 1 / 2 then (1 : ℂ) else 0) * eC (-y)
      = ∫ y in (1 / 2 : ℝ)..1, (0 : ℂ) := by
    apply intervalIntegral.integral_congr_uIoo
    intro y hy
    rw [Set.uIoo_of_le (by norm_num)] at hy
    have hf : Int.fract y = y := Int.fract_eq_self.mpr ⟨by linarith [hy.1], hy.2⟩
    simp only
    rw [hf, if_neg (by linarith [hy.1]), zero_mul]
  rw [hA, hB, intervalIntegral.integral_zero, add_zero]
  have hFTC : ∫ y in (0 : ℝ)..(1 / 2), (-(2 * (π : ℂ) * Complex.I) * eC (-y))
      = eC (-(1 / 2)) - eC (-0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun z : ℝ => eC (-z))
      (fun y _ => feed1122_hasDerivAt_eC_neg y)
      ((continuous_const.mul hc).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul, feed1122_eC_neg_half, neg_zero] at hFTC
  have h0 : eC 0 = 1 := by simpa using feed1122_eC_nat 0
  rw [h0] at hFTC
  linear_combination -hFTC

/-- FALSE finding for `leaf_fejer_sum_representation`: its universal closure
fails at `a = 0`, `b = 1 / 2`, `s = 0`, `H = 2`, comparing `x = 1 / 4` with
`x = 3 / 4`. -/
theorem leaf_fejer_sum_representation_false :
    ¬ (∀ (a b s : ℝ) (H : ℕ) (_ : 1 ≤ H) (x : ℝ) (F : ℕ → ℂ)
      (_ : ∀ h, F h =
        (2 * 12 * (1 - ((h : ℝ) + 1) / (H : ℝ))) •
          ∫ y in (0 : ℝ)..1,
            (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℂ) else 0) *
              eC (-(((h : ℝ) + 1) * y))),
      (∑ h ∈ Finset.range H, (F h * eC (((h : ℝ) + 1) * x)).re) =
        12 * (∫ t in (0 : ℝ)..1,
          (1 / (H : ℝ)) * ‖∑ k ∈ Finset.range H, eC (((k : ℝ) + 1) * (x - t))‖ ^ 2 *
            (if Int.fract (x - t - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0))
        - 12 * (∫ y in (0 : ℝ)..1,
            (if Int.fract (y - (a - s)) < b - a + 2 * s then (1 : ℝ) else 0))) := by
  intro hall
  set G : ℕ → ℂ := fun h => (2 * 12 * (1 - ((h : ℝ) + 1) / ((2 : ℕ) : ℝ))) •
    ∫ y in (0 : ℝ)..1,
      (if Int.fract (y - ((0 : ℝ) - 0)) < 1 / 2 - 0 + 2 * 0 then (1 : ℂ) else 0) *
        eC (-(((h : ℝ) + 1) * y)) with hG
  have h1 := hall 0 (1 / 2) 0 2 (by norm_num) (1 / 4) G (fun h => rfl)
  have h3 := hall 0 (1 / 2) 0 2 (by norm_num) (3 / 4) G (fun h => rfl)
  -- the right side does not depend on `x`
  set φ : ℝ → ℝ := fun u => (1 / ((2 : ℕ) : ℝ)) *
      ‖∑ k ∈ Finset.range 2, eC (((k : ℝ) + 1) * u)‖ ^ 2 *
      (if Int.fract (u - ((0 : ℝ) - 0)) < 1 / 2 - 0 + 2 * 0 then (1 : ℝ) else 0) with hφ
  have hper : Function.Periodic φ 1 := by
    intro u
    rw [hφ]
    simp only
    have hs : ∀ k : ℕ, eC (((k : ℝ) + 1) * (u + 1)) = eC (((k : ℝ) + 1) * u) := by
      intro k
      rw [show ((k : ℝ) + 1) * (u + 1) = ((k : ℝ) + 1) * u + ((k + 1 : ℕ) : ℝ) by
        push_cast; ring, feed1122_eC_add, feed1122_eC_nat, mul_one]
    simp only [hs]
    rw [show u + 1 - ((0 : ℝ) - 0) = (u - ((0 : ℝ) - 0)) + 1 by ring, Int.fract_add_one]
  have hconst : ∀ x : ℝ, (∫ t in (0 : ℝ)..1, φ (x - t)) = ∫ u in (0 : ℝ)..1, φ u := by
    intro x
    rw [intervalIntegral.integral_comp_sub_left (fun u => φ u) x]
    have := hper.intervalIntegral_add_eq (x - 1) 0
    simp only [sub_add_cancel, zero_add, sub_zero] at this ⊢
    exact this
  have e1 : (∫ t in (0 : ℝ)..1,
      (1 / ((2 : ℕ) : ℝ)) * ‖∑ k ∈ Finset.range 2, eC (((k : ℝ) + 1) * (1 / 4 - t))‖ ^ 2 *
        (if Int.fract (1 / 4 - t - ((0 : ℝ) - 0)) < 1 / 2 - 0 + 2 * 0 then (1 : ℝ) else 0))
      = ∫ u in (0 : ℝ)..1, φ u := hconst (1 / 4)
  have e3 : (∫ t in (0 : ℝ)..1,
      (1 / ((2 : ℕ) : ℝ)) * ‖∑ k ∈ Finset.range 2, eC (((k : ℝ) + 1) * (3 / 4 - t))‖ ^ 2 *
        (if Int.fract (3 / 4 - t - ((0 : ℝ) - 0)) < 1 / 2 - 0 + 2 * 0 then (1 : ℝ) else 0))
      = ∫ u in (0 : ℝ)..1, φ u := hconst (3 / 4)
  rw [e1] at h1
  rw [e3] at h3
  have hLHS : (∑ h ∈ Finset.range 2, (G h * eC (((h : ℝ) + 1) * (1 / 4))).re)
      = (∑ h ∈ Finset.range 2, (G h * eC (((h : ℝ) + 1) * (3 / 4))).re) := by
    rw [h1, h3]
  -- evaluate the left side
  set g : ℂ := ∫ y in (0 : ℝ)..1, (if Int.fract y < 1 / 2 then (1 : ℂ) else 0) * eC (-y)
    with hg
  have hG0 : G 0 = (12 : ℝ) • g := by
    rw [hG, hg]
    simp only
    congr 1
    · norm_num
    · apply intervalIntegral.integral_congr
      intro y _
      simp
  have hG1 : G 1 = 0 := by
    rw [hG]
    simp only
    norm_num
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hG0, hG1, zero_mul,
    Complex.zero_re, add_zero, Nat.cast_zero] at hLHS
  rw [show (1 : ℝ) * (1 / 4) = 1 / 4 by ring, feed1122_eC_quarter,
    show (1 : ℝ) * (3 / 4) = 1 / 4 + 1 / 2 by ring, feed1122_eC_add,
    feed1122_eC_quarter, feed1122_eC_half] at hLHS
  have hcoef := feed1122_coeff_half
  rw [← hg] at hcoef
  have hre := congrArg Complex.re hcoef
  have him : g.im = 0 := by
    simp [Complex.smul_re, Complex.mul_re, Complex.mul_im] at hLHS
    linarith
  simp [Complex.mul_re, Complex.mul_im, him] at hre
