import LeanLab.GoldbachAverage.GSAnalyticInputs

/-!
Elementary variance steps in P0051 pages 19 and 20.
The Grosswald input stays named. The short interval edge estimate has no cited input.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.GSInputs
open MeasureTheory Set Filter

/-- The square of the psi error is integrable on every compact positive interval. -/
lemma psi_error_square_integrable {x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable (fun t : ℝ => (Chebyshev.psi t - t) ^ 2) volume 0 x := by
  have hm : Measurable (fun t : ℝ => (Chebyshev.psi t - t) ^ 2) :=
    (Chebyshev.psi_mono.measurable.sub measurable_id).pow_const 2
  refine (intervalIntegrable_const (c := (Chebyshev.psi x + x) ^ 2)).mono_fun'
    hm.aestronglyMeasurable ?_
  rw [Set.uIoc_of_le hx]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  have hbound : |Chebyshev.psi t - t| ≤ Chebyshev.psi x + x := by
    rw [abs_le]
    have hp := Chebyshev.psi_nonneg t
    have hpx := Chebyshev.psi_nonneg x
    have hmono := Chebyshev.psi_mono ht.2
    constructor <;> linarith [ht.1, ht.2]
  exact pow_le_pow_left₀ (abs_nonneg _) hbound 2

/-- J of x and h is bounded by four times H of x plus h. -/
theorem J_le_four_H {x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) :
    J x h ≤ 4 * InghamTheta.H (x + h) := by
  set f : ℝ → ℝ := fun t => (Chebyshev.psi t - t) ^ 2 with hf
  have hi := psi_error_square_integrable (show 0 ≤ x + h by linarith)
  have hix : IntervalIntegrable f volume 0 x := by
    apply hi.mono_set
    simp only [uIcc_of_le hx, uIcc_of_le (show 0 ≤ x + h by linarith)]
    intro t ht
    exact ⟨ht.1, by linarith [ht.2]⟩
  have hih : IntervalIntegrable f volume h (x + h) := by
    apply hi.mono_set
    simp only [uIcc_of_le (show h ≤ x + h by linarith),
      uIcc_of_le (show 0 ≤ x + h by linarith)]
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hishift : IntervalIntegrable (fun t => f (t + h)) volume 0 x := by
    convert hih.comp_add_right h using 1 <;> ring
  have hig : IntervalIntegrable (fun t => 2 * f (t + h) + 2 * f t) volume 0 x :=
    (hishift.const_mul 2).add (hix.const_mul 2)
  have hpt : ∀ t : ℝ, (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2 ≤
      2 * f (t + h) + 2 * f t := by
    intro t
    dsimp [f]
    nlinarith [sq_nonneg ((Chebyshev.psi (t + h) - (t + h)) + (Chebyshev.psi t - t))]
  have hm : Measurable (fun t => (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2) :=
    (((Chebyshev.psi_mono.measurable.comp (by fun_prop)).sub
      Chebyshev.psi_mono.measurable).sub measurable_const).pow_const 2
  have hij : IntervalIntegrable (fun t => (Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2)
      volume 0 x := by
    refine hig.mono_fun' hm.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    change ‖(Chebyshev.psi (t + h) - Chebyshev.psi t - h) ^ 2‖ ≤ 2 * f (t + h) + 2 * f t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt t
  have hcmp := intervalIntegral.integral_mono_on hx hij hig (fun t _ => hpt t)
  rw [intervalIntegral.integral_add (hishift.const_mul 2) (hix.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_add_right] at hcmp
  simp only [zero_add] at hcmp
  have hf0 : ∀ t : ℝ, 0 ≤ f t := fun t => sq_nonneg _
  have hm1 := intervalIntegral.integral_mono_interval hh
    (show h ≤ x + h by linarith) le_rfl (Eventually.of_forall hf0) hi
  have hm2 := intervalIntegral.integral_mono_interval (le_refl (0 : ℝ)) hx
    (show x ≤ x + h by linarith) (Eventually.of_forall hf0) hi
  dsimp [J, InghamTheta.H]
  dsimp [f] at hcmp hm1 hm2
  linarith

/-- Eq. 83 follows from the named Grosswald input, with its original logarithm free shape. -/
theorem H_of_grosswald (hG : GrosswaldPsiTheta) (htheta : 1 / 2 < Theta) (htheta1 : Theta < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 2 ≤ x →
      InghamTheta.H x ≤ K * x ^ (2 * Theta + 1) := by
  obtain ⟨C, hC, hb⟩ := hG htheta htheta1
  set A := Chebyshev.psi 2 + 2 with hA
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨(C + A) ^ 2, sq_nonneg _, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hxp : 1 ≤ x ^ Theta := Real.one_le_rpow (by linarith) (by linarith)
  have hpt : ∀ t : ℝ, 0 ≤ t → t ≤ x →
      |Chebyshev.psi t - t| ≤ (C + A) * x ^ Theta := by
    intro t ht htx
    by_cases ht2 : 2 ≤ t
    · have hp : t ^ Theta ≤ x ^ Theta := Real.rpow_le_rpow ht htx (by linarith)
      have h1 := mul_le_mul_of_nonneg_left hp hC
      have h2 : 0 ≤ A * x ^ Theta := by positivity
      exact (hb t ht2).trans (by nlinarith)
    · have hp := Chebyshev.psi_mono (show t ≤ 2 by linarith)
      have hp0 := Chebyshev.psi_nonneg t
      have he : |Chebyshev.psi t - t| ≤ A := by
        rw [abs_le]
        dsimp [A]
        constructor <;> linarith
      have h1 : A ≤ A * x ^ Theta := le_mul_of_one_le_right hA0 hxp
      have h2 : 0 ≤ C * x ^ Theta := by positivity
      exact he.trans (by nlinarith)
  refine (InghamTheta.H_le_of_uniform hx0.le hpt).trans (le_of_eq ?_)
  have hp : (x ^ Theta) ^ 2 = x ^ (2 * Theta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1
    norm_num
    ring
  rw [mul_pow, hp, Real.rpow_add hx0, Real.rpow_one]
  ring

end LeanLab.GoldbachAverage.GSInputs
