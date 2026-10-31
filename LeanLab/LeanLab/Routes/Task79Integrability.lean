/-
CODEX task79. AI wrote the Lean code. Binary Goldbach is open.
Elementary integrability component of the lab WeightedJtheta input.
Source: U1522 source twin. Paper context: Chirre and Hagen Section 5, printed page 13.
-/
import LeanLab.Routes.U1522Frontier

namespace LeanLab.Routes.Task79

open Real MeasureTheory Set Chebyshev LeanLab.Routes.U1522

theorem weighted_error_le_majorant {X δ y : ℝ} (hX : 0 < X) (hδ : 0 < δ) (hy : 0 < y) :
    Eθ δ y ^ 2 * Wt (y / X) ≤ 16 * (1 + δ) ^ 2 * X ^ 4 * y ^ (-2 : ℝ) := by
  let K := 4 * (1 + δ)
  have hK : 0 < K := by dsimp [K]; positivity
  have htheta : ∀ y : ℝ, 0 ≤ y → θ y ≤ 3 * y := by
    intro y hy
    have hh := theta_le_log4_mul_x hy
    have hlog : Real.log 4 ≤ 3 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hlog hy]
  have hE : ∀ y : ℝ, 0 < y → |Eθ δ y| ≤ K * y := by
    intro y hy
    have hk := htheta ((1 + δ) * y) (by positivity)
    have hh := htheta y hy.le
    have ht1 := theta_nonneg y
    have ht2 := theta_nonneg ((1 + δ) * y)
    have hdy : 0 ≤ δ * y := mul_nonneg hδ.le hy.le
    dsimp [Eθ, K]
    rw [abs_le]
    constructor <;> nlinarith
  have hW : ∀ y : ℝ, 0 < y → Wt (y / X) ≤ X ^ 4 / y ^ 4 := by
    intro y hy
    unfold Wt
    split_ifs with h
    · have hyX : y ≤ X := (div_le_one hX).mp h
      rw [le_div_iff₀ (by positivity : 0 < y ^ 4)]
      simpa using pow_le_pow_left₀ hy.le hyX 4
    · apply le_of_eq
      field_simp
  have he := hE y hy
  have hs : Eθ δ y ^ 2 ≤ K ^ 2 * y ^ 2 := by
    have hh := mul_le_mul he he (abs_nonneg _) (by positivity : 0 ≤ K * y)
    nlinarith [sq_abs (Eθ δ y)]
  calc
    _ ≤ (K ^ 2 * y ^ 2) * (X ^ 4 / y ^ 4) :=
      mul_le_mul hs (hW y hy) (Wt_nonneg _) (by positivity)
    _ = (K ^ 2 * X ^ 4) * y ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hy.le, Real.rpow_two]
      field_simp <;> ring
    _ = _ := by dsimp [K]; ring

theorem weighted_error_integrable {X δ : ℝ} (hX : 0 < X) (hδ : 0 < δ) :
    IntegrableOn (fun y => Eθ δ y ^ 2 * Wt (y / X)) (Ioi 2) := by
  have hm : Measurable (fun y => Eθ δ y ^ 2 * Wt (y / X)) := by
    have htheta := theta_mono.measurable
    have he : Measurable (Eθ δ) := by
      exact ((htheta.comp (measurable_const.mul measurable_id)).sub htheta).sub
        (measurable_const.mul measurable_id)
    exact (he.pow_const 2).mul (continuous_Wt.measurable.comp (measurable_id.div_const X))
  have hi : IntegrableOn (fun y : ℝ => (16 * (1 + δ) ^ 2 * X ^ 4) * y ^ (-2 : ℝ)) (Ioi 2) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 2)).const_mul _
  apply hi.mono' hm.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : 0 < y := lt_trans (by norm_num : (0 : ℝ) < 2) hy
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Wt_nonneg _))]
  exact weighted_error_le_majorant hX hδ hy0


theorem weighted_error_integral_le {X δ : ℝ} (hX : 0 < X) (hδ : 0 < δ) :
    (∫ y in Ioi 2, Eθ δ y ^ 2 * Wt (y / X)) ≤ 8 * (1 + δ) ^ 2 * X ^ 4 := by
  let C := 16 * (1 + δ) ^ 2 * X ^ 4
  have hi : IntegrableOn (fun y : ℝ => C * y ^ (-2 : ℝ)) (Ioi 2) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 2)).const_mul _
  calc
    _ ≤ ∫ y in Ioi 2, C * y ^ (-2 : ℝ) := by
      apply integral_mono_ae (weighted_error_integrable hX hδ) hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact weighted_error_le_majorant hX hδ (lt_trans (by norm_num : (0 : ℝ) < 2) hy)
    _ = _ := by
      rw [MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 2)]
      norm_num [C, Real.rpow_neg_one] <;> ring

theorem elementary_bound_not_weighted_scale {δ C X0 : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) :
    ¬ ∀ X : ℝ, X0 ≤ X → 1 ≤ X →
      8 * (1 + δ) ^ 2 * X ^ 4 ≤ C * δ * Real.log (2.0001 / δ) ^ 2 * X ^ 2 := by
  intro h
  let A := C * δ * Real.log (2.0001 / δ) ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let X := A + |X0| + 2
  have hX0 : X0 ≤ X := by dsimp [X]; linarith [le_abs_self X0]
  have hX1 : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg X0]
  have hXp : 0 < X := by linarith
  have hXA : A < X := by dsimp [X]; linarith [abs_nonneg X0]
  have hXsq : X ≤ X ^ 2 := by nlinarith [mul_nonneg hXp.le (sub_nonneg.mpr hX1)]
  have hASq : A < X ^ 2 := hXA.trans_le hXsq
  have hh := h X hX0 hX1
  change 8 * (1 + δ) ^ 2 * X ^ 4 ≤ A * X ^ 2 at hh
  have hcoef : 1 ≤ 8 * (1 + δ) ^ 2 := by nlinarith [sq_nonneg δ]
  have hsmall : X ^ 4 ≤ 8 * (1 + δ) ^ 2 * X ^ 4 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef (pow_nonneg hXp.le 4)
  have hlarge : A * X ^ 2 < X ^ 4 := by
    have hmul := mul_lt_mul_of_pos_right hASq (sq_pos_of_pos hXp)
    nlinarith only [hmul]
  exact not_lt_of_ge (hsmall.trans hh) hlarge

theorem ee_le_weighted_unconditional {x δ : ℝ} (hx : 128 ≤ x) (hδ : 0 < δ) :
    |∫ t in (x / 64)..(63 * x / 64), Ugm (t / x) * (Eθ δ t * Eθ δ (x - t))|
      ≤ ∫ y in Ioi 2, Eθ δ y ^ 2 * Wt (y / (x / 2)) := by
  exact ee_le_weighted hx hδ (weighted_error_integrable (by linarith : 0 < x / 2) hδ)

end LeanLab.Routes.Task79
