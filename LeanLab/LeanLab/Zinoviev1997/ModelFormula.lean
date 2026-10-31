/-
AI wrote this Lean code. Codex task69, 2026-10-25.
Elementary geometric model bounds for the integration range error in Lemma 3.2, page 355.
The constant one quarter below replaces the paper's sharper 0.16 bound.
Binary Goldbach is open.
-/
import LeanLab.Zinoviev1997.ModelBounds
import LeanLab.PNTPort.LargeSieve.Basic

namespace LeanLab.Zinoviev1997
open Real Finset Filter Topology LeanLab.CircleOrth MeasureTheory

theorem ee_nat_mul (n : ℕ) (α : ℝ) : ee (n * α) = ee α ^ n := by
  unfold ee
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The geometric ratio of the reflected model series. -/
noncomputable def modelRatio (N : ℕ) (α : ℝ) : ℂ :=
  (Real.exp (-1 / (N : ℝ)) : ℂ) * ee α

theorem norm_modelRatio (N : ℕ) (α : ℝ) :
    ‖modelRatio N α‖ = Real.exp (-1 / (N : ℝ)) := by
  rw [modelRatio, norm_mul, norm_ee, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

/-- The geometric expression stated on page 352. -/
theorem modelSum_geometric (N : ℕ) (hN : 0 < N) (α : ℝ) :
    modelSum N α = modelRatio N α ^ 3 / (1 - modelRatio N α) := by
  have hnr : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : ‖modelRatio N α‖ < 1 := by
    rw [norm_modelRatio]
    exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hnr)
  have hg := hasSum_geometric_of_norm_lt_one hr
  have ht : Summable (fun n : ℕ => (modelWeight N n : ℂ) * ee (n * α)) := by
    apply Summable.of_norm
    simp_rw [norm_modelTerm]
    exact summable_modelWeight hN
  have hshift := ht.sum_add_tsum_nat_add 3
  have hzero : (∑ n ∈ Finset.range 3, (modelWeight N n : ℂ) * ee (n * α)) = 0 := by
    norm_num [Finset.sum_range_succ, modelWeight]
  rw [hzero, zero_add] at hshift
  have he : ∀ n : ℕ, (modelWeight N (n + 3) : ℂ) * ee ((n + 3 : ℕ) * α) =
      modelRatio N α ^ (n + 3) := by
    intro n
    simp only [modelWeight, show 3 ≤ n + 3 by omega, ite_true, modelRatio, mul_pow]
    rw [ee_nat_mul]
    congr 1
    rw [← Complex.ofReal_pow]
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  change (∑' n : ℕ, (modelWeight N n : ℂ) * ee (n * α)) = _
  rw [← hshift]
  simp_rw [he]
  have hh := hg.mul_left (modelRatio N α ^ 3)
  have hp : (fun n : ℕ => modelRatio N α ^ 3 * modelRatio N α ^ n) =
      (fun n => modelRatio N α ^ (n + 3)) := by
    funext n
    rw [pow_add]
    ring
  rw [hp] at hh
  rw [hh.tsum_eq]
  ring

/-- Moving a unit complex point radially inward cannot reduce this scaled chord bound. -/
theorem radial_chord (u : ℂ) (hu : ‖u‖ = 1) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    r * ‖1 - u‖ ≤ ‖1 - (r : ℂ) * u‖ := by
  have hu2 : u.re ^ 2 + u.im ^ 2 = 1 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hu
    rw [Complex.sq_norm] at h
    simpa only [Complex.normSq_apply, one_pow, pow_two, one_mul] using h
  have hre : u.re ≤ 1 := by
    have h := (le_abs_self u.re).trans (Complex.abs_re_le_norm u)
    rwa [hu] at h
  have hinner : 0 ≤ 1 + r - 2 * r * u.re := by
    have hh := mul_le_mul_of_nonneg_left hre (show 0 ≤ 2 * r by positivity)
    nlinarith
  have hprod := mul_nonneg (show 0 ≤ 1 - r by linarith) hinner
  have hunit := congrArg (fun x : ℝ => r ^ 2 * x) hu2
  apply (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp
  rw [mul_pow]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  nlinarith

/-- A chord estimate on the centered full period. -/
theorem four_abs_le_chord (α : ℝ) (hα : |α| ≤ 1 / 2) : 4 * |α| ≤ ‖1 - ee α‖ := by
  rw [norm_sub_rev]
  have he : ee α = Complex.exp (Complex.I * ((2 * Real.pi * α : ℝ) : ℂ)) := by
    unfold ee
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
  have h := LeanLab.PNTPort.LargeSieve.two_abs_le_abs_sin hα
  rw [show 2 * Real.pi * α / 2 = Real.pi * α by ring]
  linarith

/-- A sufficient elementary replacement for the pointwise tail bound on page 355. -/
theorem modelSum_minor_bound (N : ℕ) (hN : 0 < N) (α : ℝ)
    (hα : 0 < |α|) (hα' : |α| ≤ 1 / 2) :
    ‖modelSum N α‖ ≤ 1 / (4 * |α|) := by
  let r := Real.exp (-1 / (N : ℝ))
  have hnr : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hnr)
  have hc := radial_chord (ee α) (norm_ee α) r hr.le hr1.le
  have hch := mul_le_mul_of_nonneg_left (four_abs_le_chord α hα') hr.le
  have hd : 4 * r * |α| ≤ ‖1 - modelRatio N α‖ := by
    change 4 * r * |α| ≤ ‖1 - (r : ℂ) * ee α‖
    nlinarith
  have hd0 : 0 < ‖1 - modelRatio N α‖ := lt_of_lt_of_le (by positivity) hd
  rw [modelSum_geometric N hN α, norm_div, norm_pow, norm_modelRatio]
  change r ^ 3 / ‖1 - modelRatio N α‖ ≤ _
  calc
    _ ≤ r / ‖1 - modelRatio N α‖ := by
      apply div_le_div_of_nonneg_right _ hd0.le
      have hh : r ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg hr.le (show 0 ≤ 1 - r by linarith)]
      calc r ^ 3 = r * r ^ 2 := by ring
           _ ≤ r * 1 := mul_le_mul_of_nonneg_left hh hr.le
           _ = r := by ring
    _ ≤ r / (4 * r * |α|) := div_le_div_of_nonneg_left hr.le (by positivity) hd
    _ = _ := by field_simp

end LeanLab.Zinoviev1997
