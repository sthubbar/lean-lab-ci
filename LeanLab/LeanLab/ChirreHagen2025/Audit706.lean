import Mathlib
import LeanLab.ChirreHagen2025.Decomp536a

/-!
A smooth-density audit of Ramare 2013 pages 117 and 118.
https://doi.org/10.4064/aa159-2-2
The zero-sum theorems and their sealed constants are unchanged.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Audit706
open MeasureTheory Set Filter Topology

/-- Ramare 2013 page 117 Lemma 4.2 and page 118 after equation 5.1.
The smooth counting density has a plus-one boundary contribution. -/
theorem smooth_density_integral (T : ℝ) (hT : 2 * Real.pi ≤ T) :
    IntegrableOn (fun t : ℝ => Real.log (t / (2 * Real.pi)) / (2 * Real.pi * t ^ 2)) (Ioi T) ∧
    (∫ t in Ioi T, Real.log (t / (2 * Real.pi)) / (2 * Real.pi * t ^ 2)) =
      (Real.log (T / (2 * Real.pi)) + 1) / (2 * Real.pi * T) := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hT0 : 0 < T := hp.trans_le hT
  let F : ℝ → ℝ := fun t => -(Real.log (t / (2 * Real.pi)) + 1) / (2 * Real.pi * t)
  have hd (t : ℝ) (ht : t ∈ Ici T) : HasDerivAt F
      (Real.log (t / (2 * Real.pi)) / (2 * Real.pi * t ^ 2)) t := by
    have ht0 : t ≠ 0 := ne_of_gt (hT0.trans_le ht)
    have hl := ((hasDerivAt_id t).div_const (2 * Real.pi)).log
      (div_ne_zero ht0 hp.ne')
    have hh := ((hl.add_const 1).neg).div
      ((hasDerivAt_id t).const_mul (2 * Real.pi)) (mul_ne_zero hp.ne' ht0)
    convert hh using 1
    · funext u
      rfl
    · simp only [id_eq, Pi.neg_apply]
      field_simp
      <;> ring
  have hz : Tendsto F atTop (𝓝 0) := by
    have hl : Tendsto (fun t : ℝ => Real.log t / t) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1 : ℝ) ≠ 0)
    have hi : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
      simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
    have hh := ((hl.sub (hi.const_mul (Real.log (2 * Real.pi) - 1))).div_const
      (2 * Real.pi)).neg
    convert hh.congr' ?_ using 1 <;> try norm_num
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    dsimp [F]
    rw [Real.log_div ht.ne' hp.ne']
    ring
  have hn (t : ℝ) (ht : t ∈ Ioi T) :
      0 ≤ Real.log (t / (2 * Real.pi)) / (2 * Real.pi * t ^ 2) := by
    apply div_nonneg _ (by positivity)
    apply Real.log_nonneg
    exact (le_div_iff₀ hp).mpr (by have htt : T < t := ht; linarith)
  have hi := integrableOn_Ioi_deriv_of_nonneg' hd hn hz
  refine ⟨hi, ?_⟩
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi hz
  rw [hh]
  dsimp [F]
  ring

/-- Ramare 2013 page 118, audit of the smooth density at the printed cutoff.
This concerns the smooth density integral, not an actual zero-tail sum. -/
theorem smooth_density_at_cutoff_gt_printed_error :
    1.75 / 10 ^ 12 <
      ∫ t in Ioi (2.44 * 10 ^ 12 : ℝ),
        Real.log (t / (2 * Real.pi)) / (2 * Real.pi * t ^ 2) := by
  rw [(smooth_density_integral (2.44 * 10 ^ 12)
    (by nlinarith [Real.pi_lt_four])).2]
  have hp : 0 < 2 * Real.pi := by positivity
  have hpi : Real.pi < 3.142 := by linarith [Real.pi_lt_d6]
  have he26 : Real.exp 26 ≤ (2.719 : ℝ) ^ 26 := by
    calc
      _ = Real.exp 1 ^ 26 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := by gcongr; linarith [Real.exp_one_lt_d9]
  have hl : 26 < Real.log ((2.44 * 10 ^ 12 : ℝ) / (2 * Real.pi)) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    apply he26.trans_lt
    apply (lt_div_iff₀ hp).mpr
    nlinarith
  apply (lt_div_iff₀ (by positivity : 0 < 2 * Real.pi * (2.44 * 10 ^ 12))).mpr
  nlinarith

/-- Ramare 2013 page 117 Lemma 4.2, the literal smooth counting contribution.
This substitutes the smooth count for the actual discrete zero count. -/
theorem smooth_count_partial_summation (T : ℝ) (hT : 2 * Real.pi ≤ T) :
    IntegrableOn (fun t : ℝ =>
      2 * (Decomp536a.smoothCount t - Decomp536a.smoothCount T) / t ^ 3) (Ioi T) ∧
    (∫ t in Ioi T,
      2 * (Decomp536a.smoothCount t - Decomp536a.smoothCount T) / t ^ 3) =
      (Real.log (T / (2 * Real.pi)) + 1) / (2 * Real.pi * T) := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hT0 : 0 < T := hp.trans_le hT
  have hd := Audit706.smooth_density_integral T hT
  have he (k : ℕ) :
      (fun t : ℝ => t ^ (-(k : ℝ))) =ᵐ[volume.restrict (Ioi T)]
        (fun t : ℝ => 1 / t ^ k) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.rpow_neg (hT0.trans ht).le, Real.rpow_natCast, one_div]
  have h2 : IntegrableOn (fun t : ℝ => 1 / t ^ 2) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT0).congr (he 2)
  have h3 : IntegrableOn (fun t : ℝ => 1 / t ^ 3) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hT0).congr (he 3)
  have hi2 := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT0
  have hi3 := integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hT0
  have he2 : (fun t : ℝ => t ^ (-2 : ℝ)) =ᵐ[volume.restrict (Ioi T)]
      (fun t : ℝ => 1 / t ^ 2) := by simpa using he 2
  have he3 : (fun t : ℝ => t ^ (-3 : ℝ)) =ᵐ[volume.restrict (Ioi T)]
      (fun t : ℝ => 1 / t ^ 3) := by simpa using he 3
  rw [integral_congr_ae he2] at hi2
  rw [integral_congr_ae he3] at hi3
  norm_num [Real.rpow_neg hT0.le] at hi2 hi3
  simp only [← one_div] at hi2 hi3
  let k : ℝ := 7 / 8 - Decomp536a.smoothCount T
  have heq : (fun t : ℝ =>
      2 * (Decomp536a.smoothCount t - Decomp536a.smoothCount T) / t ^ 3) =ᵐ[
        volume.restrict (Ioi T)]
      (fun t : ℝ =>
        2 * (Real.log (t / (2 * Real.pi)) / (2 * Real.pi * t ^ 2)) -
          (2 / (2 * Real.pi)) * (1 / t ^ 2) + (2 * k) * (1 / t ^ 3)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 := ne_of_gt (hT0.trans ht)
    dsimp [Decomp536a.smoothCount, k]
    field_simp [ht0, Real.pi_ne_zero]
    <;> ring
  have hi := ((hd.1.const_mul 2).sub (h2.const_mul (2 / (2 * Real.pi)))).add
    (h3.const_mul (2 * k))
  refine ⟨hi.congr heq.symm, ?_⟩
  have hadd := integral_add
    ((hd.1.const_mul 2).sub (h2.const_mul (2 / (2 * Real.pi))))
    (h3.const_mul (2 * k))
  simp only [Pi.sub_apply] at hadd
  have hsub := integral_sub (hd.1.const_mul 2) (h2.const_mul (2 / (2 * Real.pi)))
  rw [integral_congr_ae heq, hadd, hsub,
    integral_const_mul, integral_const_mul, integral_const_mul, hd.2, hi2, hi3]
  dsimp [k, Decomp536a.smoothCount]
  field_simp [hT0.ne', Real.pi_ne_zero]
  <;> ring

/-- P0075 page 4 Lemma 2.3, audit of the weaker inherited pointwise envelope.
Its integral exceeds the target budget throughout the stated range.
This compares the envelope, not the actual zeta integrand. -/
theorem pointwise_envelope_integral_too_large (T : ℝ) (hT : 4 * 10 ^ 13 ≤ T) :
    (∫ t in (10 ^ 4 : ℝ)..T, 10 * t) = 5 * (T ^ 2 - (10 ^ 4 : ℝ) ^ 2) ∧
    0.8056 * T < ∫ t in (10 ^ 4 : ℝ)..T, 10 * t := by
  have hi : (∫ t in (10 ^ 4 : ℝ)..T, 10 * t) =
      5 * (T ^ 2 - (10 ^ 4 : ℝ) ^ 2) := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  refine ⟨hi, ?_⟩
  rw [hi]
  nlinarith [sq_nonneg (T - 10000)]

end LeanLab.ChirreHagen2025.Audit706
