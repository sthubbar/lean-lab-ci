import LeanLab.ChirreHagen2025.Statements

/-!
A conservative scalar repair for Ramare 2013 pages 119 and 120.
This supplies an elementary upper bound for the auxiliary integral only.
It does not supply a zeta zero estimate.
https://doi.org/10.4064/aa159-2-2
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.IntegralRepair391c
open MeasureTheory Filter Set Topology

/-- Ramare page 119 auxiliary integral, a valid arithmetic-geometric comparison. -/
theorem exponent_split (a u : ℝ) (ha : 0 ≤ a) (hu : 0 < u) :
    -a / u - u ≤ -Real.sqrt (2 * a) - u / 2 := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * a)
  have hsq := sq_nonneg (u - Real.sqrt (2 * a))
  have hh : Real.sqrt (2 * a) - u / 2 ≤ a / u := by
    apply (le_div_iff₀ hu).mpr
    nlinarith
  rw [neg_div]
  linarith

/-- Ramare page 119 auxiliary integral, the elementary exponential primitive. -/
theorem exponential_primitive (u : ℝ) :
    HasDerivAt (fun v : ℝ => -(2 * v + 4) * Real.exp (-v / 2))
      (u * Real.exp (-u / 2)) u := by
  have hp := (((hasDerivAt_id u).const_mul 2).add_const 4).neg
  have he := (((hasDerivAt_id u).neg).div_const 2).exp
  convert hp.mul he using 1
  · ext v
    simp only [Pi.mul_apply, Pi.neg_apply, Pi.add_apply, id_eq]
  · simp only [Pi.mul_apply, Pi.neg_apply, Pi.add_apply, id_eq]
    ring

/-- Ramare page 119 auxiliary integral, the primitive vanishes at infinity. -/
theorem exponential_primitive_limit :
    Tendsto (fun u : ℝ => -(2 * u + 4) * Real.exp (-u / 2)) atTop (𝓝 0) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (1 / 2) (by norm_num)
  have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) (1 / 2) (by norm_num)
  have hh := ((h1.const_mul (-2)).add (h0.const_mul (-4)))
  convert hh using 1
  · funext u
    simp only [Real.rpow_one, Real.rpow_zero, one_mul]
    ring_nf
  · norm_num

/-- Ramare page 119 auxiliary integral, an integrable positive majorant. -/
theorem exponential_tail (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (fun u : ℝ => u * Real.exp (-u / 2)) (Ioi t) ∧
    (∫ u in Ioi t, u * Real.exp (-u / 2)) = (2 * t + 4) * Real.exp (-t / 2) := by
  have hd := fun u (_ : u ∈ Ici t) => exponential_primitive u
  have hn : ∀ u ∈ Ioi t, 0 ≤ u * Real.exp (-u / 2) := by
    intro u hu
    have hu0 : 0 ≤ u := by have htu : t < u := hu; linarith
    exact mul_nonneg hu0 (Real.exp_pos _).le
  constructor
  · exact integrableOn_Ioi_deriv_of_nonneg' hd hn exponential_primitive_limit
  · have hh := integral_Ioi_of_hasDerivAt_of_nonneg' hd hn exponential_primitive_limit
    simpa only [zero_sub, neg_mul, neg_neg] using hh

/-- Ramare page 119 auxiliary integral, a valid upper envelope with convergence.
This replaces only the audited scalar integration step, not its zero inputs. -/
theorem auxiliary_integral_bound (a t : ℝ) (ha : 0 ≤ a) (ht : 0 < t) :
    IntegrableOn (fun u : ℝ => u * Real.exp (-a / u - u) / (2 * Real.pi)) (Ioi t) ∧
    (∫ u in Ioi t, u * Real.exp (-a / u - u) / (2 * Real.pi)) ≤
      Real.exp (-Real.sqrt (2 * a)) * ((2 * t + 4) * Real.exp (-t / 2)) / (2 * Real.pi) := by
  let C := Real.exp (-Real.sqrt (2 * a)) / (2 * Real.pi)
  have hmaj := ((exponential_tail t ht.le).1.const_mul C)
  have hc : ContinuousOn (fun u : ℝ => u * Real.exp (-a / u - u) / (2 * Real.pi)) (Ioi t) := by
    have hd : ContinuousOn (fun u : ℝ => -a / u - u) (Ioi t) :=
      (continuousOn_const.div continuousOn_id (fun u hu => ne_of_gt (ht.trans hu))).sub continuousOn_id
    exact (continuousOn_id.mul (Real.continuous_exp.comp_continuousOn hd)).div_const _
  have hb : ∀ u ∈ Ioi t, u * Real.exp (-a / u - u) / (2 * Real.pi) ≤
      C * (u * Real.exp (-u / 2)) := by
    intro u hu
    have hu0 : 0 < u := ht.trans hu
    have he := Real.exp_le_exp.mpr (exponent_split a u ha hu0)
    have he' : Real.exp (-a / u - u) ≤
        Real.exp (-Real.sqrt (2 * a)) * Real.exp (-u / 2) := by
      convert he using 1
      rw [show -Real.sqrt (2 * a) - u / 2 = -Real.sqrt (2 * a) + (-u / 2) by ring,
        Real.exp_add]
    have hh := mul_le_mul_of_nonneg_left he' hu0.le
    have hh' := div_le_div_of_nonneg_right hh (by positivity : 0 ≤ 2 * Real.pi)
    convert hh' using 1 <;> dsimp [C] <;> ring
  have hi : IntegrableOn (fun u : ℝ => u * Real.exp (-a / u - u) / (2 * Real.pi)) (Ioi t) := by
    apply hmaj.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := ht.trans hu; positivity)]
    exact hb u hu
  refine ⟨hi, ?_⟩
  have hh := integral_mono_ae hi hmaj
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu; exact hb u hu)
  rw [integral_const_mul, (exponential_tail t ht.le).2] at hh
  convert hh using 1 <;> dsimp [C] <;> ring

/-- Ramare page 119 auxiliary integral, a uniform conservative envelope. -/
theorem auxiliary_integral_uniform (a t : ℝ) (ha : 0 ≤ a) (ht : 0 < t) :
    (∫ u in Ioi t, u * Real.exp (-a / u - u) / (2 * Real.pi)) ≤
      (2 / Real.pi) * Real.exp (-Real.sqrt (2 * a)) := by
  have hh := (auxiliary_integral_bound a t ha ht).2
  have hc : (2 * t + 4) * Real.exp (-t / 2) ≤ 4 := by
    rw [show -t / 2 = -(t / 2) by ring, Real.exp_neg, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith [Real.add_one_le_exp (t / 2)]
  calc
    _ ≤ Real.exp (-Real.sqrt (2 * a)) * ((2 * t + 4) * Real.exp (-t / 2)) /
        (2 * Real.pi) := hh
    _ ≤ Real.exp (-Real.sqrt (2 * a)) * 4 / (2 * Real.pi) := by gcongr
    _ = _ := by ring

/-- Ramare pages 119 and 120, a valid coarse replacement for the scaled error.
The parameter a at least 1568 covers the source transition since log T0 exceeds 28.
This theorem concerns only the auxiliary integral. -/
theorem auxiliary_integral_scaled (a t : ℝ) (ha : 1568 ≤ a) (ht : 0 < t) :
    (∫ u in Ioi t, u * Real.exp (-a / u - u) / (2 * Real.pi)) *
      (5.69693 * a) ^ 2 ≤ 1 / 1000 := by
  let v := Real.sqrt (2 * a)
  have ha0 : 0 ≤ a := by linarith
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hv2 : v ^ 2 = 2 * a := Real.sq_sqrt (by positivity)
  have hv : 56 ≤ v := by nlinarith
  have hexp : 9 * v ^ 4 ≤ (1 / 1000 : ℝ) * Real.exp v := by
    have hs := Real.pow_div_factorial_le_exp v hv0 11
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 56) hv 7
    have hm : (56 : ℝ) ^ 7 * v ^ 4 ≤ v ^ 11 := by
      calc
        _ ≤ v ^ 7 * v ^ 4 := mul_le_mul_of_nonneg_right hp (pow_nonneg hv0 4)
        _ = _ := by ring
    norm_num at hs hm
    nlinarith only [hs, hm, pow_nonneg hv0 4]
  have hL : (5.69693 * a) ^ 2 ≤ 9 * v ^ 4 := by
    have hv4 : v ^ 4 = 4 * a ^ 2 := by
      calc
        v ^ 4 = (v ^ 2) ^ 2 := by ring
        _ = 4 * a ^ 2 := by rw [hv2]; ring
    rw [hv4]
    nlinarith [sq_nonneg a]
  have hI := auxiliary_integral_uniform a t ha0 ht
  have hc : (2 / Real.pi : ℝ) ≤ 1 := by
    apply (div_le_one Real.pi_pos).mpr
    linarith [Real.pi_gt_three]
  have hI' : (∫ u in Ioi t, u * Real.exp (-a / u - u) / (2 * Real.pi)) ≤
      Real.exp (-v) := by
    apply hI.trans
    simpa [v] using mul_le_mul_of_nonneg_right hc (Real.exp_pos (-Real.sqrt (2 * a))).le
  calc
    _ ≤ Real.exp (-v) * (5.69693 * a) ^ 2 :=
      mul_le_mul_of_nonneg_right hI' (sq_nonneg _)
    _ ≤ Real.exp (-v) * (9 * v ^ 4) := mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le
    _ ≤ Real.exp (-v) * ((1 / 1000 : ℝ) * Real.exp v) :=
      mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
    _ = _ := by rw [Real.exp_neg]; field_simp

end LeanLab.ChirreHagen2025.IntegralRepair391c
