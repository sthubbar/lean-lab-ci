import LeanLab.HelfgottMajor.HalfMoment389

/-!
The Gaussian half power moment in P0014 page 43, display 4.42.
A rational Taylor certificate and a derivative tail prove 1.03045.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.WeightedMoment389
open Real MeasureTheory Set Filter
open scoped Topology

/-- The integrated even Taylor bound for the weighted quartic core in display 4.42.
The split point is nine quarters after t equals u squared.
-/
theorem weighted_core_bound (n : ℕ) :
    (∫ u in (0 : ℝ)..(9 / 4 : ℝ), u ^ 2 * exp (-u ^ 4 / 2)) ≤
      (9 / 4 : ℝ) ^ 3 * ∑ k ∈ Finset.range (2 * n + 1),
        (-6561 / 512 : ℝ) ^ k / ((k.factorial : ℝ) * (4 * k + 3)) := by
  let p : ℝ → ℝ := fun u => ∑ k ∈ Finset.range (2 * n + 1),
    ((-1 / 2 : ℝ) ^ k / (k.factorial : ℝ)) * u ^ (4 * k + 2)
  have hp : Continuous p := by unfold p; fun_prop
  have hmaj (u : ℝ) : u ^ 2 * exp (-u ^ 4 / 2) ≤ p u := by
    have h := HalfMoment389.exp_neg_le_even_sum (u ^ 4 / 2) (by positivity) n
    have heq : p u = u ^ 2 * ∑ k ∈ Finset.range (2 * n + 1),
        (-(u ^ 4 / 2)) ^ k / (k.factorial : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [show -(u ^ 4 / 2) = (-1 / 2 : ℝ) * u ^ 4 by ring,
        mul_pow, ← pow_mul, pow_add]
      ring
    rw [heq]
    simpa only [neg_div] using mul_le_mul_of_nonneg_left h (sq_nonneg u)
  calc
    _ ≤ ∫ u in (0 : ℝ)..(9 / 4 : ℝ), p u :=
      intervalIntegral.integral_mono_on (by norm_num)
        ((by fun_prop : Continuous (fun u : ℝ => u ^ 2 * exp (-u ^ 4 / 2))).intervalIntegrable _ _)
        (hp.intervalIntegrable _ _) (fun u _ => hmaj u)
    _ = _ := by
      unfold p
      rw [intervalIntegral.integral_finsetSum]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [intervalIntegral.integral_const_mul, integral_pow]
        simp only [zero_pow (by omega : 4 * k + 2 + 1 ≠ 0), sub_zero]
        have hpow : (9 / 4 : ℝ) ^ (4 * k + 2 + 1) = (9 / 4 : ℝ) ^ 3 * ((9 / 4 : ℝ) ^ 4) ^ k := by
          rw [show 4 * k + 2 + 1 = 4 * k + 3 by omega, pow_add, pow_mul]
          ring
        rw [hpow]
        have hmix : (-1 / 2 : ℝ) ^ k * ((9 / 4 : ℝ) ^ 4) ^ k = (-6561 / 512 : ℝ) ^ k := by
          rw [← mul_pow]
          norm_num
        push_cast
        rw [div_mul_div_comm]
        have hnum : (-1 / 2 : ℝ) ^ k * ((9 / 4 : ℝ) ^ 3 * ((9 / 4 : ℝ) ^ 4) ^ k) =
            (9 / 4 : ℝ) ^ 3 * (-6561 / 512 : ℝ) ^ k := by
          calc
            _ = (9 / 4 : ℝ) ^ 3 * ((-1 / 2 : ℝ) ^ k * ((9 / 4 : ℝ) ^ 4) ^ k) := by ring
            _ = _ := by rw [hmix]
        rw [hnum]
        ring
      · intro k hk
        exact (continuous_const.mul (continuous_pow _)).intervalIntegrable _ _

/-- The weighted quartic tail majorant for the half power moment in display 4.42. -/
theorem weighted_tail_bound :
    (∫ u in Ioi (9 / 4 : ℝ), u ^ 2 * exp (-u ^ 4 / 2)) ≤
      (2 / 9 : ℝ) * exp (-6561 / 512) := by
  let g : ℝ → ℝ := fun u => -(2 / 9 : ℝ) * exp (-u ^ 4 / 2)
  let g' : ℝ → ℝ := fun u => (4 / 9 : ℝ) * u ^ 3 * exp (-u ^ 4 / 2)
  have hd (u : ℝ) : HasDerivAt g (g' u) u := by
    have hh := ((((hasDerivAt_id u).pow 4).neg.div_const 2).exp).const_mul (-(2 / 9 : ℝ))
    convert hh using 1
    · rfl
    · dsimp [g']; norm_num; ring
  have hc : ContinuousWithinAt g (Ici (9 / 4)) (9 / 4) := by unfold g; fun_prop
  have hl : Tendsto g atTop (nhds 0) := by
    have hh : Tendsto (fun u : ℝ => u ^ 4 / 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).atTop_div_const (by norm_num)
    have he := (tendsto_exp_neg_atTop_nhds_zero.comp hh).const_mul (-(2 / 9 : ℝ))
    simpa [g, neg_div] using he
  have hpos : ∀ u ∈ Ioi (9 / 4 : ℝ), 0 ≤ g' u := by
    intro u hu
    have hu0 : 0 ≤ u := by linarith [show 9 / 4 < u from hu]
    dsimp [g']
    positivity
  have hg : IntegrableOn g' (Ioi (9 / 4)) :=
    integrableOn_Ioi_deriv_of_nonneg hc (fun u _ => hd u) hpos hl
  have hbound : ∀ u ∈ Ioi (9 / 4 : ℝ), u ^ 2 * exp (-u ^ 4 / 2) ≤ g' u := by
    intro u hu
    have hu' : 0 ≤ u - 9 / 4 := by linarith [show 9 / 4 < u from hu]
    have hcub : u ^ 2 ≤ (4 / 9 : ℝ) * u ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg u) hu']
    exact mul_le_mul_of_nonneg_right hcub (exp_pos _).le
  have hf : IntegrableOn (fun u : ℝ => u ^ 2 * exp (-u ^ 4 / 2)) (Ioi (9 / 4)) := by
    apply hg.mono' (by fun_prop : Continuous (fun u : ℝ => u ^ 2 * exp (-u ^ 4 / 2))).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound u hu
  calc
    _ ≤ ∫ u in Ioi (9 / 4 : ℝ), g' u := integral_mono_ae hf hg <|
      (ae_restrict_mem measurableSet_Ioi).mono (fun u hu => hbound u hu)
    _ = _ := by
      rw [integral_Ioi_of_hasDerivAt_of_nonneg hc (fun u _ => hd u) hpos hl]
      norm_num [g]

/-- The rational certificate for the whole weighted quartic moment behind display 4.42. -/
theorem weighted_quartic_bound :
    (∫ u in Ioi (0 : ℝ), u ^ 2 * exp (-u ^ 4 / 2)) ≤ 0.5152246 := by
  have hi : IntegrableOn (fun u : ℝ => u ^ 2 * exp (-u ^ 4 / 2)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := (2 : ℝ)) (p := (4 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    apply h.congr_fun _ measurableSet_Ioi
    intro u hu
    norm_num only [rpow_two, rpow_ofNat]
    congr 2
    ring
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi
    (hi.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 9 / 4)))
  have hc := weighted_core_bound 24
  have hcert : (2 : ℝ) * (9 / 4 : ℝ) ^ 3 * ∑ k ∈ Finset.range 49,
      (-6561 / 512 : ℝ) ^ k / ((k.factorial : ℝ) * (4 * k + 3)) ≤ 1.0304474 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have he : exp (-6561 / 512) ≤ (0.00000373 : ℝ) := by
    have he25 : exp (-25) ≤ (0.00000373 : ℝ) ^ 2 := by
      have heq : exp (-25) = exp (-1) ^ 25 := by rw [← exp_nat_mul]; norm_num
      rw [heq]
      calc
        _ ≤ (0.3678794412 : ℝ) ^ 25 := by gcongr; exact exp_neg_one_lt_d9.le
        _ ≤ _ := by norm_num
    have hs : exp (-25 / 2) ^ 2 = exp (-25) := by
      rw [pow_two, ← exp_add]
      congr 1
      norm_num
    have hh : exp (-25 / 2) ≤ (0.00000373 : ℝ) := by nlinarith [exp_nonneg (-25 / 2)]
    exact (exp_le_exp.mpr (by norm_num : (-6561 / 512 : ℝ) ≤ -25 / 2)).trans hh
  have ht := weighted_tail_bound
  norm_num only [show 2 * (24 : ℕ) + 1 = 49 by norm_num] at hc
  nlinarith

/-- The Gaussian half power moment is at most 1.03045, P0014 page 43, display 4.42. -/
theorem gaussian_half_power_bound :
    (∫ t in Ioi (0 : ℝ), t ^ (1 / 2 : ℝ) * exp (-t ^ 2 / 2)) ≤ 1.03045 := by
  have hs := integral_comp_rpow_Ioi_of_pos
    (g := fun t : ℝ => t ^ (1 / 2 : ℝ) * exp (-t ^ 2 / 2))
    (p := (2 : ℝ)) (by norm_num)
  have he : (∫ u in Ioi (0 : ℝ),
      (2 * u ^ ((2 : ℝ) - 1)) •
        ((u ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * exp (-(u ^ (2 : ℝ)) ^ 2 / 2))) =
      2 * ∫ u in Ioi (0 : ℝ), u ^ 2 * exp (-u ^ 4 / 2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hp : (u ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = u := by
      rw [← rpow_mul (show 0 ≤ u from le_of_lt hu)]
      norm_num
    dsimp only
    rw [hp]
    simp only [show (2 : ℝ) - 1 = 1 by norm_num, rpow_one, smul_eq_mul, rpow_two]
    rw [show -(u ^ 2) ^ 2 / 2 = -u ^ 4 / 2 by ring]
    ring
  rw [he] at hs
  have hh := weighted_quartic_bound
  linarith

end LeanLab.HelfgottMajor.WeightedMoment389
