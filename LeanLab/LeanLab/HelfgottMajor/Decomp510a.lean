import Mathlib
import LeanLab.HelfgottMajor.Sec45
import LeanLab.HelfgottMajor.Gamma503
import LeanLab.HelfgottMajor.ZeroCount1623
import LeanLab.HelfgottMajor.BookP1617
import LeanLab.Helfgott2013.GammaFine
import LeanLab.HelfgottArcs.Statements

/-!
The convergence domain of the raw Gaussian Mellin integral.
Source P0014 Section 2.3, page 8, and the Gaussian transform on page 43.
These statements concern the Bochner integral, not its analytic continuation.
They supply boundary checks for Corollary 3.2 on page 10.
AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Decomp510a
open Real MeasureTheory LeanLab.HelfgottArcs SplitGaussian123

/-- The defining Gaussian Mellin integral converges exactly in the positive half plane.
Derived convergence support for P0014 page 8 and page 43 display 4.43.
The Fourier modulation has norm one and cannot change absolute convergence. -/
theorem gaussian_mellin_integrable_iff (δ : ℝ) (s : ℂ) :
    IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ (s - 1) • ((exp (-t ^ 2 / 2) : ℂ) * e (δ * t))) (Set.Ioi 0) ↔
      0 < s.re := by
  have hm : AEStronglyMeasurable (fun t : ℝ =>
      (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) (volume.restrict (Set.Ioi 0)) := by
    have hc : Continuous (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) := by
      unfold e
      fun_prop
    exact hc.aestronglyMeasurable
  have hn (t : ℝ) : ‖(exp (-t ^ 2 / 2) : ℂ) * e (δ * t)‖ = exp (-t ^ 2 / 2) := by
    have he : ‖e (δ * t)‖ = 1 := by simp [e, Complex.norm_exp, Complex.mul_re]
    rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (exp_pos _)]
  rw [mellin_convergent_iff_norm Set.Subset.rfl measurableSet_Ioi hm]
  simp_rw [hn]
  constructor
  · intro hi
    have hsmall : IntegrableOn (fun t : ℝ => exp (-(1 / 2 : ℝ)) * t ^ (s.re - 1))
        (Set.Ioo (0 : ℝ) 1) := by
      apply (hi.mono_set Set.Ioo_subset_Ioi_self).mono'
      · exact (measurable_const.mul (measurable_id.pow_const _)).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _),
          abs_of_nonneg (rpow_nonneg ht.1.le _)]
        have hsq : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
        have he : exp (-(1 / 2 : ℝ)) ≤ exp (-t ^ 2 / 2) :=
          exp_le_exp.mpr (by linarith)
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right he (rpow_nonneg ht.1.le _)
    have hp : IntegrableOn (fun t : ℝ => t ^ (s.re - 1)) (Set.Ioo (0 : ℝ) 1) :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (exp_pos _).ne') _).mp hsmall
    have h := (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mp hp
    linarith
  · intro hs
    have hi := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := s.re - 1) (p := 2) (b := (1 / 2 : ℝ))
      (by linarith) (by norm_num) (by norm_num)
    refine hi.congr_fun (fun t ht => ?_) measurableSet_Ioi
    dsimp only
    rw [rpow_two]
    congr 2
    ring

/-- Outside the convergence half plane the raw Bochner Mellin integral is zero.
Source P0014 Section 2.3 page 8, with the integral convention made explicit.
This is not the value of the analytic continuation used in Section 3. -/
theorem raw_gaussian_mellin_zero_of_nonpos (δ : ℝ) (s : ℂ) (hs : s.re ≤ 0) :
    mellin (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (δ * t)) s = 0 := by
  apply integral_undef
  exact fun hi => (not_lt.mpr hs) ((gaussian_mellin_integrable_iff δ s).mp hi)

/-- On the imaginary axis away from zero, the raw zero shift integral differs from
its Gamma continuation. Source P0014 page 29 before display 3.76.
This diagnoses an object convention, not the decay inequality of Corollary 3.2. -/
theorem raw_gaussian_mellin_ne_gamma_on_boundary (s : ℂ)
    (hs : s.re = 0) (him : s.im ≠ 0) :
    mellin (fun t : ℝ => (exp (-t ^ 2 / 2) : ℂ) * e (0 * t)) s ≠
      (2 : ℂ) ^ (s / 2 - 1) * Complex.Gamma (s / 2) := by
  rw [raw_gaussian_mellin_zero_of_nonpos 0 s hs.le]
  apply Ne.symm
  apply mul_ne_zero
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  · apply Complex.Gamma_ne_zero
    intro n heq
    have h := congrArg Complex.im heq
    simp only [Complex.div_ofNat_im, Complex.neg_im, Complex.natCast_im, neg_zero] at h
    exact him ((div_eq_zero_iff).mp h |>.resolve_right (by norm_num))

/-- The scalar residue budget after display 4.22 on P0014 page 37.
CONDITIONAL ON the supplied logarithmic derivative estimate.
The missing finite critical line input is not removed by this arithmetic. -/
theorem residue_bound_of_log_derivative (q : ℕ) (hq : 3 ≤ q) (z : ℂ)
    (hz : ‖z‖ ≤ 2 * log q + 15.07017) :
    ‖((log (2 * π / q) + eulerMascheroniConstant : ℝ) : ℂ) - z‖ ≤
      3 * log q + 15.289 := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hlog3 : (1.098612288 : ℝ) < log 3 := by
    have heq : log (3 : ℝ) = log 2 + log (3 / 2) := by
      rw [← log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
      norm_num
    rw [heq]
    linarith [log_two_gt_d9, LeanLab.Helfgott2013.GammaFine.log_three_halves_gt]
  have hlogq : (1.098612288 : ℝ) ≤ log q :=
    hlog3.le.trans (log_le_log (by norm_num) hq3)
  have hc : log (2 * π) + eulerMascheroniConstant ≤ 2.415094751 := by
    rw [log_mul (by norm_num) pi_ne_zero]
    linarith [BookP1617.log_pi_lt, log_two_lt_d9,
      LeanLab.Helfgott2013.GammaFine.gamma_lt_fine]
  have hc0 : 0 ≤ log (2 * π) + eulerMascheroniConstant := by
    have hl : 0 ≤ log (2 * π) := log_nonneg (by linarith [pi_gt_three])
    linarith [one_half_lt_eulerMascheroniConstant]
  have hscalar : |log (2 * π / q) + eulerMascheroniConstant| ≤ log q + 0.21883 := by
    rw [log_div (by positivity) hq0.ne']
    apply abs_le.mpr
    constructor <;> linarith
  calc
    _ ≤ ‖((log (2 * π / q) + eulerMascheroniConstant : ℝ) : ℂ)‖ + ‖z‖ := norm_sub_le _ _
    _ = |log (2 * π / q) + eulerMascheroniConstant| + ‖z‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ _ := by linarith

/-- Removing the height one cutoff only increases the squared Mellin mass.
Derived finite sum bookkeeping for P0014 pages 39 and 40.
This supplies the elementary cutoff leaf of the old discrete split and no sampling estimate. -/
theorem squared_mass_cutoff_le_full (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : ZeroCount1623.ZeroIdx χ T,
      Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    ∑' ρ : ZeroCount1623.ZeroIdx χ T,
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ ρ.val‖ ^ 2 := by
  classical
  have := ZeroCount1623.zeroIdx_finite χ T
  apply Summable.tsum_le_tsum _ Summable.of_finite Summable.of_finite
  intro ρ
  exact Set.indicator_le_self' (fun _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) ρ

/-- The height factor is at most the cutoff T term by term in the finite squared mass.
Derived bookkeeping for P0014 pages 39 and 40 and the old discrete split.
No discrete Plancherel or numerical zero count bound is asserted. -/
theorem squared_mass_height_pullout (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (δ T : ℝ) :
    (∑' ρ : ZeroCount1623.ZeroIdx χ T,
      Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          |ρ.val.im| * ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) ≤
    T * (∑' ρ : ZeroCount1623.ZeroIdx χ T,
      Set.indicator {ρ | |ρ.val.im| ≤ 1}ᶜ
        (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
          ‖gaussianMellin δ ρ.val‖ ^ 2) ρ) := by
  classical
  have := ZeroCount1623.zeroIdx_finite χ T
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ Summable.of_finite Summable.of_finite
  intro ρ
  by_cases h : |ρ.val.im| ≤ 1
  · simp [Set.indicator, h]
  · have hmem : ρ ∈ {ρ : ZeroCount1623.ZeroIdx χ T | |ρ.val.im| ≤ 1}ᶜ := h
    simp only [Set.indicator_of_mem hmem]
    calc
      _ = |ρ.val.im| *
          ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
            ‖gaussianMellin δ ρ.val‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ρ.property.2.2.2
        (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- The k equal to zero main coefficient in display 3.69 on P0014 page 27.
Convexity in one minus sigma reduces the estimate to its two endpoints.
This supplies scalar arithmetic and no saddle contour expansion. -/
theorem saddle_main_coefficient_bound (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    2 * (1 + (7.83 : ℝ) ^ (1 - σ)) * ((3 / 2 : ℝ) / (2 * π)) ^ (1 - σ) ≤
      4.217 := by
  let a : ℝ := (3 / 2 : ℝ) / (2 * π)
  have ha : 0 < a := by dsimp [a]; positivity
  have hc := (convexOn_rpow_left ha).add
    (convexOn_rpow_left (mul_pos (by norm_num : (0 : ℝ) < 7.83) ha))
  have h := hc.le_max_of_mem_Icc (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (show 1 - σ ∈ Set.Icc (0 : ℝ) 1 by constructor <;> linarith)
  simp only [Pi.add_apply, rpow_zero, rpow_one] at h
  have hend : a + 7.83 * a ≤ 2.1085 := by
    have heq : a + 7.83 * a = 13.245 / (2 * π) := by dsimp [a]; ring
    rw [heq, div_le_iff₀ (by positivity)]
    nlinarith [pi_gt_d4]
  have hmax : max (1 + 1 : ℝ) (a + 7.83 * a) ≤ 2.1085 :=
    max_le (by norm_num) hend
  have heq : 2 * (1 + (7.83 : ℝ) ^ (1 - σ)) * a ^ (1 - σ) =
      2 * (a ^ (1 - σ) + (7.83 * a) ^ (1 - σ)) := by
    rw [mul_rpow (by norm_num : (0 : ℝ) ≤ 7.83) ha.le]
    ring
  change 2 * (1 + (7.83 : ℝ) ^ (1 - σ)) * a ^ (1 - σ) ≤ _
  rw [heq]
  linarith [h.trans hmax]

/-- One strip zero contributes at least its unweighted squared Mellin norm.
Derived source audit support for P0014 pages 39 and 40.
Nontriviality gives an entire nonzero L function and hence positive finite multiplicity. -/
theorem single_squared_mass_le_full_mass (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (δ T : ℝ)
    (ρ : ZeroCount1623.ZeroIdx χ T) :
    ‖gaussianMellin δ ρ.val‖ ^ 2 ≤
      ∑' z : ZeroCount1623.ZeroIdx χ T,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) z.val : ℝ) *
          ‖gaussianMellin δ z.val‖ ^ 2 := by
  classical
  have ha : ∀ z : ℂ, AnalyticAt ℂ (DirichletCharacter.LFunction χ) z :=
    fun z => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hf : analyticOrderAt (DirichletCharacter.LFunction χ) ρ.val ≠ ⊤ := by
    intro ht
    have heq : DirichletCharacter.LFunction χ = 0 :=
      (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero
        (f := DirichletCharacter.LFunction χ) ρ.val ha).mp ht
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (show (1 : ℝ) ≤ (2 : ℂ).re by norm_num)) (congrFun heq 2)
  have hn : 0 < analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val := by
    apply Nat.pos_of_ne_zero
    intro hn
    have hc := Nat.cast_analyticOrderNatAt hf
    rw [hn] at hc
    have hz : analyticOrderAt (DirichletCharacter.LFunction χ) ρ.val ≠ 0 :=
      (ha ρ.val).analyticOrderAt_ne_zero.mpr ρ.property.1
    exact hz hc.symm
  have hnr : (1 : ℝ) ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val := by
    exact_mod_cast hn
  have := ZeroCount1623.zeroIdx_finite χ T
  let _ := Fintype.ofFinite (ZeroCount1623.ZeroIdx χ T)
  rw [tsum_fintype]
  calc
    _ ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ.val : ℝ) *
        ‖gaussianMellin δ ρ.val‖ ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) hnr
    _ ≤ _ := Finset.single_le_sum
      (f := fun z : ZeroCount1623.ZeroIdx χ T =>
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) z.val : ℝ) *
          ‖gaussianMellin δ z.val‖ ^ 2)
      (fun z _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) (Finset.mem_univ ρ)

/-- A single zero with the externally tested mass rules out the old full mass split.
Derived audit of the lab leaf associated with P0014 pages 39 and 40.
CONDITIONAL ON the supplied zero and norm certificate. This is not a paper theorem refutation. -/
theorem full_mass_bound_fails_of_single_zero (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (δ T : ℝ)
    (ρ : ZeroCount1623.ZeroIdx χ T) (hlarge : 3.94 ≤ ‖gaussianMellin δ ρ.val‖ ^ 2) :
    ¬ (∑' z : ZeroCount1623.ZeroIdx χ T,
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) z.val : ℝ) *
        ‖gaussianMellin δ z.val‖ ^ 2) ≤ Sec45.nTwo + Sec45.nLog := by
  have hsingle := single_squared_mass_le_full_mass q χ hχ δ T ρ
  have hbudget : Sec45.nTwo + Sec45.nLog < 2.834 := by
    have htwo : Sec45.nTwo < 0.886227 := by
      unfold Sec45.nTwo
      linarith [Sec45.sqrt_pi_lt]
    linarith [Sec45.nLog_le]
  intro hbound
  linarith

/-- The character hypotheses for the modulo 163 sampling audit are inhabited.
Derived source audit support for P0014 pages 39 and 40.
This proves the character facts and no assertion about its zeros. -/
theorem exists_primitive_odd_mod163 :
    ∃ χ : DirichletCharacter ℂ 163, χ.IsPrimitive ∧ χ ≠ 1 ∧ χ.Odd := by
  let _ : Fact (Nat.Prime 163) := ⟨by norm_num⟩
  let χ : DirichletCharacter ℂ 163 :=
    (quadraticChar (ZMod 163)).ringHomComp (Int.castRingHom ℂ)
  have hχ : χ ≠ 1 := by
    apply (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := ℂ))).mpr
    exact quadraticChar_ne_one
      (by rw [ZMod.ringChar_zmod_n]; decide : ringChar (ZMod 163) ≠ 2)
  have hodd : χ.Odd := by
    have hs : quadraticChar (ZMod 163) (-1) = -1 := by
      rw [quadraticChar_neg_one
        (by rw [ZMod.ringChar_zmod_n]; decide : ringChar (ZMod 163) ≠ 2)]
      norm_num [ZMod.χ₄_nat_eq_if_mod_four]
    change (Int.castRingHom ℂ) (quadraticChar (ZMod 163) (-1)) = -1
    rw [hs]
    simp
  refine ⟨χ, ?_, hχ, hodd⟩
  change DirichletCharacter.conductor χ = 163
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 163)).mp
    (DirichletCharacter.conductor_dvd_level χ) with h | h
  · exact False.elim (hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))
  · exact h

end LeanLab.HelfgottMajor.Decomp510a
