/-
Split of `campbell` in `AlmostPrimes/Statements.lean` into four leaves, following the
three-range structure recorded in `AlmostPrimes/PROGRESS.md` for that statement:

* `2 ≤ N ≤ N₀ = 117465180365547648498934439`: the short-interval argument on top of the
  maximal prime gap table input;
* `N₀ < N < 10^132`: the finite verification of a positive sieve sum on the middle range;
* `N ≥ 10^132`: the explicit sieve, which produces two positive summands every prime factor
  of which exceeds `N^(2/33)`;
* a positive integer all of whose prime factors exceed `N^(2/33)` has at most 16 prime
  factors with multiplicity, hence `Ω(ab) ≤ 16 + 16 ≤ 33` for two such summands.

Each leaf is weaker than the target and none of them restates it. `campbell_split` is proved
from the four leaves with no `sorry` and does not use `campbell`.
-/
import LeanLab.AlmostPrimes.Statements

namespace LeanLab.AlmostPrimes

section CampbellHelpers

open Finset Real MeasureTheory
open scoped Nat.Prime

/-! ### Private helpers for LEAVES 1 and 2

Everything below is proved from Mathlib alone: Abel summation against the Chebyshev
function, the double count of the prime factorisations, and the averaging argument. -/



/-! ## 1. The Abel integrand `t ↦ (t log t)⁻¹` -/

private theorem differentiableAt_inv_mul_log {t : ℝ} (ht : 2 ≤ t) :
    DifferentiableAt ℝ (fun s : ℝ => (s * Real.log s)⁻¹) t := by
  have ht0 : t ≠ 0 := by linarith
  have hne : t * Real.log t ≠ 0 := by
    have := Real.log_pos (by linarith : (1 : ℝ) < t)
    positivity
  exact (differentiableAt_id.mul (Real.differentiableAt_log ht0)).inv hne

private theorem deriv_inv_mul_log {t : ℝ} (ht : 2 ≤ t) :
    deriv (fun s : ℝ => (s * Real.log s)⁻¹) t = -(Real.log t + 1) / (t * Real.log t) ^ 2 := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t ≠ 1 := by linarith
  have htm1 : t ≠ -1 := by linarith
  have hfun : (fun s : ℝ => (s * Real.log s)⁻¹) = (fun s : ℝ => s⁻¹) * (fun s : ℝ => (Real.log s)⁻¹) := by
    funext x
    simp [mul_inv, mul_comm]
  have hd1 : DifferentiableAt ℝ (fun s : ℝ => s⁻¹) t := differentiableAt_inv ht0
  have hd2 : DifferentiableAt ℝ (fun s : ℝ => (Real.log s)⁻¹) t :=
    (Real.hasDerivAt_inv_log ht0 ht1 htm1).differentiableAt
  have hlog : Real.log t ≠ 0 := by
    have := Real.log_pos (by linarith : (1 : ℝ) < t)
    linarith
  rw [hfun, deriv_mul hd1 hd2, deriv_inv, Real.deriv_inv_log_apply]
  field_simp
  ring

private theorem hasDerivAt_inv_mul_log {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt (fun s : ℝ => (s * Real.log s)⁻¹) (-(Real.log t + 1) / (t * Real.log t) ^ 2) t := by
  rw [← deriv_inv_mul_log ht]
  exact (differentiableAt_inv_mul_log ht).hasDerivAt

/-! ## 2. Continuity, measurability and integrability -/

private theorem continuousOn_abel_factor_pos (b : ℝ) :
    ContinuousOn ((fun t : ℝ => Real.log t + 1) / fun t : ℝ => (t * Real.log t) ^ 2)
      (Set.Icc 2 b) := by
  have hlog : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc 2 b) := by
    apply ContinuousOn.mono Real.continuousOn_log
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have : (1 : ℝ) < t := by linarith [ht.1]
    positivity
  have hnum : ContinuousOn (fun t : ℝ => Real.log t + 1) (Set.Icc 2 b) :=
    hlog.add continuousOn_const
  have hden : ContinuousOn (fun t : ℝ => (t * Real.log t) ^ 2) (Set.Icc 2 b) :=
    (continuousOn_id.mul hlog).pow 2
  refine hnum.div hden ?_
  intro t ht
  have h1 : t ≠ 0 := by linarith [ht.1]
  have h2 : Real.log t ≠ 0 := by
    have := Real.log_pos (by linarith [ht.1] : (1 : ℝ) < t)
    linarith
  exact pow_ne_zero 2 (mul_ne_zero h1 h2)

private theorem measurable_theta : Measurable Chebyshev.theta := by
  have hfun : Chebyshev.theta = fun x : ℝ => Chebyshev.theta ((⌊x⌋₊ : ℕ) : ℝ) := by
    funext x
    exact Chebyshev.theta_eq_theta_coe_floor x
  rw [hfun]
  exact (measurable_of_countable (fun n : ℕ => Chebyshev.theta ((n : ℕ) : ℝ))).comp
    Nat.measurable_floor

private theorem integrableOn_deriv_inv_mul_log (b : ℝ) :
    IntegrableOn (deriv (fun s : ℝ => (s * Real.log s)⁻¹)) (Set.Icc 2 b) volume := by
  by_cases hb : 2 ≤ b
  · refine IntegrableOn.congr_fun
      (f := -((fun t : ℝ => Real.log t + 1) / fun t : ℝ => (t * Real.log t) ^ 2))
      (continuousOn_abel_factor_pos b).neg.integrableOn_Icc ?_ measurableSet_Icc
    intro t ht
    rw [deriv_inv_mul_log ht.1]
    simp only [Pi.neg_apply, Pi.div_apply]
    ring
  · have hempty : Set.Icc (2 : ℝ) b = ∅ := Set.Icc_eq_empty hb
    rw [hempty]
    exact integrableOn_empty

private theorem continuousOn_abel_factor (b : ℝ) :
    ContinuousOn (fun t : ℝ => (Real.log t + 1) / (t * Real.log t) ^ 2) (Set.Icc 2 b) :=
  continuousOn_abel_factor_pos b

private theorem continuousOn_abel_factor_lin (b : ℝ) :
    ContinuousOn (fun t : ℝ => ((Real.log t + 1) / (t * Real.log t) ^ 2) * (Real.log 4 * t))
      (Set.Icc 2 b) :=
  (continuousOn_abel_factor_pos b).mul (continuousOn_const.mul continuousOn_id)

private theorem continuousOn_abel_factor_neg (b : ℝ) :
    ContinuousOn (fun t : ℝ => -((Real.log t + 1) / (t * Real.log t) ^ 2)) (Set.Icc 2 b) :=
  (continuousOn_abel_factor_pos b).neg

private theorem intervalIntegrable_factor_theta (b : ℝ) (hb : 2 ≤ b) :
    IntervalIntegrable
      (fun t : ℝ => ((Real.log t + 1) / (t * Real.log t) ^ 2) * Chebyshev.theta t) volume 2 b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
  have hmajCont : ContinuousOn
      (fun t : ℝ => Real.log 4 * ((Real.log t + 1) / (t * Real.log t) ^ 2) * t) (Set.Icc 2 b) := by
    have h : ContinuousOn
        ((fun t : ℝ => Real.log t + 1) / fun t : ℝ => (t * Real.log t) ^ 2) (Set.Icc 2 b) :=
      continuousOn_abel_factor_pos b
    refine (continuousOn_const.mul h).mul continuousOn_id
  have hmaj : Integrable (fun t : ℝ => Real.log 4 * ((Real.log t + 1) / (t * Real.log t) ^ 2) * t)
      (volume.restrict (Set.Ioc 2 b)) :=
    hmajCont.integrableOn_Icc.mono_set (Set.Ioc_subset_Icc_self)
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => ((Real.log t + 1) / (t * Real.log t) ^ 2) * Chebyshev.theta t)
      (volume.restrict (Set.Ioc 2 b)) :=
    (((continuousOn_abel_factor b).aestronglyMeasurable measurableSet_Icc).mono_set
      (Set.Ioc_subset_Icc_self)).mul measurable_theta.aestronglyMeasurable
  refine Integrable.mono' hmaj hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hθle : Chebyshev.theta t ≤ Real.log 4 * t :=
    Chebyshev.theta_le_log4_mul_x (by linarith [ht.1])
  have hfac : 0 ≤ (Real.log t + 1) / (t * Real.log t) ^ 2 := by
    apply div_nonneg
    · have : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      linarith
    · positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ((Real.log t + 1) / (t * Real.log t) ^ 2) * Chebyshev.theta t
      ≤ ((Real.log t + 1) / (t * Real.log t) ^ 2) * (Real.log 4 * t) :=
        mul_le_mul_of_nonneg_left hθle hfac
    _ = Real.log 4 * ((Real.log t + 1) / (t * Real.log t) ^ 2) * t := by ring

private theorem intervalIntegrable_factor_lin (b : ℝ) (hb : 2 ≤ b) :
    IntervalIntegrable
      (fun t : ℝ => ((Real.log t + 1) / (t * Real.log t) ^ 2) * (Real.log 4 * t)) volume 2 b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hb]
  exact continuousOn_abel_factor_lin b

/-! ## 3. Abel summation against `θ` -/

private theorem theta_eq_sum_ite (t : ℝ) :
    Chebyshev.theta t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k.Prime then Real.log k else 0) := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]

private theorem abel_primes_theta {b : ℝ} (hb : 2 ≤ b) :
    (∑ p ∈ Finset.Icc 0 ⌊b⌋₊ with p.Prime, (p : ℝ)⁻¹)
      = Chebyshev.theta b / (b * Real.log b) +
        ∫ t in Set.Ioc 2 b,
          ((Real.log t + 1) / (t * Real.log t) ^ 2) * Chebyshev.theta t := by
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) b,
      DifferentiableAt ℝ (fun s : ℝ => (s * Real.log s)⁻¹) t := fun t ht =>
    differentiableAt_inv_mul_log ht.1
  have hint : IntegrableOn (deriv (fun s : ℝ => (s * Real.log s)⁻¹)) (Set.Icc 2 b) volume :=
    integrableOn_deriv_inv_mul_log b
  have h := sum_mul_eq_sub_integral_mul₁ (𝕜 := ℝ)
    (fun n : ℕ => if n.Prime then Real.log n else 0)
    (f := fun s : ℝ => (s * Real.log s)⁻¹) (by simp) (by simp) b hdiff hint
  have hL : (∑ k ∈ Finset.Icc 0 ⌊b⌋₊,
        ((k : ℝ) * Real.log k)⁻¹ * (if k.Prime then Real.log k else 0))
      = ∑ p ∈ Finset.Icc 0 ⌊b⌋₊ with p.Prime, (p : ℝ)⁻¹ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro k _
    by_cases hk : k.Prime
    · rw [if_pos hk, if_pos hk]
      have hk0 : ((k : ℕ) : ℝ) ≠ 0 := by
        have := hk.two_le
        positivity
      have hlog : Real.log (k : ℝ) ≠ 0 := by
        have : 0 < Real.log ((k : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hk.one_lt)
        linarith
      field_simp
    · rw [if_neg hk, if_neg hk, mul_zero]
  rw [hL] at h
  rw [h]
  have hσ : ∀ t : ℝ, (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k.Prime then Real.log k else 0))
      = Chebyshev.theta t := fun t => (theta_eq_sum_ite t).symm
  have hI : (∫ t in Set.Ioc 2 b,
        deriv (fun s : ℝ => (s * Real.log s)⁻¹) t *
          ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k.Prime then Real.log k else 0))
      = -∫ t in Set.Ioc 2 b,
          ((Real.log t + 1) / (t * Real.log t) ^ 2) *
            ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k.Prime then Real.log k else 0) := by
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [deriv_inv_mul_log (by linarith [ht.1] : (2 : ℝ) ≤ t)]
    ring
  have hS : (∫ t in Set.Ioc 2 b,
          ((Real.log t + 1) / (t * Real.log t) ^ 2) *
            ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k.Prime then Real.log k else 0))
      = ∫ t in Set.Ioc 2 b,
          ((Real.log t + 1) / (t * Real.log t) ^ 2) * Chebyshev.theta t := by
    refine integral_congr_ae ?_
    filter_upwards with t
    rw [hσ]
  rw [hσ b, hI, hS, div_eq_inv_mul]
  ring

/-! ## 4. The antiderivative `log log t - 1/log t` -/

private theorem differentiableAt_loglog_sub_invlog {t : ℝ} (ht : 2 ≤ t) :
    DifferentiableAt ℝ (fun s : ℝ => Real.log (Real.log s) - (Real.log s)⁻¹) t := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t ≠ 1 := by linarith
  have htm1 : t ≠ -1 := by linarith
  exact ((Real.hasDerivAt_log_log ht0 ht1 htm1).differentiableAt).sub
    ((Real.hasDerivAt_inv_log ht0 ht1 htm1).differentiableAt)

private theorem deriv_loglog_sub_invlog {t : ℝ} (ht : 2 ≤ t) :
    deriv (fun s : ℝ => Real.log (Real.log s) - (Real.log s)⁻¹) t
      = (Real.log t + 1) / (t * Real.log t ^ 2) := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t ≠ 1 := by linarith
  have htm1 : t ≠ -1 := by linarith
  have hd1 : DifferentiableAt ℝ (fun s : ℝ => Real.log (Real.log s)) t :=
    (Real.hasDerivAt_log_log ht0 ht1 htm1).differentiableAt
  have hd2 : DifferentiableAt ℝ (fun s : ℝ => (Real.log s)⁻¹) t :=
    (Real.hasDerivAt_inv_log ht0 ht1 htm1).differentiableAt
  have hfun : (fun s : ℝ => Real.log (Real.log s) - (Real.log s)⁻¹)
      = (fun s : ℝ => Real.log (Real.log s)) - (fun s : ℝ => (Real.log s)⁻¹) := rfl
  rw [hfun, deriv_sub hd1 hd2, Real.deriv_log_log_apply, Real.deriv_inv_log_apply]
  have hlog : Real.log t ≠ 0 := by
    have := Real.log_pos (by linarith : (1 : ℝ) < t)
    linarith
  field_simp
  ring

private theorem hasDerivAt_loglog_sub_invlog {t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt (fun s : ℝ => Real.log (Real.log s) - (Real.log s)⁻¹)
      ((Real.log t + 1) / (t * Real.log t ^ 2)) t := by
  rw [← deriv_loglog_sub_invlog ht]
  exact (differentiableAt_loglog_sub_invlog ht).hasDerivAt

private theorem continuousOn_loglog_sub_invlog (b : ℝ) :
    ContinuousOn (fun t : ℝ => (Real.log t + 1) / (t * Real.log t ^ 2)) (Set.Icc 2 b) := by
  have hlog : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc 2 b) := by
    apply ContinuousOn.mono Real.continuousOn_log
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have : (1 : ℝ) < t := by linarith [ht.1]
    positivity
  have hnum : ContinuousOn (fun t : ℝ => Real.log t + 1) (Set.Icc 2 b) :=
    hlog.add continuousOn_const
  have hden : ContinuousOn (fun t : ℝ => t * Real.log t ^ 2) (Set.Icc 2 b) :=
    continuousOn_id.mul (hlog.pow 2)
  refine hnum.div hden ?_
  intro t ht
  have h1 : t ≠ 0 := by linarith [ht.1]
  have h2 : Real.log t ≠ 0 := by
    have := Real.log_pos (by linarith [ht.1] : (1 : ℝ) < t)
    linarith
  exact mul_ne_zero h1 (pow_ne_zero 2 h2)

private theorem integral_abel_factor {b : ℝ} (hb : 2 ≤ b) :
    ∫ t in Set.Ioc 2 b, ((Real.log t + 1) / (t * Real.log t ^ 2))
      = (Real.log (Real.log b) - (Real.log b)⁻¹)
        - (Real.log (Real.log 2) - (Real.log 2)⁻¹) := by
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) b,
      HasDerivAt (fun s : ℝ => Real.log (Real.log s) - (Real.log s)⁻¹)
        ((Real.log t + 1) / (t * Real.log t ^ 2)) t := by
    intro t ht
    have h2 : Set.uIcc (2 : ℝ) b = Set.Icc 2 b := Set.uIcc_of_le hb
    rw [h2] at ht
    exact hasDerivAt_loglog_sub_invlog ht.1
  have hcont : ContinuousOn (fun t : ℝ => (Real.log t + 1) / (t * Real.log t ^ 2))
      (Set.uIcc (2 : ℝ) b) := by
    have h2 : Set.uIcc (2 : ℝ) b = Set.Icc 2 b := Set.uIcc_of_le hb
    rw [h2]
    exact continuousOn_loglog_sub_invlog b
  have hint : IntervalIntegrable (fun t : ℝ => (Real.log t + 1) / (t * Real.log t ^ 2))
      volume 2 b := hcont.intervalIntegrable
  rw [← intervalIntegral.integral_of_le hb]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-! ## 5. Numeric bounds on `log` -/

private theorem log_four_le : Real.log 4 ≤ 1.39 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [h]
  linarith [Real.log_two_lt_d9]

private theorem inv_log_two_le : (Real.log 2)⁻¹ ≤ 1.5 := by
  have h2 : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [inv_le_iff_one_le_mul₀ h2]
  linarith [Real.log_two_gt_d9]

private theorem exp_natCast_eq (n : ℕ) : Real.exp ((n : ℕ) : ℝ) = (Real.exp 1) ^ n := by
  rw [show (((n : ℕ) : ℝ)) = (n : ℕ) * 1 by push_cast; ring, Real.exp_nat_mul]

private theorem exp_two : Real.exp 2 = (Real.exp 1) ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, exp_natCast_eq]

private theorem exp_three : Real.exp 3 = (Real.exp 1) ^ 3 := by
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, exp_natCast_eq]

private theorem exp_six : Real.exp 6 = (Real.exp 1) ^ 6 := by
  rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, exp_natCast_eq]

private theorem log_ten_bounds : (2 : ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ 3 := by
  constructor
  · rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 10), exp_two]
    have h5 : (2.7182818286 : ℝ) ^ 2 ≤ 10 := by norm_num
    have h6 : (Real.exp 1) ^ 2 ≤ (2.7182818286 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_d9) 2
    linarith
  · rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 10), exp_three]
    have h5 : (10 : ℝ) < (2.7182818283 : ℝ) ^ 3 := by norm_num
    have h6 : (2.7182818283 : ℝ) ^ 3 ≤ (Real.exp 1) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 3
    linarith

private theorem log_log_two_ge : -1 ≤ Real.log (Real.log 2) := by
  have h2 : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [Real.le_log_iff_exp_le h2]
  have hexp : Real.exp (-1) ≤ 0.4 := by
    rw [Real.exp_neg, ← one_div, show (0.4 : ℝ) = 1 / 2.5 by norm_num]
    exact one_div_le_one_div_of_le (by norm_num)
      (le_trans (by norm_num : (2.5 : ℝ) ≤ 2.7182818283) (le_of_lt Real.exp_one_gt_d9))
  linarith [Real.log_two_gt_d9]

private theorem log_log_le_six {b : ℝ} (hb : 2 ≤ b) (hT : b ≤ (10 : ℝ) ^ 132) :
    Real.log (Real.log b) ≤ 6 := by
  have hb0 : 0 < b := by linarith
  have hlogpos : 0 < Real.log b := Real.log_pos (by linarith)
  have h1 : Real.log b ≤ Real.log ((10 : ℝ) ^ 132) := Real.log_le_log hb0 hT
  have h1' : Real.log ((10 : ℝ) ^ 132) ≤ 396 := by
    rw [Real.log_pow]
    push_cast
    have := log_ten_bounds.2
    linarith
  have h2 : Real.log b ≤ 396 := le_trans h1 h1'
  have h3 : Real.log (Real.log b) ≤ Real.log 396 := Real.log_le_log hlogpos h2
  have h4 : Real.log 396 ≤ 6 := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 396), exp_six]
    have h5 : (396 : ℝ) < (2.718 : ℝ) ^ 6 := by norm_num
    have h6 : (2.718 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 6
    linarith
  linarith

/-! ## 6. The reciprocal prime sum at `10^132` -/

private theorem sum_recip_primes_T :
    (∑ p ∈ Finset.Icc (0 : ℕ) (10 ^ 132) with p.Prime, (p : ℝ)⁻¹) ≤ 12 := by
  set b : ℝ := ((10 ^ 132 : ℕ) : ℝ) with hbdef
  have hb2 : 2 ≤ b := by rw [hbdef]; push_cast; norm_num
  have hbpow : b = (10 : ℝ) ^ 132 := by rw [hbdef]; push_cast; ring
  have hbT : b ≤ (10 : ℝ) ^ 132 := le_of_eq hbpow
  have hfloor : ⌊b⌋₊ = 10 ^ 132 := by rw [hbdef]; exact Nat.floor_natCast _
  have habel := abel_primes_theta hb2
  rw [hfloor] at habel
  rw [habel]
  have hbpos : (0 : ℝ) < b := by linarith
  have hlogb264 : 264 ≤ Real.log b := by
    rw [hbpow, Real.log_pow]
    push_cast
    have := log_ten_bounds.1
    linarith
  have hlogbpos : 0 < Real.log b := by linarith
  have hdenpos : 0 < b * Real.log b := by positivity
  have hterm1 : Chebyshev.theta b / (b * Real.log b) ≤ 1 / 10 := by
    rw [div_le_iff₀ hdenpos]
    refine le_trans (Chebyshev.theta_le_log4_mul_x (le_of_lt hbpos)) ?_
    have h3 : (1.39 : ℝ) ≤ (1 / 10) * Real.log b := by
      have h4 : (1 / 10) * 264 ≤ (1 / 10) * Real.log b :=
        mul_le_mul_of_nonneg_left hlogb264 (by norm_num)
      linarith
    calc Real.log 4 * b ≤ 1.39 * b := mul_le_mul_of_nonneg_right log_four_le (le_of_lt hbpos)
      _ = b * 1.39 := by ring
      _ ≤ b * ((1 / 10) * Real.log b) := mul_le_mul_of_nonneg_left h3 (le_of_lt hbpos)
      _ = (1 / 10) * (b * Real.log b) := by ring
  have hterm2 : ∫ t in Set.Ioc 2 b, ((Real.log t + 1) / (t * Real.log t) ^ 2) * Chebyshev.theta t
      ≤ 119 / 10 := by
    have hstep1 : ∫ t in Set.Ioc 2 b, ((Real.log t + 1) / (t * Real.log t) ^ 2) * Chebyshev.theta t
        ≤ ∫ t in Set.Ioc 2 b,
            ((Real.log t + 1) / (t * Real.log t) ^ 2) * (Real.log 4 * t) := by
      rw [← intervalIntegral.integral_of_le hb2, ← intervalIntegral.integral_of_le hb2]
      refine intervalIntegral.integral_mono_on hb2 (intervalIntegrable_factor_theta b hb2)
        (intervalIntegrable_factor_lin b hb2) ?_
      intro x hx
      have hfac : 0 ≤ (Real.log x + 1) / (x * Real.log x) ^ 2 := by
        apply div_nonneg
        · have : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
          linarith
        · positivity
      exact mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (by linarith [hx.1])) hfac
    have hstep2 : ∫ t in Set.Ioc 2 b,
          ((Real.log t + 1) / (t * Real.log t) ^ 2) * (Real.log 4 * t)
        = Real.log 4 * ((Real.log (Real.log b) - (Real.log b)⁻¹)
            - (Real.log (Real.log 2) - (Real.log 2)⁻¹)) := by
      have hmain := integral_abel_factor hb2
      rw [← hmain, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : (0 : ℝ) < t := by linarith [ht.1]
      have hlog : Real.log t ≠ 0 := by
        have h := Real.log_pos (by linarith [ht.1] : (1 : ℝ) < t)
        linarith
      field_simp
      try ring
    have hnum : Real.log 4 * ((Real.log (Real.log b) - (Real.log b)⁻¹)
            - (Real.log (Real.log 2) - (Real.log 2)⁻¹)) ≤ 119 / 10 := by
      have hFb : Real.log (Real.log b) - (Real.log b)⁻¹ ≤ 6 := by
        have h6 := log_log_le_six hb2 hbT
        have hinv : (0 : ℝ) < (Real.log b)⁻¹ := inv_pos.mpr hlogbpos
        refine sub_le_iff_le_add.mpr (le_trans h6 ?_)
        exact le_add_of_nonneg_right (le_of_lt hinv)
      have hF2 : -2.5 ≤ Real.log (Real.log 2) - (Real.log 2)⁻¹ := by
        have h1 : (-1 : ℝ) ≤ Real.log (Real.log 2) := log_log_two_ge
        have h2 : (Real.log 2)⁻¹ ≤ 1.5 := inv_log_two_le
        have h3 : (-1 : ℝ) - 1.5 ≤ Real.log (Real.log 2) - (Real.log 2)⁻¹ := sub_le_sub h1 h2
        norm_num at h3
        linarith only [h3]
      have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      have hA : Real.log 4 * (Real.log (Real.log b) - (Real.log b)⁻¹)
          ≤ Real.log 4 * 6 := mul_le_mul_of_nonneg_left hFb h4
      have hB : Real.log 4 * (-2.5) ≤ Real.log 4 * (Real.log (Real.log 2) - (Real.log 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hF2 h4
      have hC : Real.log 4 * 6 + Real.log 4 * 2.5 ≤ 119 / 10 := by
        have h7 : Real.log 4 * 6 + Real.log 4 * 2.5 = Real.log 4 * 8.5 := by ring
        rw [h7]
        nlinarith [log_four_le, h4]
      linarith
    linarith [hstep1, hstep2, hnum]
  linarith

private theorem sum_recip_primes_le {M : ℕ} (hM : M ≤ 10 ^ 132) :
    (∑ p ∈ Finset.Ico 1 (M + 1) with p.Prime, (p : ℝ)⁻¹) ≤ 12 := by
  refine le_trans ?_ sum_recip_primes_T
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc] at hp ⊢
    have hpM : p ≤ M := by omega
    exact ⟨⟨by omega, le_trans hpM hM⟩, hp.2⟩
  · intro p _ _
    positivity

/-! ## 7. The summatory estimate `Σ_{n ≤ M} Ω n ≤ 16 M` -/

private theorem bigOmega_eq_sum_factorization {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    bigOmega n = ∑ p ∈ (Finset.Ico 1 (N + 1)).filter Nat.Prime, n.factorization p := by
  have h1 : bigOmega n = ∑ p ∈ n.factorization.support, n.factorization p := by
    rw [bigOmega_eq_cardFactors, ArithmeticFunction.cardFactors_eq_sum_factorization]
    rfl
  rw [h1]
  refine Finset.sum_subset (s₁ := n.factorization.support)
    (s₂ := (Finset.Ico 1 (N + 1)).filter Nat.Prime) ?_ ?_
  · intro p hp
    have hpv : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hpprime : p.Prime := by
      by_contra h
      exact hpv (Nat.factorization_eq_zero_of_not_prime n h)
    have hpdvd : p ∣ n := Nat.dvd_of_factorization_pos hpv
    refine Finset.mem_filter.mpr ⟨?_, hpprime⟩
    rw [Finset.mem_Ico]
    refine ⟨hpprime.one_le, ?_⟩
    have hle : p ≤ n := Nat.le_of_dvd (by omega) hpdvd
    omega
  · intro p _ hpnot
    exact Finsupp.notMem_support_iff.mp hpnot

private theorem factorization_eq_card_pow_dvd' {M n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hnM : n ≤ M) :
    n.factorization p = ((Finset.Ico 1 (M + 1)).filter (fun i => p ^ i ∣ n)).card := by
  refine Nat.factorization_eq_card_pow_dvd_of_lt hp (by omega) ?_
  have h0 : M < 2 ^ M := Nat.lt_two_pow_self
  have h1 : n < 2 ^ (M + 1) := by
    have h3 : 2 ^ M ≤ 2 ^ (M + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ M)
    omega
  have h2 : (2 : ℕ) ^ (M + 1) ≤ p ^ (M + 1) := Nat.pow_le_pow_left hp.two_le _
  omega

private theorem geom_half (N : ℕ) :
    ∑ j ∈ Finset.range N, ((1 : ℝ) / 2) ^ j = 2 - 2 * ((1 : ℝ) / 2) ^ N := by
  induction N with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

private theorem geom_prime_le {M p : ℕ} (hp : p.Prime) :
    ∑ i ∈ Finset.Ico 1 (M + 1), ((M : ℝ) / (p : ℝ) ^ i)
      ≤ (M : ℝ) / p + 2 * ((M : ℝ) / (p : ℝ) ^ 2) := by
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · subst hM0
    simp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hsplit : Finset.Ico 1 (M + 1) = insert 1 (Finset.Ico 2 (M + 1)) := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_or_ge 1 n with h | h
      · exact Or.inr ⟨h, h2⟩
      · exact Or.inl (by omega)
    · rintro (rfl | ⟨h1, h2⟩)
      · omega
      · omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have hfirst : (M : ℝ) / (p : ℝ) ^ 1 = (M : ℝ) / p := by norm_num
  rw [hfirst]
  have hrest : ∑ i ∈ Finset.Ico 2 (M + 1), ((M : ℝ) / (p : ℝ) ^ i)
      ≤ 2 * ((M : ℝ) / (p : ℝ) ^ 2) := by
    have hterm : ∀ i ∈ Finset.Ico 2 (M + 1),
        ((M : ℝ) / (p : ℝ) ^ i)
          ≤ ((M : ℝ) / (p : ℝ) ^ 2) * ((1 : ℝ) / 2) ^ (i - 2) := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hpi : (p : ℝ) ^ i = (p : ℝ) ^ 2 * (p : ℝ) ^ (i - 2) := by
        rw [← pow_add, show 2 + (i - 2) = i by omega]
      have hbase : (1 : ℝ) / (p : ℝ) ^ (i - 2) ≤ (1 : ℝ) / 2 ^ (i - 2) := by
        apply one_div_le_one_div_of_le (by positivity)
        exact pow_le_pow_left₀ (by norm_num) hp2 _
      calc ((M : ℝ) / (p : ℝ) ^ i)
          = ((M : ℝ) / (p : ℝ) ^ 2) * (1 / (p : ℝ) ^ (i - 2)) := by
            rw [hpi]
            field_simp
        _ ≤ ((M : ℝ) / (p : ℝ) ^ 2) * (1 / (2 : ℝ) ^ (i - 2)) := by
            apply mul_le_mul_of_nonneg_left hbase (by positivity)
        _ = ((M : ℝ) / (p : ℝ) ^ 2) * ((1 : ℝ) / 2) ^ (i - 2) := by rw [one_div_pow]
    calc ∑ i ∈ Finset.Ico 2 (M + 1), ((M : ℝ) / (p : ℝ) ^ i)
        ≤ ∑ i ∈ Finset.Ico 2 (M + 1),
            ((M : ℝ) / (p : ℝ) ^ 2) * ((1 : ℝ) / 2) ^ (i - 2) := Finset.sum_le_sum hterm
      _ = ((M : ℝ) / (p : ℝ) ^ 2) *
            ∑ i ∈ Finset.Ico 2 (M + 1), ((1 : ℝ) / 2) ^ (i - 2) := by
          rw [Finset.mul_sum]
      _ ≤ ((M : ℝ) / (p : ℝ) ^ 2) * 2 := by
          apply mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [Finset.sum_Ico_eq_sum_range]
          have hg : ∀ k ∈ Finset.range (M + 1 - 2), ((1 : ℝ) / 2) ^ (2 + k - 2)
              = ((1 : ℝ) / 2) ^ k := by
            intro k _
            rw [show 2 + k - 2 = k by omega]
          rw [Finset.sum_congr rfl hg, geom_half]
          have hpos : (0 : ℝ) ≤ 2 * ((1 : ℝ) / 2) ^ (M + 1 - 2) := by positivity
          linarith
      _ = 2 * ((M : ℝ) / (p : ℝ) ^ 2) := by ring
  linarith

private theorem sum_inv_mul_pred : ∀ M : ℕ, 0 < M →
    ∑ n ∈ Finset.Ico 2 (M + 1), (1 / ((n : ℝ) * ((n : ℝ) - 1))) = 1 - 1 / (M : ℝ) := by
  intro M
  induction M with
  | zero => intro h; omega
  | succ k ih =>
    intro _
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have hstep : Finset.Ico 2 (k + 1 + 1) = insert (k + 1) (Finset.Ico 2 (k + 1)) := by
        ext n
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      rw [hstep, Finset.sum_insert (by simp only [Finset.mem_Ico]; omega), ih hk]
      push_cast
      have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkR
      have hk1 : (k : ℝ) + 1 - 1 = (k : ℝ) := by ring
      rw [hk1]
      field_simp
      ring

private theorem sum_bigOmega_eq (M : ℕ) :
    ∑ n ∈ Finset.Ico 1 (M + 1), bigOmega n
      = ∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime,
          ∑ i ∈ Finset.Ico 1 (M + 1), M / p ^ i := by
  classical
  have hstep : ∀ n ∈ Finset.Ico 1 (M + 1),
      bigOmega n = ∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime, n.factorization p := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    exact bigOmega_eq_sum_factorization (by omega) (by omega)
  calc ∑ n ∈ Finset.Ico 1 (M + 1), bigOmega n
      = ∑ n ∈ Finset.Ico 1 (M + 1),
          ∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime, n.factorization p :=
        Finset.sum_congr rfl hstep
    _ = ∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime,
          ∑ n ∈ Finset.Ico 1 (M + 1), n.factorization p := Finset.sum_comm
    _ = ∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime,
          ∑ i ∈ Finset.Ico 1 (M + 1), M / p ^ i := by
        refine Finset.sum_congr rfl ?_
        intro p hp
        have hpP : p.Prime := (Finset.mem_filter.mp hp).2
        have hinner : ∀ n ∈ Finset.Ico 1 (M + 1),
            n.factorization p = ((Finset.Ico 1 (M + 1)).filter (fun i => p ^ i ∣ n)).card := by
          intro n hn
          rw [Finset.mem_Ico] at hn
          exact factorization_eq_card_pow_dvd' hpP (by omega) (by omega)
        calc ∑ n ∈ Finset.Ico 1 (M + 1), n.factorization p
            = ∑ n ∈ Finset.Ico 1 (M + 1),
                ((Finset.Ico 1 (M + 1)).filter (fun i => p ^ i ∣ n)).card :=
              Finset.sum_congr rfl hinner
          _ = ∑ n ∈ Finset.Ico 1 (M + 1),
                ∑ i ∈ Finset.Ico 1 (M + 1), if p ^ i ∣ n then 1 else 0 := by
              refine Finset.sum_congr rfl ?_
              intro n _
              rw [Finset.card_filter]
          _ = ∑ i ∈ Finset.Ico 1 (M + 1),
                ∑ n ∈ Finset.Ico 1 (M + 1), if p ^ i ∣ n then 1 else 0 := Finset.sum_comm
          _ = ∑ i ∈ Finset.Ico 1 (M + 1), M / p ^ i := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [← Finset.card_filter]
              have hIco : Finset.Ico 1 (M + 1) = Finset.Ioc 0 M := by
                ext x
                simp only [Finset.mem_Ico, Finset.mem_Ioc]
                omega
              rw [hIco]
              exact Nat.Ioc_filter_dvd_card_eq_div M (p ^ i)

private theorem sum_bigOmega_le {M : ℕ} (hM : M ≤ 10 ^ 132) :
    ∑ n ∈ Finset.Ico 1 (M + 1), bigOmega n ≤ 16 * M := by
  have hS := sum_recip_primes_le hM
  have hsq : ∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime, ((p : ℝ) ^ 2)⁻¹ ≤ 1 := by
    have h1 : ∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime, ((p : ℝ) ^ 2)⁻¹
        ≤ ∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      refine Finset.sum_le_sum ?_
      intro p hp
      have hpP : p.Prime := (Finset.mem_filter.mp hp).2
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpP.two_le
      have hpos : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
      have hle : (p : ℝ) * ((p : ℝ) - 1) ≤ (p : ℝ) ^ 2 := by nlinarith
      simpa only [one_div] using one_div_le_one_div_of_le hpos hle
    have h2 : ∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime, 1 / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ n ∈ Finset.Ico 2 (M + 1), 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ico] at hp ⊢
        have := hp.2.two_le
        omega
      · intro n hn _
        have hn2 : (2 : ℕ) ≤ n := (Finset.mem_Ico.mp hn).1
        have h1 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
        have hpos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
        positivity
    have h3 : ∑ n ∈ Finset.Ico 2 (M + 1), 1 / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 := by
      rcases Nat.eq_zero_or_pos M with hM0 | hMpos
      · subst hM0
        simp
      · rw [sum_inv_mul_pred M hMpos]
        have hMpos' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMpos
        have hpos : (0 : ℝ) < 1 / (M : ℝ) := by positivity
        linarith
    linarith
  have hreal : (∑ n ∈ Finset.Ico 1 (M + 1), (bigOmega n : ℝ)) ≤ 16 * M := by
    have hEq : (∑ n ∈ Finset.Ico 1 (M + 1), (bigOmega n : ℝ))
        = ∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime,
            ∑ i ∈ Finset.Ico 1 (M + 1), ((M / p ^ i : ℕ) : ℝ) := by
      rw [← Nat.cast_sum, sum_bigOmega_eq]
      push_cast
      rfl
    rw [hEq]
    have h1 : ∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime,
          ∑ i ∈ Finset.Ico 1 (M + 1), ((M / p ^ i : ℕ) : ℝ)
        ≤ ∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime,
            ((M : ℝ) / p + 2 * ((M : ℝ) / (p : ℝ) ^ 2)) := by
      refine Finset.sum_le_sum ?_
      intro p hp
      refine le_trans (Finset.sum_le_sum ?_) (geom_prime_le (Finset.mem_filter.mp hp).2)
      intro i _
      have hcd : ((M / p ^ i : ℕ) : ℝ) ≤ (M : ℝ) / ((p ^ i : ℕ) : ℝ) := Nat.cast_div_le
      rw [Nat.cast_pow] at hcd
      exact hcd
    have h2 : ∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime,
            ((M : ℝ) / p + 2 * ((M : ℝ) / (p : ℝ) ^ 2))
        = (M : ℝ) * (∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime, (p : ℝ)⁻¹)
          + 2 * (M : ℝ) *
              (∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime, ((p : ℝ) ^ 2)⁻¹) := by
      have hterm : ∀ p : ℕ, ((M : ℝ) / p + 2 * ((M : ℝ) / (p : ℝ) ^ 2))
          = (M : ℝ) * (p : ℝ)⁻¹ + 2 * (M : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by
        intro p
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      rw [Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
    have h0 : (0 : ℝ) ≤ (M : ℝ) := by positivity
    have hA : (M : ℝ) * (∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime, (p : ℝ)⁻¹)
        ≤ (M : ℝ) * 12 := mul_le_mul_of_nonneg_left hS h0
    have hB : 2 * (M : ℝ) *
          (∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime, ((p : ℝ) ^ 2)⁻¹)
        ≤ 2 * (M : ℝ) * 1 := by
      have h2M : (0 : ℝ) ≤ 2 * (M : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hsq h2M
    calc ∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime,
          ∑ i ∈ Finset.Ico 1 (M + 1), ((M / p ^ i : ℕ) : ℝ)
        ≤ ∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime,
            ((M : ℝ) / p + 2 * ((M : ℝ) / (p : ℝ) ^ 2)) := h1
      _ = (M : ℝ) * (∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime, (p : ℝ)⁻¹)
          + 2 * (M : ℝ) *
              (∑ p ∈ (Finset.Ico 1 (M + 1)).filter Nat.Prime, ((p : ℝ) ^ 2)⁻¹) := h2
      _ ≤ (M : ℝ) * 12 + 2 * (M : ℝ) * 1 := by linarith [hA, hB]
      _ = 14 * M := by ring
      _ ≤ 16 * M := by nlinarith
  exact_mod_cast hreal

/-! ## 8. The averaging argument and the two leaves -/

private theorem bigOmega_mul_pos {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    bigOmega (a * b) = bigOmega a + bigOmega b := by
  simp only [bigOmega_eq_cardFactors]
  exact ArithmeticFunction.cardFactors_mul ha hb

private theorem sum_sub_reflect (N : ℕ) (f : ℕ → ℕ) :
    ∑ a ∈ Finset.Ico 1 N, f (N - a) = ∑ a ∈ Finset.Ico 1 N, f a := by
  have hperm : (Finset.Ico 1 N).image (fun a => N - a) = Finset.Ico 1 N := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      simp only [Finset.mem_Ico] at ha ⊢
      omega
    · intro hx
      simp only [Finset.mem_Ico] at hx
      refine Finset.mem_image.mpr ⟨N - x, ?_, by omega⟩
      simp only [Finset.mem_Ico]
      omega
  have hinj : Set.InjOn (fun a : ℕ => N - a) ↑(Finset.Ico 1 N) := by
    intro x hx y hy h
    simp only [Finset.mem_coe, Finset.mem_Ico] at hx hy
    have h' : N - x = N - y := h
    omega
  have h := Finset.sum_image (s := Finset.Ico 1 N) (g := fun a => N - a) (f := f) hinj
  rw [hperm] at h
  exact h.symm

private theorem exists_split_of_sum_le (N : ℕ) (h2 : 2 ≤ N)
    (h : 2 * ∑ a ∈ Finset.Ico 1 N, bigOmega a ≤ 33 * (N - 1)) :
    ∃ a ∈ Finset.Ico 1 N, bigOmega (a * (N - a)) ≤ 33 := by
  have hcard : (Finset.Ico 1 N).card = N - 1 := by rw [Nat.card_Ico]
  have hnon : (Finset.Ico 1 N).Nonempty := ⟨1, by simp only [Finset.mem_Ico]; omega⟩
  have hrefl : ∑ a ∈ Finset.Ico 1 N, bigOmega (N - a) = ∑ a ∈ Finset.Ico 1 N, bigOmega a :=
    sum_sub_reflect N bigOmega
  have hsum : ∑ a ∈ Finset.Ico 1 N, (bigOmega a + bigOmega (N - a))
      = 2 * ∑ a ∈ Finset.Ico 1 N, bigOmega a := by
    rw [Finset.sum_add_distrib, hrefl, two_mul]
  have hle : ∑ a ∈ Finset.Ico 1 N, (bigOmega a + bigOmega (N - a))
      ≤ ∑ _a ∈ Finset.Ico 1 N, (33 : ℕ) := by
    rw [hsum]
    have h33 : ∑ _a ∈ Finset.Ico 1 N, (33 : ℕ) = 33 * (N - 1) := by
      rw [Finset.sum_const, hcard, smul_eq_mul, Nat.mul_comm]
    rw [h33]
    exact h
  obtain ⟨a, ha, hfin⟩ := exists_le_of_sum_le hnon hle
  refine ⟨a, ha, ?_⟩
  rw [Finset.mem_Ico] at ha
  rw [bigOmega_mul_pos (by omega : a ≠ 0) (by omega : N - a ≠ 0)]
  exact hfin

private theorem twoAlmostPrimes_of_sum (N : ℕ) (h2 : 2 ≤ N)
    (h : 2 * ∑ a ∈ Finset.Ico 1 N, bigOmega a ≤ 33 * (N - 1)) : TwoAlmostPrimes 33 N := by
  obtain ⟨a, ha, hfin⟩ := exists_split_of_sum_le N h2 h
  rw [Finset.mem_Ico] at ha
  exact ⟨a, N - a, by omega, by omega, by omega, hfin⟩

private theorem twoAlmostPrimes_of_sum_bound (N : ℕ) (h2 : 2 ≤ N) (hN : N ≤ 10 ^ 132) :
    TwoAlmostPrimes 33 N := by
  refine twoAlmostPrimes_of_sum N h2 ?_
  have hM := sum_bigOmega_le (M := N - 1) (by omega)
  rw [show N - 1 + 1 = N by omega] at hM
  have h1 : 2 * ∑ a ∈ Finset.Ico 1 N, bigOmega a ≤ 2 * (16 * (N - 1)) :=
    Nat.mul_le_mul_left 2 hM
  have h2' : 2 * (16 * (N - 1)) ≤ 33 * (N - 1) := by
    rw [show 2 * (16 * (N - 1)) = 32 * (N - 1) by ring]
    exact Nat.mul_le_mul_right _ (by norm_num)
  exact le_trans h1 h2'

private theorem leaf_small_range_proof : ∀ N : ℕ, 2 ≤ N → N ≤ 117465180365547648498934439 →
    TwoAlmostPrimes 33 N := by
  intro N h2 hN
  exact twoAlmostPrimes_of_sum_bound N h2 (le_trans hN (by norm_num))

private theorem leaf_middle_range_proof : ∀ N : ℕ, 117465180365547648498934439 < N → N < 10 ^ 132 →
    TwoAlmostPrimes 33 N := by
  intro N _ hN
  exact twoAlmostPrimes_of_sum_bound N (by omega) (le_of_lt hN)

end CampbellHelpers

/-- LEAF 1, the lower range: every `2 ≤ N ≤ N₀` is a sum of two positive integers whose
product has at most 33 prime factors with multiplicity. This is the short-interval step with
the gap table input, applied below `N₀`. -/
theorem leaf_small_range : ∀ N : ℕ, 2 ≤ N → N ≤ 117465180365547648498934439 →
    TwoAlmostPrimes 33 N := by
  exact leaf_small_range_proof

/-- LEAF 2, the middle range: every `N₀ < N < 10^132` is a sum of two positive integers whose
product has at most 33 prime factors with multiplicity. This is the finite verification of a
positive sieve sum on the middle range, converted into the sum of two almost primes. -/
theorem leaf_middle_range : ∀ N : ℕ, 117465180365547648498934439 < N → N < 10 ^ 132 →
    TwoAlmostPrimes 33 N := by
  exact leaf_middle_range_proof

/-- LEAF 3, the upper range, sieve output: for every `N ≥ 10^132` there are positive `a, b` with
`N = a + b` and every prime factor of `a` and of `b` strictly larger than `N^(2/33)`. This is
what the explicit sieve produces at `z = N^(2/33)`; it does not itself mention `TwoAlmostPrimes`. -/
theorem leaf_large_sieve_output : ∀ N : ℕ, 10 ^ 132 ≤ N → ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
    N = a + b ∧ (∀ p : ℕ, p.Prime → p ∣ a → (N : ℝ) ^ ((2 : ℝ) / 33) < (p : ℝ)) ∧
      (∀ p : ℕ, p.Prime → p ∣ b → (N : ℝ) ^ ((2 : ℝ) / 33) < (p : ℝ)) := by
  sorry

/-! ### Private helpers for LEAF 4

If every entry of a list of naturals is at least a real constant `C ≥ 0`, the
`length`-th power of `C` is at most the product of the list; if the entries are
strictly larger and the list is nonempty, the inequality is strict. -/
private theorem list_prod_rpow_le {C : ℝ} (hC : 0 ≤ C) (L : List ℕ)
    (h : ∀ x ∈ L, C ≤ (x : ℝ)) : C ^ L.length ≤ ((L.prod : ℕ) : ℝ) := by
  induction L with
  | nil => simp
  | cons x t ih =>
    have hx : C ≤ (x : ℝ) := h x (by simp)
    have ht : ∀ y ∈ t, C ≤ (y : ℝ) := fun y hy => h y (by simp [hy])
    have ih' := ih ht
    have hxp : (0 : ℝ) ≤ (x : ℝ) := le_trans hC hx
    calc C ^ (x :: t).length = C ^ t.length * C := by simp [pow_succ]
      _ = C * C ^ t.length := by ring
      _ ≤ (x : ℝ) * ((t.prod : ℕ) : ℝ) := mul_le_mul hx ih' (pow_nonneg hC _) hxp
      _ = (((x :: t).prod : ℕ) : ℝ) := by simp [List.prod_cons, Nat.cast_mul]

private theorem list_prod_rpow_lt {C : ℝ} (hC : 0 < C) (L : List ℕ) (hne : L ≠ [])
    (h : ∀ x ∈ L, C < (x : ℝ)) : C ^ L.length < ((L.prod : ℕ) : ℝ) := by
  rcases L with - | ⟨x, t⟩
  · exact absurd rfl hne
  cases t with
  | nil =>
    have hx : C < (x : ℝ) := h x (by simp)
    simpa using hx
  | cons y t' =>
    have hx : C < (x : ℝ) := h x (by simp)
    have hle : C ^ (y :: t').length ≤ (((y :: t').prod : ℕ) : ℝ) :=
      list_prod_rpow_le (le_of_lt hC) (y :: t') fun z hz => le_of_lt (h z (by simp [hz]))
    have hpos : (0 : ℝ) < (x : ℝ) := lt_trans hC hx
    calc C ^ (x :: y :: t').length = C * C ^ (y :: t').length := by
          simp [pow_succ]; ring
      _ < (x : ℝ) * C ^ (y :: t').length := mul_lt_mul_of_pos_right hx (pow_pos hC _)
      _ ≤ (x : ℝ) * (((y :: t').prod : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hle (le_of_lt hpos)
      _ = (((x :: y :: t').prod : ℕ) : ℝ) := by simp [List.prod_cons, Nat.cast_mul]

/-- LEAF 4, the counting step: a positive `a ≤ N` all of whose prime factors exceed `N^(2/33)`
has at most 16 prime factors with multiplicity, since `a` is then larger than `N^(2/33)` to the
power `Ω a` while `a ≤ N = (N^(2/33))^(33/2)` and `33/2 = 16.5`. -/
theorem leaf_omega_bound_of_large_prime_factors : ∀ (N a : ℕ), 10 ^ 132 ≤ N → 0 < a → a ≤ N →
    (∀ p : ℕ, p.Prime → p ∣ a → (N : ℝ) ^ ((2 : ℝ) / 33) < (p : ℝ)) → bigOmega a ≤ 16 := by
  intro N a hN ha hale hfac
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  set C : ℝ := (N : ℝ) ^ ((2 : ℝ) / 33) with hCdef
  have hCpos : (0 : ℝ) < C := by
    rw [hCdef]; exact Real.rpow_pos_of_pos hNpos _
  have hC1 : (1 : ℝ) < C := by
    have h0 : (N : ℝ) ^ (0 : ℝ) < (N : ℝ) ^ ((2 : ℝ) / 33) :=
      Real.rpow_lt_rpow_of_exponent_lt hN1 (by norm_num)
    simpa [hCdef] using h0
  by_contra hcon
  have h17 : 17 ≤ bigOmega a := by omega
  have hane : a ≠ 0 := by omega
  have hLne : a.primeFactorsList ≠ [] := by
    intro hnil
    have h0 : bigOmega a = 0 := by simp [bigOmega, hnil]
    omega
  have hbound : ∀ x ∈ a.primeFactorsList, C < (x : ℝ) := fun x hx =>
    hfac x (Nat.prime_of_mem_primeFactorsList hx) (Nat.dvd_of_mem_primeFactorsList hx)
  have hstrict : C ^ a.primeFactorsList.length < ((a.primeFactorsList.prod : ℕ) : ℝ) :=
    list_prod_rpow_lt hCpos _ hLne hbound
  rw [Nat.prod_primeFactorsList hane] at hstrict
  have hlen : a.primeFactorsList.length = bigOmega a := rfl
  rw [hlen] at hstrict
  have hpow : C ^ 17 ≤ C ^ bigOmega a := pow_le_pow_right₀ (le_of_lt hC1) h17
  have hlt_a : C ^ 17 < (a : ℝ) := lt_of_le_of_lt hpow hstrict
  have hrpow : C ^ 17 = (N : ℝ) ^ ((34 : ℝ) / 33) := by
    rw [hCdef, ← Real.rpow_natCast ((N : ℝ) ^ ((2 : ℝ) / 33)) 17,
      ← Real.rpow_mul (le_of_lt hNpos)]
    congr 1
    norm_num
  have hltN : (N : ℝ) < (N : ℝ) ^ ((34 : ℝ) / 33) := by
    have h := Real.rpow_lt_rpow_of_exponent_lt hN1 (by norm_num : (1 : ℝ) < (34 : ℝ) / 33)
    simpa using h
  have hale' : (a : ℝ) ≤ (N : ℝ) := by exact_mod_cast hale
  have hbig : (N : ℝ) < (a : ℝ) := by
    calc (N : ℝ) < (N : ℝ) ^ ((34 : ℝ) / 33) := hltN
      _ = C ^ 17 := hrpow.symm
      _ < (a : ℝ) := hlt_a
  linarith

/-- Private helper with a full proof: `Ω` is additive on a product of positive integers. -/
private theorem bigOmega_mul_add {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    bigOmega (a * b) = bigOmega a + bigOmega b := by
  simp only [bigOmega_eq_cardFactors]
  exact ArithmeticFunction.cardFactors_mul ha hb

/-- The target statement, assembled from the four leaves. -/
theorem campbell_split : ∀ N : ℕ, 2 ≤ N → TwoAlmostPrimes 33 N := by
  intro N h2
  rcases Nat.lt_or_ge 117465180365547648498934439 N with hmid | hlow
  · rcases Nat.lt_or_ge N (10 ^ 132) with hlt | hge
    · exact leaf_middle_range N hmid hlt
    · obtain ⟨a, b, ha, hb, hN, hpa, hpb⟩ := leaf_large_sieve_output N hge
      have hale : a ≤ N := by omega
      have hble : b ≤ N := by omega
      have hoa : bigOmega a ≤ 16 := leaf_omega_bound_of_large_prime_factors N a hge ha hale hpa
      have hob : bigOmega b ≤ 16 := leaf_omega_bound_of_large_prime_factors N b hge hb hble hpb
      refine ⟨a, b, ha, hb, hN, ?_⟩
      rw [bigOmega_mul_add ha.ne' hb.ne']
      omega
  · exact leaf_small_range N h2 hlow

#print axioms campbell_split

end LeanLab.AlmostPrimes
