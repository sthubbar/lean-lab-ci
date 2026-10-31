import Mathlib

/-!
Elementary probability bounds in P0098 pages 165 and 166, eqs. 3.2 and 3.3.
The product is the zero success probability for independent Bernoulli trials.
This file proves the numerical bounds and does not construct the prime probability space.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Sampling124
open Finset Real MeasureTheory

/-- P0098 page 165, the independent Bernoulli zero success bound.
The product of one minus each success probability is at most the exponential of minus its sum. -/
theorem zero_success_product {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i ∧ p i ≤ 1) :
    ∏ i ∈ s, (1 - p i) ≤ Real.exp (-(∑ i ∈ s, p i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hpa := hp a (mem_insert_self a s)
    have hps := fun i hi => hp i (mem_insert_of_mem hi)
    rw [prod_insert ha, sum_insert ha, neg_add, Real.exp_add]
    exact mul_le_mul (by linarith [Real.add_one_le_exp (-p a)]) (ih hps)
      (prod_nonneg fun i hi => sub_nonneg.mpr (hps i hi).2) (Real.exp_pos _).le

/-- P0098 page 166 eq. 3.3, the exponent beats three halves.
The source lower bound for the mean is four log n plus a bounded error. -/
theorem failure_exponent_margin : (3 : ℝ) / 2 < 4 * (Real.log 4 - 1) := by
  have h2 := Real.log_two_gt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h4]
  linarith

/-- P0098 page 166 eq. 3.3, the explicit exponential tail is at most n to minus three halves. -/
theorem failure_power_bound {n : ℝ} (hn : 1 ≤ n) :
    Real.exp (-(4 * Real.log n) * (Real.log 4 - 1)) ≤ n ^ (-(3 : ℝ) / 2) := by
  have hn0 : 0 < n := by linarith
  rw [Real.rpow_def_of_pos hn0]
  apply Real.exp_le_exp.mpr
  have hl : 0 ≤ Real.log n := Real.log_nonneg hn
  have hm := mul_le_mul_of_nonneg_right failure_exponent_margin.le hl
  nlinarith

/-- P0098 page 166 after eq. 3.3, the error probabilities admit a summable majorant. -/
theorem summable_failure_majorant : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 : ℝ) / 2)) := by
  exact Real.summable_nat_rpow.mpr (by norm_num)

/-- P0098 page 166 after eq. 3.3, a probability bound by the summable power tail
makes the total failure mass finite. The shift by one avoids the initial index zero. -/
theorem failure_mass_finite {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (A : ℕ → Set Ω) (K : ℝ)
    (hb : ∀ n : ℕ, μ (A n) ≤ ENNReal.ofReal (K * ((n : ℝ) + 1) ^ (-(3 : ℝ) / 2))) :
    (∑' n : ℕ, μ (A n)) ≠ ⊤ := by
  have hs : Summable (fun n : ℕ => K * ((n : ℝ) + 1) ^ (-(3 : ℝ) / 2)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).mpr summable_failure_majorant).mul_left K
  exact ne_of_lt ((ENNReal.tsum_le_tsum hb).trans_lt hs.tsum_ofReal_lt_top)

/-- P0098 page 165, the variance identity for a zero or one valued random variable. -/
theorem bernoulli_variance_eq_mean_sub_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MeasureTheory.MemLp X 2 μ)
    (h01 : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    ProbabilityTheory.variance X μ =
      (∫ ω, X ω ∂μ) - (∫ ω, X ω ∂μ) ^ 2 := by
  have heq : X ^ 2 =ᵐ[μ] X := by
    filter_upwards [h01] with ω hω
    change X ω ^ 2 = X ω
    rcases hω with hω | hω <;> simp [hω]
  rw [ProbabilityTheory.variance_eq_sub hX, MeasureTheory.integral_congr_ae heq]

/-- P0098 page 165, a Bernoulli variable has variance at most its expectation. -/
theorem bernoulli_variance_le_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MeasureTheory.MemLp X 2 μ)
    (h01 : ∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) :
    ProbabilityTheory.variance X μ ≤ ∫ ω, X ω ∂μ := by
  rw [bernoulli_variance_eq_mean_sub_sq μ X hX h01]
  exact sub_le_self _ (sq_nonneg _)

end LeanLab.GoldbachAverage.Sampling124
