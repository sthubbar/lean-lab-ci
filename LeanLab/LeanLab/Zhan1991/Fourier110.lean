import LeanLab.Zhan1991.Decomp110

/-! Elementary leaves for page 270. AI wrote the Lean code. Goldbach is open. -/

namespace LeanLab.Zhan1991
noncomputable section
open MeasureTheory

 /-- LEAF. The phase e of x has complex norm 1. Page 270, the phase in 3.20 and 3.21. -/
theorem ee_norm110 (x : ℝ) : ‖ee x‖ = 1 := by
  simp [ee, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

 /-- LEAF. The phase of x plus y equals the product of the phases. Page 270, expansion in 3.21. -/
theorem ee_add110 (x y : ℝ) : ee (x + y) = ee x * ee y := by
  simp only [ee, Complex.ofReal_add, mul_add, Complex.exp_add]

 /-- LEAF. The integral of e of k alpha over the unit interval is 1 for integer k = 0 and 0 for every other integer k. Page 270, orthogonality in 3.21. -/
theorem ee_integral_int110 (k : ℤ) : (∫ α in (0 : ℝ)..1, ee ((k : ℝ) * α)) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst k
    simp [ee]
  · have hz : (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hk)
    have he : ∀ α : ℝ, ee ((k : ℝ) * α) = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) * (α : ℂ)) := by
      intro α
      simp only [ee, Complex.ofReal_mul, Complex.ofReal_intCast]
      congr 1
      ring
    simp_rw [he]
    rw [integral_exp_mul_complex hz]
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) by ring,
      Complex.exp_int_mul_two_pi_mul_I]
    simp

 /-- LEAF. The prime window exponential sum is continuous in alpha. Page 270, integrals in 3.20 and 3.21. -/
theorem primeSum_continuous110 (N : ℕ) (U : ℝ) : Continuous (primeSum110 N U) := by
  unfold primeSum110 ee
  fun_prop

 /-- LEAF. The periodic major arc set is Lebesgue measurable. Page 270, E1. -/
theorem majorArcs_measurable110 (N : ℕ) (U d : ℝ) : MeasurableSet (majorArcs110 N U d) := by
  have hset : majorArcs110 N U d = ⋃ (q : ℕ) (a : ℤ),
      {α : ℝ | 1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ d ∧ Int.gcd a q = 1 ∧
        |α - (a : ℝ) / q| ≤ Real.log N ^ (4 : ℝ) / U} := by
    ext α
    simp only [majorArcs110, Set.mem_ofPred_eq, Set.mem_iUnion]
    aesop
  rw [hset]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases h : 1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ d ∧ Int.gcd a q = 1
  · simp only [h.1, h.2.1, h.2.2, true_and]
    exact isClosed_le (by fun_prop) continuous_const |>.measurableSet
  · have hfalse : {α : ℝ | 1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ d ∧ Int.gcd a q = 1 ∧
        |α - (a : ℝ) / q| ≤ Real.log N ^ (4 : ℝ) / U} = ∅ := by
      ext α
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      tauto
    rw [hfalse]
    exact MeasurableSet.empty



/-- LEAF. Page 270, display 3.21. The count T is the sum over three window primes of the indicator that their sum is N. -/
theorem triple_count110 (N : ℕ) (U : ℝ) : (T N U : ℂ) =
    ∑ p ∈ Win N U, ∑ q ∈ Win N U, ∑ r ∈ Win N U,
      if p + q + r = N then (1 : ℂ) else 0 := by
  classical
  unfold T
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hS : ∀ r ∈ Win N U, 0 < r := by
    intro r hr
    exact (Finset.mem_filter.mp hr).2.pos
  by_cases hpq : p + q < N
  · have he : ∀ r : ℕ, p + q + r = N ↔ r = N - p - q := by omega
    simp only [he, Finset.sum_ite_eq', hpq, true_and]
  · have he : ∀ r ∈ Win N U, p + q + r ≠ N := by
      intro r hr
      have := hS r hr
      omega
    simp only [hpq, false_and, ite_false]
    symm
    exact Finset.sum_eq_zero fun r hr => ite_eq_right (he r hr)


/-- LEAF. Page 270, display 3.21. The cubed prime sum times the negative N phase expands into integer frequencies p plus q plus r minus N. -/
theorem primeSum_cube110 (N : ℕ) (U α : ℝ) :
    primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α) =
      ∑ p ∈ Win N U, ∑ q ∈ Win N U, ∑ r ∈ Win N U,
        ee (((p : ℤ) + q + r - N : ℤ) * α) := by
  classical
  simp only [primeSum110, pow_succ, pow_zero, one_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  rw [← ee_add110, ← ee_add110, ← ee_add110]
  congr 1
  push_cast
  ring


/-- LEAF. Page 270, display 3.21. The full unit interval integral of the cubed prime sum times the negative N phase equals T. -/
theorem triple_orthogonality110 (N : ℕ) (U : ℝ) :
    (∫ α in (0 : ℝ)..1, primeSum110 N U α ^ 3 * ee (-(N : ℝ) * α)) = (T N U : ℂ) := by
  classical
  simp_rw [primeSum_cube110]
  rw [intervalIntegral.integral_finsetSum]
  · rw [triple_count110]
    apply Finset.sum_congr rfl
    intro p hp
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro q hq
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro r hr
        rw [ee_integral_int110]
        have he : (p : ℤ) + q + r - N = 0 ↔ p + q + r = N := by omega
        simp only [he]
      · intro r hr
        apply Continuous.intervalIntegrable
        unfold ee
        fun_prop
    · intro q hq
      apply Continuous.intervalIntegrable
      unfold ee
      fun_prop
  · intro p hp
    apply Continuous.intervalIntegrable
    unfold ee
    fun_prop

end
end LeanLab.Zhan1991
