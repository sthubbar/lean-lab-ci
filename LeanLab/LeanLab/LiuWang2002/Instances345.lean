import LeanLab.LiuWang2002.Decomp345b
import LeanLab.LiuWang2002.Numeric345

/-!
Task345. Concrete instances for the supplied statements.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.LiuWang2002.Task345

open Real Finset U1543

/-- A concrete instance of both explicit component hypotheses, using X equal to 1.
This checks the hypotheses of psi_bound_of_components on Schoenfeld page 356. -/
theorem component_instance :
    (0 : ℝ) < 1 ∧ Chebyshev.theta 1 ≤ 1.001093 * 1 ∧
      Chebyshev.psi 1 - Chebyshev.theta 1 ≤
        1.001093 * √1 + 3 * (1 : ℝ) ^ (1 / 3 : ℝ) := by
  have ht : Chebyshev.theta 1 = 0 := Chebyshev.theta_eq_zero_of_lt_two (by norm_num)
  norm_num [ht, Chebyshev.psi_one]

/-- The threshold used in Lemma 6.2 on page 169 is attained and is positive. -/
theorem threshold_instance : exp 9.634 ≤ exp 9.634 ∧ 0 < exp (9.634 : ℝ) :=
  ⟨le_rfl, exp_pos _⟩

/-- A nonempty first sum instance for Lemma 6.2 on page 169.
At N equal to ceiling exp 3100 and c equal to zero, the prime 2 lies in
both the strict summation range and the first Vaughan coefficient cutoff. -/
theorem first_sum_instance :
    3100 ≤ Real.log (⌈exp 3100⌉₊ : ℕ) ∧
      2 ∈ rangeN 0 ⌈exp 3100⌉₊ ∧
        (2 : ℝ) ≤ Uf ⌈exp 3100⌉₊ ∧ 0 < lam1 (Uf ⌈exp 3100⌉₊) 2 := by
  have hL := logN_hyp_holds
  have h2 : 2 ≤ ⌈exp (3100 : ℝ)⌉₊ := by
    have he : (2 : ℝ) ≤ exp (3100 : ℝ) := by linarith [Real.add_one_le_exp (3100 : ℝ)]
    exact_mod_cast he.trans (Nat.le_ceil (exp (3100 : ℝ)))
  have hU : (2 : ℝ) ≤ Uf ⌈exp 3100⌉₊ := by
    have hu := (params_facts ⌈exp 3100⌉₊ hL).1
    linarith
  refine ⟨hL, ?_, hU, ?_⟩
  · simp only [rangeN, mem_filter, mem_Icc, zero_mul]
    exact ⟨⟨by norm_num, h2⟩, by norm_num⟩
  · simp only [lam1, Nat.cast_ofNat, if_pos hU]
    exact ArithmeticFunction.vonMangoldt_pos_iff.mpr Nat.prime_two.isPrimePow

/-- A concrete instance of the hypotheses of the denominator half of display 6.5. -/
theorem q_exp_instance :
    exp 30.95 ≤ exp (31 : ℝ) ∧
      (0.28 / 1.0012) ^ 2 * log (exp (31 : ℝ)) ^ 4 < (100000 : ℕ) := by
  constructor
  · exact exp_le_exp.mpr (by norm_num)
  · norm_num

/-- Concrete witnesses for all three ranges in Schoenfeld page 356.
The middle witness exp 18.5 lies strictly between 10 to the eighth and exp 18.7. -/
theorem theta_range_instances :
    ((0 : ℝ) < 1 ∧ (1 : ℝ) ≤ 10 ^ 8) ∧
      ((10 : ℝ) ^ 8 < exp 18.5 ∧ exp (18.5 : ℝ) < exp 18.7) ∧
        exp (18.7 : ℝ) ≤ exp 18.7 := by
  have he : (2.7182818283 : ℝ) ≤ exp 1 := Real.exp_one_gt_d9.le
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) he 18
  have hs : (1.625 : ℝ) ≤ exp 0.5 := by
    have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.5) 3
    norm_num [Finset.sum_range_succ, Nat.factorial] at ht
    linarith
  have hmid : (10 : ℝ) ^ 8 < exp 18.5 := by
    calc
      (10 : ℝ) ^ 8 < 2.7182818283 ^ 18 * 1.625 := by norm_num
      _ ≤ exp 1 ^ 18 * exp 0.5 := mul_le_mul hp hs (by norm_num) (by positivity)
      _ = exp 18.5 := by rw [← exp_nat_mul, ← exp_add]; norm_num
  exact ⟨⟨by norm_num, by norm_num⟩,
    ⟨hmid, exp_lt_exp.mpr (by norm_num)⟩, le_rfl⟩

/-- Concrete nonempty parameters for the derived prime power helpers on
Schoenfeld page 356. The gap at 10000 contains the proper prime power 4,
and theta at 2 is positive. The compressed count at 168 equals 25. -/
theorem additional_instances :
    (9.634 : ℝ) ≤ 10 ∧ exp 9.634 ≤ exp (10 : ℝ) ∧ (8 : ℕ) ≤ 8 ∧
      (8 : ℝ) ≤ log (exp (10 : ℝ)) / log 2 ∧ (0 : ℝ) < 10000 ∧
        (10000 : ℝ) ≤ 16384 ∧ 0 < Chebyshev.psi 10000 - Chebyshev.theta 10000 ∧
          0 < Chebyshev.theta 2 ∧ powerBitSum 168 = 25 := by
  have h8 : (8 : ℝ) ≤ log (exp (10 : ℝ)) / log 2 := by
    rw [log_exp]
    apply (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    linarith [Real.log_two_lt_d9]
  have hg : 0 < Chebyshev.psi 10000 - Chebyshev.theta 10000 := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime]
    apply Finset.sum_pos'
    · intro n hn
      exact ArithmeticFunction.vonMangoldt_nonneg
    · refine ⟨4, ?_, ?_⟩
      · norm_num
      · exact ArithmeticFunction.vonMangoldt_pos_iff.mpr (by decide +kernel)
  exact ⟨by norm_num, exp_le_exp.mpr (by norm_num), by norm_num, h8,
    by norm_num, by norm_num, hg, Chebyshev.theta_pos le_rfl, power_bit_certificate.1⟩

end LeanLab.LiuWang2002.Task345

#print axioms LeanLab.LiuWang2002.Task345.component_instance
#print axioms LeanLab.LiuWang2002.Task345.threshold_instance
#print axioms LeanLab.LiuWang2002.Task345.first_sum_instance
#print axioms LeanLab.LiuWang2002.Task345.q_exp_instance

#print axioms LeanLab.LiuWang2002.Task345.theta_range_instances

#print axioms LeanLab.LiuWang2002.Task345.additional_instances
