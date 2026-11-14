import LeanLab.LiuWang2002.ThetaCert352

/-!
Negative results for binomial and scalar exponential envelopes.
Source Schoenfeld page 356, display 5.1 star, derived proof route audit.
This compares upper envelopes and does not refute a primorial bound.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task551

/-- The polynomial factor k is absorbed by the ratio of the two
exponential bases for k at least eight. Derived arithmetic for the
finite certificate route on Schoenfeld page 356, display 5.1 star. -/
theorem mul_three_pow_le_four_pow (k : ℕ) (hk : 8 ≤ k) :
    k * 3 ^ k ≤ 4 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => decide +kernel
  | succ k hk ih =>
    rw [pow_succ, pow_succ]
    calc
      (k + 1) * (3 ^ k * 3) = (3 * (k + 1)) * 3 ^ k := by ring
      _ ≤ (4 * k) * 3 ^ k := Nat.mul_le_mul_right _ (by omega)
      _ = (k * 3 ^ k) * 4 := by ring
      _ ≤ 4 ^ k * 4 := Nat.mul_le_mul_right _ ih

/-- The Mathlib binomial interval upper envelope exceeds the desired
normalized contraction when the width is at least eight and at most
the left endpoint. Derived negative route result for Schoenfeld
page 356, display 5.1 star. This is not a negation of any assigned leaf. -/
theorem binomial_envelope_exceeds_target (a k : ℕ) (hk : 8 ≤ k) (ha : k ≤ a) :
    68 ^ k < (a + k).choose a * 25 ^ k := by
  have hcentral : 3 ^ k < k.centralBinom := by
    have h := (mul_three_pow_le_four_pow k hk).trans_lt
      (Nat.four_pow_lt_mul_centralBinom k (by omega))
    exact Nat.lt_of_mul_lt_mul_left h
  have hchoose : 3 ^ k ≤ (a + k).choose a := by
    rw [Nat.choose_symm_add]
    exact hcentral.le.trans (Nat.choose_le_choose k (by omega))
  have hpow : 68 ^ k < 75 ^ k :=
    Nat.pow_lt_pow_left (by decide) (by omega)
  calc
    68 ^ k < 75 ^ k := hpow
    _ = 3 ^ k * 25 ^ k := by norm_num [← mul_pow]
    _ ≤ (a + k).choose a * 25 ^ k := Nat.mul_le_mul_right _ hchoose

/-- The first proposed smaller range has a binomial envelope larger
than its target ratio. The exponents stay symbolic during checking.
Derived instance for Schoenfeld page 356, display 5.1 star. -/
theorem binomial_first_range_obstruction :
    68 ^ 4000000 < (16000000 + 4000000).choose 16000000 * 25 ^ 4000000 := by
  exact binomial_envelope_exceeds_target 16000000 4000000 (by omega) (by omega)

/-- The scalar exponential envelope in display 5.1 star admits a
positive real equality case in the product comparison. The witness
is not asserted to be an actual primorial. Derived negative route
comparison for Schoenfeld page 356. -/
theorem paper_envelope_has_countermodel (n : ℕ) (hn : 0 < n) :
    ∃ y : ℝ, 0 < y ∧ y < Real.exp (1.001093 * n) ∧
      y * 25 ^ n = (68 : ℝ) ^ n := by
  refine ⟨(68 / 25 : ℝ) ^ n, by positivity, ?_, ?_⟩
  · calc
      (68 / 25 : ℝ) ^ n < (Real.exp 1.001093) ^ n :=
        pow_lt_pow_left₀ Task352.certificate_base (by norm_num) (by omega)
      _ = Real.exp (1.001093 * n) := by rw [mul_comm, Real.exp_nat_mul]
  · rw [div_pow]
    exact div_mul_cancel₀ _ (by positivity)

end LeanLab.LiuWang2002.Task551
#print axioms LeanLab.LiuWang2002.Task551.mul_three_pow_le_four_pow
#print axioms LeanLab.LiuWang2002.Task551.binomial_envelope_exceeds_target
#print axioms LeanLab.LiuWang2002.Task551.binomial_first_range_obstruction
#print axioms LeanLab.LiuWang2002.Task551.paper_envelope_has_countermodel
