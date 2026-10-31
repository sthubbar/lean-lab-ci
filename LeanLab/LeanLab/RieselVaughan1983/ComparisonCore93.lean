import LeanLab.RieselVaughan1983.SieveWeights93

/-! The local pairing behind equation 3.13 on page 52.
AI wrote the Lean code. Binary Goldbach is OPEN.
The diagnostic theorem rejects a termwise proof, not the paper statement. -/
namespace LeanLab.RieselVaughan1983.ComparisonCore93
open Real Finset
open SieveWeights93
noncomputable section

/-- A termwise comparison cannot prove equation 3.13. -/
lemma termwise_comparison_fails : coefficient 6 3 < Lemma2.sieveCoeff 3 / wt 6 := by
  have hpf : (6 : ℕ).primeFactors = {2, 3} := by norm_num [Nat.primeFactors]
  have hf : (6 : ℕ).primeFactors.filter (2 < ·) = {3} := by
    rw [hpf]
    ext p
    simp only [mem_filter, mem_insert, mem_singleton]
    omega
  have hw : wt 6 = 2 := by
    unfold wt
    rw [hf]
    norm_num
  rw [hw, Lemma2.sieveCoeff_prime 3 (by decide)]
  norm_num [coefficient, localFactor, Lemma2.localWeight,
    (by decide : Nat.Prime 3).primeFactors,
    ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3)]


/-- Pairing m and p*m compensates for the smaller local coefficient.
The cutoff k is 0 if p*m exceeds the summation limit and 1 otherwise. -/
lemma local_pair (p m z k : ℝ) (hp : 2 < p) (hm : 0 ≤ m) (hz : 0 < z)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) :
    (p - 2) / (p - 1) *
        (1 / (1 + m / z) + k * (2 / (p - 2)) / (1 + p * m / z)) ≤
      1 / (1 + m / z) + k * (1 / (p - 1)) / (1 + p * m / z) := by
  have hdm : 0 < 1 + m / z := by positivity
  have hdp : 0 < 1 + p * m / z := by positivity
  have hden : 1 + m / z ≤ 1 + p * m / z := by
    have hmp : m ≤ p * m := by nlinarith
    have hd := div_le_div_of_nonneg_right hmp hz.le
    linarith
  have hr := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hdm hden
  have hkr : k / (1 + p * m / z) ≤ 1 / (1 + m / z) := by
    exact (div_le_div_of_nonneg_right hk1 hdp.le).trans hr
  have hpos : 0 ≤ (1 / (p - 1)) *
      (1 / (1 + m / z) - k / (1 + p * m / z)) := by
    apply mul_nonneg (div_nonneg zero_le_one (by linarith))
    linarith
  have hid : 1 / (1 + m / z) + k * (1 / (p - 1)) / (1 + p * m / z) -
      (p - 2) / (p - 1) *
        (1 / (1 + m / z) + k * (2 / (p - 2)) / (1 + p * m / z)) =
      (1 / (p - 1)) * (1 / (1 + m / z) - k / (1 + p * m / z)) := by
    have hp1 : p - 1 ≠ 0 := by linarith
    have hp2 : p - 2 ≠ 0 := by linarith
    field_simp [hp1, hp2]
    ring
  linarith

end
end LeanLab.RieselVaughan1983.ComparisonCore93

#print axioms LeanLab.RieselVaughan1983.ComparisonCore93.termwise_comparison_fails
#print axioms LeanLab.RieselVaughan1983.ComparisonCore93.local_pair
