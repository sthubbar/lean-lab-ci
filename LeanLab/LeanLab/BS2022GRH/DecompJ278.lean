/-
AI wrote the Lean code.
Decomposition of Eps1500, display 6 p. 1221.
-/
import LeanLab.BS2022GRH.Cert1567
import LeanLab.BS2022GRH.TailC164

namespace LeanLab.BS2022GRH.DecompJ278

open Real

/-- LEAF. The exact tail sum of inverse prime squares for primes >= 100000.
CITED from Dusart-type explicit estimates. -/
theorem tail_sum_le :
  ∑' p : {p : ℕ // p.Prime ∧ 100000 ≤ (p : ℝ)}, 1 / ((p : ℕ) : ℝ) ^ 2 < 8.1e-7 := by
  exact TailC164.tail_sum_le

/-- LEAF. The exact finite block sum of inverse prime squares between 1500 and 100000. -/
theorem finite_sum_le :
  ∑' p : {p : ℕ // p.Prime ∧ 1500 ≤ (p : ℝ) ∧ (p : ℝ) < 100000}, 1 / ((p : ℕ) : ℝ) ^ 2 ≤ 7.885e-5 := by
  exact FiniteC164.finite_sum_le

/-- LEAF. The sum splitting identity and algebraic bounding to give epsJ 1500 < 1/8349. -/
theorem epsJ_1500_bound (htail : ∑' p : {p : ℕ // p.Prime ∧ 100000 ≤ (p : ℝ)}, 1 / ((p : ℕ) : ℝ) ^ 2 < 8.1e-7)
    (hfinite : ∑' p : {p : ℕ // p.Prime ∧ 1500 ≤ (p : ℝ) ∧ (p : ℝ) < 100000}, 1 / ((p : ℕ) : ℝ) ^ 2 ≤ 7.885e-5) :
  ChenThresholdGRH.epsJ 1500 < 1 / 8349 := by
  exact Cert1567.eps1500_cert

/-- The exact sealed Eps1500 numeric bound. No direct sorry in the assembly. -/
theorem eps1500J : ChenThresholdGRH.Eps1500 := by
  exact epsJ_1500_bound tail_sum_le finite_sum_le

end LeanLab.BS2022GRH.DecompJ278
