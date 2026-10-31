/-
AI wrote this Lean code for CODEX task58.
Exact integration of the accelerated IB1 polynomial.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task58IB1Polynomial
import LeanLab.ChenPrimeExceptional.Task58MassCertificate

open Real Finset intervalIntegral MeasureTheory

namespace LeanLab.ChenPrimeExceptional.Task58

noncomputable section

/-- Monomial form of the logarithm polynomial. -/
theorem logPoly_expansion (n : ℕ) (q : ℝ) :
    logPoly n q = ∑ i ∈ range n, -(-1 : ℝ) ^ (i + 1) / (i + 1) * q ^ (i + 1) := by
  unfold logPoly
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i hi
  rw [neg_pow]
  ring

/-- Monomial form of the reciprocal polynomial. -/
theorem reciprocalPoly_expansion (q : ℝ) :
    reciprocalPoly q = ∑ j ∈ range 70, (1 + (-1 / 2 : ℝ) ^ j / 2) * q ^ j := by
  unfold reciprocalPoly geomPoly
  rw [sum_div, ← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  have hp : (-q / 2) ^ j = (-1 / 2 : ℝ) ^ j * q ^ j := by
    rw [← mul_pow]
    congr 1
    ring
  rw [hp]
  ring

/-- Product polynomial expressed in monomials. -/
theorem massPoly_expansion (q : ℝ) :
    massPoly q = ∑ i ∈ range 60, ∑ j ∈ range 70,
      (-(-1 : ℝ) ^ (i + 1) / (i + 1) * (1 + (-1 / 2 : ℝ) ^ j / 2)) *
        q ^ (i + j + 1) := by
  unfold massPoly
  rw [logPoly_expansion, reciprocalPoly_expansion, sum_mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  have hp : q ^ (i + 1) * q ^ j = q ^ (i + j + 1) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = (-(-1 : ℝ) ^ (i + 1) / (i + 1) * (1 + (-1 / 2 : ℝ) ^ j / 2)) *
        (q ^ (i + 1) * q ^ j) := by ring
    _ = _ := by rw [hp]

/-- Exact integration reduces to the rational certificate. -/
theorem integral_massPoly : (∫ q in (0 : ℝ)..(7 / 10), massPoly q) = polynomialMassQ := by
  let c : ℕ → ℕ → ℝ := fun i j =>
    -(-1 : ℝ) ^ (i + 1) / (i + 1) * (1 + (-1 / 2 : ℝ) ^ j / 2)
  have hc : ∀ i j, Continuous (fun q : ℝ => c i j * q ^ (i + j + 1)) := by
    intro i j
    exact continuous_const.mul (continuous_id.pow _)
  have hsum : ∀ i, IntervalIntegrable
      (fun q : ℝ => ∑ j ∈ range 70, c i j * q ^ (i + j + 1)) volume 0 (7 / 10) := by
    intro i
    exact (continuous_finsetSum _ (fun j _ => hc i j)).intervalIntegrable _ _
  rw [integral_congr (fun q _ => massPoly_expansion q)]
  change (∫ q in (0 : ℝ)..(7 / 10), ∑ i ∈ range 60, ∑ j ∈ range 70,
    c i j * q ^ (i + j + 1)) = _
  rw [integral_finsetSum (fun i _ => hsum i)]
  have he : (∑ i ∈ range 60, ∫ q in (0 : ℝ)..(7 / 10),
      ∑ j ∈ range 70, c i j * q ^ (i + j + 1)) =
      ∑ i ∈ range 60, ∑ j ∈ range 70,
        c i j * (7 / 10 : ℝ) ^ (i + j + 2) / (i + j + 2) := by
    apply sum_congr rfl
    intro i hi
    rw [integral_finsetSum (fun j _ => (hc i j).intervalIntegrable _ _)]
    apply sum_congr rfl
    intro j hj
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp only [zero_pow (by omega : i + j + 1 + 1 ≠ 0), sub_zero]
    have hn : i + j + 1 + 1 = i + j + 2 := by omega
    rw [hn]
    push_cast
    ring
  rw [he]
  unfold polynomialMassQ
  push_cast
  rfl

end
end LeanLab.ChenPrimeExceptional.Task58

#print axioms LeanLab.ChenPrimeExceptional.Task58.logPoly_expansion
#print axioms LeanLab.ChenPrimeExceptional.Task58.reciprocalPoly_expansion
#print axioms LeanLab.ChenPrimeExceptional.Task58.massPoly_expansion
#print axioms LeanLab.ChenPrimeExceptional.Task58.integral_massPoly
