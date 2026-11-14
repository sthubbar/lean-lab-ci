import LeanLab.ChirreHagen2025.FinitePrimePowers272
import LeanLab.ChirreHagen2025.Decomp377c
import LeanLab.ChirreHagen2025.Additional122
import LeanLab.ChirreHagen2025.DecompJ207

/-!
Decomposition of P0075 Lemma A.2, page 14.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.DecompJ611

open Real ArithmeticFunction


/-- LEAF. P0075 Lemma A.2, page 14: bound the full sum by a sum over primes and prime powers. -/
theorem leaf_sum_split (x : ℝ) (hx : 10 ^ 13 ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n ^ 2 / (n : ℝ)) ≤
      (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊x⌋₊), Real.log (p : ℝ) ^ 2 / (p : ℝ)) +
        (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊Real.sqrt x⌋₊),
          ∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log (p : ℝ)⌋₊,
            Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ k) := by
  exact Decomp377c.leaf_sum_split x hx

/-- LEAF. P0075 Lemma A.2, page 14: bound the sum over prime powers by the infinite series. -/
theorem leaf_sum_prime_powers (x : ℝ) (hx : 10 ^ 13 ≤ x) :
    (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊Real.sqrt x⌋₊),
      ∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log (p : ℝ)⌋₊,
        Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ k) ≤
          ∑' p : Nat.Primes, Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (p : ℝ)) := by
  exact FinitePrimePowers272.leaf_sum_prime_powers x hx

/-- LEAF. P0075 Lemma A.2, page 14: numerical bound for the sum over prime powers. -/
theorem leaf_sum_prime_powers_bound :
    (∑' p : Nat.Primes, Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (p : ℝ))) < 0.982 :=
  DecompJ207.lemmaA1_part3_assumed.2

/-- LEAF. P0075 Lemma A.2, page 14: bound the sum over primes using integration by parts. -/
theorem leaf_theta_integral (x : ℝ) (hx : 10 ^ 13 ≤ x) (hRH : RiemannHypothesis) :
    (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊x⌋₊), Real.log (p : ℝ) ^ 2 / (p : ℝ)) ≤
      Real.log x ^ 2 / 2 + 3.5402 := sorry


theorem lemmaA2_assembled : Additional122.lemmaA2 := by
  intro hRH x hx
  have h1 := leaf_sum_split x hx
  have h2 := leaf_sum_prime_powers x hx
  have h3 := leaf_sum_prime_powers_bound
  have h4 := leaf_theta_integral x hx hRH
  calc
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, vonMangoldt n ^ 2 / (n : ℝ))
      ≤ (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊x⌋₊), Real.log (p : ℝ) ^ 2 / (p : ℝ)) +
          (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊Real.sqrt x⌋₊),
            ∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log (p : ℝ)⌋₊,
              Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ k) := h1
    _ ≤ (Real.log x ^ 2 / 2 + 3.5402) +
          (∑' p : Nat.Primes, Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (p : ℝ))) := add_le_add h4 h2
    _ ≤ (Real.log x ^ 2 / 2 + 3.5402) + 0.982 := by linarith [h3]
    _ = Real.log x ^ 2 / 2 + 4.5222 := by ring

end LeanLab.ChirreHagen2025.DecompJ611
