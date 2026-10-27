/-
Concrete instances for the task63 statement twins.
These are vacuity checks, not a finite-range extension.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.SchnirelmannGoldbach.PureSieveParameters
import LeanLab.SchnirelmannGoldbach.PureSieveLoss
import LeanLab.SchnirelmannGoldbach.PairConventions
import LeanLab.SchnirelmannGoldbach.LoglogUpper
import LeanLab.SchnirelmannGoldbach.Task63Explicit

open Finset Real
open scoped Pointwise Classical

namespace LeanLab.SchnirelmannGoldbach.Task63

/-- The exact small counts used in the statement twins. -/
theorem concrete_counts :
    PureSieve.survivors 10 {2, 3} = 1 ∧ PureSieve.multiples 10 3 = 7 ∧
    PureSieve.brunCount 10 {2, 3} 0 = 10 ∧ PureSieve.brunCount 10 {2, 3} 1 = -2 ∧
    PureSieve.brunCount 10 {2, 3} 2 = 1 ∧ unorderedCount 10 = 2 ∧ r 10 = 3 ∧
    r 8 = 2 ∧ r 6 = 1 ∧ singProd 6 = 2 ∧
    (∏ p ∈ ({3, 5} : Finset ℕ), (1 + 1 / (p : ℝ))) ^ 2 = 64 / 25 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_, ?_⟩
  · have h : (6 : ℕ).primeFactors = {2, 3} := by
      simpa [Nat.prime_two.primeFactors, Nat.prime_three.primeFactors] using Nat.primeFactors_mul (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : (3 : ℕ) ≠ 0)
    norm_num [singProd, h]
  · norm_num

example : ∀ p ∈ ({2, 3} : Finset ℕ), p.Prime := by decide
example : ∀ p ∈ ({3, 5} : Finset ℕ), 3 ≤ p ∧ Odd p := by decide
example : ∀ p ∈ ({3, 5} : Finset ℕ), p < 7 := by decide
example : Even (2 : ℕ) := by decide
example : (0 : ℝ) < 8192 := by norm_num
example : 1 / (Real.log (Real.log (Real.exp (Real.exp 1)))) ^ 6 = (1 : ℝ) := by simp

example : (1 : ℕ) ∈ Icc 1 LeanLab.SchnirelmannExplicit.Sharper5.N₂ := by
  have h := LeanLab.SchnirelmannExplicit.Sharper5.N₂_ge
  simp only [mem_Icc]
  exact ⟨le_rfl, by omega⟩

example : (1 / 14959 : ℝ) * 100003 ≤ #{n ∈ Icc 1 100003 | n ∈ G} :=
  density_mid_14959 100003 le_rfl

example : 0 ∈ (14959 : ℕ) • ({0, 1} ∪ G : Set ℕ) := by
  rw [basis_order_14959]
  trivial

example : ∃ k ≤ 29920, SumOfPrimes k 2 := schnirelmann_bounded_primes_29920 2 le_rfl

end LeanLab.SchnirelmannGoldbach.Task63

#print axioms LeanLab.SchnirelmannGoldbach.Task63.concrete_counts
