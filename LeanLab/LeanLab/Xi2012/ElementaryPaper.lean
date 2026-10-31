import Mathlib

/-!
Elementary inputs in Xi 2012, arXiv 1206.2148v1, page 5.
No analytic statement of the withdrawn paper is asserted.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Xi2012.NatEncoding

open Finset Real

/-- The finite product over odd prime divisors used on page 5. -/
noncomputable def oddPrimeProduct (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.filter (fun p => 2 < p), (1 + 1 / ((p : ℝ) - 2))

/-- The lower bound is non-strict so it also covers the empty product. -/
theorem one_le_oddPrimeProduct (n : ℕ) : 1 ≤ oddPrimeProduct n := by
  unfold oddPrimeProduct
  apply Finset.one_le_prod₀
  intro p hp
  have hp2 : 2 < p := (Finset.mem_filter.mp hp).2
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp2
  have hnonneg : (0 : ℝ) ≤ 1 / ((p : ℝ) - 2) := by positivity
  linarith

/-- The page 5 strict inequality does not cover this empty product. -/
theorem oddPrimeProduct_two :
    oddPrimeProduct 2 = 1 ∧ ¬ 1 < oddPrimeProduct 2 := by
  have h : oddPrimeProduct 2 = 1 := by
    simp [oddPrimeProduct, Nat.prime_two.primeFactors, Finset.prod_filter]
  exact ⟨h, by rw [h]; norm_num⟩

/-- The product sum in the page 5 deduction dominates the exceptional count. -/
theorem card_le_sum_oddPrimeProduct (E : Finset ℕ) :
    (E.card : ℝ) ≤ ∑ n ∈ E, oddPrimeProduct n := by
  calc
    (E.card : ℝ) = ∑ _n ∈ E, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ E, oddPrimeProduct n :=
      Finset.sum_le_sum (fun n _ => one_le_oddPrimeProduct n)

end LeanLab.Xi2012.NatEncoding
