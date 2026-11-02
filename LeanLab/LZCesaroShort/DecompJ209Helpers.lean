import LeanLab.LZCesaroShort.Lemma3Coefficients
import LeanLab.PNTPort.StrongPNT.Bridge
import Mathlib

/-!
# Helper lemmas for DecompJ209, lemma3_raw_moment_asymptotic

AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1606.00869v2 page 3, Lemma 3 raw moment.
These helpers derive the weighted Lambda square moment from the strong PNT.
-/

namespace LeanLab.LZCesaroShort

open ArithmeticFunction Chebyshev Filter Topology Finset
open scoped ArithmeticFunction.vonMangoldt

/-- Abel summation: sum of Lambda(k)*log(k) for k<=n expressed via psi. -/
lemma abel_lambda_log (n : ℕ) :
    (∑ k ∈ range (n + 1), vonMangoldt k * Real.log (k : ℝ)) =
    ψ (n : ℝ) * Real.log (n : ℝ) -
    ∑ j ∈ range n, ψ (j : ℝ) * (Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ)) := by
  have h := Finset.sum_range_by_parts (f := fun i : ℕ => Real.log (i : ℝ)) (g := vonMangoldt) (n + 1)
  simp only [Nat.add_sub_cancel] at h
  have hsum : ∀ m : ℕ, (∑ k ∈ range (m + 1), vonMangoldt k) = ψ (m : ℝ) :=
    sum_range_vonMangoldt
  simp_rw [hsum] at h
  have h1 : (∑ i ∈ range (n + 1), Real.log (i : ℝ) * vonMangoldt i) =
      (∑ k ∈ range (n + 1), vonMangoldt k * Real.log (k : ℝ)) := by
    refine sum_congr rfl fun k _ => ?_
    exact mul_comm _ _
  have h2 : Real.log (n : ℝ) * ψ (n : ℝ) = ψ (n : ℝ) * Real.log (n : ℝ) := mul_comm _ _
  have h3 : (∑ x ∈ range n, (Real.log ((x + 1 : ℕ) : ℝ) - Real.log (x : ℝ)) * ψ (x : ℝ)) =
      (∑ j ∈ range n, ψ (j : ℝ) * (Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ))) := by
    refine sum_congr rfl fun j _ => ?_
    exact mul_comm _ _
  calc (∑ k ∈ range (n + 1), vonMangoldt k * Real.log (k : ℝ))
      = (∑ i ∈ range (n + 1), Real.log (i : ℝ) * vonMangoldt i) := h1.symm
    _ = Real.log (n : ℝ) * ψ (n : ℝ) -
          ∑ x ∈ range n, (Real.log ((x + 1 : ℕ) : ℝ) - Real.log (x : ℝ)) * ψ (x : ℝ) := h
    _ = ψ (n : ℝ) * Real.log (n : ℝ) -
          ∑ j ∈ range n, ψ (j : ℝ) * (Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ)) := by
        rw [h2, h3]

/-- The sum of k*(log(k+1)-log k) telescopes to n*log n - sum_{k<=n} log k. -/
lemma telescoping_log_sum (n : ℕ) :
    (∑ j ∈ range n, (j : ℝ) * (Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ))) =
    (n : ℝ) * Real.log (n : ℝ) - ∑ k ∈ range (n + 1), Real.log (k : ℝ) := by
  sorry

/-- The key asymptotic: partial sums of Lambda^2 satisfy |A(n) - n*log n| <= C*n. -/
lemma lambda_sq_partial_sum_bound : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    |(∑ k ∈ range (n + 1), vonMangoldt k ^ 2) - (n : ℝ) * Real.log (n : ℝ)| ≤ C * (n : ℝ) := by
  sorry

end LeanLab.LZCesaroShort
