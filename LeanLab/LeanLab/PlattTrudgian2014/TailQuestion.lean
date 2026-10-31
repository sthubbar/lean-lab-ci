/-
AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1404.5669v2 page 2 defines k as a multiplicative function.
Page 5 asserts k d at most inverse of d minus 2 for every d greater than 3.
These exact counterexamples are a QUESTION for review, not a FINDING.
They do not refute either computed finite C3 lower bound.
-/
import Mathlib

namespace LeanLab.PlattTrudgian2014

noncomputable def paperWeight (d : ℕ) : ℝ :=
  if Odd d ∧ Squarefree d then ∏ p ∈ d.primeFactors, (1 : ℝ) / ((p : ℝ) - 2) else 0

theorem paperWeight_fifteen : paperWeight 15 = 1 / 3 := by
  have hs : Odd 15 ∧ Squarefree 15 := by decide +kernel
  have hp : Nat.primeFactors 15 = {3, 5} := by decide +kernel
  norm_num [paperWeight, hs, hp]

theorem pointwise_tail_bound_fails_at_fifteen :
    (1 : ℝ) / (15 - 2) < paperWeight 15 := by
  rw [paperWeight_fifteen]
  norm_num

set_option maxRecDepth 10000 in
theorem paperWeight_40011 : paperWeight 40011 = 1 / 13335 := by
  have hs : Odd 40011 ∧ Squarefree 40011 := by decide +kernel
  have hp : Nat.primeFactors 40011 = {3, 13337} := by decide +kernel
  norm_num [paperWeight, hs, hp]

theorem pointwise_tail_bound_fails_above_cutoff :
    ∃ d : ℕ, 40000 < d ∧ (1 : ℝ) / ((d : ℝ) - 2) < paperWeight d := by
  refine ⟨40011, by norm_num, ?_⟩
  rw [paperWeight_40011]
  norm_num

#print axioms paperWeight_fifteen
#print axioms pointwise_tail_bound_fails_at_fifteen
#print axioms paperWeight_40011
#print axioms pointwise_tail_bound_fails_above_cutoff

end LeanLab.PlattTrudgian2014
