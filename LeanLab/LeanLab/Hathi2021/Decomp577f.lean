/-
Rieger 1968, DOI https://doi.org/10.1515/crll.1968.231.89, page 94.
Prime modulus part of Hilfssatz 5 used in the nontrivial collision proof.
This is a partial helper, not the four linear form sieve bound.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import Mathlib

open Finset Polynomial

namespace LeanLab.Hathi2021.Decomp577f

/-- Rieger page 94, the prime modulus step in the written proof of
Hilfssatz 5. A quadratic congruence has at most two roots modulo a prime. -/
theorem prime_square_roots_card_le_two (p : ℕ) [Fact p.Prime] (r : ZMod p) :
    ((Finset.univ : Finset (ZMod p)).filter (fun x => x ^ 2 = r)).card ≤ 2 := by
  classical
  let f : Polynomial (ZMod p) := X ^ 2 - C r
  have hne : f ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by norm_num : 0 < 2) r
  have hsub : ((Finset.univ : Finset (ZMod p)).filter (fun x => x ^ 2 = r)).val ⊆ f.roots := by
    intro x hx
    change x ∈ (Finset.univ : Finset (ZMod p)).filter (fun x => x ^ 2 = r) at hx
    have heq := (Finset.mem_filter.mp hx).2
    apply (Polynomial.mem_roots hne).2
    simp [Polynomial.IsRoot, f, heq]
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  simpa [f] using hcard

end LeanLab.Hathi2021.Decomp577f
