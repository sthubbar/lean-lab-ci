import LeanLab.OpenProblems.Erdos9
import LeanLab.OpenProblems.Lemoine
import LeanLab.OpenProblems.Erdos17

/-!
# OpenProblems, named route lemmas for the provers

Unit U-1603, 2026-11-02. AI wrote the Lean code. Each statement below is a named route lemma with
sorry, NOT PROVED. The sealed open problems themselves are `def`s in their own files, and
`MOUNTAIN.md` only lists theorems with a sorry, so these rows are how the provers find this
folder. None of these lemmas settles its open problem. Each one is expected to be true and
weaker than the problem, and closing one is a step, not a solution. Erdős 273 has no row here:
its target is a search winner fed to `Erdos273.statement_of_check`.
-/

namespace LeanLab.OpenProblems

open Erdos9 Lemoine Erdos17

/-- Unit U-1603, route lemma, OPEN in the lab. Plain math: infinitely many odd numbers are not a
prime plus two powers of 2. The site's page for Erdős 9 credits this to Schinzel, and FC tags it
solved with an outside Lean proof whose body module was not read here. A first step of Erdős 9,
far weaker than positive upper density. -/
theorem route_erdos9A_infinite : Erdos9A.Infinite := by
  sorry

/-- Unit U-1603, route lemma, OPEN in the lab. Plain math: the odd numbers of the form `p + 2 q`
have positive lower density, the Lemoine twin of the lab's `S3_positive_lower_density` in
`SchnirelmannGoldbach`. Prior art not searched. Far weaker than Lemoine's conjecture. -/
theorem route_lemoine_positive_density :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      c * N ≤ (({n : ℕ | Odd n ∧ IsLemoine n} ∩ Set.Iic N).ncard : ℝ) := by
  sorry

/-- Unit U-1603, route lemma, OPEN in the lab. Plain math: at most `C x / (log x)^2` cluster primes
lie below `x`, from `prime_near_of_cluster` and a sieve bound for prime pairs with a fixed even
difference, as in the lab's `BrunGap`. Weaker than the Blecksmith, Erdős and Selfridge bound on the
Erdős 17 page, and it points away from infinitely many, so it bounds the problem, not solves it. -/
theorem route_cluster_count_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 3 ≤ x →
      (({p : ℕ | IsClusterPrime p} ∩ Set.Iic x).ncard : ℝ) ≤ C * x / Real.log x ^ 2 := by
  sorry

end LeanLab.OpenProblems

#print axioms LeanLab.OpenProblems.route_erdos9A_infinite
#print axioms LeanLab.OpenProblems.route_lemoine_positive_density
#print axioms LeanLab.OpenProblems.route_cluster_count_le
