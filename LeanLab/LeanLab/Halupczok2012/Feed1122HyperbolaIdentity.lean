import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Order.Floor.Semifield

/-!
Deepening of the MEDIUM leaf `hyperbola_identity` of Feed1122VoronoiDivisorSumAsymptotic.
Halupczok journal page 337, the Voronoi formula cited below display 2.2.
The real variable identity reduces to its integer form at N equal to floor x,
since floor of x over m is floor x divided by m and floor of root x is the integer square root of floor x.
The reduction is proved here; the integer hyperbola identity is the remaining leaf.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Feed1122HyperbolaIdentity

open Finset

/-- LEAF: integer Dirichlet hyperbola identity, the first step of the classical proof of the
Voronoi formula cited on Halupczok page 337. For every natural N, the sum of d of n for n up to N
equals twice the sum over m up to the integer square root of N of N divided by m,
minus the square of that integer square root.
Class MEDIUM: an exact finite lattice point count by the symmetry of the hyperbola. -/
theorem nat_hyperbola_identity :
    ∀ N : ℕ, (∑ n ∈ Icc 1 N, (n.divisors.card : ℝ)) =
      2 * ∑ m ∈ Icc 1 (Nat.sqrt N), ((N / m : ℕ) : ℝ) - (Nat.sqrt N : ℝ) ^ 2 := by
  sorry

/-- For x at least 0, the floor of root x is the integer square root of floor x. -/
theorem floor_sqrt_eq (x : ℝ) (hx : 0 ≤ x) : ⌊Real.sqrt x⌋₊ = Nat.sqrt ⌊x⌋₊ := by
  set N := ⌊x⌋₊
  rw [Nat.floor_eq_iff (Real.sqrt_nonneg x)]
  have h1 : ((Nat.sqrt N : ℕ) : ℝ) ^ 2 ≤ x := by
    have := Nat.sqrt_le' N
    have h2 : ((Nat.sqrt N ^ 2 : ℕ) : ℝ) ≤ N := by exact_mod_cast this
    push_cast at h2
    exact h2.trans (Nat.floor_le hx)
  have h3 : x < ((Nat.sqrt N : ℕ) + 1 : ℝ) ^ 2 := by
    have h4 : N + 1 ≤ (Nat.sqrt N + 1) ^ 2 := Nat.lt_succ_sqrt' N
    have h5 : ((N + 1 : ℕ) : ℝ) ≤ (((Nat.sqrt N + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h4
    push_cast at h5
    linarith [Nat.lt_floor_add_one x]
  constructor
  · exact Real.le_sqrt_of_sq_le h1
  · rw [Real.sqrt_lt' (by positivity)]; exact h3

/-- The real variable hyperbola identity, assembled from the integer leaf.
Statement identical to `hyperbola_identity`. -/
theorem hyperbola_identity_of_leaves :
    ∀ x : ℝ, 1 ≤ x →
      (∑ n ∈ Icc 1 ⌊x⌋₊, (n.divisors.card : ℝ)) =
        2 * ∑ m ∈ Icc 1 ⌊Real.sqrt x⌋₊, (⌊x / m⌋₊ : ℝ) - (⌊Real.sqrt x⌋₊ : ℝ) ^ 2 := by
  intro x hx
  have hx0 : 0 ≤ x := by linarith
  rw [floor_sqrt_eq x hx0, nat_hyperbola_identity ⌊x⌋₊]
  congr 2
  apply sum_congr rfl
  intro m _
  rw [Nat.floor_div_natCast]

end LeanLab.Halupczok2012.Feed1122HyperbolaIdentity

#print axioms LeanLab.Halupczok2012.Feed1122HyperbolaIdentity.floor_sqrt_eq
#print axioms LeanLab.Halupczok2012.Feed1122HyperbolaIdentity.hyperbola_identity_of_leaves
