import LeanLab.Hathi2021.Decomp577d

/-!
Rieger 1968 Satz 3, pages 94 to 96, split for Decomp577d.rieger_nontrivial_collision_bound.
DOI https://doi.org/10.1515/crll.1968.231.89, used by Hu 2019 page 195.
The nontrivial collisions of prime squares are first reduced to odd primes with no
lower cutoff, then parameterized as in Rieger display 15, and the parameterized count
is the sieve input of displays 18 to 20.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/

open Finset

namespace LeanLab.Hathi2021.Decomp577dLeavesRieger

open LeanLab.Hathi2021.Decomp577d

/-- Rieger page 94, the set counted by `C x` before display 15: ordered quadruples of
odd primes up to `X` with `p₁² + p₂² = p₃² + p₄²`, excluding the two trivial matches. -/
def oddCollisions (X : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ((range (X + 1)) ×ˢ (range (X + 1)) ×ˢ (range (X + 1)) ×ˢ (range (X + 1))).filter
    (fun q => q.1.Prime ∧ q.1 ≠ 2 ∧ q.2.1.Prime ∧ q.2.1 ≠ 2 ∧ q.2.2.1.Prime ∧ q.2.2.1 ≠ 2 ∧
      q.2.2.2.Prime ∧ q.2.2.2 ≠ 2 ∧
      q.1 ^ 2 + q.2.1 ^ 2 = q.2.2.1 ^ 2 + q.2.2.2 ^ 2 ∧
      (q.2.2.1, q.2.2.2) ≠ (q.1, q.2.1) ∧ (q.2.2.1, q.2.2.2) ≠ (q.2.1, q.1))

/-- An odd prime at most `X`. Helper predicate for the parameterization of Rieger
display 15. -/
def OddPrimeLe (X q : ℕ) : Prop := q.Prime ∧ q ≠ 2 ∧ q ≤ X

instance (X q : ℕ) : Decidable (OddPrimeLe X q) := by unfold OddPrimeLe; infer_instance

/-- Rieger page 94, display 15: from `p₁² - p₃² = p₄² - p₂²` with `p₁ > p₃`, write
`p₁ - p₃ = g u`, `p₄ - p₂ = g v` with `u, v` coprime and `p₁ + p₃ = v h`, `p₄ + p₂ = u h`.
The four primes are then `(gu + vh)/2`, `(vh - gu)/2`, `(gv + uh)/2`, `(uh - gv)/2`.
The case `u = v` is the swapped trivial match and is excluded. Tuples `(g, u, v, h)`. -/
def paramQuads (X : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ((range (2 * X + 1)) ×ˢ (range (2 * X + 1)) ×ˢ (range (2 * X + 1)) ×ˢ
      (range (2 * X + 1))).filter
    (fun t => 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ t.2.1 ≠ t.2.2.1 ∧
      Nat.Coprime t.2.1 t.2.2.1 ∧
      t.1 * t.2.1 < t.2.2.1 * t.2.2.2 ∧ t.1 * t.2.2.1 < t.2.1 * t.2.2.2 ∧
      2 ∣ t.1 * t.2.1 + t.2.2.1 * t.2.2.2 ∧ 2 ∣ t.1 * t.2.2.1 + t.2.1 * t.2.2.2 ∧
      OddPrimeLe X ((t.1 * t.2.1 + t.2.2.1 * t.2.2.2) / 2) ∧
      OddPrimeLe X ((t.2.2.1 * t.2.2.2 - t.1 * t.2.1) / 2) ∧
      OddPrimeLe X ((t.1 * t.2.2.1 + t.2.1 * t.2.2.2) / 2) ∧
      OddPrimeLe X ((t.2.1 * t.2.2.2 - t.1 * t.2.2.1) / 2))

/-- LEAF: Rieger page 94 and Satz 3, reduction of the weighted range to odd primes. Class
MEDIUM. Hu 2019 page 195. The ordered nontrivial collision count with the Hu lower cutoff is
at most the number of odd prime collisions up to `√n`: the cutoff only removes pairs, and a
collision containing the prime 2 is trivial by parity. -/
theorem collisionCount_le_oddCollisions (n₁ n : ℕ) :
    collisionCount n₁ n ≤ ((oddCollisions (Nat.sqrt n)).card : ℝ) := by
  sorry

/-- LEAF: Rieger page 94, display 15, the parameterization. Class MEDIUM. Each odd prime
collision with `p₁ > p₃` gives one tuple of `paramQuads`, with `g = gcd`; the case
`p₁ < p₃` is the same after exchanging the two sides, giving the factor 2. -/
theorem oddCollisions_le_paramQuads (X : ℕ) :
    (oddCollisions X).card ≤ 2 * (paramQuads X).card := by
  sorry

/-- LEAF: Rieger pages 95 and 96, displays 18 to 20. Class HARD. The parameterized count
is `O(n / log³ n)` at `X = √n`: a sieve upper bound for the four linear forms in `g, h`
for fixed `u, v`, then the average of the singular factors over `u, v`. -/
theorem paramQuads_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ((paramQuads (Nat.sqrt n)).card : ℝ) ≤ K * (n : ℝ) / Real.log n ^ 3 := by
  sorry

/-- The exact statement of `Decomp577d.rieger_nontrivial_collision_bound`, from the three
leaves of this file. -/
theorem rieger_nontrivial_collision_bound_of_leaves :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n : ℕ,
      N₀ ≤ n → n ≤ n₁ → collisionCount n₁ n ≤ K * (n : ℝ) / Real.log n ^ 3 := by
  obtain ⟨K, hK, N₀, hN⟩ := paramQuads_bound
  refine ⟨2 * K, by positivity, N₀, fun n₁ n hn _ => ?_⟩
  have h1 := collisionCount_le_oddCollisions n₁ n
  have h2 : ((oddCollisions (Nat.sqrt n)).card : ℝ) ≤
      2 * ((paramQuads (Nat.sqrt n)).card : ℝ) := by
    exact_mod_cast oddCollisions_le_paramQuads (Nat.sqrt n)
  have h3 := hN n hn
  calc collisionCount n₁ n ≤ 2 * ((paramQuads (Nat.sqrt n)).card : ℝ) := h1.trans h2
    _ ≤ 2 * (K * (n : ℝ) / Real.log n ^ 3) := by linarith
    _ = 2 * K * (n : ℝ) / Real.log n ^ 3 := by ring

end LeanLab.Hathi2021.Decomp577dLeavesRieger
