/-
AI-written Lean code, Claude, 2026-10-20, CLOUD 20261020T0115Z-cloud31, unit U-5913, paper P0004.

# Hardy-Littlewood 1923, Section 5.69: Theorems X 2, X 4 and the combinatorial core of X 5

Read from the page images pp. 64 to 66 of `papers/P0004.pdf`. A group `b₁ < ⋯ < b_m` is
*possible* when its singular series `H(b)` is nonzero, which by Theorem X 2 holds when for each prime
`ϖ` the `b`'s miss some residue mod `ϖ`; that residue condition is the definition used here.
Theorem X 4: if `p_r ≤ n < p_{r+1}` then `p_{r+1}, …, p_{r+n}` is a possible `n`-group. Theorem X 5:
with `x = p_{r+n} - p_{r+1} + 1`, `ρ(x) ≥ n`. The paper's `ρ(x)` is `limsup (π(n + x) - π(n))` and
equals the largest possible group of length `x` only on its Hypothesis X, the prime `k`-tuples
conjecture, Theorem X 1; what is proved here with no hypothesis is the combinatorial statement, a
possible group of `n` primes of length `x`. Only `n < p_{r+1}` is needed.

The prime `k`-tuples conjecture and binary Goldbach are OPEN.
-/
import Mathlib

namespace LeanLab.HardyLittlewood1923.Section5

open Finset

/-- A finite set is *possible*, admissible: for every prime `q` it misses some residue mod `q`. -/
def Possible (b : Finset ℕ) : Prop := ∀ q : ℕ, q.Prime → ∃ a < q, ∀ x ∈ b, x % q ≠ a

/-- Pigeonhole: fewer than `q` elements miss a residue mod `q`. -/
lemma possible_of_card_lt (b : Finset ℕ) (q : ℕ) (hq : 0 < q) (h : b.card < q) :
    ∃ a < q, ∀ x ∈ b, x % q ≠ a := by
  by_contra hne
  push_neg at hne
  have hsub : Finset.range q ⊆ b.image (fun x => x % q) := by
    intro a ha
    obtain ⟨x, hx, hxa⟩ := hne a (mem_range.mp ha)
    exact mem_image.mpr ⟨x, hx, hxa⟩
  have := (card_le_card hsub).trans card_image_le
  rw [card_range] at this
  omega

/-- The block of `n` consecutive primes starting at `p_{r+1} = nth Prime r`. -/
noncomputable def block (r n : ℕ) : Finset ℕ := (Finset.range n).image (fun i => Nat.nth Nat.Prime (r + i))

lemma card_block (r n : ℕ) : (block r n).card = n := by
  rw [block, card_image_of_injective _ fun i j h => by
    have := Nat.nth_injective Nat.infinite_setOf_prime h; omega]
  exact card_range n

/-- **Theorem X 4.** If `n < p_{r+1}`, in particular if `p_r ≤ n < p_{r+1}`, then
`p_{r+1}, …, p_{r+n}` is a possible group. -/
theorem theoremX4 (r n : ℕ) (hn : n < Nat.nth Nat.Prime r) : Possible (block r n) := by
  intro q hq
  by_cases hqn : q ≤ n
  · refine ⟨0, hq.pos, fun x hx => ?_⟩
    obtain ⟨i, -, rfl⟩ := mem_image.mp hx
    have hp := Nat.prime_nth_prime (r + i)
    have hmono : Nat.nth Nat.Prime r ≤ Nat.nth Nat.Prime (r + i) :=
      Nat.nth_monotone Nat.infinite_setOf_prime (by omega)
    intro h0
    have hdvd : q ∣ Nat.nth Nat.Prime (r + i) := Nat.dvd_of_mod_eq_zero h0
    have := (Nat.prime_dvd_prime_iff_eq hq hp).mp hdvd
    omega
  · exact possible_of_card_lt _ q hq.pos (by rw [card_block]; omega)

/-- **Theorem X 5, combinatorial core.** If `1 ≤ n < p_{r+1}`, there is a possible group of `n`
primes inside `[p_{r+1}, p_{r+n}]`, an interval of length `x = p_{r+n} - p_{r+1} + 1`. -/
theorem theoremX5 (r n : ℕ) (h1 : 1 ≤ n) (hn : n < Nat.nth Nat.Prime r) :
    ∃ b : Finset ℕ, Possible b ∧ b.card = n ∧ (∀ y ∈ b, y.Prime) ∧
      ∀ y ∈ b, Nat.nth Nat.Prime r ≤ y ∧ y ≤ Nat.nth Nat.Prime (r + n - 1) := by
  refine ⟨block r n, theoremX4 r n hn, card_block r n, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨i, -, rfl⟩ := mem_image.mp hy
    exact Nat.prime_nth_prime _
  · obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
    rw [mem_range] at hi
    exact ⟨Nat.nth_monotone Nat.infinite_setOf_prime (by omega),
      Nat.nth_monotone Nat.infinite_setOf_prime (by omega)⟩

end LeanLab.HardyLittlewood1923.Section5
