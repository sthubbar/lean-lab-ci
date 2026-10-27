/-
# R-0036, T3 MOONSHOT: the equivariant topology route, Z/2 index and Lefschetz counts

Unit U-1342, PC run 20261021T0303Z-27628. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN; nothing here is progress on it.

The route: Borsuk-Ulam, Z/2 index, Smith theory and Lefschetz-type arguments prove that a
solution exists by computing a count modulo 2, or a signed count, from topology. The Goldbach
solution set {a ≤ N : a, N - a in P} carries exactly one natural symmetry, the reflection
a ↦ N - a, a Z/2 action whose only possible fixed point is N/2. This file proves that every
such invariant is determined by trivial data:

PROVED here, unconditional, for an arbitrary decidable predicate `P`:
* `count_two_mul_mod_two`: r_P(2m) mod 2 = 1 if P m, else 0. The mod 2 count is the fixed
  point count of the reflection, Smith's congruence in its zero dimensional form.
* `signed_count_eq_zero`: for any sign ε with ε(N - a) = -ε(a), Σ_{solutions} ε(a) = 0. Every
  orientation-reversing equivariant degree of the reflection vanishes identically.
* `parity_blind`: the mod 2 invariant of P at 2m equals that of P ∩ {m}, whose count is at
  most one and is zero when m ∉ P. So the Z/2 invariant cannot tell the primes from a set
  that misses every even number whose half is not in it.
* `exists_of_count_odd`: an odd count gives a representation; for P = primes this happens
  only when m itself is prime, the trivial case m + m.
-/
import Mathlib

namespace LeanLab.Routes.R0036

open Finset

/-- Ordered representation count of `N` as `a + (N - a)` with both summands in `P`. -/
def r (P : ℕ → Prop) [DecidablePred P] (N : ℕ) : ℕ :=
  ∑ a ∈ range (N + 1), if P a ∧ P (N - a) then 1 else 0

theorem r_eq_card (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    r P N = ((range (N + 1)).filter (fun a => P a ∧ P (N - a))).card := by
  unfold r; rw [Finset.card_filter]

/-- The reflection identity: the summand is symmetric under `a ↦ N - a`. -/
theorem r_reflect (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    (∑ a ∈ range (N + 1), if P (N - a) ∧ P (N - (N - a)) then (1 : ℕ) else 0) = r P N := by
  unfold r
  have := Finset.sum_range_reflect (fun a => if P a ∧ P (N - a) then (1 : ℕ) else 0) (N + 1)
  simpa using this

/-- Smith's congruence for the reflection: the count at `2m` is odd iff `m ∈ P`. -/
theorem count_two_mul_mod_two (P : ℕ → Prop) [DecidablePred P] (m : ℕ) :
    r P (2 * m) % 2 = if P m then 1 else 0 := by
  set f : ℕ → ℕ := fun a => if P a ∧ P (2 * m - a) then 1 else 0 with hf
  -- split range (2m+1) as [0,m) ∪ {m} ∪ [m+1, 2m+1)
  have hsplit : r P (2 * m) = (∑ k ∈ range m, f k) + f m + ∑ k ∈ range m, f (m + 1 + k) := by
    unfold r
    rw [show 2 * m + 1 = (m + 1) + m by ring, Finset.sum_range_add, Finset.sum_range_succ]
  have hhi : (∑ k ∈ range m, f (m + 1 + k)) = ∑ k ∈ range m, f k := by
    rw [← Finset.sum_range_reflect f m]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < m := Finset.mem_range.mp hk
    simp only [hf]
    have h1 : 2 * m - (m + 1 + k) = m - 1 - k := by omega
    have h2 : 2 * m - (m - 1 - k) = m + 1 + k := by omega
    rw [h1, h2]
    by_cases ha : P (m + 1 + k) <;> by_cases hb : P (m - 1 - k) <;> simp [ha, hb]
  have hmid : f m = if P m then 1 else 0 := by
    simp only [hf]
    have : 2 * m - m = m := by omega
    rw [this]; by_cases h : P m <;> simp [h]
  rw [hsplit, hhi, hmid]
  by_cases h : P m <;> simp [h] <;> omega

/-- Orientation-reversing equivariant degrees vanish: an antisymmetric signed count is zero. -/
theorem signed_count_eq_zero (P : ℕ → Prop) [DecidablePred P] (N : ℕ) (ε : ℕ → ℤ)
    (hε : ∀ a ≤ N, ε (N - a) = -ε a) :
    (∑ a ∈ range (N + 1), if P a ∧ P (N - a) then ε a else 0) = 0 := by
  set S := ∑ a ∈ range (N + 1), if P a ∧ P (N - a) then ε a else 0 with hS
  have hrefl : S = ∑ a ∈ range (N + 1),
      if P (N - a) ∧ P (N - (N - a)) then ε (N - a) else 0 := by
    rw [hS]
    have := Finset.sum_range_reflect (fun a => if P a ∧ P (N - a) then ε a else 0) (N + 1)
    simpa using this.symm
  have hneg : S = -S := by
    calc S = _ := hrefl
      _ = ∑ a ∈ range (N + 1), -(if P a ∧ P (N - a) then ε a else 0) := by
          apply Finset.sum_congr rfl
          intro a ha
          have haN : a ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
          have h2 : N - (N - a) = a := by omega
          rw [h2, hε a haN]
          by_cases h1 : P (N - a) <;> by_cases h3 : P a <;> simp [h1, h3]
      _ = -S := by rw [Finset.sum_neg_distrib]
  omega

/-- The singleton slice `P ∩ {m}` has count at most one at `2m`, exactly `1` iff `m ∈ P`. -/
theorem r_singleton (P : ℕ → Prop) [DecidablePred P] (m : ℕ) :
    r (fun n => P n ∧ n = m) (2 * m) = if P m then 1 else 0 := by
  unfold r
  rw [Finset.sum_eq_single m]
  · have : 2 * m - m = m := by omega
    rw [this]; by_cases h : P m <;> simp [h]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

/-- Z/2 blindness: the primes and the slice `primes ∩ {m}` have the same mod 2 invariant. -/
theorem parity_blind (P : ℕ → Prop) [DecidablePred P] (m : ℕ) :
    r P (2 * m) % 2 = r (fun n => P n ∧ n = m) (2 * m) % 2 := by
  rw [count_two_mul_mod_two, r_singleton]
  by_cases h : P m <;> simp [h]

/-- An odd count gives a representation. -/
theorem exists_of_count_odd (P : ℕ → Prop) [DecidablePred P] (N : ℕ) (h : r P N % 2 = 1) :
    ∃ a ≤ N, P a ∧ P (N - a) := by
  by_contra hne
  push_neg at hne
  have : r P N = 0 := by
    unfold r
    apply Finset.sum_eq_zero
    intro a ha
    have haN : a ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    by_cases hp : P a
    · simp [hp, hne a haN hp]
    · simp [hp]
  omega

/-- For the primes the odd case is the trivial representation `m + m`. -/
theorem prime_count_odd_iff (m : ℕ) :
    r Nat.Prime (2 * m) % 2 = 1 ↔ Nat.Prime m := by
  rw [count_two_mul_mod_two]; by_cases h : Nat.Prime m <;> simp [h]

/-! Vacuity checks: the hypotheses hold in concrete instances. -/

/-- `ε(a) = a - N/2` style sign at `N = 10` satisfies the antisymmetry hypothesis. -/
example : ∀ a ≤ 10, ((5 : ℤ) - ((10 - a : ℕ) : ℤ)) = -((5 : ℤ) - (a : ℤ)) := by
  intro a ha; push_cast [ha]; ring

/-- `16 = 2·8`, 8 not prime: the count is even, though `16 = 3 + 13`. -/
example : r Nat.Prime (2 * 8) % 2 = 0 := by
  rw [count_two_mul_mod_two]; norm_num

/-- `10 = 2·5`, 5 prime: the count is odd. -/
example : r Nat.Prime (2 * 5) % 2 = 1 := (prime_count_odd_iff 5).mpr (by norm_num)

end LeanLab.Routes.R0036
