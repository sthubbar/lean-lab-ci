/-
Split of Decomp369b.count_lower, CLOUD S106 burst-20261122. The original file is unchanged.
Ramaré 1995, P0008, Section 9 p. 704: hypothesis a of Theorem 9.1 for the set 𝒜.
The existing proof Section9.hypA needs two cited inputs, Theorem 2 and finite Goldbach
through 2 times 10^10. The bottom block of p. 704 needs far less than that: 1600 elements
of 𝒜 in the interval from 1 to n/8 are enough, and they come from a kernel check of even
Goldbach through 3300. So count_lower below is CONDITIONAL ON Theorem 2 alone.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Common.Goldbach
import LeanLab.Ramare1995.Section9

open Finset Real
open scoped Classical

namespace LeanLab.Ramare1995.S106SplitDecomp369b
open LeanLab LeanLab.SchnirelmannConstant LeanLab.Ramare1995.Section9

/-- LEAF: Ramaré 1995 Theorem 2, p. 646, the explicit density of sums of two primes, as used
on p. 704 for the three dyadic blocks: for real X at least exp 67, at least X/5 even integers
in the interval from X to 2X are sums of two primes. The paper proves it in Sections 2 to 8
from Propositions 1 to 4; the lab reduction to two moments is Decomp1526a.theorem2_of_moments,
and Proposition 1 is DecompJ1066.proposition1_leaf. HARD for Codex. -/
theorem theorem2_leaf : Theorem2 := by
  sorry

/-- Even Goldbach through 3300, a kernel computation with the lab checker. -/
theorem evenGoldbachUpTo_3300 : EvenGoldbachUpTo 3300 :=
  allEvenGB_sound 3300 (by decide +kernel)

/-- The bottom block of p. 704 in the small form needed: for c at least 1600, the set 𝒜 has at
least 1600 elements in the interval from 1 to c. The paper cites finite Goldbach here; through
3300 is enough. -/
theorem bottom_small (c : ℕ) (hc : 1600 ≤ c) : 1600 ≤ cnt 𝒜 c := by
  unfold cnt
  have : Icc 1 1600 ⊆ {a ∈ Icc 1 c | a ∈ 𝒜} := by
    intro a ha
    simp only [mem_Icc] at ha
    rw [mem_filter, mem_Icc]
    exact ⟨⟨ha.1, by omega⟩, evenGoldbachUpTo_3300 _ ⟨a + 3, by ring⟩ (by omega) (by omega)⟩
  have h := card_le_card this
  simpa using h

/-- Hypothesis a of Theorem 9.1 for 𝒜, p. 704, CONDITIONAL ON Theorem 2 alone. The proof is
that of Section9.hypA, three dyadic blocks from Theorem 2, with bottom_small in place of the
finite Goldbach input through 2 times 10^10. -/
theorem count_lower_of_theorem2 (h2 : Theorem2) (n : ℕ) (hn : n₀ ≤ n) :
    (7 / 20 : ℝ) * n + 1560 ≤ cnt 𝒜 n := by
  have hE := exp67_le
  have hn' : (125250000000000000000000000000 : ℕ) ≤ n / 2 / 2 := by simp only [n₀] at hn; omega
  have hn8 : 1600 ≤ n / 2 / 2 / 2 := by omega
  have hb : ∀ b : ℕ, n / 2 / 2 ≤ b → exp 67 ≤ (b : ℝ) + 3 := by
    intro b hb
    have : ((125250000000000000000000000000 : ℕ) : ℝ) ≤ b := by exact_mod_cast hn'.trans hb
    push_cast at this; linarith
  have b0 := block h2 n (hb n (by omega))
  have b1 := block h2 (n / 2) (hb _ (by omega))
  have b2 := block h2 (n / 2 / 2) (hb _ le_rfl)
  have s0 := cnt_split 𝒜 n
  have s1 := cnt_split 𝒜 (n / 2)
  have s2 := cnt_split 𝒜 (n / 2 / 2)
  have bot := bottom_small _ hn8
  have q1 : (n : ℝ) / 2 - 1 ≤ ((n / 2 : ℕ) : ℝ) := by
    have : n ≤ 2 * (n / 2) + 1 := by omega
    have : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have q2 : ((n / 2 : ℕ) : ℝ) / 2 - 1 ≤ ((n / 2 / 2 : ℕ) : ℝ) := by
    have : n / 2 ≤ 2 * (n / 2 / 2) + 1 := by omega
    have : ((n / 2 : ℕ) : ℝ) ≤ 2 * ((n / 2 / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast this
    linarith
  have r0 : (cnt 𝒜 n : ℝ) = cnt 𝒜 (n / 2) + #{a ∈ Ioc (n / 2) n | a ∈ 𝒜} := by
    exact_mod_cast s0
  have r1 : (cnt 𝒜 (n / 2) : ℝ) =
      cnt 𝒜 (n / 2 / 2) + #{a ∈ Ioc (n / 2 / 2) (n / 2) | a ∈ 𝒜} := by
    exact_mod_cast s1
  have r2 : (cnt 𝒜 (n / 2 / 2) : ℝ) =
      cnt 𝒜 (n / 2 / 2 / 2) + #{a ∈ Ioc (n / 2 / 2 / 2) (n / 2 / 2) | a ∈ 𝒜} := by
    exact_mod_cast s2
  have rb : (1600 : ℝ) ≤ cnt 𝒜 (n / 2 / 2 / 2) := by exact_mod_cast bot
  linarith

/-- Assembly of the exact statement of Decomp369b.count_lower from theorem2_leaf.
Ramaré 1995 p. 704. No sorry of its own; CONDITIONAL ON theorem2_leaf. -/
theorem count_lower (m : ℕ) (hm : n₀ ≤ m) :
    (7 / 20 : ℝ) * m + 1560 ≤ cnt 𝒜 m :=
  count_lower_of_theorem2 theorem2_leaf m hm

end LeanLab.Ramare1995.S106SplitDecomp369b
