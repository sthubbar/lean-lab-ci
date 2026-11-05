/-
An upper range conversion with no large finite Goldbach input.
Ramaré 1995 pp. 701 to 704 gives the additive theorem and the three dyadic blocks.
The paper uses K equal to 39 and sigma equal to 7 divided by 20.
This laboratory adaptation uses K equal to 40 and sigma equal to 3499 divided by 10000.
The resulting slack absorbs the block errors without a positive bottom block.
One extra nearby prime pair reuses an existing HypB certificate.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Ramare1995.Decomp369b

namespace LeanLab.Ramare1995.Count369
open Finset
open LeanLab LeanLab.SchnirelmannConstant LeanLab.Ramare1995.Section9

/-- Extend the low block by the single pair 3 plus 83.
Auxiliary adaptation of hypothesis b on pp. 701 and 704. -/
theorem low_block40 : ∀ i : ℕ, i ≤ 40 → i ∈ 𝒜 := by
  intro i hi
  rcases le_or_gt i 39 with h | h
  · exact Decomp369b.low_block i h
  · have he : i = 40 := by omega
    subst i
    exact ⟨3, 83, Nat.prime_three, by norm_num, rfl⟩

/-- Extend the high block by the pair 367 plus the existing certified prime 2n₀ minus 281.
Auxiliary adaptation of the p. 704 finite block. No new large primality check. -/
theorem high_block40 : ∀ i : ℕ, i ≤ 40 → n₀ + i ∈ 𝒜 := by
  intro i hi
  rcases le_or_gt i 39 with h | h
  · exact HypB.hypBHigh i h
  · have he : i = 40 := by omega
    subst i
    exact ⟨367, 1001999999999999999999999999719, by norm_num,
      HypB.c1001999999999999999999999999719, by unfold n₀; norm_num⟩

/-- Three dyadic blocks suffice at the slightly smaller density 3499 divided by 10000.
CONDITIONAL ON Theorem 2 alone. Unlike the exact paper parameters, no finite Goldbach
hypothesis is needed to supply a positive bottom block. -/
theorem count_lower_slack (h2 : Theorem2) (n : ℕ) (hn : n₀ ≤ n) :
    (3499 / 10000 : ℝ) * n + 1640 ≤ cnt 𝒜 n := by
  classical
  have hE := exp67_le
  have hn' : (125250000000000000000000000000 : ℕ) ≤ n / 2 / 2 := by
    simp only [n₀] at hn
    omega
  have hb : ∀ b : ℕ, n / 2 / 2 ≤ b → Real.exp 67 ≤ (b : ℝ) + 3 := by
    intro b hb
    have ht : ((125250000000000000000000000000 : ℕ) : ℝ) ≤ b := by
      exact_mod_cast hn'.trans hb
    push_cast at ht
    linarith
  have b0 := block h2 n (hb n (by omega))
  have b1 := block h2 (n / 2) (hb _ (by omega))
  have b2 := block h2 (n / 2 / 2) (hb _ le_rfl)
  have s0 := Section9.cnt_split 𝒜 n
  have s1 := Section9.cnt_split 𝒜 (n / 2)
  have s2 := Section9.cnt_split 𝒜 (n / 2 / 2)
  have q1 : (n : ℝ) / 2 - 1 ≤ ((n / 2 : ℕ) : ℝ) := by
    have ht : n ≤ 2 * (n / 2) + 1 := by omega
    have ht' : (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast ht
    linarith
  have q2 : ((n / 2 : ℕ) : ℝ) / 2 - 1 ≤ ((n / 2 / 2 : ℕ) : ℝ) := by
    have ht : n / 2 ≤ 2 * (n / 2 / 2) + 1 := by omega
    have ht' : ((n / 2 : ℕ) : ℝ) ≤ 2 * ((n / 2 / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast ht
    linarith
  have r0 : (cnt 𝒜 n : ℝ) = cnt 𝒜 (n / 2) + #{a ∈ Ioc (n / 2) n | a ∈ 𝒜} := by
    exact_mod_cast s0
  have r1 : (cnt 𝒜 (n / 2) : ℝ) =
      cnt 𝒜 (n / 2 / 2) + #{a ∈ Ioc (n / 2 / 2) (n / 2) | a ∈ 𝒜} := by
    exact_mod_cast s1
  have r2 : (cnt 𝒜 (n / 2 / 2) : ℝ) =
      cnt 𝒜 (n / 2 / 2 / 2) + #{a ∈ Ioc (n / 2 / 2 / 2) (n / 2 / 2) | a ∈ 𝒜} := by
    exact_mod_cast s2
  have hbot : (0 : ℝ) ≤ cnt 𝒜 (n / 2 / 2 / 2) := Nat.cast_nonneg _
  have hnlarge : (20000000 : ℝ) ≤ n := by
    exact_mod_cast (show 20000000 ≤ n by simp only [n₀] at hn; omega)
  linarith

/-- The upper additive conversion now needs only the explicit density theorem.
CONDITIONAL ON Theorem 2. All finite block and additive inputs have proofs. -/
theorem large_even_of_theorem2 (h2 : Theorem2) :
    ∀ N : ℕ, Even N → 6 * n₀ + 18 ≤ N → AtMostPrimes 6 N := by
  intro N hN hle
  obtain ⟨k, hk⟩ := hN
  have h0 : (0 : ℕ) ∈ 𝒜 := ⟨3, 3, Nat.prime_three, Nat.prime_three, rfl⟩
  have hA : ∀ m : ℕ, n₀ ≤ m →
      (3499 / 10000 : ℝ) * m + (40 * (40 + 1) / 2 : ℝ) * ((3 : ℝ) - 1) ≤ cnt 𝒜 m := by
    intro m hm
    convert count_lower_slack h2 m hm using 1 <;> norm_num
  obtain ⟨l, hl, hmem, hs⟩ := Theorem91.theorem91 𝒜 (3499 / 10000) 3 40 n₀
    (by norm_num) h0 hA low_block40 high_block40 (by norm_num) (k - 9) (by omega)
  have hsum := (atMost_of_list l hmem).add (six_mul (3 - l.length))
  rw [hs] at hsum
  have heq : 2 * (k - 9) + 6 * l.length + 6 * (3 - l.length) = N := by omega
  rw [heq] at hsum
  exact hsum.mono (by omega)

/-- The exact upper leaf range, CONDITIONAL ON Theorem 2 alone.
This auxiliary theorem does not repoint or modify the sealed leaf. -/
theorem upper_of_theorem2 (h2 : Theorem2) (n : ℕ) (hn : Even n)
    (h : 4 * 10 ^ 32 < n) : AtMostPrimes 6 n :=
  large_even_of_theorem2 h2 n hn (by simp only [n₀]; omega)

end LeanLab.Ramare1995.Count369
