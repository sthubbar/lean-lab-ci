/-
Jia 1996 page 283 display 58, with the page 278 linear sieve comparison and page 253 Lemma 17.
Source https://doi.org/10.4064/aa-77-3-207-287.
Split of Decomp578a.pair_sieve_transfer into a sieve reduction LEAF and a
dyadic block union LEAF for Lemma 17. Both remain OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp565c

namespace LeanLab.Languasco2004.Feed578aPair
open Finset Real Decomp279a Decomp316a Source565 Decomp565c
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Display 58 support: a pointwise reduction with slack 0.00000004 times the scale leaves
only the block error above 0.00000001 times the scale on the exceptional set. -/
theorem count_transfer (s : Finset ℕ) (E sc G : ℕ → ℝ)
    (h : ∀ n ∈ s, E n ≤ 0.00000004 * sc n + G n) :
    ((s.filter (fun n => 0.00000005 * sc n < E n)).card : ℝ) ≤
      ((s.filter (fun n => 0.00000001 * sc n < G n)).card : ℝ) := by
  exact_mod_cast card_le_card (by
    intro n hn
    obtain ⟨hn, hbad⟩ := mem_filter.mp hn
    refine mem_filter.mpr ⟨hn, ?_⟩
    have := h n hn
    linarith)

/-- LEAF: Jia page 283 display 58 with the page 278 linear sieve comparison, the reduction of the pair transfer to Lemma 17 remainders, HARD.
For small epsilon, the fundamental lemma sieve weights of level Y to 19/36 divided by pq at
the cutoff Y to delta, combined with the pairs of pairDomain true, give bounded weights on
moduli m equal to p q d coprime to n. The local factor comparison of the A and B main terms
produces C of n over log N. Pointwise for every n of the basic interval, the pair transfer
error is at most 0.00000004 times the scale plus the sum of the absolute Lemma 17 remainders
over at most K log N dyadic blocks of moduli between 1 and Y to 19/36. -/
theorem pair_sieve_reduction :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ (K : ℝ) (M : ℕ → ℝ → ℝ) (a : ℕ → ℝ → ℕ → ℝ),
      (∀ j : ℕ, ∀ N : ℝ, 2 ≤ N → 1 ≤ M j N ∧ M j N ≤ (localization N ε) ^ (19 / 36 : ℝ)) ∧
      (∀ j : ℕ, ∀ N : ℝ, ∀ m : ℕ, |a j N m| ≤ 1) ∧
      ∃ T : ℝ, ∀ N : ℝ, T ≤ N → ∀ n ∈ window N ε,
        |pairMass false true N (localization N ε) n ((localization N ε) ^ delta ε) -
            singular n / log N * pairMass true true N (localization N ε) n ((localization N ε) ^ delta ε)| ≤
          0.00000004 * scale N (localization N ε) n +
          ∑ j ∈ range ⌈K * log N⌉₊,
            |progressionRemainder N (localization N ε) (M j N) n (a j N)| := by sorry

/-- LEAF: Jia page 253 Lemma 17 summed over at most K log N dyadic blocks with constants uniform in the block data, HARD.
Lemma 17 holds with implicit constants depending only on epsilon and B, so a union over
K log N blocks at exponent B plus one, together with C of n at least one for even n and
log Y at most log N, gives this exceptional estimate at threshold 0.00000001 times the scale.
The sealed Decomp565c.lemma17_progression_input lets its constants depend on M and the
weights, so it does not yield this union directly. -/
theorem lemma17_blocks_uniform :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∀ (K : ℝ) (M : ℕ → ℝ → ℝ) (a : ℕ → ℝ → ℕ → ℝ),
      (∀ j : ℕ, ∀ N : ℝ, 2 ≤ N → 1 ≤ M j N ∧ M j N ≤ (localization N ε) ^ (19 / 36 : ℝ)) →
      (∀ j : ℕ, ∀ N : ℝ, ∀ m : ℕ, |a j N m| ≤ 1) →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.00000001 * scale N (localization N ε) n <
          ∑ j ∈ range ⌈K * log N⌉₊,
            |progressionRemainder N (localization N ε) (M j N) n (a j N)|)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by sorry

/-- Jia page 283 display 58: exact type of Decomp578a.pair_sieve_transfer.
CONDITIONAL ON the two LEAFs pair_sieve_reduction and lemma17_blocks_uniform.
The supplied Lemma 17 hypothesis is carried but not used, see lemma17_blocks_uniform. -/
theorem pair_sieve_transfer_from_leaves (h17 : type_of% Decomp565c.lemma17_progression_input) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        0.00000005 * scale N (localization N ε) n <
          |pairMass false true N (localization N ε) n ((localization N ε) ^ delta ε) -
            singular n / log N * pairMass true true N (localization N ε) n ((localization N ε) ^ delta ε)|)).card : ℝ) ≤
      C * windowLength N ε / Real.log N ^ B := by
  obtain ⟨e₁, he₁, hred⟩ := pair_sieve_reduction
  obtain ⟨e₂, he₂, hblk⟩ := lemma17_blocks_uniform
  refine ⟨min e₁ e₂, lt_min he₁ he₂, ?_⟩
  intro ε B hε hεe hB
  obtain ⟨K, M, a, hM, ha, T, hT⟩ := hred ε hε (hεe.trans_le (min_le_left _ _))
  obtain ⟨C, N₀, hC⟩ := hblk ε B hε (hεe.trans_le (min_le_right _ _)) hB K M a hM ha
  refine ⟨C, max N₀ T, ?_⟩
  intro N hN
  refine (count_transfer _ _ _ _ (hT N ((le_max_right _ _).trans hN))).trans ?_
  exact hC N ((le_max_left _ _).trans hN)

#print axioms count_transfer
#print axioms pair_sieve_reduction
#print axioms lemma17_blocks_uniform
#print axioms pair_sieve_transfer_from_leaves
end
end LeanLab.Languasco2004.Feed578aPair
