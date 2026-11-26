import LeanLab.ChenDoubleSieve.Decomp315a

/-!
SPLIT of `Task315.first_half`, Wu 2004 equation 9.7, into equation 9.6 and the
Buchstab step on page 36 that gives Delta at least Upsilon 5 plus Delta one.
Source: Wu 2004, https://arxiv.org/pdf/0705.1652, pages 36 and 37.
This file imports Decomp315a because the parent's statement uses `deltaOne`, defined
there; the original is not edited, keeping imports acyclic.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task315.Feed1122FirstHalf
open Task275
open Wu41 (S)
open Wu08Sum (P2)

/-- The third sum in Delta of Wu 2004 page 36, display after 9.6: pairs with
N to the kappa one at most p one below N to the kappa two at most p two below N to the rho,
sifted below p one, at Section 10's rho equal one quarter, which satisfies 3 kappa one plus rho
equal one half by `parameters_admissible`. -/
def pairRho (N : ℕ) : ℝ :=
  let A := primeSequence N
  let y := fun k : ℝ => (N : ℝ) ^ k
  (∑ q ∈ P2 N (fun p q => y kappa1 ≤ p ∧ (p : ℝ) < y kappa2 ∧
      y kappa2 ≤ q ∧ (q : ℝ) < y (1 / 4)), S A (q.1 * q.2) N q.1 : ℕ)

/-- LEAF: Wu 2004 page 36 equation 9.6, which is 9.5, Lemma 9.1 at kappa two and sigma two,
after the Buchstab and switching rewrites of pages 35 and 36, with Delta written as minus the
first and third triple sums plus `pairRho`, and the nonnegative Upsilon 6, 11, 12 dropped;
the error O of N to the one minus kappa two is absorbed into C times N to the eleven twelfths.
The first Delta sum sifts below p one, so its paper modulus N p one equals N here. Class HARD. -/
theorem leaf_eq96 : ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      2 * sieveTerms N 0 - sieveTerms N 1 - sieveTerms N 3 +
        sieveTerms N 4 - 2 * sieveTerms N 7 - sieveTerms N 9 -
        tripleTerms N 0 - tripleTerms N 2 + pairRho N ≤
      2 * (D12 N : ℝ) + C * (N : ℝ) ^ (11 / 12 : ℝ) := by
  have h_main : ∀ (N : ℕ), Even N → 4096 ≤ N →
      2 * sieveTerms N 0 - sieveTerms N 1 - sieveTerms N 3 +
        sieveTerms N 4 - 2 * sieveTerms N 7 - sieveTerms N 9 -
        tripleTerms N 0 - tripleTerms N 2 + pairRho N ≤
      2 * (D12 N : ℝ) + 11 * (N : ℝ) ^ (11 / 12 : ℝ) := by
    sorry
  sorry

/-- LEAF: Wu 2004 page 36, the Buchstab identity step after 9.6: since 3 kappa one plus rho is
one half, N to the rho is at least N to the half minus two kappa one over p one, so
`pairRho` is at least Upsilon 5 minus the second triple sum of Delta one. Class MEDIUM. -/
theorem leaf_buchstab : ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      sieveTerms N 5 - tripleTerms N 1 ≤ pairRho N := by
  have h_main : ∀ (N : ℕ), Even N → 4 ≤ N → sieveTerms N 5 ≤ pairRho N + tripleTerms N 1 := by
    intro N hEven hN
    have h₁ : sieveTerms N 5 = (∑ q ∈ P2 N (fun p q => ((N : ℝ) ^ kappa1 : ℝ) ≤ p ∧ (p : ℝ) < ((N : ℝ) ^ kappa2 : ℝ) ∧ ((N : ℝ) ^ kappa2 : ℝ) ≤ q ∧ (q : ℝ) < ((N : ℝ) ^ (1 / 2 - 2 * kappa1 : ℝ)) / (p : ℝ)), (S (primeSequence N) (q.1 * q.2) N ((N : ℝ) ^ kappa1) : ℕ)) := by sorry
    have h₂ : pairRho N = (∑ q ∈ P2 N (fun p q => ((N : ℝ) ^ kappa1 : ℝ) ≤ p ∧ (p : ℝ) < ((N : ℝ) ^ kappa2 : ℝ) ∧ ((N : ℝ) ^ kappa2 : ℝ) ≤ q ∧ (q : ℝ) < ((N : ℝ) ^ (1 / 4 : ℝ))), (S (primeSequence N) (q.1 * q.2) N (q.1 : ℝ) : ℕ)) := by sorry
    have h₃ : tripleTerms N 1 = (∑ q ∈ primeTriples N (fun p q r => ((N : ℝ) ^ kappa1 : ℝ) ≤ p ∧ (p : ℝ) < q ∧ (q : ℝ) < ((N : ℝ) ^ kappa2 : ℝ) ∧ ((N : ℝ) ^ kappa2 : ℝ) ≤ r ∧ (r : ℝ) < ((N : ℝ) ^ (1 / 2 - 2 * kappa1 : ℝ)) / (q : ℝ)), (S (primeSequence N) (q.1 * q.2.1 * q.2.2) N (q.1 : ℝ) : ℕ)) := by sorry
    sorry
  sorry

/-- The parent `first_half`, exactly as stated in Decomp315a, from the two leaves. -/
theorem first_half_of_leaves : ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      2 * sieveTerms N 0 - sieveTerms N 1 - sieveTerms N 3 +
        sieveTerms N 4 + sieveTerms N 5 - 2 * sieveTerms N 7 -
        sieveTerms N 9 + deltaOne N ≤
      2 * (D12 N : ℝ) + C * (N : ℝ) ^ (11 / 12 : ℝ) := by
  obtain ⟨C, hC, M1, h1⟩ := leaf_eq96
  obtain ⟨M2, h2⟩ := leaf_buchstab
  refine ⟨C, hC, max M1 M2, fun N hN hle => ?_⟩
  have a := h1 N hN (le_trans (le_max_left _ _) hle)
  have b := h2 N hN (le_trans (le_max_right _ _) hle)
  dsimp only [deltaOne]
  linarith

end LeanLab.ChenDoubleSieve.Task315.Feed1122FirstHalf
