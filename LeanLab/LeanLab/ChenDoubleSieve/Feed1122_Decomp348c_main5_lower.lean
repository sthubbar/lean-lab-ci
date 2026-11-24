import LeanLab.ChenDoubleSieve.Decomp348a

/-!
Feed split of `main5_lower` in Decomp348c, Wu 2004 page 39 equation 10.5.
Source: https://arxiv.org/pdf/0705.1652, page 39 and Lemmas 2.2 and 2.3.
The parent's main term uses N over log N. The paper applies the linear sieve,
Lemma 2.2, with the Bombieri Vinogradov input, Lemma 2.3, to the sequence of
N minus p with total size pi of N, for each pair of primes, and only then
replaces pi of N. This file splits the parent into the sieve step at size
pi of N and the prime number theorem replacement.
This file cannot import Decomp348c, so `main5` and `lowerSum5` are written out verbatim.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Feed1122.Decomp348c
open LeanLab.ChenDoubleSieve.Task275 LeanLab.ChenDoubleSieve.Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- Generic assembly: a lower bound with a comparison main term and a
uniform comparison of the two main terms give the lower bound for the first. -/
theorem lower_of_compare (u : ℕ → ℝ) (main mainPi : ℝ → ℕ → ℝ)
    (hsieve : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N → mainPi B N - η * Θ N ≤ u N)
    (hcmp : ∀ η : ℝ, 0 < η → ∀ B : ℝ, 0 < B → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N → |main B N - mainPi B N| ≤ η * Θ N) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N → main B N - η * Θ N ≤ u N := by
  intro η hη
  obtain ⟨B, hB, N0, hN0⟩ := hsieve (η / 2) (by positivity)
  obtain ⟨N1, hN1⟩ := hcmp (η / 2) (by positivity) B hB
  refine ⟨B, hB, max N0 N1, fun N hE hN => ?_⟩
  have h1 := hN0 N hE (le_trans (le_max_left _ _) hN)
  have h2 := (abs_le.1 (hN1 N hE (le_trans (le_max_right _ _) hN))).2
  linarith

/-- LEAF: Wu 2004 page 39 equation 10.5, application of Lemma 2.2, the linear sieve
lower bound at level N to the half over log N to the B over p q, to each sifted set
in Upsilon 5, with Lemma 2.3, the Bombieri Vinogradov bound for the remainder sum
over moduli p q d, for the sequence of N minus p of size pi of N.
Main term written with `Nat.primeCounting N`. HARD. -/
theorem main5Pi_lower (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        (Nat.primeCounting N : ℝ) * lowerDensity N *
            (∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ kappa2 ∧
                (N : ℝ) ^ kappa2 ≤ q ∧ (q : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / p),
              f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ))
          - η * Θ N ≤ sieveTerms N 5 := by
  sorry

/-- LEAF: Wu 2004 page 39, the replacement of pi of N by N over log N in the
Upsilon 5 main term, by the prime number theorem, with the Mertens bound on the
Euler product and boundedness of f and of the prime pair sum, so the difference
is little o of Theta N. MEDIUM. -/
theorem main5_compare (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∀ B : ℝ, 0 < B → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        |(N : ℝ) / log N * lowerDensity N *
            (∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ kappa2 ∧
                (N : ℝ) ^ kappa2 ≤ q ∧ (q : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / p),
              f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ))
          - (Nat.primeCounting N : ℝ) * lowerDensity N *
            (∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ kappa2 ∧
                (N : ℝ) ^ kappa2 ≤ q ∧ (q : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / p),
              f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ))| ≤ η * Θ N := by
  sorry

/-- The parent statement of `main5_lower`, with `main5` unfolded, from the leaves. -/
theorem main5_lower_of_leaves (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        (N : ℝ) / log N * lowerDensity N *
            (∑ q ∈ Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ kappa2 ∧
                (N : ℝ) ^ kappa2 ≤ q ∧ (q : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / p),
              f (lowerLevel B N (q.1 * q.2)) / (Nat.totient (q.1 * q.2) : ℝ))
          - η * Θ N ≤ sieveTerms N 5 :=
  lower_of_compare (fun N => sieveTerms N 5) _ _ (main5Pi_lower F f h)
    (main5_compare F f h)

end LeanLab.ChenDoubleSieve.Feed1122.Decomp348c
