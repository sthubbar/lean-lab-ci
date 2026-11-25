import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.Section3
import LeanLab.BS2022GRH.PortedMertens

/-!
Feed split of `main0Pi_lower` in Feed1122_Decomp348a_main0_lower, Wu 2004 page 38.
Source: https://arxiv.org/pdf/0705.1652, page 6 Lemmas 2.2 and 2.3, page 38 before equation 10.2.
The linear sieve lower bound, Lemma 2.2, is applied to the sequence of N minus p,
p prime at most N, of total size pi of N, with density one over phi of d, sifting
level N to the kappa one and level of distribution N to the half over log N to the B.
It leaves the remainder sum over squarefree d below the level dividing the sifting
product of the absolute values of the count of N minus p divisible by d minus
pi of N over phi of d. Lemma 2.3, the Bombieri Vinogradov theorem, bounds that sum.
The remainder is written inline in both leaves.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Feed1122.S120
open LeanLab.ChenDoubleSieve.Task275
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- LEAF: Wu 2004 page 6 Lemma 2.2, the linear sieve lower bound, applied on page 38
to the sequence of N minus p of size pi of N with sifting level N to the kappa one
and level N to the half over log N to the B. The relative error of the sieve
is absorbed into eta Theta N, and the remainder sum over squarefree d up to the level
dividing the sifting product is kept. Class HARD. -/
theorem linear_sieve_piN (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∀ B : ℝ, 0 < B → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        (Nat.primeCounting N : ℝ) *
            (∏ p ∈ Wu41.PS N 0 ((N : ℝ) ^ kappa1), (1 - 1 / ((p : ℝ) - 1))) *
            f (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (1 : ℕ)) /
              log ((N : ℝ) ^ kappa1))
          - η * Θ N
          - ∑ d ∈ (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B⌋₊).filter
              (fun d => Squarefree d ∧ d ∣ ∏ p ∈ Wu41.PS N 0 ((N : ℝ) ^ kappa1), p),
              |(#((primeSequence N).filter (fun a => d ∣ a)) : ℝ) -
                (Nat.primeCounting N : ℝ) / (d.totient : ℝ)|
          ≤ sieveTerms N 0 := by
  sorry

/-- LEAF: Wu 2004 page 6 Lemma 2.3, the Bombieri Vinogradov theorem, at the level
N to the half over log N to the B on page 38: for B large the remainder sum of the
linear sieve is at most eta Theta N for N large. It rests on the lab's proved
Bombieri Vinogradov theorem in LeanLab.PNTPort. Class MEDIUM. -/
theorem remainder_piN_small :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        ∑ d ∈ (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B⌋₊).filter
            (fun d => Squarefree d ∧ d ∣ ∏ p ∈ Wu41.PS N 0 ((N : ℝ) ^ kappa1), p),
            |(#((primeSequence N).filter (fun a => d ∣ a)) : ℝ) -
              (Nat.primeCounting N : ℝ) / (d.totient : ℝ)|
          ≤ η * Θ N := by
  sorry

/-- Assembly of Wu 2004 page 38: Lemma 2.2 at size pi of N with Lemma 2.3. -/
theorem main0Pi_lower_of_leaves (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        (Nat.primeCounting N : ℝ) *
            (∏ p ∈ Wu41.PS N 0 ((N : ℝ) ^ kappa1), (1 - 1 / ((p : ℝ) - 1))) *
            f (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (1 : ℕ)) /
              log ((N : ℝ) ^ kappa1))
          - η * Θ N ≤ sieveTerms N 0 := by
  intro η hη
  obtain ⟨B, hB, N1, hN1⟩ := remainder_piN_small (η / 2) (by positivity)
  obtain ⟨N0, hN0⟩ := linear_sieve_piN F f h (η / 2) (by positivity) B hB
  refine ⟨B, hB, max N0 N1, fun N hE hN => ?_⟩
  have h1 := hN0 N hE (le_trans (le_max_left _ _) hN)
  have h2 := hN1 N hE (le_trans (le_max_right _ _) hN)
  linarith

end LeanLab.ChenDoubleSieve.Feed1122.S120
