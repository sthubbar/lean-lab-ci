import LeanLab.ChenDoubleSieve.Decomp275b
import LeanLab.ChenDoubleSieve.Feed1122_S120_main0Pi_split
import LeanLab.ChenDoubleSieve.Section3
import LeanLab.BS2022GRH.PortedMertens

/-!
Feed split of `main0_lower` in Decomp348a, Wu 2004 page 38 before equation 10.2.
Source: https://arxiv.org/pdf/0705.1652, pages 6, 38 and 39, Lemmas 2.2 and 2.3.
The parent's main term uses N over log N. The paper applies the linear sieve,
Lemma 2.2, with the Bombieri Vinogradov input, Lemma 2.3, to the sequence of
N minus p with total size pi of N, and only then replaces pi of N.
This file splits the parent into the sieve step at size pi of N and the
prime number theorem replacement.
This file cannot import Decomp348a, so `main0`, `lowerDensity` and `lowerLevel`
are written out verbatim.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Feed1122.Decomp348a
open LeanLab.ChenDoubleSieve.Task275
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

/-- LEAF: Wu 2004 page 38, application of Lemma 2.2, the linear sieve lower bound
with sifting function f at level N to the half over log N to the B, together with
Lemma 2.3, the Bombieri Vinogradov bound for the remainder sum, to the sequence of
N minus p of size pi of N. Main term written with `Nat.primeCounting N`. HARD. -/
theorem main0Pi_lower (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        (Nat.primeCounting N : ℝ) *
            (∏ p ∈ Wu41.PS N 0 ((N : ℝ) ^ kappa1), (1 - 1 / ((p : ℝ) - 1))) *
            f (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (1 : ℕ)) /
              log ((N : ℝ) ^ kappa1))
          - η * Θ N ≤ sieveTerms N 0 :=
  LeanLab.ChenDoubleSieve.Feed1122.S120.main0Pi_lower_of_leaves F f h

/-- LEAF: Wu 2004 page 38, the replacement of pi of N by N over log N in the main
term, by the prime number theorem together with the Mertens bound on the Euler
product of order one over log N, so the difference is little o of Theta N. MEDIUM. -/
theorem main0_compare (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∀ B : ℝ, 0 < B → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        |(N : ℝ) / log N *
            (∏ p ∈ Wu41.PS N 0 ((N : ℝ) ^ kappa1), (1 - 1 / ((p : ℝ) - 1))) *
            f (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (1 : ℕ)) /
              log ((N : ℝ) ^ kappa1))
          - (Nat.primeCounting N : ℝ) *
            (∏ p ∈ Wu41.PS N 0 ((N : ℝ) ^ kappa1), (1 - 1 / ((p : ℝ) - 1))) *
            f (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (1 : ℕ)) /
              log ((N : ℝ) ^ kappa1))| ≤ η * Θ N := by
  sorry

/-- The parent statement of `main0_lower`, with `main0` unfolded, from the leaves. -/
theorem main0_lower_of_leaves (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        (N : ℝ) / log N *
            (∏ p ∈ Wu41.PS N 0 ((N : ℝ) ^ kappa1), (1 - 1 / ((p : ℝ) - 1))) *
            f (log (((N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B) / (1 : ℕ)) /
              log ((N : ℝ) ^ kappa1))
          - η * Θ N ≤ sieveTerms N 0 :=
  lower_of_compare (fun N => sieveTerms N 0) _ _ (main0Pi_lower F f h) (main0_compare F f h)

end LeanLab.ChenDoubleSieve.Feed1122.Decomp348a
