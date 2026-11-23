import LeanLab.ChenDoubleSieve.Feed1122_Decomp315b_lower_F4

/-!
Feed split of `lower_F5` in `Decomp315b`, Wu 2004 Section 10, page 39, equation 10.5.
Source: https://arxiv.org/pdf/0705.1652, pages 38 to 42.
Same scheme as `lower_F4`: linear sieve on each `A_{pq}` at level `N^{1/2}/(pq)`,
then prime pair sum to double integral, with the shared Mertens main term.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task315.Feed1122F0
open Task275
open Wu41 (S PS)
open Wu08Sum (P2 P4)
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The pair weight sum of the F5 term of equation 10.5, over
`N^{κ₁} ≤ p < N^{κ₂} ≤ q < N^{1/2 - 2κ₁}/p`. -/
def pairSum5 (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ q ∈ P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ kappa2 ∧
      (N : ℝ) ^ kappa2 ≤ q ∧ (q : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / p),
    f ((1 / 2 - Real.log q.1 / Real.log N - Real.log q.2 / Real.log N) / kappa1) /
      (((q.1 : ℝ) - 1) * ((q.2 : ℝ) - 1))

/-- LEAF: Wu 2004 page 39, proof of equation 10.5 for F5, the linear sieve lower bound applied
to each `A_{pq}` at level `N^{1/2}/(pq)` and sifting limit `N^{κ₁}`, summed over the pairs,
remainders by Bombieri Vinogradov. Class HARD. -/
theorem sieve_lower5 (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ e : ℝ, 0 < e → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      mainXV N * pairSum5 f N - e * Θ N ≤ sieveTerms N 5 := by
  sorry

/-- LEAF: Wu 2004 page 39, equation 10.5 main term for F5, the prime pair sum tends to
`∫_{κ₁}^{κ₂} ∫_{κ₂}^{1/2 - 2κ₁ - t} f((1/2 - t - u)/κ₁) du/u dt/t`, by the prime number
theorem with partial summation and continuity of `f`. Class MEDIUM. -/
theorem pair_sum5_limit (F f : ℝ → ℝ) (h : IsLinearSieve F f) :
    ∀ e : ℝ, 0 < e → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      |pairSum5 f N - ∫ t in kappa1..kappa2,
        (∫ u in kappa2..(1 / 2 - 2 * kappa1 - t), f ((1 / 2 - t - u) / kappa1) / u) / t| ≤ e := by
  sorry

theorem lower_F5_of_leaves (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 5 - ε) * Θ N ≤ sieveTerms N 5 := by
  have hI : integralTerms F f ω 5 = 2 / (kappa1 * exp eulerMascheroniConstant) *
      ∫ t in kappa1..kappa2, (∫ u in kappa2..(1 / 2 - 2 * kappa1 - t),
        f ((1 / 2 - t - u) / kappa1) / u) / t := rfl
  rw [hI]
  exact eventual_prod (fun N => sieveTerms N 5) mainXV (pairSum5 f) _ _
    (by unfold kappa1; positivity) (sieve_lower5 F f ω h hω) mertens_main_term
    (pair_sum5_limit F f h)

end LeanLab.ChenDoubleSieve.Task315.Feed1122F0
