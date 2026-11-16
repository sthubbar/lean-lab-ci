/-
AI wrote the Lean code. CODEX task591.
Source: Song 2020, https://arxiv.org/pdf/2012.06322v1, page 7.
The sealed per u claim is moved here unchanged to avoid an import cycle.
Binary Goldbach is open.
-/
import LeanLab.Song2020.Decomp139

namespace LeanLab.Song2020.SPLIT_lambda_sum_per_h

open LeanLab.Song2020 LeanLab.Song2020.State1562

noncomputable section

/-- LEAF: Song 2020, page 7, the display after "Choosing v = (n/u)^{1/2}": for every
Vaughan parameter u with 1 at most u at most n, n to the minus epsilon times Sigma 1 plus
Sigma 2 plus Sigma 3 is at most six monomials in n, y, u and the absolute value of h.
Published inputs: Dirichlet approximation and the Ramanujan sum splitting, page 5; the
Vaughan identity, Lemma 3.2, page 5; Iwaniec and Kowalski Corollary 8.13 for Sigma 1,
page 6; Graham and Kolesnik Lemma 2.5 for T(R,S), page 6, with Corollary 8.13 for the
inner r sum and Lemma 2.4 for L, page 7. -/
theorem vaughan_per_u :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 → ∀ α : ℝ,
          ∀ h : ℤ, h ≠ 0 → ∀ t : ℝ, ∀ u : ℝ, 1 ≤ u → u ≤ n →
            ‖lambdaSum γ n y α h t‖ ≤ C * (n : ℝ) ^ ε *
              ((n : ℝ) ^ (1 - γ / 4) * |(h : ℝ)| ^ (-(1 : ℝ) / 4) +
                u ^ ((1 : ℝ) / 4) * (n : ℝ) ^ ((3 : ℝ) / 4) +
                u * (|(h : ℝ)| ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (γ / 2 - 1) * y) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((3 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) +
                u ^ (-(1 : ℝ) / 6) * ((n : ℝ) ^ ((γ + 3) / 6) * y ^ ((1 : ℝ) / 3) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 6)) +
                u ^ (-(1 : ℝ) / 4) * ((n : ℝ) ^ ((γ + 1) / 4) * y ^ ((1 : ℝ) / 2) *
                  |(h : ℝ)| ^ ((1 : ℝ) / 4))) := by
  simpa only [lambdaSum, subWindow, Decomp139.lambdaSum, Decomp139.subWindow] using
    Decomp139.vaughan_per_u

end

end LeanLab.Song2020.SPLIT_lambda_sum_per_h

#print axioms LeanLab.Song2020.SPLIT_lambda_sum_per_h.vaughan_per_u
