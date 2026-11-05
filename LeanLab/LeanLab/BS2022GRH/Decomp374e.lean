/- AI wrote this Lean code for CODEX task374. Goldbach is open.
Reuse the existing Rosser weight assembly for journal Theorem 4, p. 1218.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.DecompC169d

namespace LeanLab.BS2022GRH.Decomp374e
open Real Finset Classical ChenThresholdGRH Decomp148f
noncomputable section

/-- Exact statement of Decomp148f.upper_sieve from the existing weight assembly.
CONDITIONAL ON the existing rosser_upper_model leaf. No new analytic input. -/
theorem upper_sieve (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ)
    (g : ℕ → ℕ → ℝ) (z D : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hsupp : ∀ n, n ∉ supp → a n = 0)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P)
    (hg : ∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1) (hz : 2 ≤ z)
    (hprod : ∀ n u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g n p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ≤ D) (hs : log D / log z ≤ 3) :
    sifted supp a P z ≤
      (2 * exp eulerMascheroniConstant / (log D / log z) +
        (1 / 8349 : ℝ) * 112 * exp 2 * hS (log D / log z)) * mainMass supp a P g z +
      errorSum supp a P Q g z D := by
  exact (DecompC169d.linearSieveT4_8349 supp a P Q g z D ha hsupp hP hQ hg
    (by norm_num) (by norm_num) hz hprod).1 hzD hs

end
end LeanLab.BS2022GRH.Decomp374e

#print axioms LeanLab.BS2022GRH.Decomp374e.upper_sieve
