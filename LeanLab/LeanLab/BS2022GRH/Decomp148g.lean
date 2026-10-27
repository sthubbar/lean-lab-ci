/- AI wrote this Lean code for CODEX task148.
Recovered from the recorded write commands. Fresh checks are required.
Journal Theorem 4, lower sieve and exact lab assembly. Goldbach is open. -/
import LeanLab.BS2022GRH.Decomp148f
namespace LeanLab.BS2022GRH.Decomp148g
open Real Finset Classical ChenThresholdGRH Decomp148f
/-- LEAF. Lower half of Theorem 4 p. 1218 on 2 ≤ s ≤ 4.
CITED source is Bordignon, Johnston and Starichkova, arXiv 2207.09452,
Theorem 6 and Table 1. Constants at reciprocal epsilon 6100 apply at 8349.
This is the non-strict sealed lab formulation. -/
theorem lower_sieve (supp : Finset ℕ) (a : ℕ → ℝ) (P : Set ℕ) (Q : Finset ℕ)
    (g : ℕ → ℕ → ℝ) (z D : ℝ)
    (ha : ∀ n, 0 ≤ a n) (hsupp : ∀ n, n ∉ supp → a n = 0)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ↑Q ⊆ P)
    (hg : ∀ n, ∀ p ∈ P, 0 ≤ g n p ∧ g n p < 1) (hz : 2 ≤ z)
    (hprod : ∀ n u, 1 < u → u < z →
      ∏ p ∈ (range ⌈z⌉₊).filter (fun p => p ∈ P ∧ p ∉ Q ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - g n p)⁻¹ ≤ (1 + (1 / 8349 : ℝ)) * (log z / log u))
    (hzD : z ^ 2 ≤ D) (hs : log D / log z ≤ 4) :
    (2 * exp eulerMascheroniConstant * log (log D / log z - 1) / (log D / log z) -
      (1 / 8349 : ℝ) * 114 * exp 2 * hS (log D / log z)) * mainMass supp a P g z -
      errorSum supp a P Q g z D ≤ sifted supp a P z := by
  sorry
/-- Exact selected LinearSieveT4. OPEN through two cited leaves, with no direct sorry. -/
theorem linearSieveT4_8349 : LinearSieveT4 (1 / 8349) 112 114 := by
  intro supp a P Q g z D ha hsupp hP hQ hg _heps _heps63 hz hprod
  exact ⟨fun hzD hs => upper_sieve supp a P Q g z D ha hsupp hP hQ hg hz hprod hzD hs,
    fun hzD hs => lower_sieve supp a P Q g z D ha hsupp hP hQ hg hz hprod hzD hs⟩
end LeanLab.BS2022GRH.Decomp148g
#print axioms LeanLab.BS2022GRH.Decomp148g.lower_sieve
#print axioms LeanLab.BS2022GRH.Decomp148g.linearSieveT4_8349
