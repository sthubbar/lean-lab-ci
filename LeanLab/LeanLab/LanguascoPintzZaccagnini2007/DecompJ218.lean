import LeanLab.LanguascoPintzZaccagnini2007.Decomp131

namespace LeanLab.LPZ2007

open Finset Real Filter MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- LEAF. Page 8 display 25 and Corollary 4.2.
For n in J_1(X), the major arcs contribution R_M(n) is bounded by n S(n). -/
theorem major_arcs_j1_131 (η : ℝ) (hη : 0 < η) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ, AdmissibleP131 X P →
      ∀ N ∈ evenJ131 X,
        |majorContribution131 1 X N P - (N : ℝ) * Sing N| ≤ η * (N : ℝ) * Sing N := by
  sorry

/-- LEAF. Page 8, Corollary 4.2.
The contribution from n in J_2(X) is small. -/
theorem major_arcs_j2_131 (k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ, AdmissibleP131 X P →
      ∀ N ∈ evenJ131 X,
        |majorContribution131 k X N P - (N : ℝ) * Sing N| ≤ η * (N : ℝ) * Lg X ^ k := by
  sorry

/-- LEAF. Page 8 display 25, combining J_1 and J_2 approximations gives C(k, N). -/
theorem major_arcs_combine131 (k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ, AdmissibleP131 X P →
      ∀ N ∈ evenJ131 X,
        |majorContribution131 k X N P - coefficient131 k N * N * Lg X ^ k| ≤ η * (N : ℝ) * Lg X ^ k := by
  sorry

/-- LEAF. Page 3, an admissible P always exists for large X. -/
theorem admissible_P_exists131 :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∃ P : ℝ, AdmissibleP131 X P := by
  sorry

/-- Assembly of the major arc asymptotic from the decomposition. -/
theorem major_asymptotic131_assembly (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∃ P : ℝ, AdmissibleP131 X P ∧
      ∀ N ∈ evenJ131 X,
        |majorContribution131 k X N P - coefficient131 k N * N * Lg X ^ k| ≤
          ε * N * Lg X ^ k := by
  obtain ⟨X₁, hX₁⟩ := major_arcs_combine131 k hk ε hε
  obtain ⟨X₂, hX₂⟩ := admissible_P_exists131
  refine ⟨max X₁ X₂, fun X hX => ?_⟩
  have hx1 : X₁ ≤ X := by omega
  have hx2 : X₂ ≤ X := by omega
  obtain ⟨P, hP⟩ := hX₂ X hx2
  refine ⟨P, hP, fun N hN => ?_⟩
  exact hX₁ X hx1 P hP N hN

end

end LeanLab.LPZ2007
