import LeanLab.Song2020.Decomp139

namespace LeanLab.Song2020.DecompJ1132

open LeanLab.Song2020 LeanLab.Song2020.Decomp139
open scoped Classical

noncomputable section

/-- LEAF. Page 4, first half. There exists a coefficient family `a` bounded by `K / |h|`. -/
theorem fourier_coefficients :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ a : ℕ → ℤ → ℂ, ∃ K : ℝ, 1 ≤ K ∧
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) := by
  sorry

/-- LEAF. Pages 4 and 5, S2 bound. The difference `sawSum - truncatedSum` is bounded. -/
theorem fourier_error :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 → ∀ a : ℕ → ℤ → ℂ, ∀ K : ℝ,
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) →
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
          ∀ H : ℕ, 1 ≤ H → ∀ α : ℝ,
            ‖sawSum γ n y α - truncatedSum a H γ n y α‖ ≤
              C * tailBudget γ n y H := by
  sorry

/-- Assembly of the Fourier approximation from the coefficient and error leaves. -/
theorem fourier_approximation :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ a : ℕ → ℤ → ℂ, ∃ K : ℝ, 1 ≤ K ∧
        (∀ H : ℕ, ∀ h : ℤ, h ≠ 0 → ‖a H h‖ ≤ K / |(h : ℝ)|) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
          (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
          ∀ H : ℕ, 1 ≤ H → ∀ α : ℝ,
            ‖sawSum γ n y α - truncatedSum a H γ n y α‖ ≤
              C * tailBudget γ n y H := by
  intro γ hγ hγ1
  obtain ⟨a, K, hK, ha⟩ := fourier_coefficients γ hγ hγ1
  obtain ⟨C, hC, N₀, herr⟩ := fourier_error γ hγ hγ1 a K ha
  exact ⟨a, K, hK, ha, C, hC, N₀, herr⟩

end

end LeanLab.Song2020.DecompJ1132
