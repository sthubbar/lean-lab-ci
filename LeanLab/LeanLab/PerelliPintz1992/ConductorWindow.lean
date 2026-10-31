/-
P0070 Section 6, page 367, equation 37 from the Farey window count 21.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.ConductorCount
import LeanLab.PerelliPintz1992.FareyWindow

namespace LeanLab.PerelliPintz1992.Section6
open Real Finset
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The moduli of a finite family of reduced Farey centres. -/
def fareyWindowModuli (F : Finset ℚ) : Finset ℕ+ :=
  F.image (fun x => ⟨x.den, x.pos⟩)

/-- Equation 37 for every finite meeting Farey family, uniformly in real ξ. -/
theorem farey_window_conductors (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ F : Finset ℚ, ∀ M : ℕ, 1 ≤ M → ∀ Q H ξ : ℝ,
      (M : ℝ) ≤ Q → 0 < H →
      (∀ x ∈ F, M ≤ x.den ∧ x.den ≤ 2 * M) →
      (∀ x ∈ F, ∃ α : ℝ,
        |(x : ℝ) - α| ≤ 1 / ((x.den : ℝ) * Q) ∧ |α - ξ| ≤ 1 / H) →
      ((characterConductors (fareyWindowModuli F)).card : ℝ) ≤
        K * ((M : ℝ) ^ 2 / H + 1) * (M : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := characterConductors_card_le_rpow ε hε
  refine ⟨9 * C * (2 : ℝ) ^ ε, by positivity, fun F M hM Q H ξ hMQ hH hden hmeet => ?_⟩
  have hmod : ∀ q ∈ fareyWindowModuli F, (q : ℕ) ≤ 2 * M := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    exact (hden x hx).2
  have hc := hbound (2 * M) (fareyWindowModuli F) hmod
  have hmodcard : ((fareyWindowModuli F).card : ℝ) ≤ (F.card : ℝ) := by
    exact_mod_cast (show (fareyWindowModuli F).card ≤ F.card from Finset.card_image_le)
  have hwindow := hmodcard.trans (farey_arcs_card_le F M hM Q H ξ hMQ hH hden hmeet)
  have hpow : (((2 * M : ℕ) : ℝ) ^ ε) = (2 : ℝ) ^ ε * (M : ℝ) ^ ε := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg M)]
  calc
    ((characterConductors (fareyWindowModuli F)).card : ℝ) ≤
        C * (fareyWindowModuli F).card * ((2 * M : ℕ) : ℝ) ^ ε := hc
    _ ≤ C * (9 * ((M : ℝ) ^ 2 / H + 1)) * ((2 * M : ℕ) : ℝ) ^ ε := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg _) ε)
      exact mul_le_mul_of_nonneg_left hwindow hC.le
    _ = (9 * C * (2 : ℝ) ^ ε) * ((M : ℝ) ^ 2 / H + 1) * (M : ℝ) ^ ε := by
      rw [hpow]
      ring

#print axioms farey_window_conductors

end
end LeanLab.PerelliPintz1992.Section6
