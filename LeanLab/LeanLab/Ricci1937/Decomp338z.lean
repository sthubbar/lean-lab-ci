import LeanLab.Ricci1937.Decomp338y

/-!
Ricci 1937, saved support supplier for the first two mixed pairs.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Clean supplier of the shifted support for first memoir page 89 case two.
Second memoir pages 113 to 115, formulas 31.3 to 31.5 and their mixed variant. -/
theorem decomp338_mixed_support_5_7_proved :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / ((5 : ℝ) + 1) < δ ∧ δ ≤ 1 / 2 ∧
        1 / ((7 : ℝ) + 1) < δ * (3 / 4 : ℝ) ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          let v := ⌊(t : ℝ) ^ (3 / 4 : ℝ)⌋₊
          let H := decomp338EncodedGap h v t
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ) := by
  have hm := decompJ365_first_four_saved_exponents
  dsimp only at hm
  obtain ⟨δ, κ, hδ0, hκ, hδA, hδB, hsave⟩ := hm.2.1
  norm_num at hδA hδB
  have hδ : 1 / ((5 : ℝ) + 1) < min δ (1 / 2) := lt_min (by norm_num; exact hδA) (by norm_num)
  have hδr : 1 / ((7 : ℝ) + 1) < min δ (1 / 2) * (3 / 4 : ℝ) := by
    have hh : (4 / 3 : ℝ) / (7 + 1) < min δ (1 / 2) := lt_min (by norm_num; exact hδB) (by norm_num)
    norm_num at hh ⊢
    linarith
  have hlog : Real.log (3 / 4 : ℝ) = -Real.log (4 / 3 : ℝ) := by
    rw [show (3 / 4 : ℝ) = (4 / 3 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hτ : 0 ≤ ricciTau 2 := by linarith [decomp338_tau_two_gt]
  have hC : 0 ≤ 1 + 2 * (exp (Real.log (3 / 4 : ℝ) / 2) * ricciTau 2 + 0.001) := by positivity
  apply decomp338_mixed_support_from_parameters 5 7 (3 / 4) (min δ (1 / 2)) κ
    (by norm_num) (by norm_num) (by linarith) hδ (min_le_right _ _) hδr hκ
  apply (mul_le_mul_of_nonneg_right (min_le_left δ (1 / 2)) hC).trans
  rw [hlog]
  convert hsave using 1 <;> ring

/-- Clean supplier of the shifted support for first memoir page 89 case three.
Second memoir pages 113 to 115, formulas 31.3 to 31.5 and their mixed variant. -/
theorem decomp338_mixed_support_4_9_proved :
    ∃ Y₀ : ℕ, 4 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∃ δ κ : ℝ, 1 / ((4 : ℝ) + 1) < δ ∧ δ ≤ 1 / 2 ∧
        1 / ((9 : ℝ) + 1) < δ * (1 / 2 : ℝ) ∧ 0 < κ ∧
        ∃ X : ℕ, ∀ ξ h : ℕ, X ≤ ξ →
          let t := ⌊(ξ : ℝ) ^ δ⌋₊
          let v := ⌊(t : ℝ) ^ (1 / 2 : ℝ)⌋₊
          let H := decomp338EncodedGap h v t
          ∀ S ⊆ Nat.primesLE t, (∀ j ∈ range (t + 1),
            (S.filter (fun p : ℕ => decomp338GreedyCutoff H Y t j < p)).card ≤ 2 * j + 1) →
              ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (ξ : ℝ) ^ (1 - κ) := by
  have hm := decompJ365_first_four_saved_exponents
  dsimp only at hm
  obtain ⟨δ, κ, hδ0, hκ, hδA, hδB, hsave⟩ := hm.2.2.1
  norm_num at hδA hδB
  have hδ : 1 / ((4 : ℝ) + 1) < min δ (1 / 2) := lt_min (by norm_num; exact hδA) (by norm_num)
  have hδr : 1 / ((9 : ℝ) + 1) < min δ (1 / 2) * (1 / 2 : ℝ) := by
    have hh : (2 : ℝ) / (9 + 1) < min δ (1 / 2) := lt_min (by norm_num; exact hδB) (by norm_num)
    norm_num at hh ⊢
    linarith
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log (2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hτ : 0 ≤ ricciTau 2 := by linarith [decomp338_tau_two_gt]
  have hC : 0 ≤ 1 + 2 * (exp (Real.log (1 / 2 : ℝ) / 2) * ricciTau 2 + 0.001) := by positivity
  apply decomp338_mixed_support_from_parameters 4 9 (1 / 2) (min δ (1 / 2)) κ
    (by norm_num) (by norm_num) (by linarith) hδ (min_le_right _ _) hδr hκ
  apply (mul_le_mul_of_nonneg_right (min_le_left δ (1 / 2)) hC).trans
  rw [hlog]
  convert hsave using 1 <;> ring

end
end LeanLab.Ricci1937
