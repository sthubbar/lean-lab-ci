import LeanLab.ExceptionalSet.Counting385
import LeanLab.ExceptionalSet.PrimePowers385

/-!
The clean implication from the even weighted mean square to the exceptional set bound.
Source: P0029 page 13 display 3.8 and the following calculation.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.BG2026.Supply385

open Finset Real

/-- Prime power control makes the weighted error large at every sufficiently large
Goldbach exception. Source: P0029 page 13 following display 3.8. -/
theorem error_large_at_exception :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n → ¬ IsGoldbachSum n →
      C0 * (n : ℝ) ≤ |error n| := by
  obtain ⟨N₀, hN₀, hsmall⟩ := prime_power_eventually_small
  refine ⟨N₀, hN₀, fun n hn hbad => ?_⟩
  have hr := hsmall n hn hbad
  have hsing := mul_le_mul_of_nonneg_right (Sing_ge n) (Nat.cast_nonneg (α := ℝ) n)
  have herr : error n ≤ -(C0 * (n : ℝ)) := by dsimp [error]; nlinarith
  exact le_trans (by linarith) (neg_le_abs (error n))

/-- A positive exponent even error energy bound gives the corresponding exceptional set bound.
Source: P0029 page 13 after display 3.8, with dyadic summation.
CONDITIONAL ON the explicit even error energy estimate. -/
theorem powerBound_of_even_energy {θ : ℝ} (hθ : 0 < θ)
    (henergy : ∃ C : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ n ∈ (range (X + 1)).filter Even, (error n) ^ 2 ≤ C * (X : ℝ) ^ (θ + 2)) :
    PowerBound θ := by
  obtain ⟨C, X₀, hmean⟩ := henergy
  obtain ⟨N₀, hN₀, hlarge⟩ := error_large_at_exception
  apply MV.powerBound_of_window (θ := θ) (C := C / (C0 / 2) ^ 2)
    (X0 := max X₀ (2 * N₀)) hθ
  intro X hX
  have hXX₀ : X₀ ≤ X := (le_max_left _ _).trans hX
  have hXN₀ : 2 * N₀ ≤ X := (le_max_right _ _).trans hX
  have hX1 : 1 ≤ X := by omega
  apply window_from_energy hX1 (show 0 < C0 / 2 by exact div_pos C0_pos (by norm_num))
  · intro n hn _ hbad
    have hbounds := mem_Icc.mp hn
    have hnN₀ : N₀ ≤ n := by omega
    have hhalf : (X : ℝ) / 2 ≤ n := by
      have : X ≤ 2 * n := by omega
      exact (div_le_iff₀ (by norm_num)).mpr (by exact_mod_cast (by omega : X ≤ n * 2))
    calc C0 / 2 * (X : ℝ) = C0 * ((X : ℝ) / 2) := by ring
      _ ≤ C0 * (n : ℝ) := mul_le_mul_of_nonneg_left hhalf C0_pos.le
      _ ≤ |error n| := hlarge n hnN₀ hbad
  · exact hmean X hXX₀

end LeanLab.ExceptionalSet.BG2026.Supply385
