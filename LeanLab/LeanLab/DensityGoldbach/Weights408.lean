/-
The explicit mean margins in Shao 1206.6139v2 page 16 and
Alsetri 2505.09648v3 page 14.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.DensityGoldbach.Profiles408

open Finset
open scoped Classical

namespace LeanLab.DensityGoldbach.Weights408

/-- Shao page 15, the strict cutoff in the profile definition.
The natural endpoint is the floor of 2n minus 1 divided by 3. -/
theorem strict_cutoff_iff (n p : ℕ) (hn : 0 < n) :
    3 * p < 2 * n ↔ p ≤ (2 * n - 1) / 3 := by omega

/-- Shao page 16, the equality preceding the lower bound on delta_i.
A positive truncated profile lets one remove the max with zero exactly. -/
theorem profile_sum_of_pos (A : Set ℕ) (W n b : ℕ) (δ : ℝ)
    (hp : 0 < Profiles408.primeProfile A W n δ b) :
    (3 * (W.totient : ℝ) / (2 * n)) *
      (∑ p ∈ (range (n + 1)).filter
        (fun p => p ∈ A ∧ p % W = b % W ∧ 3 * p < 2 * n), Real.log p) =
      Profiles408.primeProfile A W n δ b + δ / 8 := by
  unfold Profiles408.primeProfile at hp ⊢
  have hleft := (lt_max_iff.mp hp).resolve_right (lt_irrefl 0)
  rw [max_eq_left hleft.le]
  ring

/-- Shao page 16 and Alsetri page 14, choosing kappa small enough.
The concrete bound kappa at most delta/100 yields the printed delta/20 margin. -/
theorem profile_mean_margin (δ κ u : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8)
    (hκ : 0 ≤ κ) (hκsmall : κ ≤ δ / 100) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    2 / 3 * u + δ / 20 ≤ 2 / (3 * (1 + 2 * κ)) * (u + δ / 8) := by
  have hden : 0 < 3 * (1 + 2 * κ) := by positivity
  have hκu : κ * u ≤ κ := mul_le_of_le_one_right hκ hu1
  have hκδ : κ * δ ≤ κ / 8 := by
    nlinarith [mul_le_mul_of_nonneg_left hδsmall hκ]
  have he : 2 / (3 * (1 + 2 * κ)) * (u + δ / 8) =
      2 * (u + δ / 8) / (3 * (1 + 2 * κ)) := by ring
  rw [he, le_div_iff₀ hden]
  nlinarith

/-- Shao page 16, the two displays confirming the mean condition 23.
Three profile values summing above 3/2 give a positive common mass margin. -/
theorem three_mass_margins (δ : ℝ) (hδ : 0 < δ) (u mass : Fin 3 → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hsum : 3 / 2 < u 0 + u 1 + u 2)
    (hmass : ∀ i, 2 / 3 * u i + δ / 20 ≤ mass i) :
    (∀ i, δ / 20 ≤ mass i) ∧ δ / 20 ≤ mass 0 + mass 1 + mass 2 - 1 := by
  constructor
  · intro i
    have := hmass i
    have := hu i
    linarith
  · have h0 := hmass 0
    have h1 := hmass 1
    have h2 := hmass 2
    linarith

end LeanLab.DensityGoldbach.Weights408

#print axioms LeanLab.DensityGoldbach.Weights408.strict_cutoff_iff
#print axioms LeanLab.DensityGoldbach.Weights408.profile_sum_of_pos
#print axioms LeanLab.DensityGoldbach.Weights408.profile_mean_margin
#print axioms LeanLab.DensityGoldbach.Weights408.three_mass_margins
