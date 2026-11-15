import LeanLab.Teravainen2016.MainInputs

namespace LeanLab.Teravainen2016

open Finset
open scoped Classical

/-- LEAF. The weighted sieve step gives a positive mass coefficient for each fixed parameter
family and all sufficiently large scales. -/
theorem leaf_weighted_prime_mass
    (Cc J w : ℕ) (hJ : 5 ≤ J) (hw : wBig ≤ w) (hCc : (Cc : ℝ) ^ 20 ≤ w) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ χ : ℤ → ℝ,
      (∀ n, 0 ≤ χ n) → FourierComplexityLE χ Cc →
      ∀ b : ℤ, 0 ≤ b → b < WW J w → Amenable (WW J w) b →
      ∀ N : ℕ, N₀ ≤ N → ∀ t : ℤ,
        (N : ℝ) / 3 < t → (t : ℝ) < 2 * N / 3 →
        δ * (∑ n ∈ dyad N, χ (t - n)) - N / (w : ℝ) ^ ((1 : ℝ) / 3)
          ≤ ∑ n ∈ dyad N, fW (WW J w) b N n * χ (t - n) := by
  sorry

/-- LEAF. The uniformity step supplies one positive coefficient that works below every
mass coefficient furnished by the weighted sieve for an admissible parameter family. -/
theorem leaf_uniform_mass_coefficient :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ Cc J w δ : ℕ → ℝ, 5 ≤ J → wBig ≤ w → (Cc : ℝ) ^ 20 ≤ w → 0 < δ →
      (∀ χ : ℤ → ℝ, (∀ n, 0 ≤ χ n) → FourierComplexityLE χ Cc →
        ∀ b : ℤ, 0 ≤ b → b < WW J w → Amenable (WW J w) b →
        ∀ N : ℕ, ∀ t : ℤ, (N : ℝ) / 3 < t → (t : ℝ) < 2 * N / 3 →
          δ * (∑ n ∈ dyad N, χ (t - n)) - N / (w : ℝ) ^ ((1 : ℝ) / 3)
            ≤ ∑ n ∈ dyad N, fW (WW J w) b N n * χ (t - n)) →
      δ₀ ≤ δ := by
  sorry

/-- LEAF. The scale parameter used in the error term is strictly positive. -/
theorem leaf_wBig_positive : 0 < wBig := by
  sorry

/-- The weighted prime distribution input on page 9, assembled from the local weighted sieve
mass estimate and its uniform mass coefficient. -/
theorem paper_weighted_prime_input_F556 : Prop32 := by
  unfold Prop32 Prop32On
  obtain ⟨δ₀, hδ₀, hunif⟩ := leaf_uniform_mass_coefficient
  refine ⟨δ₀, 1 / δ₀, hδ₀, div_pos (by norm_num) hδ₀, ?_⟩
  intro Cc J w hJ hw hCc
  obtain ⟨δ, hδ, N₀, hN₀⟩ :=
    leaf_weighted_prime_mass Cc J w hJ hw hCc
  refine ⟨N₀, ?_⟩
  intro χ hχ hχc b hb hbW hAmenable N hN t ht₁ ht₂
  have hmass := hunif Cc J w δ hJ hw hCc hδ
    (fun χ hχ hχc b hb hbW hAmenable N t ht₁ ht₂ => by
      exact hN₀ χ hχ hχc b hb hbW hAmenable N hN t ht₁ ht₂)
  have hsum : 0 ≤ ∑ n ∈ dyad N, χ (t - n) := by
    apply Finset.sum_nonneg
    intro n hn
    exact hχ (t - n)
  have hwpos : 0 < (w : ℝ) := by
    have hbig := leaf_wBig_positive
    unfold wBig at hbig
    have : 0 < (w : ℝ) := by linarith
    exact this
  have hrpow : 0 < (w : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hwpos _
  have herror : 0 ≤ N / (w : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hmain := hN₀ χ hχ hχc b hb hbW hAmenable N hN t ht₁ ht₂
  have hscale : δ₀ * (∑ n ∈ dyad N, χ (t - n)) ≤
      δ * (∑ n ∈ dyad N, χ (t - n)) :=
    mul_le_mul_of_nonneg_right hmass hsum
  have herror_scaled :
      δ₀ * (1 / δ₀ * (N / (w : ℝ) ^ ((1 : ℝ) / 3))) =
        N / (w : ℝ) ^ ((1 : ℝ) / 3) := by
    field_simp
  calc
    δ₀ * (∑ n ∈ dyad N, χ (t - n) - 1 / δ₀ * (N / (w : ℝ) ^ ((1 : ℝ) / 3)))
        = δ₀ * (∑ n ∈ dyad N, χ (t - n)) -
            δ₀ * (1 / δ₀ * (N / (w : ℝ) ^ ((1 : ℝ) / 3))) := by ring
    _ = δ₀ * (∑ n ∈ dyad N, χ (t - n)) - N / (w : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [herror_scaled]
    _ ≤ δ * (∑ n ∈ dyad N, χ (t - n)) - N / (w : ℝ) ^ ((1 : ℝ) / 3) := by
      linarith
    _ ≤ ∑ n ∈ dyad N, fW (WW J w) b N n * χ (t - n) := hmain

end LeanLab.Teravainen2016
