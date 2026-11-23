/-
P0076, Section 4, page 15, the first inequality of the display after display 4.3.
G_1 of z is at least a constant times the product over w < p at most z of the inverse of 1 - omega p / p.
PROVED: the assembly of G1LowerSplit.lean with its two LEAFs closed by G1TailExpansion.lean
and RankinTailSplit.lean and the proved Mertens level change.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.G1TailExpansion
import LeanLab.Teravainen2016.RankinTailSplit

open Finset Real
open scoped Classical

namespace LeanLab.Teravainen2016

/-- The statement of leaf_G1_ge_euler_product in NormalizationSplit.lean, PROVED:
the assembly of leaf_G1_ge_euler_product_of_leaves with G1_ge_product_sub_tail_proved and
rankin_tail_of_leaves in place of its two LEAFs. Selberg sieve lower bound of page 15. -/
theorem G1_ge_euler_product_proved :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ w : ℕ, wBig ≤ w → ∀ z : ℝ, 1 ≤ z →
      c₀ * ∏ p ∈ (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z),
          (1 - (envelopingOmega w p : ℝ) / p)⁻¹ ≤ envelopingG w 1 z := by
  obtain ⟨K, hK, HT⟩ := rankin_tail_of_leaves
  obtain ⟨C, hC, HC⟩ := euler_product_level_change K hK
  refine ⟨1 / (2 * C), by positivity, ?_⟩
  intro w hw z hz
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hy1 : 1 ≤ z ^ (1 / K) := Real.one_le_rpow hz (by positivity)
  have hyz : z ^ (1 / K) ≤ z := by
    calc z ^ (1 / K) ≤ z ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hz (by rw [div_le_one hK0]; exact hK)
      _ = z := Real.rpow_one z
  have hA := G1_ge_product_sub_tail_proved w hw (z ^ (1 / K)) z hy1 hyz
  have hT := HT w hw z hz
  have hCz := HC w hw z hz
  set Ey := ∏ p ∈ (range (⌊z ^ (1 / K)⌋₊ + 1)).filter
    (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z ^ (1 / K)), (1 - (envelopingOmega w p : ℝ) / p)⁻¹
  set Ez := ∏ p ∈ (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ w < p ∧ (p : ℝ) ≤ z),
    (1 - (envelopingOmega w p : ℝ) / p)⁻¹
  have h1 : 1 / (2 * C) * Ez ≤ 1 / (2 * C) * (C * Ey) :=
    mul_le_mul_of_nonneg_left hCz (by positivity)
  have h2 : 1 / (2 * C) * (C * Ey) = (1 / 2) * Ey := by field_simp
  linarith


end LeanLab.Teravainen2016
