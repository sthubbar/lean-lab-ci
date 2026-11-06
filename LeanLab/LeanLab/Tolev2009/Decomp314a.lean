/-
AI wrote this Lean code. Codex task314. Re-cut by U-1626.
Binary Goldbach is open.
Source: Halupczok 2008 pages 7 to 11, the expansion into O1, O2 and O3.
The definitions and exact expansions moved unchanged to Base314a. The three remainder
means below keep their statements and are now supplied by Decomp346a, b and c.
-/
import LeanLab.Tolev2009.Base314a
import LeanLab.Tolev2009.Decomp346a
import LeanLab.Tolev2009.Decomp346b
import LeanLab.Tolev2009.Decomp346c

open Finset Real MeasureTheory
namespace LeanLab.Tolev2009.Decomp314a
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Decomp286a

/-- Halupczok page 9, the O1 sum after one progression replacement.
Tolev 1999 pages 77 to 78 and 81 to 82 display 49.
Only terms linear in the exact prime progression remainder occur.
Statement unchanged by U-1626, proof is Decomp346a.linear_remainder_mean. -/
theorem linear_remainder_mean :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => errorTerm 1 (Qof A N) (τof A N) k l N)
            lam l₃ (10 ^ 4 * A) N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) :=
  Decomp346a.linear_remainder_mean

/-- Halupczok pages 9 to 10, the O2 sum with two progression errors.
Tolev 1999 pages 77 to 78 and 81 to 82 display 49.
Statement unchanged by U-1626, proof is Decomp346b.quadratic_remainder_mean. -/
theorem quadratic_remainder_mean :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => errorTerm 2 (Qof A N) (τof A N) k l N)
            lam l₃ (10 ^ 4 * A) N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) :=
  Decomp346b.quadratic_remainder_mean

/-- Halupczok pages 10 to 11, the O3 sum with three progression errors.
Tolev 1999 pages 77 to 78 and 81 to 82 display 49.
Statement unchanged by U-1626, proof is Decomp346c.cubic_remainder_mean. -/
theorem cubic_remainder_mean :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => errorTerm 3 (Qof A N) (τof A N) k l N)
            lam l₃ (10 ^ 4 * A) N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) :=
  Decomp346c.cubic_remainder_mean

/-- Exact sealed progression replacement statement.
Assembled from the three remainder means in this file. -/
theorem progression_replacement :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => RM (Qof A N) (τof A N) k l N -
            model (Qof A N) (τof A N) k l N) lam l₃ (10 ^ 4 * A) N ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA l₃ hl₃
  obtain ⟨Ng, hg⟩ := rational_arc_expansion A hA
  obtain ⟨C₁, N₁, h₁⟩ := linear_remainder_mean A hA l₃ hl₃
  obtain ⟨C₂, N₂, h₂⟩ := quadratic_remainder_mean A hA l₃ hl₃
  obtain ⟨C₃, N₃, h₃⟩ := cubic_remainder_mean A hA l₃ hl₃
  refine ⟨C₁ + C₂ + C₃, max Ng (max N₁ (max N₂ N₃)), ?_⟩
  intro lam hlam N hodd hN
  have hNg : Ng ≤ N := (le_max_left _ _).trans hN
  have hNs := (le_max_right _ _).trans hN
  have hN₁ := (le_max_left _ _).trans hNs
  have hNs' := (le_max_right _ _).trans hNs
  have hN₂ := (le_max_left _ _).trans hNs'
  have hN₃ := (le_max_right _ _).trans hNs'
  simp_rw [hg N hNg]
  have hs := EF_add_le
    (fun k l => errorTerm 1 (Qof A N) (τof A N) k l N +
      errorTerm 2 (Qof A N) (τof A N) k l N)
    (fun k l => errorTerm 3 (Qof A N) (τof A N) k l N) lam l₃ (10 ^ 4 * A) N
  have ht := EF_add_le
    (fun k l => errorTerm 1 (Qof A N) (τof A N) k l N)
    (fun k l => errorTerm 2 (Qof A N) (τof A N) k l N) lam l₃ (10 ^ 4 * A) N
  have hb₁ := h₁ lam hlam N hodd hN₁
  have hb₂ := h₂ lam hlam N hodd hN₂
  have hb₃ := h₃ lam hlam N hodd hN₃
  nlinarith

end LeanLab.Tolev2009.Decomp314a
