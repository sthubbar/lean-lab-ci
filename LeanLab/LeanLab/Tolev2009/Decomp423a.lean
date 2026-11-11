/-
AI wrote this Lean code. Codex task423.
Binary Goldbach is open.
Source: Halupczok 2008 pages 8 to 12 and 18 to 19.
Exact supplies for the three sealed Decomp286a leaves.
Existing proofs are reused without changing the inherited leaf file.
-/
import LeanLab.Tolev2009.MajorArc341
import LeanLab.Tolev2009.Instances355

open Finset Real MeasureTheory
namespace LeanLab.Tolev2009.Decomp423a
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Decomp286a

/-- Exact supply. Halupczok 2008 pages 8 to 11, O1, O2 and O3.
The statement is identical to the sealed leaf. -/
theorem progression_replacement :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => RM (Qof A N) (τof A N) k l N -
            model (Qof A N) (τof A N) k l N) lam l₃ (10 ^ 4 * A) N ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (-A) :=
  MajorArc341.progression_replacement

/-- Exact supply. Halupczok 2008 pages 11 to 12 and 19, e2.
The statement is identical to the sealed leaf. -/
theorem singular_integral_error :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => model (Qof A N) (τof A N) k l N -
            truncatedMain (Qof A N) k l N) lam l₃ (10 ^ 4 * A) N ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (-A) :=
  Decomp355c.singular_integral_error

/-- Exact supply. Halupczok 2008 pages 12 and 18 to 19, e1.
The statement is identical to the sealed leaf. -/
theorem singular_series_tail :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => truncatedMain (Qof A N) k l N -
            M singSeries k l N) lam l₃ (10 ^ 4 * A) N ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (-A) :=
  MajorArc341.singular_series_tail

/-- Halupczok 2008 pages 8 to 12, all three errors share a positive budget.
The threshold is at least three, so the logarithm and the budget are positive. -/
theorem simultaneous_error_bounds (A : ℝ) (hA : 10 ^ 4 ≤ A)
    (l₃ : ℕ) (hl₃ : 1 ≤ l₃) :
    ∃ C N₀ : ℝ, 1 ≤ C ∧ 3 ≤ N₀ ∧
      ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => RM (Qof A N) (τof A N) k l N -
            model (Qof A N) (τof A N) k l N) lam l₃ (10 ^ 4 * A) N ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (-A) ∧
          EF (fun k l => model (Qof A N) (τof A N) k l N -
            truncatedMain (Qof A N) k l N) lam l₃ (10 ^ 4 * A) N ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (-A) ∧
          EF (fun k l => truncatedMain (Qof A N) k l N -
            M singSeries k l N) lam l₃ (10 ^ 4 * A) N ≤
              C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  obtain ⟨C₁, N₁, h₁⟩ := progression_replacement A hA l₃ hl₃
  obtain ⟨C₂, N₂, h₂⟩ := singular_integral_error A hA l₃ hl₃
  obtain ⟨C₃, N₃, h₃⟩ := singular_series_tail A hA l₃ hl₃
  let C := max 1 (max C₁ (max C₂ C₃))
  let N₀ := max 3 (max N₁ (max N₂ N₃))
  refine ⟨C, N₀, le_max_left _ _, le_max_left _ _, ?_⟩
  intro lam hlam N hodd hN
  have hN₁ : N₁ ≤ N :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN₂ : N₂ ≤ N :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hN
  have hN₃ : N₃ ≤ N :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hN
  have hNN : (3 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hpow : 0 ≤ Real.log N ^ (-A) := Real.rpow_nonneg hL _
  have hC₁ : C₁ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC₂ : C₂ ≤ C :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hC₃ : C₃ ≤ C :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨(h₁ lam hlam N hodd hN₁).trans ?_,
    (h₂ lam hlam N hodd hN₂).trans ?_, (h₃ lam hlam N hodd hN₃).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC₁ (sq_nonneg _)) hpow
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC₂ (sq_nonneg _)) hpow
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC₃ (sq_nonneg _)) hpow

/-- Tolev 2009 page 3, both modulus ranges are nonempty above any threshold.
The bounded indicator weight is nonzero at an included third modulus. -/
theorem nonempty_major_arc_regime (A : ℝ) (hA : 10000 ≤ A) (T : ℝ) :
    ∃ N : ℕ, Odd N ∧ T ≤ N ∧ 3 ≤ (N : ℝ) ∧
      1 ≤ Dyadic.cutoff (10000 * A) N ∧
      1 ≤ Dyadic.cutoff3 (10000 * A) N ∧
      (∀ k : ℕ, |(if k = 1 then 1 else 0 : ℝ)| ≤ 1) ∧
      (if (1 : ℕ) = 1 then 1 else 0 : ℝ) = 1 := by
  obtain ⟨N, hodd, hN, hL, hK, _⟩ :=
    Instances355.large_odd_instances A hA (max T 3)
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hK12 := Level346.third_cutoff_le_first (10000 * A) N
    (by exact_mod_cast (show (1 : ℝ) ≤ N by linarith))
  refine ⟨N, hodd, (le_max_left _ _).trans hN, hN3, hK.trans hK12, hK, ?_, ?_⟩
  · intro k
    split_ifs <;> norm_num
  · norm_num

end LeanLab.Tolev2009.Decomp423a
