/-
AI wrote this Lean code. Codex task346.
Binary Goldbach is open.
Source: Halupczok 2008 page 10 to 11, O3.
The scalar rectangular mean is OPEN. The exact assemblies are CONDITIONAL ON it.
-/
import LeanLab.Tolev2009.ScalarEnvelope346

open Finset Real MeasureTheory
namespace LeanLab.Tolev2009.Decomp346c
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Decomp314a LeanLab.Tolev2009.Progression346
open LeanLab.Tolev2009.ScalarEnvelope346

-- Helper lemma: for N ≥ 3, log N ≥ 1
lemma logN_ge_one {N : ℕ} (h : (3 : ℕ) ≤ N) : (1 : ℝ) ≤ Real.log N := by
  have h₀ : (0 : ℝ) < N := by exact_mod_cast h
  rw [Real.le_log_iff_exp_le h₀]
  linarith [Real.exp_one_lt_d9]

-- Helper lemma: log N ^ (-A) = (log N ^ A)⁻¹ ≤ 1 for A ≥ 0 and log N ≥ 1
lemma log_rpow_neg_le_inv {N : ℕ} {A : ℝ} (hA : 0 ≤ A) (h : (1 : ℝ) ≤ Real.log N) :
    Real.log N ^ (-A) = (Real.log N ^ A)⁻¹ ∧ (Real.log N ^ A)⁻¹ ≤ 1 := by
  refine' ⟨Real.rpow_neg (by positivity) (Real.log N) |>.symm, _⟩
  exact Real.inv_le_one (Real.one_le_rpow h hA)

/-- LEAF. Halupczok page 10 to 11, O3, the positive scalar rectangular mean.
Only real theta discrepancies, totients, logarithms and natural modulus sums occur.
There are no prime polynomials, rational phases, residue variables, signed weights
or integrals in this arithmetic leaf. The bad prime profile is explicit. OPEN. -/
theorem cubic_scalar_mean :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∃ C N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
      scalarMean 3 A N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  sorry

/-- Halupczok page 10 to 11, O3, after discrete partial summation on page 7.
Estimate only the static positive degree 3 rational prefix discrepancy average.
There is no beta variable, integral or arbitrary lambda. The full prime interval
and the fixed third residue retain the sealed 2009 adaptation.
CONDITIONAL ON cubic_scalar_mean. -/
theorem cubic_prefix_mean :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
        EF (fun k l => errorEnvelope 3 (Qof A N) (τof A N) k l N)
          (fun _ => 1) l₃ (10 ^ 4 * A) N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, N₀, h⟩ := cubic_scalar_mean A hA
  refine ⟨C, max N₀ 3, fun N hodd hN => ?_⟩
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    linarith [Real.exp_one_lt_d9]
  have hQ : 1 ≤ Qof A N := Real.one_le_rpow hL (by linarith)
  exact (prefix_mean_le_scalar 3 A N l₃ hQ (by exact_mod_cast (show (1 : ℝ) ≤ N by linarith))).trans
    (h N hodd ((le_max_left _ _).trans hN))

/-- The exact sealed degree 3 remainder statement.
CONDITIONAL ON the static positive prefix mean. No new integral estimate is assumed. -/
theorem cubic_remainder_mean :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          EF (fun k l => errorTerm 3 (Qof A N) (τof A N) k l N)
            lam l₃ (10 ^ 4 * A) N ≤ C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, N₀, h⟩ := cubic_prefix_mean A hA l₃ hl₃
  exact ⟨C, N₀, fun lam hlam N hodd hN =>
    (error_mean_bound 3 A lam l₃ N hlam).trans (h N hodd hN)⟩

end LeanLab.Tolev2009.Decomp346c