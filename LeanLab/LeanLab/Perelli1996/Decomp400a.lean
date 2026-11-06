/-
Perelli 1996, pages 477 and 478, Theorem 1 and Corollary 1.
Bridges between the two existing encodings.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Decomp88
import LeanLab.Perelli1996.Merge

namespace LeanLab.Perelli1996.Decomp400a
open Finset Real Polynomial
noncomputable section

/-- Page 477. Both encodings use the same von Mangoldt convolution. -/
theorem R_eq_encA (m : ℕ) : R m = EncA.R m := by
  change B.R m = LeanLab.PerelliPintz1992.r m
  exact B.R_eq m

/-- Page 478. The two errors agree whenever the polynomial value is nonnegative. -/
theorem delta_eq_err (F : ℤ[X]) (n : ℕ) (hn : 0 ≤ Fv F n) :
    Delta F n = EncA.err F n := by
  have hc : ((Fv F n).toNat : ℝ) = (Fv F n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hn
  unfold Delta EncA.err
  rw [R_eq_encA]
  change EncA.R (Fv F n).toNat - (Fv F n : ℝ) * Sing (Fv F n).toNat =
    EncA.R (Fv F n).toNat - ((Fv F n).toNat : ℝ) * Sing (Fv F n).toNat
  rw [hc]

/-- Page 480 before equation 1. For large N the errors agree on the whole window. -/
theorem eventually_delta_eq_err (F : ℤ[X]) (hF : Admissible F) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N → 0 ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ n ∈ win F N H, Delta F n = EncA.err F n := by
  obtain ⟨c, N₀, hc, hN₀, hcut⟩ := Decomp88.leaf_cutoff F hF
  refine ⟨N₀, hN₀, ?_⟩
  intro N H hN hH0 hH n hn
  exact delta_eq_err F n (hcut N H hN hH0 hH n hn).1

/-- Page 478 Theorem 1. The existing current input implies encoding A's exact statement.
CONDITIONAL ON the explicit current Theorem 1 input. -/
theorem theorem1_encA_of (h : Theorem1) (F : ℤ[X]) : EncA.Theorem1 F := by
  intro hF A ε hA hε
  obtain ⟨C, N₁, hb⟩ := h F hF A ε hA hε
  obtain ⟨N₂, hN₂, he⟩ := eventually_delta_eq_err F hF
  refine ⟨C, max N₁ N₂, ?_⟩
  intro N H hN hH hHu
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂' : N₂ ≤ N := (le_max_right _ _).trans hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith [hN₂.trans hN₂'])
  have hsum : (∑ n ∈ win F N H, Delta F n ^ 2) =
      ∑ n ∈ EncA.nRange (N ^ (1 / EncA.deg F)) H, EncA.err F n ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [he N H hN₂' ((Real.rpow_nonneg (by linarith [hN₂.trans hN₂']) _).trans hH) hHu n hn]
  have ht := hb N H hN₁ hH hHu
  rw [hsum, Real.rpow_neg hL.le, ← div_eq_mul_inv] at ht
  exact ht

/-- Page 478 Theorem 1. All encoding A inputs imply the exact current statement.
CONDITIONAL ON the explicit family of encoding A inputs. -/
theorem theorem1_of_encA (h : ∀ F : ℤ[X], EncA.Theorem1 F) : Theorem1 := by
  intro F hF A ε hA hε
  obtain ⟨C, N₁, hb⟩ := h F hF A ε hA hε
  obtain ⟨N₂, hN₂, he⟩ := eventually_delta_eq_err F hF
  refine ⟨C, max N₁ N₂, ?_⟩
  intro N H hN hH hHu
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂' : N₂ ≤ N := (le_max_right _ _).trans hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith [hN₂.trans hN₂'])
  have ht := hb N H hN₁ hH hHu
  rw [Real.rpow_neg hL.le, ← div_eq_mul_inv]
  calc
    _ = ∑ n ∈ EncA.nRange (N ^ (1 / EncA.deg F)) H, EncA.err F n ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [he N H hN₂' ((Real.rpow_nonneg (by linarith [hN₂.trans hN₂']) _).trans hH) hHu n hn]
    _ ≤ _ := ht

/-- Page 478 Theorem 1. This bridge uses the existing decomposition.
CONDITIONAL ON its named analytic leaves. The assembly adds no sorry. -/
theorem theorem1 (F : ℤ[X]) : EncA.Theorem1 F :=
  theorem1_encA_of Decomp88.theorem1 F

/-- Page 478 Corollary 1. The existing proof applies through the Theorem 1 bridge.
CONDITIONAL ON the named analytic leaves of Decomp88. -/
theorem corollary1b (F : ℤ[X]) : EncA.Corollary1b F :=
  corollary1b_of_theorem1 (theorem1 F)

end
end LeanLab.Perelli1996.Decomp400a
