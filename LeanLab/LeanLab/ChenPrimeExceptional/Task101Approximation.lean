/-
AI wrote this Lean code for CODEX task101.
P0039 Lemma 4.2, page 19, and Definition 2.4, page 10.
The companion norm hypothesis is explicit. No pre-sieve estimate is assumed proved.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task101NaturalFourier

open Finset Real

namespace LeanLab.ChenPrimeExceptional.Task101

noncomputable section

/-- Exact exponent bookkeeping from the two-thirds estimate to the exceptional-set allowance. -/
theorem natConv_power_saving (N : ℕ) (hN : 1 ≤ N) (f g : ℕ → ℂ) {a : ℝ} (ha : 0 < a)
    (hf : fourierNorm (range (N + 1)) f ≤ (N : ℝ) ^ (1 - 2 * a))
    (hg : sqrt (∑ n ∈ range (N + 1), ‖g n‖ ^ 2) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + a / 3)) :
    (((range (2 * N + 1)).filter fun m =>
      (N : ℝ) ^ (1 - a) < ‖natConv N f g m‖).card : ℝ) ≤ (N : ℝ) ^ (1 - a) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  let η : ℝ := (N : ℝ) ^ (-2 * a)
  have hη : 0 < η := rpow_pos_of_pos hNp _
  have hηN : η * N = (N : ℝ) ^ (1 - 2 * a) := by
    change (N : ℝ) ^ (-2 * a) * N = _
    calc
      _ = (N : ℝ) ^ (-2 * a + 1) := by rw [rpow_add hNp, rpow_one]
      _ = _ := by congr 1; ring
  have ht : η ^ ((2 : ℝ) / 3) = (N : ℝ) ^ (-4 * a / 3) := by
    change ((N : ℝ) ^ (-2 * a)) ^ ((2 : ℝ) / 3) = _
    rw [← rpow_mul hNp.le]
    congr 1
    ring
  have hthreshold : η ^ ((2 : ℝ) / 3) * sqrt N *
      sqrt (∑ n ∈ range (N + 1), ‖g n‖ ^ 2) ≤ (N : ℝ) ^ (1 - a) := by
    rw [ht, sqrt_eq_rpow]
    calc
      _ ≤ (N : ℝ) ^ (-4 * a / 3) * (N : ℝ) ^ ((1 : ℝ) / 2) *
          (N : ℝ) ^ ((1 : ℝ) / 2 + a / 3) :=
        mul_le_mul_of_nonneg_left hg (by positivity)
      _ = _ := by
        rw [← rpow_add hNp, ← rpow_add hNp]
        congr 1
        ring
  have hc := natConv_paper_large_values N f g hη (by omega) (by rwa [hηN])
  have hsub : ((range (2 * N + 1)).filter fun m => (N : ℝ) ^ (1 - a) < ‖natConv N f g m‖) ⊆
      ((range (2 * N + 1)).filter fun m => η ^ ((2 : ℝ) / 3) * sqrt N *
        sqrt (∑ n ∈ range (N + 1), ‖g n‖ ^ 2) < ‖natConv N f g m‖) := by
    intro m hm
    simp only [mem_filter] at hm ⊢
    exact ⟨hm.1, hthreshold.trans_lt hm.2⟩
  refine (show (((range (2 * N + 1)).filter fun m =>
      (N : ℝ) ^ (1 - a) < ‖natConv N f g m‖).card : ℝ) ≤ _ from
      Nat.cast_le.mpr (card_le_card hsub)).trans (hc.trans ?_)
  rw [ht]
  calc
    _ = (N : ℝ) ^ (-4 * a / 3 + 1) := by rw [rpow_add hNp, rpow_one]
    _ ≤ _ := rpow_le_rpow_of_exponent_le hNr (by linarith)

/-- The numerical threshold in Definition 2.4 dominates the Fourier-derived threshold. -/
theorem approximation_threshold {N m : ℕ} {a ε S : ℝ} (hN : 1 ≤ N) (hm : N ≤ m)
    (hε : (N : ℝ) ^ (-a) ≤ ε) (hS : 0 ≤ S) :
    (N : ℝ) ^ (1 - a) ≤ ε * m * (S + 1) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hε0 : 0 ≤ ε := (rpow_pos_of_pos hNp (-a)).le.trans hε
  have hm' : (N : ℝ) ≤ m := by exact_mod_cast hm
  calc
    _ = (N : ℝ) ^ (-a) * N := by
      calc
        _ = (N : ℝ) ^ (-a + 1) := by congr 1; ring
        _ = _ := by rw [rpow_add hNp, rpow_one]
    _ ≤ ε * N := mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)
    _ ≤ ε * m := mul_le_mul_of_nonneg_left hm' hε0
    _ ≤ _ := le_mul_of_one_le_right (mul_nonneg hε0 (Nat.cast_nonneg _)) (by linarith)

/-- A finite quantitative sufficient condition for the error bound in Definition 2.4. -/
theorem definition24_count (N : ℕ) (hN : 1 ≤ N) (f g : ℕ → ℂ)
    {a ε : ℝ} (ha : 0 < a) (S : ℕ → ℝ) (hS : ∀ m, 0 ≤ S m)
    (hε : (N : ℝ) ^ (-a) ≤ ε)
    (hf : fourierNorm (range (N + 1)) f ≤ (N : ℝ) ^ (1 - 2 * a))
    (hg : sqrt (∑ n ∈ range (N + 1), ‖g n‖ ^ 2) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + a / 3)) :
    (((range (2 * N + 1)).filter fun m =>
      5 * N ≤ 4 * m ∧ 4 * m ≤ 7 * N ∧
        ε * m * (S m + 1) < ‖natConv N f g m‖).card : ℝ) ≤ (N : ℝ) ^ (1 - a) := by
  refine (show (((range (2 * N + 1)).filter fun m =>
      5 * N ≤ 4 * m ∧ 4 * m ≤ 7 * N ∧ ε * m * (S m + 1) < ‖natConv N f g m‖).card : ℝ) ≤
      (((range (2 * N + 1)).filter fun m => (N : ℝ) ^ (1 - a) < ‖natConv N f g m‖).card : ℝ)
      from Nat.cast_le.mpr (card_le_card ?_)).trans (natConv_power_saving N hN f g ha hf hg)
  intro m hm
  simp only [mem_filter] at hm ⊢
  exact ⟨hm.1, (approximation_threshold hN (by omega) hε (hS m)).trans_lt hm.2.2.2⟩

end
end LeanLab.ChenPrimeExceptional.Task101

#print axioms LeanLab.ChenPrimeExceptional.Task101.natConv_power_saving
#print axioms LeanLab.ChenPrimeExceptional.Task101.approximation_threshold
#print axioms LeanLab.ChenPrimeExceptional.Task101.definition24_count
