/-
AI wrote this Lean code for CODEX task101.
Fixed implied constants in P0039 Lemma 4.2, page 19.
The companion norm estimate remains an explicit hypothesis.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task101Approximation

open Finset Real Filter Topology

namespace LeanLab.ChenPrimeExceptional.Task101

noncomputable section

/-- Explicit absorption of the Fourier implied constant and any positive error-threshold constant. -/
theorem natConv_power_saving_constant (N : ℕ) (hN : 1 ≤ N) (f g : ℕ → ℂ)
    {a C K : ℝ} (ha : 0 < a) (hC : 0 < C) (_hK : 0 < K)
    (hsmall : C ^ ((2 : ℝ) / 3) ≤ min 1 K * (N : ℝ) ^ (a / 6))
    (hf : fourierNorm (range (N + 1)) f ≤ C * (N : ℝ) ^ (1 - 2 * a))
    (hg : sqrt (∑ n ∈ range (N + 1), ‖g n‖ ^ 2) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + a / 6)) :
    (((range (2 * N + 1)).filter fun m =>
      K * (N : ℝ) ^ (1 - a) < ‖natConv N f g m‖).card : ℝ) ≤ (N : ℝ) ^ (1 - a) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  let η : ℝ := C * (N : ℝ) ^ (-2 * a)
  have hη : 0 < η := mul_pos hC (rpow_pos_of_pos hNp _)
  have hηN : η * N = C * (N : ℝ) ^ (1 - 2 * a) := by
    change (C * (N : ℝ) ^ (-2 * a)) * N = _
    calc
      _ = C * (N : ℝ) ^ (-2 * a + 1) := by rw [rpow_add hNp, rpow_one]; ring
      _ = _ := by congr 1; congr 1; ring
  have ht : η ^ ((2 : ℝ) / 3) = C ^ ((2 : ℝ) / 3) * (N : ℝ) ^ (-4 * a / 3) := by
    change (C * (N : ℝ) ^ (-2 * a)) ^ ((2 : ℝ) / 3) = _
    rw [mul_rpow hC.le (rpow_nonneg hNp.le _), ← rpow_mul hNp.le]
    congr 2
    ring
  have hcount : C ^ ((2 : ℝ) / 3) ≤ (N : ℝ) ^ (a / 6) := by
    refine hsmall.trans ?_
    exact mul_le_of_le_one_left (rpow_nonneg hNp.le _) (min_le_left _ _)
  have hthresholdC : C ^ ((2 : ℝ) / 3) ≤ K * (N : ℝ) ^ (a / 6) :=
    hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (rpow_nonneg hNp.le _))
  have hthreshold : η ^ ((2 : ℝ) / 3) * sqrt N *
      sqrt (∑ n ∈ range (N + 1), ‖g n‖ ^ 2) ≤ K * (N : ℝ) ^ (1 - a) := by
    rw [ht, sqrt_eq_rpow]
    calc
      _ ≤ C ^ ((2 : ℝ) / 3) * (N : ℝ) ^ (-4 * a / 3) * (N : ℝ) ^ ((1 : ℝ) / 2) *
          (N : ℝ) ^ ((1 : ℝ) / 2 + a / 6) := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = C ^ ((2 : ℝ) / 3) * (N : ℝ) ^ (1 - 7 * a / 6) := by
        rw [mul_assoc, mul_assoc, ← rpow_add hNp, ← rpow_add hNp]
        congr 2
        ring
      _ ≤ (K * (N : ℝ) ^ (a / 6)) * (N : ℝ) ^ (1 - 7 * a / 6) :=
        mul_le_mul_of_nonneg_right hthresholdC (rpow_nonneg hNp.le _)
      _ = _ := by
        rw [mul_assoc, ← rpow_add hNp]
        congr 2
        ring
  have hc := natConv_paper_large_values N f g hη (by omega) (by rwa [hηN])
  have hsub : ((range (2 * N + 1)).filter fun m => K * (N : ℝ) ^ (1 - a) < ‖natConv N f g m‖) ⊆
      ((range (2 * N + 1)).filter fun m => η ^ ((2 : ℝ) / 3) * sqrt N *
        sqrt (∑ n ∈ range (N + 1), ‖g n‖ ^ 2) < ‖natConv N f g m‖) := by
    intro m hm
    simp only [mem_filter] at hm ⊢
    exact ⟨hm.1, hthreshold.trans_lt hm.2⟩
  refine (show (((range (2 * N + 1)).filter fun m =>
      K * (N : ℝ) ^ (1 - a) < ‖natConv N f g m‖).card : ℝ) ≤ _ from
      Nat.cast_le.mpr (card_le_card hsub)).trans (hc.trans ?_)
  rw [ht]
  calc
    _ = C ^ ((2 : ℝ) / 3) * (N : ℝ) ^ (1 - 4 * a / 3) := by
      rw [mul_assoc]
      congr 1
      rw [show 1 - 4 * a / 3 = -4 * a / 3 + 1 by ring, rpow_add hNp, rpow_one]
    _ ≤ (N : ℝ) ^ (a / 6) * (N : ℝ) ^ (1 - 4 * a / 3) :=
      mul_le_mul_of_nonneg_right hcount (rpow_nonneg hNp.le _)
    _ = (N : ℝ) ^ (1 - 7 * a / 6) := by rw [← rpow_add hNp]; congr 1; ring
    _ ≤ _ := rpow_le_rpow_of_exponent_le hNr (by linarith)

/-- Every fixed implied constant is absorbed for sufficiently large natural N. -/
theorem eventually_power_saving_constant {a C K : ℝ} (ha : 0 < a) (hC : 0 < C) (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop, ∀ f g : ℕ → ℂ,
      fourierNorm (range (N + 1)) f ≤ C * (N : ℝ) ^ (1 - 2 * a) →
      sqrt (∑ n ∈ range (N + 1), ‖g n‖ ^ 2) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 + a / 6) →
      (((range (2 * N + 1)).filter fun m =>
        K * (N : ℝ) ^ (1 - a) < ‖natConv N f g m‖).card : ℝ) ≤ (N : ℝ) ^ (1 - a) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (a / 6)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < a / 6)).comp tendsto_natCast_atTop_atTop
  have hmin : 0 < min (1 : ℝ) K := lt_min zero_lt_one hK
  filter_upwards [eventually_ge_atTop (1 : ℕ), ht.eventually_ge_atTop (C ^ ((2 : ℝ) / 3) / min 1 K)]
    with N hN hs
  intro f g hf hg
  apply natConv_power_saving_constant N hN f g ha hC hK _ hf hg
  have h := (div_le_iff₀ hmin).mp hs
  nlinarith

end
end LeanLab.ChenPrimeExceptional.Task101

#print axioms LeanLab.ChenPrimeExceptional.Task101.natConv_power_saving_constant
#print axioms LeanLab.ChenPrimeExceptional.Task101.eventually_power_saving_constant
