import LeanLab.LZCesaroShort.Theorem1Full

/-!
# P0058 Theorem 2 eq. (3) as the printed Prop, and Theorem 1 for every `N ≥ 2`, `2 ≤ H ≤ N`

Lab proof, unit U-6209, CLOUD 20261020T0817Z-cloud38, T1. AI wrote this file. CONDITIONAL ON
RiemannHypothesis only. Binary Goldbach is OPEN.

* `absorb_small`: a bound `f ≤ K g` for `N ≥ N₀` extends to every `N ≥ 2` when `g > 0` on the
  finitely many smaller pairs, by enlarging `K`;
* `theorem2bP_proved : RiemannHypothesis → Theorem2bP`: the printed Theorem 2 eq. (3), every
  `N ≥ 2` and `1 ≤ H ≤ N`, with no restriction left;
* `theorem1_all`: the printed Theorem 1 for every `N ≥ 2` and `2 ≤ H ≤ N`; `Theorem1P` also asks
  for `H = 1`, which stays open in the lab.
-/

namespace LeanLab.LZCesaroShort

open Finset

/-- **Absorbing finitely many small `N` into the constant.** -/
lemma absorb_small (f g : ℕ → ℕ → ℝ) (h0 : ℕ) (hg : ∀ N H, 2 ≤ N → h0 ≤ H → H ≤ N → 0 < g N H)
    {K : ℝ} {N₀ : ℕ} (hK : ∀ N H, N₀ ≤ N → h0 ≤ H → H ≤ N → f N H ≤ K * g N H) :
    ∃ K' : ℝ, ∀ N H, 2 ≤ N → h0 ≤ H → H ≤ N → f N H ≤ K' * g N H := by
  set S := (range N₀ ×ˢ range N₀).filter (fun p : ℕ × ℕ => 2 ≤ p.1 ∧ h0 ≤ p.2 ∧ p.2 ≤ p.1) with hS
  set M := ∑ p ∈ S, |f p.1 p.2| / g p.1 p.2 with hM
  have hM0 : ∀ p ∈ S, 0 ≤ |f p.1 p.2| / g p.1 p.2 := by
    intro p hp
    simp only [hS, mem_filter] at hp
    exact div_nonneg (abs_nonneg _) (hg _ _ hp.2.1 hp.2.2.1 hp.2.2.2).le
  refine ⟨max K M, fun N H hN hH hHN => ?_⟩
  have hg0 := hg N H hN hH hHN
  rcases le_or_gt N₀ N with h | h
  · exact (hK N H h hH hHN).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hg0.le)
  · have hp : (N, H) ∈ S := by
      simp only [hS, mem_filter, mem_product, mem_range]
      exact ⟨⟨h, by omega⟩, hN, hH, hHN⟩
    have h1 : |f N H| / g N H ≤ M := single_le_sum (f := fun p : ℕ × ℕ => |f p.1 p.2| / g p.1 p.2)
      hM0 hp
    have h2 : f N H ≤ M * g N H := by
      have := (le_abs_self (f N H)).trans (le_of_eq (div_mul_cancel₀ (|f N H|) hg0.ne').symm)
      exact this.trans (mul_le_mul_of_nonneg_right h1 hg0.le)
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hg0.le)

lemma log_two_N_div_pos {N H : ℕ} (hN : 2 ≤ N) (hH : 1 ≤ H) (hHN : H ≤ N) :
    0 < Real.log (2 * (N : ℝ) / H) := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hHN' : (H : ℝ) ≤ N := by exact_mod_cast hHN
  apply Real.log_pos
  rw [lt_div_iff₀ hH0]
  have : (2 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

/-- **P0058 Theorem 2 eq. (3), the printed Prop, from RH.** -/
theorem theorem2bP_proved (hRH : RiemannHypothesis) : Theorem2bP := by
  obtain ⟨K, -, h⟩ := theorem2b_full hRH
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, (10 : ℝ) ^ 20 ≤ N₀ := ⟨10 ^ 20, by norm_num⟩
  have hK : ∀ N H : ℕ, N₀ ≤ N → 1 ≤ H → H ≤ N →
      |wsum N H H| ≤ K * (N * Real.log (2 * (N : ℝ) / H) ^ 2) := by
    intro N H hN hH hHN
    have := h N H (hN₀.trans (by exact_mod_cast hN)) hH hHN
    rw [← mul_assoc]; exact this
  obtain ⟨K', hK'⟩ := absorb_small (fun N H => |wsum N H H|)
    (fun N H => N * Real.log (2 * (N : ℝ) / H) ^ 2) 1
    (fun N H hN hH hHN => by
      have := log_two_N_div_pos hN hH hHN
      have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      positivity) hK
  refine ⟨K', fun N H hN hH hHN => ?_⟩
  have := hK' N H hN hH hHN
  rw [mul_assoc]; exact this

/-- **P0058 Theorem 1 as printed, from RH, for every `N ≥ 2` and `2 ≤ H ≤ N`.** -/
theorem theorem1_all (hRH : RiemannHypothesis) : ∃ K : ℝ, ∀ N H : ℕ, 2 ≤ N → 2 ≤ H → H ≤ N →
    ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖
      ≤ K * (N * Real.log (2 * (N : ℝ) / H) ^ 2 + H * Real.log N ^ 2 * Real.log (2 * H)) := by
  obtain ⟨K, N₀, h⟩ := theorem1_full hRH
  exact absorb_small (fun N H => ‖((cesaro N H : ℝ) : ℂ) - (H : ℂ) * N + 2 / (H : ℂ) * ZH N H‖)
    (fun N H => N * Real.log (2 * (N : ℝ) / H) ^ 2 + H * Real.log N ^ 2 * Real.log (2 * H)) 2
    (fun N H hN hH hHN => by
      have := log_two_N_div_pos hN (by omega) hHN
      have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have : 0 ≤ (H : ℝ) * Real.log N ^ 2 * Real.log (2 * H) := by
        have : (1 : ℝ) ≤ 2 * H := by
          have : (2 : ℝ) ≤ H := by exact_mod_cast hH
          linarith
        have := Real.log_nonneg this
        positivity
      positivity)
    (fun N H hN hH hHN => h N H hN hH hHN)

end LeanLab.LZCesaroShort
