/-
P0076, Proposition 2.1, pages 7 to 8, with eta below 0.05.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.Prop21Estimates
import LeanLab.Teravainen2016.Prop21Counting

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- Proposition 2.1 with eta below 0.05, as needed on page 11. -/
theorem prop21_small_proved : Prop21With (1 / 20) := by
  intro K δ ε hK hδ hε
  obtain ⟨t, η, ht, hη, hηmax, hparam⟩ := prop21_parameters hK hδ hε
  refine ⟨η, hη, hηmax, ⌈K / (t ^ 2) ^ 3⌉₊ + 1, ?_⟩
  intro N hN f₁ f₂ hf₁ hf₂
  letI : NeZero N := ⟨hN.ne'⟩
  let S := (range N).filter (fun ξ => t ^ 2 ≤ ‖fhat N f₁ ξ‖)
  by_cases hF3 : ∑ ξ ∈ range N, ‖fhat N f₁ ξ‖ ^ 3 ≤ K
  · let Ω := insert (1 % N) S
    have hc : S.card ≤ ⌈K / (t ^ 2) ^ 3⌉₊ := by
      have h1 := large_spectrum_card (range N) (fun ξ => ‖fhat N f₁ ξ‖)
        (fun ξ _ => norm_nonneg _) (sq_pos_of_pos ht) hF3
      have h2 : (S.card : ℝ) ≤ K / (t ^ 2) ^ 3 :=
        (le_div_iff₀ (by positivity)).mpr h1
      exact_mod_cast h2.trans (Nat.le_ceil _)
    refine ⟨Ω, ?_, mem_insert_self _ _, ?_, ?_⟩
    · exact insert_subset (mem_range.mpr (Nat.mod_lt _ hN)) (filter_subset _ _)
    · exact (card_insert_le _ _).trans (by omega)
    intro χ hχ hlocal hmass hmom
    have hm := chiNorm_pos hη hχ
    have hη1 : η ≤ 1 := by linarith
    let g₂ := fun n => (chiNorm N χ)⁻¹ * conv N f₂ (fun k => χ k) n
    let h₂ := fun n => f₂ n - g₂ n
    have hg : ∀ n, 0 ≤ g₂ n := by
      intro n
      exact mul_nonneg (inv_nonneg.mpr hm.le)
        (conv_nonneg N f₂ _ hf₂ (fun k => hχ.1 k) n)
    have hgl : ∀ k : ℕ, (N : ℝ) / 3 < k → (k : ℝ) < 2 * N / 3 → δ ≤ g₂ k := by
      intro k hk1 hk2
      have hh := hlocal k (by simpa using hk1) (by simpa using hk2)
      dsimp [g₂]
      rw [conv_cutoff_eq N hN f₂ χ hχ.2.2.1, inv_mul_eq_div, le_div_iff₀ hm]
      exact hh
    have hmain : ∀ n ≤ N, 9 * N ≤ 10 * n → δ ^ 2 ≤ conv N f₁ g₂ n := by
      intro n hn h9
      exact conv_smooth_lower hN f₁ g₂ hδ hf₁ hg hgl hmass hn h9
    have hhat : ∀ ξ, fhat N h₂ ξ = fhat N f₂ ξ *
        (1 - fhat N (fun n => χ n) ξ / (chiNorm N χ : ℂ)) := by
      intro ξ
      dsimp [h₂, g₂]
      rw [fhat_sub, fhat_real_smul, fhat_conv]
      push_cast
      ring
    have hH : ∀ ξ ∈ range N, ‖fhat N h₂ ξ‖ ≤ 2 * ‖fhat N f₂ ξ‖ := by
      intro ξ _
      rw [hhat, norm_mul]
      have hd : ‖1 - fhat N (fun n => χ n) ξ / (chiNorm N χ : ℂ)‖ ≤ 2 := by
        calc _ ≤ ‖(1 : ℂ)‖ + ‖fhat N (fun n => χ n) ξ / (chiNorm N χ : ℂ)‖ := norm_sub_le _ _
             _ ≤ 2 := by rw [norm_one]; linarith [chi_fourier_norm_le hη hχ ξ]
      nlinarith [norm_nonneg (fhat N f₂ ξ)]
    have hsmall : ∀ ξ ∈ range N, ξ ∉ Ω → ‖fhat N f₁ ξ‖ ≤ t ^ 2 := by
      intro ξ hξ hnΩ
      by_contra hh
      apply hnΩ
      exact mem_insert_of_mem (mem_filter.mpr ⟨hξ, by linarith⟩)
    have hlarge : ∀ ξ ∈ range N, ξ ∈ Ω → ‖fhat N h₂ ξ‖ ≤ 30 * η * ‖fhat N f₂ ξ‖ := by
      intro ξ _ hξ
      rw [hhat, norm_mul]
      have hd := chi_fourier_defect hN hη hη1 hχ hξ
      nlinarith [norm_nonneg (fhat N f₂ ξ)]
    have hF4 := (hmom 4 (by simp)).1
    have hG4 := (hmom 4 (by simp)).2
    have hspec := spectral_error_bound (range N) Ω (fhat N f₁) (fhat N f₂) (fhat N h₂)
      ht (by positivity : 0 ≤ 30 * η) (by linarith : 0 ≤ K) hF3 hF4 hG4 hH hsmall hlarge
    have henergy : (N : ℝ)⁻¹ * ∑ n ∈ range N, conv N f₁ h₂ n ^ 2 ≤ δ ^ 4 * ε / 10 := by
      rw [conv_energy]
      exact hspec.trans hparam
    exact prop21_bad_count hN f₁ f₂ g₂ hδ hmain henergy
  · refine ⟨{1 % N}, singleton_subset_iff.mpr (mem_range.mpr (Nat.mod_lt _ hN)), by simp,
      by simp, ?_⟩
    intro χ hχ hlocal hmass hmom
    exact (hF3 (hmom 3 (by simp)).1).elim

/-- The eta restricted proof also supplies the printed Proposition 2.1. -/
theorem prop21_proved : Prop21 :=
  prop21_of_small (by norm_num) prop21_small_proved

#print axioms prop21_small_proved
#print axioms prop21_proved

end LeanLab.Teravainen2016
