/-
P0027 Li 2024: links to the lab's explicit Chen module.
AI-written Lean code, Claude, 2026-10-16. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.Li2024.Statements

open Finset
noncomputable section
namespace LeanLab.Li2024
open LeanLab.ChenExplicit

theorem D12_eq_chenCount (N : ℕ) : D12 N = chenCount N := by
  classical
  unfold D12 chenCount
  congr 1
  ext p
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨hp, hpr, h0, hΩ⟩
    refine ⟨?_, hpr, h0, hΩ⟩
    rcases Nat.lt_or_ge p N with h | h
    · exact h
    · exact absurd (by omega : N - p = 0) h0
  · rintro ⟨hp, hpr, h⟩
    exact ⟨by omega, hpr, h⟩

theorem C_pos (N : ℕ) : 0 < C N := by
  unfold C
  have := twinC_pos
  have := one_le_oddFactor N
  positivity

/-- `U_N = 2 e^{-γ} C(N)`, so Li's normalisation and BJS's differ by `2 e^{-γ}`. -/
theorem U_eq (N : ℕ) : U N = 2 * Real.exp (-Real.eulerMascheroniConstant) * C N := by
  unfold U C; ring

/-- A smaller positive constant is implied. -/
theorem LiBound.mono {c c' : ℝ} (h : LiBound c) (hc' : c' ≤ c) : LiBound c' := by
  obtain ⟨N0, hN⟩ := h
  refine ⟨N0, fun N hN2 hN0 => le_trans ?_ (hN N hN2 hN0)⟩
  have := C_pos N
  have : 0 ≤ (N : ℝ) / Real.log N ^ 2 := by positivity
  have e : ∀ c : ℝ, c * C N * N / Real.log N ^ 2 = c * (C N * ((N : ℝ) / Real.log N ^ 2)) := by
    intro c; ring
  rw [e, e]
  exact mul_le_mul_of_nonneg_right hc' (by positivity)

/-- Li's bound with any `c > 0` gives qualitative Chen above some threshold. -/
theorem chenAbove_of_li {c : ℝ} (hc : 0 < c) (h : LiBound c) : ∃ T : ℝ, ChenAbove T := by
  obtain ⟨N0, hN⟩ := h
  refine ⟨max N0 1, fun N hN2 hT => ?_⟩
  have hN0 : N0 ≤ N := by
    have : (N0 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hT
    exact_mod_cast this.le
  have h1 : (1 : ℝ) < N := lt_of_le_of_lt (le_max_right _ _) hT
  have hlog : 0 < Real.log N := Real.log_pos h1
  have hpos : 0 < c * C N * N / Real.log N ^ 2 := by
    have := C_pos N; positivity
  have hD : 0 < chenCount N := by
    rw [← D12_eq_chenCount]; exact_mod_cast hpos.trans_le (hN N hN2 hN0)
  unfold chenCount at hD
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hD
  simp only [mem_filter, mem_range] at hp
  exact ⟨p, N - p, hp.2.1, by omega, hp.2.2⟩

/-- Li's constant, 1.733 in v3 or 1.9728 in v4, beats BJS's `2·10⁻⁴ U_N` asymptotically: with `c ≥ 4·10⁻⁴`, BJS Theorem 3's
inequality, in the non-strict form, holds for all large even `N`. -/
theorem bjs3_shape_of_li {c : ℝ} (hc : 4 / 10000 ≤ c) (h : LiBound c) :
    ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
      (2 / 10000 : ℝ) * U N * N / Real.log N ^ 2 ≤ chenCount N := by
  obtain ⟨N0, hN⟩ := h
  refine ⟨N0, fun N hN2 hN0 => ?_⟩
  rw [← D12_eq_chenCount]
  refine le_trans ?_ (hN N hN2 hN0)
  rw [U_eq]
  have hγ : Real.exp (-Real.eulerMascheroniConstant) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hγ0 : 0 < Real.exp (-Real.eulerMascheroniConstant) := Real.exp_pos _
  have := C_pos N
  have hX : 0 ≤ C N * ((N : ℝ) / Real.log N ^ 2) := by positivity
  have e1 : (2 / 10000 : ℝ) * (2 * Real.exp (-Real.eulerMascheroniConstant) * C N) * N /
      Real.log N ^ 2 = (4 / 10000 * Real.exp (-Real.eulerMascheroniConstant)) *
        (C N * ((N : ℝ) / Real.log N ^ 2)) := by ring
  have e2 : c * C N * N / Real.log N ^ 2 = c * (C N * ((N : ℝ) / Real.log N ^ 2)) := by ring
  rw [e1, e2]
  apply mul_le_mul_of_nonneg_right _ hX
  nlinarith

/-- Concretely, from v3's Theorem 1.1. -/
theorem chenAbove_of_v3 (h : theorem1_1_v3_stmt) : ∃ T : ℝ, ChenAbove T := chenAbove_of_li (by norm_num) h

end LeanLab.Li2024
