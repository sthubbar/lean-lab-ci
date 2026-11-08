import LeanLab.ExceptionalSet.SPLIT_leaf_boundary_outer_low
import LeanLab.ExceptionalSet.SPLIT_leaf_boundary_outer_high

/-!
P0082 page 365 Lemma 8, exact companions for empty upper index pieces.
The parameter hypotheses have witnesses. The counted pieces are necessarily empty.
The nonempty lower index pieces retain their analytic discrepancy inputs.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp464d

open Real MeasureTheory
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- P0082 page 365 Lemma 8, literal floor window auxiliary.
The above N piece is empty once N is at least eight. -/
theorem leaf_outer_low_low_band_upper_indices (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          N < n ∧ Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) / 4)).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  refine ⟨1, by norm_num, fun κ hκ hκcap => ⟨1, by norm_num, 8, fun N hN => ?_⟩⟩
  have hempty : ((window γ N).filter (fun n : ℕ =>
          N < n ∧ Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) / 4)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro n hn hband
    exact (not_lt_of_ge (Decomp371a.window_upper γ h1 N hN n hn)) hband.1
  rw [hempty]
  simp only [Finset.card_empty, Nat.cast_zero, one_mul]
  exact mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg (Real.exp_pos _).le _)

/-- P0082 page 365 Lemma 8, literal floor window auxiliary.
The above N piece is empty once N is at least eight. -/
theorem leaf_outer_low_high_band_upper_indices (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          N < n ∧ calE γ κ N ^ (-(1 / 8 : ℝ)) / 4 ≤ Int.fract (F γ n) ∧
            Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) / 2)).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  refine ⟨1, by norm_num, fun κ hκ hκcap => ⟨1, by norm_num, 8, fun N hN => ?_⟩⟩
  have hempty : ((window γ N).filter (fun n : ℕ =>
          N < n ∧ calE γ κ N ^ (-(1 / 8 : ℝ)) / 4 ≤ Int.fract (F γ n) ∧
            Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) / 2)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro n hn hband
    exact (not_lt_of_ge (Decomp371a.window_upper γ h1 N hN n hn)) hband.1
  rw [hempty]
  simp only [Finset.card_empty, Nat.cast_zero, one_mul]
  exact mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg (Real.exp_pos _).le _)

/-- P0082 page 365 Lemma 8, literal floor window auxiliary.
The above N piece is empty once N is at least eight. -/
theorem leaf_outer_high_lower_band_upper_indices (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          N < n ∧ 1 - calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 < Int.fract (F γ n) ∧
            Int.fract (F γ n) ≤ 1 - 1 / 4 * calE γ κ N ^ (-(1 / 8 : ℝ)))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  refine ⟨1, by norm_num, fun κ hκ hκcap => ⟨1, by norm_num, 8, fun N hN => ?_⟩⟩
  have hempty : ((window γ N).filter (fun n : ℕ =>
          N < n ∧ 1 - calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 < Int.fract (F γ n) ∧
            Int.fract (F γ n) ≤ 1 - 1 / 4 * calE γ κ N ^ (-(1 / 8 : ℝ)))) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro n hn hband
    exact (not_lt_of_ge (Decomp371a.window_upper γ h1 N hN n hn)) hband.1
  rw [hempty]
  simp only [Finset.card_empty, Nat.cast_zero, one_mul]
  exact mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg (Real.exp_pos _).le _)

/-- P0082 page 365 Lemma 8, literal floor window auxiliary.
The above N piece is empty once N is at least eight. -/
theorem leaf_outer_high_upper_band_upper_indices (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          N < n ∧ 1 - 1 / 4 * calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  refine ⟨1, by norm_num, fun κ hκ hκcap => ⟨1, by norm_num, 8, fun N hN => ?_⟩⟩
  have hempty : ((window γ N).filter (fun n : ℕ =>
          N < n ∧ 1 - 1 / 4 * calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro n hn hband
    exact (not_lt_of_ge (Decomp371a.window_upper γ h1 N hN n hn)) hband.1
  rw [hempty]
  simp only [Finset.card_empty, Nat.cast_zero, one_mul]
  exact mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg (Real.exp_pos _).le _)

end LeanLab.ExceptionalSet.Decomp464d
