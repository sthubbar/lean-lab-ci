import LeanLab.ExceptionalSet.Decomp371a

/-!
P0082 page 365, literal floor window in Lemma 8.
Source: https://doi.org/10.5802/aif.1621
The formal boundary splits also consider indices above N.
Those pieces are empty once N is at least eight.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp462j

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- P0082 page 365, empty upper index piece of the formal boundary split. -/
theorem leaf_outer_low_low_band_upper_indices_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          N < n ∧ Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) / 4)).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  refine ⟨1, by norm_num, fun κ hκ hκ1 => ⟨1, by norm_num, 8, fun N hN => ?_⟩⟩
  have he : (window γ N).filter (fun n : ℕ => N < n ∧ Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) / 4) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro n hn hbad
    have hupper := Decomp371a.window_upper γ h1 N hN n hn
    exact (not_lt_of_ge hupper) hbad.1
  rw [he]
  simp only [Finset.card_empty, Nat.cast_zero]
  unfold calE
  positivity

/-- P0082 page 365, empty upper index piece of the formal boundary split. -/
theorem leaf_outer_low_high_band_upper_indices_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          N < n ∧ calE γ κ N ^ (-(1 / 8 : ℝ)) / 4 ≤ Int.fract (F γ n) ∧
            Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) / 2)).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  refine ⟨1, by norm_num, fun κ hκ hκ1 => ⟨1, by norm_num, 8, fun N hN => ?_⟩⟩
  have he : (window γ N).filter (fun n : ℕ => N < n ∧ calE γ κ N ^ (-(1 / 8 : ℝ)) / 4 ≤ Int.fract (F γ n) ∧
            Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) / 2) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro n hn hbad
    have hupper := Decomp371a.window_upper γ h1 N hN n hn
    exact (not_lt_of_ge hupper) hbad.1
  rw [he]
  simp only [Finset.card_empty, Nat.cast_zero]
  unfold calE
  positivity

/-- P0082 page 365, empty upper index piece of the formal boundary split. -/
theorem leaf_outer_high_lower_band_upper_indices_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          N < n ∧ 1 - calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 < Int.fract (F γ n) ∧
            Int.fract (F γ n) ≤ 1 - 1 / 4 * calE γ κ N ^ (-(1 / 8 : ℝ)))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  refine ⟨1, by norm_num, fun κ hκ hκ1 => ⟨1, by norm_num, 8, fun N hN => ?_⟩⟩
  have he : (window γ N).filter (fun n : ℕ => N < n ∧ 1 - calE γ κ N ^ (-(1 / 8 : ℝ)) / 2 < Int.fract (F γ n) ∧
            Int.fract (F γ n) ≤ 1 - 1 / 4 * calE γ κ N ^ (-(1 / 8 : ℝ))) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro n hn hbad
    have hupper := Decomp371a.window_upper γ h1 N hN n hn
    exact (not_lt_of_ge hupper) hbad.1
  rw [he]
  simp only [Finset.card_empty, Nat.cast_zero]
  unfold calE
  positivity

/-- P0082 page 365, empty upper index piece of the formal boundary split. -/
theorem leaf_outer_high_upper_band_upper_indices_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          N < n ∧ 1 - 1 / 4 * calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  refine ⟨1, by norm_num, fun κ hκ hκ1 => ⟨1, by norm_num, 8, fun N hN => ?_⟩⟩
  have he : (window γ N).filter (fun n : ℕ => N < n ∧ 1 - 1 / 4 * calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro n hn hbad
    have hupper := Decomp371a.window_upper γ h1 N hN n hn
    exact (not_lt_of_ge hupper) hbad.1
  rw [he]
  simp only [Finset.card_empty, Nat.cast_zero]
  unfold calE
  positivity

end LeanLab.ExceptionalSet.Decomp462j
