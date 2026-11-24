import LeanLab.ExceptionalSet.SPLIT_leaf_mean_square

/-!
Split of `leaf_window_energy_four_not_dvd` of `LeanLab.ExceptionalSet.SPLIT_leaf_mean_square`, the second moment of
`error n = r2 n - n * Sing n` over the window `(Y/2, Y]` restricted to the even `n` not divisible by `4`.

Source: P0029, arXiv 2607.27282, page 13 display 3.8, the mean square bound
`∑_{N ≤ X} |E2 N|^2 ≪ X^(3/2 + 2Θ + ε)`, obtained there from Parseval and the zero estimate
page 12 display 3.7, with the main term of display 3.5 giving `N 𝔖(N)`.

The split expands the square, `error^2 = r2^2 - 2 (n Sing) r2 + (n Sing)^2`, so that
`∑ error^2 = (∑ r2^2 - ∑ (n Sing)^2) + 2 (∑ (n Sing)^2 - ∑ (n Sing) r2)`, and leaves
* a second moment of `r2` about zero on the window class, compared with the square of the
  main term `n 𝔖(n)` of display 3.5, and
* a twisted first moment, the correlation of `r2` with the main term `n 𝔖(n)`.
Both carry the same exponent `3/2 + 2Θ + ε` and the zero free region hypothesis.
The assembly is pure algebra.

AI wrote this Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.BG2026.Supply385

open Finset Real

namespace Feed1122_window_energy_four_not_dvd

/-- Algebraic expansion of the window energy of `error` into the two moment pieces. -/
theorem energy_expand (s : Finset ℕ) :
    ∑ n ∈ s, (error n) ^ 2 =
      (∑ n ∈ s, (r2 n) ^ 2 - ∑ n ∈ s, ((n : ℝ) * Sing n) ^ 2) +
        2 * (∑ n ∈ s, ((n : ℝ) * Sing n) ^ 2 - ∑ n ∈ s, ((n : ℝ) * Sing n) * r2 n) := by
  unfold error
  have : ∀ n ∈ s, (r2 n - (n : ℝ) * Sing n) ^ 2 =
      (r2 n) ^ 2 - ((n : ℝ) * Sing n) ^ 2 +
        2 * (((n : ℝ) * Sing n) ^ 2 - ((n : ℝ) * Sing n) * r2 n) := by
    intro n _; ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_sub_distrib]

end Feed1122_window_energy_four_not_dvd

/-- LEAF: P0029 page 13 display 3.8, the Parseval step for `|f|^4` against the squared main term
of page 11 display 3.5, restricted to one window class: the second moment of `r2` over the even
`n` not divisible by `4` in `(Y/2, Y]` exceeds the second moment of the main term `n 𝔖(n)` there by at most
`C Y^(3/2 + 2Θ + ε)`, using the zero estimate page 12 display 3.7.  Class HARD. -/
theorem leaf_window_energy_four_not_dvd_r2_sq (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ ¬ 4 ∣ n), (r2 n) ^ 2 ≤
        ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ ¬ 4 ∣ n), ((n : ℝ) * Sing n) ^ 2 +
          C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- LEAF: P0029 page 13 display 3.8 with the main term of page 11 display 3.5 and the Ramanujan sum
evaluation on page 12, restricted to one window class: the correlation of `r2 n` with the main
term `n 𝔖(n)` over the even `n` not divisible by `4` in `(Y/2, Y]` falls short of the second moment of the
main term by at most `C Y^(3/2 + 2Θ + ε)`, using the zero estimate page 12 display 3.7.
Class HARD. -/
theorem leaf_window_energy_four_not_dvd_twisted_first (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ ¬ 4 ∣ n), ((n : ℝ) * Sing n) ^ 2 -
          ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ ¬ 4 ∣ n),
            ((n : ℝ) * Sing n) * r2 n ≤
        C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- Assembly: the original window leaf from the two moment leaves, by the expansion
`Feed1122_window_energy_four_not_dvd.energy_expand`. -/
theorem leaf_window_energy_four_not_dvd_feed (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε) (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Y₀ : ℕ, 1 ≤ Y₀ ∧ ∀ Y : ℕ, Y₀ ≤ Y →
      ∑ n ∈ (Finset.Icc (Y / 2 + 1) Y).filter (fun n => Even n ∧ ¬ 4 ∣ n), (error n) ^ 2 ≤
        C * (Y : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  obtain ⟨C₁, hC₁, Y₁, hY₁, h₁⟩ := leaf_window_energy_four_not_dvd_r2_sq Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C₂, hC₂, Y₂, hY₂, h₂⟩ := leaf_window_energy_four_not_dvd_twisted_first Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨C₁ + 2 * C₂, by positivity, max Y₁ Y₂, le_max_of_le_left hY₁, fun Y hY => ?_⟩
  have a := h₁ Y ((le_max_left _ _).trans hY)
  have b := h₂ Y ((le_max_right _ _).trans hY)
  rw [Feed1122_window_energy_four_not_dvd.energy_expand]
  linarith

end LeanLab.ExceptionalSet.BG2026.Supply385
