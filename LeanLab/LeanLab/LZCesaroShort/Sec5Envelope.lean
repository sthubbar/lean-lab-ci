import LeanLab.LZCesaroShort.Lemma8Proof
import LeanLab.LZCesaroShort.Circle

/-!
# Window bounds for the zero term

AI wrote this Lean code. Binary Goldbach is open.
Source: arXiv 1606.00869v2, pages 10 and 11, Section 5.
The elementary transfer uses the proved unconditional Lemma 8.
The unproved unconditional decay rate is recorded in STATEMENTS.md only.
The displayed free n in that factor on page 11 is recorded as a notation question.
-/

namespace LeanLab.LZCesaroShort

open Finset
open scoped Chebyshev

/-- A window envelope for psi transfers to the zero term through Lemma 8. -/
theorem zero_term_bound_of_psi_window : ∃ N₀ : ℕ, ∃ K : ℝ, 0 ≤ K ∧
    ∀ N H : ℕ, N₀ ≤ N → 2 ≤ H → H ≤ N → ∀ E : ℝ, 0 ≤ E →
      (∀ n ∈ Icc (N - H) (N + H), |ψ (n : ℝ) - n| ≤ E) →
      ‖ZH N H / (H : ℂ)‖ ≤ H * E + K * N := by
  obtain ⟨N₀, K, hK⟩ := lz_lemma8_proved
  refine ⟨N₀, |K|, abs_nonneg K, fun N H hN hH hHN E _hE hE => ?_⟩
  have hHp : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  let P : ℝ := ∑ n ∈ Icc (N - H) (N + H), tw N H n * (ψ (n : ℝ) - n)
  have hb := hK N H hN hH hHN
  change ‖(P : ℂ) + ZH N H‖ ≤ K * H * N at hb
  have hb' : ‖(P : ℂ) + ZH N H‖ ≤ |K| * H * N := by
    refine hb.trans ?_
    have hm := mul_le_mul_of_nonneg_right (le_abs_self K)
      (by positivity : (0 : ℝ) ≤ H * N)
    nlinarith
  have hP : |P| ≤ (H : ℝ) ^ 2 * E := by
    calc
      |P| ≤ ∑ n ∈ Icc (N - H) (N + H), |tw N H n * (ψ (n : ℝ) - n)| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Icc (N - H) (N + H), tw N H n * E := by
        apply sum_le_sum
        intro n hn
        rw [abs_mul, abs_of_nonneg (tw_nonneg hHN hn)]
        exact mul_le_mul_of_nonneg_left (hE n hn) (tw_nonneg hHN hn)
      _ = (H : ℝ) ^ 2 * E := by rw [← sum_mul, sum_tw hHN]
  have hZ : ‖ZH N H‖ ≤ ‖(P : ℂ) + ZH N H‖ + |P| := by
    calc
      ‖ZH N H‖ = ‖((P : ℂ) + ZH N H) - (P : ℂ)‖ := by congr 1; ring
      _ ≤ ‖(P : ℂ) + ZH N H‖ + ‖(P : ℂ)‖ := norm_sub_le _ _
      _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hHp]
  nlinarith

end LeanLab.LZCesaroShort
