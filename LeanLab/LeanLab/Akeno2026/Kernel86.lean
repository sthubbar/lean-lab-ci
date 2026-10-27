/-
P0087 Akeno 2026 page 4, summing the Fourier decay bound in Lemma 2.2.
A shifted reciprocal square kernel has a uniform summable majorant.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.Akeno2026.Kernel86
open Real Finset
/-- LEAF. Page 4, the shifted reciprocal square sum is bounded uniformly in the shift. -/
theorem uniform_shifted_kernel : ∃ S : ℝ, 0 < S ∧ ∀ α : ℝ,
    Summable (fun n : ℤ => 1 / (1 + |(n : ℝ) - α|) ^ 2) ∧
      (∑' n : ℤ, 1 / (1 + |(n : ℝ) - α|) ^ 2) ≤ S := by
  let g : ℤ → ℝ := fun n => 1 / |(n : ℝ) - 1 / 2| ^ 2
  have hg : Summable g := by
    simpa [g, sub_eq_add_neg, Real.rpow_two] using
      (Real.summable_one_div_int_add_rpow (-(1 / 2 : ℝ)) 2).2 (by norm_num)
  refine ⟨(∑' n : ℤ, g n) + 1, ?_, ?_⟩
  · have hh : 0 ≤ ∑' n : ℤ, g n := tsum_nonneg (fun n => by dsimp [g]; positivity)
    linarith
  intro α
  let z : ℤ := ⌊α⌋
  have hgshift : Summable (fun n : ℤ => g (n - z)) := by
    simpa [Function.comp_def, sub_eq_add_neg] using (Equiv.addRight (-z)).summable_iff.mpr hg
  have hsum : (∑' n : ℤ, g (n - z)) = ∑' n : ℤ, g n := by
    simpa [sub_eq_add_neg] using (Equiv.addRight (-z)).tsum_eq g
  have hmajor : ∀ n : ℤ, 1 / (1 + |(n : ℝ) - α|) ^ 2 ≤ g (n - z) := by
    intro n
    have hhalf : 0 < |((n - z : ℤ) : ℝ) - 1 / 2| := by
      by_cases hk : n - z ≤ 0
      · have hh : ((n - z : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hk
        rw [abs_of_neg (by linarith)]
        linarith
      · have hh : (1 : ℝ) ≤ ((n - z : ℤ) : ℝ) := by
          exact_mod_cast (show (1 : ℤ) ≤ n - z by omega)
        rw [abs_of_pos (by linarith)]
        linarith
    have hf : |α - (z : ℝ) - 1 / 2| ≤ 1 / 2 := by
      change |Int.fract α - 1 / 2| ≤ 1 / 2
      apply abs_le.mpr
      constructor <;> linarith [Int.fract_nonneg α, Int.fract_lt_one α]
    have hid : ((n - z : ℤ) : ℝ) - 1 / 2 =
        ((n : ℝ) - α) + (α - (z : ℝ) - 1 / 2) := by push_cast; ring
    have hd : |((n - z : ℤ) : ℝ) - 1 / 2| ≤ 1 + |(n : ℝ) - α| := by
      rw [hid]
      have hh := abs_add_le ((n : ℝ) - α) (α - (z : ℝ) - 1 / 2)
      linarith
    exact one_div_le_one_div_of_le (sq_pos_of_pos hhalf)
      (pow_le_pow_left₀ (abs_nonneg _) hd 2)
  have hs := Summable.of_nonneg_of_le (fun n : ℤ => by positivity) hmajor hgshift
  refine ⟨hs, ?_⟩
  have hh := Summable.tsum_le_tsum hmajor hs hgshift
  rw [hsum] at hh
  linarith

end LeanLab.Akeno2026.Kernel86
