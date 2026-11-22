import LeanLab.Ricci1937.Case5
import LeanLab.Ricci1937.Case5Index

/-!
Ricci 1937, pages 88 to 90. Obstructions to the printed fifth pair support route.
These results do not negate either count statement for two and 366.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Real

/-- Page 89 support and companion cutoff inequalities force this strict scalar margin. -/
lemma decomp677_companion_margin {δ r τ κ B : ℝ}
    (hδ : 0 < δ) (hB : 0 < B) (hcut : 1 / B < δ * r)
    (hκ : 0 < κ) (hsave : δ * (1 + 2 * τ) ≤ 1 - κ) :
    1 + 2 * τ < B * r := by
  have hprod : 1 < B * (δ * r) := by
    simpa [mul_comm] using (div_lt_iff₀ hB).mp hcut
  by_contra h
  have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt h) hδ.le
  nlinarith

/-- Page 90 printed tau and omega cannot meet the companion cutoff and saved support. -/
theorem decomp677_printed_companion_obstruction :
    ¬ ∃ δ κ : ℝ, 0 < δ ∧ 0 < κ ∧
      1 / (367 : ℝ) < δ * exp (-ω5) ∧
      δ * (1 + 2 * tauBar5) ≤ 1 - κ := by
  rintro ⟨δ, κ, hδ, hκ, hcut, hsave⟩
  have hm := decomp677_companion_margin hδ (by norm_num : (0 : ℝ) < 367) hcut hκ hsave
  have hp := mul_lt_mul_of_pos_left hm (exp_pos ω5)
  have he : exp ω5 * (367 * exp (-ω5)) = 367 := by
    rw [mul_left_comm, ← exp_add]
    simp
  rw [he] at hp
  have := case5_rule_value_gt
  linarith

/-- Pages 88 and 90 with the required index ten cannot meet the first cutoff. -/
theorem decomp677_corrected_first_cutoff_obstruction :
    ¬ ∃ δ κ : ℝ, 1 / (3 : ℝ) < δ ∧ 0 < κ ∧
      δ * (1 + 2 * tauBar10) ≤ 1 - κ := by
  rintro ⟨δ, κ, hδ, hκ, hsave⟩
  have ht := tauBar10_gt_one
  have hδ0 : 0 < δ := by linarith
  have hp := mul_lt_mul_of_pos_left (show (3 : ℝ) < 1 + 2 * tauBar10 by linarith) hδ0
  nlinarith

end LeanLab.Ricci1937
