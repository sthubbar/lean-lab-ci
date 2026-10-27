/-
AI wrote this Lean code for CODEX task03.
P0074, pages 12 and 13, condition 29 and the convolution window.
Goldbach is open.
-/
import LeanLab.Grimmelt2019.Condition29

namespace LeanLab.Grimmelt2019.MainTerm
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The exact half-open integer interval in the convolution window. -/
theorem Wn_eq_interval {X Y : ℝ} {n : ℤ}
    (hleft : 1 ≤ (n : ℝ) - 2 * Y) (hright : (n : ℝ) - Y ≤ X) :
    Wn X Y n = Finset.Ico ⌈(n : ℝ) - 2 * Y⌉ ⌈(n : ℝ) - Y⌉ := by
  ext m
  simp only [Wn, Prop21.supp, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
  constructor
  · rintro ⟨hm, hl, hr⟩
    exact ⟨Int.ceil_le.mpr hl, Int.lt_ceil.mpr hr⟩
  · rintro ⟨hl, hr⟩
    have hl' : (n : ℝ) - 2 * Y ≤ m := Int.ceil_le.mp hl
    have hr' : (m : ℝ) < n - Y := Int.lt_ceil.mp hr
    refine ⟨⟨?_, Int.le_floor.mpr (by linarith)⟩, hl', hr'⟩
    have : (1 : ℝ) ≤ m := le_trans hleft hl'
    exact_mod_cast this

/-- The number of integers in the window differs from its real length by at most one. -/
theorem Wn_card_error {X Y : ℝ} {n : ℤ} (hY : 0 ≤ Y)
    (hleft : 1 ≤ (n : ℝ) - 2 * Y) (hright : (n : ℝ) - Y ≤ X) :
    |((Wn X Y n).card : ℝ) - Y| ≤ 1 := by
  rw [Wn_eq_interval hleft hright, Int.card_Ico]
  have hab : ⌈(n : ℝ) - 2 * Y⌉ ≤ ⌈(n : ℝ) - Y⌉ := Int.ceil_le_ceil (by linarith)
  have hd : 0 ≤ ⌈(n : ℝ) - Y⌉ - ⌈(n : ℝ) - 2 * Y⌉ := sub_nonneg.mpr hab
  have hcast : (((⌈(n : ℝ) - Y⌉ - ⌈(n : ℝ) - 2 * Y⌉).toNat : ℕ) : ℝ) =
      (⌈(n : ℝ) - Y⌉ : ℝ) - (⌈(n : ℝ) - 2 * Y⌉ : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hd, Int.cast_sub]
  rw [hcast, abs_le]
  have ha1 := Int.le_ceil ((n : ℝ) - 2 * Y)
  have ha2 := Int.ceil_lt_add_one ((n : ℝ) - 2 * Y)
  have hb1 := Int.le_ceil ((n : ℝ) - Y)
  have hb2 := Int.ceil_lt_add_one ((n : ℝ) - Y)
  constructor <;> linarith

#print axioms Wn_eq_interval
#print axioms Wn_card_error
end LeanLab.Grimmelt2019.MainTerm
