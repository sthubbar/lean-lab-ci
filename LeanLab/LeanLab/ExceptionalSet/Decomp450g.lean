import LeanLab.ExceptionalSet.Statements

/-!
Auxiliary dyadic window cover counts in SPLIT_li and SPLIT_lu.
These are elementary bounds for the formal decompositions, not new paper estimates.
No Goldbach or prime distribution input is used.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp450g

open Real

/-- Auxiliary cover estimate shared by the Li and Lu formal splits.
A radius given by a power of the integer half index needs at most a constant
multiple of Y to the complementary power many windows. -/
theorem cover_count (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℕ, 2 ≤ Y →
      ((Y / ⌊(((Y / 2 : ℕ) : ℝ) ^ a)⌋₊ + 1 : ℕ) : ℝ) ≤ C * (Y : ℝ) ^ (1 - a) := by
  refine ⟨2 * (3 : ℝ) ^ a + 1, by positivity, fun Y hY => ?_⟩
  let q : ℝ := ((Y / 2 : ℕ) : ℝ) ^ a
  let r : ℕ := ⌊q⌋₊
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
  have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast (by omega : 1 ≤ Y)
  have hh1 : (1 : ℝ) ≤ (Y / 2 : ℕ) := by exact_mod_cast (by omega : 1 ≤ Y / 2)
  have hq1 : 1 ≤ q := Real.one_le_rpow hh1 ha0
  have hr1 : 1 ≤ r := Nat.le_floor (by simpa using hq1)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hq : q ≤ 2 * (r : ℝ) := by
    have hh := Nat.div_two_lt_floor hq1
    change q / 2 < (r : ℝ) at hh
    linarith
  have hhalf : (Y : ℝ) ≤ 3 * (Y / 2 : ℕ) := by
    exact_mod_cast (by omega : Y ≤ 3 * (Y / 2))
  have hbase : (Y : ℝ) ^ a ≤ (3 : ℝ) ^ a * q := by
    calc
      _ ≤ (3 * ((Y / 2 : ℕ) : ℝ)) ^ a := Real.rpow_le_rpow hYpos.le hhalf ha0
      _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]
  have hden : (Y : ℝ) ^ a ≤ (2 * (3 : ℝ) ^ a) * r := by
    have hm := mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) a)
    nlinarith
  have hYap : 0 < (Y : ℝ) ^ a := Real.rpow_pos_of_pos hYpos a
  have hratio : (Y : ℝ) / r ≤ (2 * (3 : ℝ) ^ a) * (Y : ℝ) ^ (1 - a) := by
    rw [Real.rpow_sub hYpos, Real.rpow_one, ← mul_div_assoc]
    apply (div_le_div_iff₀ hrpos hYap).mpr
    nlinarith [mul_le_mul_of_nonneg_left hden hYpos.le]
  have hcomp : (1 : ℝ) ≤ (Y : ℝ) ^ (1 - a) := Real.one_le_rpow hY1 (by linarith)
  calc
    _ = ((Y / r : ℕ) : ℝ) + 1 := by simp [r, q]
    _ ≤ (Y : ℝ) / r + 1 := add_le_add (Nat.cast_div_le (α := ℝ) (m := Y) (n := r)) (le_rfl : (1 : ℝ) ≤ 1)
    _ ≤ (2 * (3 : ℝ) ^ a) * (Y : ℝ) ^ (1 - a) + (Y : ℝ) ^ (1 - a) :=
      add_le_add hratio hcomp
    _ = _ := by ring

/-- Exact auxiliary cover count in SPLIT_li. -/
theorem li_cover_count_supplied :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℕ, 2 ≤ Y →
      ((Y / ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ))⌋₊ + 1 : ℕ) : ℝ)
        ≤ C * (Y : ℝ) ^ (0.01 : ℝ) := by
  simpa only [show (1 : ℝ) - 0.99 = 0.01 by norm_num] using
    cover_count 0.99 (by norm_num) (by norm_num)

/-- Exact auxiliary cover count in SPLIT_lu. -/
theorem lu_cover_count_supplied :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℕ, 2 ≤ Y →
      ((Y / ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))⌋₊ + 1 : ℕ) : ℝ)
        ≤ C * (Y : ℝ) ^ (0.00021 : ℝ) := by
  simpa only [show (1 : ℝ) - 0.99979 = 0.00021 by norm_num] using
    cover_count 0.99979 (by norm_num) (by norm_num)

end LeanLab.ExceptionalSet.Decomp450g
