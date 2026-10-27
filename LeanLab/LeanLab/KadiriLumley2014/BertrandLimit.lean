/-
P0059 arXiv 1407.7902v1 page 1 contrasts Bertrand with short intervals.
This module records why the elementary fallback does not prove a printed row.
AI wrote this Lean code, CODEX task64, 2026-10-25.
-/
import LeanLab.KadiriLumley2014.RowInputs
import LeanLab.KadiriLumley2014.BindingRow

namespace LeanLab.KadiriLumley2014.Task64
open Real

/-- Bertrand gives the new weaker row with denominator two. -/
theorem row_two_of_bertrand : KLRow 4 2 := by
  intro x hx
  let n : ℕ := ⌊x / 2⌋₊
  have hn : 2 ≤ n := Nat.le_floor (by linarith : (2 : ℝ) ≤ x / 2)
  obtain ⟨p, hp, hnp, hp2n⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have hstrict : p < 2 * n := by
    by_contra hh
    have heq : p = 2 * n := by omega
    have hd : 2 ∣ p := by rw [heq]; exact dvd_mul_right _ _
    have hdiv := (Nat.dvd_prime hp).mp hd
    omega
  have hpR : (p : ℝ) < x := by
    have hnR : (n : ℝ) ≤ x / 2 := Nat.floor_le (by linarith)
    have hpR : (p : ℝ) < 2 * n := by exact_mod_cast hstrict
    linarith
  have hlo : x / 2 < p := by
    have hfloor : x / 2 < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have hnpR : (n : ℝ) + 1 ≤ p := by exact_mod_cast hnp
    linarith
  exact ⟨p, hp, by nlinarith, hpR⟩

/-- An interval row can be weakened to a smaller positive denominator.
The reverse direction is not supplied by interval inclusion. -/
theorem row_weaken {x0 x1 D E : ℝ} (h : KLRow x0 D)
    (hx : x0 ≤ x1) (hx1 : 0 ≤ x1) (hE : 0 < E) (hED : E ≤ D) : KLRow x1 E := by
  intro x hxx
  obtain ⟨p, hp, hl, hu⟩ := h x (lt_of_le_of_lt hx hxx)
  have hrecip : 1 / D ≤ 1 / E := one_div_le_one_div_of_le hE hED
  have hxpos : 0 < x := lt_of_le_of_lt hx1 hxx
  refine ⟨p, hp, ?_, hu⟩
  have hm := mul_le_mul_of_nonneg_right hrecip hxpos.le
  nlinarith

/-- The elementary denominator two gives a ceiling below even the row 45 threshold. -/
theorem bertrand_ceiling_lt_exp45 : (2 : ℝ) * evenBase < Real.exp 45 := by
  calc
    (2 : ℝ) * evenBase < (2.7182818283 : ℝ) ^ 45 := by norm_num [evenBase]
    _ ≤ Real.exp 1 ^ 45 := by gcongr; exact Real.exp_one_gt_d9.le
    _ = Real.exp 45 := by rw [← Real.exp_nat_mul]; norm_num

/-- Every printed denominator is strictly greater than the elementary value two. -/
theorem tableTwo_stronger_than_two {r : PrintedRow} (hr : r ∈ tableTwo) :
    2 < r.gapDenom := by
  have h := (tableTwo_denominators r hr).1
  omega

end LeanLab.KadiriLumley2014.Task64
