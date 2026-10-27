/-
P0017 Richstein 2001, Table 1: all 56 printed values of p(n) / (log² n log log n) PROVED to lie
within half a unit of the fourth decimal, and every p column value PROVED, see Table1.lean.
Run 20261018T1103Z-12430, unit U-0937. AI-written Lean code, Claude, 2026-10-18.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Richstein2001.Table1
import LeanLab.Richstein2001.Ratio1
import LeanLab.Richstein2001.Ratio2
import LeanLab.Richstein2001.Ratio3
import LeanLab.Richstein2001.Ratio4

namespace LeanLab.Richstein2001

/-- Every row of Table 1, third column as printed. -/
theorem table1_ratio_all : ∀ x ∈ table1Ratio,
    ((2 * x.2.2 - 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ ratio x.1 x.2.1 ∧
    ratio x.1 x.2.1 < ((2 * x.2.2 + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) := by
  intro x hx
  simp only [table1Ratio, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ratio_6
  · exact ratio_12
  · exact ratio_30
  · exact ratio_98
  · exact ratio_220
  · exact ratio_308
  · exact ratio_556
  · exact ratio_992
  · exact ratio_2642
  · exact ratio_5372
  · exact ratio_7426
  · exact ratio_43532
  · exact ratio_54244
  · exact ratio_63274
  · exact ratio_113672
  · exact ratio_128168
  · exact ratio_194428
  · exact ratio_194470
  · exact ratio_413572
  · exact ratio_503222
  · exact ratio_1077422
  · exact ratio_3526958
  · exact ratio_3807404
  · exact ratio_10759922
  · exact ratio_24106882
  · exact ratio_27789878
  · exact ratio_37998938
  · exact ratio_60119912
  · exact ratio_113632822
  · exact ratio_187852862
  · exact ratio_335070838
  · exact ratio_419911924
  · exact ratio_721013438
  · exact ratio_1847133842
  · exact ratio_7473202036
  · exact ratio_11001080372
  · exact ratio_12703943222
  · exact ratio_21248558888
  · exact ratio_35884080836
  · exact ratio_105963812462
  · exact ratio_244885595672
  · exact ratio_599533546358
  · exact ratio_3132059294006
  · exact ratio_3620821173302
  · exact ratio_4438327672994
  · exact ratio_5320503815888
  · exact ratio_8342945544436
  · exact ratio_10591605900482
  · exact ratio_12982270197518
  · exact ratio_15197900994218
  · exact ratio_28998050650046
  · exact ratio_46878442766282
  · exact ratio_76903574497118
  · exact ratio_184162477860248
  · exact ratio_217361316706568
  · exact ratio_389965026819938

/-- The largest printed value, 1.6023 at n = 6, PROVED to within half a unit; the GvLtR 1989
bound 1.603 is not exceeded by any row. -/
theorem table1_ratio_lt_1603 : ∀ x ∈ table1Ratio, ratio x.1 x.2.1 < 1.603 := by
  intro x hx
  have hc : x.2.2 ≤ 16023 := by
    revert hx; revert x; decide
  have h := (table1_ratio_all x hx).2
  have : ((2 * x.2.2 + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ 1.603 := by
    rw [div_le_iff₀ (by norm_num)]
    have : ((2 * x.2.2 + 1 : ℕ) : ℝ) ≤ 32047 := by exact_mod_cast (by omega : 2 * x.2.2 + 1 ≤ 32047)
    linarith
  linarith

end LeanLab.Richstein2001
