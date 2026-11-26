/-
Jia 1996 pages 267 to 269 and 281 to 282.
Source https://doi.org/10.4064/aa-77-3-207-287.
Printed subdomain membership and the first match facts behind Feed564bRiemann, split out
so that each module builds well under the 8 GB memory guide, session S140.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Feed564bRowData

namespace LeanLab.Languasco2004.Feed564bRiemann
open Finset Real Decomp279a Decomp316c Model564 RemainderData564 Feed564bRough
noncomputable section
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 2000000 in
/-- Pages 267 to 269 and 282: printed subdomain 11 lies in region 53 under the first match rule. -/
theorem row9_region (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p) (hq0 : (0 : ℝ) < q)
    (hm : rowMem 9 Y p q) : regionIndex Y p q = 53 := by
  obtain ⟨l1, l2, l3, l4⟩ := rowMem_logs 9 Y hY p q hp0 hq0 hm
  simp only [show numericData 9 0 = (3397/7830 : ℚ) from rfl, show numericData 9 1 = (7/16 : ℚ) from rfl, show numericData 9 2 = (17/12 : ℚ) from rfl, show numericData 9 3 = (-35/12 : ℚ) from rfl, show numericData 9 4 = (17/12 : ℚ) from rfl, show numericData 9 5 = (-29/10 : ℚ) from rfl] at l1 l2 l3 l4
  push_cast at l1 l2 l3 l4
  have hL : 0 < Real.log Y := Real.log_pos hY
  refine regionIndex_eq_of_logs' Y hY p q hp0 hq0 53 ?_ ?_ ?_ ?_ (by simp) ?_
  · simp only [show regionData 53 0 = (3397/7830 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 53 1 = (4/9 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 53 2 = (-35/12 : ℚ) from rfl, show regionData 53 3 = (17/12 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 53 4 = (-29/10 : ℚ) from rfl, show regionData 53 5 = (17/12 : ℚ) from rfl]; push_cast; linarith
  · intro i' hi'
    interval_cases i'
    · exact Or.inl rfl
    · right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 37 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 38 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 39 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 40 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 41 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 42 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 43 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 44 1 = (11/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 45 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 46 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 47 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 48 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 49 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 50 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 51 1 = (3397/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 52 1 = (3397/7830 : ℚ) from rfl]; push_cast; linarith

set_option maxHeartbeats 2000000 in
/-- Pages 267 to 269 and 282: printed subdomain 12 lies in region 53 under the first match rule. -/
theorem row10_region (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p) (hq0 : (0 : ℝ) < q)
    (hm : rowMem 10 Y p q) : regionIndex Y p q = 53 := by
  obtain ⟨l1, l2, l3, l4⟩ := rowMem_logs 10 Y hY p q hp0 hq0 hm
  simp only [show numericData 10 0 = (7/16 : ℚ) from rfl, show numericData 10 1 = (70/159 : ℚ) from rfl, show numericData 10 2 = (17/12 : ℚ) from rfl, show numericData 10 3 = (-35/12 : ℚ) from rfl, show numericData 10 4 = (1/4 : ℚ) from rfl, show numericData 10 5 = (-1/4 : ℚ) from rfl] at l1 l2 l3 l4
  push_cast at l1 l2 l3 l4
  have hL : 0 < Real.log Y := Real.log_pos hY
  refine regionIndex_eq_of_logs' Y hY p q hp0 hq0 53 ?_ ?_ ?_ ?_ (by simp) ?_
  · simp only [show regionData 53 0 = (3397/7830 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 53 1 = (4/9 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 53 2 = (-35/12 : ℚ) from rfl, show regionData 53 3 = (17/12 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 53 4 = (-29/10 : ℚ) from rfl, show regionData 53 5 = (17/12 : ℚ) from rfl]; push_cast; linarith
  · intro i' hi'
    interval_cases i'
    · exact Or.inl rfl
    · right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 37 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 38 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 39 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 40 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 41 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 42 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 43 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 44 1 = (11/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 45 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 46 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 47 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 48 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 49 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 50 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 51 1 = (3397/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 52 1 = (3397/7830 : ℚ) from rfl]; push_cast; linarith

set_option maxHeartbeats 2000000 in
/-- Pages 267 to 269 and 282: printed subdomain 13 lies in region 53 under the first match rule. -/
theorem row11_region (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p) (hq0 : (0 : ℝ) < q)
    (hm : rowMem 11 Y p q) : regionIndex Y p q = 53 := by
  obtain ⟨l1, l2, l3, l4⟩ := rowMem_logs 11 Y hY p q hp0 hq0 hm
  simp only [show numericData 11 0 = (7/16 : ℚ) from rfl, show numericData 11 1 = (70/159 : ℚ) from rfl, show numericData 11 2 = (1/4 : ℚ) from rfl, show numericData 11 3 = (-1/4 : ℚ) from rfl, show numericData 11 4 = (17/12 : ℚ) from rfl, show numericData 11 5 = (-29/10 : ℚ) from rfl] at l1 l2 l3 l4
  push_cast at l1 l2 l3 l4
  have hL : 0 < Real.log Y := Real.log_pos hY
  refine regionIndex_eq_of_logs' Y hY p q hp0 hq0 53 ?_ ?_ ?_ ?_ (by simp) ?_
  · simp only [show regionData 53 0 = (3397/7830 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 53 1 = (4/9 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 53 2 = (-35/12 : ℚ) from rfl, show regionData 53 3 = (17/12 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 53 4 = (-29/10 : ℚ) from rfl, show regionData 53 5 = (17/12 : ℚ) from rfl]; push_cast; linarith
  · intro i' hi'
    interval_cases i'
    · exact Or.inl rfl
    · right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 37 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 38 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 39 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 40 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 41 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 42 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 43 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 44 1 = (11/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 45 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 46 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 47 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 48 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 49 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 50 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 51 1 = (3397/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 52 1 = (3397/7830 : ℚ) from rfl]; push_cast; linarith

set_option maxHeartbeats 2000000 in
/-- Pages 267 to 269 and 282: printed subdomain 14 lies in region 53 under the first match rule. -/
theorem row12_region (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p) (hq0 : (0 : ℝ) < q)
    (hm : rowMem 12 Y p q) : regionIndex Y p q = 53 := by
  obtain ⟨l1, l2, l3, l4⟩ := rowMem_logs 12 Y hY p q hp0 hq0 hm
  simp only [show numericData 12 0 = (70/159 : ℚ) from rfl, show numericData 12 1 = (4/9 : ℚ) from rfl, show numericData 12 2 = (17/12 : ℚ) from rfl, show numericData 12 3 = (-35/12 : ℚ) from rfl, show numericData 12 4 = (17/12 : ℚ) from rfl, show numericData 12 5 = (-29/10 : ℚ) from rfl] at l1 l2 l3 l4
  push_cast at l1 l2 l3 l4
  have hL : 0 < Real.log Y := Real.log_pos hY
  refine regionIndex_eq_of_logs' Y hY p q hp0 hq0 53 ?_ ?_ ?_ ?_ (by simp) ?_
  · simp only [show regionData 53 0 = (3397/7830 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 53 1 = (4/9 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 53 2 = (-35/12 : ℚ) from rfl, show regionData 53 3 = (17/12 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 53 4 = (-29/10 : ℚ) from rfl, show regionData 53 5 = (17/12 : ℚ) from rfl]; push_cast; linarith
  · intro i' hi'
    interval_cases i'
    · exact Or.inl rfl
    · right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 37 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 38 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 39 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 40 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 41 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 42 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 43 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 44 1 = (11/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 45 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 46 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 47 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 48 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 49 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 50 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 51 1 = (3397/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 52 1 = (3397/7830 : ℚ) from rfl]; push_cast; linarith

set_option maxHeartbeats 2000000 in
/-- Pages 267 to 269 and 282: printed subdomain 15 lies in region 66 under the first match rule. -/
theorem row13_region (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p) (hq0 : (0 : ℝ) < q)
    (hm : rowMem 13 Y p q) : regionIndex Y p q = 66 := by
  obtain ⟨l1, l2, l3, l4⟩ := rowMem_logs 13 Y hY p q hp0 hq0 hm
  simp only [show numericData 13 0 = (211/432 : ℚ) from rfl, show numericData 13 1 = (329/669 : ℚ) from rfl, show numericData 13 2 = (89/27 : ℚ) from rfl, show numericData 13 3 = (-58/9 : ℚ) from rfl, show numericData 13 4 = (36/11 : ℚ) from rfl, show numericData 13 5 = (-70/11 : ℚ) from rfl] at l1 l2 l3 l4
  push_cast at l1 l2 l3 l4
  have hL : 0 < Real.log Y := Real.log_pos hY
  refine regionIndex_eq_of_logs' Y hY p q hp0 hq0 66 ?_ ?_ ?_ ?_ (by simp) ?_
  · simp only [show regionData 66 0 = (211/432 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 66 1 = (281/570 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 66 2 = (-58/9 : ℚ) from rfl, show regionData 66 3 = (89/27 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 66 4 = (-70/11 : ℚ) from rfl, show regionData 66 5 = (36/11 : ℚ) from rfl]; push_cast; linarith
  · intro i' hi'
    interval_cases i'
    · exact Or.inl rfl
    · right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 37 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 38 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 39 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 40 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 41 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 42 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 43 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 44 1 = (11/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 45 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 46 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 47 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 48 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 49 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 50 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 51 1 = (3397/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 52 1 = (3397/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 53 1 = (4/9 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 54 1 = (4/9 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 55 1 = (701/1566 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 56 1 = (701/1566 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 57 1 = (41/90 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 58 1 = (41/90 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 59 1 = (17/36 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 60 1 = (16/33 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 61 1 = (307/630 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 62 1 = (307/630 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 63 1 = (211/432 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 64 1 = (211/432 : ℚ) from rfl]; push_cast; linarith
    · right; right; simp only [show regionData 65 4 = (-58/9 : ℚ) from rfl, show regionData 65 5 = (89/27 : ℚ) from rfl]; push_cast; linarith

set_option maxHeartbeats 2000000 in
/-- Pages 267 to 269 and 282: printed subdomain 16 lies in region 66 under the first match rule. -/
theorem row14_region (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p) (hq0 : (0 : ℝ) < q)
    (hm : rowMem 14 Y p q) : regionIndex Y p q = 66 := by
  obtain ⟨l1, l2, l3, l4⟩ := rowMem_logs 14 Y hY p q hp0 hq0 hm
  simp only [show numericData 14 0 = (329/669 : ℚ) from rfl, show numericData 14 1 = (281/570 : ℚ) from rfl, show numericData 14 2 = (89/27 : ℚ) from rfl, show numericData 14 3 = (-58/9 : ℚ) from rfl, show numericData 14 4 = (1/4 : ℚ) from rfl, show numericData 14 5 = (-1/4 : ℚ) from rfl] at l1 l2 l3 l4
  push_cast at l1 l2 l3 l4
  have hL : 0 < Real.log Y := Real.log_pos hY
  refine regionIndex_eq_of_logs' Y hY p q hp0 hq0 66 ?_ ?_ ?_ ?_ (by simp) ?_
  · simp only [show regionData 66 0 = (211/432 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 66 1 = (281/570 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 66 2 = (-58/9 : ℚ) from rfl, show regionData 66 3 = (89/27 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 66 4 = (-70/11 : ℚ) from rfl, show regionData 66 5 = (36/11 : ℚ) from rfl]; push_cast; linarith
  · intro i' hi'
    interval_cases i'
    · exact Or.inl rfl
    · right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 37 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 38 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 39 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 40 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 41 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 42 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 43 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 44 1 = (11/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 45 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 46 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 47 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 48 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 49 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 50 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 51 1 = (3397/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 52 1 = (3397/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 53 1 = (4/9 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 54 1 = (4/9 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 55 1 = (701/1566 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 56 1 = (701/1566 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 57 1 = (41/90 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 58 1 = (41/90 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 59 1 = (17/36 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 60 1 = (16/33 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 61 1 = (307/630 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 62 1 = (307/630 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 63 1 = (211/432 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 64 1 = (211/432 : ℚ) from rfl]; push_cast; linarith
    · right; right; simp only [show regionData 65 4 = (-58/9 : ℚ) from rfl, show regionData 65 5 = (89/27 : ℚ) from rfl]; push_cast; linarith

set_option maxHeartbeats 2000000 in
/-- Pages 267 to 269 and 282: printed subdomain 17 lies in region 66 under the first match rule. -/
theorem row15_region (Y : ℝ) (hY : 1 < Y) (p q : ℕ) (hp0 : (0 : ℝ) < p) (hq0 : (0 : ℝ) < q)
    (hm : rowMem 15 Y p q) : regionIndex Y p q = 66 := by
  obtain ⟨l1, l2, l3, l4⟩ := rowMem_logs 15 Y hY p q hp0 hq0 hm
  simp only [show numericData 15 0 = (329/669 : ℚ) from rfl, show numericData 15 1 = (281/570 : ℚ) from rfl, show numericData 15 2 = (1/4 : ℚ) from rfl, show numericData 15 3 = (-1/4 : ℚ) from rfl, show numericData 15 4 = (36/11 : ℚ) from rfl, show numericData 15 5 = (-70/11 : ℚ) from rfl] at l1 l2 l3 l4
  push_cast at l1 l2 l3 l4
  have hL : 0 < Real.log Y := Real.log_pos hY
  refine regionIndex_eq_of_logs' Y hY p q hp0 hq0 66 ?_ ?_ ?_ ?_ (by simp) ?_
  · simp only [show regionData 66 0 = (211/432 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 66 1 = (281/570 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 66 2 = (-58/9 : ℚ) from rfl, show regionData 66 3 = (89/27 : ℚ) from rfl]; push_cast; linarith
  · simp only [show regionData 66 4 = (-70/11 : ℚ) from rfl, show regionData 66 5 = (36/11 : ℚ) from rfl]; push_cast; linarith
  · intro i' hi'
    interval_cases i'
    · exact Or.inl rfl
    · right; left; simp only [show regionData 1 1 = (89/462 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 2 1 = (41/180 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 3 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 4 1 = (8/33 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 5 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 6 1 = (37/150 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 7 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 8 1 = (17/63 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 9 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 10 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 11 1 = (17/57 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 12 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 13 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 14 1 = (31/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 15 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 16 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 17 1 = (17/54 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 18 1 = (221/693 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 19 1 = (221/693 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 20 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 21 1 = (859/2610 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 22 1 = (109/330 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 23 1 = (109/330 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 24 1 = (151/450 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 25 1 = (151/450 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 26 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 27 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 28 1 = (34/99 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 29 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 30 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 31 1 = (1649/4752 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 32 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 33 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 34 1 = (25/72 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 35 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 36 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 37 1 = (10/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 38 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 39 1 = (617/1620 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 40 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 41 1 = (1823/4725 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 42 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 43 1 = (3041/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 44 1 = (11/27 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 45 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 46 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 47 1 = (34/81 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 48 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 49 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 50 1 = (49/114 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 51 1 = (3397/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 52 1 = (3397/7830 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 53 1 = (4/9 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 54 1 = (4/9 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 55 1 = (701/1566 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 56 1 = (701/1566 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 57 1 = (41/90 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 58 1 = (41/90 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 59 1 = (17/36 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 60 1 = (16/33 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 61 1 = (307/630 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 62 1 = (307/630 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 63 1 = (211/432 : ℚ) from rfl]; push_cast; linarith
    · right; left; simp only [show regionData 64 1 = (211/432 : ℚ) from rfl]; push_cast; linarith
    · right; right; simp only [show regionData 65 4 = (-58/9 : ℚ) from rfl, show regionData 65 5 = (89/27 : ℚ) from rfl]; push_cast; linarith


#print axioms row9_region
#print axioms row10_region
#print axioms row11_region
#print axioms row12_region
#print axioms row13_region
#print axioms row14_region
#print axioms row15_region
end
end LeanLab.Languasco2004.Feed564bRiemann
