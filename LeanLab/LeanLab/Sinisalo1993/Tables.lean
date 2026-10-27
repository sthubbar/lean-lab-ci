/-
P0041 Sinisalo 1993, Checking the Goldbach conjecture up to 4·10^11, Math. Comp. 61 (1993)
931 to 934. Read in Claude in Chrome 2026-10-18 from the AMS free PDF, its OCR text layer decoded
in the page and checked against the page image; run 20261018T1103Z-12430, unit U-0940.
PROVED, zero sorry: Table 1, the 41 champions of p(n) from 6 to 244885595672, is exactly the
lab's A025018 record rows with 6 ≤ n ≤ 4·10^11, each with minGB n = p; both quotient columns
to three decimals in Quot1 to Quot3; Table 2, 67 rows p, S(p), each with minGB S(p) = p, and
S(p) increasing; Section 3, p(n) ≤ 3163 on every Table 1 row.
NOT proved: that the champion lists are complete and each S(p) the least, which is Sinisalo's
search; nor the 4·10^11 range, `Verifications.sinisalo`, cited. Python reproduced both tables
for n up to 4·10^8.
AI-written Lean code, Claude, 2026-10-18. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.RecordsSummary
import LeanLab.Sinisalo1993.Table2_1
import LeanLab.Sinisalo1993.Table2_2
import LeanLab.Sinisalo1993.Table2_3
import LeanLab.Sinisalo1993.Table2_4

namespace LeanLab.Sinisalo1993

open LeanLab.Verifications LeanLab.Verifications.Top50

/-- Sinisalo 1993 Table 1, rows (n, p(n)), 41 rows. -/
def table1 : List (ℕ × ℕ) := [
    (6, 3),
    (12, 5),
    (30, 7),
    (98, 19),
    (220, 23),
    (308, 31),
    (556, 47),
    (992, 73),
    (2642, 103),
    (5372, 139),
    (7426, 173),
    (43532, 211),
    (54244, 233),
    (63274, 293),
    (113672, 313),
    (128168, 331),
    (194428, 359),
    (194470, 383),
    (413572, 389),
    (503222, 523),
    (1077422, 601),
    (3526958, 727),
    (3807404, 751),
    (10759922, 829),
    (24106882, 929),
    (27789878, 997),
    (37998938, 1039),
    (60119912, 1093),
    (113632822, 1163),
    (187852862, 1321),
    (335070838, 1427),
    (419911924, 1583),
    (721013438, 1789),
    (1847133842, 1861),
    (7473202036, 1877),
    (11001080372, 1879),
    (12703943222, 2029),
    (21248558888, 2089),
    (35884080836, 2803),
    (105963812462, 3061),
    (244885595672, 3163)]

theorem table1_length : table1.length = 41 := rfl

/-- Table 1 is exactly the record list A025018, A025019 between 6 and 4·10^11. -/
theorem table1_eq_recTable :
    table1 = (recTable.filter (fun x => decide (6 ≤ x.2 ∧ x.2 ≤ 4 * 10 ^ 11))).map
      (fun x => (x.2, x.1)) := by decide +kernel

theorem table1_minGB : ∀ x ∈ table1, minGB x.1 = x.2 := by
  intro x hx
  rw [table1_eq_recTable] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact recTable_minGB _ (List.mem_filter.mp hy).1

/-- Section 3: on Table 1, p(n) ≤ 3163, attained at the last row. -/
theorem table1_le_3163 : ∀ x ∈ table1, x.2 ≤ 3163 := by decide +kernel

theorem minGB_244885595672 : minGB 244885595672 = 3163 :=
  table1_minGB (244885595672, 3163) (by decide +kernel)

/-- Sinisalo 1993 Table 2, rows (p, S(p)), 67 rows; the 68th, p = 2441, has S(p) above 4·10^11. -/
def table2 : List (ℕ × ℕ) := [
    (3, 6),
    (5, 12),
    (7, 30),
    (11, 124),
    (17, 418),
    (37, 1274),
    (53, 2512),
    (59, 3526),
    (71, 4618),
    (83, 7432),
    (89, 12778),
    (101, 26098),
    (131, 34192),
    (149, 37768),
    (167, 59914),
    (179, 88786),
    (191, 97768),
    (197, 112558),
    (223, 221942),
    (257, 237544),
    (263, 485326),
    (281, 642358),
    (317, 686638),
    (347, 1042078),
    (379, 1172918),
    (401, 2041402),
    (419, 2406448),
    (463, 4288574),
    (487, 4938848),
    (509, 9292156),
    (521, 14341888),
    (569, 17726098),
    (593, 20757292),
    (659, 32507242),
    (739, 34362758),
    (743, 37890844),
    (761, 49358128),
    (773, 68788066),
    (839, 129796642),
    (853, 144516902),
    (911, 150386932),
    (941, 206892484),
    (977, 247013164),
    (1031, 299434108),
    (1049, 379410652),
    (1061, 554463808),
    (1091, 678546502),
    (1097, 1168888534),
    (1283, 1673268292),
    (1301, 1927528888),
    (1327, 2331465314),
    (1429, 2538833642),
    (1439, 2816593312),
    (1451, 4407165118),
    (1493, 5801828806),
    (1559, 8946630856),
    (1571, 21439965412),
    (1787, 26070202114),
    (1811, 30325742068),
    (1867, 30834371756),
    (1873, 32652627542),
    (1889, 44460316708),
    (1907, 64243962808),
    (1997, 65334725368),
    (2027, 113843130358),
    (2153, 244808993116),
    (2351, 384619217512)]

theorem table2_length : table2.length = 67 := rfl

/-- Every row of Table 2: the least Goldbach prime of S(p) is p. -/
theorem table2_minGB : ∀ x ∈ table2, minGB x.2 = x.1 := by
  intro x hx
  simp only [table2, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact minGB_S_3
  · exact minGB_S_5
  · exact minGB_S_7
  · exact minGB_S_11
  · exact minGB_S_17
  · exact minGB_S_37
  · exact minGB_S_53
  · exact minGB_S_59
  · exact minGB_S_71
  · exact minGB_S_83
  · exact minGB_S_89
  · exact minGB_S_101
  · exact minGB_S_131
  · exact minGB_S_149
  · exact minGB_S_167
  · exact minGB_S_179
  · exact minGB_S_191
  · exact minGB_S_197
  · exact minGB_S_223
  · exact minGB_S_257
  · exact minGB_S_263
  · exact minGB_S_281
  · exact minGB_S_317
  · exact minGB_S_347
  · exact minGB_S_379
  · exact minGB_S_401
  · exact minGB_S_419
  · exact minGB_S_463
  · exact minGB_S_487
  · exact minGB_S_509
  · exact minGB_S_521
  · exact minGB_S_569
  · exact minGB_S_593
  · exact minGB_S_659
  · exact minGB_S_739
  · exact minGB_S_743
  · exact minGB_S_761
  · exact minGB_S_773
  · exact minGB_S_839
  · exact minGB_S_853
  · exact minGB_S_911
  · exact minGB_S_941
  · exact minGB_S_977
  · exact minGB_S_1031
  · exact minGB_S_1049
  · exact minGB_S_1061
  · exact minGB_S_1091
  · exact minGB_S_1097
  · exact minGB_S_1283
  · exact minGB_S_1301
  · exact minGB_S_1327
  · exact minGB_S_1429
  · exact minGB_S_1439
  · exact minGB_S_1451
  · exact minGB_S_1493
  · exact minGB_S_1559
  · exact minGB_S_1571
  · exact minGB_S_1787
  · exact minGB_S_1811
  · exact minGB_S_1867
  · exact minGB_S_1873
  · exact minGB_S_1889
  · exact minGB_S_1907
  · exact minGB_S_1997
  · exact minGB_S_2027
  · exact minGB_S_2153
  · exact minGB_S_2351

/-- Both columns of Table 2 increase, as a champion list of S must. -/
theorem table2_increasing : (table2.map Prod.fst).Pairwise (· < ·) ∧
    (table2.map Prod.snd).Pairwise (· < ·) := by decide +kernel

/-- The rows of Table 2 below 4·10^11 with S(p) also a record of p(n) are three, p = 3, 5, 7. -/
theorem table2_records : (table2.filter (fun x => decide ((x.2, x.1) ∈ table1))).map Prod.fst =
    [3, 5, 7] := by decide +kernel

end LeanLab.Sinisalo1993
