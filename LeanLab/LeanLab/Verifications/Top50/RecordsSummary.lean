/-
OEIS A025018 and A025019: the n at which the least Goldbach prime p(n) sets a new record, and
the record values, all 69 rows to 3325581707333960528, read 2026-10-17. These are Kai's
A020481 records; A020481(m) is minGB of 2m. PROVED, zero sorry: minGB n = p on every row,
and the record values strictly increase with n. NOT proved: that no even n between two rows
beats the earlier record. Python confirmed that part for every even n up to 2e6 only; above
that it is the searches of Oliveira e Silva, Herzog, Pardi and earlier authors.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.Records1
import LeanLab.Verifications.Top50.Records2
import LeanLab.Verifications.Top50.Records3

namespace LeanLab.Verifications.Top50

open LeanLab.Verifications

/-- A025019 and A025018 rows as pairs (record p, n). -/
def recTable : List (ℕ × ℕ) := [
    (2, 4),
    (3, 6),
    (5, 12),
    (7, 30),
    (19, 98),
    (23, 220),
    (31, 308),
    (47, 556),
    (73, 992),
    (103, 2642),
    (139, 5372),
    (173, 7426),
    (211, 43532),
    (233, 54244),
    (293, 63274),
    (313, 113672),
    (331, 128168),
    (359, 194428),
    (383, 194470),
    (389, 413572),
    (523, 503222),
    (601, 1077422),
    (727, 3526958),
    (751, 3807404),
    (829, 10759922),
    (929, 24106882),
    (997, 27789878),
    (1039, 37998938),
    (1093, 60119912),
    (1163, 113632822),
    (1321, 187852862),
    (1427, 335070838),
    (1583, 419911924),
    (1789, 721013438),
    (1861, 1847133842),
    (1877, 7473202036),
    (1879, 11001080372),
    (2029, 12703943222),
    (2089, 21248558888),
    (2803, 35884080836),
    (3061, 105963812462),
    (3163, 244885595672),
    (3457, 599533546358),
    (3463, 3132059294006),
    (3529, 3620821173302),
    (3613, 4438327672994),
    (3769, 5320503815888),
    (3917, 8342945544436),
    (4003, 10591605900482),
    (4027, 12982270197518),
    (4057, 15197900994218),
    (4327, 28998050650046),
    (4519, 46878442766282),
    (4909, 76903574497118),
    (5077, 184162477860248),
    (5209, 217361316706568),
    (5569, 389965026819938),
    (6469, 1047610575836828),
    (6961, 6253262345930828),
    (7559, 24925556008175266),
    (7753, 31284177910528922),
    (8443, 121005022304007026),
    (8501, 255329126688555994),
    (8933, 258549426916149682),
    (8941, 555274351556750822),
    (9161, 887123803077837868),
    (9341, 906030579562279642),
    (9629, 2795935116574469638),
    (9781, 3325581707333960528)]

/-- Every record row: the least Goldbach prime of n is p. -/
theorem recTable_minGB : ∀ x ∈ recTable, minGB x.2 = x.1 := by
  intro x hx
  simp only [recTable, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Records1.minGB_2
  · exact Records1.minGB_3
  · exact Records1.minGB_5
  · exact Records1.minGB_7
  · exact Records1.minGB_19
  · exact Records1.minGB_23
  · exact Records1.minGB_31
  · exact Records1.minGB_47
  · exact Records1.minGB_73
  · exact Records1.minGB_103
  · exact Records1.minGB_139
  · exact Records1.minGB_173
  · exact Records1.minGB_211
  · exact Records1.minGB_233
  · exact Records1.minGB_293
  · exact Records1.minGB_313
  · exact Records1.minGB_331
  · exact Records1.minGB_359
  · exact Records1.minGB_383
  · exact Records1.minGB_389
  · exact Records1.minGB_523
  · exact Records1.minGB_601
  · exact Records1.minGB_727
  · exact Records2.minGB_751
  · exact Records2.minGB_829
  · exact Records2.minGB_929
  · exact Records2.minGB_997
  · exact Records2.minGB_1039
  · exact Records2.minGB_1093
  · exact Records2.minGB_1163
  · exact Records2.minGB_1321
  · exact Records2.minGB_1427
  · exact Records2.minGB_1583
  · exact Records2.minGB_1789
  · exact Records2.minGB_1861
  · exact Records2.minGB_1877
  · exact Records2.minGB_1879
  · exact Records2.minGB_2029
  · exact Records2.minGB_2089
  · exact Records2.minGB_2803
  · exact Records2.minGB_3061
  · exact Records2.minGB_3163
  · exact Records2.minGB_3457
  · exact Records2.minGB_3463
  · exact Records2.minGB_3529
  · exact Records2.minGB_3613
  · exact Records3.minGB_3769
  · exact Records3.minGB_3917
  · exact Records3.minGB_4003
  · exact Records3.minGB_4027
  · exact Records3.minGB_4057
  · exact Records3.minGB_4327
  · exact Records3.minGB_4519
  · exact Records3.minGB_4909
  · exact Records3.minGB_5077
  · exact Records3.minGB_5209
  · exact Records3.minGB_5569
  · exact Records3.minGB_6469
  · exact Records3.minGB_6961
  · exact Records3.minGB_7559
  · exact Records3.minGB_7753
  · exact Records3.minGB_8443
  · exact Records3.minGB_8501
  · exact Records3.minGB_8933
  · exact Records3.minGB_8941
  · exact Records3.minGB_9161
  · exact Records3.minGB_9341
  · exact Records3.minGB_9629
  · exact Records3.minGB_9781

/-- Both columns strictly increase. -/
theorem recTable_increasing : (recTable.map Prod.fst).Pairwise (· < ·) ∧
    (recTable.map Prod.snd).Pairwise (· < ·) := by decide +kernel

end LeanLab.Verifications.Top50
