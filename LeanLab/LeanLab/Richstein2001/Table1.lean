/-
P0017 Richstein 2001, Verifying the Goldbach conjecture up to 4·10^14, Math. Comp. 70 (2001)
1745 to 1749. Table 1, page 1748: the even n at which the least Goldbach prime p(n) sets a new
record, with p(n) and p(n) / (log² n log log n). Read in Claude in Chrome 2026-10-18 from the AMS
free PDF, run 20261018T1103Z-12430, unit U-0937.
PROVED here, zero sorry: every one of the 56 rows has minGB n = p, and the table is exactly the
OEIS A025018 and A025019 records of the lab's recTable with 6 ≤ n ≤ 4·10^14, in order.
NOT proved: that no even n between two rows beats the earlier record, which is Richstein's
search; nor the range 4·10^14 itself, `Verifications.richstein`, cited.
AI-written Lean code, Claude, 2026-10-18. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.RecordsSummary

namespace LeanLab.Richstein2001

open LeanLab.Verifications LeanLab.Verifications.Top50

/-- Richstein 2001 Table 1, rows (n, p(n)), both columns, 56 rows. -/
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
    (244885595672, 3163),
    (599533546358, 3457),
    (3132059294006, 3463),
    (3620821173302, 3529),
    (4438327672994, 3613),
    (5320503815888, 3769),
    (8342945544436, 3917),
    (10591605900482, 4003),
    (12982270197518, 4027),
    (15197900994218, 4057),
    (28998050650046, 4327),
    (46878442766282, 4519),
    (76903574497118, 4909),
    (184162477860248, 5077),
    (217361316706568, 5209),
    (389965026819938, 5569)]

/-- Table 1 with its third column, p(n) / (log² n log log n), times 10^4 as printed. -/
def table1Ratio : List (ℕ × ℕ × ℕ) := [
    (6, 3, 16023),
    (12, 5, 8896),
    (30, 7, 4943),
    (98, 19, 5935),
    (220, 23, 4691),
    (308, 31, 5408),
    (556, 47, 6380),
    (992, 73, 7939),
    (2642, 103, 8037),
    (5372, 139, 8762),
    (7426, 173, 9956),
    (43532, 211, 7808),
    (54244, 233, 8207),
    (63274, 293, 9977),
    (113672, 313, 9410),
    (128168, 331, 9708),
    (194428, 359, 9685),
    (194470, 383, 10332),
    (413572, 389, 9086),
    (503222, 523, 11784),
    (1077422, 601, 11839),
    (3526958, 727, 11790),
    (3807404, 751, 12034),
    (10759922, 829, 11357),
    (24106882, 929, 11349),
    (27789878, 997, 11943),
    (37998938, 1039, 11928),
    (60119912, 1093, 11807),
    (113632822, 1163, 11575),
    (187852862, 1321, 12350),
    (335070838, 1427, 12440),
    (419911924, 1583, 13436),
    (721013438, 1789, 14262),
    (1847133842, 1861, 13357),
    (7473202036, 1877, 11625),
    (11001080372, 1879, 11191),
    (12703943222, 2029, 11912),
    (21248558888, 2089, 11658),
    (35884080836, 2803, 14873),
    (105963812462, 3061, 14686),
    (244885595672, 3163, 14080),
    (599533546358, 3457, 14243),
    (3132059294006, 3463, 12452),
    (3620821173302, 3529, 12543),
    (4438327672994, 3613, 12637),
    (5320503815888, 3769, 12996),
    (8342945544436, 3917, 13042),
    (10591605900482, 4003, 13086),
    (12982270197518, 4027, 12962),
    (15197900994218, 4057, 12903),
    (28998050650046, 4327, 13114),
    (46878442766282, 4519, 13221),
    (76903574497118, 4909, 13859),
    (184162477860248, 5077, 13476),
    (217361316706568, 5209, 13668),
    (389965026819938, 5569, 14038)]

theorem table1_length : table1.length = 56 := rfl

theorem table1Ratio_cols : table1Ratio.map (fun x => (x.1, x.2.1)) = table1 := by decide +kernel

/-- Table 1 is exactly the record list A025018, A025019 between 6 and 4·10^14. -/
theorem table1_eq_recTable :
    table1 = (recTable.filter (fun x => decide (6 ≤ x.2 ∧ x.2 ≤ 4 * 10 ^ 14))).map
      (fun x => (x.2, x.1)) := by decide +kernel

theorem table1_mem {x : ℕ × ℕ} (hx : x ∈ table1) : (x.2, x.1) ∈ recTable := by
  rw [table1_eq_recTable] at hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact (List.mem_filter.mp hy).1

/-- Every row of Table 1: the least Goldbach prime of n is p. -/
theorem table1_minGB : ∀ x ∈ table1, minGB x.1 = x.2 :=
  fun x hx => recTable_minGB _ (table1_mem hx)

/-- Both columns strictly increase, as a record table must. -/
theorem table1_increasing : (table1.map Prod.fst).Pairwise (· < ·) ∧
    (table1.map Prod.snd).Pairwise (· < ·) := by decide +kernel

theorem minGB_spec {n p : ℕ} (h : minGB n = p) (hp : 0 < p) : p.Prime ∧ (n - p).Prime := by
  classical
  unfold minGB at h
  by_cases hex : ∃ q, q.Prime ∧ (n - q).Prime
  · rw [dif_pos hex] at h
    subst h
    exact Nat.find_spec hex
  · rw [dif_neg hex] at h
    omega

/-- The abstract: the largest p needed below 4·10^14 in Table 1 is 5569, at the partition
389965026819938 = 5569 + 389965026814369. -/
theorem abstract_max : minGB 389965026819938 = 5569 :=
  table1_minGB (389965026819938, 5569) (by decide +kernel)

theorem abstract_partition : (5569 : ℕ).Prime ∧ (389965026814369 : ℕ).Prime ∧
    389965026819938 = 5569 + 389965026814369 := by
  obtain ⟨h1, h2⟩ := minGB_spec abstract_max (by norm_num)
  exact ⟨h1, by simpa using h2, by norm_num⟩

/-- 5569 is the largest p in Table 1. -/
theorem table1_max : ∀ x ∈ table1, x.2 ≤ 5569 := by decide +kernel

end LeanLab.Richstein2001
