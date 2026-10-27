/-
P0005 Top 50 table of minimal Goldbach partitions, all 50 rows, zero sorry.
Source: sweet.ua.pt/tos/goldbach.html, the "Top 50" list of S(p), read 2026-10-17. Each pair
(p, n) below satisfies minGB n = p: no prime q < p has n - q prime, and n - p is prime.
NOT proved here: that n is the least even number with minGB n = p, and that no even
n ≤ 4e18 has minGB n > 9781. Both are the authors' computation, cited in OeSHPTables.lean.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.Rows1
import LeanLab.Verifications.Top50.Rows2
import LeanLab.Verifications.Top50.Rows3
import LeanLab.Verifications.Top50.Rows4
import LeanLab.Verifications.Top50.Rows5

namespace LeanLab.Verifications.Top50

open LeanLab.Verifications

/-- The Top 50 table, rank order, as pairs (p, S(p)). -/
def table : List (ℕ × ℕ) := [
    (9781, 3325581707333960528),
    (9629, 2795935116574469638),
    (9341, 906030579562279642),
    (9203, 1348113579429547486),
    (9161, 887123803077837868),
    (9091, 3164069160661844912),
    (9001, 3893009227433420582),
    (8971, 2588356991883139892),
    (8951, 914477234251916254),
    (8941, 555274351556750822),
    (8933, 258549426916149682),
    (8929, 3124359166604172278),
    (8831, 2408339849235552478),
    (8821, 1670956148143530128),
    (8819, 2717573047007392768),
    (8779, 2314720066740314852),
    (8761, 3239057563834411028),
    (8747, 3732282634272065914),
    (8737, 764631157850242766),
    (8731, 2390680417510189328),
    (8719, 1570806049003948202),
    (8707, 2171733197984232734),
    (8699, 2994288576612717268),
    (8693, 2046389249882424466),
    (8689, 1302376001194370768),
    (8681, 771065232370426528),
    (8677, 1928324890105696568),
    (8663, 1262364268433128726),
    (8647, 2725058671961297876),
    (8641, 517711842598037624),
    (8629, 1238289311132116112),
    (8623, 1211650031699177606),
    (8609, 1872496293265949398),
    (8599, 3556579867740673142),
    (8597, 2218708020325772974),
    (8581, 3663298595929927532),
    (8573, 1134059832934400206),
    (8563, 280460266911644252),
    (8543, 2297378342492406154),
    (8539, 941908391556321548),
    (8527, 1295157480539726954),
    (8521, 1176800594358737918),
    (8513, 3431343341961351016),
    (8501, 255329126688555994),
    (8467, 2576438410505131868),
    (8461, 2565581056818705782),
    (8447, 2764135889801480338),
    (8443, 121005022304007026),
    (8431, 2290653905851200938),
    (8419, 1730120042260542848)]

/-- Every row of the Top 50 table: the least Goldbach prime of S(p) is p. -/
theorem table_minGB : ∀ x ∈ table, minGB x.2 = x.1 := by
  intro x hx
  simp only [table, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Rows1.minGB_9781
  · exact Rows1.minGB_9629
  · exact Rows1.minGB_9341
  · exact Rows1.minGB_9203
  · exact Rows1.minGB_9161
  · exact Rows1.minGB_9091
  · exact Rows1.minGB_9001
  · exact Rows1.minGB_8971
  · exact Rows1.minGB_8951
  · exact Rows1.minGB_8941
  · exact Rows2.minGB_8933
  · exact Rows2.minGB_8929
  · exact Rows2.minGB_8831
  · exact Rows2.minGB_8821
  · exact Rows2.minGB_8819
  · exact Rows2.minGB_8779
  · exact Rows2.minGB_8761
  · exact Rows2.minGB_8747
  · exact Rows2.minGB_8737
  · exact Rows2.minGB_8731
  · exact Rows3.minGB_8719
  · exact Rows3.minGB_8707
  · exact Rows3.minGB_8699
  · exact Rows3.minGB_8693
  · exact Rows3.minGB_8689
  · exact Rows3.minGB_8681
  · exact Rows3.minGB_8677
  · exact Rows3.minGB_8663
  · exact Rows3.minGB_8647
  · exact Rows3.minGB_8641
  · exact Rows4.minGB_8629
  · exact Rows4.minGB_8623
  · exact Rows4.minGB_8609
  · exact Rows4.minGB_8599
  · exact Rows4.minGB_8597
  · exact Rows4.minGB_8581
  · exact Rows4.minGB_8573
  · exact Rows4.minGB_8563
  · exact Rows4.minGB_8543
  · exact Rows4.minGB_8539
  · exact Rows5.minGB_8527
  · exact Rows5.minGB_8521
  · exact Rows5.minGB_8513
  · exact Rows5.minGB_8501
  · exact Rows5.minGB_8467
  · exact Rows5.minGB_8461
  · exact Rows5.minGB_8447
  · exact Rows5.minGB_8443
  · exact Rows5.minGB_8431
  · exact Rows5.minGB_8419

/-- Every row is even and at most 4e18. -/
theorem table_range : ∀ x ∈ table, Even x.2 ∧ x.2 ≤ 4 * 10 ^ 18 := by
  intro x hx
  simp only [table, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by norm_num⟩

/-- The 50 values of S(p) are distinct. -/
theorem table_nodup : (table.map Prod.snd).Nodup := by decide +kernel

/-- So at least 50 even n ≤ 4e18 have least Goldbach prime at least 8419, zero sorry. -/
theorem fifty_hard : ∃ S : Finset ℕ, S.card = 50 ∧
    ∀ n ∈ S, Even n ∧ n ≤ 4 * 10 ^ 18 ∧ 8419 ≤ minGB n := by
  refine ⟨(table.map Prod.snd).toFinset, ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup table_nodup]; rfl
  · intro n hn
    rw [List.mem_toFinset, List.mem_map] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    obtain ⟨he, hle⟩ := table_range x hx
    refine ⟨he, hle, ?_⟩
    rw [table_minGB x hx]
    simp only [table, List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

end LeanLab.Verifications.Top50
