/-
P0005 Oliveira e Silva, Herzog, Pardi 2014, Table 9, page 2051, record-breaking first
occurrences P(g) of a prime gap g, part 3: each row IsGapAt P(g) g, that is P(g) and
P(g) + g are consecutive primes. Divisors and Pratt certificates by Python, checked by the
kernel. That P(g) is the FIRST gap of size g is the authors' search, cited; the lab's Python
reproduced the 42 rows below 10^9. Run 20261018T1103Z-12430, unit U-0946.
AI-written Lean code, Claude, 2026-10-18. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.GapsBase

namespace LeanLab.OeSHP2014

open LeanLab.Verifications LeanLab.Verifications.Top50.Gaps
open LeanLab.Verifications.Pratt (pB)

set_option Elab.async false

theorem p18642539 : Nat.Prime 18642539 := by
  refine Pratt.pratt 18642539 2 [(2, 1), (53, 1), (175873, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p20411689 : Nat.Prime 20411689 := by
  refine Pratt.pratt 20411689 17 [(2, 3), (3, 1), (11, 1), (77317, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p25255733 : Nat.Prime 25255733 := by
  refine Pratt.pratt 25255733 3 [(2, 2), (47, 1), (134339, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p52458149 : Nat.Prime 52458149 := by
  refine Pratt.pratt 52458149 2 [(2, 2), (379, 1), (34603, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p64454149 : Nat.Prime 64454149 := by
  refine Pratt.pratt 64454149 6 [(2, 2), (3, 2), (11, 1), (37, 1), (53, 1), (83, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p67769407 : Nat.Prime 67769407 := by
  refine Pratt.pratt 67769407 3 [(2, 1), (3, 3), (59, 1), (89, 1), (239, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p108131561 : Nat.Prime 108131561 := by
  refine Pratt.pratt 108131561 6 [(2, 3), (5, 1), (17, 1), (159017, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p121767133 : Nat.Prime 121767133 := by
  refine Pratt.pratt 121767133 5 [(2, 2), (3, 1), (31, 1), (327331, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p135582107 : Nat.Prime 135582107 := by
  refine Pratt.pratt 135582107 2 [(2, 1), (11, 1), (17, 1), (227, 1), (1597, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p141292633 : Nat.Prime 141292633 := by
  refine Pratt.pratt 141292633 10 [(2, 3), (3, 1), (13, 1), (191, 1), (2371, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p145762249 : Nat.Prime 145762249 := by
  refine Pratt.pratt 145762249 7 [(2, 3), (3, 1), (31, 1), (107, 1), (1831, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p372850781 : Nat.Prime 372850781 := by
  refine Pratt.pratt 372850781 2 [(2, 2), (5, 1), (18642539, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p18642539
theorem p384412837 : Nat.Prime 384412837 := by
  refine Pratt.pratt 384412837 2 [(2, 2), (3, 1), (269, 1), (119087, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p820678769 : Nat.Prime 820678769 := by
  refine Pratt.pratt 820678769 15 [(2, 4), (7, 1), (13, 1), (83, 1), (6791, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p2237104687 : Nat.Prime 2237104687 := by
  refine Pratt.pratt 2237104687 3 [(2, 1), (3, 1), (372850781, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p372850781
theorem p2357881993 : Nat.Prime 2357881993 := by
  refine Pratt.pratt 2357881993 5 [(2, 3), (3, 2), (1783, 1), (18367, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p2357882257 : Nat.Prime 2357882257 := by
  refine Pratt.pratt 2357882257 10 [(2, 4), (3, 1), (3733, 1), (13159, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p4260928601 : Nat.Prime 4260928601 := by
  refine Pratt.pratt 4260928601 6 [(2, 3), (5, 2), (19, 1), (1121297, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p4260928879 : Nat.Prime 4260928879 := by
  refine Pratt.pratt 4260928879 3 [(2, 1), (3, 2), (29, 1), (8162699, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p4743983581 : Nat.Prime 4743983581 := by
  refine Pratt.pratt 4743983581 2 [(2, 2), (3, 1), (5, 1), (7, 1), (1381, 1), (8179, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p5692630189 : Nat.Prime 5692630189 := by
  refine Pratt.pratt 5692630189 2 [(2, 2), (3, 1), (7, 1), (67769407, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p67769407
theorem p5692630483 : Nat.Prime 5692630483 := by
  refine Pratt.pratt 5692630483 2 [(2, 1), (3, 3), (7, 1), (11, 1), (709, 1), (1931, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p5979620827 : Nat.Prime 5979620827 := by
  refine Pratt.pratt 5979620827 2 [(2, 1), (3, 3), (239, 1), (463321, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p6565430153 : Nat.Prime 6565430153 := by
  refine Pratt.pratt 6565430153 3 [(2, 3), (820678769, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p820678769
theorem p6669359821 : Nat.Prime 6669359821 := by
  refine Pratt.pratt 6669359821 6 [(2, 2), (3, 2), (5, 1), (401, 1), (92399, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p8650524583 : Nat.Prime 8650524583 := by
  refine Pratt.pratt 8650524583 3 [(2, 1), (3, 2), (7, 2), (9807851, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p8650524881 : Nat.Prime 8650524881 := by
  refine Pratt.pratt 8650524881 7 [(2, 4), (5, 1), (108131561, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p108131561
theorem p8948418749 : Nat.Prime 8948418749 := by
  refine Pratt.pratt 8948418749 2 [(2, 2), (2237104687, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p2237104687
theorem p8948419063 : Nat.Prime 8948419063 := by
  refine Pratt.pratt 8948419063 3 [(2, 1), (3, 1), (11, 1), (135582107, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p135582107
theorem p12109172293 : Nat.Prime 12109172293 := by
  refine Pratt.pratt 12109172293 6 [(2, 2), (3, 2), (7, 1), (3967, 1), (12113, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p12109172609 : Nat.Prime 12109172609 := by
  refine Pratt.pratt 12109172609 3 [(2, 7), (13, 1), (7277147, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p13086861181 : Nat.Prime 13086861181 := by
  refine Pratt.pratt 13086861181 2 [(2, 2), (3, 1), (5, 1), (911, 1), (239423, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p13086861509 : Nat.Prime 13086861509 := by
  refine Pratt.pratt 13086861509 3 [(2, 2), (7, 1), (59, 1), (821, 1), (9649, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p17682990503 : Nat.Prime 17682990503 := by
  refine Pratt.pratt 17682990503 5 [(2, 1), (23, 1), (384412837, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p384412837
theorem p25038161611 : Nat.Prime 25038161611 := by
  refine Pratt.pratt 25038161611 7 [(2, 1), (3, 1), (5, 1), (7, 2), (11, 1), (1548433, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p30827138509 : Nat.Prime 30827138509 := by
  refine Pratt.pratt 30827138509 6 [(2, 2), (3, 2), (47, 1), (131, 1), (139079, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p30827138843 : Nat.Prime 30827138843 := by
  refine Pratt.pratt 30827138843 2 [(2, 1), (173, 1), (4057, 1), (21961, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p35877724601 : Nat.Prime 35877724601 := by
  refine Pratt.pratt 35877724601 3 [(2, 3), (5, 2), (53, 1), (3384691, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p35877724963 : Nat.Prime 35877724963 := by
  refine Pratt.pratt 35877724963 2 [(2, 1), (3, 1), (5979620827, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p5979620827
theorem p51430518413 : Nat.Prime 51430518413 := by
  refine Pratt.pratt 51430518413 3 [(2, 2), (7, 1), (13, 1), (141292633, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p141292633
theorem p51430518781 : Nat.Prime 51430518781 := by
  refine Pratt.pratt 51430518781 2 [(2, 2), (3, 1), (5, 1), (131, 1), (6543323, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p59942358571 : Nat.Prime 59942358571 := by
  refine Pratt.pratt 59942358571 10 [(2, 1), (3, 1), (5, 1), (31, 1), (64454149, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p64454149
theorem p59942358941 : Nat.Prime 59942358941 := by
  refine Pratt.pratt 59942358941 3 [(2, 2), (5, 1), (191, 1), (331, 1), (47407, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p61803193577 : Nat.Prime 61803193577 := by
  refine Pratt.pratt 61803193577 3 [(2, 3), (53, 1), (145762249, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p145762249
theorem p156798792223 : Nat.Prime 156798792223 := by
  refine Pratt.pratt 156798792223 3 [(2, 1), (3, 1), (17, 1), (3323, 1), (462607, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p156798792611 : Nat.Prime 156798792611 := by
  refine Pratt.pratt 156798792611 2 [(2, 1), (5, 1), (61, 1), (149, 1), (829, 1), (2081, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p280974865361 : Nat.Prime 280974865361 := by
  refine Pratt.pratt 280974865361 13 [(2, 4), (5, 1), (7, 1), (37, 1), (101, 1), (134263, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p280974865783 : Nat.Prime 280974865783 := by
  refine Pratt.pratt 280974865783 6 [(2, 1), (3, 1), (13, 1), (8923, 1), (403703, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p367459059871 : Nat.Prime 367459059871 := by
  refine Pratt.pratt 367459059871 6 [(2, 1), (3, 3), (5, 1), (7, 1), (1483, 1), (131101, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p367459060307 : Nat.Prime 367459060307 := by
  refine Pratt.pratt 367459060307 2 [(2, 1), (13, 1), (43, 1), (1553, 1), (211639, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p417470554687 : Nat.Prime 417470554687 := by
  refine Pratt.pratt 417470554687 5 [(2, 1), (3, 1), (23, 1), (2579, 1), (1172993, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p417470555129 : Nat.Prime 417470555129 := by
  refine Pratt.pratt 417470555129 6 [(2, 3), (11, 1), (4743983581, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p4743983581
theorem p466855187471 : Nat.Prime 466855187471 := by
  refine Pratt.pratt 466855187471 19 [(2, 1), (5, 1), (7, 1), (6669359821, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p6669359821
theorem p466855187923 : Nat.Prime 466855187923 := by
  refine Pratt.pratt 466855187923 2 [(2, 1), (3, 3), (71, 1), (121767133, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p121767133
theorem p565855695631 : Nat.Prime 565855695631 := by
  refine Pratt.pratt 565855695631 15 [(2, 1), (3, 2), (5, 1), (41, 1), (71, 1), (643, 1), (3359, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p565855696097 : Nat.Prime 565855696097 := by
  refine Pratt.pratt 565855696097 3 [(2, 5), (17682990503, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p17682990503
theorem p681753256133 : Nat.Prime 681753256133 := by
  refine Pratt.pratt 681753256133 2 [(2, 2), (13, 1), (11113, 1), (1179757, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p681753256603 : Nat.Prime 681753256603 := by
  refine Pratt.pratt 681753256603 2 [(2, 1), (3, 1), (11, 1), (409, 1), (25255733, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p25255733
theorem p865244709607 : Nat.Prime 865244709607 := by
  refine Pratt.pratt 865244709607 3 [(2, 1), (3, 1), (2749, 1), (52458149, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p52458149
theorem p865244710079 : Nat.Prime 865244710079 := by
  refine Pratt.pratt 865244710079 7 [(2, 1), (7, 1), (61803193577, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p61803193577
theorem p1051602787181 : Nat.Prime 1051602787181 := by
  refine Pratt.pratt 1051602787181 2 [(2, 2), (5, 1), (11, 1), (2699, 1), (1771031, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p1051602787663 : Nat.Prime 1051602787663 := by
  refine Pratt.pratt 1051602787663 5 [(2, 1), (3, 1), (7, 1), (25038161611, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p25038161611
theorem p1275363152099 : Nat.Prime 1275363152099 := by
  refine Pratt.pratt 1275363152099 2 [(2, 1), (7, 1), (4463, 1), (20411689, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p20411689
theorem p1275363152587 : Nat.Prime 1275363152587 := by
  refine Pratt.pratt 1275363152587 2 [(2, 1), (3, 4), (97, 1), (281, 1), (367, 1), (787, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p1339347750707 : Nat.Prime 1339347750707 := by
  refine Pratt.pratt 1339347750707 2 [(2, 1), (7, 1), (59, 1), (113, 1), (1063, 1), (13499, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p1339347751213 : Nat.Prime 1339347751213 := by
  refine Pratt.pratt 1339347751213 2 [(2, 2), (3, 1), (17, 1), (6565430153, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p6565430153

def gds_264 : List ℕ := [
    2, 3, 2, 17, 2, 11, 2, 3, 2, 347, 2, 5, 2, 3, 2, 7,
    2, 83, 2, 3, 2, 5, 2, 37, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 21383, 2, 827, 2, 3, 2, 13, 2, 5, 2, 3, 2, 4289, 2, 31,
    2, 3, 2, 5, 2, 293, 2, 3, 2, 7, 2, 23, 2, 3, 2, 6229,
    2, 13, 2, 3, 2, 151, 2, 5, 2, 3, 2, 113, 2, 23719, 2, 3,
    2, 5, 2, 59, 2, 3, 2, 43, 2, 19, 2, 3, 2, 11, 2, 487,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 16699, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 13, 2, 181, 2, 3, 2, 9629, 2, 443, 2, 3,
    2, 2467, 2, 5, 2, 3, 2, 719, 2, 11, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 331, 2, 1361, 2, 3, 2, 4603, 2, 7, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 19, 2, 41, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 337, 2, 23509, 2, 3, 2, 7, 2, 53, 2, 3, 2, 1193, 2, 5,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 17,
    2, 137, 2, 3, 2, 29, 2, 353, 2, 3, 2, 971, 2, 5, 2, 3,
    2, 7, 2, 173, 2, 3, 2, 5, 2, 31, 2, 3, 2, 131, 2, 7,
    2, 3, 2, 23, 2, 37, 2, 3, 2, 41, 2, 5, 2, 3, 2, 223,
    2, 89, 2, 3, 2, 5, 2]

/-- Table 9 row: the prime after 2357881993 is 2357881993 + 264. -/
theorem gap9_264 : IsGapAt 2357881993 264 :=
  isGapAt_of 2357881993 264 (p2357881993) (by show Nat.Prime 2357882257; exact p2357882257) gds_264 (by decide +kernel)

def gds_278 : List ℕ := [
    2, 17, 2, 3, 2, 13, 2, 7, 2, 3, 2, 127, 2, 5, 2, 3,
    2, 19, 2, 37, 2, 3, 2, 5, 2, 1669, 2, 3, 2, 853, 2, 13,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 2683, 2, 5, 2, 3, 2, 41,
    2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 131, 2, 3,
    2, 89, 2, 3853, 2, 3, 2, 257, 2, 5, 2, 3, 2, 7, 2, 167,
    2, 3, 2, 5, 2, 23, 2, 3, 2, 563, 2, 7, 2, 3, 2, 227,
    2, 28493, 2, 3, 2, 31, 2, 5, 2, 3, 2, 179, 2, 13, 2, 3,
    2, 5, 2, 67, 2, 3, 2, 7, 2, 42829, 2, 3, 2, 11, 2, 59,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 17, 2, 2617, 2, 3, 2, 5,
    2, 24137, 2, 3, 2, 61, 2, 79, 2, 3, 2, 953, 2, 15091, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 37, 2, 11, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 43, 2, 181, 2, 3, 2, 11213, 2, 13, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 53, 2, 37847, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 23899, 2, 41, 2, 3, 2, 2801, 2, 7, 2, 3, 2, 103, 2, 5,
    2, 3, 2, 307, 2, 3919, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13,
    2, 37, 2, 3, 2, 7, 2, 29, 2, 3, 2, 4421, 2, 5, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 23, 2, 61,
    2, 3, 2, 643, 2]

/-- Table 9 row: the prime after 4260928601 is 4260928601 + 278. -/
theorem gap9_278 : IsGapAt 4260928601 278 :=
  isGapAt_of 4260928601 278 (p4260928601) (by show Nat.Prime 4260928879; exact p4260928879) gds_278 (by decide +kernel)

def gds_294 : List ℕ := [
    2, 3, 2, 89, 2, 5, 2, 3, 2, 41, 2, 53, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 977, 2, 439, 2, 3, 2, 17, 2, 2731, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 11, 2, 631, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 3407, 2, 397, 2, 3, 2, 1613, 2, 23, 2, 3, 2, 1019,
    2, 5, 2, 3, 2, 2647, 2, 19, 2, 3, 2, 5, 2, 113, 2, 3,
    2, 47, 2, 11, 2, 3, 2, 67, 2, 7, 2, 3, 2, 131, 2, 5,
    2, 3, 2, 887, 2, 4547, 2, 3, 2, 5, 2, 9743, 2, 3, 2, 37,
    2, 1163, 2, 3, 2, 7, 2, 7829, 2, 3, 2, 29, 2, 5, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 5, 2, 6091, 2, 3, 2, 359, 2, 13,
    2, 3, 2, 19, 2, 11, 2, 3, 2, 239, 2, 5, 2, 3, 2, 7,
    2, 281, 2, 3, 2, 5, 2, 2237, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 97, 2, 167, 2, 3, 2, 38953, 2, 5, 2, 3, 2, 43, 2, 911,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 241, 2, 3, 2, 197,
    2, 59, 2, 3, 2, 71, 2, 5, 2, 3, 2, 31, 2, 13, 2, 3,
    2, 5, 2, 199, 2, 3, 2, 17, 2, 499, 2, 3, 2, 11, 2, 29,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 137, 2, 257, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 19, 2, 1483, 2, 3, 2, 181, 2, 47, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 743, 2, 11, 2, 3, 2, 5, 2, 35257,
    2, 3, 2, 6661, 2]

/-- Table 9 row: the prime after 5692630189 is 5692630189 + 294. -/
theorem gap9_294 : IsGapAt 5692630189 294 :=
  isGapAt_of 5692630189 294 (p5692630189) (by show Nat.Prime 5692630483; exact p5692630483) gds_294 (by decide +kernel)

def gds_298 : List ℕ := [
    2, 3, 2, 179, 2, 7, 2, 3, 2, 73547, 2, 5, 2, 3, 2, 59,
    2, 73, 2, 3, 2, 5, 2, 53101, 2, 3, 2, 19, 2, 17, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 5479, 2, 7,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 11, 2, 409, 2, 3, 2, 17,
    2, 13, 2, 3, 2, 257, 2, 5, 2, 3, 2, 7, 2, 433, 2, 3,
    2, 5, 2, 313, 2, 3, 2, 359, 2, 7, 2, 3, 2, 3301, 2, 6271,
    2, 3, 2, 167, 2, 5, 2, 3, 2, 52363, 2, 53, 2, 3, 2, 5,
    2, 23813, 2, 3, 2, 7, 2, 67, 2, 3, 2, 11, 2, 173, 2, 3,
    2, 431, 2, 5, 2, 3, 2, 7211, 2, 197, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 103, 2, 23, 2, 3, 2, 149, 2, 10853, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 631, 2, 19, 2, 3, 2, 71, 2, 41, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 13, 2, 337, 2, 3, 2, 5, 2, 1171, 2, 3, 2, 821,
    2, 47, 2, 3, 2, 31, 2, 7, 2, 3, 2, 36109, 2, 5, 2, 3,
    2, 38851, 2, 29, 2, 3, 2, 5, 2, 11, 2, 3, 2, 113, 2, 1223,
    2, 3, 2, 7, 2, 137, 2, 3, 2, 769, 2, 5, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 5, 2, 661, 2, 3, 2, 17, 2, 37, 2, 3,
    2, 13, 2, 31, 2, 3, 2, 61, 2, 5, 2, 3, 2, 7, 2, 23,
    2, 3, 2, 5, 2, 19, 2, 3, 2]

/-- Table 9 row: the prime after 8650524583 is 8650524583 + 298. -/
theorem gap9_298 : IsGapAt 8650524583 298 :=
  isGapAt_of 8650524583 298 (p8650524583) (by show Nat.Prime 8650524881; exact p8650524881) gds_298 (by decide +kernel)

def gds_314 : List ℕ := [
    2, 51971, 2, 3, 2, 5, 2, 71, 2, 3, 2, 1747, 2, 67, 2, 3,
    2, 73, 2, 227, 2, 3, 2, 7, 2, 5, 2, 3, 2, 1789, 2, 677,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 2069, 2, 3, 2, 41,
    2, 4259, 2, 3, 2, 653, 2, 5, 2, 3, 2, 11, 2, 113, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 251, 2, 53, 2, 3, 2, 373, 2, 7,
    2, 3, 2, 773, 2, 5, 2, 3, 2, 4219, 2, 20693, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 61, 2, 11, 2, 3, 2, 7, 2, 103, 2, 3,
    2, 31, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 107, 2, 37, 2, 3, 2, 607, 2, 79973, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 101, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 3727, 2, 11, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 53, 2, 66347, 2, 3, 2, 5, 2, 89, 2, 3, 2, 7,
    2, 157, 2, 3, 2, 13, 2, 167, 2, 3, 2, 1303, 2, 5, 2, 3,
    2, 29, 2, 19, 2, 3, 2, 5, 2, 317, 2, 3, 2, 47, 2, 13,
    2, 3, 2, 76081, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 8707,
    2, 83, 2, 3, 2, 5, 2, 7, 2, 3, 2, 1129, 2, 151, 2, 3,
    2, 11, 2, 5107, 2, 3, 2, 17, 2, 5, 2, 3, 2, 509, 2, 59,
    2, 3, 2, 5, 2, 48799, 2, 3, 2, 23, 2, 79, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 41, 2, 5, 2, 3, 2, 31, 2, 11, 2, 3,
    2, 5, 2, 463, 2, 3, 2, 2129, 2]

/-- Table 9 row: the prime after 8948418749 is 8948418749 + 314. -/
theorem gap9_314 : IsGapAt 8948418749 314 :=
  isGapAt_of 8948418749 314 (p8948418749) (by show Nat.Prime 8948419063; exact p8948419063) gds_314 (by decide +kernel)

def gds_316 : List ℕ := [
    2, 3, 2, 53, 2, 7, 2, 3, 2, 137, 2, 5, 2, 3, 2, 13,
    2, 29717, 2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2, 887, 2, 3,
    2, 7, 2, 73, 2, 3, 2, 71, 2, 5, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 5, 2, 41, 2, 3, 2, 24203, 2, 31, 2, 3, 2, 1759,
    2, 19, 2, 3, 2, 163, 2, 5, 2, 3, 2, 7, 2, 1559, 2, 3,
    2, 5, 2, 79, 2, 3, 2, 349, 2, 7, 2, 3, 2, 13, 2, 3469,
    2, 3, 2, 15913, 2, 5, 2, 3, 2, 2687, 2, 29, 2, 3, 2, 5,
    2, 56591, 2, 3, 2, 7, 2, 13, 2, 3, 2, 379, 2, 647, 2, 3,
    2, 43, 2, 5, 2, 3, 2, 41, 2, 76603, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 20113, 2, 103, 2, 3, 2, 37, 2, 11, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 29, 2, 131, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 11, 2, 19, 2, 3, 2, 31, 2, 1709, 2, 3, 2, 1117, 2, 5,
    2, 3, 2, 241, 2, 13, 2, 3, 2, 5, 2, 101, 2, 3, 2, 4451,
    2, 23, 2, 3, 2, 8069, 2, 7, 2, 3, 2, 24091, 2, 5, 2, 3,
    2, 191, 2, 37, 2, 3, 2, 5, 2, 3463, 2, 3, 2, 31181, 2, 2063,
    2, 3, 2, 7, 2, 17, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 5, 2, 197, 2, 3, 2, 13241, 2, 6131, 2, 3,
    2, 59, 2, 13, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 89, 2, 7, 2, 3, 2, 347,
    2, 16111, 2, 3, 2, 11, 2, 5, 2, 3, 2]

/-- Table 9 row: the prime after 12109172293 is 12109172293 + 316. -/
theorem gap9_316 : IsGapAt 12109172293 316 :=
  isGapAt_of 12109172293 316 (p12109172293) (by show Nat.Prime 12109172609; exact p12109172609) gds_316 (by decide +kernel)

def gds_328 : List ℕ := [
    2, 3, 2, 5, 2, 37, 2, 3, 2, 30559, 2, 7, 2, 3, 2, 14387,
    2, 23459, 2, 3, 2, 13, 2, 5, 2, 3, 2, 79, 2, 19, 2, 3,
    2, 5, 2, 41, 2, 3, 2, 7, 2, 109, 2, 3, 2, 11, 2, 13,
    2, 3, 2, 29, 2, 5, 2, 3, 2, 17, 2, 23, 2, 3, 2, 5,
    2, 563, 2, 3, 2, 93131, 2, 823, 2, 3, 2, 3461, 2, 139, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 19681, 2, 11, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 13, 2, 53, 2, 3, 2, 19, 2, 241, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 41, 2, 21101, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 65963, 2, 167, 2, 3, 2, 2027, 2, 7, 2, 3, 2, 82723, 2, 5,
    2, 3, 2, 73, 2, 59, 2, 3, 2, 5, 2, 11, 2, 3, 2, 17,
    2, 26209, 2, 3, 2, 7, 2, 29, 2, 3, 2, 4637, 2, 5, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 5, 2, 79, 2, 3, 2, 61, 2, 47,
    2, 3, 2, 1031, 2, 23, 2, 3, 2, 101719, 2, 5, 2, 3, 2, 7,
    2, 307, 2, 3, 2, 5, 2, 3067, 2, 3, 2, 19, 2, 7, 2, 3,
    2, 29, 2, 17, 2, 3, 2, 577, 2, 5, 2, 3, 2, 2521, 2, 103,
    2, 3, 2, 5, 2, 359, 2, 3, 2, 7, 2, 383, 2, 3, 2, 13,
    2, 19, 2, 3, 2, 17, 2, 5, 2, 3, 2, 59, 2, 31, 2, 3,
    2, 5, 2, 1427, 2, 3, 2, 4621, 2, 13, 2, 3, 2, 47, 2, 11,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 619, 2, 107717, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 11, 2, 61, 2, 3, 2, 67, 2, 6607, 2, 3,
    2, 71, 2, 5, 2, 3, 2]

/-- Table 9 row: the prime after 13086861181 is 13086861181 + 328. -/
theorem gap9_328 : IsGapAt 13086861181 328 :=
  isGapAt_of 13086861181 328 (p13086861181) (by show Nat.Prime 13086861509; exact p13086861509) gds_328 (by decide +kernel)

def gds_334 : List ℕ := [
    2, 3, 2, 17, 2, 5, 2, 3, 2, 53, 2, 103, 2, 3, 2, 5,
    2, 89, 2, 3, 2, 7, 2, 23, 2, 3, 2, 13, 2, 9497, 2, 3,
    2, 52009, 2, 5, 2, 3, 2, 19183, 2, 11, 2, 3, 2, 5, 2, 43,
    2, 3, 2, 293, 2, 13, 2, 3, 2, 1307, 2, 58787, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 23, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 29, 2, 107, 2, 3, 2, 37591, 2, 1361, 2, 3, 2, 7039, 2, 5,
    2, 3, 2, 271, 2, 2699, 2, 3, 2, 5, 2, 11, 2, 3, 2, 71,
    2, 181, 2, 3, 2, 389, 2, 7, 2, 3, 2, 37, 2, 5, 2, 3,
    2, 11, 2, 13, 2, 3, 2, 5, 2, 83, 2, 3, 2, 193, 2, 359,
    2, 3, 2, 7, 2, 463, 2, 3, 2, 66601, 2, 5, 2, 3, 2, 61,
    2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 113, 2, 11, 2, 3,
    2, 691, 2, 461, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 821,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 51257, 2, 7, 2, 3, 2, 17,
    2, 13, 2, 3, 2, 38693, 2, 5, 2, 3, 2, 43, 2, 53, 2, 3,
    2, 5, 2, 773, 2, 3, 2, 7, 2, 47, 2, 3, 2, 2063, 2, 11,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 727, 2, 31, 2, 3, 2, 5,
    2, 10399, 2, 3, 2, 11, 2, 155717, 2, 3, 2, 283, 2, 383, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 117329, 2, 19, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 149, 2, 139, 2, 3, 2, 107, 2, 23, 2, 3, 2, 79,
    2, 5, 2, 3, 2, 17, 2, 557, 2, 3, 2, 5, 2, 3727, 2, 3,
    2, 307, 2, 40519, 2, 3, 2, 11, 2, 7, 2, 3, 2]

/-- Table 9 row: the prime after 30827138509 is 30827138509 + 334. -/
theorem gap9_334 : IsGapAt 30827138509 334 :=
  isGapAt_of 30827138509 334 (p30827138509) (by show Nat.Prime 30827138843; exact p30827138843) gds_334 (by decide +kernel)

def gds_362 : List ℕ := [
    2, 7, 2, 3, 2, 41263, 2, 67, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 11, 2, 37, 2, 3, 2, 5, 2, 43, 2, 3, 2, 7, 2, 23,
    2, 3, 2, 82651, 2, 907, 2, 3, 2, 19, 2, 5, 2, 3, 2, 13,
    2, 29, 2, 3, 2, 5, 2, 6661, 2, 3, 2, 1637, 2, 11, 2, 3,
    2, 31, 2, 83, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 17,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 131, 2, 743, 2, 3, 2, 101,
    2, 12763, 2, 3, 2, 2557, 2, 5, 2, 3, 2, 29, 2, 59, 2, 3,
    2, 5, 2, 239, 2, 3, 2, 467, 2, 229, 2, 3, 2, 13, 2, 7,
    2, 3, 2, 15803, 2, 5, 2, 3, 2, 761, 2, 2213, 2, 3, 2, 5,
    2, 97, 2, 3, 2, 11, 2, 13, 2, 3, 2, 7, 2, 53, 2, 3,
    2, 15473, 2, 5, 2, 3, 2, 37, 2, 7, 2, 3, 2, 5, 2, 227,
    2, 3, 2, 191, 2, 17, 2, 3, 2, 23201, 2, 81019, 2, 3, 2, 829,
    2, 5, 2, 3, 2, 7, 2, 653, 2, 3, 2, 5, 2, 135719, 2, 3,
    2, 137, 2, 7, 2, 3, 2, 11, 2, 41, 2, 3, 2, 6673, 2, 5,
    2, 3, 2, 59, 2, 13, 2, 3, 2, 5, 2, 1619, 2, 3, 2, 7,
    2, 37, 2, 3, 2, 313, 2, 13577, 2, 3, 2, 31, 2, 5, 2, 3,
    2, 73, 2, 11, 2, 3, 2, 5, 2, 21487, 2, 3, 2, 19, 2, 27941,
    2, 3, 2, 67, 2, 283, 2, 3, 2, 7, 2, 5, 2, 3, 2, 173,
    2, 397, 2, 3, 2, 5, 2, 7, 2, 3, 2, 41, 2, 47, 2, 3,
    2, 197, 2, 13, 2, 3, 2, 174893, 2, 5, 2, 3, 2, 17, 2, 211,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 139, 2, 2393, 2, 3, 2, 157,
    2, 7, 2, 3, 2, 79, 2, 5, 2, 3, 2, 11, 2, 6133, 2, 3,
    2, 5, 2, 223, 2, 3, 2, 13, 2]

/-- Table 9 row: the prime after 35877724601 is 35877724601 + 362. -/
theorem gap9_362 : IsGapAt 35877724601 362 :=
  isGapAt_of 35877724601 362 (p35877724601) (by show Nat.Prime 35877724963; exact p35877724963) gds_362 (by decide +kernel)

def gds_368 : List ℕ := [
    2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 3457, 2, 3,
    2, 23, 2, 7, 2, 3, 2, 29, 2, 163, 2, 3, 2, 30047, 2, 5,
    2, 3, 2, 41, 2, 13, 2, 3, 2, 5, 2, 107, 2, 3, 2, 7,
    2, 211, 2, 3, 2, 19, 2, 11, 2, 3, 2, 31, 2, 5, 2, 3,
    2, 8461, 2, 37, 2, 3, 2, 5, 2, 233, 2, 3, 2, 11, 2, 67,
    2, 3, 2, 47, 2, 22133, 2, 3, 2, 7, 2, 5, 2, 3, 2, 3271,
    2, 4729, 2, 3, 2, 5, 2, 7, 2, 3, 2, 76259, 2, 17, 2, 3,
    2, 2161, 2, 13, 2, 3, 2, 307, 2, 5, 2, 3, 2, 13513, 2, 159167,
    2, 3, 2, 5, 2, 227, 2, 3, 2, 127, 2, 29, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 23879, 2, 5, 2, 3, 2, 23, 2, 71, 2, 3,
    2, 5, 2, 1217, 2, 3, 2, 13, 2, 199, 2, 3, 2, 7, 2, 2011,
    2, 3, 2, 6427, 2, 5, 2, 3, 2, 1483, 2, 7, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 29, 2, 41, 2, 3, 2, 79, 2, 19, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 7, 2, 4327, 2, 3, 2, 5, 2, 131111,
    2, 3, 2, 3089, 2, 7, 2, 3, 2, 521, 2, 83, 2, 3, 2, 69467,
    2, 5, 2, 3, 2, 13, 2, 23, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 7, 2, 2437, 2, 3, 2, 61, 2, 29207, 2, 3, 2, 379, 2, 5,
    2, 3, 2, 11, 2, 557, 2, 3, 2, 5, 2, 443, 2, 3, 2, 97,
    2, 37, 2, 3, 2, 23, 2, 2099, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 14243, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2, 197, 2, 11,
    2, 3, 2, 13, 2, 6551, 2, 3, 2, 11057, 2, 5, 2, 3, 2, 25943,
    2, 79609, 2, 3, 2, 5, 2, 101, 2, 3, 2, 17, 2, 13, 2, 3,
    2, 223, 2, 7, 2, 3, 2, 311, 2, 5, 2, 3, 2, 47, 2]

/-- Table 9 row: the prime after 51430518413 is 51430518413 + 368. -/
theorem gap9_368 : IsGapAt 51430518413 368 :=
  isGapAt_of 51430518413 368 (p51430518413) (by show Nat.Prime 51430518781; exact p51430518781) gds_368 (by decide +kernel)

def gds_370 : List ℕ := [
    2, 3, 2, 5, 2, 43, 2, 3, 2, 7, 2, 89, 2, 3, 2, 25037,
    2, 3413, 2, 3, 2, 13, 2, 5, 2, 3, 2, 101, 2, 19, 2, 3,
    2, 5, 2, 29, 2, 3, 2, 647, 2, 107, 2, 3, 2, 193, 2, 11,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 313, 2, 571, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 11, 2, 269, 2, 3, 2, 53, 2, 17, 2, 3,
    2, 9049, 2, 5, 2, 3, 2, 21059, 2, 23, 2, 3, 2, 5, 2, 131,
    2, 3, 2, 13, 2, 73, 2, 3, 2, 19, 2, 7, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 5867, 2, 157, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 3011, 2, 123407, 2, 3, 2, 7, 2, 41, 2, 3, 2, 37, 2, 5,
    2, 3, 2, 83, 2, 7, 2, 3, 2, 5, 2, 491, 2, 3, 2, 156259,
    2, 691, 2, 3, 2, 174673, 2, 277, 2, 3, 2, 1429, 2, 5, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 5, 2, 67, 2, 3, 2, 89, 2, 7,
    2, 3, 2, 41999, 2, 1069, 2, 3, 2, 11, 2, 5, 2, 3, 2, 127,
    2, 29, 2, 3, 2, 5, 2, 31, 2, 3, 2, 7, 2, 181, 2, 3,
    2, 59, 2, 23, 2, 3, 2, 35437, 2, 5, 2, 3, 2, 161167, 2, 23201,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 1489, 2, 1931, 2, 3, 2, 13,
    2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 1847, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 221773, 2, 13, 2, 3, 2, 1153, 2, 53,
    2, 3, 2, 613, 2, 5, 2, 3, 2, 2203, 2, 1993, 2, 3, 2, 5,
    2, 2347, 2, 3, 2, 61, 2, 11, 2, 3, 2, 17, 2, 7, 2, 3,
    2, 21269, 2, 5, 2, 3, 2, 211, 2, 2531, 2, 3, 2, 5, 2, 34211,
    2, 3, 2, 31, 2, 7549, 2, 3, 2, 7, 2, 233, 2, 3, 2, 79,
    2, 5, 2, 3, 2, 131, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3,
    2]

/-- Table 9 row: the prime after 59942358571 is 59942358571 + 370. -/
theorem gap9_370 : IsGapAt 59942358571 370 :=
  isGapAt_of 59942358571 370 (p59942358571) (by show Nat.Prime 59942358941; exact p59942358941) gds_370 (by decide +kernel)

def gds_388 : List ℕ := [
    2, 3, 2, 7, 2, 5869, 2, 3, 2, 509, 2, 5, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 761, 2, 73, 2, 3,
    2, 84179, 2, 92581, 2, 3, 2, 43, 2, 5, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 5, 2, 45233, 2, 3, 2, 79, 2, 7, 2, 3, 2, 53,
    2, 37, 2, 3, 2, 11, 2, 5, 2, 3, 2, 47, 2, 25747, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 7, 2, 15377, 2, 3, 2, 9239, 2, 13,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 31, 2, 23, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 17, 2, 20431, 2, 3, 2, 12967, 2, 41, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 11, 2, 19, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 13, 2, 173, 2, 3, 2, 23, 2, 109, 2, 3, 2, 1597,
    2, 5, 2, 3, 2, 102587, 2, 31, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 263, 2, 11, 2, 3, 2, 1511, 2, 7, 2, 3, 2, 49391, 2, 5,
    2, 3, 2, 29, 2, 137, 2, 3, 2, 5, 2, 61, 2, 3, 2, 41,
    2, 227, 2, 3, 2, 7, 2, 79, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 5, 2, 131, 2, 3, 2, 149, 2, 499,
    2, 3, 2, 255191, 2, 11, 2, 3, 2, 613, 2, 5, 2, 3, 2, 7,
    2, 257, 2, 3, 2, 5, 2, 47, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 6397, 2, 53, 2, 3, 2, 233, 2, 5, 2, 3, 2, 97, 2, 17,
    2, 3, 2, 5, 2, 83777, 2, 3, 2, 7, 2, 206807, 2, 3, 2, 13,
    2, 197, 2, 3, 2, 42281, 2, 5, 2, 3, 2, 587, 2, 641, 2, 3,
    2, 5, 2, 1609, 2, 3, 2, 19, 2, 13, 2, 3, 2, 11, 2, 443,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 199, 2, 277, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 47, 2, 4597, 2, 3, 2, 21143, 2, 19, 2, 3,
    2, 29, 2, 5, 2, 3, 2, 787, 2, 11, 2, 3, 2, 5, 2, 23,
    2, 3, 2]

/-- Table 9 row: the prime after 156798792223 is 156798792223 + 388. -/
theorem gap9_388 : IsGapAt 156798792223 388 :=
  isGapAt_of 156798792223 388 (p156798792223) (by show Nat.Prime 156798792611; exact p156798792611) gds_388 (by decide +kernel)

def gds_422 : List ℕ := [
    2, 211, 2, 3, 2, 7, 2, 11, 2, 3, 2, 797, 2, 5, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 5, 2, 14143, 2, 3, 2, 11, 2, 281,
    2, 3, 2, 37, 2, 409, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7,
    2, 440087, 2, 3, 2, 5, 2, 45887, 2, 3, 2, 192233, 2, 7, 2, 3,
    2, 29, 2, 132529, 2, 3, 2, 88799, 2, 5, 2, 3, 2, 347, 2, 71,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 331, 2, 3, 2, 11,
    2, 41, 2, 3, 2, 181, 2, 5, 2, 3, 2, 47, 2, 17, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 40559, 2, 13, 2, 3, 2, 1699, 2, 63587,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 137, 2, 11, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 1367, 2, 1039, 2, 3, 2, 15607, 2, 35977, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 89, 2, 50909, 2, 3, 2, 5, 2, 617,
    2, 3, 2, 41, 2, 29, 2, 3, 2, 467, 2, 7, 2, 3, 2, 73,
    2, 5, 2, 3, 2, 82657, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 31, 2, 17, 2, 3, 2, 7, 2, 739, 2, 3, 2, 71, 2, 5,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 149, 2, 3, 2, 29,
    2, 97, 2, 3, 2, 17, 2, 3391, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 7, 2, 857, 2, 3, 2, 5, 2, 53, 2, 3, 2, 317, 2, 7,
    2, 3, 2, 19, 2, 13, 2, 3, 2, 43, 2, 5, 2, 3, 2, 109,
    2, 79, 2, 3, 2, 5, 2, 47, 2, 3, 2, 7, 2, 101, 2, 3,
    2, 239, 2, 1597, 2, 3, 2, 179, 2, 5, 2, 3, 2, 61, 2, 59,
    2, 3, 2, 5, 2, 359, 2, 3, 2, 13, 2, 37, 2, 3, 2, 823,
    2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 263, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 11, 2, 517553, 2, 3, 2, 10337, 2, 43,
    2, 3, 2, 53, 2, 5, 2, 3, 2, 449, 2, 487, 2, 3, 2, 5,
    2, 2837, 2, 3, 2, 19, 2, 23, 2, 3, 2, 31, 2, 7, 2, 3,
    2, 2689, 2, 5, 2, 3, 2, 13, 2, 67, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 113, 2]

/-- Table 9 row: the prime after 280974865361 is 280974865361 + 422. -/
theorem gap9_422 : IsGapAt 280974865361 422 :=
  isGapAt_of 280974865361 422 (p280974865361) (by show Nat.Prime 280974865783; exact p280974865783) gds_422 (by decide +kernel)

def gds_436 : List ℕ := [
    2, 3, 2, 5, 2, 7, 2, 3, 2, 59, 2, 45337, 2, 3, 2, 83,
    2, 17, 2, 3, 2, 22129, 2, 5, 2, 3, 2, 19, 2, 139, 2, 3,
    2, 5, 2, 71, 2, 3, 2, 3607, 2, 11, 2, 3, 2, 8231, 2, 7,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 13, 2, 124717, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 23, 2, 29, 2, 3, 2, 7, 2, 19559, 2, 3,
    2, 31, 2, 5, 2, 3, 2, 7013, 2, 7, 2, 3, 2, 5, 2, 103,
    2, 3, 2, 64301, 2, 509, 2, 3, 2, 41, 2, 11, 2, 3, 2, 53,
    2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 571, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 13, 2, 373, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 157, 2, 80107, 2, 3, 2, 5, 2, 19051, 2, 3, 2, 7,
    2, 13, 2, 3, 2, 61, 2, 37, 2, 3, 2, 307, 2, 5, 2, 3,
    2, 71, 2, 19, 2, 3, 2, 5, 2, 113, 2, 3, 2, 67, 2, 211,
    2, 3, 2, 11, 2, 179, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23,
    2, 797, 2, 3, 2, 5, 2, 7, 2, 3, 2, 43, 2, 17, 2, 3,
    2, 787, 2, 739, 2, 3, 2, 1321, 2, 5, 2, 3, 2, 6091, 2, 11,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 1823, 2, 18059, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 31, 2, 41, 2, 3,
    2, 5, 2, 270493, 2, 3, 2, 31121, 2, 288179, 2, 3, 2, 7, 2, 61,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 709, 2, 7, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 1567, 2, 472573, 2, 3, 2, 37, 2, 13, 2, 3,
    2, 229, 2, 5, 2, 3, 2, 7, 2, 31, 2, 3, 2, 5, 2, 1409,
    2, 3, 2, 79, 2, 7, 2, 3, 2, 23, 2, 47, 2, 3, 2, 41,
    2, 5, 2, 3, 2, 17, 2, 241, 2, 3, 2, 5, 2, 1039, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 283, 2, 10067, 2, 3, 2, 58109, 2, 5,
    2, 3, 2, 199, 2, 37, 2, 3, 2, 5, 2, 13, 2, 3, 2, 53849,
    2, 751, 2, 3, 2, 547, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 5801, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 53, 2, 173,
    2, 3, 2]

/-- Table 9 row: the prime after 367459059871 is 367459059871 + 436. -/
theorem gap9_436 : IsGapAt 367459059871 436 :=
  isGapAt_of 367459059871 436 (p367459059871) (by show Nat.Prime 367459060307; exact p367459060307) gds_436 (by decide +kernel)

def gds_442 : List ℕ := [
    2, 3, 2, 41, 2, 43, 2, 3, 2, 7, 2, 11, 2, 3, 2, 631,
    2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 193, 2, 3,
    2, 11, 2, 1307, 2, 3, 2, 167, 2, 101, 2, 3, 2, 107791, 2, 5,
    2, 3, 2, 7, 2, 31469, 2, 3, 2, 5, 2, 601, 2, 3, 2, 17107,
    2, 7, 2, 3, 2, 1213, 2, 19, 2, 3, 2, 47, 2, 5, 2, 3,
    2, 17, 2, 557, 2, 3, 2, 5, 2, 1259, 2, 3, 2, 7, 2, 134947,
    2, 3, 2, 11, 2, 176791, 2, 3, 2, 283, 2, 5, 2, 3, 2, 71,
    2, 23, 2, 3, 2, 5, 2, 61, 2, 3, 2, 151, 2, 13, 2, 3,
    2, 29, 2, 6421, 2, 3, 2, 7, 2, 5, 2, 3, 2, 515231, 2, 11,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 97, 2, 83, 2, 3, 2, 23,
    2, 103, 2, 3, 2, 11, 2, 5, 2, 3, 2, 593, 2, 311, 2, 3,
    2, 5, 2, 41611, 2, 3, 2, 17, 2, 19, 2, 3, 2, 467, 2, 7,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 1061, 2, 13, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 461, 2, 59, 2, 3, 2, 7, 2, 607, 2, 3,
    2, 1777, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 37,
    2, 3, 2, 101, 2, 29, 2, 3, 2, 41, 2, 17, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 7, 2, 43, 2, 3, 2, 5, 2, 17749, 2, 3,
    2, 55589, 2, 7, 2, 3, 2, 383, 2, 13, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 1523, 2, 197, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7,
    2, 3911, 2, 3, 2, 157, 2, 1399, 2, 3, 2, 246319, 2, 5, 2, 3,
    2, 83, 2, 5171, 2, 3, 2, 5, 2, 36151, 2, 3, 2, 13, 2, 433,
    2, 3, 2, 99761, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 462899,
    2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 251, 2, 3,
    2, 1051, 2, 1181, 2, 3, 2, 19, 2, 5, 2, 3, 2, 31, 2, 73,
    2, 3, 2, 5, 2, 23, 2, 3, 2, 269, 2, 71, 2, 3, 2, 6857,
    2, 7, 2, 3, 2, 359, 2, 5, 2, 3, 2, 13, 2, 19, 2, 3,
    2, 5, 2, 29, 2, 3, 2, 107, 2, 151, 2, 3, 2, 7, 2, 653,
    2, 3, 2, 23, 2, 5, 2, 3, 2]

/-- Table 9 row: the prime after 417470554687 is 417470554687 + 442. -/
theorem gap9_442 : IsGapAt 417470554687 442 :=
  isGapAt_of 417470554687 442 (p417470554687) (by show Nat.Prime 417470555129; exact p417470555129) gds_442 (by decide +kernel)

def gds_452 : List ℕ := [
    2, 211949, 2, 3, 2, 7, 2, 53, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 29, 2, 7, 2, 3, 2, 5, 2, 211, 2, 3, 2, 17, 2, 349,
    2, 3, 2, 349207, 2, 3797, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7,
    2, 19, 2, 3, 2, 5, 2, 37, 2, 3, 2, 41, 2, 7, 2, 3,
    2, 262337, 2, 13, 2, 3, 2, 6653, 2, 5, 2, 3, 2, 25633, 2, 59,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 137, 2, 3, 2, 71,
    2, 17, 2, 3, 2, 127, 2, 5, 2, 3, 2, 11, 2, 113, 2, 3,
    2, 5, 2, 2663, 2, 3, 2, 13, 2, 334843, 2, 3, 2, 19, 2, 208577,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 3121, 2, 103, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 757, 2, 11, 2, 3, 2, 11923, 2, 118751, 2, 3,
    2, 1487, 2, 5, 2, 3, 2, 73, 2, 43, 2, 3, 2, 5, 2, 206461,
    2, 3, 2, 23, 2, 31, 2, 3, 2, 149, 2, 7, 2, 3, 2, 29,
    2, 5, 2, 3, 2, 13, 2, 17, 2, 3, 2, 5, 2, 827, 2, 3,
    2, 8647, 2, 223, 2, 3, 2, 7, 2, 11, 2, 3, 2, 1447, 2, 5,
    2, 3, 2, 1109, 2, 7, 2, 3, 2, 5, 2, 2699, 2, 3, 2, 11,
    2, 61, 2, 3, 2, 523463, 2, 644857, 2, 3, 2, 89, 2, 5, 2, 3,
    2, 7, 2, 541, 2, 3, 2, 5, 2, 149251, 2, 3, 2, 227, 2, 7,
    2, 3, 2, 13, 2, 19, 2, 3, 2, 109, 2, 5, 2, 3, 2, 67,
    2, 48299, 2, 3, 2, 5, 2, 383, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 11, 2, 29, 2, 3, 2, 317, 2, 5, 2, 3, 2, 23, 2, 120997,
    2, 3, 2, 5, 2, 53, 2, 3, 2, 401, 2, 11393, 2, 3, 2, 17,
    2, 191, 2, 3, 2, 7, 2, 5, 2, 3, 2, 389, 2, 11, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 199, 2, 40697, 2, 3, 2, 29, 2, 31,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 167, 2, 13, 2, 3, 2, 5,
    2, 97, 2, 3, 2, 151, 2, 19, 2, 3, 2, 439, 2, 7, 2, 3,
    2, 173, 2, 5, 2, 3, 2, 107, 2, 23, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 163, 2, 67, 2, 3, 2, 7, 2, 43, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 252173, 2, 3,
    2, 419, 2]

/-- Table 9 row: the prime after 466855187471 is 466855187471 + 452. -/
theorem gap9_452 : IsGapAt 466855187471 452 :=
  isGapAt_of 466855187471 452 (p466855187471) (by show Nat.Prime 466855187923; exact p466855187923) gds_452 (by decide +kernel)

def gds_466 : List ℕ := [
    2, 3, 2, 5, 2, 131, 2, 3, 2, 25621, 2, 7, 2, 3, 2, 11,
    2, 313, 2, 3, 2, 167, 2, 5, 2, 3, 2, 58897, 2, 19, 2, 3,
    2, 5, 2, 239, 2, 3, 2, 7, 2, 23, 2, 3, 2, 59, 2, 1217,
    2, 3, 2, 48571, 2, 5, 2, 3, 2, 47, 2, 11, 2, 3, 2, 5,
    2, 37, 2, 3, 2, 29, 2, 17, 2, 3, 2, 101021, 2, 31, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 23, 2, 4861, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 6803, 2, 53, 2, 3, 2, 17, 2, 1621, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 83, 2, 73, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 443, 2, 227, 2, 3, 2, 165103, 2, 7, 2, 3, 2, 8431, 2, 5,
    2, 3, 2, 11, 2, 5227, 2, 3, 2, 5, 2, 7867, 2, 3, 2, 2663,
    2, 4019, 2, 3, 2, 7, 2, 12161, 2, 3, 2, 1091, 2, 5, 2, 3,
    2, 26699, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 13, 2, 11,
    2, 3, 2, 373, 2, 61493, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7,
    2, 43, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 7, 2, 3,
    2, 23, 2, 6581, 2, 3, 2, 61, 2, 5, 2, 3, 2, 853, 2, 29033,
    2, 3, 2, 5, 2, 47, 2, 3, 2, 7, 2, 440939, 2, 3, 2, 997,
    2, 11, 2, 3, 2, 139, 2, 5, 2, 3, 2, 13, 2, 311, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 11, 2, 59, 2, 3, 2, 41, 2, 37,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 173, 2, 163, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 17, 2, 101, 2, 3, 2, 127, 2, 23, 2, 3,
    2, 235979, 2, 5, 2, 3, 2, 35911, 2, 20873, 2, 3, 2, 5, 2, 52697,
    2, 3, 2, 47, 2, 397, 2, 3, 2, 11, 2, 7, 2, 3, 2, 197,
    2, 5, 2, 3, 2, 487, 2, 29, 2, 3, 2, 5, 2, 191, 2, 3,
    2, 67, 2, 13, 2, 3, 2, 7, 2, 17, 2, 3, 2, 43, 2, 5,
    2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 233, 2, 3, 2, 59,
    2, 25189, 2, 3, 2, 107, 2, 30427, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 7, 2, 53, 2, 3, 2, 5, 2, 394327, 2, 3, 2, 18899, 2, 7,
    2, 3, 2, 37, 2, 97, 2, 3, 2, 412339, 2, 5, 2, 3, 2, 19,
    2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 3607, 2, 3,
    2]

/-- Table 9 row: the prime after 565855695631 is 565855695631 + 466. -/
theorem gap9_466 : IsGapAt 565855695631 466 :=
  isGapAt_of 565855695631 466 (p565855695631) (by show Nat.Prime 565855696097; exact p565855696097) gds_466 (by decide +kernel)

def gds_470 : List ℕ := [
    2, 5, 2, 3, 2, 101, 2, 43, 2, 3, 2, 5, 2, 313, 2, 3,
    2, 11, 2, 56597, 2, 3, 2, 5519, 2, 29, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 991, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 251,
    2, 23, 2, 3, 2, 79, 2, 17, 2, 3, 2, 409, 2, 5, 2, 3,
    2, 83, 2, 17569, 2, 3, 2, 5, 2, 277, 2, 3, 2, 179, 2, 19,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 23,
    2, 10771, 2, 3, 2, 5, 2, 2003, 2, 3, 2, 41, 2, 730837, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 523, 2, 5, 2, 3, 2, 103, 2, 7,
    2, 3, 2, 5, 2, 647, 2, 3, 2, 37, 2, 165947, 2, 3, 2, 151,
    2, 317, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 5, 2, 179923, 2, 3, 2, 13, 2, 7, 2, 3, 2, 70913, 2, 1709,
    2, 3, 2, 43, 2, 5, 2, 3, 2, 73, 2, 23, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 7, 2, 29, 2, 3, 2, 31, 2, 11953, 2, 3,
    2, 641, 2, 5, 2, 3, 2, 11, 2, 47, 2, 3, 2, 5, 2, 211,
    2, 3, 2, 131, 2, 4027, 2, 3, 2, 23, 2, 1483, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 13, 2, 16189, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 29, 2, 11, 2, 3, 2, 52457, 2, 31, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 401, 2, 71, 2, 3, 2, 5, 2, 53, 2, 3, 2, 711967,
    2, 30553, 2, 3, 2, 17, 2, 7, 2, 3, 2, 7547, 2, 5, 2, 3,
    2, 97, 2, 19, 2, 3, 2, 5, 2, 1181, 2, 3, 2, 827, 2, 10799,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 977, 2, 5, 2, 3, 2, 1831,
    2, 7, 2, 3, 2, 5, 2, 347, 2, 3, 2, 11, 2, 13, 2, 3,
    2, 41, 2, 354743, 2, 3, 2, 37, 2, 5, 2, 3, 2, 7, 2, 1031,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 1237, 2, 7, 2, 3, 2, 19,
    2, 59, 2, 3, 2, 31, 2, 5, 2, 3, 2, 17, 2, 83, 2, 3,
    2, 5, 2, 173, 2, 3, 2, 7, 2, 101, 2, 3, 2, 11, 2, 193,
    2, 3, 2, 71, 2, 5, 2, 3, 2, 743, 2, 13, 2, 3, 2, 5,
    2, 37, 2, 3, 2, 43, 2, 3847, 2, 3, 2, 104059, 2, 151, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 471749, 2, 11, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 468491, 2]

/-- Table 9 row: the prime after 681753256133 is 681753256133 + 470. -/
theorem gap9_470 : IsGapAt 681753256133 470 :=
  isGapAt_of 681753256133 470 (p681753256133) (by show Nat.Prime 681753256603; exact p681753256603) gds_470 (by decide +kernel)

def gds_472 : List ℕ := [
    2, 3, 2, 541, 2, 43, 2, 3, 2, 19, 2, 631, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 47, 2, 109, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 13, 2, 10343, 2, 3, 2, 6659, 2, 2557, 2, 3, 2, 846779, 2, 5,
    2, 3, 2, 11, 2, 37, 2, 3, 2, 5, 2, 13, 2, 3, 2, 363949,
    2, 1741, 2, 3, 2, 31, 2, 7, 2, 3, 2, 61, 2, 5, 2, 3,
    2, 59, 2, 439, 2, 3, 2, 5, 2, 71, 2, 3, 2, 691, 2, 11,
    2, 3, 2, 7, 2, 1531, 2, 3, 2, 108637, 2, 5, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 19, 2, 157999, 2, 3,
    2, 2593, 2, 31, 2, 3, 2, 144539, 2, 5, 2, 3, 2, 7, 2, 172633,
    2, 3, 2, 5, 2, 157, 2, 3, 2, 17, 2, 7, 2, 3, 2, 2153,
    2, 11, 2, 3, 2, 887, 2, 5, 2, 3, 2, 1597, 2, 257, 2, 3,
    2, 5, 2, 41, 2, 3, 2, 7, 2, 407321, 2, 3, 2, 13, 2, 53,
    2, 3, 2, 373, 2, 5, 2, 3, 2, 37, 2, 22717, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 104579, 2, 13, 2, 3, 2, 155231, 2, 17, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 71, 2, 42923, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 469687, 2, 23, 2, 3, 2, 11, 2, 30853, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 41, 2, 43, 2, 3, 2, 5, 2, 55681, 2, 3,
    2, 401, 2, 19, 2, 3, 2, 2857, 2, 7, 2, 3, 2, 33113, 2, 5,
    2, 3, 2, 23, 2, 11, 2, 3, 2, 5, 2, 73, 2, 3, 2, 47,
    2, 74731, 2, 3, 2, 7, 2, 211, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 137, 2, 7, 2, 3, 2, 5, 2, 183023, 2, 3, 2, 311, 2, 24049,
    2, 3, 2, 547, 2, 29, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7,
    2, 2309, 2, 3, 2, 5, 2, 11, 2, 3, 2, 3167, 2, 7, 2, 3,
    2, 337, 2, 13, 2, 3, 2, 67, 2, 5, 2, 3, 2, 11, 2, 23,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 1801, 2, 3, 2, 29,
    2, 79531, 2, 3, 2, 107, 2, 5, 2, 3, 2, 197, 2, 8501, 2, 3,
    2, 5, 2, 492769, 2, 3, 2, 13, 2, 11, 2, 3, 2, 23, 2, 65899,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 31, 2, 152519, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 2897, 2, 83, 2, 3, 2, 17, 2, 1367, 2, 3,
    2, 19, 2, 5, 2, 3, 2]

/-- Table 9 row: the prime after 865244709607 is 865244709607 + 472. -/
theorem gap9_472 : IsGapAt 865244709607 472 :=
  isGapAt_of 865244709607 472 (p865244709607) (by show Nat.Prime 865244710079; exact p865244710079) gds_472 (by decide +kernel)

def gds_482 : List ℕ := [
    2, 13, 2, 3, 2, 37, 2, 47, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 23, 2, 418199, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 11,
    2, 3, 2, 83, 2, 53, 2, 3, 2, 19, 2, 5, 2, 3, 2, 41,
    2, 409, 2, 3, 2, 5, 2, 109, 2, 3, 2, 401, 2, 479, 2, 3,
    2, 283, 2, 7, 2, 3, 2, 175291, 2, 5, 2, 3, 2, 43951, 2, 13,
    2, 3, 2, 5, 2, 31, 2, 3, 2, 652903, 2, 71, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 47, 2, 5, 2, 3, 2, 251, 2, 7, 2, 3,
    2, 5, 2, 103, 2, 3, 2, 11, 2, 456427, 2, 3, 2, 378011, 2, 1669,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 661, 2, 3, 2, 5,
    2, 7393, 2, 3, 2, 107, 2, 7, 2, 3, 2, 19, 2, 13, 2, 3,
    2, 3631, 2, 5, 2, 3, 2, 29, 2, 32561, 2, 3, 2, 5, 2, 719,
    2, 3, 2, 7, 2, 59, 2, 3, 2, 11, 2, 461, 2, 3, 2, 52391,
    2, 5, 2, 3, 2, 1427, 2, 17, 2, 3, 2, 5, 2, 1051, 2, 3,
    2, 13, 2, 41, 2, 3, 2, 67, 2, 28517, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 37, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 21401,
    2, 43991, 2, 3, 2, 3209, 2, 23, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 278501, 2, 223, 2, 3, 2, 5, 2, 31307, 2, 3, 2, 19, 2, 31,
    2, 3, 2, 239, 2, 7, 2, 3, 2, 11177, 2, 5, 2, 3, 2, 13,
    2, 47, 2, 3, 2, 5, 2, 11, 2, 3, 2, 59, 2, 17, 2, 3,
    2, 7, 2, 19, 2, 3, 2, 619, 2, 5, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 5, 2, 3547, 2, 3, 2, 68963, 2, 337, 2, 3, 2, 17,
    2, 90659, 2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2, 67, 2, 3,
    2, 5, 2, 53, 2, 3, 2, 14321, 2, 7, 2, 3, 2, 13, 2, 83,
    2, 3, 2, 33857, 2, 5, 2, 3, 2, 683, 2, 69737, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 7, 2, 13, 2, 3, 2, 31, 2, 75029, 2, 3,
    2, 43, 2, 5, 2, 3, 2, 79, 2, 154057, 2, 3, 2, 5, 2, 367,
    2, 3, 2, 523, 2, 19, 2, 3, 2, 700211, 2, 11, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 17, 2, 61, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 11, 2, 40883, 2, 3, 2, 23291, 2, 29, 2, 3, 2, 53, 2, 5,
    2, 3, 2, 1429, 2, 13, 2, 3, 2, 5, 2, 787, 2, 3, 2, 271,
    2]

/-- Table 9 row: the prime after 1051602787181 is 1051602787181 + 482. -/
theorem gap9_482 : IsGapAt 1051602787181 482 :=
  isGapAt_of 1051602787181 482 (p1051602787181) (by show Nat.Prime 1051602787663; exact p1051602787663) gds_482 (by decide +kernel)

def gds_488 : List ℕ := [
    2, 97, 2, 3, 2, 5, 2, 11, 2, 3, 2, 131, 2, 17, 2, 3,
    2, 1039, 2, 7, 2, 3, 2, 21739, 2, 5, 2, 3, 2, 11, 2, 899309,
    2, 3, 2, 5, 2, 15091, 2, 3, 2, 13, 2, 118051, 2, 3, 2, 7,
    2, 105379, 2, 3, 2, 53, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 37, 2, 11, 2, 3, 2, 67339, 2, 731681,
    2, 3, 2, 2437, 2, 5, 2, 3, 2, 7, 2, 559217, 2, 3, 2, 5,
    2, 13859, 2, 3, 2, 113, 2, 7, 2, 3, 2, 149, 2, 15199, 2, 3,
    2, 43, 2, 5, 2, 3, 2, 13, 2, 433, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 7, 2, 665177, 2, 3, 2, 189901, 2, 11, 2, 3, 2, 67,
    2, 5, 2, 3, 2, 17, 2, 23, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 11, 2, 673, 2, 3, 2, 313, 2, 36269, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 107, 2, 103, 2, 3, 2, 5, 2, 7, 2, 3, 2, 283,
    2, 47, 2, 3, 2, 13, 2, 43, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 41, 2, 109, 2, 3, 2, 5, 2, 17, 2, 3, 2, 61, 2, 13,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 677, 2, 5, 2, 3, 2, 173,
    2, 19, 2, 3, 2, 5, 2, 251, 2, 3, 2, 17, 2, 1098469, 2, 3,
    2, 7, 2, 3919, 2, 3, 2, 465743, 2, 5, 2, 3, 2, 587, 2, 7,
    2, 3, 2, 5, 2, 67, 2, 3, 2, 31, 2, 16547, 2, 3, 2, 47,
    2, 23, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 5, 2, 6173, 2, 3, 2, 709, 2, 7, 2, 3, 2, 19, 2, 17,
    2, 3, 2, 883, 2, 5, 2, 3, 2, 89, 2, 29, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 7, 2, 31, 2, 3, 2, 353677, 2, 44087, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 11, 2, 3187, 2, 3, 2, 5, 2, 37,
    2, 3, 2, 43, 2, 41, 2, 3, 2, 8111, 2, 13, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 29, 2, 1753, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 3023, 2, 11, 2, 3, 2, 3877, 2, 269, 2, 3, 2, 71, 2, 5,
    2, 3, 2, 499, 2, 17, 2, 3, 2, 5, 2, 23, 2, 3, 2, 13,
    2, 227, 2, 3, 2, 199, 2, 7, 2, 3, 2, 151, 2, 5, 2, 3,
    2, 236219, 2, 9743, 2, 3, 2, 5, 2, 13, 2, 3, 2, 154087, 2, 1043113,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 23, 2, 5, 2, 3, 2, 523,
    2, 7, 2, 3, 2, 5, 2]

/-- Table 9 row: the prime after 1275363152099 is 1275363152099 + 488. -/
theorem gap9_488 : IsGapAt 1275363152099 488 :=
  isGapAt_of 1275363152099 488 (p1275363152099) (by show Nat.Prime 1275363152587; exact p1275363152587) gds_488 (by decide +kernel)

def gds_506 : List ℕ := [
    2, 37, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 839, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 139, 2, 1747, 2, 3, 2, 263, 2, 19,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 173, 2, 41, 2, 3, 2, 5,
    2, 317777, 2, 3, 2, 359, 2, 11, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 43, 2, 5, 2, 3, 2, 67, 2, 659, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 526651, 2, 13, 2, 3, 2, 7, 2, 73, 2, 3, 2, 523,
    2, 5, 2, 3, 2, 6551, 2, 7, 2, 3, 2, 5, 2, 967, 2, 3,
    2, 17, 2, 463, 2, 3, 2, 241, 2, 11, 2, 3, 2, 41, 2, 5,
    2, 3, 2, 7, 2, 541181, 2, 3, 2, 5, 2, 13711, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 37, 2, 43, 2, 3, 2, 557, 2, 5, 2, 3,
    2, 411127, 2, 13, 2, 3, 2, 5, 2, 457, 2, 3, 2, 7, 2, 59,
    2, 3, 2, 29, 2, 17, 2, 3, 2, 53, 2, 5, 2, 3, 2, 307,
    2, 5153, 2, 3, 2, 5, 2, 23, 2, 3, 2, 181, 2, 67, 2, 3,
    2, 11, 2, 356311, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 37,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 127, 2, 281, 2, 3, 2, 631,
    2, 13, 2, 3, 2, 23, 2, 5, 2, 3, 2, 1433, 2, 11, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 167, 2, 47, 2, 3, 2, 84223, 2, 7,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 175211, 2, 17, 2, 3, 2, 5,
    2, 41, 2, 3, 2, 13, 2, 29, 2, 3, 2, 7, 2, 139, 2, 3,
    2, 4201, 2, 5, 2, 3, 2, 712477, 2, 7, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 43, 2, 49843, 2, 3, 2, 523261, 2, 227, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 7, 2, 72139, 2, 3, 2, 5, 2, 491, 2, 3,
    2, 29, 2, 7, 2, 3, 2, 47, 2, 149, 2, 3, 2, 10739, 2, 5,
    2, 3, 2, 13, 2, 19, 2, 3, 2, 5, 2, 20873, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 2423, 2, 187793, 2, 3, 2, 1061, 2, 5, 2, 3,
    2, 137, 2, 20747, 2, 3, 2, 5, 2, 43, 2, 3, 2, 223, 2, 101,
    2, 3, 2, 17, 2, 6229, 2, 3, 2, 7, 2, 5, 2, 3, 2, 2221,
    2, 3461, 2, 3, 2, 5, 2, 7, 2, 3, 2, 10853, 2, 37, 2, 3,
    2, 13, 2, 11, 2, 3, 2, 34513, 2, 5, 2, 3, 2, 1721, 2, 61,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 11, 2, 13, 2, 3, 2, 809,
    2, 7, 2, 3, 2, 89, 2, 5, 2, 3, 2, 311, 2, 34301, 2, 3,
    2, 5, 2, 151, 2, 3, 2, 53, 2]

/-- Table 9 row: the prime after 1339347750707 is 1339347750707 + 506. -/
theorem gap9_506 : IsGapAt 1339347750707 506 :=
  isGapAt_of 1339347750707 506 (p1339347750707) (by show Nat.Prime 1339347751213; exact p1339347751213) gds_506 (by decide +kernel)

end LeanLab.OeSHP2014
