/-
P0005 Oliveira e Silva, Herzog, Pardi 2014, Table 9, page 2051, record-breaking first
occurrences P(g) of a prime gap g, part 5: each row IsGapAt P(g) g, that is P(g) and
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

theorem p12342331 : Nat.Prime 12342331 := by
  refine Pratt.pratt 12342331 15 [(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (137, 1)] (by norm_num)
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
theorem p13231819 : Nat.Prime 13231819 := by
  refine Pratt.pratt 13231819 2 [(2, 1), (3, 2), (367, 1), (2003, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p15605407 : Nat.Prime 15605407 := by
  refine Pratt.pratt 15605407 5 [(2, 1), (3, 3), (288989, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p18312059 : Nat.Prime 18312059 := by
  refine Pratt.pratt 18312059 2 [(2, 1), (179, 1), (51151, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p23198299 : Nat.Prime 23198299 := by
  refine Pratt.pratt 23198299 2 [(2, 1), (3, 1), (397, 1), (9739, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p24752789 : Nat.Prime 24752789 := by
  refine Pratt.pratt 24752789 2 [(2, 2), (1009, 1), (6133, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p26266099 : Nat.Prime 26266099 := by
  refine Pratt.pratt 26266099 3 [(2, 1), (3, 1), (1789, 1), (2447, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p33692251 : Nat.Prime 33692251 := by
  refine Pratt.pratt 33692251 2 [(2, 1), (3, 1), (5, 3), (167, 1), (269, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p39147397 : Nat.Prime 39147397 := by
  refine Pratt.pratt 39147397 5 [(2, 2), (3, 1), (17, 1), (191899, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p62421629 : Nat.Prime 62421629 := by
  refine Pratt.pratt 62421629 2 [(2, 2), (15605407, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p15605407
theorem p66726713 : Nat.Prime 66726713 := by
  refine Pratt.pratt 66726713 3 [(2, 3), (13, 1), (43, 2), (347, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p76518731 : Nat.Prime 76518731 := by
  refine Pratt.pratt 76518731 2 [(2, 1), (5, 1), (7651873, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p83064101 : Nat.Prime 83064101 := by
  refine Pratt.pratt 83064101 2 [(2, 2), (5, 2), (7, 1), (107, 1), (1109, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p116573311 : Nat.Prime 116573311 := by
  refine Pratt.pratt 116573311 7 [(2, 1), (3, 3), (5, 1), (7, 1), (37, 1), (1667, 1)] (by norm_num)
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
theorem p130088671 : Nat.Prime 130088671 := by
  refine Pratt.pratt 130088671 3 [(2, 1), (3, 1), (5, 1), (37, 1), (163, 1), (719, 1)] (by norm_num)
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
theorem p133453427 : Nat.Prime 133453427 := by
  refine Pratt.pratt 133453427 2 [(2, 1), (66726713, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p66726713
theorem p141234931 : Nat.Prime 141234931 := by
  refine Pratt.pratt 141234931 2 [(2, 1), (3, 2), (5, 1), (29, 1), (53, 1), (1021, 1)] (by norm_num)
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
theorem p166128203 : Nat.Prime 166128203 := by
  refine Pratt.pratt 166128203 2 [(2, 1), (83064101, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p83064101
theorem p295584013 : Nat.Prime 295584013 := by
  refine Pratt.pratt 295584013 2 [(2, 2), (3, 3), (2736889, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p559261831 : Nat.Prime 559261831 := by
  refine Pratt.pratt 559261831 3 [(2, 1), (3, 1), (5, 1), (53, 1), (211, 1), (1667, 1)] (by norm_num)
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
theorem p726602791 : Nat.Prime 726602791 := by
  refine Pratt.pratt 726602791 3 [(2, 1), (3, 1), (5, 1), (137, 1), (176789, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p847409587 : Nat.Prime 847409587 := by
  refine Pratt.pratt 847409587 2 [(2, 1), (3, 1), (141234931, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p141234931
theorem p1182336053 : Nat.Prime 1182336053 := by
  refine Pratt.pratt 1182336053 2 [(2, 2), (295584013, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p295584013
theorem p1513431637 : Nat.Prime 1513431637 := by
  refine Pratt.pratt 1513431637 2 [(2, 2), (3, 1), (97, 1), (1300199, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p1782082949 : Nat.Prime 1782082949 := by
  refine Pratt.pratt 1782082949 2 [(2, 2), (37, 1), (79, 1), (152419, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p1784286641 : Nat.Prime 1784286641 := by
  refine Pratt.pratt 1784286641 3 [(2, 4), (5, 1), (23, 1), (969721, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p3503144317 : Nat.Prime 3503144317 := by
  refine Pratt.pratt 3503144317 5 [(2, 2), (3, 1), (7, 1), (2243, 1), (18593, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p4493912387 : Nat.Prime 4493912387 := by
  refine Pratt.pratt 4493912387 2 [(2, 1), (109, 1), (197, 1), (269, 1), (389, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p9630259663 : Nat.Prime 9630259663 := by
  refine Pratt.pratt 9630259663 5 [(2, 1), (3, 1), (41, 1), (39147397, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p39147397
theorem p12396514477 : Nat.Prime 12396514477 := by
  refine Pratt.pratt 12396514477 2 [(2, 2), (3, 1), (17519, 1), (58967, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p22762571129 : Nat.Prime 22762571129 := by
  refine Pratt.pratt 22762571129 6 [(2, 3), (11, 1), (31, 1), (47, 1), (177533, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p43756087423 : Nat.Prime 43756087423 := by
  refine Pratt.pratt 43756087423 3 [(2, 1), (3, 1), (379, 1), (3347, 1), (5749, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p51180675893 : Nat.Prime 51180675893 := by
  refine Pratt.pratt 51180675893 2 [(2, 2), (967, 1), (13231819, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p13231819
theorem p74379086863 : Nat.Prime 74379086863 := by
  refine Pratt.pratt 74379086863 3 [(2, 1), (3, 1), (12396514477, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p12396514477
theorem p114261874481 : Nat.Prime 114261874481 := by
  refine Pratt.pratt 114261874481 3 [(2, 4), (5, 1), (13, 1), (157, 1), (699791, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p173532412447 : Nat.Prime 173532412447 := by
  refine Pratt.pratt 173532412447 3 [(2, 1), (3, 1), (12809, 1), (2257949, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p262536524539 : Nat.Prime 262536524539 := by
  refine Pratt.pratt 262536524539 3 [(2, 1), (3, 1), (43756087423, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p43756087423
theorem p1855391556871 : Nat.Prime 1855391556871 := by
  refine Pratt.pratt 1855391556871 3 [(2, 1), (3, 3), (5, 1), (829, 1), (2459, 1), (3371, 1)] (by norm_num)
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
theorem p5043845602099 : Nat.Prime 5043845602099 := by
  refine Pratt.pratt 5043845602099 2 [(2, 1), (3, 3), (79, 1), (1182336053, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p1182336053
theorem p7496728838381 : Nat.Prime 7496728838381 := by
  refine Pratt.pratt 7496728838381 2 [(2, 2), (5, 1), (107, 1), (3503144317, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p3503144317
theorem p10295961509129 : Nat.Prime 10295961509129 := by
  refine Pratt.pratt 10295961509129 3 [(2, 3), (61, 1), (127, 1), (166128203, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p166128203
theorem p10378674622273 : Nat.Prime 10378674622273 := by
  refine Pratt.pratt 10378674622273 7 [(2, 6), (3, 1), (11, 2), (1973, 1), (226427, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p12354644861107 : Nat.Prime 12354644861107 := by
  refine Pratt.pratt 12354644861107 2 [(2, 1), (3, 1), (19, 1), (23, 1), (761, 1), (6191743, 1)] (by norm_num)
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
theorem p14887121097491 : Nat.Prime 14887121097491 := by
  refine Pratt.pratt 14887121097491 2 [(2, 1), (5, 1), (271, 1), (8863, 1), (619813, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p20591923018259 : Nat.Prime 20591923018259 := by
  refine Pratt.pratt 20591923018259 2 [(2, 1), (10295961509129, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p10295961509129
theorem p22093449494243 : Nat.Prime 22093449494243 := by
  refine Pratt.pratt 22093449494243 2 [(2, 1), (7, 1), (67, 1), (127, 1), (163, 1), (1137809, 1)] (by norm_num)
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
theorem p29361821428141 : Nat.Prime 29361821428141 := by
  refine Pratt.pratt 29361821428141 2 [(2, 2), (3, 1), (5, 1), (31, 1), (601, 1), (26266099, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p26266099
theorem p37458851161691 : Nat.Prime 37458851161691 := by
  refine Pratt.pratt 37458851161691 2 [(2, 1), (5, 1), (7, 1), (191, 1), (227, 1), (12342331, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p12342331
theorem p42113001691367 : Nat.Prime 42113001691367 := by
  refine Pratt.pratt 42113001691367 5 [(2, 1), (337327, 1), (62421629, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p62421629
theorem p255294593822687 : Nat.Prime 255294593822687 := by
  refine Pratt.pratt 255294593822687 5 [(2, 1), (11, 1), (89203, 1), (130088671, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p130088671
theorem p255294593823439 : Nat.Prime 255294593823439 := by
  refine Pratt.pratt 255294593823439 3 [(2, 1), (3, 3), (13, 1), (193373, 1), (1880653, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p323811481625339 : Nat.Prime 323811481625339 := by
  refine Pratt.pratt 323811481625339 2 [(2, 1), (7, 1), (41357, 1), (559261831, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p559261831
theorem p323811481626103 : Nat.Prime 323811481626103 := by
  refine Pratt.pratt 323811481626103 3 [(2, 1), (3, 1), (311, 1), (173532412447, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p173532412447
theorem p423683030575549 : Nat.Prime 423683030575549 := by
  refine Pratt.pratt 423683030575549 2 [(2, 2), (3, 2), (103, 1), (114261874481, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p114261874481
theorem p423683030576317 : Nat.Prime 423683030576317 := by
  refine Pratt.pratt 423683030576317 11 [(2, 2), (3, 1), (7, 1), (5043845602099, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p5043845602099
theorem p469789142849483 : Nat.Prime 469789142849483 := by
  refine Pratt.pratt 469789142849483 5 [(2, 1), (89, 1), (1481, 1), (1782082949, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p1782082949
theorem p469789142850257 : Nat.Prime 469789142850257 := by
  refine Pratt.pratt 469789142850257 3 [(2, 4), (29361821428141, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p29361821428141
theorem p471911699384963 : Nat.Prime 471911699384963 := by
  refine Pratt.pratt 471911699384963 2 [(2, 1), (132241, 1), (1784286641, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p1784286641
theorem p471911699385743 : Nat.Prime 471911699385743 := by
  refine Pratt.pratt 471911699385743 5 [(2, 1), (7, 1), (11, 1), (29, 1), (98963, 1), (1067749, 1)] (by norm_num)
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
theorem p726507223559111 : Nat.Prime 726507223559111 := by
  refine Pratt.pratt 726507223559111 7 [(2, 1), (5, 1), (7, 1), (10378674622273, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p10378674622273
theorem p726507223559893 : Nat.Prime 726507223559893 := by
  refine Pratt.pratt 726507223559893 5 [(2, 2), (3, 2), (3894859, 1), (5181383, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p1271309838631957 : Nat.Prime 1271309838631957 := by
  refine Pratt.pratt 1271309838631957 5 [(2, 2), (3, 2), (19, 1), (193, 1), (9630259663, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p9630259663
theorem p1271309838632753 : Nat.Prime 1271309838632753 := by
  refine Pratt.pratt 1271309838632753 3 [(2, 4), (17681, 1), (4493912387, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p4493912387
theorem p1710270958551941 : Nat.Prime 1710270958551941 := by
  refine Pratt.pratt 1710270958551941 2 [(2, 2), (5, 1), (41, 1), (634541, 1), (3286937, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p1710270958552753 : Nat.Prime 1710270958552753 := by
  refine Pratt.pratt 1710270958552753 5 [(2, 4), (3, 1), (571, 1), (911, 1), (8167, 1), (8387, 1)] (by norm_num)
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
theorem p2537070652896083 : Nat.Prime 2537070652896083 := by
  refine Pratt.pratt 2537070652896083 2 [(2, 1), (23, 1), (2423, 1), (22762571129, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p22762571129
theorem p2537070652896931 : Nat.Prime 2537070652896931 := by
  refine Pratt.pratt 2537070652896931 2 [(2, 1), (3, 2), (5, 1), (379, 1), (74379086863, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p74379086863
theorem p2759317684446707 : Nat.Prime 2759317684446707 := by
  refine Pratt.pratt 2759317684446707 2 [(2, 1), (67, 1), (20591923018259, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p20591923018259
theorem p2759317684447573 : Nat.Prime 2759317684447573 := by
  refine Pratt.pratt 2759317684447573 6 [(2, 2), (3, 3), (1101341, 1), (23198299, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p23198299
theorem p3190972068244913 : Nat.Prime 3190972068244913 := by
  refine Pratt.pratt 3190972068244913 3 [(2, 4), (7, 1), (113, 1), (347, 1), (726602791, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p726602791
theorem p3371055452381147 : Nat.Prime 3371055452381147 := by
  refine Pratt.pratt 3371055452381147 2 [(2, 1), (1031, 1), (66047, 1), (24752789, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p24752789
theorem p3371055452382029 : Nat.Prime 3371055452382029 := by
  refine Pratt.pratt 3371055452382029 2 [(2, 2), (17, 1), (23, 1), (31, 1), (521, 1), (133453427, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p133453427
theorem p4127074165753081 : Nat.Prime 4127074165753081 := by
  refine Pratt.pratt 4127074165753081 17 [(2, 3), (3, 1), (5, 1), (131, 1), (262536524539, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p262536524539
theorem p4127074165753967 : Nat.Prime 4127074165753967 := by
  refine Pratt.pratt 4127074165753967 5 [(2, 1), (7, 2), (42113001691367, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p42113001691367
theorem p4198168149492463 : Nat.Prime 4198168149492463 := by
  refine Pratt.pratt 4198168149492463 5 [(2, 1), (3, 1), (47, 1), (14887121097491, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p14887121097491
theorem p4198168149493361 : Nat.Prime 4198168149493361 := by
  refine Pratt.pratt 4198168149493361 3 [(2, 4), (5, 1), (7, 1), (7496728838381, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p7496728838381
theorem p4286129201882221 : Nat.Prime 4286129201882221 := by
  refine Pratt.pratt 4286129201882221 13 [(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (613, 1), (1513431637, 1)] (by norm_num)
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
  · exact p1513431637
theorem p4286129201883143 : Nat.Prime 4286129201883143 := by
  refine Pratt.pratt 4286129201883143 5 [(2, 1), (97, 1), (22093449494243, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p22093449494243
theorem p4355934264871829 : Nat.Prime 4355934264871829 := by
  refine Pratt.pratt 4355934264871829 2 [(2, 2), (37, 1), (223, 1), (739, 1), (839, 1), (212867, 1)] (by norm_num)
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
theorem p6381944136489827 : Nat.Prime 6381944136489827 := by
  refine Pratt.pratt 6381944136489827 2 [(2, 1), (3190972068244913, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p3190972068244913
theorem p6381944136490753 : Nat.Prime 6381944136490753 := by
  refine Pratt.pratt 6381944136490753 5 [(2, 8), (3, 2), (19, 1), (4327, 1), (33692251, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p33692251
theorem p10244316228469423 : Nat.Prime 10244316228469423 := by
  refine Pratt.pratt 10244316228469423 5 [(2, 1), (3, 1), (11, 1), (23, 1), (368531, 1), (18312059, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p18312059
theorem p10244316228470351 : Nat.Prime 10244316228470351 := by
  refine Pratt.pratt 10244316228470351 17 [(2, 1), (5, 2), (13, 1), (59, 1), (3491, 1), (76518731, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p76518731
theorem p10676480515967939 : Nat.Prime 10676480515967939 := by
  refine Pratt.pratt 10676480515967939 2 [(2, 1), (7, 1), (727, 1), (266863, 1), (3930767, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p10676480515968871 : Nat.Prime 10676480515968871 := by
  refine Pratt.pratt 10676480515968871 7 [(2, 1), (3, 2), (5, 1), (5651, 1), (81233, 1), (258421, 1)] (by norm_num)
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
theorem p19124990244992669 : Nat.Prime 19124990244992669 := by
  refine Pratt.pratt 19124990244992669 2 [(2, 2), (93419, 1), (51180675893, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p51180675893
theorem p19124990244993637 : Nat.Prime 19124990244993637 := by
  refine Pratt.pratt 19124990244993637 6 [(2, 2), (3, 2), (43, 1), (12354644861107, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p12354644861107
theorem p19403684901755939 : Nat.Prime 19403684901755939 := by
  refine Pratt.pratt 19403684901755939 2 [(2, 1), (7, 1), (37, 1), (37458851161691, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p37458851161691
theorem p19403684901756919 : Nat.Prime 19403684901756919 := by
  refine Pratt.pratt 19403684901756919 3 [(2, 1), (3, 2), (7, 1), (83, 1), (1855391556871, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p1855391556871
theorem p34847474118974633 : Nat.Prime 34847474118974633 := by
  refine Pratt.pratt 34847474118974633 3 [(2, 3), (4355934264871829, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p4355934264871829
theorem p34847474118975619 : Nat.Prime 34847474118975619 := by
  refine Pratt.pratt 34847474118975619 2 [(2, 1), (3, 1), (127, 1), (392299, 1), (116573311, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p116573311
theorem p37343192296558573 : Nat.Prime 37343192296558573 := by
  refine Pratt.pratt 37343192296558573 2 [(2, 2), (3, 5), (37, 1), (61, 1), (601, 1), (857, 1), (33049, 1)] (by norm_num)
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
theorem p37343192296559579 : Nat.Prime 37343192296559579 := by
  refine Pratt.pratt 37343192296559579 2 [(2, 1), (11, 1), (13, 1), (4327, 1), (49937, 1), (604277, 1)] (by norm_num)
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
theorem p37967240836435909 : Nat.Prime 37967240836435909 := by
  refine Pratt.pratt 37967240836435909 7 [(2, 2), (3, 1), (607, 1), (6151, 1), (847409587, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p847409587
theorem p37967240836436927 : Nat.Prime 37967240836436927 := by
  refine Pratt.pratt 37967240836436927 5 [(2, 1), (7, 1), (919, 1), (1386617, 1), (2128183, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

def gds_752 : List ℕ := [
    2, 2309, 2, 3, 2, 131, 2, 5, 2, 3, 2, 23, 2, 743, 2, 3,
    2, 5, 2, 9029, 2, 3, 2, 158407, 2, 104161, 2, 3, 2, 167, 2, 11,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 173, 2, 106859, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 11, 2, 31, 2, 3, 2, 2521, 2, 13, 2, 3,
    2, 29, 2, 5, 2, 3, 2, 10326013, 2, 19, 2, 3, 2, 5, 2, 4702279,
    2, 3, 2, 1523, 2, 151, 2, 3, 2, 894923, 2, 7, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 631889, 2, 23, 2, 3, 2, 5, 2, 97, 2, 3,
    2, 13, 2, 503, 2, 3, 2, 7, 2, 18637, 2, 3, 2, 15187, 2, 5,
    2, 3, 2, 83, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 89,
    2, 41, 2, 3, 2, 19, 2, 653, 2, 3, 2, 257, 2, 5, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 5, 2, 1054181, 2, 3, 2, 67, 2, 7,
    2, 3, 2, 31, 2, 29, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13,
    2, 479, 2, 3, 2, 5, 2, 197, 2, 3, 2, 7, 2, 2789, 2, 3,
    2, 81551, 2, 113, 2, 3, 2, 163, 2, 5, 2, 3, 2, 101293, 2, 43,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 79, 2, 127, 2, 3, 2, 29,
    2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 1511, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 19, 2, 17, 2, 3, 2, 13, 2, 37,
    2, 3, 2, 223, 2, 5, 2, 3, 2, 73, 2, 439, 2, 3, 2, 5,
    2, 216779, 2, 3, 2, 157, 2, 11, 2, 3, 2, 17, 2, 7, 2, 3,
    2, 137, 2, 5, 2, 3, 2, 433, 2, 3079, 2, 3, 2, 5, 2, 61,
    2, 3, 2, 2393, 2, 569, 2, 3, 2, 7, 2, 1009, 2, 3, 2, 1879,
    2, 5, 2, 3, 2, 499, 2, 7, 2, 3, 2, 5, 2, 829, 2, 3,
    2, 11669869, 2, 29, 2, 3, 2, 431, 2, 11, 2, 3, 2, 31, 2, 5,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 23, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 2423, 2, 41, 2, 3, 2, 43, 2, 5, 2, 3,
    2, 17, 2, 12721, 2, 3, 2, 5, 2, 139, 2, 3, 2, 7, 2, 19,
    2, 3, 2, 37, 2, 59, 2, 3, 2, 13, 2, 5, 2, 3, 2, 47,
    2, 71, 2, 3, 2, 5, 2, 107339, 2, 3, 2, 1453, 2, 1456333, 2, 3,
    2, 11, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 709, 2, 83,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 41, 2, 4123121, 2, 3, 2, 53,
    2, 43, 2, 3, 2, 449, 2, 5, 2, 3, 2, 19, 2, 11, 2, 3,
    2, 5, 2, 89, 2, 3, 2, 13, 2, 510271, 2, 3, 2, 6761, 2, 7,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 181, 2, 1433, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 23687, 2, 233, 2, 3, 2, 7, 2, 163, 2, 3,
    2, 409, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 23, 2, 199, 2, 3, 2, 563413, 2, 17, 2, 3, 2, 67,
    2, 5, 2, 3, 2, 7, 2, 269, 2, 3, 2, 5, 2, 434683, 2, 3,
    2, 197, 2, 7, 2, 3, 2, 1299211, 2, 1031, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 109, 2, 31, 2, 3, 2, 5, 2, 47, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 83, 2, 193, 2, 3, 2, 149, 2, 5, 2, 3,
    2, 37, 2, 19, 2, 3, 2, 5, 2, 3677, 2, 3, 2, 43, 2, 23,
    2, 3, 2, 13, 2, 691, 2, 3, 2, 7, 2, 5, 2, 3, 2, 5066729,
    2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 1289, 2, 13, 2, 3,
    2, 151, 2, 11, 2, 3, 2, 271, 2, 5, 2, 3, 2, 23, 2, 29,
    2, 3, 2, 5, 2, 67, 2, 3, 2, 11, 2, 37, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 631, 2, 5, 2, 3, 2, 120941, 2, 173, 2, 3,
    2, 5, 2, 43, 2, 3, 2, 127, 2, 1796131, 2, 3, 2, 7, 2]

/-- Table 9 row: the prime after 255294593822687 is 255294593822687 + 752. -/
theorem gap9_752 : IsGapAt 255294593822687 752 :=
  isGapAt_of 255294593822687 752 (p255294593822687) (by show Nat.Prime 255294593823439; exact p255294593823439) gds_752 (by decide +kernel)

def gds_764 : List ℕ := [
    2, 23, 2, 3, 2, 5, 2, 1926637, 2, 3, 2, 19, 2, 6745897, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 47, 2, 5, 2, 3, 2, 17, 2, 1019,
    2, 3, 2, 5, 2, 631, 2, 3, 2, 2498071, 2, 3019, 2, 3, 2, 7,
    2, 19, 2, 3, 2, 97, 2, 5, 2, 3, 2, 331, 2, 7, 2, 3,
    2, 5, 2, 7669, 2, 3, 2, 13, 2, 29, 2, 3, 2, 29531, 2, 59,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 271, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 229, 2, 7, 2, 3, 2, 31, 2, 4721, 2, 3,
    2, 55799, 2, 5, 2, 3, 2, 373, 2, 37, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 563, 2, 3, 2, 353, 2, 23, 2, 3, 2, 547,
    2, 5, 2, 3, 2, 11, 2, 89, 2, 3, 2, 5, 2, 113, 2, 3,
    2, 164377, 2, 19, 2, 3, 2, 71, 2, 31, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 9614887, 2, 301181, 2, 3, 2, 5, 2, 7, 2, 3, 2, 4271,
    2, 11, 2, 3, 2, 41, 2, 17, 2, 3, 2, 103, 2, 5, 2, 3,
    2, 2922529, 2, 47, 2, 3, 2, 5, 2, 3137, 2, 3, 2, 1193, 2, 107981,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 19,
    2, 13066751, 2, 3, 2, 5, 2, 29, 2, 3, 2, 409, 2, 13, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 10531, 2, 5, 2, 3, 2, 37, 2, 7,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 157, 2, 3, 2, 43,
    2, 14173, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 5, 2, 3581, 2, 3, 2, 347, 2, 7, 2, 3, 2, 47419, 2, 181,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 89, 2, 13, 2, 3, 2, 5,
    2, 1249, 2, 3, 2, 7, 2, 37, 2, 3, 2, 11, 2, 34603, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 3842327, 2, 41, 2, 3, 2, 5, 2, 233,
    2, 3, 2, 83, 2, 43, 2, 3, 2, 36457, 2, 798397, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 23497, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 733, 2, 17, 2, 3, 2, 677, 2, 13, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 109, 2, 29, 2, 3, 2, 5, 2, 661, 2, 3, 2, 241,
    2, 59, 2, 3, 2, 17, 2, 7, 2, 3, 2, 41, 2, 5, 2, 3,
    2, 53, 2, 71, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 2063,
    2, 3, 2, 7, 2, 415097, 2, 3, 2, 167, 2, 5, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 37, 2, 47, 2, 3,
    2, 1123, 2, 1294721, 2, 3, 2, 1433, 2, 5, 2, 3, 2, 7, 2, 137,
    2, 3, 2, 5, 2, 4051603, 2, 3, 2, 389, 2, 7, 2, 3, 2, 269,
    2, 122833, 2, 3, 2, 421, 2, 5, 2, 3, 2, 13, 2, 31, 2, 3,
    2, 5, 2, 301489, 2, 3, 2, 7, 2, 23, 2, 3, 2, 317, 2, 229,
    2, 3, 2, 3027133, 2, 5, 2, 3, 2, 1429, 2, 521, 2, 3, 2, 5,
    2, 139, 2, 3, 2, 19, 2, 239, 2, 3, 2, 47, 2, 11, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 23, 2, 557, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 11, 2, 493457, 2, 3, 2, 13, 2, 19, 2, 3, 2, 991,
    2, 5, 2, 3, 2, 50123, 2, 43, 2, 3, 2, 5, 2, 109, 2, 3,
    2, 17, 2, 13, 2, 3, 2, 79, 2, 7, 2, 3, 2, 29, 2, 5,
    2, 3, 2, 587, 2, 53, 2, 3, 2, 5, 2, 379, 2, 3, 2, 263,
    2, 809, 2, 3, 2, 7, 2, 479, 2, 3, 2, 186587, 2, 5, 2, 3,
    2, 41, 2, 7, 2, 3, 2, 5, 2, 11131, 2, 3, 2, 149, 2, 83,
    2, 3, 2, 2099, 2, 17, 2, 3, 2, 37, 2, 5, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 5, 2, 31, 2, 3, 2, 601283, 2, 7, 2, 3,
    2, 23, 2, 35851, 2, 3, 2, 11, 2, 5, 2, 3, 2, 274829, 2, 13214237,
    2, 3, 2, 5, 2, 197, 2, 3, 2, 7, 2]

/-- Table 9 row: the prime after 323811481625339 is 323811481625339 + 764. -/
theorem gap9_764 : IsGapAt 323811481625339 764 :=
  isGapAt_of 323811481625339 764 (p323811481625339) (by show Nat.Prime 323811481626103; exact p323811481626103) gds_764 (by decide +kernel)

def gds_768 : List ℕ := [
    2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 167, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 13, 2, 19946579, 2, 3, 2, 97187, 2, 23, 2, 3,
    2, 37, 2, 5, 2, 3, 2, 132499, 2, 302171, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 139, 2, 947, 2, 3, 2, 11, 2, 7, 2, 3, 2, 631,
    2, 5, 2, 3, 2, 19, 2, 449, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 43, 2, 47, 2, 3, 2, 7, 2, 2633, 2, 3, 2, 196549, 2, 5,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 17,
    2, 557, 2, 3, 2, 29, 2, 31, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 7, 2, 15061, 2, 3, 2, 5, 2, 173, 2, 3, 2, 15795473, 2, 7,
    2, 3, 2, 10321, 2, 109, 2, 3, 2, 887, 2, 5, 2, 3, 2, 6833,
    2, 113969, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 845951, 2, 3,
    2, 13, 2, 17, 2, 3, 2, 19, 2, 5, 2, 3, 2, 11, 2, 6501637,
    2, 3, 2, 5, 2, 41, 2, 3, 2, 917513, 2, 13, 2, 3, 2, 135367,
    2, 137029, 2, 3, 2, 7, 2, 5, 2, 3, 2, 4523, 2, 19, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 1619, 2, 11, 2, 3, 2, 228023, 2, 5774017,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 3967, 2, 457, 2, 3, 2, 5,
    2, 191, 2, 3, 2, 15557183, 2, 3457, 2, 3, 2, 683, 2, 7, 2, 3,
    2, 7699, 2, 5, 2, 3, 2, 41, 2, 13, 2, 3, 2, 5, 2, 79,
    2, 3, 2, 29, 2, 61, 2, 3, 2, 7, 2, 11, 2, 3, 2, 3677,
    2, 5, 2, 3, 2, 71, 2, 7, 2, 3, 2, 5, 2, 197, 2, 3,
    2, 11, 2, 163, 2, 3, 2, 113, 2, 37, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 7, 2, 10709, 2, 3, 2, 5, 2, 211, 2, 3, 2, 23,
    2, 7, 2, 3, 2, 61381, 2, 13, 2, 3, 2, 89, 2, 5, 2, 3,
    2, 241, 2, 73, 2, 3, 2, 5, 2, 5981, 2, 3, 2, 7, 2, 17,
    2, 3, 2, 11, 2, 229981, 2, 3, 2, 67, 2, 5, 2, 3, 2, 1399,
    2, 101, 2, 3, 2, 5, 2, 29, 2, 3, 2, 13, 2, 125423, 2, 3,
    2, 17, 2, 499, 2, 3, 2, 7, 2, 5, 2, 3, 2, 31, 2, 11,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 543971, 2, 23, 2, 3, 2, 1153,
    2, 19, 2, 3, 2, 11, 2, 5, 2, 3, 2, 47, 2, 83, 2, 3,
    2, 5, 2, 1279, 2, 3, 2, 83983, 2, 439, 2, 3, 2, 37, 2, 7,
    2, 3, 2, 173, 2, 5, 2, 3, 2, 13, 2, 31, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 1069, 2, 2240669, 2, 3, 2, 7, 2, 227, 2, 3,
    2, 103, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 67,
    2, 3, 2, 131, 2, 7229, 2, 3, 2, 61, 2, 331, 2, 3, 2, 977,
    2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5, 2, 117329, 2, 3,
    2, 147853, 2, 7, 2, 3, 2, 13, 2, 78779, 2, 3, 2, 3500477, 2, 5,
    2, 3, 2, 582433, 2, 23, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7,
    2, 13, 2, 3, 2, 43, 2, 53, 2, 3, 2, 79, 2, 5, 2, 3,
    2, 1769909, 2, 4243, 2, 3, 2, 5, 2, 223, 2, 3, 2, 17, 2, 239,
    2, 3, 2, 23, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19,
    2, 59779, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 2657, 2, 3,
    2, 448187, 2, 59, 2, 3, 2, 73, 2, 5, 2, 3, 2, 1979, 2, 13,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 333769, 2, 43, 2, 3, 2, 127,
    2, 7, 2, 3, 2, 199, 2, 5, 2, 3, 2, 37, 2, 1217, 2, 3,
    2, 5, 2, 161881, 2, 3, 2, 151, 2, 953, 2, 3, 2, 7, 2, 23,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 1429, 2, 7, 2, 3, 2, 5,
    2, 155539, 2, 3, 2, 47, 2, 2837773, 2, 3, 2, 97, 2, 13, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2]

/-- Table 9 row: the prime after 423683030575549 is 423683030575549 + 768. -/
theorem gap9_768 : IsGapAt 423683030575549 768 :=
  isGapAt_of 423683030575549 768 (p423683030575549) (by show Nat.Prime 423683030576317; exact p423683030576317) gds_768 (by decide +kernel)

def gds_774 : List ℕ := [
    2, 5, 2, 3, 2, 37, 2, 73, 2, 3, 2, 5, 2, 41, 2, 3,
    2, 30389, 2, 47, 2, 3, 2, 13, 2, 7, 2, 3, 2, 59, 2, 5,
    2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 31, 2, 3, 2, 401,
    2, 13, 2, 3, 2, 7, 2, 1294339, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 802661, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 9973, 2, 17,
    2, 3, 2, 439, 2, 23, 2, 3, 2, 739, 2, 5, 2, 3, 2, 7,
    2, 211, 2, 3, 2, 5, 2, 11, 2, 3, 2, 121763, 2, 7, 2, 3,
    2, 17, 2, 6379, 2, 3, 2, 137, 2, 5, 2, 3, 2, 11, 2, 13,
    2, 3, 2, 5, 2, 257, 2, 3, 2, 7, 2, 41681, 2, 3, 2, 557,
    2, 67, 2, 3, 2, 19, 2, 5, 2, 3, 2, 97, 2, 991883, 2, 3,
    2, 5, 2, 389687, 2, 3, 2, 31, 2, 11, 2, 3, 2, 353, 2, 53,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 27739, 2, 19, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 953, 2, 43, 2, 3, 2, 24469, 2, 13, 2, 3,
    2, 5239987, 2, 5, 2, 3, 2, 17, 2, 1844747, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 37, 2, 31, 2, 3, 2, 20297, 2, 7, 2, 3, 2, 15629,
    2, 5, 2, 3, 2, 29803, 2, 127, 2, 3, 2, 5, 2, 1741, 2, 3,
    2, 11, 2, 41, 2, 3, 2, 7, 2, 59, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 293, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 569,
    2, 61, 2, 3, 2, 733, 2, 30497, 2, 3, 2, 73, 2, 5, 2, 3,
    2, 7, 2, 1331921, 2, 3, 2, 5, 2, 521, 2, 3, 2, 17, 2, 7,
    2, 3, 2, 11, 2, 53503, 2, 3, 2, 15101, 2, 5, 2, 3, 2, 13,
    2, 223, 2, 3, 2, 5, 2, 5869, 2, 3, 2, 7, 2, 97, 2, 3,
    2, 31, 2, 151, 2, 3, 2, 199, 2, 5, 2, 3, 2, 313, 2, 11,
    2, 3, 2, 5, 2, 103, 2, 3, 2, 19, 2, 43591, 2, 3, 2, 59,
    2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 47, 2, 9109, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 23, 2, 924523, 2, 3, 2, 13, 2, 19,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 10588397, 2, 4152289, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 691, 2, 13, 2, 3, 2, 89, 2, 7, 2, 3,
    2, 37, 2, 5, 2, 3, 2, 11, 2, 43, 2, 3, 2, 5, 2, 201923,
    2, 3, 2, 1087, 2, 137363, 2, 3, 2, 7, 2, 480553, 2, 3, 2, 1061,
    2, 5, 2, 3, 2, 17911, 2, 7, 2, 3, 2, 5, 2, 53, 2, 3,
    2, 10305569, 2, 11, 2, 3, 2, 131, 2, 41, 2, 3, 2, 29, 2, 5,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 37, 2, 3, 2, 14356357,
    2, 7, 2, 3, 2, 61, 2, 41911, 2, 3, 2, 31, 2, 5, 2, 3,
    2, 23, 2, 67, 2, 3, 2, 5, 2, 63241, 2, 3, 2, 7, 2, 431,
    2, 3, 2, 449, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 347,
    2, 1225501, 2, 3, 2, 5, 2, 47, 2, 3, 2, 11, 2, 17, 2, 3,
    2, 956861, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 174457,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 29927, 2, 59, 2, 3, 2, 17,
    2, 29, 2, 3, 2, 43, 2, 5, 2, 3, 2, 79, 2, 23, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 13, 2, 1657, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 83, 2, 5, 2, 3, 2, 4200587, 2, 137, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 47, 2, 2137, 2, 3, 2, 7, 2, 397, 2, 3,
    2, 41627, 2, 5, 2, 3, 2, 1873, 2, 7, 2, 3, 2, 5, 2, 6089,
    2, 3, 2, 11974537, 2, 7949, 2, 3, 2, 1863049, 2, 43, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 7, 2, 3881, 2, 3, 2, 5, 2, 1063, 2, 3,
    2, 59, 2, 7, 2, 3, 2, 241, 2, 37, 2, 3, 2, 1997, 2, 5,
    2, 3, 2, 127, 2, 19, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7,
    2, 1933, 2, 3, 2]

/-- Table 9 row: the prime after 469789142849483 is 469789142849483 + 774. -/
theorem gap9_774 : IsGapAt 469789142849483 774 :=
  isGapAt_of 469789142849483 774 (p469789142849483) (by show Nat.Prime 469789142850257; exact p469789142850257) gds_774 (by decide +kernel)

def gds_780 : List ℕ := [
    2, 5, 2, 3, 2, 877, 2, 9397, 2, 3, 2, 5, 2, 4147147, 2, 3,
    2, 661, 2, 11, 2, 3, 2, 31, 2, 47309, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 27827, 2, 199, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19,
    2, 37, 2, 3, 2, 29, 2, 106367, 2, 3, 2, 113, 2, 5, 2, 3,
    2, 9923, 2, 434461, 2, 3, 2, 5, 2, 2731, 2, 3, 2, 569, 2, 83,
    2, 3, 2, 47, 2, 7, 2, 3, 2, 107, 2, 5, 2, 3, 2, 67,
    2, 13, 2, 3, 2, 5, 2, 271853, 2, 3, 2, 11, 2, 499, 2, 3,
    2, 7, 2, 79, 2, 3, 2, 311, 2, 5, 2, 3, 2, 73, 2, 7,
    2, 3, 2, 5, 2, 41, 2, 3, 2, 6323, 2, 114859, 2, 3, 2, 2183789,
    2, 61, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 157, 2, 3,
    2, 5, 2, 149, 2, 3, 2, 59, 2, 7, 2, 3, 2, 11, 2, 13,
    2, 3, 2, 2203, 2, 5, 2, 3, 2, 181, 2, 212791, 2, 3, 2, 5,
    2, 3848447, 2, 3, 2, 7, 2, 17, 2, 3, 2, 163, 2, 251533, 2, 3,
    2, 31, 2, 5, 2, 3, 2, 41, 2, 11, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 13, 2, 67, 2, 3, 2, 17, 2, 55009, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 83, 2, 43, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 3329, 2, 71, 2, 3, 2, 277, 2, 259009, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 19, 2, 313, 2, 3, 2, 5, 2, 11, 2, 3, 2, 577331,
    2, 10213799, 2, 3, 2, 223637, 2, 7, 2, 3, 2, 13747933, 2, 5, 2, 3,
    2, 11, 2, 829, 2, 3, 2, 5, 2, 19, 2, 3, 2, 86353, 2, 461,
    2, 3, 2, 7, 2, 2473, 2, 3, 2, 3547, 2, 5, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 227, 2, 11, 2, 3,
    2, 3600917, 2, 159233, 2, 3, 2, 2129819, 2, 5, 2, 3, 2, 7, 2, 89,
    2, 3, 2, 5, 2, 151, 2, 3, 2, 449, 2, 7, 2, 3, 2, 13,
    2, 14220197, 2, 3, 2, 19, 2, 5, 2, 3, 2, 31, 2, 7128749, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 7, 2, 13, 2, 3, 2, 2777, 2, 11,
    2, 3, 2, 37, 2, 5, 2, 3, 2, 239, 2, 19, 2, 3, 2, 5,
    2, 359, 2, 3, 2, 11, 2, 137, 2, 3, 2, 127, 2, 191, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 47869, 2, 31, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 53, 2, 1459, 2, 3, 2, 39703, 2, 10601, 2, 3, 2, 7129,
    2, 5, 2, 3, 2, 563, 2, 13, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 67, 2, 23, 2, 3, 2, 11, 2, 7, 2, 3, 2, 491, 2, 5,
    2, 3, 2, 2321017, 2, 29, 2, 3, 2, 5, 2, 13337, 2, 3, 2, 11329,
    2, 109, 2, 3, 2, 7, 2, 42709, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 23, 2, 7, 2, 3, 2, 5, 2, 47, 2, 3, 2, 59011, 2, 101,
    2, 3, 2, 73, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7,
    2, 83, 2, 3, 2, 5, 2, 1399, 2, 3, 2, 10622099, 2, 7, 2, 3,
    2, 90511, 2, 54493, 2, 3, 2, 316777, 2, 5, 2, 3, 2, 1289, 2, 17,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 1361, 2, 3, 2, 347,
    2, 41, 2, 3, 2, 997, 2, 5, 2, 3, 2, 11, 2, 23, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 47, 2, 131, 2, 3, 2, 739, 2, 19,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 283, 2, 1193, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 43, 2, 11, 2, 3, 2, 23, 2, 71, 2, 3,
    2, 1181, 2, 5, 2, 3, 2, 13, 2, 127, 2, 3, 2, 5, 2, 941,
    2, 3, 2, 41, 2, 17, 2, 3, 2, 137, 2, 7, 2, 3, 2, 6827,
    2, 5, 2, 3, 2, 263, 2, 13360511, 2, 3, 2, 5, 2, 8443, 2, 3,
    2, 113, 2, 2381, 2, 3, 2, 7, 2, 11, 2, 3, 2, 29, 2, 5,
    2, 3, 2, 61, 2, 7, 2, 3, 2, 5, 2, 43, 2, 3, 2, 11,
    2, 19, 2, 3, 2, 13, 2, 23, 2, 3, 2]

/-- Table 9 row: the prime after 471911699384963 is 471911699384963 + 780. -/
theorem gap9_780 : IsGapAt 471911699384963 780 :=
  isGapAt_of 471911699384963 780 (p471911699384963) (by show Nat.Prime 471911699385743; exact p471911699385743) gds_780 (by decide +kernel)

def gds_782 : List ℕ := [
    2, 17, 2, 3, 2, 7, 2, 4313917, 2, 3, 2, 1129, 2, 5, 2, 3,
    2, 1390247, 2, 7, 2, 3, 2, 5, 2, 79, 2, 3, 2, 1361, 2, 13,
    2, 3, 2, 17, 2, 44189, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 5, 2, 23, 2, 3, 2, 2459, 2, 7, 2, 3,
    2, 26321, 2, 563, 2, 3, 2, 11, 2, 5, 2, 3, 2, 89, 2, 19,
    2, 3, 2, 5, 2, 61, 2, 3, 2, 7, 2, 181, 2, 3, 2, 72923,
    2, 233, 2, 3, 2, 23, 2, 5, 2, 3, 2, 59, 2, 13, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 821, 2, 2269, 2, 3, 2, 43, 2, 277073,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 73, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 606241, 2, 199, 2, 3, 2, 19, 2, 67, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 31, 2, 439919, 2, 3, 2, 5, 2, 26573,
    2, 3, 2, 709, 2, 11, 2, 3, 2, 6343, 2, 7, 2, 3, 2, 179,
    2, 5, 2, 3, 2, 197, 2, 26593109, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 3907, 2, 43, 2, 3, 2, 7, 2, 421, 2, 3, 2, 34819, 2, 5,
    2, 3, 2, 347, 2, 7, 2, 3, 2, 5, 2, 153733, 2, 3, 2, 13,
    2, 37, 2, 3, 2, 163, 2, 11, 2, 3, 2, 113969, 2, 5, 2, 3,
    2, 7, 2, 139, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 1283, 2, 691, 2, 3, 2, 48809, 2, 5, 2, 3, 2, 910229,
    2, 613, 2, 3, 2, 5, 2, 83, 2, 3, 2, 7, 2, 229, 2, 3,
    2, 106949, 2, 17, 2, 3, 2, 29, 2, 5, 2, 3, 2, 13, 2, 503,
    2, 3, 2, 5, 2, 1028029, 2, 3, 2, 61, 2, 23, 2, 3, 2, 11,
    2, 271, 2, 3, 2, 7, 2, 5, 2, 3, 2, 41, 2, 37337, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 569, 2, 117991, 2, 3, 2, 857, 2, 541,
    2, 3, 2, 131, 2, 5, 2, 3, 2, 23, 2, 11, 2, 3, 2, 5,
    2, 641, 2, 3, 2, 37, 2, 109, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 1787, 2, 17, 2, 3, 2, 5, 2, 31,
    2, 3, 2, 2311, 2, 13, 2, 3, 2, 7, 2, 29, 2, 3, 2, 73,
    2, 5, 2, 3, 2, 47, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 1982599, 2, 61, 2, 3, 2, 1385843, 2, 193, 2, 3, 2, 59, 2, 5,
    2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 2791, 2, 3, 2, 257,
    2, 7, 2, 3, 2, 29, 2, 1429, 2, 3, 2, 467, 2, 5, 2, 3,
    2, 19, 2, 13, 2, 3, 2, 5, 2, 53, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 23, 2, 251, 2, 3, 2, 829, 2, 5, 2, 3, 2, 151,
    2, 227, 2, 3, 2, 5, 2, 19, 2, 3, 2, 31, 2, 1187, 2, 3,
    2, 17, 2, 9941, 2, 3, 2, 7, 2, 5, 2, 3, 2, 433, 2, 67,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 359, 2, 163, 2, 3, 2, 13870601,
    2, 11, 2, 3, 2, 45989, 2, 5, 2, 3, 2, 6922901, 2, 2357, 2, 3,
    2, 5, 2, 5647, 2, 3, 2, 11, 2, 29, 2, 3, 2, 95621, 2, 7,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 389, 2, 16001, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 13, 2, 79657, 2, 3, 2, 7, 2, 353, 2, 3,
    2, 43, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 29, 2, 21877673, 2, 3, 2, 11, 2, 2199719, 2, 3, 2, 887,
    2, 5, 2, 3, 2, 7, 2, 137, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 13043, 2, 7, 2, 3, 2, 61, 2, 59, 2, 3, 2, 1021, 2, 5,
    2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7,
    2, 977, 2, 3, 2, 19, 2, 43, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 167, 2, 5857, 2, 3, 2, 5, 2, 23, 2, 3, 2, 17, 2, 127,
    2, 3, 2, 71, 2, 41, 2, 3, 2, 7, 2, 5, 2, 3, 2, 4451,
    2, 461, 2, 3, 2, 5, 2, 7, 2, 3, 2, 6389, 2]

/-- Table 9 row: the prime after 726507223559111 is 726507223559111 + 782. -/
theorem gap9_782 : IsGapAt 726507223559111 782 :=
  isGapAt_of 726507223559111 782 (p726507223559111) (by show Nat.Prime 726507223559893; exact p726507223559893) gds_782 (by decide +kernel)

def gds_796 : List ℕ := [
    2, 3, 2, 17, 2, 13, 2, 3, 2, 1009, 2, 101, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 23176717, 2, 6067, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 25367, 2, 3209, 2, 3, 2, 3851, 2, 163, 2, 3, 2, 103, 2, 5,
    2, 3, 2, 11, 2, 31, 2, 3, 2, 5, 2, 26699, 2, 3, 2, 37,
    2, 47, 2, 3, 2, 61, 2, 7, 2, 3, 2, 2153, 2, 5, 2, 3,
    2, 550061, 2, 13, 2, 3, 2, 5, 2, 23, 2, 3, 2, 19, 2, 11,
    2, 3, 2, 7, 2, 2371, 2, 3, 2, 17, 2, 5, 2, 3, 2, 967,
    2, 7, 2, 3, 2, 5, 2, 31727, 2, 3, 2, 43, 2, 257, 2, 3,
    2, 41, 2, 19, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 681823,
    2, 3, 2, 5, 2, 41023, 2, 3, 2, 29, 2, 7, 2, 3, 2, 47,
    2, 11, 2, 3, 2, 499661, 2, 5, 2, 3, 2, 1399, 2, 17, 2, 3,
    2, 5, 2, 15329, 2, 3, 2, 7, 2, 1107049, 2, 3, 2, 53, 2, 61,
    2, 3, 2, 424027, 2, 5, 2, 3, 2, 127, 2, 149, 2, 3, 2, 5,
    2, 43, 2, 3, 2, 13, 2, 137, 2, 3, 2, 653539, 2, 11731141, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 3614179, 2, 15803, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 429589, 2, 19, 2, 3, 2, 11, 2, 103, 2, 3, 2, 839,
    2, 5, 2, 3, 2, 2027, 2, 1777, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 23, 2, 17, 2, 3, 2, 503, 2, 7, 2, 3, 2, 37, 2, 5,
    2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 9619, 2, 3, 2, 16538351,
    2, 7717, 2, 3, 2, 7, 2, 122209, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 5, 2, 479, 2, 3, 2, 1531, 2, 823,
    2, 3, 2, 1013, 2, 1523, 2, 3, 2, 7537, 2, 5, 2, 3, 2, 7,
    2, 3371, 2, 3, 2, 5, 2, 11, 2, 3, 2, 31, 2, 7, 2, 3,
    2, 13, 2, 227, 2, 3, 2, 41, 2, 5, 2, 3, 2, 11, 2, 59,
    2, 3, 2, 5, 2, 113, 2, 3, 2, 7, 2, 13, 2, 3, 2, 1087,
    2, 53, 2, 3, 2, 74521, 2, 5, 2, 3, 2, 17, 2, 77659, 2, 3,
    2, 5, 2, 67, 2, 3, 2, 199, 2, 11, 2, 3, 2, 799837, 2, 9739,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 47, 2, 29, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 4663699, 2, 127, 2, 3, 2, 89, 2, 476009, 2, 3,
    2, 281, 2, 5, 2, 3, 2, 84857, 2, 13, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 607, 2, 191, 2, 3, 2, 137, 2, 7, 2, 3, 2, 2029,
    2, 5, 2, 3, 2, 29, 2, 23, 2, 3, 2, 5, 2, 97, 2, 3,
    2, 11, 2, 423931, 2, 3, 2, 7, 2, 457399, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 239, 2, 7, 2, 3, 2, 5, 2, 41, 2, 3, 2, 3203,
    2, 181, 2, 3, 2, 19, 2, 13, 2, 3, 2, 3274961, 2, 5, 2, 3,
    2, 7, 2, 179, 2, 3, 2, 5, 2, 1987, 2, 3, 2, 10678183, 2, 7,
    2, 3, 2, 11, 2, 17, 2, 3, 2, 83, 2, 5, 2, 3, 2, 577,
    2, 197, 2, 3, 2, 5, 2, 104281, 2, 3, 2, 7, 2, 131543, 2, 3,
    2, 1619, 2, 31, 2, 3, 2, 17, 2, 5, 2, 3, 2, 41, 2, 11,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 827, 2, 157, 2, 3, 2, 43,
    2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 1097, 2, 9084391, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 19, 2, 65599, 2, 3, 2, 311, 2, 48767,
    2, 3, 2, 29, 2, 5, 2, 3, 2, 13, 2, 17, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 163, 2, 53791, 2, 3, 2, 722273, 2, 7, 2, 3,
    2, 383, 2, 5, 2, 3, 2, 11, 2, 107, 2, 3, 2, 5, 2, 53,
    2, 3, 2, 47, 2, 43, 2, 3, 2, 7, 2, 229, 2, 3, 2, 31,
    2, 5, 2, 3, 2, 631, 2, 7, 2, 3, 2, 5, 2, 20311901, 2, 3,
    2, 109, 2, 11, 2, 3, 2, 13, 2, 1063, 2, 3, 2, 4919, 2, 5,
    2, 3, 2, 7, 2, 21143, 2, 3, 2, 5, 2, 23, 2, 3, 2, 941,
    2, 7, 2, 3, 2, 271, 2, 29, 2, 3, 2]

/-- Table 9 row: the prime after 1271309838631957 is 1271309838631957 + 796. -/
theorem gap9_796 : IsGapAt 1271309838631957 796 :=
  isGapAt_of 1271309838631957 796 (p1271309838631957) (by show Nat.Prime 1271309838632753; exact p1271309838632753) gds_796 (by decide +kernel)

def gds_812 : List ℕ := [
    2, 83, 2, 3, 2, 11, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 673, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 163, 2, 17,
    2, 3, 2, 43, 2, 137, 2, 3, 2, 811, 2, 5, 2, 3, 2, 256117,
    2, 11, 2, 3, 2, 5, 2, 1209739, 2, 3, 2, 1837739, 2, 78721, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 408869, 2, 6367,
    2, 3, 2, 5, 2, 223, 2, 3, 2, 353, 2, 2593, 2, 3, 2, 7,
    2, 13, 2, 3, 2, 2647, 2, 5, 2, 3, 2, 7039, 2, 7, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 157, 2, 41, 2, 3, 2, 421, 2, 5743,
    2, 3, 2, 172829, 2, 5, 2, 3, 2, 7, 2, 103, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 13, 2, 7, 2, 3, 2, 79, 2, 37, 2, 3,
    2, 61, 2, 5, 2, 3, 2, 17, 2, 1229, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 269, 2, 9689231, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 9811, 2, 29, 2, 3, 2, 5, 2, 31, 2, 3,
    2, 19, 2, 45697, 2, 3, 2, 263, 2, 257, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 13, 2, 853, 2, 3, 2, 5, 2, 7, 2, 3, 2, 571,
    2, 397, 2, 3, 2, 1529903, 2, 11, 2, 3, 2, 751, 2, 5, 2, 3,
    2, 29, 2, 47, 2, 3, 2, 5, 2, 127, 2, 3, 2, 11, 2, 11261,
    2, 3, 2, 32887, 2, 7, 2, 3, 2, 22637, 2, 5, 2, 3, 2, 1619,
    2, 107, 2, 3, 2, 5, 2, 347, 2, 3, 2, 1493, 2, 15176867, 2, 3,
    2, 7, 2, 227, 2, 3, 2, 137, 2, 5, 2, 3, 2, 4523, 2, 7,
    2, 3, 2, 5, 2, 18059, 2, 3, 2, 23, 2, 13, 2, 3, 2, 11,
    2, 17, 2, 3, 2, 53, 2, 5, 2, 3, 2, 7, 2, 1163, 2, 3,
    2, 5, 2, 163, 2, 3, 2, 73, 2, 7, 2, 3, 2, 151, 2, 41,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 3925829, 2, 11, 2, 3, 2, 5,
    2, 7589, 2, 3, 2, 7, 2, 31, 2, 3, 2, 1235093, 2, 25303, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 541, 2, 13, 2, 3, 2, 5, 2, 26921,
    2, 3, 2, 13043, 2, 23, 2, 3, 2, 293, 2, 521, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 19, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 41, 2, 467, 2, 3, 2, 5189, 2, 24133, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 11, 2, 8255197, 2, 3, 2, 5, 2, 19, 2, 3, 2, 5167,
    2, 457, 2, 3, 2, 9473, 2, 7, 2, 3, 2, 401, 2, 5, 2, 3,
    2, 379, 2, 83, 2, 3, 2, 5, 2, 73, 2, 3, 2, 997, 2, 11,
    2, 3, 2, 7, 2, 12583, 2, 3, 2, 1198081, 2, 5, 2, 3, 2, 37,
    2, 7, 2, 3, 2, 5, 2, 7211, 2, 3, 2, 13, 2, 17, 2, 3,
    2, 1033, 2, 29, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 23,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 41192639, 2, 7, 2, 3, 2, 17,
    2, 11, 2, 3, 2, 59, 2, 5, 2, 3, 2, 14595499, 2, 19, 2, 3,
    2, 5, 2, 97, 2, 3, 2, 7, 2, 37, 2, 3, 2, 23, 2, 3823,
    2, 3, 2, 101, 2, 5, 2, 3, 2, 13, 2, 877, 2, 3, 2, 5,
    2, 19592579, 2, 3, 2, 79, 2, 9733, 2, 3, 2, 47, 2, 43, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 359, 2, 61, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 53, 2, 751871, 2, 3, 2, 11, 2, 151, 2, 3, 2, 3733687,
    2, 5, 2, 3, 2, 17, 2, 659, 2, 3, 2, 5, 2, 37991, 2, 3,
    2, 217201, 2, 1514197, 2, 3, 2, 13, 2, 7, 2, 3, 2, 31, 2, 5,
    2, 3, 2, 13763, 2, 11, 2, 3, 2, 5, 2, 21229471, 2, 3, 2, 281,
    2, 13, 2, 3, 2, 7, 2, 439, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 641, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 37, 2, 109,
    2, 3, 2, 607, 2, 103, 2, 3, 2, 227, 2, 5, 2, 3, 2, 7,
    2, 65353, 2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2, 7, 2, 3,
    2, 743, 2, 79, 2, 3, 2, 1193, 2, 5, 2, 3, 2, 11, 2, 13,
    2, 3, 2, 5, 2, 76801, 2, 3, 2, 7, 2]

/-- Table 9 row: the prime after 1710270958551941 is 1710270958551941 + 812. -/
theorem gap9_812 : IsGapAt 1710270958551941 812 :=
  isGapAt_of 1710270958551941 812 (p1710270958551941) (by show Nat.Prime 1710270958552753; exact p1710270958552753) gds_812 (by decide +kernel)

def gds_848 : List ℕ := [
    2, 5, 2, 3, 2, 53, 2, 13, 2, 3, 2, 5, 2, 487, 2, 3,
    2, 7, 2, 17, 2, 3, 2, 19, 2, 11, 2, 3, 2, 101, 2, 5,
    2, 3, 2, 24239, 2, 3301, 2, 3, 2, 5, 2, 317, 2, 3, 2, 11,
    2, 262733, 2, 3, 2, 17, 2, 103, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 36049817, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 113, 2, 2791577,
    2, 3, 2, 2626927, 2, 13, 2, 3, 2, 283, 2, 5, 2, 3, 2, 10501,
    2, 71, 2, 3, 2, 5, 2, 43, 2, 3, 2, 313, 2, 31, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 1423, 2, 5, 2, 3, 2, 157, 2, 37,
    2, 3, 2, 5, 2, 3833, 2, 3, 2, 13, 2, 1103, 2, 3, 2, 7,
    2, 2293, 2, 3, 2, 1229, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 39163741, 2, 29, 2, 3, 2, 929, 2, 19,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 3433, 2, 3, 2, 5,
    2, 67, 2, 3, 2, 1151, 2, 7, 2, 3, 2, 47911, 2, 23, 2, 3,
    2, 373, 2, 5, 2, 3, 2, 13, 2, 41, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 1087, 2, 3, 2, 31, 2, 6393641, 2, 3, 2, 71,
    2, 5, 2, 3, 2, 11, 2, 191, 2, 3, 2, 5, 2, 131, 2, 3,
    2, 17, 2, 47, 2, 3, 2, 79, 2, 181, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 37, 2, 4373, 2, 3, 2, 5, 2, 7, 2, 3, 2, 463,
    2, 11, 2, 3, 2, 13, 2, 31, 2, 3, 2, 41, 2, 5, 2, 3,
    2, 557, 2, 586841, 2, 3, 2, 5, 2, 433, 2, 3, 2, 97, 2, 13,
    2, 3, 2, 53, 2, 7, 2, 3, 2, 1731701, 2, 5, 2, 3, 2, 48497,
    2, 59, 2, 3, 2, 5, 2, 23, 2, 3, 2, 83, 2, 37, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 17, 2, 5, 2, 3, 2, 19, 2, 7,
    2, 3, 2, 5, 2, 3511, 2, 3, 2, 11, 2, 73, 2, 3, 2, 337,
    2, 197, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 61, 2, 7, 2, 3, 2, 787, 2, 761,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 251, 2, 17, 2, 3, 2, 5,
    2, 101, 2, 3, 2, 7, 2, 157, 2, 3, 2, 11, 2, 7549, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 59, 2, 14403817, 2, 3, 2, 5, 2, 41,
    2, 3, 2, 103, 2, 941, 2, 3, 2, 1609, 2, 13, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 139, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 37, 2, 1693, 2, 3, 2, 2439919, 2, 41236997, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 131, 2, 19, 2, 3, 2, 5, 2, 71, 2, 3, 2, 13,
    2, 17, 2, 3, 2, 43, 2, 7, 2, 3, 2, 241, 2, 5, 2, 3,
    2, 41, 2, 11981, 2, 3, 2, 5, 2, 11, 2, 3, 2, 701, 2, 419,
    2, 3, 2, 7, 2, 821, 2, 3, 2, 36037, 2, 5, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 5, 2, 809, 2, 3, 2, 7193, 2, 517403, 2, 3,
    2, 19, 2, 67, 2, 3, 2, 37273, 2, 5, 2, 3, 2, 7, 2, 334991,
    2, 3, 2, 5, 2, 651067, 2, 3, 2, 18503, 2, 7, 2, 3, 2, 16553,
    2, 137, 2, 3, 2, 191, 2, 5, 2, 3, 2, 47, 2, 431993, 2, 3,
    2, 5, 2, 617, 2, 3, 2, 7, 2, 401, 2, 3, 2, 269, 2, 283,
    2, 3, 2, 33623, 2, 5, 2, 3, 2, 17, 2, 31, 2, 3, 2, 5,
    2, 103, 2, 3, 2, 317, 2, 83, 2, 3, 2, 13, 2, 11, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 4500491, 2, 1489, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 11, 2, 13, 2, 3, 2, 29173663, 2, 51133, 2, 3, 2, 37,
    2, 5, 2, 3, 2, 229, 2, 37423, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 79, 2, 647, 2, 3, 2, 293, 2, 7, 2, 3, 2, 29, 2, 5,
    2, 3, 2, 113, 2, 23, 2, 3, 2, 5, 2, 139, 2, 3, 2, 17,
    2, 107, 2, 3, 2, 7, 2, 263, 2, 3, 2, 197, 2, 5, 2, 3,
    2, 7993, 2, 7, 2, 3, 2, 5, 2, 37, 2, 3, 2, 54469, 2, 30841,
    2, 3, 2, 23, 2, 301267, 2, 3, 2, 59, 2, 5, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 5, 2, 47, 2, 3, 2, 48995633, 2, 7, 2, 3,
    2, 109, 2, 17, 2, 3, 2, 11, 2, 5, 2, 3, 2, 83, 2]

/-- Table 9 row: the prime after 2537070652896083 is 2537070652896083 + 848. -/
theorem gap9_848 : IsGapAt 2537070652896083 848 :=
  isGapAt_of 2537070652896083 848 (p2537070652896083) (by show Nat.Prime 2537070652896931; exact p2537070652896931) gds_848 (by decide +kernel)

def gds_866 : List ℕ := [
    2, 43, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 103, 2, 3,
    2, 5, 2, 9907, 2, 3, 2, 61, 2, 29, 2, 3, 2, 88681, 2, 13,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 31, 2, 19, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 1350607, 2, 11, 2, 3, 2, 1201, 2, 17, 2, 3,
    2, 67, 2, 5, 2, 3, 2, 149, 2, 47, 2, 3, 2, 5, 2, 257783,
    2, 3, 2, 13, 2, 131, 2, 3, 2, 587, 2, 7, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 23, 2, 31, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 34910489, 2, 27271873, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5368267, 2, 5,
    2, 3, 2, 23603, 2, 7, 2, 3, 2, 5, 2, 251, 2, 3, 2, 11,
    2, 61, 2, 3, 2, 61819, 2, 73, 2, 3, 2, 37, 2, 5, 2, 3,
    2, 7, 2, 17, 2, 3, 2, 5, 2, 331, 2, 3, 2, 43, 2, 7,
    2, 3, 2, 809, 2, 7755161, 2, 3, 2, 41, 2, 5, 2, 3, 2, 2129,
    2, 23, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 449, 2, 3,
    2, 11, 2, 171091, 2, 3, 2, 1871, 2, 5, 2, 3, 2, 5347, 2, 137,
    2, 3, 2, 5, 2, 37, 2, 3, 2, 19, 2, 811, 2, 3, 2, 13,
    2, 6653, 2, 3, 2, 7, 2, 5, 2, 3, 2, 4423, 2, 11, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 487, 2, 13, 2, 3, 2, 11959, 2, 19,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 337, 2, 1253717, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 4733, 2, 1063, 2, 3, 2, 17, 2, 7, 2, 3,
    2, 379, 2, 5, 2, 3, 2, 239, 2, 767527, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 623671, 2, 101, 2, 3, 2, 7, 2, 23, 2, 3, 2, 431,
    2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 41, 2, 3,
    2, 13645013, 2, 47, 2, 3, 2, 1031, 2, 541, 2, 3, 2, 7001, 2, 5,
    2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 48527, 2, 3, 2, 15986071,
    2, 7, 2, 3, 2, 61, 2, 59, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 17, 2, 9631, 2, 3, 2, 5, 2, 461, 2, 3, 2, 7, 2, 83,
    2, 3, 2, 269, 2, 13, 2, 3, 2, 79, 2, 5, 2, 3, 2, 29,
    2, 227, 2, 3, 2, 5, 2, 977, 2, 3, 2, 73, 2, 109, 2, 3,
    2, 47, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 474359,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 31, 2, 3, 2, 383,
    2, 421, 2, 3, 2, 127, 2, 5, 2, 3, 2, 314267, 2, 27089977, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 17, 2, 40767101, 2, 3, 2, 59, 2, 7,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 443, 2, 163, 2, 3, 2, 5,
    2, 37573, 2, 3, 2, 12241, 2, 2081, 2, 3, 2, 7, 2, 353053, 2, 3,
    2, 349, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 2909,
    2, 3, 2, 123499, 2, 223, 2, 3, 2, 54631, 2, 17, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 73, 2, 3,
    2, 140663, 2, 7, 2, 3, 2, 31, 2, 67, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 223849, 2, 19, 2, 3, 2, 5, 2, 120929, 2, 3, 2, 7,
    2, 53, 2, 3, 2, 13, 2, 103, 2, 3, 2, 10651, 2, 5, 2, 3,
    2, 251, 2, 1345633, 2, 3, 2, 5, 2, 11, 2, 3, 2, 23, 2, 13,
    2, 3, 2, 647, 2, 31, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11,
    2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 211, 2, 107, 2, 3,
    2, 19, 2, 528709, 2, 3, 2, 113, 2, 5, 2, 3, 2, 139, 2, 3813679,
    2, 3, 2, 5, 2, 503, 2, 3, 2, 11467, 2, 11, 2, 3, 2, 250721,
    2, 7, 2, 3, 2, 709, 2, 5, 2, 3, 2, 47, 2, 13, 2, 3,
    2, 5, 2, 127, 2, 3, 2, 241, 2, 23, 2, 3, 2, 7, 2, 947,
    2, 3, 2, 61, 2, 5, 2, 3, 2, 521359, 2, 7, 2, 3, 2, 5,
    2, 1447, 2, 3, 2, 3923, 2, 17, 2, 3, 2, 29, 2, 11, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 7, 2, 199, 2, 3, 2, 5, 2, 16943,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 17, 2, 13, 2, 3, 2, 3911,
    2, 5, 2, 3, 2, 37, 2, 347, 2, 3, 2, 5, 2, 16075667, 2, 3,
    2, 7, 2, 36629, 2, 3, 2, 24917, 2, 19, 2, 3, 2, 293, 2, 5,
    2, 3, 2, 1248193, 2, 4409, 2, 3, 2, 5, 2, 1009873, 2, 3, 2, 13,
    2]

/-- Table 9 row: the prime after 2759317684446707 is 2759317684446707 + 866. -/
theorem gap9_866 : IsGapAt 2759317684446707 866 :=
  isGapAt_of 2759317684446707 866 (p2759317684446707) (by show Nat.Prime 2759317684447573; exact p2759317684447573) gds_866 (by decide +kernel)

def gds_882 : List ℕ := [
    2, 13, 2, 3, 2, 56883353, 2, 5, 2, 3, 2, 165443, 2, 17, 2, 3,
    2, 5, 2, 43, 2, 3, 2, 18059, 2, 271013, 2, 3, 2, 11, 2, 37607,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 1621, 2, 31, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 13, 2, 2649923, 2, 3, 2, 859, 2, 29, 2, 3,
    2, 59, 2, 5, 2, 3, 2, 41911, 2, 11, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 131, 2, 2053211, 2, 3, 2, 97, 2, 7, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 2251517, 2, 1399, 2, 3, 2, 5, 2, 19387, 2, 3,
    2, 71, 2, 17, 2, 3, 2, 7, 2, 23, 2, 3, 2, 193, 2, 5,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 1487,
    2, 47, 2, 3, 2, 17, 2, 2113, 2, 3, 2, 53, 2, 5, 2, 3,
    2, 7, 2, 3776719, 2, 3, 2, 5, 2, 577, 2, 3, 2, 16349, 2, 7,
    2, 3, 2, 76757, 2, 37, 2, 3, 2, 79, 2, 5, 2, 3, 2, 43,
    2, 101, 2, 3, 2, 5, 2, 104681, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 13, 2, 1339087, 2, 3, 2, 7219, 2, 5, 2, 3, 2, 11923, 2, 709,
    2, 3, 2, 5, 2, 31, 2, 3, 2, 197, 2, 13, 2, 3, 2, 47,
    2, 41, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 167, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 19, 2, 163, 2, 3, 2, 269, 2, 11,
    2, 3, 2, 103, 2, 5, 2, 3, 2, 3011, 2, 97, 2, 3, 2, 5,
    2, 5113, 2, 3, 2, 11, 2, 317, 2, 3, 2, 113, 2, 7, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 1493, 2, 13, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 41, 2, 25525781, 2, 3, 2, 7, 2, 137, 2, 3, 2, 919,
    2, 5, 2, 3, 2, 9661, 2, 7, 2, 3, 2, 5, 2, 223, 2, 3,
    2, 17, 2, 42491, 2, 3, 2, 11, 2, 659, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 7, 2, 908857, 2, 3, 2, 5, 2, 239, 2, 3, 2, 457,
    2, 7, 2, 3, 2, 656707, 2, 13, 2, 3, 2, 101, 2, 5, 2, 3,
    2, 11527, 2, 11, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 19,
    2, 3, 2, 59, 2, 17, 2, 3, 2, 11, 2, 5, 2, 3, 2, 61169,
    2, 191, 2, 3, 2, 5, 2, 587, 2, 3, 2, 13, 2, 4519, 2, 3,
    2, 43, 2, 17167, 2, 3, 2, 7, 2, 5, 2, 3, 2, 61909, 2, 25453,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 53, 2, 1607, 2, 3, 2, 3253,
    2, 103, 2, 3, 2, 3449, 2, 5, 2, 3, 2, 11, 2, 2498183, 2, 3,
    2, 5, 2, 83, 2, 3, 2, 503, 2, 757, 2, 3, 2, 157, 2, 7,
    2, 3, 2, 307, 2, 5, 2, 3, 2, 13, 2, 17, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 1129, 2, 11, 2, 3, 2, 7, 2, 149, 2, 3,
    2, 809, 2, 5, 2, 3, 2, 37, 2, 7, 2, 3, 2, 5, 2, 127,
    2, 3, 2, 139, 2, 2272453, 2, 3, 2, 41, 2, 569, 2, 3, 2, 6852799,
    2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 2026789, 2, 3,
    2, 179, 2, 7, 2, 3, 2, 13, 2, 11, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 74311, 2, 2411, 2, 3, 2, 5, 2, 1571, 2, 3, 2, 7,
    2, 13, 2, 3, 2, 73, 2, 5479, 2, 3, 2, 15601, 2, 5, 2, 3,
    2, 29, 2, 19, 2, 3, 2, 5, 2, 2251, 2, 3, 2, 883, 2, 59,
    2, 3, 2, 17, 2, 271, 2, 3, 2, 7, 2, 5, 2, 3, 2, 97,
    2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 173, 2, 53, 2, 3,
    2, 11, 2, 3637, 2, 3, 2, 14144477, 2, 5, 2, 3, 2, 6311, 2, 13,
    2, 3, 2, 5, 2, 47, 2, 3, 2, 878309, 2, 45987853, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 64303, 2, 11, 2, 3,
    2, 5, 2, 10949, 2, 3, 2, 1653997, 2, 293, 2, 3, 2, 7, 2, 113,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5,
    2, 89, 2, 3, 2, 37, 2, 73, 2, 3, 2, 483017, 2, 13, 2, 3,
    2, 571, 2, 5, 2, 3, 2, 7, 2, 43, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 47, 2, 7, 2, 3, 2, 37785431, 2, 23, 2, 3, 2, 29,
    2, 5, 2, 3, 2, 11, 2, 67, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 7, 2, 65371, 2, 3, 2, 149, 2, 139, 2, 3, 2, 857, 2, 5,
    2, 3, 2, 107, 2, 4121321, 2, 3, 2, 5, 2, 13, 2, 3, 2, 17,
    2, 11, 2, 3, 2, 131, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3,
    2]

/-- Table 9 row: the prime after 3371055452381147 is 3371055452381147 + 882. -/
theorem gap9_882 : IsGapAt 3371055452381147 882 :=
  isGapAt_of 3371055452381147 882 (p3371055452381147) (by show Nat.Prime 3371055452382029; exact p3371055452382029) gds_882 (by decide +kernel)

def gds_886 : List ℕ := [
    2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 41, 2, 3, 2, 13,
    2, 11, 2, 3, 2, 31, 2, 5, 2, 3, 2, 2137, 2, 23, 2, 3,
    2, 5, 2, 463, 2, 3, 2, 11, 2, 13, 2, 3, 2, 59617, 2, 43,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 53419901, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 1307, 2, 1159027, 2, 3, 2, 23, 2, 421, 2, 3,
    2, 71, 2, 5, 2, 3, 2, 193, 2, 67, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 263, 2, 59, 2, 3, 2, 11, 2, 7, 2, 3, 2, 151,
    2, 5, 2, 3, 2, 853, 2, 13, 2, 3, 2, 5, 2, 3769, 2, 3,
    2, 131, 2, 7547, 2, 3, 2, 7, 2, 271, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 54437, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 124669,
    2, 79, 2, 3, 2, 955469, 2, 23, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 7, 2, 53, 2, 3, 2, 5, 2, 120209, 2, 3, 2, 104179, 2, 7,
    2, 3, 2, 577, 2, 13, 2, 3, 2, 37, 2, 5, 2, 3, 2, 31,
    2, 17, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 47, 2, 3,
    2, 495827, 2, 369959, 2, 3, 2, 58417, 2, 5, 2, 3, 2, 11, 2, 29485817,
    2, 3, 2, 5, 2, 3547, 2, 3, 2, 13, 2, 1880789, 2, 3, 2, 23285011,
    2, 41, 2, 3, 2, 7, 2, 5, 2, 3, 2, 5477, 2, 31, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 2621, 2, 11, 2, 3, 2, 19, 2, 167,
    2, 3, 2, 38747, 2, 5, 2, 3, 2, 2879, 2, 97, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 73, 2, 17, 2, 3, 2, 47, 2, 7, 2, 3,
    2, 21283, 2, 5, 2, 3, 2, 13, 2, 29, 2, 3, 2, 5, 2, 367,
    2, 3, 2, 41, 2, 3371, 2, 3, 2, 7, 2, 11, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 67, 2, 7, 2, 3, 2, 5, 2, 71, 2, 3,
    2, 11, 2, 211, 2, 3, 2, 4111, 2, 1621, 2, 3, 2, 227, 2, 5,
    2, 3, 2, 7, 2, 953, 2, 3, 2, 5, 2, 40961, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 13, 2, 107, 2, 3, 2, 823, 2, 5, 2, 3,
    2, 127, 2, 322429, 2, 3, 2, 5, 2, 431, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 11, 2, 19, 2, 3, 2, 61, 2, 5, 2, 3, 2, 17,
    2, 62723, 2, 3, 2, 5, 2, 31, 2, 3, 2, 443, 2, 1949, 2, 3,
    2, 38273, 2, 3903413, 2, 3, 2, 7, 2, 5, 2, 3, 2, 43, 2, 11,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 67, 2, 3, 2, 3863,
    2, 37, 2, 3, 2, 11, 2, 5, 2, 3, 2, 71, 2, 13, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 45427, 2, 55073, 2, 3, 2, 1291, 2, 7,
    2, 3, 2, 659, 2, 5, 2, 3, 2, 739, 2, 239, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 17, 2, 19, 2, 3, 2, 7, 2, 197, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 509,
    2, 3, 2, 31, 2, 23, 2, 3, 2, 41, 2, 13, 2, 3, 2, 769,
    2, 5, 2, 3, 2, 7, 2, 89, 2, 3, 2, 5, 2, 138569, 2, 3,
    2, 6481, 2, 7, 2, 3, 2, 283, 2, 17, 2, 3, 2, 107, 2, 5,
    2, 3, 2, 19, 2, 1453, 2, 3, 2, 5, 2, 79, 2, 3, 2, 7,
    2, 31, 2, 3, 2, 37, 2, 83, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 7433, 2, 353, 2, 3, 2, 5, 2, 13, 2, 3, 2, 13814887, 2, 127,
    2, 3, 2, 24006893, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 97,
    2, 313, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 12372793, 2, 3,
    2, 1103, 2, 62201869, 2, 3, 2, 1087, 2, 5, 2, 3, 2, 13, 2, 17,
    2, 3, 2, 5, 2, 173, 2, 3, 2, 397, 2, 20287, 2, 3, 2, 29,
    2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 73, 2, 41, 2, 3,
    2, 5, 2, 54307787, 2, 3, 2, 67, 2, 6719, 2, 3, 2, 7, 2, 109,
    2, 3, 2, 15203431, 2, 5, 2, 3, 2, 89, 2, 7, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 139, 2, 71, 2, 3, 2, 13, 2, 163, 2, 3,
    2, 1669, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 53,
    2, 3, 2, 277, 2, 7, 2, 3, 2, 213361, 2, 31, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 28387, 2, 569, 2, 3, 2, 5, 2, 1249, 2, 3,
    2, 7, 2, 29, 2, 3, 2, 17, 2, 23, 2, 3, 2, 113, 2, 5,
    2, 3, 2, 37, 2, 409, 2, 3, 2, 5, 2, 11, 2, 3, 2, 47,
    2, 97, 2, 3, 2]

/-- Table 9 row: the prime after 4127074165753081 is 4127074165753081 + 886. -/
theorem gap9_886 : IsGapAt 4127074165753081 886 :=
  isGapAt_of 4127074165753081 886 (p4127074165753081) (by show Nat.Prime 4127074165753967; exact p4127074165753967) gds_886 (by decide +kernel)

def gds_898 : List ℕ := [
    2, 3, 2, 24094009, 2, 37, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19,
    2, 59197, 2, 3, 2, 5, 2, 89, 2, 3, 2, 32251, 2, 11, 2, 3,
    2, 31, 2, 7, 2, 3, 2, 21589, 2, 5, 2, 3, 2, 47, 2, 2543,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 491, 2, 8420443, 2, 3, 2, 7,
    2, 103, 2, 3, 2, 3216211, 2, 5, 2, 3, 2, 97, 2, 7, 2, 3,
    2, 5, 2, 991, 2, 3, 2, 13, 2, 17, 2, 3, 2, 385267, 2, 11,
    2, 3, 2, 277, 2, 5, 2, 3, 2, 7, 2, 4597, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 11, 2, 7, 2, 3, 2, 17, 2, 24025609, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 163, 2, 79, 2, 3, 2, 5, 2, 161881,
    2, 3, 2, 7, 2, 211, 2, 3, 2, 37, 2, 12048259, 2, 3, 2, 43,
    2, 5, 2, 3, 2, 13, 2, 19, 2, 3, 2, 5, 2, 487, 2, 3,
    2, 251, 2, 23, 2, 3, 2, 11, 2, 22452011, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 179, 2, 131, 2, 3, 2, 5, 2, 7, 2, 3, 2, 137,
    2, 461, 2, 3, 2, 67, 2, 280921, 2, 3, 2, 31, 2, 5, 2, 3,
    2, 17, 2, 11, 2, 3, 2, 5, 2, 47, 2, 3, 2, 431, 2, 389,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 1069,
    2, 73, 2, 3, 2, 5, 2, 2441, 2, 3, 2, 199697, 2, 13, 2, 3,
    2, 7, 2, 41, 2, 3, 2, 4909, 2, 5, 2, 3, 2, 61, 2, 7,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 151, 2, 1829011, 2, 3, 2, 7741,
    2, 149, 2, 3, 2, 823, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3,
    2, 5, 2, 36857, 2, 3, 2, 17, 2, 7, 2, 3, 2, 389533, 2, 3251,
    2, 3, 2, 53, 2, 5, 2, 3, 2, 5776871, 2, 13, 2, 3, 2, 5,
    2, 449, 2, 3, 2, 7, 2, 11, 2, 3, 2, 23, 2, 14437, 2, 3,
    2, 1163, 2, 5, 2, 3, 2, 37, 2, 29, 2, 3, 2, 5, 2, 1181,
    2, 3, 2, 229, 2, 30055309, 2, 3, 2, 127, 2, 17, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 31, 2, 61, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 43, 2, 911, 2, 3, 2, 71, 2, 11, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 29, 2, 631, 2, 3, 2, 5, 2, 107, 2, 3, 2, 11,
    2, 37, 2, 3, 2, 79, 2, 7, 2, 3, 2, 131, 2, 5, 2, 3,
    2, 1499, 2, 31, 2, 3, 2, 5, 2, 1301711, 2, 3, 2, 13, 2, 13537,
    2, 3, 2, 7, 2, 9332759, 2, 3, 2, 47743, 2, 5, 2, 3, 2, 311,
    2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 1171, 2, 19, 2, 3,
    2, 11, 2, 47, 2, 3, 2, 13553, 2, 5, 2, 3, 2, 7, 2, 877,
    2, 3, 2, 5, 2, 3708611, 2, 3, 2, 109, 2, 7, 2, 3, 2, 4337,
    2, 101, 2, 3, 2, 73, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3,
    2, 5, 2, 120689, 2, 3, 2, 7, 2, 22739147, 2, 3, 2, 443, 2, 56133743,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 19, 2, 59, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 37, 2, 17, 2, 3, 2, 41, 2, 197, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 67, 2, 6257, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 7069, 2, 7971787, 2, 3, 2, 13, 2, 5273, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 11, 2, 127, 2, 3, 2, 5, 2, 31, 2, 3,
    2, 53, 2, 13, 2, 3, 2, 4484423, 2, 7, 2, 3, 2, 6037, 2, 5,
    2, 3, 2, 43, 2, 9887, 2, 3, 2, 5, 2, 103, 2, 3, 2, 1878061,
    2, 11, 2, 3, 2, 7, 2, 73, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 59, 2, 7, 2, 3, 2, 5, 2, 919, 2, 3, 2, 1061, 2, 767093,
    2, 3, 2, 26309, 2, 29, 2, 3, 2, 337, 2, 5, 2, 3, 2, 7,
    2, 13, 2, 3, 2, 5, 2, 983, 2, 3, 2, 101, 2, 7, 2, 3,
    2, 219091, 2, 11, 2, 3, 2, 3613, 2, 5, 2, 3, 2, 241, 2, 41,
    2, 3, 2, 5, 2, 61, 2, 3, 2, 7, 2, 83, 2, 3, 2, 29,
    2, 2259139, 2, 3, 2, 13, 2, 5, 2, 3, 2, 479, 2, 47, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 7878961, 2, 238321, 2, 3, 2, 19, 2, 13,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 2917, 2, 27944401, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 17, 2, 31, 2, 3, 2, 11, 2, 229, 2, 3,
    2, 41, 2, 5, 2, 3, 2, 9283, 2, 1997, 2, 3, 2, 5, 2, 359,
    2, 3, 2, 13, 2, 23, 2, 3, 2, 199, 2, 7, 2, 3, 2, 563,
    2, 5, 2, 3, 2, 53759, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3,
    2]

/-- Table 9 row: the prime after 4198168149492463 is 4198168149492463 + 898. -/
theorem gap9_898 : IsGapAt 4198168149492463 898 :=
  isGapAt_of 4198168149492463 898 (p4198168149492463) (by show Nat.Prime 4198168149493361; exact p4198168149493361) gds_898 (by decide +kernel)

def gds_922 : List ℕ := [
    2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 73, 2, 3, 2, 37,
    2, 59, 2, 3, 2, 42577, 2, 5, 2, 3, 2, 71, 2, 197, 2, 3,
    2, 5, 2, 66863, 2, 3, 2, 311, 2, 2833069, 2, 3, 2, 937, 2, 7,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 303053, 2, 13, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 19, 2, 467, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 607, 2, 5, 2, 3, 2, 109, 2, 7, 2, 3, 2, 5, 2, 1009,
    2, 3, 2, 1169587, 2, 23, 2, 3, 2, 43, 2, 19, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 2617, 2, 3,
    2, 53, 2, 7, 2, 3, 2, 41, 2, 13, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 23, 2, 29, 2, 3, 2, 5, 2, 20479, 2, 3, 2, 7,
    2, 167, 2, 3, 2, 2887, 2, 45659, 2, 3, 2, 61, 2, 5, 2, 3,
    2, 83, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 43,
    2, 3, 2, 26099167, 2, 240641, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11,
    2, 461, 2, 3, 2, 5, 2, 7, 2, 3, 2, 251, 2, 19, 2, 3,
    2, 293, 2, 809, 2, 3, 2, 2434837, 2, 5, 2, 3, 2, 31, 2, 23,
    2, 3, 2, 5, 2, 173, 2, 3, 2, 337, 2, 11, 2, 3, 2, 1483,
    2, 7, 2, 3, 2, 10903, 2, 5, 2, 3, 2, 13, 2, 79, 2, 3,
    2, 5, 2, 137, 2, 3, 2, 1831787, 2, 17, 2, 3, 2, 7, 2, 383,
    2, 3, 2, 673, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5,
    2, 109, 2, 3, 2, 751, 2, 37, 2, 3, 2, 17, 2, 11, 2, 3,
    2, 36847, 2, 5, 2, 3, 2, 7, 2, 131, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 13, 2, 47, 2, 3, 2, 631,
    2, 5, 2, 3, 2, 13049, 2, 179, 2, 3, 2, 5, 2, 1888031, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 82759, 2, 23, 2, 3, 2, 29, 2, 5,
    2, 3, 2, 430999, 2, 210719, 2, 3, 2, 5, 2, 101, 2, 3, 2, 577,
    2, 6012583, 2, 3, 2, 11, 2, 229, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 17, 2, 103, 2, 3, 2, 5, 2, 7, 2, 3, 2, 1297, 2, 31249,
    2, 3, 2, 97, 2, 8623031, 2, 3, 2, 47, 2, 5, 2, 3, 2, 53,
    2, 11, 2, 3, 2, 5, 2, 4597, 2, 3, 2, 37, 2, 2797, 2, 3,
    2, 2287, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 1451, 2, 853,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 59, 2, 2311, 2, 3, 2, 7,
    2, 29, 2, 3, 2, 13, 2, 5, 2, 3, 2, 1051, 2, 7, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 17, 2, 503, 2, 3, 2, 19, 2, 13,
    2, 3, 2, 22129, 2, 5, 2, 3, 2, 7, 2, 17519, 2, 3, 2, 5,
    2, 41, 2, 3, 2, 137, 2, 7, 2, 3, 2, 29, 2, 149, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 46245631, 2, 8204929, 2, 3, 2, 5, 2, 5351,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 79, 2, 17, 2, 3, 2, 131,
    2, 5, 2, 3, 2, 101, 2, 113, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 31, 2, 613, 2, 3, 2, 419, 2, 361211, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 41, 2, 47, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19,
    2, 241, 2, 3, 2, 181, 2, 11, 2, 3, 2, 26099, 2, 5, 2, 3,
    2, 13, 2, 53, 2, 3, 2, 5, 2, 271, 2, 3, 2, 11, 2, 29,
    2, 3, 2, 83, 2, 7, 2, 3, 2, 37, 2, 5, 2, 3, 2, 46078691,
    2, 17, 2, 3, 2, 5, 2, 373, 2, 3, 2, 23, 2, 17992193, 2, 3,
    2, 7, 2, 43, 2, 3, 2, 683, 2, 5, 2, 3, 2, 179, 2, 7,
    2, 3, 2, 5, 2, 59, 2, 3, 2, 29, 2, 10111, 2, 3, 2, 11,
    2, 71, 2, 3, 2, 73, 2, 5, 2, 3, 2, 7, 2, 5939, 2, 3,
    2, 5, 2, 37, 2, 3, 2, 1489, 2, 7, 2, 3, 2, 53, 2, 20983609,
    2, 3, 2, 89, 2, 5, 2, 3, 2, 5693, 2, 11, 2, 3, 2, 5,
    2, 6569, 2, 3, 2, 7, 2, 17, 2, 3, 2, 31, 2, 3876947, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 557, 2, 22247, 2, 3, 2, 5, 2, 24469,
    2, 3, 2, 1354057, 2, 9151, 2, 3, 2, 17, 2, 56453, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 23, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 2801, 2, 15121, 2, 3, 2, 149, 2, 31, 2, 3, 2, 257, 2, 5,
    2, 3, 2, 11, 2, 2417, 2, 3, 2, 5, 2, 1422721, 2, 3, 2, 43,
    2, 263, 2, 3, 2, 110269, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 91957, 2, 219977, 2, 3, 2, 5, 2, 19, 2, 3, 2, 371333, 2, 11,
    2, 3, 2, 7, 2, 13, 2, 3, 2]

/-- Table 9 row: the prime after 4286129201882221 is 4286129201882221 + 922. -/
theorem gap9_922 : IsGapAt 4286129201882221 922 :=
  isGapAt_of 4286129201882221 922 (p4286129201882221) (by show Nat.Prime 4286129201883143; exact p4286129201883143) gds_922 (by decide +kernel)

def gds_926 : List ℕ := [
    2, 15107471, 2, 3, 2, 17, 2, 5, 2, 3, 2, 49019, 2, 170761, 2, 3,
    2, 5, 2, 443, 2, 3, 2, 31, 2, 3517, 2, 3, 2, 13, 2, 7,
    2, 3, 2, 257, 2, 5, 2, 3, 2, 197, 2, 59, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 151, 2, 13, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 37, 2, 5, 2, 3, 2, 311, 2, 7, 2, 3, 2, 5, 2, 44867,
    2, 3, 2, 11, 2, 31, 2, 3, 2, 67, 2, 8689, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 7, 2, 71, 2, 3, 2, 5, 2, 113, 2, 3,
    2, 229, 2, 7, 2, 3, 2, 2009509, 2, 2004763, 2, 3, 2, 241, 2, 5,
    2, 3, 2, 439, 2, 13, 2, 3, 2, 5, 2, 37, 2, 3, 2, 7,
    2, 19, 2, 3, 2, 11, 2, 1511911, 2, 3, 2, 26823893, 2, 5, 2, 3,
    2, 59, 2, 2551, 2, 3, 2, 5, 2, 56843, 2, 3, 2, 10170179, 2, 17,
    2, 3, 2, 103, 2, 83, 2, 3, 2, 7, 2, 5, 2, 3, 2, 29,
    2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 131, 2, 65927, 2, 3,
    2, 17, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 19, 2, 67,
    2, 3, 2, 5, 2, 7859419, 2, 3, 2, 23, 2, 358903, 2, 3, 2, 43,
    2, 7, 2, 3, 2, 71, 2, 5, 2, 3, 2, 109, 2, 799031, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 13, 2, 121727, 2, 3, 2, 7, 2, 31,
    2, 3, 2, 397, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 2129, 2, 101, 2, 3, 2, 23029, 2, 1213, 2, 3,
    2, 6917, 2, 5, 2, 3, 2, 7, 2, 4637, 2, 3, 2, 5, 2, 133321,
    2, 3, 2, 73, 2, 7, 2, 3, 2, 727, 2, 16451, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 13, 2, 347, 2, 3, 2, 5, 2, 2529881, 2, 3,
    2, 7, 2, 151, 2, 3, 2, 127, 2, 37, 2, 3, 2, 29, 2, 5,
    2, 3, 2, 23, 2, 19, 2, 3, 2, 5, 2, 17, 2, 3, 2, 1019,
    2, 79, 2, 3, 2, 41, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 509, 2, 7052723, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 26713,
    2, 3, 2, 13, 2, 359, 2, 3, 2, 157, 2, 5, 2, 3, 2, 153509,
    2, 53, 2, 3, 2, 5, 2, 4493, 2, 3, 2, 5657, 2, 13, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 1491439, 2, 5, 2, 3, 2, 743, 2, 23,
    2, 3, 2, 5, 2, 73, 2, 3, 2, 92269, 2, 56359, 2, 3, 2, 7,
    2, 17, 2, 3, 2, 1285607, 2, 5, 2, 3, 2, 67, 2, 7, 2, 3,
    2, 5, 2, 47, 2, 3, 2, 881, 2, 149, 2, 3, 2, 23, 2, 1187,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5,
    2, 71, 2, 3, 2, 29063, 2, 7, 2, 3, 2, 29, 2, 10003541, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 461, 2, 41, 2, 3, 2, 5, 2, 1373,
    2, 3, 2, 7, 2, 163, 2, 3, 2, 1237, 2, 229, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 31, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 47, 2, 10337417, 2, 3, 2, 857, 2, 13, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 11, 2, 127, 2, 3, 2, 5, 2, 7, 2, 3, 2, 4079,
    2, 67, 2, 3, 2, 2393, 2, 1051, 2, 3, 2, 41, 2, 5, 2, 3,
    2, 1319, 2, 31, 2, 3, 2, 5, 2, 281, 2, 3, 2, 13, 2, 11,
    2, 3, 2, 284737, 2, 7, 2, 3, 2, 38595199, 2, 5, 2, 3, 2, 71,
    2, 797, 2, 3, 2, 5, 2, 13, 2, 3, 2, 447749, 2, 17, 2, 3,
    2, 7, 2, 40013, 2, 3, 2, 349, 2, 5, 2, 3, 2, 79, 2, 7,
    2, 3, 2, 5, 2, 97, 2, 3, 2, 29, 2, 19, 2, 3, 2, 17,
    2, 11, 2, 3, 2, 9576397, 2, 5, 2, 3, 2, 7, 2, 11733569, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 11, 2, 7, 2, 3, 2, 107, 2, 53,
    2, 3, 2, 43, 2, 5, 2, 3, 2, 73, 2, 2011, 2, 3, 2, 5,
    2, 2081, 2, 3, 2, 7, 2, 201827, 2, 3, 2, 46451, 2, 47, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 19, 2, 4673, 2, 3, 2, 5, 2, 41,
    2, 3, 2, 149, 2, 37, 2, 3, 2, 11, 2, 631, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 17, 2, 89, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 223, 2, 13, 2, 3, 2, 927161, 2, 43, 2, 3, 2, 83, 2, 5,
    2, 3, 2, 54401, 2, 11, 2, 3, 2, 5, 2, 79, 2, 3, 2, 353,
    2, 1447, 2, 3, 2, 59, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 41, 2, 36451, 2, 3, 2, 5, 2, 17, 2, 3, 2, 67, 2, 3049,
    2, 3, 2, 7, 2, 101, 2, 3, 2, 19, 2, 5, 2, 3, 2, 13109,
    2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2]

/-- Table 9 row: the prime after 6381944136489827 is 6381944136489827 + 926. -/
theorem gap9_926 : IsGapAt 6381944136489827 926 :=
  isGapAt_of 6381944136489827 926 (p6381944136489827) (by show Nat.Prime 6381944136490753; exact p6381944136490753) gds_926 (by decide +kernel)

def gds_928 : List ℕ := [
    2, 3, 2, 13, 2, 197, 2, 3, 2, 11, 2, 5, 2, 3, 2, 233,
    2, 43, 2, 3, 2, 5, 2, 17, 2, 3, 2, 1429, 2, 13, 2, 3,
    2, 14887, 2, 4286393, 2, 3, 2, 7, 2, 5, 2, 3, 2, 193, 2, 31721,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 29, 2, 3, 2, 1669,
    2, 1907, 2, 3, 2, 47, 2, 5, 2, 3, 2, 11, 2, 61609, 2, 3,
    2, 5, 2, 31, 2, 3, 2, 211, 2, 53, 2, 3, 2, 137, 2, 7,
    2, 3, 2, 3739, 2, 5, 2, 3, 2, 4637, 2, 13, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 29, 2, 11, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 89, 2, 5, 2, 3, 2, 1331821, 2, 7, 2, 3, 2, 5, 2, 41,
    2, 3, 2, 25771, 2, 333791, 2, 3, 2, 347, 2, 149, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 7, 2, 806203, 2, 3, 2, 5, 2, 113, 2, 3,
    2, 8374739, 2, 7, 2, 3, 2, 967, 2, 11, 2, 3, 2, 43, 2, 5,
    2, 3, 2, 53, 2, 311, 2, 3, 2, 5, 2, 173, 2, 3, 2, 7,
    2, 19, 2, 3, 2, 2939, 2, 2207143, 2, 3, 2, 584621, 2, 5, 2, 3,
    2, 41, 2, 17, 2, 3, 2, 5, 2, 29, 2, 3, 2, 13, 2, 71,
    2, 3, 2, 658309, 2, 26189, 2, 3, 2, 7, 2, 5, 2, 3, 2, 107251,
    2, 47, 2, 3, 2, 5, 2, 7, 2, 3, 2, 1607, 2, 31, 2, 3,
    2, 11, 2, 43, 2, 3, 2, 454379, 2, 5, 2, 3, 2, 19, 2, 103811,
    2, 3, 2, 5, 2, 1753, 2, 3, 2, 23, 2, 4561, 2, 3, 2, 2741,
    2, 7, 2, 3, 2, 83, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 624487, 2, 17, 2, 3, 2, 7, 2, 139,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 100051723, 2, 7, 2, 3, 2, 5,
    2, 3440527, 2, 3, 2, 1877, 2, 107, 2, 3, 2, 17, 2, 67, 2, 3,
    2, 15581, 2, 5, 2, 3, 2, 7, 2, 1484663, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 4987, 2, 7, 2, 3, 2, 13, 2, 59, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 11, 2, 29, 2, 3, 2, 5, 2, 45137, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 24091, 2, 45673, 2, 3, 2, 269, 2, 5,
    2, 3, 2, 23, 2, 19, 2, 3, 2, 5, 2, 79, 2, 3, 2, 43,
    2, 11, 2, 3, 2, 149, 2, 31, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 17, 2, 601, 2, 3, 2, 5, 2, 7, 2, 3, 2, 1019, 2, 97,
    2, 3, 2, 101, 2, 89, 2, 3, 2, 271, 2, 5, 2, 3, 2, 397,
    2, 13, 2, 3, 2, 5, 2, 7319867, 2, 3, 2, 1181, 2, 211, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 10613, 2, 5, 2, 3, 2, 127, 2, 23,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 11, 2, 47, 2, 3, 2, 7,
    2, 89393, 2, 3, 2, 13, 2, 5, 2, 3, 2, 653, 2, 7, 2, 3,
    2, 5, 2, 42124829, 2, 3, 2, 17, 2, 277, 2, 3, 2, 23, 2, 13,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 84089, 2, 3, 2, 5,
    2, 811, 2, 3, 2, 1097, 2, 7, 2, 3, 2, 11, 2, 12149, 2, 3,
    2, 179, 2, 5, 2, 3, 2, 109, 2, 784837, 2, 3, 2, 5, 2, 661,
    2, 3, 2, 7, 2, 3943, 2, 3, 2, 47, 2, 17, 2, 3, 2, 29,
    2, 5, 2, 3, 2, 2237, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 599, 2, 9511, 2, 3, 2, 89, 2, 19, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 103, 2, 37, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11577431,
    2, 307, 2, 3, 2, 251, 2, 140407, 2, 3, 2, 1021, 2, 5, 2, 3,
    2, 13, 2, 569, 2, 3, 2, 5, 2, 11, 2, 3, 2, 41, 2, 2551,
    2, 3, 2, 73, 2, 7, 2, 3, 2, 1423, 2, 5, 2, 3, 2, 11,
    2, 17, 2, 3, 2, 5, 2, 271231, 2, 3, 2, 823, 2, 59, 2, 3,
    2, 7, 2, 29, 2, 3, 2, 79, 2, 5, 2, 3, 2, 31, 2, 7,
    2, 3, 2, 5, 2, 641, 2, 3, 2, 115303, 2, 11, 2, 3, 2, 13,
    2, 7643, 2, 3, 2, 239, 2, 5, 2, 3, 2, 7, 2, 12227, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 71, 2, 7, 2, 3, 2, 29, 2, 56431,
    2, 3, 2, 311, 2, 5, 2, 3, 2, 37, 2, 31, 2, 3, 2, 5,
    2, 109, 2, 3, 2, 7, 2, 17, 2, 3, 2, 338231, 2, 11, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 19, 2, 1433, 2, 3, 2, 5, 2, 877,
    2, 3, 2, 11, 2, 73, 2, 3, 2, 17, 2, 1297, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 4287991, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 541, 2, 37, 2, 3, 2, 359, 2, 412493, 2, 3, 2, 1621, 2, 5,
    2, 3, 2, 47, 2, 79, 2, 3, 2, 5, 2, 10433, 2, 3, 2]

/-- Table 9 row: the prime after 10244316228469423 is 10244316228469423 + 928. -/
theorem gap9_928 : IsGapAt 10244316228469423 928 :=
  isGapAt_of 10244316228469423 928 (p10244316228469423) (by show Nat.Prime 10244316228470351; exact p10244316228470351) gds_928 (by decide +kernel)

def gds_932 : List ℕ := [
    2, 17, 2, 3, 2, 5, 2, 98221, 2, 3, 2, 29, 2, 61, 2, 3,
    2, 53, 2, 7, 2, 3, 2, 6961, 2, 5, 2, 3, 2, 307, 2, 19,
    2, 3, 2, 5, 2, 41, 2, 3, 2, 11, 2, 6079, 2, 3, 2, 7,
    2, 85859729, 2, 3, 2, 97, 2, 5, 2, 3, 2, 227, 2, 7, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 47, 2, 1601, 2, 3, 2, 6917, 2, 1036631,
    2, 3, 2, 79, 2, 5, 2, 3, 2, 7, 2, 136111, 2, 3, 2, 5,
    2, 211, 2, 3, 2, 757, 2, 7, 2, 3, 2, 11, 2, 77479, 2, 3,
    2, 109, 2, 5, 2, 3, 2, 13, 2, 5552947, 2, 3, 2, 5, 2, 29,
    2, 3, 2, 7, 2, 17827, 2, 3, 2, 17, 2, 14207, 2, 3, 2, 31,
    2, 5, 2, 3, 2, 37, 2, 11, 2, 3, 2, 5, 2, 2129, 2, 3,
    2, 103, 2, 271, 2, 3, 2, 14431, 2, 349, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 2646533, 2, 2073353, 2, 3, 2, 5, 2, 7, 2, 3, 2, 389,
    2, 89, 2, 3, 2, 13, 2, 23, 2, 3, 2, 919, 2, 5, 2, 3,
    2, 125311, 2, 239, 2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2, 13,
    2, 3, 2, 631, 2, 7, 2, 3, 2, 101, 2, 5, 2, 3, 2, 11,
    2, 79, 2, 3, 2, 5, 2, 97, 2, 3, 2, 1949, 2, 7219, 2, 3,
    2, 7, 2, 19, 2, 3, 2, 59, 2, 5, 2, 3, 2, 39163, 2, 7,
    2, 3, 2, 5, 2, 35149, 2, 3, 2, 1151, 2, 11, 2, 3, 2, 71,
    2, 268531, 2, 3, 2, 117659, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 61487, 2, 7, 2, 3, 2, 173, 2, 7433,
    2, 3, 2, 199, 2, 5, 2, 3, 2, 31, 2, 67, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 7, 2, 59915111, 2, 3, 2, 28591, 2, 11, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 29, 2, 1087, 2, 3, 2, 5, 2, 103,
    2, 3, 2, 11, 2, 19, 2, 3, 2, 16349, 2, 13, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 43, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 260573, 2, 73, 2, 3, 2, 1579, 2, 17, 2, 3, 2, 563, 2, 5,
    2, 3, 2, 1303, 2, 113, 2, 3, 2, 5, 2, 929, 2, 3, 2, 13,
    2, 151, 2, 3, 2, 11, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 19, 2, 5657, 2, 3, 2, 5, 2, 13, 2, 3, 2, 167, 2, 120709,
    2, 3, 2, 7, 2, 1439, 2, 3, 2, 29333, 2, 5, 2, 3, 2, 811,
    2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 11969, 2, 353, 2, 3,
    2, 51263, 2, 59, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 17,
    2, 3, 2, 5, 2, 338323, 2, 3, 2, 23, 2, 7, 2, 3, 2, 7213,
    2, 41, 2, 3, 2, 29, 2, 5, 2, 3, 2, 229, 2, 47, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 7, 2, 2087, 2, 3, 2, 79, 2, 798059,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 11, 2, 71, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 42373, 2, 28837, 2, 3, 2, 13, 2, 117563, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 67, 2, 19, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 41, 2, 11, 2, 3, 2, 59, 2, 1567, 2, 3, 2, 61,
    2, 5, 2, 3, 2, 11939, 2, 1213, 2, 3, 2, 5, 2, 101, 2, 3,
    2, 491, 2, 307, 2, 3, 2, 17, 2, 7, 2, 3, 2, 53, 2, 5,
    2, 3, 2, 23, 2, 2430851, 2, 3, 2, 5, 2, 37, 2, 3, 2, 6977,
    2, 263, 2, 3, 2, 7, 2, 11, 2, 3, 2, 313, 2, 5, 2, 3,
    2, 239, 2, 7, 2, 3, 2, 5, 2, 13239727, 2, 3, 2, 11, 2, 991,
    2, 3, 2, 29, 2, 6661, 2, 3, 2, 71, 2, 5, 2, 3, 2, 7,
    2, 199, 2, 3, 2, 5, 2, 89, 2, 3, 2, 1115363, 2, 7, 2, 3,
    2, 3517, 2, 359, 2, 3, 2, 13, 2, 5, 2, 3, 2, 17, 2, 23,
    2, 3, 2, 5, 2, 9431, 2, 3, 2, 7, 2, 31, 2, 3, 2, 11,
    2, 13, 2, 3, 2, 8693, 2, 5, 2, 3, 2, 103, 2, 2437, 2, 3,
    2, 5, 2, 317, 2, 3, 2, 19, 2, 257, 2, 3, 2, 23, 2, 3691,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 1709077, 2, 11, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 13, 2, 29, 2, 3, 2, 1637, 2, 19, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 101, 2, 73, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 17, 2, 59, 2, 3, 2, 41, 2, 7, 2, 3, 2, 2137829,
    2, 5, 2, 3, 2, 1727491, 2, 2389, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 29, 2, 3181, 2, 3, 2, 7, 2, 23, 2, 3, 2, 251, 2, 5,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 346373, 2, 3, 2, 331,
    2, 30373697, 2, 3, 2, 47, 2, 17, 2, 3, 2, 181, 2, 5, 2, 3,
    2, 7, 2]

/-- Table 9 row: the prime after 10676480515967939 is 10676480515967939 + 932. -/
theorem gap9_932 : IsGapAt 10676480515967939 932 :=
  isGapAt_of 10676480515967939 932 (p10676480515967939) (by show Nat.Prime 10676480515968871; exact p10676480515968871) gds_932 (by decide +kernel)

def gds_968 : List ℕ := [
    2, 13, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 29, 2, 3,
    2, 11, 2, 3169, 2, 3, 2, 383, 2, 5, 2, 3, 2, 41, 2, 414097,
    2, 3, 2, 5, 2, 115438579, 2, 3, 2, 149, 2, 179, 2, 3, 2, 103495361,
    2, 107, 2, 3, 2, 7, 2, 5, 2, 3, 2, 283, 2, 11, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 29, 2, 9337, 2, 3, 2, 169789, 2, 13,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 109, 2, 137, 2, 3, 2, 5,
    2, 668737, 2, 3, 2, 73, 2, 2777, 2, 3, 2, 14699, 2, 7, 2, 3,
    2, 2029, 2, 5, 2, 3, 2, 5851, 2, 19, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 13, 2, 213821, 2, 3, 2, 7, 2, 9767, 2, 3, 2, 37,
    2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 13249, 2, 17, 2, 3, 2, 17419133, 2, 14478677, 2, 3, 2, 59, 2, 5,
    2, 3, 2, 7, 2, 5410667, 2, 3, 2, 5, 2, 29, 2, 3, 2, 241,
    2, 7, 2, 3, 2, 17, 2, 211, 2, 3, 2, 197, 2, 5, 2, 3,
    2, 13, 2, 4373, 2, 3, 2, 5, 2, 37, 2, 3, 2, 7, 2, 23,
    2, 3, 2, 547, 2, 113, 2, 3, 2, 67, 2, 5, 2, 3, 2, 8360809,
    2, 30871, 2, 3, 2, 5, 2, 73, 2, 3, 2, 127, 2, 331, 2, 3,
    2, 151, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 131,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 281, 2, 3, 2, 13,
    2, 627479, 2, 3, 2, 68567, 2, 5, 2, 3, 2, 17, 2, 1423, 2, 3,
    2, 5, 2, 109, 2, 3, 2, 19, 2, 13, 2, 3, 2, 1553, 2, 7,
    2, 3, 2, 691, 2, 5, 2, 3, 2, 499, 2, 677, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 191, 2, 31, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 317, 2, 5, 2, 3, 2, 10859, 2, 7, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 859, 2, 1879, 2, 3, 2, 1753, 2, 227, 2, 3, 2, 3391,
    2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 53, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 23, 2, 59, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 29, 2, 89, 2, 3, 2, 5, 2, 313, 2, 3, 2, 7,
    2, 3490363, 2, 3, 2, 357431, 2, 37, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 97, 2, 297793, 2, 3, 2, 5, 2, 11, 2, 3, 2, 12429457, 2, 19,
    2, 3, 2, 31, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11,
    2, 7717, 2, 3, 2, 5, 2, 7, 2, 3, 2, 168293, 2, 43, 2, 3,
    2, 54131563, 2, 23, 2, 3, 2, 17, 2, 5, 2, 3, 2, 151883, 2, 2197603,
    2, 3, 2, 5, 2, 251, 2, 3, 2, 13, 2, 11, 2, 3, 2, 59,
    2, 7, 2, 3, 2, 131, 2, 5, 2, 3, 2, 19, 2, 139, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 653, 2, 1297, 2, 3, 2, 7, 2, 151,
    2, 3, 2, 163, 2, 5, 2, 3, 2, 101, 2, 7, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 61, 2, 8147, 2, 3, 2, 37, 2, 11, 2, 3,
    2, 29, 2, 5, 2, 3, 2, 7, 2, 157, 2, 3, 2, 5, 2, 1601,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 1069, 2, 47, 2, 3, 2, 997,
    2, 5, 2, 3, 2, 3943, 2, 263, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 7, 2, 97, 2, 3, 2, 1373, 2, 325309, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 5279, 2, 37, 2, 3, 2, 5, 2, 10987, 2, 3, 2, 683821,
    2, 17, 2, 3, 2, 11, 2, 103, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 673, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 271027, 2, 13,
    2, 3, 2, 17, 2, 29, 2, 3, 2, 47, 2, 5, 2, 3, 2, 587,
    2, 11, 2, 3, 2, 5, 2, 193, 2, 3, 2, 17239, 2, 1571, 2, 3,
    2, 4789, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 18731, 2, 43,
    2, 3, 2, 5, 2, 1231, 2, 3, 2, 39804151, 2, 59, 2, 3, 2, 7,
    2, 67, 2, 3, 2, 223, 2, 5, 2, 3, 2, 26321, 2, 7, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 3929, 2, 30348541, 2, 3, 2, 2643079, 2, 1301,
    2, 3, 2, 92227, 2, 5, 2, 3, 2, 7, 2, 134661229, 2, 3, 2, 5,
    2, 83, 2, 3, 2, 23, 2, 7, 2, 3, 2, 14293, 2, 1106779, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 31, 2, 71, 2, 3, 2, 5, 2, 97879,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 743, 2, 13, 2, 3, 2, 1925393,
    2, 5, 2, 3, 2, 1783, 2, 73351, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 19, 2, 29, 2, 3, 2, 983, 2, 163, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 2851, 2, 31, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13,
    2, 23, 2, 3, 2, 603191, 2, 11, 2, 3, 2, 43, 2, 5, 2, 3,
    2, 2647, 2, 41, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 248707,
    2, 3, 2, 61, 2, 7, 2, 3, 2, 50775289, 2, 5, 2, 3, 2, 23,
    2, 109, 2, 3, 2, 5, 2]

/-- Table 9 row: the prime after 19124990244992669 is 19124990244992669 + 968. -/
theorem gap9_968 : IsGapAt 19124990244992669 968 :=
  isGapAt_of 19124990244992669 968 (p19124990244992669) (by show Nat.Prime 19124990244993637; exact p19124990244993637) gds_968 (by decide +kernel)

def gds_980 : List ℕ := [
    2, 41, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 849253, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 47, 2, 5, 2, 3, 2, 17, 2, 397073,
    2, 3, 2, 5, 2, 26951, 2, 3, 2, 1033, 2, 7433, 2, 3, 2, 7,
    2, 19, 2, 3, 2, 23, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 5, 2, 43, 2, 3, 2, 1213, 2, 73, 2, 3, 2, 29, 2, 199,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 169691, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 113, 2, 7, 2, 3, 2, 853, 2, 37, 2, 3,
    2, 349, 2, 5, 2, 3, 2, 59, 2, 719, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 967, 2, 3, 2, 13, 2, 24373, 2, 3, 2, 769,
    2, 5, 2, 3, 2, 11, 2, 151, 2, 3, 2, 5, 2, 31, 2, 3,
    2, 227, 2, 13, 2, 3, 2, 337, 2, 751, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 225347, 2, 2153, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23,
    2, 11, 2, 3, 2, 601, 2, 17, 2, 3, 2, 277, 2, 5, 2, 3,
    2, 25609, 2, 47, 2, 3, 2, 5, 2, 212909, 2, 3, 2, 107, 2, 71,
    2, 3, 2, 6337, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 19,
    2, 13, 2, 3, 2, 5, 2, 41, 2, 3, 2, 29, 2, 109, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 97, 2, 5, 2, 3, 2, 1831, 2, 7,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 23, 2, 3, 2, 1777,
    2, 1556369, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 5, 2, 79, 2, 3, 2, 1069583, 2, 7, 2, 3, 2, 283, 2, 13,
    2, 3, 2, 68983891, 2, 5, 2, 3, 2, 23, 2, 37, 2, 3, 2, 5,
    2, 29256103, 2, 3, 2, 7, 2, 31, 2, 3, 2, 11, 2, 797, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 61, 2, 263, 2, 3, 2, 5, 2, 29,
    2, 3, 2, 13, 2, 88747, 2, 3, 2, 53, 2, 131449, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 709, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 139, 2, 17, 2, 3, 2, 7159, 2, 67, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 257, 2, 23, 2, 3, 2, 5, 2, 1249, 2, 3, 2, 163,
    2, 4297, 2, 3, 2, 17, 2, 7, 2, 3, 2, 523, 2, 5, 2, 3,
    2, 13, 2, 72758219, 2, 3, 2, 5, 2, 11, 2, 3, 2, 89, 2, 1693,
    2, 3, 2, 7, 2, 2293, 2, 3, 2, 59, 2, 5, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 5, 2, 137, 2, 3, 2, 353, 2, 41, 2, 3,
    2, 43, 2, 288733, 2, 3, 2, 1801, 2, 5, 2, 3, 2, 7, 2, 73,
    2, 3, 2, 5, 2, 3343, 2, 3, 2, 17387, 2, 7, 2, 3, 2, 13,
    2, 31, 2, 3, 2, 271729, 2, 5, 2, 3, 2, 17, 2, 29, 2, 3,
    2, 5, 2, 131, 2, 3, 2, 7, 2, 13, 2, 3, 2, 1723, 2, 23,
    2, 3, 2, 83, 2, 5, 2, 3, 2, 9013, 2, 487, 2, 3, 2, 5,
    2, 331547, 2, 3, 2, 19, 2, 43, 2, 3, 2, 47, 2, 11, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 29, 2, 173249, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 11, 2, 317, 2, 3, 2, 313, 2, 19, 2, 3, 2, 79,
    2, 5, 2, 3, 2, 157, 2, 13, 2, 3, 2, 5, 2, 7016921, 2, 3,
    2, 17, 2, 211, 2, 3, 2, 121394921, 2, 7, 2, 3, 2, 31, 2, 5,
    2, 3, 2, 331, 2, 23609, 2, 3, 2, 5, 2, 971, 2, 3, 2, 23813,
    2, 3389, 2, 3, 2, 7, 2, 139, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 109, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 37, 2, 10513,
    2, 3, 2, 25453, 2, 13, 2, 3, 2, 12541, 2, 5, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 5, 2, 2729, 2, 3, 2, 127, 2, 7, 2, 3,
    2, 69512939, 2, 41, 2, 3, 2, 11, 2, 5, 2, 3, 2, 11834477, 2, 105365191,
    2, 3, 2, 5, 2, 163, 2, 3, 2, 7, 2, 98729, 2, 3, 2, 1021,
    2, 347, 2, 3, 2, 29, 2, 5, 2, 3, 2, 113, 2, 79, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 71, 2, 2687, 2, 3, 2, 62753, 2, 5651,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 41, 2, 2833763, 2, 3, 2, 59, 2, 1783, 2, 3,
    2, 1481, 2, 5, 2, 3, 2, 13, 2, 43, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 346649, 2, 11, 2, 3, 2, 149, 2, 7, 2, 3, 2, 107,
    2, 5, 2, 3, 2, 47, 2, 181, 2, 3, 2, 5, 2, 281, 2, 3,
    2, 23, 2, 283, 2, 3, 2, 7, 2, 29, 2, 3, 2, 139210681, 2, 5,
    2, 3, 2, 1229, 2, 7, 2, 3, 2, 5, 2, 53, 2, 3, 2, 1087,
    2, 17, 2, 3, 2, 13, 2, 11, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 7, 2, 35315461, 2, 3, 2, 5, 2, 677, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 17, 2, 73, 2, 3, 2, 16161953, 2, 5, 2, 3, 2, 193,
    2, 19, 2, 3, 2, 5, 2, 1049, 2, 3, 2, 7, 2, 23, 2, 3,
    2, 463, 2]

/-- Table 9 row: the prime after 19403684901755939 is 19403684901755939 + 980. -/
theorem gap9_980 : IsGapAt 19403684901755939 980 :=
  isGapAt_of 19403684901755939 980 (p19403684901755939) (by show Nat.Prime 19403684901756919; exact p19403684901756919) gds_980 (by decide +kernel)

def gds_986 : List ℕ := [
    2, 5, 2, 3, 2, 743, 2, 211, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 31, 2, 167, 2, 3, 2, 7, 2, 857, 2, 3, 2, 3283129, 2, 5,
    2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 251, 2, 3, 2, 1855649,
    2, 4153, 2, 3, 2, 59, 2, 17, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 7, 2, 73, 2, 3, 2, 5, 2, 6559801, 2, 3, 2, 43, 2, 7,
    2, 3, 2, 881, 2, 107, 2, 3, 2, 17, 2, 5, 2, 3, 2, 127,
    2, 131, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 15111749, 2, 5347, 2, 3, 2, 1451, 2, 5, 2, 3, 2, 11, 2, 23,
    2, 3, 2, 5, 2, 6883, 2, 3, 2, 103, 2, 29, 2, 3, 2, 13,
    2, 69401, 2, 3, 2, 7, 2, 5, 2, 3, 2, 2467, 2, 17, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 3677, 2, 11, 2, 3, 2, 23, 2, 37,
    2, 3, 2, 277, 2, 5, 2, 3, 2, 19, 2, 89, 2, 3, 2, 5,
    2, 20973311, 2, 3, 2, 29, 2, 2400001, 2, 3, 2, 31, 2, 7, 2, 3,
    2, 181, 2, 5, 2, 3, 2, 1467007, 2, 88926017, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 193, 2, 53, 2, 3, 2, 7, 2, 11, 2, 3, 2, 62347,
    2, 5, 2, 3, 2, 47, 2, 7, 2, 3, 2, 5, 2, 1175219, 2, 3,
    2, 11, 2, 17, 2, 3, 2, 151, 2, 23, 2, 3, 2, 15110993, 2, 5,
    2, 3, 2, 7, 2, 1367, 2, 3, 2, 5, 2, 67, 2, 3, 2, 449,
    2, 7, 2, 3, 2, 17, 2, 467729, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 26513, 2, 359101, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 89113,
    2, 3, 2, 11, 2, 13, 2, 3, 2, 79, 2, 5, 2, 3, 2, 43,
    2, 19, 2, 3, 2, 5, 2, 103, 2, 3, 2, 347, 2, 127, 2, 3,
    2, 167, 2, 83, 2, 3, 2, 7, 2, 5, 2, 3, 2, 89, 2, 11,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 79889, 2, 3, 2, 1373,
    2, 191, 2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 37, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 59, 2, 263, 2, 3, 2, 19, 2, 7,
    2, 3, 2, 41, 2, 5, 2, 3, 2, 1543, 2, 17569, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 450799, 2, 2909, 2, 3, 2, 7, 2, 42367687, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 79867, 2, 4861, 2, 3, 2, 811, 2, 99139, 2, 3, 2, 381943,
    2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 2843, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 126271, 2, 73, 2, 3, 2, 239, 2, 5,
    2, 3, 2, 72307, 2, 137, 2, 3, 2, 5, 2, 4093, 2, 3, 2, 7,
    2, 61, 2, 3, 2, 13, 2, 727, 2, 3, 2, 145193, 2, 5, 2, 3,
    2, 29, 2, 53, 2, 3, 2, 5, 2, 3030031, 2, 3, 2, 1051, 2, 13,
    2, 3, 2, 1103, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 31,
    2, 157, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 173, 2, 3,
    2, 43, 2, 63143863, 2, 3, 2, 17, 2, 5, 2, 3, 2, 51754561, 2, 349,
    2, 3, 2, 5, 2, 193, 2, 3, 2, 9137, 2, 37, 2, 3, 2, 61511,
    2, 7, 2, 3, 2, 907, 2, 5, 2, 3, 2, 557779, 2, 13, 2, 3,
    2, 5, 2, 59, 2, 3, 2, 383, 2, 30113, 2, 3, 2, 7, 2, 640267,
    2, 3, 2, 223, 2, 5, 2, 3, 2, 41, 2, 7, 2, 3, 2, 5,
    2, 1091, 2, 3, 2, 71413, 2, 19, 2, 3, 2, 138647, 2, 67, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 311,
    2, 3, 2, 337, 2, 7, 2, 3, 2, 1748477, 2, 13, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 23, 2, 107, 2, 3, 2, 5, 2, 199, 2, 3,
    2, 7, 2, 433, 2, 3, 2, 2791, 2, 101, 2, 3, 2, 233, 2, 5,
    2, 3, 2, 19, 2, 197, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13,
    2, 17, 2, 3, 2, 61, 2, 129581, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 11, 2, 313, 2, 3, 2, 5, 2, 7, 2, 3, 2, 73, 2, 2663,
    2, 3, 2, 17, 2, 2309, 2, 3, 2, 47, 2, 5, 2, 3, 2, 54460649,
    2, 23, 2, 3, 2, 5, 2, 31, 2, 3, 2, 113, 2, 11, 2, 3,
    2, 21661, 2, 7, 2, 3, 2, 76201669, 2, 5, 2, 3, 2, 13, 2, 375209,
    2, 3, 2, 5, 2, 83, 2, 3, 2, 127, 2, 13451, 2, 3, 2, 7,
    2, 53, 2, 3, 2, 19, 2, 5, 2, 3, 2, 1499, 2, 7, 2, 3,
    2, 5, 2, 131, 2, 3, 2, 58111, 2, 68281, 2, 3, 2, 29, 2, 11,
    2, 3, 2, 89, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5,
    2, 36067, 2, 3, 2, 11, 2, 7, 2, 3, 2, 13, 2, 2903, 2, 3,
    2, 2203, 2, 5, 2, 3, 2, 173, 2, 43, 2, 3, 2, 5, 2, 73,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 67, 2, 23, 2, 3, 2, 1531,
    2, 5, 2, 3, 2, 97053239, 2, 30757, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 5669, 2, 261451, 2, 3, 2, 11, 2]

/-- Table 9 row: the prime after 34847474118974633 is 34847474118974633 + 986. -/
theorem gap9_986 : IsGapAt 34847474118974633 986 :=
  isGapAt_of 34847474118974633 986 (p34847474118974633) (by show Nat.Prime 34847474118975619; exact p34847474118975619) gds_986 (by decide +kernel)

def gds_1006 : List ℕ := [
    2, 3, 2, 11, 2, 47, 2, 3, 2, 17, 2, 5, 2, 3, 2, 7,
    2, 23291, 2, 3, 2, 5, 2, 71, 2, 3, 2, 43, 2, 7, 2, 3,
    2, 23957, 2, 37, 2, 3, 2, 173, 2, 5, 2, 3, 2, 1321, 2, 11,
    2, 3, 2, 5, 2, 41, 2, 3, 2, 7, 2, 61, 2, 3, 2, 6222163,
    2, 1667, 2, 3, 2, 11, 2, 5, 2, 3, 2, 53, 2, 17, 2, 3,
    2, 5, 2, 197, 2, 3, 2, 31667, 2, 1367, 2, 3, 2, 271, 2, 109,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 1607, 2, 13, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 19, 2, 31, 2, 3, 2, 1540447, 2, 29, 2, 3,
    2, 487, 2, 5, 2, 3, 2, 11, 2, 683, 2, 3, 2, 5, 2, 599,
    2, 3, 2, 15073, 2, 11239, 2, 3, 2, 463, 2, 7, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 71, 2, 541, 2, 3, 2, 5, 2, 139, 2, 3,
    2, 101, 2, 11, 2, 3, 2, 7, 2, 13, 2, 3, 2, 157, 2, 5,
    2, 3, 2, 2293, 2, 7, 2, 3, 2, 5, 2, 251, 2, 3, 2, 1217,
    2, 23, 2, 3, 2, 17, 2, 7499, 2, 3, 2, 149, 2, 5, 2, 3,
    2, 7, 2, 59, 2, 3, 2, 5, 2, 107, 2, 3, 2, 13, 2, 7,
    2, 3, 2, 31, 2, 11, 2, 3, 2, 283, 2, 5, 2, 3, 2, 23,
    2, 37, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 37243, 2, 66271, 2, 3, 2, 573691, 2, 5, 2, 3, 2, 43, 2, 47,
    2, 3, 2, 5, 2, 64781, 2, 3, 2, 127, 2, 29, 2, 3, 2, 61,
    2, 31, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 257, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 384817, 2, 659, 2, 3, 2, 11, 2, 53284709,
    2, 3, 2, 431, 2, 5, 2, 3, 2, 19, 2, 23, 2, 3, 2, 5,
    2, 2063, 2, 3, 2, 29, 2, 30253, 2, 3, 2, 79, 2, 7, 2, 3,
    2, 29167, 2, 5, 2, 3, 2, 373, 2, 11, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 239, 2, 215249, 2, 3, 2, 7, 2, 499, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 37, 2, 7, 2, 3, 2, 5, 2, 307, 2, 3,
    2, 17, 2, 13, 2, 3, 2, 1259, 2, 61, 2, 3, 2, 31, 2, 5,
    2, 3, 2, 7, 2, 14747, 2, 3, 2, 5, 2, 11, 2, 3, 2, 107,
    2, 7, 2, 3, 2, 313, 2, 113, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 11, 2, 10810873, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 37,
    2, 3, 2, 2181541, 2, 17, 2, 3, 2, 311, 2, 5, 2, 3, 2, 61973749,
    2, 13, 2, 3, 2, 5, 2, 157, 2, 3, 2, 2837, 2, 11, 2, 3,
    2, 73, 2, 3381223, 2, 3, 2, 7, 2, 5, 2, 3, 2, 1423, 2, 2129,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 103, 2, 89, 2, 3, 2, 43,
    2, 41, 2, 3, 2, 13, 2, 5, 2, 3, 2, 193, 2, 4987, 2, 3,
    2, 5, 2, 14533, 2, 3, 2, 97, 2, 47, 2, 3, 2, 19, 2, 7,
    2, 3, 2, 143239, 2, 5, 2, 3, 2, 17573, 2, 17, 2, 3, 2, 5,
    2, 21684821, 2, 3, 2, 11, 2, 601, 2, 3, 2, 7, 2, 53, 2, 3,
    2, 859, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 13, 2, 43, 2, 3, 2, 331, 2, 271, 2, 3, 2, 5039,
    2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 149909, 2, 7, 2, 3, 2, 11, 2, 82806589, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 61583, 2, 31, 2, 3, 2, 5, 2, 3929, 2, 3, 2, 7,
    2, 17, 2, 3, 2, 41868187, 2, 1230829, 2, 3, 2, 59, 2, 5, 2, 3,
    2, 13, 2, 11, 2, 3, 2, 5, 2, 151, 2, 3, 2, 89, 2, 2417,
    2, 3, 2, 17, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 5807,
    2, 523, 2, 3, 2, 5, 2, 7, 2, 3, 2, 37273, 2, 109, 2, 3,
    2, 15511, 2, 3221, 2, 3, 2, 6659687, 2, 5, 2, 3, 2, 167, 2, 34291757,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 64251233, 2, 67531, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 739, 2, 5, 2, 3, 2, 11, 2, 1163, 2, 3,
    2, 5, 2, 83, 2, 3, 2, 23, 2, 13, 2, 3, 2, 7, 2, 149,
    2, 3, 2, 577, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5,
    2, 26959, 2, 3, 2, 79, 2, 11, 2, 3, 2, 8268493, 2, 367, 2, 3,
    2, 37, 2, 5, 2, 3, 2, 7, 2, 491591, 2, 3, 2, 5, 2, 31,
    2, 3, 2, 15124297, 2, 7, 2, 3, 2, 41, 2, 71, 2, 3, 2, 29,
    2, 5, 2, 3, 2, 108139, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 7, 2, 23, 2, 3, 2, 1549, 2, 11, 2, 3, 2, 105137, 2, 5,
    2, 3, 2, 19, 2, 49633, 2, 3, 2, 5, 2, 37, 2, 3, 2, 11,
    2, 2273, 2, 3, 2, 547, 2, 59, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 23, 2, 179, 2, 3, 2, 5, 2, 7, 2, 3, 2, 10809553, 2, 881,
    2, 3, 2, 4993, 2, 13, 2, 3, 2, 83, 2, 5, 2, 3, 2, 521,
    2, 541231, 2, 3, 2, 5, 2, 863309, 2, 3, 2, 31, 2, 2155799, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 13999, 2, 5, 2, 3, 2]

/-- Table 9 row: the prime after 37343192296558573 is 37343192296558573 + 1006. -/
theorem gap9_1006 : IsGapAt 37343192296558573 1006 :=
  isGapAt_of 37343192296558573 1006 (p37343192296558573) (by show Nat.Prime 37343192296559579; exact p37343192296559579) gds_1006 (by decide +kernel)

def gds_1018 : List ℕ := [
    2, 3, 2, 19, 2, 5, 2, 3, 2, 29, 2, 162791, 2, 3, 2, 5,
    2, 127, 2, 3, 2, 17, 2, 11, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 71935489, 2, 5, 2, 3, 2, 10871767, 2, 19, 2, 3, 2, 5, 2, 28759,
    2, 3, 2, 188999, 2, 13, 2, 3, 2, 7, 2, 6389, 2, 3, 2, 283181,
    2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 73, 2, 3,
    2, 31, 2, 509, 2, 3, 2, 41, 2, 11, 2, 3, 2, 760531, 2, 5,
    2, 3, 2, 7, 2, 115153, 2, 3, 2, 5, 2, 59, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 19, 2, 109013, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 67, 2, 13, 2, 3, 2, 5, 2, 140910619, 2, 3, 2, 7, 2, 31,
    2, 3, 2, 3583, 2, 1033, 2, 3, 2, 139, 2, 5, 2, 3, 2, 97,
    2, 23, 2, 3, 2, 5, 2, 1601, 2, 3, 2, 191, 2, 47, 2, 3,
    2, 11, 2, 103, 2, 3, 2, 7, 2, 5, 2, 3, 2, 433, 2, 17,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 37, 2, 179, 2, 3, 2, 23,
    2, 13, 2, 3, 2, 22937, 2, 5, 2, 3, 2, 29096983, 2, 11, 2, 3,
    2, 5, 2, 19356377, 2, 3, 2, 19, 2, 107, 2, 3, 2, 3761, 2, 7,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 12829, 2, 41, 2, 3, 2, 5,
    2, 53, 2, 3, 2, 13, 2, 67, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 163811, 2, 5, 2, 3, 2, 173, 2, 7, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 13171, 2, 17, 2, 3, 2, 1181, 2, 23, 2, 3, 2, 313,
    2, 5, 2, 3, 2, 7, 2, 43, 2, 3, 2, 5, 2, 83, 2, 3,
    2, 43370183, 2, 7, 2, 3, 2, 17, 2, 31, 2, 3, 2, 41, 2, 5,
    2, 3, 2, 13, 2, 23827, 2, 3, 2, 5, 2, 45863, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 29, 2, 547, 2, 3, 2, 53, 2, 5, 2, 3,
    2, 73, 2, 24631, 2, 3, 2, 5, 2, 281, 2, 3, 2, 37309, 2, 19,
    2, 3, 2, 1399, 2, 2138971, 2, 3, 2, 7, 2, 5, 2, 3, 2, 444289,
    2, 1009457, 2, 3, 2, 5, 2, 7, 2, 3, 2, 631, 2, 2731, 2, 3,
    2, 13, 2, 11, 2, 3, 2, 37, 2, 5, 2, 3, 2, 17, 2, 139,
    2, 3, 2, 5, 2, 23, 2, 3, 2, 11, 2, 13, 2, 3, 2, 107,
    2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 19, 2, 59, 2, 3,
    2, 5, 2, 25279873, 2, 3, 2, 101, 2, 29, 2, 3, 2, 7, 2, 46831,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 641, 2, 7, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 1567, 2, 79, 2, 3, 2, 11, 2, 3380731, 2, 3,
    2, 347, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 1021,
    2, 3, 2, 17, 2, 7, 2, 3, 2, 8969, 2, 569, 2, 3, 2, 151,
    2, 5, 2, 3, 2, 47, 2, 11, 2, 3, 2, 5, 2, 229, 2, 3,
    2, 7, 2, 17579, 2, 3, 2, 150453253, 2, 43, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 41, 2, 7542707, 2, 3, 2, 5, 2, 61, 2, 3, 2, 103,
    2, 3849583, 2, 3, 2, 109, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 20981, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 64879,
    2, 3, 2, 2777, 2, 438701, 2, 3, 2, 17, 2, 5, 2, 3, 2, 11,
    2, 239, 2, 3, 2, 5, 2, 29, 2, 3, 2, 13, 2, 947, 2, 3,
    2, 523, 2, 7, 2, 3, 2, 337, 2, 5, 2, 3, 2, 137143, 2, 2437,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 53, 2, 11, 2, 3, 2, 7,
    2, 443, 2, 3, 2, 479, 2, 5, 2, 3, 2, 2969, 2, 7, 2, 3,
    2, 5, 2, 71, 2, 3, 2, 1301, 2, 23, 2, 3, 2, 2161, 2, 37,
    2, 3, 2, 2851, 2, 5, 2, 3, 2, 7, 2, 557639, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 43, 2, 7, 2, 3, 2, 1787, 2, 11, 2, 3,
    2, 608117, 2, 5, 2, 3, 2, 23, 2, 269, 2, 3, 2, 5, 2, 4339,
    2, 3, 2, 7, 2, 955391, 2, 3, 2, 887, 2, 127, 2, 3, 2, 823,
    2, 5, 2, 3, 2, 1151, 2, 223, 2, 3, 2, 5, 2, 103, 2, 3,
    2, 19, 2, 17, 2, 3, 2, 13, 2, 4733, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 79, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 47,
    2, 13, 2, 3, 2, 11, 2, 19, 2, 3, 2, 2551, 2, 5, 2, 3,
    2, 71, 2, 23, 2, 3, 2, 5, 2, 37643, 2, 3, 2, 75580187, 2, 89,
    2, 3, 2, 37, 2, 7, 2, 3, 2, 96797411, 2, 5, 2, 3, 2, 29,
    2, 11, 2, 3, 2, 5, 2, 31, 2, 3, 2, 3539, 2, 53, 2, 3,
    2, 7, 2, 3257, 2, 3, 2, 11, 2, 5, 2, 3, 2, 102282779, 2, 7,
    2, 3, 2, 5, 2, 113, 2, 3, 2, 199, 2, 283, 2, 3, 2, 541,
    2, 313, 2, 3, 2, 59, 2, 5, 2, 3, 2, 7, 2, 37, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 10159, 2, 7, 2, 3, 2, 34376549, 2, 131,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 173, 2, 3, 2, 5,
    2, 79, 2, 3, 2, 7, 2, 1861, 2, 3, 2, 139, 2, 13, 2, 3,
    2, 839, 2, 5, 2, 3, 2, 43, 2, 1619, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 31, 2, 11, 2, 3, 2]

/-- Table 9 row: the prime after 37967240836435909 is 37967240836435909 + 1018. -/
theorem gap9_1018 : IsGapAt 37967240836435909 1018 :=
  isGapAt_of 37967240836435909 1018 (p37967240836435909) (by show Nat.Prime 37967240836436927; exact p37967240836436927) gds_1018 (by decide +kernel)

end LeanLab.OeSHP2014
