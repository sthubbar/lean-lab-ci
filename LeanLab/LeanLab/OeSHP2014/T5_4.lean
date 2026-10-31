/-
P0005 Oliveira e Silva, Herzog, Pardi 2014, Math. Comp. 83, 2033 to 2060, Table 5 page 2044,
the rows not already in Sinisalo 1993 Table 2, part 4: minGB S(p) = p. Divisors and Pratt
certificates by Python, checked by the kernel. That S(p) is the least such n and the list of
records complete are the authors' search, cited. Run 20261018T1103Z-12430, unit U-0946.
AI-written Lean code, Claude, 2026-10-18. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.Base

namespace LeanLab.OeSHP2014

open LeanLab.Verifications LeanLab.Verifications.Top50
open LeanLab.Verifications.Pratt (pB)

set_option Elab.async false

theorem p10050203 : Nat.Prime 10050203 := by
  refine Pratt.pratt 10050203 2 [(2, 1), (19, 1), (73, 1), (3623, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p11402329 : Nat.Prime 11402329 := by
  refine Pratt.pratt 11402329 43 [(2, 3), (3, 1), (7, 1), (67, 1), (1013, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p140702843 : Nat.Prime 140702843 := by
  refine Pratt.pratt 140702843 2 [(2, 1), (7, 1), (10050203, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p10050203
theorem p281405687 : Nat.Prime 281405687 := by
  refine Pratt.pratt 281405687 5 [(2, 1), (140702843, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p140702843
theorem p312019297 : Nat.Prime 312019297 := by
  refine Pratt.pratt 312019297 5 [(2, 5), (3, 1), (317, 1), (10253, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p2701620223 : Nat.Prime 2701620223 := by
  refine Pratt.pratt 2701620223 3 [(2, 1), (3, 1), (7, 1), (19, 1), (29, 1), (116741, 1)] (by norm_num)
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
theorem p2916002657 : Nat.Prime 2916002657 := by
  refine Pratt.pratt 2916002657 3 [(2, 5), (7, 1), (17, 1), (19, 1), (41, 1), (983, 1)] (by norm_num)
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
theorem p6074268019 : Nat.Prime 6074268019 := by
  refine Pratt.pratt 6074268019 2 [(2, 1), (3, 1), (7, 1), (13, 1), (269, 1), (41357, 1)] (by norm_num)
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
theorem p6422404841 : Nat.Prime 6422404841 := by
  refine Pratt.pratt 6422404841 3 [(2, 3), (5, 1), (17, 1), (9444713, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p17209562219 : Nat.Prime 17209562219 := by
  refine Pratt.pratt 17209562219 2 [(2, 1), (4517, 1), (1904977, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p47935391117 : Nat.Prime 47935391117 := by
  refine Pratt.pratt 47935391117 2 [(2, 2), (1051, 1), (11402329, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p11402329
theorem p52882918379 : Nat.Prime 52882918379 := by
  refine Pratt.pratt 52882918379 2 [(2, 1), (35461, 1), (745649, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p118696140709 : Nat.Prime 118696140709 := by
  refine Pratt.pratt 118696140709 2 [(2, 2), (3, 1), (17, 1), (239, 1), (2434493, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p172903694273 : Nat.Prime 172903694273 := by
  refine Pratt.pratt 172903694273 3 [(2, 6), (2701620223, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p2701620223
theorem p960654543091 : Nat.Prime 960654543091 := by
  refine Pratt.pratt 960654543091 11 [(2, 1), (3, 1), (5, 1), (11, 1), (17, 1), (23, 1), (7445203, 1)] (by norm_num)
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
theorem p5187110828191 : Nat.Prime 5187110828191 := by
  refine Pratt.pratt 5187110828191 6 [(2, 1), (3, 1), (5, 1), (172903694273, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p172903694273
theorem p7742873306969 : Nat.Prime 7742873306969 := by
  refine Pratt.pratt 7742873306969 3 [(2, 3), (17, 1), (140263, 1), (405901, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p28967857897373251 : Nat.Prime 28967857897373251 := by
  refine Pratt.pratt 28967857897373251 3 [(2, 1), (3, 1), (5, 3), (19, 1), (457, 1), (26647, 1), (166931, 1)] (by norm_num)
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
theorem p296540042727106103 : Nat.Prime 296540042727106103 := by
  refine Pratt.pratt 296540042727106103 5 [(2, 1), (37, 1), (409, 1), (1613, 1), (6074268019, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p6074268019
theorem p344205743816088281 : Nat.Prime 344205743816088281 := by
  refine Pratt.pratt 344205743816088281 3 [(2, 3), (5, 1), (7, 1), (19, 1), (499, 1), (1303, 2), (76369, 1)] (by norm_num)
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
theorem p370581106766901881 : Nat.Prime 370581106766901881 := by
  refine Pratt.pratt 370581106766901881 3 [(2, 3), (5, 1), (23, 1), (349, 1), (397, 1), (1493, 1), (1947241, 1)] (by norm_num)
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
theorem p411411629991715477 : Nat.Prime 411411629991715477 := by
  refine Pratt.pratt 411411629991715477 2 [(2, 2), (3, 1), (43, 1), (16633, 1), (47935391117, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p47935391117
theorem p558619547569900139 : Nat.Prime 558619547569900139 := by
  refine Pratt.pratt 558619547569900139 2 [(2, 1), (7, 2), (17, 1), (1191539, 1), (281405687, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p281405687
theorem p754276228832949539 : Nat.Prime 754276228832949539 := by
  refine Pratt.pratt 754276228832949539 2 [(2, 1), (47, 1), (67, 1), (1009, 1), (118696140709, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p118696140709
theorem p813695622192160313 : Nat.Prime 813695622192160313 := by
  refine Pratt.pratt 813695622192160313 3 [(2, 3), (11, 2), (2694047, 1), (312019297, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p312019297
theorem p1473611722331814509 : Nat.Prime 1473611722331814509 := by
  refine Pratt.pratt 1473611722331814509 2 [(2, 2), (353, 1), (162499, 1), (6422404841, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p6422404841
theorem p1599566025914310491 : Nat.Prime 1599566025914310491 := by
  refine Pratt.pratt 1599566025914310491 6 [(2, 1), (5, 1), (541, 1), (5591, 1), (52882918379, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p52882918379
theorem p1793167785904795067 : Nat.Prime 1793167785904795067 := by
  refine Pratt.pratt 1793167785904795067 2 [(2, 1), (13, 1), (29, 1), (138191, 1), (17209562219, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p17209562219
theorem p2043437180188802729 : Nat.Prime 2043437180188802729 := by
  refine Pratt.pratt 2043437180188802729 3 [(2, 3), (11, 1), (2999, 1), (7742873306969, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p7742873306969
theorem p2758163428100230091 : Nat.Prime 2758163428100230091 := by
  refine Pratt.pratt 2758163428100230091 2 [(2, 1), (5, 1), (139, 1), (149, 1), (4567, 1), (2916002657, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p2916002657
theorem p3244400084505804113 : Nat.Prime 3244400084505804113 := by
  refine Pratt.pratt 3244400084505804113 6 [(2, 4), (7, 1), (28967857897373251, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p28967857897373251
theorem p3511797567359752331 : Nat.Prime 3511797567359752331 := by
  refine Pratt.pratt 3511797567359752331 2 [(2, 1), (5, 1), (11, 1), (167, 1), (199, 1), (960654543091, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p960654543091
theorem p3714759793830641033 : Nat.Prime 3714759793830641033 := by
  refine Pratt.pratt 3714759793830641033 3 [(2, 3), (89519, 1), (5187110828191, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p5187110828191
theorem p3878297017437637919 : Nat.Prime 3878297017437637919 := by
  refine Pratt.pratt 3878297017437637919 13 [(2, 1), (19, 1), (439, 1), (853, 1), (881, 1), (11969, 1), (25847, 1)] (by norm_num)
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

def ds_7013 : List ℕ := [
    2, 151, 53, 3, 5, 3, 103, 3,
    61, 7, 3, 3, 5, 3, 317, 31,
    41, 3, 3, 5, 3, 3, 70226389, 17271521,
    3, 5, 3, 11, 3, 7, 3, 5,
    104055547, 3, 163, 3, 3, 3, 1471, 11,
    107, 3, 5, 3, 7, 3, 3, 3,
    379, 3, 769, 7, 3, 5, 701, 553517,
    13, 3, 3, 5, 3, 1571, 3, 5,
    3, 37, 3, 3, 13, 3, 281213683, 1789,
    3, 3, 3, 4013, 61, 3, 5, 3,
    347970499, 3, 5, 3, 3, 653, 7, 3,
    5, 3, 13033, 23, 3, 5, 3, 11,
    17, 5, 3, 3, 3, 127, 344407501, 11,
    3, 3, 12841, 967, 73, 3, 3, 3,
    7, 3, 3, 5, 3, 433, 585749, 7,
    3, 3, 307, 709, 3, 5, 3, 233,
    3, 3, 3, 7, 3, 3, 5, 3,
    11689, 3, 29, 991, 3, 5, 3, 7,
    3, 131, 3, 26715473, 3, 97, 3, 5,
    3, 1721, 3, 5, 3, 3209, 3, 5,
    839, 7, 3, 5, 83, 19, 3, 3,
    3, 449, 17, 3, 5, 3, 3, 13,
    3, 5, 3, 3, 3, 5, 3, 11,
    683, 67, 3, 3, 3, 5, 3, 7,
    3, 5, 115853, 3319, 3, 3, 157, 17,
    11, 3, 3, 3, 71, 53, 3, 13,
    7, 3, 3, 5, 3, 23, 29, 3,
    3, 5, 10507879, 7, 3, 3, 335281, 3,
    11, 3, 647, 13, 3, 5, 3, 3,
    3, 5, 3, 61, 3, 11, 7, 5,
    1439, 3, 3, 3, 19, 11, 3, 5,
    3, 7, 3, 5, 509, 3, 293289817, 248389,
    3, 3, 811, 3, 3, 7, 3, 3,
    79, 3, 7, 5, 3, 17, 3, 3,
    3, 3, 3, 3, 22664731, 3, 3, 5,
    11, 3, 347, 3, 3, 5, 3, 7,
    3, 11, 5, 13, 31, 5, 3, 317,
    3, 83, 90469, 3, 3, 23, 3, 7,
    3, 3, 41, 3, 17, 3, 13, 100604327,
    5, 3, 7, 3, 31, 5, 3, 7,
    3, 3, 5, 3, 11, 3, 3, 3,
    739, 7, 3, 19, 3, 17, 3, 137,
    3, 23, 3, 3, 3, 7, 59, 3,
    43, 7, 3, 3, 5, 2819, 3, 3,
    5, 3, 3, 248673101, 349, 5, 11, 7,
    3, 5, 17, 199, 3, 3, 149, 3,
    3, 5, 3, 2699, 7, 3, 3, 19,
    5, 3, 13, 3, 5, 7, 3, 31,
    3, 59, 3, 3, 3, 13, 3, 19,
    23831, 3, 5, 3, 3, 13553, 3, 5,
    3, 17, 3, 211, 73, 3, 3, 5,
    3, 3549019, 3, 2239, 7, 3, 3, 5,
    11, 3, 15913, 216919, 113, 3, 7, 16993,
    3, 17, 23, 7, 3, 13, 3, 5,
    3, 151, 3, 5, 3, 3, 3, 3,
    163, 137, 3, 67, 3, 7, 3, 5189,
    3, 3, 3, 5, 37, 11, 3, 5,
    3, 5, 3, 41, 3, 3, 1121509, 3,
    3, 3, 3, 491, 101, 3, 3, 7,
    541, 3, 5, 3, 7, 3, 11, 787,
    3, 2837, 3, 5, 3, 13, 3, 5,
    3, 3, 3, 10552963, 3, 181, 11, 3,
    3, 7, 3, 3, 5, 3, 79, 3,
    3, 389, 13, 3, 3, 3, 503, 5,
    3, 7331, 3, 3, 5, 3, 19, 3,
    3, 3, 5, 7, 3, 13, 3, 311,
    11, 5, 3, 19, 3, 5, 3, 229,
    3, 5, 3, 3, 5, 269, 3, 67,
    23, 3, 3, 19, 3, 1543, 5, 3,
    179, 13, 7, 3, 3, 61, 3, 3,
    6653, 17, 5, 3, 3, 3, 197, 3,
    11, 43, 3, 173, 3, 3, 3, 5,
    1861, 3, 7, 3, 5, 3, 29906263, 1367,
    3, 5, 3, 17, 19, 3, 3, 6841,
    3, 367, 3, 3, 2395031, 5, 7, 16937,
    5, 3, 3, 3, 5, 53, 11, 5,
    3, 349, 3, 3, 19, 3, 7, 7570561,
    3, 3, 3, 17011, 3, 3, 3, 3,
    13, 3, 15450913, 7, 3, 3, 3, 107,
    5559979, 5, 31, 5, 3, 3, 7, 5,
    3, 3, 59, 3, 11, 29, 3, 3,
    7, 3, 3, 5, 42102419, 31, 3, 3,
    1279, 5, 3, 97, 7, 3, 3, 47,
    3, 19, 3, 3, 3, 89, 165779, 3,
    5, 3, 163, 5, 3, 3, 5, 19,
    17, 3, 3, 3, 3, 29, 7, 3,
    5, 3, 11, 3, 3, 3, 5, 3,
    7, 5, 3803, 7, 3, 8467, 17, 23,
    3, 191, 3, 5, 5, 11, 183892729, 136539059,
    3, 3, 13, 3, 3, 3, 5, 3,
    3, 5, 6961, 3, 353, 5, 3, 17,
    11, 3, 3, 5, 3, 3, 3, 7,
    3, 5, 3, 251, 3, 3, 5, 3,
    7, 3, 29, 3, 3, 523, 3, 5,
    11, 3, 5, 3, 3, 3, 7, 3,
    5, 13, 17, 3, 3, 3, 29, 11,
    3, 3, 5, 7, 3, 61, 3, 239,
    2540093, 3, 157, 6037, 3, 5, 72778679, 3,
    5, 256211, 3, 3, 11, 149, 3, 3,
    3, 37, 3, 5, 11, 3, 5, 3,
    2231609, 3, 3, 2861, 13, 3, 7, 3,
    3, 5, 3, 3, 2657, 137909, 491, 3,
    3, 7, 113, 3, 5, 43577, 17, 7,
    3, 3, 13, 101, 3, 3, 3, 3,
    601, 3, 3, 3, 1583, 3, 3, 167,
    3, 5, 5, 3, 3, 5, 3, 31,
    19, 3, 3, 5, 107, 3, 3, 3,
    127, 47, 3, 3, 3, 23, 3, 5,
    3, 3, 43, 3, 67, 5, 3, 139,
    3, 5, 3, 3389, 3, 23, 3, 7,
    3, 21347, 9533, 157, 3, 3, 13, 3,
    5, 7, 41, 3, 7, 3, 3, 5,
    13, 65123, 3, 3, 5]

theorem prime_sub_7013 : Nat.Prime (296540042727113116 - 7013) := by
  show Nat.Prime 296540042727106103
  exact p296540042727106103

theorem check_7013 : allC 296540042727113116 7013 P10k ds_7013 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 296540042727113116 is 7013. -/
theorem minGB_S_7013 : minGB 296540042727113116 = 7013 :=
  minGB_eq_of P10k P10k_complete 296540042727113116 7013 (by norm_num) (by norm_num) prime_sub_7013 ds_7013 check_7013

def ds_7187 : List ℕ := [
    2, 5, 17, 3, 59, 3, 41, 3,
    5, 74719, 3, 3, 7, 3, 13, 5,
    61, 3, 3, 31, 3, 3, 5, 149,
    3, 19, 3, 17, 3, 5, 3, 11,
    157, 3, 5273, 3, 3, 3, 7, 5,
    3671, 3, 73, 3, 11, 3, 3, 3,
    110563, 3, 5, 23, 3, 7, 31, 5,
    211, 3, 3, 13, 3, 5, 3, 17,
    3, 98639, 3, 3, 29, 3, 5, 13,
    3, 3, 3, 5, 3323, 3, 809, 3,
    7, 3, 953, 3, 3, 5, 263, 3,
    7, 3, 9649, 83, 3, 43103, 3, 5,
    41, 29, 3, 3, 3, 19, 5, 2819,
    3, 3, 7, 5, 37, 3, 3, 3,
    17, 3, 3, 1223, 3, 1446449, 5, 11,
    3, 3, 283, 5, 3, 499, 3, 17,
    3, 3, 3, 5, 3, 3, 378179, 3,
    5, 3, 7, 27751, 3, 17, 3, 13,
    3, 7, 3, 11, 3, 5, 3, 7,
    3, 71473, 3, 647, 3, 23, 3, 363829,
    127, 5, 3, 113, 83, 5, 3, 3,
    3, 5, 656791, 3, 150091, 3, 3, 7,
    3, 13, 3, 3, 3, 7, 3, 6701,
    5, 232753, 3, 3, 3, 109, 3, 5,
    3, 503, 11, 5, 3, 3, 7, 5,
    17, 3, 3, 3, 7, 179, 3, 5,
    3673, 3, 3, 7, 3, 139, 11, 3,
    3, 89, 239, 5, 3, 3, 269, 3,
    7, 3, 5, 75767287, 3, 11, 3, 3,
    3, 23, 3, 37, 3, 5, 419, 7,
    5, 3, 3, 3, 5, 31, 3, 1109,
    3, 5, 3, 59581, 13, 3, 5, 23,
    3, 3, 7, 3, 3, 5087, 3, 3,
    19, 3, 37, 7, 3, 5, 3, 3,
    3, 3, 3, 3, 103, 3, 3, 19,
    5, 3, 7, 3, 3, 823, 3, 149,
    3, 7, 107, 61291, 5, 7, 3, 5647,
    3, 5, 11, 3, 3, 13, 3, 5,
    3, 3, 263, 3, 19, 3, 5, 97081,
    436003, 3, 29, 3, 7, 11, 3, 53,
    3, 3, 7, 3, 5, 3, 3, 3,
    353, 5, 3, 1019, 3, 5, 3, 7,
    3, 5, 3, 3, 3, 7311937, 7, 3,
    5, 839, 3, 3, 7, 39229, 3, 3,
    19, 3, 3, 5, 479, 190979, 7457, 5,
    3, 11, 23, 109, 3, 3, 7, 3,
    3, 185208887, 3, 5, 14505679, 3, 3, 4273,
    1777, 3, 19, 3, 13, 5, 3, 17,
    3, 5, 3, 3, 3, 7, 3, 5,
    13, 3, 1468553, 3, 3, 7, 3, 761,
    3, 5, 3, 13, 543803989, 3, 3, 211,
    3, 37, 3, 11, 5, 3, 3, 17,
    137, 3, 7, 5, 251, 3, 31646963, 7,
    3, 29, 5, 11, 3, 23, 3, 13,
    3, 5, 3, 37, 3, 3, 3, 3,
    5, 13, 3, 10009, 3, 23, 3, 11,
    3, 3, 3, 7, 5, 883, 3, 11941,
    3, 21980041, 3, 73, 3, 3, 11, 3,
    3, 3, 3, 5, 727, 3, 3, 136113541,
    7, 3, 17, 3, 2087, 3, 19, 5,
    3, 6417413, 3, 41, 3, 83, 3, 947,
    3, 3, 3, 7, 3, 5, 911, 3,
    3, 13, 3, 3, 1201, 3, 5, 3,
    3, 1955501, 5, 3, 3, 3, 821, 1163,
    3, 17, 3, 3, 137, 3, 53, 3,
    3, 3, 11, 109, 3, 7, 3, 268676497,
    5, 7, 3, 5, 3, 7823, 3, 5,
    3, 17, 3, 3, 181, 601, 3, 5,
    37, 3, 3, 7, 3, 7, 29, 3,
    79, 5, 4657, 3, 3, 1297, 3, 3,
    5, 491, 11, 3, 3, 3, 132263, 3,
    5, 521, 3, 7, 3, 3, 3, 43,
    193, 3, 328043, 3, 7, 3, 5, 13,
    3, 97, 3, 5, 11, 3, 3, 13,
    3, 29, 3, 3, 5, 17, 1837181, 7,
    11, 3, 3, 3, 7, 1283, 5, 79,
    3, 5, 3, 3, 23, 3, 5, 19,
    3, 3, 3, 5, 3, 3, 3, 3,
    269, 3, 5, 13, 3, 3, 3, 5,
    359, 41, 5, 31, 3, 3, 5, 11,
    3, 3, 7, 3, 5, 17, 3, 3,
    11, 3, 3, 7, 103, 19, 3, 3,
    1091, 23, 3, 41, 5, 3, 3, 59,
    3, 5, 3, 3, 3, 5, 73, 3,
    509, 3, 7, 10889, 3, 3, 7, 593,
    89, 3, 3, 3, 3, 11, 5, 3,
    607, 3, 5741, 3, 3, 3, 19, 3,
    38603, 37, 5, 11, 3, 449, 5, 17,
    3, 5, 3, 13, 173, 331, 5, 133520921,
    3, 3, 7, 3, 3, 3, 36493, 3,
    3, 12967, 11, 3, 5, 7, 3, 13,
    127, 3, 3, 205015303, 3, 3, 3, 5,
    3, 347, 3, 523, 3, 3, 31, 3,
    197, 3, 7, 3, 3, 5, 3, 7,
    17, 3, 11, 3, 3, 3, 5, 3,
    19, 11, 5, 3, 3, 3, 5, 443,
    3, 3, 1511, 1237, 3, 7, 3, 13,
    5, 3, 37, 11, 3, 27487, 312029, 3,
    67, 19, 3, 3, 7, 5, 3, 3,
    3, 7, 3, 163, 5, 3, 7, 3,
    5, 3, 3, 5, 29339, 3, 5, 3,
    3, 14593, 3, 3, 7, 5, 11, 3,
    3, 13, 7, 3, 23, 2833, 5, 17,
    3, 3, 5, 5119, 3, 3, 3, 3,
    230431, 3, 3, 3, 23, 3, 3, 5,
    3, 1549, 13, 3, 3, 7, 3, 5,
    9601, 3, 3, 31, 11, 3, 3, 3,
    5, 41, 3, 3, 3, 499, 3, 89,
    3, 3, 7, 3, 17, 7, 3, 40939,
    3, 43, 3, 5, 3, 19, 3, 5,
    3, 6779, 5, 1499, 3, 3, 53, 3,
    13, 12983, 6689, 3, 29, 3, 3, 7,
    427436791, 5, 3, 3, 23, 5, 435277, 3,
    3, 5, 3, 3, 163, 5, 1811, 209549,
    11, 3, 41, 3, 3]

theorem prime_sub_7187 : Nat.Prime (344205743816095468 - 7187) := by
  show Nat.Prime 344205743816088281
  exact p344205743816088281

theorem check_7187 : allC 344205743816095468 7187 P10k ds_7187 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 344205743816095468 is 7187. -/
theorem minGB_S_7187 : minGB 344205743816095468 = 7187 :=
  minGB_eq_of P10k P10k_complete 344205743816095468 7187 (by norm_num) (by norm_num) prime_sub_7187 ds_7187 check_7187

def ds_7307 : List ℕ := [
    2, 5, 17, 3, 311, 3, 7, 3,
    5, 11, 3, 3, 191, 3, 1597, 5,
    7, 3, 3, 19, 3, 3, 5, 743689,
    3, 7, 3, 17, 3, 5, 3, 108217,
    13, 3, 47, 3, 3, 3, 43, 5,
    1951, 3, 101, 3, 1289, 3, 3, 3,
    7, 3, 5, 59, 3, 40697, 8273, 5,
    7, 3, 3, 137, 3, 5, 3, 7,
    3, 313, 3, 3, 97, 3, 5, 11,
    3, 3, 3, 5, 163, 3, 127, 3,
    256577, 3, 23, 3, 3, 5, 13, 3,
    86509, 3, 1279807, 7, 3, 11, 3, 5,
    18490709, 7, 3, 3, 3, 11, 5, 23,
    3, 3, 56081, 5, 149, 3, 3, 3,
    17, 3, 3, 19, 3, 7, 5, 1016083,
    3, 3, 349, 5, 3, 2221, 3, 17,
    3, 3, 3, 5, 3, 3, 13, 3,
    5, 3, 101, 103, 3, 11, 3, 31,
    3, 13, 3, 7, 3, 5, 3, 167,
    3, 11, 3, 53, 3, 97, 3, 7,
    59, 5, 3, 48337, 73, 5, 3, 3,
    3, 5, 11, 3, 513628867, 3, 3, 2677,
    3, 2089, 3, 3, 3, 1709, 3, 19,
    5, 7, 3, 3, 3, 7, 3, 5,
    3, 37, 191, 5, 3, 3, 11, 5,
    13, 3, 3, 3, 23, 7, 3, 5,
    109, 3, 3, 59, 3, 13, 7, 3,
    3, 7, 163, 5, 3, 3, 125641, 3,
    103, 3, 5, 19, 3, 419, 3, 3,
    3, 11, 3, 7, 3, 5, 2029, 97,
    5, 3, 3, 3, 5, 47, 3, 7,
    3, 5, 3, 83, 139, 3, 5, 13,
    3, 3, 17, 3, 3, 19, 3, 3,
    7, 3, 49193, 199, 3, 5, 3, 3,
    3, 3, 3, 3, 709, 3, 3, 11,
    5, 3, 37, 3, 3, 131, 3, 11,
    3, 1097, 2341, 7, 5, 13, 3, 7,
    3, 5, 1753, 3, 3, 4271, 3, 5,
    3, 3, 719, 3, 29, 3, 5, 37,
    211, 3, 13, 3, 83, 2243, 3, 31,
    3, 3, 11, 3, 5, 3, 3, 3,
    11, 5, 3, 19, 3, 5, 3, 205151,
    3, 5, 3, 3, 3, 4639, 653, 3,
    5, 11, 3, 3, 17, 107903, 3, 3,
    284071859, 3, 3, 5, 13, 7, 367, 5,
    3, 89, 389, 125526539, 3, 3, 13, 3,
    3, 179, 3, 5, 223, 3, 3, 7,
    1697, 3, 607, 3, 7, 5, 3, 17,
    3, 5, 3, 3, 3, 31, 3, 5,
    307, 3, 13, 3, 3, 73, 3, 2603233,
    3, 5, 3, 23, 7, 3, 3, 11,
    3, 53, 3, 61, 5, 3, 3, 17,
    102533, 3, 239, 5, 29, 3, 1453, 113,
    3, 7, 5, 47, 3, 7, 3, 228223,
    3, 5, 3, 7, 3, 3, 3, 3,
    5, 271, 3, 2389, 3, 53, 3, 7,
    3, 3, 3, 23, 5, 7, 3, 101,
    3, 7, 3, 13, 3, 3, 269, 3,
    3, 3, 3, 5, 11, 3, 3, 211,
    18565919, 3, 17, 3, 907, 3, 157, 5,
    3, 127, 3, 7, 3, 23, 3, 13,
    3, 3, 3, 11, 3, 5, 6247, 3,
    3, 353, 3, 3, 79, 3, 5, 3,
    3, 31, 5, 3, 3, 3, 11, 7,
    3, 17, 3, 3, 2411, 3, 19, 3,
    3, 3, 293, 89599, 3, 17, 3, 7,
    5, 12141413, 3, 5, 3, 1993, 3, 5,
    3, 7, 3, 3, 6481, 563, 3, 5,
    7039, 3, 3, 19, 3, 11, 7349, 3,
    7, 5, 23, 3, 3, 7, 3, 3,
    5, 71, 7, 3, 3, 3, 29, 3,
    5, 433, 3, 23, 3, 3, 3, 127,
    7, 3, 131, 3, 47666369, 3, 5, 7,
    3, 13, 3, 5, 17, 3, 3, 474137,
    3, 13, 3, 3, 5, 17, 70753, 53,
    97, 3, 3, 3, 11, 46889, 5, 73,
    3, 5, 3, 3, 11, 3, 5, 31,
    3, 3, 3, 5, 3, 3, 3, 3,
    7, 3, 5, 11, 3, 3, 3, 5,
    7, 4346857, 5, 7, 3, 3, 5, 619,
    3, 3, 359, 3, 5, 17, 3, 3,
    13, 3, 3, 12713, 3877, 7, 3, 3,
    31, 7, 3, 37918817, 5, 3, 3, 10867,
    3, 5, 3, 3, 3, 5, 4871, 3,
    14087, 3, 41, 13, 3, 3, 1847, 19,
    7, 3, 3, 3, 3, 421, 5, 3,
    29, 3, 1100123, 3, 3, 3, 193, 3,
    229, 23, 5, 163, 3, 1297, 5, 7,
    3, 5, 3, 7, 373, 218592833, 5, 23,
    3, 3, 6619, 3, 3, 3, 11, 3,
    3, 107, 7, 3, 5, 669173, 3, 11,
    7, 3, 3, 41, 3, 3, 3, 5,
    3, 431299507, 3, 11, 3, 3, 67, 3,
    19, 3, 728333, 3, 3, 5, 3, 4079,
    17, 3, 6229, 3, 3, 3, 5, 3,
    131, 159946607, 5, 3, 3, 3, 5, 31,
    3, 3, 2336393, 29, 3, 211, 3, 7,
    5, 3, 2027, 7, 3, 7, 13, 3,
    154232149, 20359, 3, 3, 227, 5, 3, 3,
    3, 23, 3, 11, 5, 3, 61, 3,
    5, 3, 3, 5, 59073647, 3, 5, 3,
    3, 13, 3, 3, 59, 5, 41, 3,
    3, 37, 11, 3, 571, 7, 5, 17,
    3, 3, 5, 7, 3, 3, 3, 3,
    29, 3, 3, 3, 365773, 3, 3, 5,
    3, 41381, 109, 3, 3, 7789, 3, 5,
    7, 3, 3, 83, 5087, 3, 3, 3,
    5, 61781, 3, 3, 3, 13, 3, 178447,
    3, 3, 10606429, 3, 7, 11, 3, 7,
    3, 769, 3, 5, 3, 11, 3, 5,
    3, 67, 5, 78683827, 3, 3, 79, 3,
    19, 23, 7, 3, 11, 3, 3, 87060863,
    28571, 5, 3, 3, 13, 5, 4027, 3,
    3, 5, 3, 3, 13, 5, 73, 983,
    2365997, 3, 31, 3, 3, 2539, 5, 3,
    1103, 3, 3, 61, 3, 3, 17, 5,
    5, 3]

theorem prime_sub_7307 : Nat.Prime (370581106766909188 - 7307) := by
  show Nat.Prime 370581106766901881
  exact p370581106766901881

theorem check_7307 : allC 370581106766909188 7307 P10k ds_7307 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 370581106766909188 is 7307. -/
theorem minGB_S_7307 : minGB 370581106766909188 = 7307 :=
  minGB_eq_of P10k P10k_complete 370581106766909188 7307 (by norm_num) (by norm_num) prime_sub_7307 ds_7307 check_7307

def ds_7489 : List ℕ := [
    2, 61, 3, 103, 3, 390389, 3, 349,
    3, 3, 5, 19, 3, 863, 3, 3,
    3, 5, 7, 3, 13, 23, 3, 3,
    37, 3, 1721, 3, 7, 3, 17, 3,
    3, 29, 3, 5, 13721479, 2531, 3, 3,
    3, 5, 3, 7, 3, 11, 5, 43,
    3, 13, 3, 3, 5, 3, 3, 3,
    3, 5, 7, 3, 41237363, 3, 13, 3,
    29, 3, 5, 72043, 3, 2161, 3, 3,
    53, 32941, 19, 3, 3, 11, 3, 1459,
    3, 5, 3, 17, 68213, 3, 3, 191,
    3, 11, 3, 3, 7, 3, 230571877, 3,
    3, 3, 641, 5, 2659, 3, 3, 3,
    5, 4493, 3, 3, 3, 5, 19, 7,
    3, 13, 5, 3, 71, 3, 3, 3,
    5, 18503, 3, 3, 5, 3, 241, 3,
    11, 181, 7, 3, 5, 797, 3, 23,
    3, 25219, 3, 3, 5, 3, 7, 3,
    12071, 3, 13, 3, 11, 3, 47, 3,
    97, 3, 7, 3, 2741, 3, 67, 3,
    3, 3, 2417, 3, 3, 3, 5, 43,
    13, 3, 3, 5, 3, 7, 683, 3,
    5, 3, 19, 71, 13, 3, 4751, 3,
    3, 3, 7, 11, 186187, 3, 41, 3,
    5, 3, 3, 3, 5, 31177, 3, 3,
    3, 5, 11437, 17, 3, 3, 967, 3,
    3, 5, 829, 3, 3943, 3, 3, 5,
    7, 3, 3, 3, 5, 13, 3, 197,
    3, 37, 3, 3, 431, 3, 7, 23,
    5, 3, 113, 3, 8398207, 3, 3, 3,
    3, 5, 81937, 317, 3, 3, 257, 3,
    7, 3, 23, 3, 3, 104008559, 3, 3,
    5, 79, 3, 17, 7, 3, 1217, 499,
    3, 196767821, 3, 3, 47, 3, 5, 7,
    233, 17, 190301, 11, 3, 7, 5, 3,
    3, 5, 3, 5, 13, 3, 7, 3,
    29, 3, 3, 3, 3, 3, 31, 3,
    5, 3, 3, 12757, 523, 3, 7, 3,
    5, 7121, 3, 43, 3, 29, 3, 3,
    3, 7, 3, 19, 3, 3, 11, 3,
    5, 41, 3, 67, 3, 5, 11, 19,
    3, 3, 5, 3, 68909, 3, 5, 3,
    17, 3, 5, 23, 7, 3, 3, 5,
    3, 3, 5, 71, 3, 3, 5, 7,
    3, 41, 109, 3, 3, 3, 3, 3,
    139, 3, 3, 3, 616379219, 17, 3, 7,
    5, 3, 37, 3, 3, 5, 20572597, 3,
    3, 53, 3, 2511811, 3, 3, 13, 3,
    19, 3, 5, 17, 59, 3, 18731, 3,
    3, 11, 3, 7, 101, 3, 5, 3,
    29, 3, 5669, 3, 3, 5, 7, 3,
    13, 3, 137, 3, 3, 5, 20089, 3,
    3, 19, 3, 3, 3, 2897, 3, 3,
    11379527, 3, 3, 3, 5, 3, 5, 3,
    653, 3, 11, 3, 7, 5, 167, 49663,
    3, 3, 257, 3, 5, 3, 89, 3,
    11, 5, 17, 3, 3, 3, 7, 3,
    19, 3, 23, 3, 7, 5, 3, 5,
    12007, 45557, 43, 3, 3, 5, 7, 3,
    3, 5, 3, 553097189, 3, 5, 3, 3,
    11, 3, 19, 3, 1523, 3, 7, 3,
    11, 5, 113, 3, 23, 3, 3, 5,
    53, 3, 246923, 5, 3, 13, 3, 31,
    41, 3, 3, 5, 7, 6091, 3, 3,
    309160361, 3, 5, 11, 3, 264416279, 3, 487,
    7505033, 13, 3, 3, 3023, 3, 29, 3,
    3, 3, 1151, 3, 7, 3, 3032033, 3,
    11447, 3, 7, 61, 3, 3, 599, 3,
    3, 5, 23, 3, 29, 3, 3, 17,
    3, 3, 3, 5, 11, 3, 5, 7,
    3, 3, 3, 11, 7, 5, 3, 13,
    3, 3, 67, 3, 11, 1997, 5, 3,
    3, 23, 3, 5, 3, 13183, 3, 3,
    5, 3, 61, 3, 3, 127481, 65653067, 3,
    3719, 3, 11, 13, 3, 3, 3, 3,
    3, 11, 5, 7013, 3, 3, 3, 3,
    19, 3, 1519673, 17, 3, 7, 3, 3,
    233, 5, 33434173, 3, 5, 13, 7, 5,
    3, 61, 3, 3, 5, 2239, 29, 3,
    3, 3, 3, 3, 31, 7, 3, 3,
    37, 163, 3, 269, 3, 3, 5, 7,
    3, 5, 5, 3, 3, 3, 71, 13,
    3, 3, 28444567, 3, 3, 5, 67, 3,
    197, 3, 13, 128002921, 7457, 3, 3, 5,
    3, 7, 3, 3, 21391, 181, 3, 3,
    3, 5, 7, 1319, 20211187, 3, 3, 19,
    3, 1427, 3, 2083, 298861, 17, 3, 7,
    3, 3, 3, 3, 5, 3, 3, 3,
    23, 3, 11, 3, 3, 3, 3, 3,
    336756467, 11, 3, 79, 5, 496339, 3, 7,
    16901, 3, 3, 11, 3, 3, 96794101, 3,
    3, 5, 7, 3, 39217, 983, 7, 3,
    5, 3, 19, 3, 5, 37, 3, 7,
    3, 109, 3, 319037, 13, 3, 5, 3,
    3, 7, 3, 11, 101, 7, 3, 5,
    3, 3, 3, 5, 41, 17, 3, 3,
    5, 107, 3, 3, 37, 3, 5, 3,
    3, 13, 3, 3, 47, 3, 3, 11,
    3, 3, 887, 17, 3, 3, 63779857, 7,
    13, 3, 5, 3, 3, 5, 3, 8093,
    3, 5, 67, 3, 3, 7, 3, 5,
    157, 3, 29, 17, 3, 3, 3, 5,
    2113, 3, 3, 5, 3, 3, 3, 3,
    11, 353, 3, 3, 5, 7, 53657, 389,
    3, 31, 5, 23, 3, 5, 11, 3,
    5, 3, 3, 173, 13, 3, 17, 3,
    3, 5, 7, 3, 3, 71, 7, 379,
    3, 3, 5, 43, 127, 3, 5, 3,
    7, 421, 3, 11, 3, 3, 19, 3,
    5, 3, 2441, 3, 6659, 3, 7, 3,
    5, 3, 3, 3, 5, 9161, 3, 113,
    3, 3, 3, 151, 3, 5, 67, 3,
    3, 3, 5, 7, 3, 3, 3, 293,
    7, 3, 41, 2538821, 3, 3, 3, 3,
    3, 11, 3, 157, 2278631, 3, 3, 7,
    3, 308421227, 19, 3, 457, 744859, 3, 3,
    3, 761, 3, 2411, 5, 3, 7, 3,
    5, 17, 11, 5, 7, 3, 3, 3,
    7, 34757, 3, 3]

theorem prime_sub_7489 : Nat.Prime (411411629991722966 - 7489) := by
  show Nat.Prime 411411629991715477
  exact p411411629991715477

theorem check_7489 : allC 411411629991722966 7489 P10k ds_7489 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 411411629991722966 is 7489. -/
theorem minGB_S_7489 : minGB 411411629991722966 = 7489 :=
  minGB_eq_of P10k P10k_complete 411411629991722966 7489 (by norm_num) (by norm_num) prime_sub_7489 ds_7489 check_7489

def ds_7577 : List ℕ := [
    2, 19, 71, 3, 5, 3, 113, 3,
    4127, 223, 3, 3, 5, 3, 17, 7,
    64633, 3, 3, 5, 3, 3, 47, 319441,
    3, 5, 3, 4789, 3, 13, 3, 5,
    7, 3, 17, 3, 3, 3, 11, 15349,
    7, 3, 5, 3, 1301, 3, 3, 3,
    12809, 3, 11, 56629, 3, 5, 23, 7,
    13, 3, 3, 5, 3, 139, 3, 5,
    3, 10357, 3, 3, 7, 3, 17, 193,
    3, 3, 3, 19, 7, 3, 5, 3,
    59, 3, 5, 3, 3, 43, 151, 3,
    5, 3, 31, 1483, 3, 5, 3, 13,
    233, 5, 3, 3, 3, 7, 11, 2099,
    3, 3, 2141731, 340647829, 7, 3, 3, 3,
    1005439, 3, 3, 5, 3, 47, 31, 13,
    3, 3, 495879869, 7, 3, 5, 3, 443,
    3, 3, 3, 18211, 3, 3, 5, 3,
    59, 3, 3847, 7, 3, 5, 3, 11,
    3, 19, 3, 71, 3, 17, 3, 5,
    3, 2113, 3, 5, 3, 47, 3, 5,
    23, 19, 3, 5, 7, 10663, 3, 3,
    3, 173, 7, 3, 5, 3, 3, 13,
    3, 5, 3, 3, 3, 5, 3, 1645291,
    7, 3761, 3, 3, 3, 5, 3, 5431,
    3, 5, 7, 821, 3, 3, 43, 11,
    7, 3, 3, 3, 1297781, 131, 3, 13,
    11, 3, 3, 5, 3, 143213269, 9695327, 3,
    3, 5, 223, 17, 3, 3, 19, 3,
    29, 3, 73, 7, 3, 5, 3, 3,
    3, 5, 3, 11, 3, 47, 23, 5,
    7, 3, 3, 3, 11, 991, 3, 5,
    3, 31, 3, 5, 7, 3, 157, 11,
    3, 3, 19, 3, 3, 53, 3, 3,
    1009, 3, 71, 5, 3, 7, 3, 3,
    3, 3, 3, 3, 101, 3, 3, 5,
    33911, 3, 83, 3, 3, 5, 3, 862789,
    3, 1163, 5, 13, 23, 5, 3, 11,
    3, 103, 19, 3, 3, 525043829, 3, 109,
    3, 3, 7, 3, 503, 3, 13, 7,
    5, 3, 17, 3, 41, 5, 3, 97,
    3, 3, 5, 3, 7, 3, 3, 3,
    19, 11, 3, 7, 3, 84827, 3, 881,
    3, 67, 3, 3, 3, 13, 73, 3,
    4639, 47, 3, 3, 5, 23173, 3, 3,
    5, 3, 3, 17, 37, 5, 15551, 14831,
    3, 5, 7, 353, 3, 3, 11, 3,
    3, 5, 3, 11, 19, 3, 3, 79,
    5, 3, 11, 3, 5, 13332401, 3, 7,
    3, 19, 3, 3, 3, 13, 3, 3989,
    7, 3, 5, 3, 3, 113, 3, 5,
    3, 61, 3, 19, 2953, 3, 3, 5,
    3, 29, 3, 41, 13, 3, 3, 5,
    23, 3, 59, 17, 7, 3, 283, 11,
    3, 1069, 631, 310361, 3, 13, 3, 5,
    3, 43, 3, 5, 3, 3, 3, 3,
    41, 173, 3, 7, 3, 11, 3, 29,
    3, 3, 3, 5, 7, 17, 3, 5,
    3, 5, 3, 31, 3, 3, 184969003, 3,
    3, 3, 3, 12377, 7, 3, 3, 19,
    107, 3, 5, 3, 13, 3, 113, 7,
    3, 54269, 3, 5, 3, 11, 3, 5,
    3, 3, 3, 79, 3, 11, 7, 3,
    3, 331, 3, 3, 5, 3, 149, 3,
    3, 17, 7, 3, 3, 3, 14221, 5,
    3, 317, 3, 3, 5, 3, 17, 3,
    3, 3, 5, 8592509, 3, 13, 3, 11,
    19, 5, 3, 7, 3, 5, 3, 11,
    3, 5, 3, 3, 5, 7, 3, 17,
    11, 3, 3, 152909, 3, 101987, 5, 3,
    3123773, 13, 738285727, 3, 3, 367, 3, 3,
    151, 827, 5, 3, 3, 3, 7, 3,
    1327, 22769, 3, 1113083, 3, 3, 3, 5,
    61, 3, 17, 3, 5, 3, 7, 11,
    3, 5, 3, 67, 1231, 3, 3, 7,
    3, 643, 3, 3, 19, 5, 23, 14887,
    5, 3, 3, 3, 5, 11, 7, 5,
    3, 9826813, 3, 3, 229, 3, 11, 7,
    3, 3, 3, 61, 3, 3, 3, 3,
    13, 3, 107, 11321, 3, 3, 3, 7,
    337, 5, 233, 5, 3, 3, 29, 5,
    3, 3, 11, 3, 13, 7, 3, 3,
    101, 3, 3, 5, 47, 9769, 3, 3,
    11, 5, 3, 73, 17, 3, 3, 7,
    3, 197, 3, 3, 3, 541, 7, 3,
    5, 3, 97, 5, 3, 3, 5, 23,
    20507, 3, 3, 3, 3, 17, 57187909, 3,
    5, 3, 8893, 3, 3, 3, 5, 3,
    14449, 5, 109, 31849, 3, 41, 7, 127,
    3, 83, 3, 5, 5, 7, 4373, 19,
    3, 3, 13, 3, 3, 3, 5, 3,
    3, 5, 179233, 3, 53, 5, 3, 37,
    263, 3, 3, 5, 3, 3, 3, 13,
    3, 5, 3, 7, 3, 3, 5, 3,
    17, 3, 202973, 3, 3, 311, 3, 5,
    167, 3, 5, 3, 3, 3, 25367, 3,
    5, 7, 73, 3, 3, 3, 11, 7,
    3, 3, 5, 3757861, 3, 531763957, 3, 79,
    677, 3, 107, 191, 3, 5, 1051, 3,
    5, 101, 3, 3, 31, 23, 3, 3,
    3, 516275833, 3, 5, 295219, 3, 5, 3,
    7, 3, 3, 11, 13, 3, 97, 3,
    3, 5, 3, 3, 7789, 479239093, 7, 3,
    3, 47, 29, 3, 5, 82469, 157, 23,
    3, 3, 7, 121453, 3, 3, 3, 3,
    172787, 3, 3, 3, 449, 3, 3, 17,
    3, 5, 5, 3, 3, 5, 3, 7,
    11, 3, 3, 5, 523, 3, 3, 3,
    19, 257, 3, 3, 3, 7, 3, 5,
    3, 3, 167, 3, 211, 5, 3, 17,
    3, 5, 3, 8945617, 3, 83, 3, 11,
    3, 7, 719, 571, 3, 3, 7, 3,
    5, 103, 5107, 3, 42967, 3, 3, 5,
    13, 7, 3, 3, 5, 3623, 23, 3,
    3, 8597, 3, 3, 40013, 389, 7, 5,
    73, 3, 5, 3, 3, 17, 7, 3,
    5, 3, 3, 11, 3, 3, 71, 460626071,
    37, 3, 89, 3, 3, 5, 3, 31,
    3, 3, 3, 3, 3, 23, 5, 46507,
    3, 3, 5, 7, 3, 59, 3, 29,
    13, 7, 3, 5, 102571577, 3, 11, 3,
    3]

theorem prime_sub_7577 : Nat.Prime (558619547569907716 - 7577) := by
  show Nat.Prime 558619547569900139
  exact p558619547569900139

theorem check_7577 : allC 558619547569907716 7577 P10k ds_7577 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 558619547569907716 is 7577. -/
theorem minGB_S_7577 : minGB 558619547569907716 = 7577 :=
  minGB_eq_of P10k P10k_complete 558619547569907716 7577 (by norm_num) (by norm_num) prime_sub_7577 ds_7577 check_7577

def ds_7649 : List ℕ := [
    2, 5, 2203, 3, 10909, 3, 11, 3,
    5, 7, 3, 3, 19, 3, 97, 5,
    13, 3, 3, 7, 3, 3, 5, 351457,
    3, 83, 3, 641, 3, 5, 3, 29,
    13, 3, 11, 3, 3, 3, 17, 5,
    595981, 3, 37810103, 3, 7, 3, 3, 3,
    31, 3, 5, 7, 3, 10817299, 8389, 5,
    17, 3, 3, 7, 3, 5, 3, 131,
    3, 109, 3, 3, 11, 3, 5, 53,
    3, 3, 3, 5, 227, 3, 199, 3,
    223, 3, 353, 3, 3, 5, 7, 3,
    470863, 3, 6337, 11, 3, 7, 3, 5,
    443, 36013, 3, 3, 3, 263, 5, 191,
    3, 3, 1009, 5, 31, 3, 3, 3,
    7, 3, 3, 170540609, 3, 47, 5, 7,
    3, 3, 11, 5, 3, 7, 3, 37,
    3, 3, 3, 5, 3, 3, 13, 3,
    5, 3, 1091, 11, 3, 677, 3, 7,
    3, 13, 3, 139, 3, 5, 3, 17,
    3, 181, 3, 7, 3, 47, 3, 11,
    997, 5, 3, 31, 59, 5, 3, 3,
    3, 5, 109012303, 3, 73, 3, 3, 163,
    3, 1481, 3, 3, 3, 12671, 3, 83,
    5, 751, 3, 3, 3, 13, 3, 5,
    3, 19, 17, 5, 3, 3, 449, 5,
    13, 3, 3, 3, 577, 11393, 3, 5,
    7, 3, 3, 967, 3, 13, 257, 3,
    3, 2712431, 499, 5, 3, 3, 19, 3,
    293, 3, 5, 461, 3, 23, 3, 3,
    3, 1163, 3, 521, 3, 5, 7, 43,
    5, 3, 3, 3, 5, 89, 3, 1489,
    3, 5, 3, 11, 37, 3, 5, 13,
    3, 3, 19, 3, 3, 7, 3, 3,
    13, 3, 7, 439, 3, 5, 3, 3,
    3, 3, 3, 3, 79, 3, 3, 26351933,
    5, 3, 4211, 3, 3, 29, 3, 7,
    3, 113, 17, 73, 5, 11, 3, 53,
    3, 5, 19, 3, 3, 11, 3, 5,
    3, 3, 43, 3, 59, 3, 5, 127,
    3463, 3, 7, 3, 233, 77899, 3, 7,
    3, 3, 23, 3, 5, 3, 3, 3,
    17, 5, 3, 863, 3, 5, 3, 41,
    3, 5, 3, 3, 3, 7, 17, 3,
    5, 7, 3, 3, 52511, 67, 3, 3,
    7, 3, 3, 5, 13, 17, 23, 5,
    3, 1609, 421, 11, 3, 3, 13, 3,
    3, 1759, 3, 5, 7, 3, 3, 6526057,
    7, 3, 107, 3, 47, 5, 3, 11,
    3, 5, 3, 3, 3, 4409, 3, 5,
    3877, 3, 13, 3, 3, 619, 3, 29,
    3, 5, 3, 19, 11, 3, 3, 7,
    3, 17, 3, 103, 5, 3, 3, 191,
    11520617, 3, 128092793, 5, 703463, 3, 7, 37,
    3, 97, 5, 7, 3, 1087, 3, 7,
    3, 5, 3, 54419, 3, 3, 3, 3,
    5, 29, 3, 11, 3, 7, 3, 443,
    3, 3, 3, 32831347, 5, 79, 3, 7,
    3, 11, 3, 13, 3, 3, 941, 3,
    3, 3, 3, 5, 17, 3, 3, 7,
    139, 3, 472051, 3, 7, 3, 3547, 5,
    3, 11, 3, 19, 3, 47, 3, 13,
    3, 3, 3, 99349, 3, 5, 53, 3,
    3, 7, 3, 3, 11, 3, 5, 3,
    3, 52147, 5, 3, 3, 3, 23, 1377457,
    3, 1103, 3, 3, 487, 3, 149, 3,
    3, 3, 31, 7, 3, 11, 3, 23,
    5, 224563, 3, 5, 3, 7, 3, 5,
    3, 13, 3, 3, 11, 19, 3, 5,
    646747267, 3, 3, 31, 3, 41, 344423, 3,
    191, 5, 7, 3, 3, 37, 3, 3,
    5, 10465603, 43, 3, 3, 3, 11839, 3,
    5, 11177, 3, 79, 3, 3, 3, 23,
    977, 3, 7, 3, 11, 3, 5, 19,
    3, 7, 3, 5, 34483, 3, 3, 227123683,
    3, 13, 3, 3, 5, 36265067, 7, 3250831,
    709, 3, 3, 3, 17, 379, 5, 7,
    3, 5, 3, 3, 59, 3, 5, 431,
    3, 3, 3, 5, 3, 3, 3, 3,
    11, 3, 5, 7, 3, 3, 3, 5,
    1427, 7, 5, 367, 3, 3, 5, 71,
    3, 3, 179, 3, 5, 1373, 3, 3,
    7, 3, 3, 59, 31, 20297, 3, 3,
    256689473, 700948463, 3, 37, 5, 3, 3, 11,
    3, 5, 3, 3, 3, 5, 7109, 3,
    7972189, 3, 23, 13, 3, 3, 83, 140817577,
    11, 3, 3, 3, 3, 1531, 5, 3,
    19, 3, 2221, 3, 3, 3, 11, 3,
    7, 176357, 5, 7, 3, 11, 5, 103,
    3, 5, 3, 29, 37, 2423, 5, 19,
    3, 3, 14327, 3, 3, 3, 13, 3,
    3, 17, 1097, 3, 5, 29173, 3, 101,
    13, 3, 3, 7, 3, 3, 3, 5,
    3, 23, 3, 43, 3, 3, 157813, 3,
    7, 3, 174527, 3, 3, 5, 3, 41,
    272381, 3, 7, 3, 3, 3, 5, 3,
    1174549, 31, 5, 3, 3, 3, 5, 73,
    3, 3, 139, 7, 3, 17, 3, 43,
    5, 3, 103, 61, 3, 17, 13, 3,
    887, 71, 3, 3, 29, 5, 3, 3,
    3, 11, 3, 363841, 5, 3, 13609963, 3,
    5, 3, 3, 5, 19, 3, 5, 3,
    3, 11, 3, 3, 24359, 5, 37, 3,
    3, 7, 13, 3, 19, 181, 5, 7,
    3, 3, 5, 3809719, 3, 3, 3, 3,
    17, 3, 3, 3, 41, 3, 3, 5,
    3, 17, 493621, 3, 3, 11, 3, 5,
    29, 3, 3, 7, 131, 3, 3, 3,
    5, 79811, 3, 3, 3, 13, 3, 293,
    3, 3, 53, 3, 31, 713753, 3, 67,
    3, 7, 3, 5, 3, 180352937, 3, 5,
    3, 109, 5, 263, 3, 3, 17, 3,
    6047, 7, 11, 3, 7, 3, 3, 23,
    654679, 5, 3, 3, 7, 5, 16358201, 3,
    3, 5, 3, 3, 11, 5, 19, 673,
    7, 3, 3491, 3, 3, 41, 5, 3,
    7, 3, 3, 99233, 3, 3, 23, 5,
    5, 3, 17, 3, 3, 95072311, 3, 59,
    3, 3, 3, 3, 3, 5, 19, 5343529,
    3, 3, 31, 229, 3, 271, 3, 2658067,
    5, 139, 3, 11, 7, 3, 10559, 3,
    3, 579353, 5, 7, 3, 3, 11, 3,
    3, 5]

theorem prime_sub_7649 : Nat.Prime (754276228832957188 - 7649) := by
  show Nat.Prime 754276228832949539
  exact p754276228832949539

theorem check_7649 : allC 754276228832957188 7649 P10k ds_7649 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 754276228832957188 is 7649. -/
theorem minGB_S_7649 : minGB 754276228832957188 = 7649 :=
  minGB_eq_of P10k P10k_complete 754276228832957188 7649 (by norm_num) (by norm_num) prime_sub_7649 ds_7649 check_7649

def ds_7691 : List ℕ := [
    2, 11, 349, 3, 47, 3, 947, 3,
    7, 5, 3, 3, 53, 3, 11, 321469,
    5, 3, 3, 179, 3, 3, 397, 5,
    3, 43, 3, 7, 3, 11, 3, 17,
    83, 3, 5, 3, 3, 3, 21727, 19,
    5, 3, 7, 3, 17467, 3, 3, 3,
    73, 3, 7, 5, 3, 4813, 593, 13,
    5, 3, 3, 89657, 3, 47, 3, 11,
    3, 7, 3, 3, 79, 3, 308467, 5,
    3, 3, 3, 52967, 5, 3, 7, 3,
    5, 3, 181, 3, 3, 7, 5, 3,
    23, 3, 89, 5, 3, 29, 3, 109,
    5, 31, 3, 3, 3, 12329, 797, 5,
    3, 3, 56929, 283, 5, 3, 3, 3,
    43, 3, 3, 11, 3, 2389, 7, 5,
    3, 3, 53, 197, 3, 152519, 3, 5,
    3, 3, 3, 17, 3, 3, 607, 3,
    11, 3, 1481, 5, 3, 7, 3, 233,
    3, 5, 3, 19, 3, 7, 3, 67,
    3, 13, 3, 103, 3, 5, 3, 541,
    7, 823, 3, 11, 37, 4931, 3, 3,
    3, 23, 5, 3, 7, 3, 3, 5,
    3, 127, 3, 3, 3, 22153, 3, 41,
    11, 5, 3, 3, 3, 17, 3, 107,
    3, 941, 29, 637515397, 3, 3, 1171, 271,
    5, 3, 3, 3, 5, 13, 3, 7,
    5, 3, 3, 11, 3, 7603, 5, 3,
    3, 29, 7, 4177, 3, 3, 5, 3,
    19, 3, 11, 5, 3, 7, 3, 3,
    3, 2459, 3, 44207, 3, 7, 5, 13,
    2441, 3, 3, 3, 3602773, 5, 3, 647,
    3, 257, 3, 14867, 322407457, 3, 2067799, 5,
    3, 3, 31, 3, 3, 13, 3, 3,
    11, 3, 5, 30464717, 3, 113, 3, 3,
    3, 3, 3, 3, 7, 3, 3, 109,
    13, 3, 739, 3, 3, 7, 3, 95003,
    3, 5, 13, 43, 7, 3347, 3, 5,
    3, 719, 5, 3, 3, 7, 3, 61,
    3, 3, 11, 3, 5, 3, 1613, 5,
    7, 3, 37, 3, 5, 19, 3, 5,
    3, 3, 937, 3, 2731, 3, 3, 3,
    7, 13, 3, 2713, 3, 79, 3, 47,
    3, 17, 3, 3, 3, 443, 5, 3,
    7, 5, 3, 3, 199, 11, 3, 3,
    31, 3, 3, 23, 5, 59, 7, 11,
    3, 167, 13, 5, 3, 3, 17, 3,
    3, 23, 3, 7, 5, 3, 3, 5,
    146513, 3, 5, 3, 11, 20507, 3, 39509,
    3, 425250367, 3, 3, 3, 11, 3, 883,
    5, 3, 7, 3, 3, 5, 3, 178039,
    3, 7, 3, 8231, 5, 3, 3, 97,
    3, 5, 3, 7, 33107, 3, 3, 4812527,
    5, 3, 15289, 53, 5, 3, 29, 5,
    3, 293, 7, 5, 3, 5, 3, 643,
    3, 19, 3, 60292481, 3, 3, 3, 3,
    11, 5, 3, 5, 3, 19, 3, 1489,
    3, 3, 3, 17, 12357869, 5, 3, 23,
    3, 19, 3, 7, 3, 3, 5, 3,
    3, 3, 3, 9887, 5, 3, 3, 11,
    5, 3, 84802337, 3, 5, 3, 163, 11,
    3, 5, 3, 13, 3, 7, 3, 727,
    3, 3, 3, 7753, 3, 71, 5, 3,
    3, 41, 3, 3, 337, 3, 7, 3,
    3, 13, 29, 3, 3, 3, 5, 89,
    3, 7, 3, 3, 17, 3, 5, 3,
    3, 3, 7, 113, 3, 5, 3, 29,
    7, 19, 3, 61, 3, 13, 3, 37,
    3, 9701821, 3, 3, 23, 3433, 3, 151,
    5, 3, 3, 23887, 3, 5, 103, 3,
    11, 7, 5, 3, 3, 5, 3, 3,
    11, 5, 446909, 3, 3, 3, 613, 3,
    193, 5, 3, 28603, 3, 3, 3, 17,
    227, 3, 5, 3, 13, 3, 467, 5,
    3, 11, 3, 173, 5, 3, 3, 11,
    3, 5, 3, 3, 107, 7, 13, 5,
    811273, 3, 3, 3, 3259, 209089, 23, 4657,
    3, 29, 3, 3, 7, 3, 47, 97,
    3, 3, 3, 157, 3, 3, 3, 3,
    131, 3, 7, 5, 3, 3, 3, 72043,
    5, 997, 6317, 17, 3, 3, 11, 37,
    3, 3, 13, 3, 891827, 5, 3, 3,
    1511, 3, 3, 127, 23, 5, 3, 3,
    5, 11, 3, 7, 13, 3, 3, 325309,
    3, 37, 3, 3, 3, 43, 5, 3,
    7, 3, 5, 3041, 3, 3, 109, 47,
    5, 3, 3, 3, 3, 7, 23, 3,
    31, 3, 5, 3, 3, 3, 7, 3,
    71, 11, 7, 5, 3, 61, 19, 5,
    3, 13, 3, 1058147, 16381, 571, 11, 5,
    3, 3, 19, 3, 3, 3, 7, 3,
    3, 44687081, 363199, 3, 7, 2803, 3, 43291,
    5, 3, 3, 19, 3, 3, 3, 16871,
    3, 11, 3, 5, 3, 3, 7, 3,
    11, 3, 5, 3, 3, 7, 3, 29,
    769, 3, 17, 3, 3, 3, 701731, 3,
    13, 89, 4161151, 3, 3, 3, 17, 5,
    3, 3, 7, 224177, 3, 5, 3, 1450103,
    7, 3, 2422477, 5, 3, 23, 7, 3,
    902821, 5, 3, 3, 17, 11, 3, 3,
    3, 5, 3, 19, 7, 3, 7559, 3,
    313, 3, 3, 1009, 7, 3, 2216057, 3,
    3, 12553, 3, 3, 23, 41, 5, 3,
    3, 31, 5, 3, 93893, 11, 7, 5,
    3, 3, 17, 5, 3, 3, 3, 3,
    5, 3, 3, 3, 5, 3, 3, 31,
    3, 7, 1871, 3, 3, 43, 3, 311,
    5, 3, 3, 11, 5, 3, 3, 3,
    80985241, 5, 3, 3, 3, 5, 3, 7,
    3, 3, 5, 3, 13, 17, 3, 5,
    3, 4003, 3, 787, 3, 7, 3, 137518243,
    3, 6971, 17, 5, 3, 3, 5, 3,
    7, 18947, 23, 3, 5, 3, 3, 13,
    11, 79, 3, 3, 41, 19, 5, 3,
    3, 11, 3, 3, 5, 29, 5, 7,
    13, 3, 8189579, 3, 3, 9085229, 37, 3,
    356761, 3, 3, 5, 3, 3, 7, 421,
    13, 3, 11, 3, 3, 7, 3, 5,
    3, 3, 3, 3, 3, 541, 29, 7,
    3, 3, 1033, 39246793, 3, 5, 3, 13,
    17599, 5, 3, 7, 151, 3, 5, 3,
    3, 17, 7, 5, 3, 3, 83, 3,
    3, 3391, 5, 3, 13, 3, 3]

theorem prime_sub_7691 : Nat.Prime (813695622192168004 - 7691) := by
  show Nat.Prime 813695622192160313
  exact p813695622192160313

theorem check_7691 : allC 813695622192168004 7691 P10k ds_7691 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 813695622192168004 is 7691. -/
theorem minGB_S_7691 : minGB 813695622192168004 = 7691 :=
  minGB_eq_of P10k P10k_complete 813695622192168004 7691 (by norm_num) (by norm_num) prime_sub_7691 ds_7691 check_7691

def ds_7703 : List ℕ := [
    2, 24029, 19, 3, 1523, 3, 5, 3,
    43, 11, 3, 3, 7, 3, 5, 29,
    1489, 3, 3, 23, 3, 3, 7, 97,
    3, 17, 3, 5, 3, 13, 3, 5011,
    5, 3, 44269, 3, 3, 3, 5, 67,
    2239, 3, 13, 3, 5, 3, 3, 3,
    5, 3, 19, 107, 3, 7, 5, 41,
    13, 3, 3, 43, 3, 7, 3, 853,
    3, 5, 3, 3, 5, 3, 3336547, 11,
    3, 3, 3, 550833289, 79, 3, 29, 3,
    7, 3, 1069, 3, 3, 1307689, 313, 3,
    7, 3, 5, 123667, 3, 11, 3, 7,
    17, 89, 3, 3, 3, 5, 2393, 739,
    3, 3, 5, 83, 31, 3, 3, 3,
    5, 3, 3, 22901, 3, 5, 218143, 13,
    3, 3, 5, 257, 3, 61, 3, 1231,
    3, 3, 3, 1061, 3, 3, 23, 3,
    53, 3, 5, 13093, 3, 11, 3, 5,
    3, 7, 3, 5, 3, 79, 3, 7,
    3, 5, 3, 8599, 3, 211, 3, 59,
    5, 11, 3, 13, 5, 3169, 3, 3,
    3, 337, 11, 3, 19, 3, 3, 7,
    3, 3001, 3, 3, 3, 7, 3, 5,
    361531, 80233, 3, 3, 3, 11, 3, 1182763,
    3, 3203, 5, 1348247, 3, 3, 5, 17,
    71, 3, 3, 3, 7, 5, 3, 11,
    1088034043, 3, 3, 7, 3, 5, 556988791, 3,
    3, 13, 5, 19, 3, 3, 53, 3,
    5, 3, 37, 13, 3, 23, 3, 3,
    3, 11, 3, 5, 3, 41, 173, 7,
    107, 3, 3, 3, 7, 8363, 3, 43,
    3, 941, 3, 19, 5, 3, 11, 29,
    3, 3, 5, 3, 3, 5, 3, 3,
    5, 3, 151, 7, 3, 17, 3, 3,
    3, 3, 3, 3, 5, 3, 3, 11,
    37478117, 3, 5, 3, 3, 56857, 3, 5,
    3, 7, 31, 5, 73, 7, 3, 127,
    3, 7, 5099, 3, 3, 5, 3, 23,
    3, 3, 5, 3, 17, 3, 13, 10313,
    71, 3, 5, 3, 7, 6133, 3, 46170743,
    3, 3, 7, 3, 115312867, 3, 3, 3,
    5, 439, 3, 5, 3, 17, 3, 5,
    3, 11, 3, 3, 3, 5, 7, 3,
    117415189, 11, 3, 3, 7, 5, 3, 3,
    3613, 3, 3, 7, 19, 2131, 5, 859,
    3, 5827, 5, 31, 3, 3, 5, 3,
    3, 13, 3, 37, 17, 3, 3, 6781,
    11149, 3, 13, 3, 17582483, 6857, 3, 5,
    3, 29, 3, 3, 3, 5, 3, 23,
    757, 3, 59, 3, 3, 7, 3, 19,
    3, 17, 3, 5, 47, 3, 3, 11,
    3, 541, 3, 5, 13, 3, 3, 43,
    181, 3, 5, 163, 7121, 3, 5, 7,
    3, 5, 761, 19, 3, 11, 3, 29,
    3, 7, 3, 4283, 3, 3, 3, 3,
    19, 653, 3, 43, 3, 5, 3, 5,
    3, 3, 3, 7, 31, 37, 3, 131,
    3, 965963, 3, 5, 3, 3, 641, 3,
    3, 3, 3, 1223, 11, 3, 3, 5,
    7, 3, 1332517, 3, 13, 3, 5, 16829,
    3, 107, 3, 11, 3, 5, 3, 23801,
    3, 3, 3, 5, 3, 29, 19, 3,
    3, 5, 3, 3, 83, 3, 11, 3,
    3, 5, 13, 3, 3, 3, 11, 17,
    3, 5, 3, 3, 13, 3, 33647, 3,
    3, 3, 31, 5, 3, 7, 3, 5,
    3602201, 7, 3, 491, 3, 101, 3, 7,
    3, 19, 3, 3, 3067, 5, 3, 11,
    139, 3, 3, 5, 3, 7, 109, 3,
    5, 13, 577, 3, 3, 7873, 3, 3,
    7, 17, 13, 3, 3, 3, 5, 3,
    31, 24877, 3, 5, 3, 3, 3, 23,
    5, 3, 29, 3, 7, 3, 11, 89,
    3, 53, 3, 7, 401, 3, 3, 5,
    3, 23, 3, 3, 66463, 281, 5, 7,
    29588743, 3, 3, 3, 7, 5, 2411, 13,
    3, 7, 3, 3, 5, 3, 1297, 5,
    3, 3, 3, 11, 3, 3, 3, 3,
    5, 3, 3331, 11, 3, 3, 3, 8531407,
    19, 17, 7, 197, 3, 3, 107, 29,
    3, 3, 5, 3, 13, 27617, 3, 3,
    5, 3, 3, 7, 5, 347, 3, 3,
    2380519, 37253, 3, 5, 277, 3, 3, 5,
    3, 1607, 3, 3, 3, 149, 599, 3,
    19, 3, 7, 181, 3, 3, 7, 5,
    17, 3, 3, 3, 3, 5, 6421, 3,
    25247, 3, 59, 3, 3, 3, 48003701, 3,
    5, 13, 29, 23227, 3, 5, 17, 11,
    3, 7, 3, 691, 50123, 5, 4507, 67,
    3, 3, 5, 3, 3, 3, 11, 3,
    3, 21701, 5, 3, 229, 7, 3, 5,
    848579, 3, 3, 1597, 3, 3, 3, 11,
    3, 19, 3, 11, 3, 3, 13, 3,
    5, 3, 7, 3, 3, 811, 3, 7,
    5, 3, 971692487, 3, 3, 3, 2372413, 3,
    67, 5, 17, 3, 3, 3, 7013, 157,
    3, 3, 53, 5, 3, 7, 3, 5,
    11, 3, 5, 353, 3, 15041041, 5, 3,
    49433, 9779513, 3, 3, 5, 129733, 3, 3,
    3, 7, 3, 11, 1385561, 3, 7, 3,
    23, 3, 3, 7, 5, 3, 67, 3,
    3, 17, 3, 3, 5, 857, 1361, 3,
    3, 5, 7, 3, 905189, 5, 17, 443,
    3, 3, 13, 63317, 3, 3, 3, 3,
    19, 3, 3, 3, 23819, 3, 3, 43,
    3, 29, 127, 3, 3, 7, 3, 11,
    83, 3, 3, 199, 80513, 3, 3, 3,
    2160833, 41, 3, 3, 3, 167, 3, 179,
    3, 3, 7, 3, 5, 7, 3, 491,
    3, 149, 3, 7, 3, 5, 3, 17,
    3, 5, 239, 571, 3, 3, 13, 3,
    39209, 5, 5, 3, 11, 3, 3, 7,
    5, 37, 3, 3, 134731, 7, 47, 3,
    3, 5749, 3, 3, 337, 103, 23, 112279,
    5, 3, 41, 3, 3, 5, 71, 3,
    13, 3, 3, 941, 3, 3, 5, 1709,
    127, 3, 5, 3, 3, 4219, 3, 7,
    3, 3, 3, 3, 3, 7, 53, 5,
    3, 3, 31, 5, 3, 79, 3, 5,
    13, 19, 3, 307, 5, 3, 7, 3,
    3, 5, 47, 1123, 3, 3, 5, 3,
    3, 7, 17, 3, 269, 3, 3, 167,
    3]

theorem prime_sub_7703 : Nat.Prime (1473611722331822212 - 7703) := by
  show Nat.Prime 1473611722331814509
  exact p1473611722331814509

theorem check_7703 : allC 1473611722331822212 7703 P10k ds_7703 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 1473611722331822212 is 7703. -/
theorem minGB_S_7703 : minGB 1473611722331822212 = 7703 :=
  minGB_eq_of P10k P10k_complete 1473611722331822212 7703 (by norm_num) (by norm_num) prime_sub_7703 ds_7703 check_7703

def ds_7853 : List ℕ := [
    2, 11, 1889, 3, 19, 3, 23, 3,
    43, 5, 3, 3, 557, 3, 11, 557779,
    5, 3, 3, 7, 3, 3, 53, 5,
    3, 41, 3, 6287, 3, 7, 3, 224234537,
    709, 3, 5, 3, 3, 3, 17, 777173,
    5, 3, 313, 3, 7, 3, 3, 3,
    223, 3, 13, 5, 3, 37, 83, 1069,
    5, 3, 3, 7, 3, 23, 3, 11,
    3, 349304551, 3, 3, 41, 3, 19, 5,
    3, 3, 3, 179, 5, 3, 53, 3,
    5, 3, 23, 3, 3, 11, 5, 3,
    353, 3, 13, 5, 3, 7, 3, 89,
    5, 229, 3, 3, 3, 393541, 18008597, 5,
    3, 3, 29, 41, 5, 3, 3, 3,
    7, 3, 3, 11, 3, 3797, 61, 5,
    3, 3, 17, 1181289169, 3, 7, 3, 5,
    3, 3, 3, 7, 3, 3, 29, 3,
    11, 3, 43, 5, 3, 541, 3, 7,
    3, 5, 3, 13, 3, 3737633, 3, 17,
    3, 173, 3, 7, 3, 5, 3, 673,
    78787, 7, 3, 11, 73, 17, 3, 3,
    3, 13, 5, 3, 97, 3, 3, 5,
    3, 59, 3, 3, 3, 13, 3, 2131,
    11, 5, 3, 3, 3, 19, 3, 7,
    3, 191, 17, 883, 3, 3, 4127, 13729,
    5, 3, 3, 3, 5, 71, 3, 29,
    5, 3, 3, 11, 3, 13454921, 5, 3,
    3, 37, 11, 7, 3, 3, 5, 3,
    19577, 3, 11, 5, 3, 1063973, 3, 3,
    3, 13, 3, 839, 3, 17, 5, 131,
    9380633, 3, 3, 3, 397, 5, 3, 43,
    3, 7, 3, 31, 19, 3, 97, 5,
    3, 3, 13, 3, 3, 7, 3, 3,
    11, 3, 5, 19, 3, 227, 3, 3,
    3, 3, 3, 3, 31, 3, 3, 23,
    41, 3, 163, 3, 3, 13, 3, 7,
    3, 5, 17, 3181, 233, 4523, 3, 5,
    3, 31, 5, 3, 3, 6563, 3, 7,
    3, 3, 11, 3, 5, 3, 19, 5,
    599, 3, 7, 3, 5, 151, 3, 5,
    3, 3, 42589, 3, 29, 3, 3, 3,
    17, 7, 3, 244058651, 3, 827, 3, 76001,
    3, 149, 3, 3, 3, 7, 5, 3,
    109, 5, 3, 3, 8761, 11, 3, 3,
    7, 3, 3, 211, 5, 17, 13, 7,
    3, 67, 17419, 5, 3, 3, 59, 3,
    3, 31, 3, 2068501, 5, 3, 3, 5,
    7, 3, 5, 3, 11, 7, 3, 4415207,
    3, 6577, 3, 3, 3, 11, 3, 37,
    5, 3, 304336379, 3, 3, 5, 3, 359,
    3, 11, 3, 23, 5, 3, 3, 7,
    3, 5, 3, 28759, 7, 3, 3, 19,
    5, 3, 6521, 31, 5, 3, 7, 5,
    3, 277, 13, 5, 3, 5, 3, 7,
    3, 17, 3, 13, 3, 3, 3, 3,
    11, 5, 3, 5, 3, 7, 3, 73,
    3, 3, 3, 23, 19, 5, 3, 7,
    3, 16937, 3, 857, 3, 3, 5, 3,
    3, 3, 3, 145803979, 5, 3, 3, 7,
    5, 3, 29, 3, 5, 3, 71, 11,
    3, 5, 3, 31, 3, 23, 3, 1367,
    3, 3, 3, 127, 3, 17, 5, 3,
    3, 7, 3, 3, 37, 3, 1877, 3,
    3, 293, 114745139, 3, 3, 3, 5, 443,
    3, 11, 3, 3, 70913, 3, 5, 3,
    3, 3, 134003579, 7, 3, 5, 3, 103,
    37, 13, 3, 31, 3, 7, 3, 107,
    3, 23, 3, 3, 5009, 8353, 3, 151,
    5, 3, 3, 61, 3, 5, 19, 3,
    11, 58091977, 5, 3, 3, 5, 3, 3,
    11, 5, 5689, 3, 3, 3, 1709, 3,
    13, 5, 3, 23, 3, 3, 3, 13,
    53, 3, 5, 3, 29, 3, 271, 5,
    3, 7, 3, 41, 5, 3, 3, 11,
    3, 5, 3, 3, 10651, 31, 7, 5,
    257, 3, 3, 3, 17, 19, 79, 7,
    3, 1250551, 3, 3, 15307, 3, 7, 1741,
    3, 3, 3, 877, 3, 3, 3, 3,
    139, 3, 229, 5, 3, 3, 3, 242197279,
    5, 7, 627960511, 941, 3, 3, 7, 2423,
    3, 3, 859, 3, 15919, 5, 3, 3,
    7, 3, 3, 463, 7013, 5, 3, 3,
    5, 11, 3, 29, 7, 3, 3, 3011,
    3, 167, 3, 3, 3, 5003, 5, 3,
    41, 3, 5, 127, 3, 3, 431, 373,
    5, 3, 3, 3, 3, 13, 7, 3,
    53, 3, 5, 3, 3, 3, 467, 3,
    7, 11, 1193, 5, 3, 22639, 13, 5,
    3, 789977, 3, 571, 13, 47, 11, 5,
    3, 3, 101, 3, 3, 3, 43, 3,
    3, 17, 263, 3, 19, 175039441, 3, 31,
    5, 3, 3, 7, 3, 3, 3, 7,
    3, 11, 3, 5, 3, 3, 103, 3,
    7, 3, 5, 3, 3, 13, 3, 19,
    137519, 3, 7, 3, 3, 3, 7, 3,
    37, 29, 23, 3, 3, 3, 89, 5,
    3, 3, 3313, 7, 3, 5, 3, 31033,
    518214007, 3, 13, 5, 3, 17, 11, 3,
    7867, 5, 3, 3, 1511, 11, 3, 3,
    3, 5, 3, 3229, 67489, 3, 199, 3,
    61, 3, 3, 421, 217979, 3, 7, 3,
    3, 16759, 3, 3, 109, 9413, 5, 3,
    3, 7, 5, 3, 457, 11, 653, 5,
    3, 3, 409, 5, 3, 3, 3, 3,
    5, 3, 3, 3, 5, 3, 3, 13,
    3, 17, 839, 3, 3, 13, 3, 2017,
    5, 3, 3, 7, 5, 3, 3, 3,
    8363, 5, 3, 3, 3, 5, 3, 3291667,
    3, 3, 5, 3, 19, 53, 3, 5,
    3, 7, 3, 4817, 3, 179, 3, 7,
    3, 281, 13, 5, 3, 3, 5, 3,
    11, 7, 4479919, 3, 5, 3, 3, 1107734981,
    11, 1471, 3, 3, 7, 131, 5, 3,
    3, 7, 3, 3, 5, 17, 5, 123479,
    7, 3, 307, 3, 3, 2512597, 19, 3,
    7, 3, 3, 5, 3, 3, 43, 7,
    2293, 3, 11, 3, 3, 13, 3, 5,
    3, 3, 3, 3, 3, 59, 1487, 211,
    3, 3, 41, 13, 3, 5, 3, 73369,
    154621, 5, 3, 347, 7, 3, 5, 3,
    3, 37, 5328119, 5, 3, 3, 23, 3,
    3, 13, 5, 3, 7, 3, 3, 23910659,
    3, 11, 3, 3, 41, 3, 3, 7,
    3, 3, 129449, 17, 22543, 5, 7]

theorem prime_sub_7853 : Nat.Prime (1599566025914318344 - 7853) := by
  show Nat.Prime 1599566025914310491
  exact p1599566025914310491

theorem check_7853 : allC 1599566025914318344 7853 P10k ds_7853 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 1599566025914318344 is 7853. -/
theorem minGB_S_7853 : minGB 1599566025914318344 = 7853 :=
  minGB_eq_of P10k P10k_complete 1599566025914318344 7853 (by norm_num) (by norm_num) prime_sub_7853 ds_7853 check_7853

def ds_7949 : List ℕ := [
    2, 366103, 11, 3, 5, 3, 832607, 3,
    7, 19, 3, 3, 5, 3, 1069, 2267,
    13, 3, 3, 5, 3, 3, 277, 1879,
    3, 5, 3, 7, 3, 139, 3, 5,
    11, 3, 7, 3, 3, 3, 381333653, 5171,
    2802929, 3, 5, 3, 257, 3, 3, 3,
    25127, 3, 7, 79, 3, 5, 19, 6703,
    11, 3, 3, 5, 3, 13, 3, 5,
    3, 7, 3, 3, 17, 3, 23, 7,
    3, 3, 3, 1672421, 239, 3, 5, 3,
    271, 3, 5, 3, 3, 7, 13, 3,
    5, 3, 11, 1709, 3, 5, 3, 97,
    37, 5, 3, 3, 3, 137, 1249, 7,
    3, 3, 859, 181, 11, 3, 3, 3,
    7669, 3, 3, 5, 3, 293, 7, 61,
    3, 3, 479, 13, 3, 5, 3, 1933,
    3, 3, 3, 1741, 3, 3, 5, 3,
    2467, 3, 11, 43, 3, 5, 3, 19,
    3, 13, 3, 17, 3, 7, 3, 5,
    3, 31, 3, 5, 3, 11, 3, 5,
    7, 37, 3, 5, 1427, 73, 3, 3,
    3, 41, 29, 3, 5, 3, 3, 101233967,
    3, 5, 3, 3, 3, 5, 3, 51263,
    103, 30367, 3, 3, 3, 5, 3, 17,
    3, 5, 79, 11, 3, 3, 53608801, 1453,
    13, 3, 3, 3, 11, 59, 3, 7,
    443, 3, 3, 5, 3, 13, 23, 3,
    3, 5, 7, 71, 3, 3, 7, 3,
    686729, 3, 311, 19543, 3, 5, 3, 3,
    3, 5, 3, 6521, 3, 7, 107, 5,
    11, 3, 3, 3, 67, 1171, 3, 5,
    3, 43, 3, 5, 123366821, 3, 461, 7,
    3, 3, 113, 3, 3, 97, 3, 3,
    13, 3, 1364351, 5, 3, 23, 3, 3,
    3, 3, 3, 3, 7, 3, 3, 5,
    239, 3, 6133, 3, 3, 5, 3, 17,
    3, 29, 5, 229, 7, 5, 3, 7523,
    3, 280532089, 17, 3, 3, 7, 3, 31,
    3, 3, 79039, 3, 7, 3, 29, 835391,
    5, 3, 13, 3, 43, 5, 3, 53,
    3, 3, 5, 3, 199, 3, 3, 3,
    7, 337, 3, 29, 3, 13, 3, 47,
    3, 17155529, 3, 3, 3, 73, 19, 3,
    7, 59, 3, 3, 5, 43, 3, 3,
    5, 3, 3, 419, 13, 5, 7, 19,
    3, 5, 11, 7, 3, 3, 13, 3,
    3, 5, 3, 7, 47, 3, 3, 11,
    5, 3, 79, 3, 5, 13, 3, 6211,
    3, 919, 3, 3, 3, 1637, 3, 17,
    23, 3, 5, 3, 3, 37, 3, 5,
    3, 7, 3, 11, 13, 3, 3, 5,
    3, 3083, 3, 7, 11, 3, 3, 5,
    7, 3, 17, 373, 11, 3, 331, 83,
    3, 89, 7, 1376923, 3, 17, 3, 5,
    3, 13, 3, 5, 3, 3, 3, 3,
    53, 7, 3, 31, 3, 104281, 3, 38113,
    3, 3, 3, 5, 17, 119993243, 3, 5,
    3, 5, 3, 7, 3, 3, 7, 3,
    3, 3, 3, 557, 227, 3, 3, 199,
    163, 3, 5, 3, 23, 3, 17, 13,
    3, 19, 3, 5, 3, 7, 3, 5,
    3, 3, 3, 23, 3, 111731, 2689, 3,
    3, 79, 3, 3, 5, 3, 7, 3,
    3, 37, 211, 3, 3, 3, 14549063, 5,
    3, 7, 3, 3, 5, 3, 7, 3,
    3, 3, 5, 11, 3, 1129, 3, 4635269,
    7, 5, 3, 11, 3, 5, 3, 31,
    3, 5, 3, 3, 5, 17, 3, 85837,
    7, 3, 3, 443, 3, 507149, 5, 3,
    131, 7, 17, 3, 3, 31, 3, 3,
    26497, 23, 5, 3, 3, 3, 436625219, 3,
    19, 7, 3, 739, 3, 3, 3, 5,
    23, 3, 11, 3, 5, 3, 238476457, 367,
    3, 5, 3, 37, 3167, 3, 3, 163,
    3, 7, 3, 3, 99881, 5, 48866431, 149,
    5, 3, 3, 3, 5, 41, 59, 5,
    3, 11, 3, 3, 7, 3, 47, 9739,
    3, 3, 3, 13, 3, 3, 3, 3,
    1621, 3, 7, 74099, 3, 3, 3, 29,
    43, 5, 19, 5, 3, 3, 17, 5,
    3, 3, 12577, 3, 31, 1301, 3, 3,
    13, 3, 3, 5, 5348281, 11, 3, 3,
    191, 5, 3, 7, 5553083, 3, 3, 3910043,
    3, 13, 3, 3, 3, 167, 18301, 3,
    5, 3, 17, 5, 3, 3, 5, 11,
    5316709, 3, 3, 3, 3, 7, 11, 3,
    5, 3, 7, 3, 3, 3, 5, 3,
    17401, 5, 7, 1979, 3, 271, 149, 53,
    3, 263, 3, 5, 5, 19, 37, 7,
    3, 3, 11, 3, 3, 3, 5, 3,
    3, 5, 9689, 3, 7, 5, 3, 691,
    13, 3, 3, 5, 3, 3, 3, 67,
    3, 5, 3, 13873, 3, 3, 5, 3,
    8849, 3, 6011, 3, 3, 7, 3, 5,
    29, 3, 5, 3, 3, 3, 61, 3,
    5, 4139, 11, 3, 3, 3, 19, 877,
    3, 3, 5, 11927483, 3, 11, 3, 3863,
    7, 3, 79, 409, 3, 5, 7, 3,
    5, 7, 3, 3, 103, 227, 3, 3,
    3, 2333, 3, 5, 7, 3, 5, 3,
    11, 3, 3, 151, 7, 3, 15473, 3,
    3, 5, 3, 3, 337, 17, 18049, 3,
    3, 23, 13, 3, 5, 16229, 7, 757,
    3, 3, 96731, 16879, 3, 3, 3, 3,
    314267, 3, 3, 3, 7, 3, 3, 11,
    3, 5, 5, 3, 3, 5, 3, 23,
    17, 3, 3, 5, 1237231, 3, 3, 3,
    31, 7, 3, 3, 3, 13, 3, 5,
    3, 3, 31121, 3, 11, 5, 3, 47,
    3, 5, 3, 11, 3, 7, 3, 6355879,
    3, 1223, 223129079, 7, 3, 3, 53, 3,
    5, 41, 37, 3, 14461, 3, 3, 5,
    17, 19, 3, 3, 5, 1429, 223, 3,
    3, 17377, 3, 3, 7, 677, 29, 5,
    313, 3, 5, 3, 3, 457, 547, 3,
    5, 3, 3, 89, 3, 3, 7, 23,
    17, 3, 347, 3, 3, 5, 3, 79,
    3, 3, 3, 3, 3, 17839, 5, 7,
    3, 3, 5, 17, 3, 7, 3, 43,
    16747, 11, 3, 5, 13, 3, 239, 3,
    3, 17331163, 7, 17, 3, 3, 8845387, 3,
    3, 234331, 59, 3, 314024177, 3, 3, 5,
    3, 13, 3, 3, 11, 3, 3, 269,
    3, 3, 7, 7056463, 79, 251, 5, 53,
    3, 3, 7, 3, 195733, 5, 47, 7,
    3, 3, 13]

theorem prime_sub_7949 : Nat.Prime (1793167785904803016 - 7949) := by
  show Nat.Prime 1793167785904795067
  exact p1793167785904795067

theorem check_7949 : allC 1793167785904803016 7949 P10k ds_7949 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 1793167785904803016 is 7949. -/
theorem minGB_S_7949 : minGB 1793167785904803016 = 7949 :=
  minGB_eq_of P10k P10k_complete 1793167785904803016 7949 (by norm_num) (by norm_num) prime_sub_7949 ds_7949 check_7949

def ds_8039 : List ℕ := [
    2, 5, 7, 3, 13, 3, 1229, 3,
    5, 167, 3, 3, 59, 3, 7, 5,
    6421, 3, 3, 17, 3, 3, 5, 7,
    3, 1291, 3, 135007, 3, 5, 3, 7,
    467, 3, 23, 3, 3, 3, 13, 5,
    313, 3, 157, 3, 11, 3, 3, 3,
    61, 3, 5, 19, 3, 379, 7, 5,
    3709, 3, 3, 83, 3, 5, 3, 2049407,
    3, 911, 3, 3, 1572547, 3, 5, 127,
    3, 3, 3, 5, 351301, 3, 13, 3,
    269, 3, 2839939, 3, 3, 5, 33331, 3,
    11, 3, 7, 13, 3, 38693, 3, 5,
    7, 7591, 3, 3, 3, 13, 5, 101264659,
    3, 3, 1553, 5, 43801, 3, 3, 3,
    2935109, 3, 3, 66919, 3, 67, 5, 11,
    3, 3, 7, 5, 3, 23, 3, 7,
    3, 3, 3, 5, 3, 3, 7, 3,
    5, 3, 375898763, 19, 3, 73, 3, 71,
    3, 23, 3, 11, 3, 5, 3, 487,
    3, 7, 3, 37, 3, 7, 3, 443,
    13, 5, 3, 7, 23, 5, 3, 3,
    3, 5, 47, 3, 167, 3, 3, 67,
    3, 359, 3, 3, 3, 17, 3, 7,
    5, 2997233, 3, 3, 3, 19, 3, 5,
    3, 7, 11, 5, 3, 3, 31513, 5,
    35083, 3, 3, 3, 13, 83, 3, 5,
    21269, 3, 3, 47, 3, 7, 11, 3,
    3, 15671, 1279, 5, 3, 3, 282143, 3,
    41, 3, 5, 2069, 3, 11, 3, 3,
    3, 239, 3, 53, 3, 5, 17, 817297339,
    5, 3, 3, 3, 5, 7, 3, 13,
    3, 5, 3, 7, 19, 3, 5, 69011,
    3, 3, 9127, 3, 3, 23, 3, 3,
    73, 3, 31, 19, 3, 5, 3, 3,
    3, 3, 3, 3, 300239, 3, 3, 7,
    5, 3, 11, 3, 3, 198013, 3, 118369939,
    3, 103, 39863, 17, 5, 193, 3, 19,
    3, 5, 7, 3, 3, 2789, 3, 5,
    3, 3, 97, 3, 13, 3, 5, 131,
    23, 3, 109, 3, 1831, 11, 3, 15439,
    3, 3, 211968293, 3, 5, 3, 3, 3,
    43, 5, 3, 137, 3, 5, 3, 31,
    3, 5, 3, 3, 3, 162791, 11, 3,
    5, 15173, 3, 3, 13, 7, 3, 3,
    11083, 3, 3, 5, 7, 41, 17, 5,
    3, 7, 54667, 4943, 3, 3, 113, 3,
    3, 71, 3, 5, 251, 3, 3, 173,
    271, 3, 7, 3, 17, 5, 3, 41,
    3, 5, 3, 3, 3, 37, 3, 5,
    135731, 3, 47, 3, 3, 23027, 3, 13,
    3, 5, 3, 7, 61, 3, 3, 80492017,
    3, 7, 3, 11, 5, 3, 3, 7,
    1893223, 3, 13, 5, 23, 3, 17, 467,
    3, 71, 5, 11, 3, 4261, 3, 31,
    3, 5, 3, 479, 3, 3, 3, 3,
    5, 19, 3, 51839, 3, 79, 3, 11,
    3, 3, 3, 97, 5, 13, 3, 30887123,
    3, 1811, 3, 2671, 3, 3, 11, 3,
    3, 3, 3, 5, 773, 3, 3, 151,
    225353, 3, 89, 3, 182209, 3, 7, 5,
    3, 7, 3, 23, 3, 149, 3, 7,
    3, 3, 3, 347, 3, 5, 17, 3,
    3, 47, 3, 3, 59, 3, 5, 3,
    3, 7, 5, 3, 3, 3, 7, 696417373,
    3, 13, 3, 3, 7, 3, 229, 3,
    3, 3, 11, 83, 3, 101, 3, 37,
    5, 29, 3, 5, 3, 839, 3, 5,
    3, 137, 3, 3, 7, 241, 3, 5,
    197, 3, 3, 17, 3, 13, 19, 3,
    853, 5, 37, 3, 3, 17, 3, 3,
    5, 7, 11, 3, 3, 3, 31, 3,
    5, 179, 3, 11, 3, 3, 3, 79624423,
    271, 3, 19, 3, 37, 3, 5, 1523,
    3, 43, 3, 5, 7, 3, 3, 7027,
    3, 53, 3, 3, 5, 619, 655961, 9601,
    11, 3, 3, 3, 398103479, 7, 5, 185951,
    3, 5, 3, 3, 29, 3, 5, 659,
    3, 3, 3, 5, 3, 3, 3, 3,
    12049, 3, 5, 2917, 3, 3, 3, 5,
    4057, 13, 5, 38891, 3, 3, 5, 7,
    3, 3, 43, 3, 5, 19, 3, 3,
    11, 3, 3, 31, 7, 421055749, 3, 3,
    7, 127, 3, 97, 5, 3, 3, 17,
    3, 5, 3, 3, 3, 5, 1643893, 3,
    68777, 3, 29, 5477, 3, 3, 11, 7,
    211, 3, 3, 3, 3, 11, 5, 3,
    7, 3, 113, 3, 3, 3, 6379, 3,
    13, 83, 5, 11, 3, 7, 5, 283,
    3, 5, 3, 37, 7, 29, 5, 15073,
    3, 3, 107, 3, 3, 3, 163, 3,
    3, 13, 11, 3, 5, 223, 3, 7,
    97, 3, 3, 23, 3, 3, 3, 5,
    3, 7, 3, 73, 3, 3, 26633, 3,
    552096613, 3, 23, 3, 3, 5, 3, 19,
    7, 3, 11, 3, 3, 3, 5, 3,
    7, 11, 5, 3, 3, 3, 5, 691,
    3, 3, 13, 113, 3, 2777, 3, 2536999,
    5, 3, 7, 11, 3, 79, 17, 3,
    7, 25057301, 3, 3, 23663, 5, 3, 3,
    3, 17, 3, 41, 5, 3, 2083, 3,
    5, 3, 3, 5, 983, 3, 5, 3,
    3, 7, 3, 3, 29, 5, 11, 3,
    3, 179, 127520483, 3, 1481, 342853153, 5, 13,
    3, 3, 5, 23, 3, 3, 3, 3,
    7, 3, 3, 3, 61, 3, 3, 5,
    3, 38797901, 1019, 3, 3, 52147, 3, 5,
    227, 3, 3, 4463, 7, 3, 3, 3,
    5, 47, 3, 3, 3, 376153, 3, 17,
    3, 3, 13, 3, 19, 35059, 3, 29,
    3, 71, 3, 5, 3, 937, 3, 5,
    3, 1153, 5, 557, 3, 3, 199, 3,
    23, 31, 2509757, 3, 1979, 3, 3, 151,
    7, 5, 3, 3, 577, 5, 7, 3,
    3, 5, 3, 3, 19, 5, 13, 59,
    11, 3, 1913, 3, 3, 7, 5, 3,
    17, 3, 3, 7, 3, 3, 6067, 5,
    5, 3, 19, 3, 3, 41, 3, 37,
    3, 3, 3, 3, 3, 5, 103, 11,
    3, 3, 7, 225601, 3, 13, 3, 17,
    5, 53, 3, 1051, 61, 3, 1399, 3,
    3, 13, 5, 11, 3, 3, 7, 3,
    3, 5, 7, 3, 5, 3, 3, 7,
    3, 5, 3, 3, 157, 3, 3, 571,
    3, 3, 5, 7, 5, 59, 229, 5,
    3, 3, 19, 3, 5, 7, 1032067, 11,
    3, 3, 149, 16363, 3, 3, 3, 653,
    3, 3]

theorem prime_sub_8039 : Nat.Prime (2043437180188810768 - 8039) := by
  show Nat.Prime 2043437180188802729
  exact p2043437180188802729

theorem check_8039 : allC 2043437180188810768 8039 P10k ds_8039 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 2043437180188810768 is 8039. -/
theorem minGB_S_8039 : minGB 2043437180188810768 = 8039 :=
  minGB_eq_of P10k P10k_complete 2043437180188810768 8039 (by norm_num) (by norm_num) prime_sub_8039 ds_8039 check_8039

def ds_8087 : List ℕ := [
    2, 5, 61, 3, 67, 3, 37, 3,
    5, 121703581, 3, 3, 7, 3, 31, 5,
    13, 3, 3, 71, 3, 3, 5, 83,
    3, 43, 3, 3389, 3, 5, 3, 53,
    13, 3, 599, 3, 3, 3, 7, 5,
    947, 3, 149, 3, 19, 3, 3, 3,
    3109, 3, 5, 37, 3, 7, 17, 5,
    157, 3, 3, 18427, 3, 5, 3, 19,
    3, 11, 3, 3, 3931, 3, 5, 17,
    3, 3, 3, 5, 4639051, 3, 86719, 3,
    7, 3, 17377, 3, 3, 5, 11, 3,
    7, 3, 367, 41, 3, 29, 3, 5,
    1621, 20747, 3, 3, 3, 479, 5, 7151,
    3, 3, 7, 5, 113, 3, 3, 3,
    43, 3, 3, 59, 3, 11, 5, 23447,
    3, 3, 859, 5, 3, 2741, 3, 311,
    3, 3, 3, 5, 3, 3, 13, 3,
    5, 3, 7, 1026392639, 3, 101, 3, 3156347,
    3, 7, 3, 5012153, 3, 5, 3, 7,
    3, 2579, 3, 11, 3, 457, 3, 1195589,
    5233, 5, 3, 17, 11, 5, 3, 3,
    3, 5, 4723, 3, 499, 3, 3, 7,
    3, 30416279, 3, 3, 3, 7, 3, 91463,
    5, 11, 3, 3, 3, 13, 3, 5,
    3, 47, 29, 5, 3, 3, 7, 5,
    13, 3, 3, 3, 7, 17, 3, 5,
    2683, 3, 3, 7, 3, 11, 1049, 3,
    3, 29, 103, 5, 3, 3, 73, 3,
    7, 3, 5, 11, 3, 19, 3, 3,
    3, 17, 3, 467, 3, 5, 571, 7,
    5, 3, 3, 3, 5, 577, 3, 11,
    3, 5, 3, 107, 404843, 3, 5, 13,
    3, 3, 7, 3, 3, 66919, 3, 3,
    13, 3, 29, 7, 3, 5, 3, 3,
    3, 3, 3, 3, 17, 3, 3, 557,
    5, 3, 7, 3, 3, 16349, 3, 7470389,
    3, 7, 11, 19, 5, 7, 3, 7639,
    3, 5, 89, 3, 3, 24001, 3, 5,
    3, 3, 47, 3, 53, 3, 5, 144883,
    83, 3, 13, 3, 7, 139, 3, 401,
    3, 3, 7, 3, 5, 3, 3, 3,
    109, 5, 3, 37, 3, 5, 3, 7,
    3, 5, 3, 3, 3, 11, 7, 3,
    5, 25549607, 3, 3, 7, 53, 3, 3,
    23, 3, 3, 5, 13, 59, 1753, 5,
    3, 461, 41, 37, 3, 3, 7, 3,
    3, 293, 3, 5, 569, 3, 3, 29,
    19, 3, 239, 3, 53113, 5, 3, 23,
    3, 5, 3, 3, 3, 7, 3, 5,
    265493, 3, 13, 3, 3, 7, 3, 139313,
    3, 5, 3, 9463, 13, 3, 3, 5927,
    3, 19, 3, 31, 5, 3, 3, 109,
    563, 3, 7, 5, 17, 3, 29, 7,
    3, 11, 5, 173, 3, 239425507, 3, 17,
    3, 5, 3, 137, 3, 3, 3, 3,
    5, 11, 3, 59, 3, 317, 3, 2633,
    3, 3, 3, 7, 5, 23, 3, 11,
    3, 12241, 3, 13, 3, 3, 61, 3,
    3, 3, 3, 5, 797, 3, 3, 23,
    7, 3, 523, 3, 19, 3, 641, 5,
    3, 29, 3, 233, 3, 14249, 3, 13,
    3, 3, 3, 7, 3, 5, 44693113, 3,
    3, 62047, 3, 3, 31, 3, 5, 3,
    3, 11, 5, 3, 3, 3, 163, 263,
    3, 41, 3, 3, 51647, 3, 47, 3,
    3, 3, 23, 31, 3, 7, 3, 29,
    5, 7, 3, 5, 3, 101, 3, 5,
    3, 11, 3, 3, 336643, 1619243, 3, 5,
    17, 3, 3, 7, 3, 7, 47, 3,
    173, 5, 42463, 3, 3, 167, 3, 3,
    5, 11, 1471, 3, 3, 3, 337, 3,
    5, 31, 3, 7, 3, 3, 3, 11,
    81847, 3, 43, 3, 7, 3, 5, 257911273,
    3, 13, 3, 5, 293, 3, 3, 17,
    3, 13, 3, 3, 5, 414737, 61, 7,
    3011, 3, 3, 3, 7, 37, 5, 199,
    3, 5, 3, 3, 1278611, 3, 5, 7211,
    3, 3, 3, 5, 3, 3, 3, 3,
    97, 3, 5, 89, 3, 3, 3, 5,
    37, 1003241, 5, 1013, 3, 3, 5, 304651,
    3, 3, 7, 3, 5, 13463, 3, 3,
    13, 3, 3, 7, 5507, 59, 3, 3,
    131, 251, 3, 11, 5, 3, 3, 349,
    3, 5, 3, 3, 3, 5, 839, 3,
    577, 3, 7, 13, 3, 3, 7, 309667,
    19, 3, 3, 3, 3, 315467, 5, 3,
    62071, 3, 29, 3, 3, 3, 5167, 3,
    67, 43, 5, 23, 3, 14303, 5, 2309,
    3, 5, 3, 73, 191, 21673, 5, 11,
    3, 3, 7, 3, 3, 3, 13, 3,
    3, 2297, 79, 3, 5, 7, 3, 137,
    13, 3, 3, 11, 3, 3, 3, 5,
    3, 3461, 3, 67, 3, 3, 284269, 3,
    1109, 3, 7, 3, 3, 5, 3, 7,
    89, 3, 1178492473, 3, 3, 3, 5, 3,
    97, 9767, 5, 3, 3, 3, 5, 1933,
    3, 3, 11, 17, 3, 7, 3, 19,
    5, 3, 11, 2521, 3, 257, 13, 3,
    19, 211, 3, 3, 7, 5, 3, 3,
    3, 7, 3, 5413, 5, 3, 7, 3,
    5, 3, 3, 5, 193, 3, 5, 3,
    3, 13, 3, 3, 7, 5, 25309, 3,
    3, 73483, 7, 3, 103, 311, 5, 137,
    3, 3, 5, 541, 3, 3, 3, 3,
    11, 3, 3, 3, 149, 3, 3, 5,
    3, 53, 11, 3, 3, 7, 3, 5,
    397, 3, 3, 17, 104047, 3, 3, 3,
    5, 23, 3, 3, 3, 13, 3, 113,
    3, 3, 7, 3, 107, 7, 3, 12097,
    3, 281, 3, 5, 3, 151, 3, 5,
    3, 1153, 5, 199, 3, 3, 37, 3,
    239, 11, 1433, 3, 61, 3, 3, 7,
    197, 5, 3, 3, 13, 5, 499, 3,
    3, 5, 3, 3, 13, 5, 518989927, 37,
    53, 3, 19, 3, 3, 42703, 5, 3,
    23, 3, 3, 769, 3, 3, 11, 5,
    5, 3, 7, 3, 3, 419, 3, 7,
    3, 3, 3, 3, 3, 5, 29, 31642697,
    3, 3, 615479, 23, 3, 17, 3, 7,
    5, 2311, 3, 73, 13, 3, 7, 3,
    3, 11, 5, 269, 3, 3, 19, 3,
    3, 5, 67, 3, 5, 3, 3, 61,
    3, 5, 3, 3, 7, 3, 3, 16249319,
    3, 3, 5, 1123, 5, 463, 11, 5,
    3, 3, 421, 3, 5, 23, 11, 2111,
    3, 3, 7, 19, 3, 3, 3, 17,
    3, 3, 11, 3, 3, 11786689, 53]

theorem prime_sub_8087 : Nat.Prime (2758163428100238178 - 8087) := by
  show Nat.Prime 2758163428100230091
  exact p2758163428100230091

theorem check_8087 : allC 2758163428100238178 8087 P10k ds_8087 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 2758163428100238178 is 8087. -/
theorem minGB_S_8087 : minGB 2758163428100238178 = 8087 :=
  minGB_eq_of P10k P10k_complete 2758163428100238178 8087 (by norm_num) (by norm_num) prime_sub_8087 ds_8087 check_8087

def ds_8243 : List ℕ := [
    2, 11, 7, 3, 5, 3, 37579, 3,
    17, 33191, 3, 3, 5, 3, 7, 19,
    13, 3, 3, 5, 3, 3, 47, 7,
    3, 5, 3, 1831, 3, 11, 3, 5,
    13, 3, 146282041, 3, 3, 3, 19, 7,
    11, 3, 5, 3, 17838031, 3, 3, 3,
    17, 3, 1409, 43, 3, 5, 7, 139,
    127, 3, 3, 5, 3, 13, 3, 5,
    3, 31, 3, 3, 1785209149, 3, 17749, 337,
    3, 3, 3, 7, 23, 3, 5, 3,
    18917, 3, 5, 3, 3, 11, 13, 3,
    5, 3, 7, 827, 3, 5, 3, 31,
    7, 5, 3, 3, 3, 335635537, 79, 373,
    3, 3, 457, 7, 137, 3, 3, 3,
    113, 3, 3, 5, 3, 47, 389, 193181,
    3, 3, 7, 13, 3, 5, 3, 7,
    3, 3, 3, 507803, 3, 3, 5, 3,
    11, 3, 131, 163, 3, 5, 3, 1078242467,
    3, 11, 3, 239, 3, 29, 3, 5,
    3, 7, 3, 5, 3, 7, 3, 5,
    661, 73, 3, 5, 151631, 151, 3, 3,
    3, 7, 1091459, 3, 5, 3, 3, 83,
    3, 5, 3, 3, 3, 5, 3, 7,
    11, 37, 3, 3, 3, 5, 3, 1259,
    3, 5, 114221, 19, 3, 3, 23, 7,
    13, 3, 3, 3, 139969, 44927, 3, 107,
    352076999, 3, 3, 5, 3, 7, 233, 3,
    3, 5, 11, 61, 3, 3, 2789, 3,
    293, 3, 7, 251, 3, 5, 3, 3,
    3, 5, 3, 41, 3, 23, 11, 5,
    173, 3, 3, 3, 17, 7, 3, 5,
    3, 131, 3, 5, 499, 3, 15991, 13,
    3, 3, 1213, 3, 3, 87641, 3, 3,
    11, 3, 53, 5, 3, 29, 3, 3,
    3, 3, 3, 3, 43, 3, 3, 5,
    575747, 3, 2216213, 3, 3, 5, 3, 19,
    3, 151, 5, 23, 1069, 5, 3, 22271,
    3, 113, 7, 3, 3, 37, 3, 15349,
    3, 3, 11, 3, 479, 3, 7, 269,
    5, 3, 13, 3, 140822827, 5, 3, 97,
    3, 3, 5, 3, 968886007, 3, 3, 3,
    109, 1889, 3, 197, 3, 13, 3, 17,
    3, 7, 3, 3, 3, 1507374199, 11489, 3,
    19, 47, 3, 3, 5, 7, 3, 3,
    5, 3, 3, 1493, 7, 5, 12149, 11,
    3, 5, 19, 23, 3, 3, 13, 3,
    3, 5, 3, 83, 31, 3, 3, 63493,
    5, 3, 7, 3, 5, 13, 3, 157,
    3, 37, 3, 3, 3, 11, 3, 7,
    1510591, 3, 5, 3, 3, 751181, 3, 5,
    3, 11, 3, 7, 13, 3, 3, 5,
    3, 7, 3, 61, 8039, 3, 3, 5,
    17, 3, 1667, 7, 1039, 3, 59, 535589,
    3, 887, 41, 1277, 3, 1759, 3, 5,
    3, 13, 3, 5, 3, 3, 3, 3,
    11, 1163, 3, 859, 3, 71, 3, 16879,
    3, 3, 3, 5, 61, 41, 3, 5,
    3, 5, 3, 13, 3, 3, 29, 3,
    3, 3, 3, 7, 37, 3, 3, 11,
    19, 3, 5, 3, 17, 3, 7, 11,
    3, 7, 3, 5, 3, 47, 3, 5,
    3, 3, 3, 3805037, 3, 7, 83, 3,
    3, 101, 3, 3, 5, 3, 17, 3,
    3, 7, 191, 3, 3, 3, 7, 5,
    3, 11, 3, 3, 5, 3, 835979, 3,
    3, 3, 5, 6547, 3, 4271, 3, 17,
    13, 5, 3, 8647, 3, 5, 3, 6315223,
    3, 5, 3, 3, 5, 27449, 3, 5879,
    19, 3, 3, 41, 3, 59, 5, 3,
    11, 8929, 73, 3, 3, 1123, 3, 3,
    11, 7, 5, 3, 3, 3, 409, 3,
    95989, 11, 3, 19, 3, 3, 3, 5,
    37, 3, 3069841, 3, 5, 3, 23, 7333,
    3, 5, 3, 8081, 7, 3, 3, 11,
    3, 13, 3, 3, 7, 5, 1028393, 17,
    5, 3, 3, 3, 5, 7, 39173447, 5,
    3, 107, 3, 3, 29, 3, 1097, 532621,
    3, 3, 3, 7, 3, 3, 3, 3,
    173, 3, 1237, 303139, 3, 3, 3, 463,
    267497, 5, 821, 5, 3, 3, 11, 5,
    3, 3, 903563, 3, 7, 11, 3, 3,
    13, 3, 3, 5, 7, 53, 3, 3,
    7, 5, 3, 105337, 23, 3, 3, 31,
    3, 13, 3, 3, 3, 7, 5351, 3,
    5, 3, 29, 5, 3, 3, 5, 7,
    1592051, 3, 3, 3, 3, 1198529273, 31, 3,
    5, 3, 307, 3, 3, 3, 5, 3,
    947, 5, 1999, 571, 3, 7, 79, 7351,
    3, 73, 3, 5, 5, 29, 11, 43,
    3, 3, 1059344453, 3, 3, 3, 5, 3,
    3, 5, 89, 3, 157, 5, 3, 7,
    13, 3, 3, 5, 3, 3, 3, 160687,
    3, 5, 3, 19, 3, 3, 5, 3,
    11, 3, 41, 3, 3, 71, 3, 5,
    7, 3, 5, 3, 3, 3, 197, 3,
    5, 1291, 401, 3, 3, 3, 7, 3054197,
    3, 3, 5, 19, 3, 36998089, 3, 31,
    341659, 3, 7, 17, 3, 5, 11, 3,
    5, 83, 3, 3, 23, 7, 3, 3,
    3, 9649, 3, 5, 59, 3, 5, 3,
    13, 3, 3, 43, 9337, 3, 97, 3,
    3, 5, 3, 3, 29, 7, 31, 3,
    3, 47, 13, 3, 5, 11, 19, 1901,
    3, 3, 137, 367, 3, 3, 3, 3,
    7, 3, 3, 3, 11, 3, 3, 7,
    3, 5, 5, 3, 3, 5, 3, 139326757,
    47, 3, 3, 5, 7, 3, 3, 3,
    17, 37, 3, 3, 3, 13, 3, 5,
    3, 3, 113, 3, 23, 5, 3, 11,
    3, 5, 3, 283, 3, 31, 3, 211,
    3, 17, 61, 57179, 3, 3, 41, 3,
    5, 179, 43, 3, 17, 3, 3, 5,
    7, 1721, 3, 3, 5, 23, 7, 3,
    3, 11, 3, 3, 13, 7, 11, 5,
    29, 3, 5, 3, 3, 7, 101, 3,
    5, 3, 3, 7, 3, 3, 677, 613,
    373, 3, 11, 3, 3, 5, 3, 19,
    3, 3, 3, 3, 3, 53, 5, 1021,
    3, 3, 5, 2903, 3, 1031, 3, 85061,
    7, 59, 3, 5, 13, 3, 103, 3,
    3, 19, 4721, 1433, 3, 3, 7, 3,
    3, 1160594951, 7, 3, 17, 3, 3, 5,
    3, 11, 3, 3, 647067191, 3, 3, 31,
    3, 3, 1250149, 7, 29, 311, 5, 433,
    3, 3, 17, 3, 41, 5, 2179, 19,
    3, 3, 13, 97, 3, 3, 3, 14071,
    3, 3, 87221, 3, 3, 7, 5, 461,
    3, 13, 3, 5, 23, 46199, 19, 3,
    3, 5, 3, 3, 3, 401, 3, 5,
    3, 7]

theorem prime_sub_8243 : Nat.Prime (3244400084505812356 - 8243) := by
  show Nat.Prime 3244400084505804113
  exact p3244400084505804113

theorem check_8243 : allC 3244400084505812356 8243 P10k ds_8243 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 3244400084505812356 is 8243. -/
theorem minGB_S_8243 : minGB 3244400084505812356 = 8243 :=
  minGB_eq_of P10k P10k_complete 3244400084505812356 8243 (by norm_num) (by norm_num) prime_sub_8243 ds_8243 check_8243

def ds_8273 : List ℕ := [
    2, 13, 6962677, 3, 89, 3, 607, 3,
    7, 5, 3, 3, 43, 3, 17, 67,
    5, 3, 3, 19, 3, 3, 9887, 5,
    3, 11, 3, 7, 3, 575708027, 3, 163,
    1881533, 3, 5, 3, 3, 3, 11, 29,
    5, 3, 7, 3, 37, 3, 3, 3,
    7177, 3, 7, 5, 3, 17, 23, 13,
    5, 3, 3, 109, 3, 1721, 3, 151,
    3, 7, 3, 3, 29, 3, 17, 5,
    3, 3, 3, 19381, 5, 3, 7, 3,
    5, 3, 11, 3, 3, 7, 5, 3,
    73, 3, 6217, 5, 3, 809, 3, 121579,
    5, 29, 3, 3, 3, 17, 11, 5,
    3, 3, 521, 3853, 5, 3, 3, 3,
    1999, 3, 3, 19, 3, 278063, 7, 5,
    3, 3, 277, 251, 3, 41, 3, 5,
    3, 3, 3, 9281, 3, 3, 11, 3,
    137, 3, 59, 5, 3, 7, 3, 11,
    3, 5, 3, 67, 3, 7, 3, 131,
    3, 13, 3, 199, 3, 5, 3, 189371939,
    7, 400651, 3, 3109, 31, 19, 3, 3,
    3, 393970079, 5, 3, 7, 3, 3, 5,
    3, 239, 3, 3, 3, 11, 3, 19,
    1069, 5, 3, 3, 3, 59, 3, 31,
    3, 599, 7523, 41, 3, 3, 29, 11,
    5, 3, 3, 3, 5, 13, 3, 7,
    5, 3, 3, 233, 3, 37, 5, 3,
    3, 23, 7, 17, 3, 3, 5, 3,
    167, 3, 13, 5, 3, 7, 3, 3,
    3, 271, 3, 11, 3, 7, 5, 13,
    71, 3, 3, 3, 11, 5, 3, 937,
    3, 757, 3, 947, 149, 3, 89, 5,
    3, 3, 23, 3, 3, 13, 3, 3,
    9483919, 3, 5, 31, 3, 2797, 3, 3,
    3, 3, 3, 3, 7, 3, 3, 353,
    13, 3, 43, 3, 3, 7, 3, 101,
    3, 5, 13, 31, 7, 41, 3, 5,
    3, 37, 5, 3, 3, 7, 3, 227,
    3, 3, 400711, 3, 5, 3, 47, 5,
    7, 3, 17, 3, 5, 360781, 3, 5,
    3, 3, 139, 3, 19867319, 3, 3, 3,
    7, 11, 3, 19, 3, 109, 3, 193,
    3, 847219, 3, 3, 3, 238676827, 5, 3,
    7, 5, 3, 3, 19, 107, 3, 3,
    1291, 3, 3, 17, 5, 11, 7, 41,
    3, 173, 13, 5, 3, 3, 11, 3,
    3, 19081, 3, 7, 5, 3, 3, 5,
    32085727, 3, 5, 3, 43, 307, 3, 780206761,
    3, 349, 3, 3, 3, 719, 3, 19,
    5, 3, 7, 3, 3, 5, 3, 11,
    3, 7, 3, 8707, 5, 3, 3, 17,
    3, 5, 3, 7, 547, 3, 3, 37,
    5, 3, 109, 17, 5, 3, 44902213, 5,
    3, 29, 7, 5, 3, 5, 3, 3851,
    3, 31, 3, 373, 3, 3, 3, 3,
    37, 5, 3, 5, 3, 11, 3, 709,
    3, 3, 3, 47, 11, 5, 3, 5081,
    3, 100379, 3, 7, 3, 3, 5, 3,
    3, 3, 3, 103, 5, 3, 3, 317,
    5, 3, 53, 3, 5, 3, 41, 17,
    3, 5, 3, 13, 3, 7, 3, 19,
    3, 3, 3, 37, 3, 11, 5, 3,
    3, 218171, 3, 3, 31, 3, 7, 3,
    3, 13, 1723, 3, 3, 3, 5, 67,
    3, 7, 3, 3, 371073167, 3, 5, 3,
    3, 3, 7, 31, 3, 5, 3, 11,
    7, 17, 3, 19, 3, 13, 3, 11,
    3, 613, 3, 3, 43, 79, 3, 17,
    5, 3, 3, 19, 3, 5, 29, 3,
    13, 7, 5, 3, 3, 5, 3, 3,
    67, 5, 643, 3, 3, 3, 11, 3,
    116857289, 5, 3, 6734327, 3, 3, 3, 249427,
    91813, 3, 5, 3, 13, 3, 10184557, 5,
    3, 1931, 3, 89, 5, 3, 3, 59,
    3, 5, 3, 3, 2028749, 7, 13, 5,
    563, 3, 3, 3, 126108613, 11, 370883, 56071649,
    3, 199, 3, 3, 7, 3, 11, 170081,
    3, 3, 3, 193, 3, 3, 3, 3,
    17, 3, 7, 5, 3, 3, 3, 23,
    5, 59, 29718877, 11, 3, 3, 271, 12430931,
    3, 3, 11, 3, 80777, 5, 3, 3,
    89, 3, 3, 29, 67, 5, 3, 3,
    5, 71, 3, 7, 13, 3, 3, 19717,
    3, 19, 3, 3, 3, 47287, 5, 3,
    7, 3, 5, 11, 3, 3, 37, 19,
    5, 3, 3, 3, 3, 7, 127, 3,
    587, 3, 5, 3, 3, 3, 7, 3,
    4694111, 2383, 7, 5, 3, 1661034671, 37, 5,
    3, 13, 3, 17, 11, 900147317, 29, 5,
    3, 3, 449, 3, 3, 3, 7, 3,
    3, 853, 139, 3, 7, 23, 3, 701,
    5, 3, 3, 1499, 3, 3, 3, 75407,
    3, 49877, 3, 5, 3, 3, 7, 3,
    17, 3, 5, 3, 3, 7, 3, 11,
    43, 3, 29, 3, 3, 3, 71, 3,
    13, 83, 31, 3, 3, 3, 11, 5,
    3, 3, 7, 41, 3, 5, 3, 74174167,
    7, 3, 257000851, 5, 3, 3251, 7, 3,
    47, 5, 3, 3, 353, 23, 3, 3,
    3, 5, 3, 10868659, 7, 3, 27283, 3,
    61, 3, 3, 11, 7, 3, 28404251, 3,
    3, 647587, 3, 3, 1647862169, 29, 5, 3,
    3, 79, 5, 3, 139, 307, 7, 5,
    3, 3, 631, 5, 3, 3, 3, 3,
    5, 3, 3, 3, 5, 3, 3, 17,
    3, 7, 615751, 3, 3, 53, 3, 13033,
    5, 3, 3, 13, 5, 3, 3, 3,
    97, 5, 3, 3, 3, 5, 3, 7,
    3, 3, 5, 3, 13, 79, 3, 5,
    3, 113, 3, 83, 3, 7, 3, 11,
    3, 37, 27109, 5, 3, 3, 5, 3,
    7, 683, 17581, 3, 5, 3, 3, 13,
    163, 17, 3, 3, 719, 23319521, 5, 3,
    3, 295237, 3, 3, 5, 190657, 5, 7,
    13, 3, 317, 3, 3, 17, 937, 3,
    397, 3, 3, 5, 3, 3, 7, 19,
    13, 3, 29, 3, 3, 7, 3, 5,
    3, 3, 3, 3, 3, 23, 227, 7,
    3, 3, 19, 31, 3, 5, 3, 13,
    37, 5, 3, 7, 6269, 3, 5, 3,
    3, 2734211, 7, 5, 3, 3, 61, 3,
    3, 2689, 5, 3, 13, 3, 3, 11,
    3, 47, 3, 3, 4817, 3, 3, 11,
    3, 3, 7, 97, 11, 5, 4397, 1040093,
    3, 3, 7, 3, 30449, 17, 13, 5,
    3, 3, 19, 5, 3, 3, 3, 5,
    3, 3, 5, 3, 3, 5, 41, 7,
    3, 67, 3, 449, 69880919, 23, 113, 3,
    3, 7, 3, 3, 3, 5, 3, 31,
    3, 1789, 223, 3, 3]

theorem prime_sub_8273 : Nat.Prime (3511797567359760604 - 8273) := by
  show Nat.Prime 3511797567359752331
  exact p3511797567359752331

theorem check_8273 : allC 3511797567359760604 8273 P10k ds_8273 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 3511797567359760604 is 8273. -/
theorem minGB_S_8273 : minGB 3511797567359760604 = 8273 :=
  minGB_eq_of P10k P10k_complete 3511797567359760604 8273 (by norm_num) (by norm_num) prime_sub_8273 ds_8273 check_8273

def ds_8369 : List ℕ := [
    2, 11, 19, 3, 65651, 3, 5, 3,
    29, 631, 3, 3, 7, 3, 5, 17,
    13, 3, 3, 76771, 3, 3, 7, 7603159,
    3, 1933, 3, 5, 3, 11, 3, 20921,
    5, 3, 3017929, 3, 3, 3, 5, 47,
    11, 3, 37, 3, 5, 3, 3, 3,
    5, 3, 19, 181, 3, 7, 5, 4643,
    10889, 3, 3, 1223, 3, 7, 3, 11,
    3, 5, 3, 3, 5, 3, 23, 17,
    3, 3, 3, 1607, 75712009, 3, 23091209, 3,
    7, 3, 167, 3, 3, 11, 13, 3,
    7, 3, 5, 71, 3, 23, 3, 7,
    11, 1061, 3, 3, 3, 5, 17, 977,
    3, 3, 5, 138580069, 971, 3, 3, 3,
    5, 3, 3, 11, 3, 5, 57901, 1118670221,
    3, 3, 5, 13, 3, 2609, 3, 29,
    3, 3, 3, 91743767, 3, 3, 13, 3,
    11, 3, 5, 7043, 3, 823, 3, 5,
    3, 7, 3, 5, 3, 2113, 3, 7,
    3, 5, 3, 35171, 3, 787, 3, 41,
    5, 79, 3, 11, 5, 137, 3, 3,
    3, 659, 43, 3, 19, 3, 3, 7,
    3, 161753, 3, 3, 3, 7, 3, 5,
    11, 743, 3, 3, 3, 13, 3, 457,
    3, 23, 5, 101, 3, 3, 5, 89,
    13, 3, 3, 3, 7, 5, 3, 70429,
    797, 3, 3, 7, 3, 5, 23, 3,
    3, 149, 5, 19, 3, 3, 139, 3,
    5, 3, 11, 17293, 3, 389, 3, 3,
    3, 17, 3, 5, 3, 73, 11, 7,
    37, 3, 3, 3, 7, 1198609, 3, 22963,
    3, 17, 3, 19, 5, 3, 31, 13,
    3, 3, 5, 3, 3, 5, 3, 3,
    5, 3, 50873, 7, 3, 23, 3, 3,
    3, 3, 3, 3, 5, 3, 3, 191,
    59, 3, 5, 3, 3, 23, 3, 5,
    3, 7, 79, 5, 467, 7, 3, 397,
    3, 7, 1634508769, 3, 3, 5, 3, 613,
    3, 3, 5, 3, 20231, 3, 433, 673091,
    227, 3, 5, 3, 7, 29, 3, 3571,
    3, 3, 7, 3, 521, 3, 3, 3,
    5, 103, 3, 5, 3, 13, 3, 5,
    3, 1409, 3, 3, 3, 5, 7, 3,
    61, 153841, 3, 3, 7, 5, 3, 3,
    727, 3, 3, 7, 13, 37, 5, 11,
    3, 2657, 5, 29, 3, 3, 5, 3,
    3, 59, 3, 31, 221195561, 3, 3, 11329,
    117889, 3, 71, 3, 11, 13, 3, 5,
    3, 41, 3, 3, 3, 5, 3, 131,
    23, 3, 13, 3, 3, 7, 3, 19,
    3, 11, 3, 5, 13, 3, 3, 53,
    3, 11, 3, 5, 354146659, 3, 3, 509,
    1931, 3, 5, 1283, 17, 3, 5, 7,
    3, 5, 157, 19, 3, 1232096143, 3, 17,
    3, 7, 3, 127, 3, 3, 3, 3,
    11, 113, 3, 53, 3, 5, 3, 5,
    3, 3, 3, 7, 373, 97, 3, 163,
    3, 23, 3, 5, 3, 3, 37, 3,
    3, 3, 3, 79, 29, 3, 3, 5,
    7, 3, 47387, 3, 23, 3, 5, 11,
    3, 103, 3, 71, 3, 5, 3, 13,
    3, 3, 3, 5, 3, 94661741, 19, 3,
    3, 5, 3, 3, 60943, 3, 59, 3,
    3, 5, 17, 3, 3, 3, 31, 929,
    3, 5, 3, 3, 932677, 3, 1097, 3,
    3, 3, 11353, 5, 3, 7, 3, 5,
    13, 7, 3, 431, 3, 29, 3, 7,
    3, 13, 3, 3, 139, 5, 3, 379,
    17, 3, 3, 5, 3, 7, 859373, 3,
    5, 383, 523, 3, 3, 691, 3, 3,
    7, 23, 947, 3, 3, 3, 5, 3,
    17, 11, 3, 5, 3, 3, 3, 151,
    5, 3, 2551, 3, 7, 3, 199, 271,
    3, 11, 3, 7, 463, 3, 3, 5,
    3, 13, 3, 3, 29, 53, 5, 7,
    47456527, 3, 3, 3, 7, 5, 733, 4201,
    3, 7, 3, 3, 5, 3, 5471, 5,
    3, 3, 3, 13, 3, 3, 3, 3,
    5, 3, 17, 79561, 3, 3, 3, 571,
    19, 83, 7, 29, 3, 3, 11, 3769,
    3, 3, 5, 3, 19, 11, 3, 3,
    5, 3, 3, 7, 5, 43, 3, 3,
    109, 11, 3, 5, 502171, 3, 3, 5,
    3, 13, 3, 3, 3, 50700337, 59, 3,
    19, 3, 7, 13, 3, 3, 7, 5,
    1319, 3, 3, 3, 3, 5, 17, 3,
    519344053, 3, 83, 3, 3, 3, 26321, 3,
    5, 11, 2467, 521, 3, 5, 103, 251,
    3, 7, 3, 12641, 2011, 5, 11, 9857,
    3, 3, 5, 3, 3, 3, 13, 3,
    3, 13928921, 5, 3, 179, 7, 3, 5,
    13, 3, 3, 47, 3, 3, 3, 109,
    3, 11, 3, 112636417, 3, 3, 787, 3,
    5, 3, 7, 3, 3, 79, 3, 7,
    5, 3, 37, 3, 3, 3, 32272771, 3,
    113, 5, 47, 3, 3, 3, 643, 1487,
    3, 3, 41, 5, 3, 7, 3, 5,
    712927, 3, 5, 29, 3, 53, 5, 3,
    23, 89, 3, 3, 5, 11, 3, 3,
    3, 7, 3, 859, 29, 3, 7, 3,
    13, 3, 3, 7, 5, 3, 421, 3,
    3, 13, 3, 3, 5, 31, 27961, 3,
    3, 5, 7, 3, 73, 5, 229639, 3083,
    3, 3, 41, 61, 3, 3, 3, 3,
    19, 3, 3, 3, 11, 3, 3, 883,
    3, 317, 10198171, 3, 3, 7, 3, 23,
    26861, 3, 3, 11, 41, 3, 3, 3,
    490573, 47, 3, 3, 3, 13, 3, 23,
    3, 3, 7, 3, 5, 7, 3, 11,
    3, 1075453, 3, 7, 3, 5, 3, 653,
    3, 5, 25598723, 71, 3, 3, 82796249, 3,
    11, 5, 5, 3, 19, 3, 3, 7,
    5, 29, 3, 3, 13, 7, 13442641, 3,
    3, 11, 3, 3, 13, 857, 11, 1571,
    5, 3, 39139, 3, 3, 5, 17, 3,
    43, 3, 3, 78487, 3, 3, 5, 23,
    97, 3, 5, 3, 3, 29, 3, 7,
    3, 3, 3, 3, 3, 7, 1823, 5,
    3, 3, 821, 5, 3, 17, 3, 5,
    191204257, 19, 3, 191, 5, 3, 7, 3,
    3, 5, 41, 79, 3, 3, 5, 3,
    3, 7, 20312393, 3, 157, 3, 3, 26821253,
    3, 11, 3, 3, 5, 3, 3, 5,
    3, 3, 144563, 5, 61, 41, 59, 7,
    3, 3, 5, 3, 769, 11, 5, 3461,
    3, 3, 5, 122979403, 3, 3, 3, 17,
    3, 3, 1559, 3, 3, 47, 23, 5,
    3, 13, 3, 17, 5, 31, 5, 3,
    3, 13, 3, 3, 3, 23, 3, 7,
    3, 5, 43, 3, 3, 7, 3, 436531,
    3, 5, 3, 3, 3, 3, 11]

theorem prime_sub_8369 : Nat.Prime (3714759793830649402 - 8369) := by
  show Nat.Prime 3714759793830641033
  exact p3714759793830641033

theorem check_8369 : allC 3714759793830649402 8369 P10k ds_8369 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 3714759793830649402 is 8369. -/
theorem minGB_S_8369 : minGB 3714759793830649402 = 8369 :=
  minGB_eq_of P10k P10k_complete 3714759793830649402 8369 (by norm_num) (by norm_num) prime_sub_8369 ds_8369 check_8369

def ds_8387 : List ℕ := [
    2, 163, 53, 3, 5, 3, 61, 3,
    151, 139, 3, 3, 5, 3, 19, 18223,
    239, 3, 3, 5, 3, 3, 7, 29,
    3, 5, 3, 11, 3, 13, 3, 5,
    23, 3, 137, 3, 3, 3, 7, 11,
    37, 3, 5, 3, 311, 3, 3, 3,
    47, 3, 2347, 11, 3, 5, 38613437, 29,
    13, 3, 3, 5, 3, 7, 3, 5,
    3, 79, 3, 3, 13, 3, 167, 67,
    3, 3, 3, 61, 17, 3, 5, 3,
    7, 3, 5, 3, 3, 43, 38371, 3,
    5, 3, 1669, 241, 3, 5, 3, 7,
    47, 5, 3, 3, 3, 31, 8714071, 11,
    3, 3, 7, 17, 467, 3, 3, 3,
    19, 3, 3, 5, 3, 101, 3889, 13,
    3, 3, 1213, 26227, 3, 5, 3, 73,
    3, 3, 3, 31, 3, 3, 5, 3,
    313, 3, 7, 829, 3, 5, 3, 23,
    3, 7, 3, 71551, 3, 139, 3, 5,
    3, 281, 3, 5, 3, 31, 3, 5,
    157, 71, 3, 5, 179, 30920471, 3, 3,
    3, 1399, 1321, 3, 5, 3, 3, 7,
    3, 5, 3, 3, 3, 5, 3, 11,
    17, 1009, 3, 3, 3, 5, 3, 11,
    3, 5, 19, 337, 3, 3, 7, 259931891,
    11, 3, 3, 3, 7, 53, 3, 13,
    37, 3, 3, 5, 3, 17, 109, 3,
    3, 5, 25577, 1381, 3, 3, 17, 3,
    7, 3, 99530159, 13, 3, 5, 3, 3,
    3, 5, 3, 31, 3, 11, 1733588797, 5,
    89, 3, 3, 3, 7, 11, 3, 5,
    3, 113, 3, 5, 71593, 3, 17, 362622173,
    3, 3, 7, 3, 3, 199, 3, 3,
    139, 3, 25931, 5, 3, 37, 3, 3,
    3, 3, 3, 3, 1652319847, 3, 3, 5,
    11, 3, 7, 3, 3, 5, 3, 293,
    3, 7, 5, 13, 53, 5, 3, 967,
    3, 7, 809407, 3, 3, 109838761, 3, 29,
    3, 3, 1187, 3, 83477, 3, 13, 23,
    5, 3, 11, 3, 7, 5, 3, 698821,
    3, 3, 5, 3, 11, 3, 3, 3,
    23, 19, 3, 12263, 3, 3331, 3, 7,
    3, 672781607, 3, 3, 3, 13, 7, 3,
    1291, 421, 3, 3, 5, 167, 3, 3,
    5, 3, 3, 7, 37, 5, 11, 13144709,
    3, 5, 1381780669, 107, 3, 3, 7, 3,
    3, 5, 3, 461, 11, 3, 3, 61,
    5, 3, 13, 3, 5, 17, 3, 71,
    3, 1091, 3, 3, 3, 7, 3, 1061,
    29, 3, 5, 3, 3, 7, 3, 5,
    3, 13163, 3, 83, 31, 3, 3, 5,
    3, 11681, 3, 17, 13, 3, 3, 5,
    11, 3, 7, 1156327, 73, 3, 239, 7,
    3, 6997, 683, 3673, 3, 13, 3, 5,
    3, 7, 3, 5, 3, 3, 3, 3,
    71, 499, 3, 59, 3, 233, 3, 8951,
    3, 3, 3, 5, 138272471, 11, 3, 5,
    3, 5, 3, 19559, 3, 3, 41, 3,
    3, 3, 3, 1039, 47, 3, 3, 17,
    7, 3, 5, 3, 13, 3, 11, 149,
    3, 17, 3, 5, 3, 13, 3, 5,
    3, 3, 3, 7, 3, 31, 11, 3,
    3, 53881, 3, 3, 5, 3, 8563, 3,
    3, 113, 13, 3, 3, 3, 89, 5,
    3, 61, 3, 3, 5, 3, 31, 3,
    3, 3, 5, 383, 3, 7, 3, 43,
    11, 5, 3, 16693, 3, 5, 3, 7,
    3, 5, 3, 3, 5, 29, 3, 19,
    311, 3, 3, 7, 3, 7, 5, 3,
    103, 13, 20939, 3, 3, 217319, 3, 3,
    7, 94747, 5, 3, 3, 3, 197, 3,
    11, 23, 3, 7, 3, 3, 3, 5,
    148008961, 3, 1613, 3, 5, 3, 1549, 137,
    3, 5, 3, 7, 317, 3, 3, 97,
    3, 277, 3, 3, 38609, 5, 11, 7,
    5, 3, 3, 3, 5, 47, 11, 5,
    3, 7, 3, 3, 1255913, 3, 32713, 2377,
    3, 3, 3, 79, 3, 3, 3, 3,
    13, 3, 11807, 31, 3, 3, 3, 17,
    2879, 5, 7, 5, 3, 3, 24509, 5,
    3, 3, 7, 3, 11, 373, 3, 3,
    241, 3, 3, 5, 17, 59, 3, 3,
    97, 5, 3, 307, 416413, 3, 3, 23,
    3, 113, 3, 3, 3, 343141, 419, 3,
    5, 3, 7, 5, 3, 3, 5, 43,
    73, 3, 3, 3, 3, 128213, 2005277, 3,
    5, 3, 11, 3, 3, 3, 5, 3,
    337, 5, 179, 124343, 3, 127, 47, 29,
    3, 7, 3, 5, 5, 11, 31, 98873,
    3, 3, 7, 3, 3, 3, 5, 3,
    3, 5, 523, 3, 29, 5, 3, 37,
    11, 3, 3, 5, 3, 3, 3, 13,
    3, 5, 3, 71, 3, 3, 5, 3,
    23, 3, 7, 3, 3, 17, 3, 5,
    11, 3, 5, 3, 3, 3, 11, 3,
    5, 13, 1693, 3, 3, 3, 347729, 11,
    3, 3, 5, 47, 3, 7, 3, 17,
    137, 3, 13267, 10304267, 3, 5, 67, 3,
    5, 463, 3, 3, 7, 728224681, 3, 3,
    3, 7, 3, 5, 11, 3, 5, 3,
    15349, 3, 3, 7, 13, 3, 17, 3,
    3, 5, 3, 3, 7, 83, 34631, 3,
    3, 5573, 7, 3, 5, 19, 31, 89,
    3, 3, 13, 883, 3, 3, 3, 3,
    67, 3, 3, 3, 8117, 3, 3, 108013,
    3, 5, 5, 3, 3, 5, 3, 10211,
    14621, 3, 3, 5, 157, 3, 3, 3,
    557, 19, 3, 3, 3, 1597, 3, 5,
    3, 3, 7, 3, 4888969, 5, 3, 307,
    3, 5, 3, 7, 3, 3767, 3, 19803481,
    3, 234281, 89, 656980231, 3, 3, 13, 3,
    5, 17, 11827, 3, 96457, 3, 3, 5,
    13, 88022489, 3, 3, 5, 7, 17, 3,
    3, 131, 3, 3, 1390771, 11, 577, 5,
    1999, 3, 5, 3, 3, 1398421, 67, 3,
    5, 3, 3, 19, 3, 3, 97, 31,
    37, 3, 7, 3, 3, 5, 3, 7,
    3, 3, 3, 3, 3, 7, 5, 19,
    3, 3, 5, 494837459, 3, 11, 3, 7,
    13, 17, 3, 5, 137, 3, 7, 3,
    3, 1886981, 127, 23, 3, 3, 150617, 3,
    3, 7, 176201, 3, 197, 3, 3, 5,
    3, 61, 3, 3, 7, 3, 3, 13,
    3, 3, 457, 431, 2729, 11, 5, 7,
    3, 3, 109384571, 3, 149, 5, 22507601, 29,
    3, 3, 7, 37, 3, 3, 3, 39791,
    3, 3, 17, 3, 3, 13, 5, 23671,
    3, 11, 3, 5, 163417, 47, 7, 3,
    3, 5, 3, 3, 3, 41, 3, 5,
    3, 107, 17, 3, 3, 7, 3, 5,
    3, 177613031, 3, 3, 3, 3, 113, 19,
    3]

theorem prime_sub_8387 : Nat.Prime (3878297017437646306 - 8387) := by
  show Nat.Prime 3878297017437637919
  exact p3878297017437637919

theorem check_8387 : allC 3878297017437646306 8387 P10k ds_8387 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 3878297017437646306 is 8387. -/
theorem minGB_S_8387 : minGB 3878297017437646306 = 8387 :=
  minGB_eq_of P10k P10k_complete 3878297017437646306 8387 (by norm_num) (by norm_num) prime_sub_8387 ds_8387 check_8387

end LeanLab.OeSHP2014
