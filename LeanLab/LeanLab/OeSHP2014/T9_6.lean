/-
P0005 Oliveira e Silva, Herzog, Pardi 2014, Table 9, page 2051, record-breaking first
occurrences P(g) of a prime gap g, part 6: each row IsGapAt P(g) g, that is P(g) and
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

theorem p13094537 : Nat.Prime 13094537 := by
  refine Pratt.pratt 13094537 3 [(2, 3), (7, 1), (13, 1), (17987, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p14042563 : Nat.Prime 14042563 := by
  refine Pratt.pratt 14042563 2 [(2, 1), (3, 1), (53, 1), (44159, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p16079513 : Nat.Prime 16079513 := by
  refine Pratt.pratt 16079513 3 [(2, 3), (71, 1), (28309, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p18389309 : Nat.Prime 18389309 := by
  refine Pratt.pratt 18389309 2 [(2, 2), (7, 2), (17, 1), (5519, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p25505633 : Nat.Prime 25505633 := by
  refine Pratt.pratt 25505633 3 [(2, 5), (797051, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p51011267 : Nat.Prime 51011267 := by
  refine Pratt.pratt 51011267 2 [(2, 1), (25505633, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p25505633
theorem p61989379 : Nat.Prime 61989379 := by
  refine Pratt.pratt 61989379 3 [(2, 1), (3, 1), (11, 1), (17, 1), (55249, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p62014751 : Nat.Prime 62014751 := by
  refine Pratt.pratt 62014751 7 [(2, 1), (5, 3), (7, 1), (35437, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p86982781 : Nat.Prime 86982781 := by
  refine Pratt.pratt 86982781 2 [(2, 2), (3, 1), (5, 1), (23, 1), (63031, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p119938883 : Nat.Prime 119938883 := by
  refine Pratt.pratt 119938883 2 [(2, 1), (7, 1), (23, 1), (372481, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p155925157 : Nat.Prime 155925157 := by
  refine Pratt.pratt 155925157 2 [(2, 2), (3, 1), (17, 1), (764339, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p200747959 : Nat.Prime 200747959 := by
  refine Pratt.pratt 200747959 21 [(2, 1), (3, 1), (19, 1), (1760947, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p239877767 : Nat.Prime 239877767 := by
  refine Pratt.pratt 239877767 5 [(2, 1), (119938883, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p119938883
theorem p260571497 : Nat.Prime 260571497 := by
  refine Pratt.pratt 260571497 3 [(2, 3), (29, 1), (211, 1), (5323, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p416733743 : Nat.Prime 416733743 := by
  refine Pratt.pratt 416733743 5 [(2, 1), (229, 1), (909899, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p663350899 : Nat.Prime 663350899 := by
  refine Pratt.pratt 663350899 3 [(2, 1), (3, 1), (7, 1), (953, 1), (16573, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p979676419 : Nat.Prime 979676419 := by
  refine Pratt.pratt 979676419 10 [(2, 1), (3, 1), (7, 1), (1301, 1), (17929, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p1152285787 : Nat.Prime 1152285787 := by
  refine Pratt.pratt 1152285787 2 [(2, 1), (3, 2), (23, 2), (121013, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p1471144721 : Nat.Prime 1471144721 := by
  refine Pratt.pratt 1471144721 3 [(2, 4), (5, 1), (18389309, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p18389309
theorem p2266160251 : Nat.Prime 2266160251 := by
  refine Pratt.pratt 2266160251 2 [(2, 1), (3, 1), (5, 3), (71, 1), (42557, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p2290485653 : Nat.Prime 2290485653 := by
  refine Pratt.pratt 2290485653 3 [(2, 2), (7, 1), (13, 1), (6292543, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p2602814681 : Nat.Prime 2602814681 := by
  refine Pratt.pratt 2602814681 3 [(2, 3), (5, 1), (773, 1), (84179, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p5211429941 : Nat.Prime 5211429941 := by
  refine Pratt.pratt 5211429941 2 [(2, 2), (5, 1), (260571497, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p260571497
theorem p15286617677 : Nat.Prime 15286617677 := by
  refine Pratt.pratt 15286617677 2 [(2, 2), (11, 1), (2843, 1), (122203, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p16276762003 : Nat.Prime 16276762003 := by
  refine Pratt.pratt 16276762003 2 [(2, 1), (3, 1), (2039, 1), (1330453, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p26937487583 : Nat.Prime 26937487583 := by
  refine Pratt.pratt 26937487583 5 [(2, 1), (88793, 1), (151687, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p33901027597 : Nat.Prime 33901027597 := by
  refine Pratt.pratt 33901027597 11 [(2, 2), (3, 2), (8111, 1), (116101, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p75119946259 : Nat.Prime 75119946259 := by
  refine Pratt.pratt 75119946259 7 [(2, 1), (3, 1), (7, 1), (19, 1), (163, 1), (577517, 1)] (by norm_num)
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
theorem p89029217729 : Nat.Prime 89029217729 := by
  refine Pratt.pratt 89029217729 3 [(2, 6), (11, 1), (59, 1), (569, 1), (3767, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p97660572019 : Nat.Prime 97660572019 := by
  refine Pratt.pratt 97660572019 3 [(2, 1), (3, 1), (16276762003, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p16276762003
theorem p134092312163 : Nat.Prime 134092312163 := by
  refine Pratt.pratt 134092312163 2 [(2, 1), (21683, 1), (3092107, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p505625314823 : Nat.Prime 505625314823 := by
  refine Pratt.pratt 505625314823 5 [(2, 1), (5569, 1), (6673, 1), (6803, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p669975147409 : Nat.Prime 669975147409 := by
  refine Pratt.pratt 669975147409 19 [(2, 4), (3, 1), (7, 2), (419, 1), (797, 1), (853, 1)] (by norm_num)
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
theorem p857523152159 : Nat.Prime 857523152159 := by
  refine Pratt.pratt 857523152159 7 [(2, 1), (19, 1), (1607, 1), (14042563, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p14042563
theorem p3702965172799 : Nat.Prime 3702965172799 := by
  refine Pratt.pratt 3702965172799 15 [(2, 1), (3, 1), (743, 1), (11399, 1), (72869, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p4251316630877 : Nat.Prime 4251316630877 := by
  refine Pratt.pratt 4251316630877 2 [(2, 2), (7, 1), (67, 1), (2266160251, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p2266160251
theorem p6860185217273 : Nat.Prime 6860185217273 := by
  refine Pratt.pratt 6860185217273 3 [(2, 3), (857523152159, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p857523152159
theorem p8848343528467 : Nat.Prime 8848343528467 := by
  refine Pratt.pratt 8848343528467 2 [(2, 1), (3, 1), (13, 1), (196879, 1), (576193, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p9159683491381 : Nat.Prime 9159683491381 := by
  refine Pratt.pratt 9159683491381 7 [(2, 2), (3, 1), (5, 1), (167, 1), (859, 1), (1064191, 1)] (by norm_num)
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
theorem p11478095562077 : Nat.Prime 11478095562077 := by
  refine Pratt.pratt 11478095562077 2 [(2, 2), (11, 1), (13, 1), (43, 1), (229, 1), (337, 1), (6047, 1)] (by norm_num)
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
theorem p17335024445719 : Nat.Prime 17335024445719 := by
  refine Pratt.pratt 17335024445719 3 [(2, 1), (3, 4), (7, 1), (15286617677, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p15286617677
theorem p42898278107323 : Nat.Prime 42898278107323 := by
  refine Pratt.pratt 42898278107323 3 [(2, 1), (3, 3), (11, 1), (29, 1), (4423, 1), (563039, 1)] (by norm_num)
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
theorem p1198326151920127 : Nat.Prime 1198326151920127 := by
  refine Pratt.pratt 1198326151920127 3 [(2, 1), (3, 1), (301079, 1), (663350899, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p663350899
theorem p2819054420367257 : Nat.Prime 2819054420367257 := by
  refine Pratt.pratt 2819054420367257 3 [(2, 3), (881, 1), (7841, 1), (51011267, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p51011267
theorem p5691773229139691 : Nat.Prime 5691773229139691 := by
  refine Pratt.pratt 5691773229139691 2 [(2, 1), (5, 1), (7, 1), (11, 1), (41, 1), (127, 1), (373, 1), (3805927, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p10245191812451429 : Nat.Prime 10245191812451429 := by
  refine Pratt.pratt 10245191812451429 2 [(2, 2), (7, 1), (61, 1), (1151, 1), (5211429941, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p5211429941
theorem p19107099763020767 : Nat.Prime 19107099763020767 := by
  refine Pratt.pratt 19107099763020767 5 [(2, 1), (7, 1), (149, 1), (9159683491381, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p9159683491381
theorem p45534185833117529 : Nat.Prime 45534185833117529 := by
  refine Pratt.pratt 45534185833117529 3 [(2, 3), (5691773229139691, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p5691773229139691
theorem p46246848392875127 : Nat.Prime 46246848392875127 := by
  refine Pratt.pratt 46246848392875127 5 [(2, 1), (401, 1), (4403699, 1), (13094537, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p13094537
theorem p46246848392876167 : Nat.Prime 46246848392876167 := by
  refine Pratt.pratt 46246848392876167 3 [(2, 1), (3, 2), (7, 1), (223, 1), (353, 1), (601, 1), (7758139, 1)] (by norm_num)
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
theorem p88089672331629091 : Nat.Prime 88089672331629091 := by
  refine Pratt.pratt 88089672331629091 2 [(2, 1), (3, 2), (5, 1), (29, 1), (47, 1), (733, 1), (979676419, 1)] (by norm_num)
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
  · exact p979676419
theorem p88089672331630139 : Nat.Prime 88089672331630139 := by
  refine Pratt.pratt 88089672331630139 2 [(2, 1), (13, 2), (389, 1), (669975147409, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p669975147409
theorem p89219242873419107 : Nat.Prime 89219242873419107 := by
  refine Pratt.pratt 89219242873419107 2 [(2, 1), (7, 1), (1721, 1), (3702965172799, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p3702965172799
theorem p89219242873420159 : Nat.Prime 89219242873420159 := by
  refine Pratt.pratt 89219242873420159 3 [(2, 1), (3, 1), (61989379, 1), (239877767, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p61989379
  · exact p239877767
theorem p98436147540371287 : Nat.Prime 98436147540371287 := by
  refine Pratt.pratt 98436147540371287 3 [(2, 1), (3, 1), (71, 1), (457, 1), (505625314823, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p505625314823
theorem p98436147540372353 : Nat.Prime 98436147540372353 := by
  refine Pratt.pratt 98436147540372353 3 [(2, 7), (67, 1), (11478095562077, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p11478095562077
theorem p139033656446725643 : Nat.Prime 139033656446725643 := by
  refine Pratt.pratt 139033656446725643 2 [(2, 1), (7, 2), (149, 1), (4157, 1), (2290485653, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p2290485653
theorem p139033656446726737 : Nat.Prime 139033656446726737 := by
  refine Pratt.pratt 139033656446726737 5 [(2, 4), (3, 2), (370949, 1), (2602814681, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p2602814681
theorem p198887512806988729 : Nat.Prime 198887512806988729 := by
  refine Pratt.pratt 198887512806988729 7 [(2, 3), (3, 1), (59, 1), (173, 1), (159899, 1), (5077529, 1)] (by norm_num)
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
theorem p198887512806989843 : Nat.Prime 198887512806989843 := by
  refine Pratt.pratt 198887512806989843 2 [(2, 1), (11, 1), (92569, 1), (97660572019, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p97660572019
theorem p203153416523088323 : Nat.Prime 203153416523088323 := by
  refine Pratt.pratt 203153416523088323 2 [(2, 1), (23893, 1), (4251316630877, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p4251316630877
theorem p203153416523089447 : Nat.Prime 203153416523089447 := by
  refine Pratt.pratt 203153416523089447 3 [(2, 1), (3, 1), (17, 1), (67, 1), (71333, 1), (416733743, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p416733743
theorem p236552906662007587 : Nat.Prime 236552906662007587 := by
  refine Pratt.pratt 236552906662007587 7 [(2, 1), (3, 1), (7, 1), (821, 1), (6860185217273, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p6860185217273
theorem p236552906662008731 : Nat.Prime 236552906662008731 := by
  refine Pratt.pratt 236552906662008731 2 [(2, 1), (5, 1), (16079513, 1), (1471144721, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p16079513
  · exact p1471144721
theorem p293464161465135373 : Nat.Prime 293464161465135373 := by
  refine Pratt.pratt 293464161465135373 2 [(2, 2), (3, 3), (23, 1), (1327, 1), (89029217729, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p89029217729
theorem p293464161465136523 : Nat.Prime 293464161465136523 := by
  refine Pratt.pratt 293464161465136523 2 [(2, 1), (7, 1), (23, 1), (103, 1), (8848343528467, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p8848343528467
theorem p400240934741322419 : Nat.Prime 400240934741322419 := by
  refine Pratt.pratt 400240934741322419 2 [(2, 1), (167, 1), (1198326151920127, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p1198326151920127
theorem p400240934741323591 : Nat.Prime 400240934741323591 := by
  refine Pratt.pratt 400240934741323591 3 [(2, 1), (3, 1), (5, 1), (311, 1), (42898278107323, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p42898278107323
theorem p404444692323376357 : Nat.Prime 404444692323376357 := by
  refine Pratt.pratt 404444692323376357 5 [(2, 2), (3, 1), (83, 1), (352403, 1), (1152285787, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p1152285787
theorem p404444692323377543 : Nat.Prime 404444692323377543 := by
  refine Pratt.pratt 404444692323377543 5 [(2, 1), (17, 2), (461, 1), (7561, 1), (200747959, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p200747959
theorem p703390724952490921 : Nat.Prime 703390724952490921 := by
  refine Pratt.pratt 703390724952490921 19 [(2, 3), (3, 1), (5, 1), (43, 1), (4021, 1), (33901027597, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p33901027597
theorem p703390724952492113 : Nat.Prime 703390724952492113 := by
  refine Pratt.pratt 703390724952492113 3 [(2, 4), (599, 1), (977, 1), (75119946259, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p75119946259
theorem p819615344996114321 : Nat.Prime 819615344996114321 := by
  refine Pratt.pratt 819615344996114321 3 [(2, 4), (5, 1), (10245191812451429, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p10245191812451429
theorem p819615344996115523 : Nat.Prime 819615344996115523 := by
  refine Pratt.pratt 819615344996115523 2 [(2, 1), (3, 2), (45534185833117529, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p45534185833117529
theorem p1331711247969025019 : Nat.Prime 1331711247969025019 := by
  refine Pratt.pratt 1331711247969025019 2 [(2, 1), (71, 1), (541, 1), (17335024445719, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p17335024445719
theorem p1331711247969026227 : Nat.Prime 1331711247969026227 := by
  refine Pratt.pratt 1331711247969026227 3 [(2, 1), (3, 3), (353, 1), (521, 1), (134092312163, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p134092312163
theorem p1798556720194308703 : Nat.Prime 1798556720194308703 := by
  refine Pratt.pratt 1798556720194308703 3 [(2, 1), (3, 1), (31, 1), (62014751, 1), (155925157, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p62014751
  · exact p155925157
theorem p1798556720194309967 : Nat.Prime 1798556720194309967 := by
  refine Pratt.pratt 1798556720194309967 10 [(2, 1), (11, 1), (29, 1), (2819054420367257, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p2819054420367257
theorem p2980707563031238363 : Nat.Prime 2980707563031238363 := by
  refine Pratt.pratt 2980707563031238363 2 [(2, 1), (3, 1), (7, 1), (86011, 1), (543097, 1), (1519283, 1)] (by norm_num)
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
theorem p2980707563031239653 : Nat.Prime 2980707563031239653 := by
  refine Pratt.pratt 2980707563031239653 7 [(2, 2), (3, 1), (13, 1), (19107099763020767, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p19107099763020767
theorem p3278018069102480227 : Nat.Prime 3278018069102480227 := by
  refine Pratt.pratt 3278018069102480227 2 [(2, 1), (3, 1), (67, 1), (302711, 1), (26937487583, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p26937487583
theorem p3278018069102481533 : Nat.Prime 3278018069102481533 := by
  refine Pratt.pratt 3278018069102481533 2 [(2, 2), (2909, 1), (3238727, 1), (86982781, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p86982781

def gds_1040 : List ℕ := [
    2, 1891243, 2, 3, 2, 181, 2, 5, 2, 3, 2, 109, 2, 11, 2, 3,
    2, 5, 2, 29, 2, 3, 2, 7, 2, 19, 2, 3, 2, 23, 2, 3257,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 13111289, 2, 3, 2, 5,
    2, 107, 2, 3, 2, 21739, 2, 37, 2, 3, 2, 439, 2, 17, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 1608743, 2, 103, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 349, 2, 3011, 2, 3, 2, 31, 2, 131, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 11, 2, 1777043, 2, 3, 2, 5, 2, 251, 2, 3,
    2, 4835891, 2, 7283, 2, 3, 2, 13, 2, 7, 2, 3, 2, 1471, 2, 5,
    2, 3, 2, 67, 2, 149, 2, 3, 2, 5, 2, 19, 2, 3, 2, 37579147,
    2, 11, 2, 3, 2, 7, 2, 31, 2, 3, 2, 281, 2, 5, 2, 3,
    2, 28661, 2, 7, 2, 3, 2, 5, 2, 47, 2, 3, 2, 93910387, 2, 39020843,
    2, 3, 2, 383, 2, 41, 2, 3, 2, 43, 2, 5, 2, 3, 2, 7,
    2, 29, 2, 3, 2, 5, 2, 61, 2, 3, 2, 37, 2, 7, 2, 3,
    2, 8867, 2, 11, 2, 3, 2, 19, 2, 5, 2, 3, 2, 8269, 2, 13,
    2, 3, 2, 5, 2, 109, 2, 3, 2, 7, 2, 19256651, 2, 3, 2, 73,
    2, 1361, 2, 3, 2, 17929, 2, 5, 2, 3, 2, 29, 2, 19, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 41, 2, 17, 2, 3, 2, 215531, 2, 43,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 1289, 2, 643, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 360649, 2, 311, 2, 3, 2, 11, 2, 13, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 443, 2, 210565057, 2, 3, 2, 5, 2, 2083,
    2, 3, 2, 307, 2, 229, 2, 3, 2, 19, 2, 7, 2, 3, 2, 239999,
    2, 5, 2, 3, 2, 157, 2, 11, 2, 3, 2, 5, 2, 10937, 2, 3,
    2, 13, 2, 168943, 2, 3, 2, 7, 2, 16036591, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 3919, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 293,
    2, 73, 2, 3, 2, 669433, 2, 1733, 2, 3, 2, 1069, 2, 5, 2, 3,
    2, 7, 2, 134989, 2, 3, 2, 5, 2, 11, 2, 3, 2, 197, 2, 7,
    2, 3, 2, 1279181, 2, 1662547, 2, 3, 2, 29, 2, 5, 2, 3, 2, 11,
    2, 3329, 2, 3, 2, 5, 2, 2957, 2, 3, 2, 7, 2, 101, 2, 3,
    2, 71, 2, 47, 2, 3, 2, 1823, 2, 5, 2, 3, 2, 31, 2, 83,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 241, 2, 11, 2, 3, 2, 496669,
    2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 59, 2, 97177, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 17, 2, 1453, 2, 3, 2, 13, 2, 44809,
    2, 3, 2, 36791, 2, 5, 2, 3, 2, 139, 2, 31, 2, 3, 2, 5,
    2, 43, 2, 3, 2, 67, 2, 13, 2, 3, 2, 151, 2, 7, 2, 3,
    2, 47, 2, 5, 2, 3, 2, 89, 2, 2631527, 2, 3, 2, 5, 2, 10659919,
    2, 3, 2, 11, 2, 61, 2, 3, 2, 7, 2, 17, 2, 3, 2, 239,
    2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 863, 2, 3,
    2, 727, 2, 19, 2, 3, 2, 29, 2, 34519, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 53, 2, 3, 2, 1279,
    2, 7, 2, 3, 2, 11, 2, 1604131, 2, 3, 2, 433, 2, 5, 2, 3,
    2, 2003, 2, 277, 2, 3, 2, 5, 2, 5437, 2, 3, 2, 7, 2, 127,
    2, 3, 2, 9421, 2, 191, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19,
    2, 11, 2, 3, 2, 5, 2, 11839, 2, 3, 2, 173, 2, 137, 2, 3,
    2, 683, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 43, 2, 921517,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 877, 2, 29, 2, 3, 2, 23,
    2, 37, 2, 3, 2, 53, 2, 5, 2, 3, 2, 89759281, 2, 47, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 13, 2, 21587, 2, 3, 2, 29059, 2, 7,
    2, 3, 2, 41, 2, 5, 2, 3, 2, 11, 2, 10091, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 29, 2, 17, 2, 3, 2, 7, 2, 349, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 761389, 2, 7, 2, 3, 2, 5, 2, 139,
    2, 3, 2, 337, 2, 11, 2, 3, 2, 17, 2, 23, 2, 3, 2, 223,
    2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 367, 2, 3,
    2, 31, 2, 7, 2, 3, 2, 317, 2, 151, 2, 3, 2, 59, 2, 5,
    2, 3, 2, 613, 2, 521, 2, 3, 2, 5, 2, 113, 2, 3, 2, 7,
    2, 7331, 2, 3, 2, 37, 2, 11, 2, 3, 2, 71, 2, 5, 2, 3,
    2, 283, 2, 109, 2, 3, 2, 5, 2, 29, 2, 3, 2, 11, 2, 31,
    2, 3, 2, 13, 2, 10139, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17,
    2, 2731357, 2, 3, 2, 5, 2, 7, 2, 3, 2, 6473, 2, 13, 2, 3,
    2, 487, 2, 61, 2, 3, 2, 67, 2, 5, 2, 3, 2, 227, 2, 37,
    2, 3, 2, 5, 2, 23, 2, 3, 2, 4817, 2, 241, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 233, 2, 5, 2, 3, 2, 491, 2, 4441, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 665557, 2, 4643, 2, 3, 2, 7, 2, 953,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 41, 2, 7, 2, 3, 2, 5,
    2, 11804167, 2, 3, 2, 17, 2, 47, 2, 3, 2, 31, 2, 52489, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 7, 2, 8659921, 2, 3, 2, 5, 2]

/-- Table 9 row: the prime after 46246848392875127 is 46246848392875127 + 1040. -/
theorem gap9_1040 : IsGapAt 46246848392875127 1040 :=
  isGapAt_of 46246848392875127 1040 (p46246848392875127) (by show Nat.Prime 46246848392876167; exact p46246848392876167) gds_1040 (by decide +kernel)

def gds_1048 : List ℕ := [
    2, 3, 2, 5, 2, 79, 2, 3, 2, 7, 2, 102356351, 2, 3, 2, 19,
    2, 229, 2, 3, 2, 53, 2, 5, 2, 3, 2, 29, 2, 1231, 2, 3,
    2, 5, 2, 806903, 2, 3, 2, 1733, 2, 11, 2, 3, 2, 13, 2, 23,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 103, 2, 17, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 61, 2, 13, 2, 3, 2, 1033, 2, 7823, 2, 3,
    2, 285569, 2, 5, 2, 3, 2, 115466789, 2, 2491847, 2, 3, 2, 5, 2, 101,
    2, 3, 2, 31, 2, 59, 2, 3, 2, 191, 2, 7, 2, 3, 2, 43,
    2, 5, 2, 3, 2, 83, 2, 41, 2, 3, 2, 5, 2, 6473, 2, 3,
    2, 11, 2, 2411, 2, 3, 2, 7, 2, 67, 2, 3, 2, 109, 2, 5,
    2, 3, 2, 277, 2, 7, 2, 3, 2, 5, 2, 619, 2, 3, 2, 509,
    2, 17, 2, 3, 2, 149, 2, 19, 2, 3, 2, 37, 2, 5, 2, 3,
    2, 7, 2, 1741, 2, 3, 2, 5, 2, 23, 2, 3, 2, 4373, 2, 7,
    2, 3, 2, 11, 2, 43, 2, 3, 2, 13, 2, 5, 2, 3, 2, 97,
    2, 112589, 2, 3, 2, 5, 2, 175179887, 2, 3, 2, 7, 2, 5007983, 2, 3,
    2, 52957067, 2, 13, 2, 3, 2, 23, 2, 5, 2, 3, 2, 1451, 2, 11,
    2, 3, 2, 5, 2, 37, 2, 3, 2, 233, 2, 139, 2, 3, 2, 1911083,
    2, 151, 2, 3, 2, 7, 2, 5, 2, 3, 2, 934001, 2, 131, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 13, 2, 19, 2, 3, 2, 31, 2, 223,
    2, 3, 2, 15439, 2, 5, 2, 3, 2, 17, 2, 447859, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 263, 2, 3187, 2, 3, 2, 3457, 2, 7, 2, 3,
    2, 79, 2, 5, 2, 3, 2, 11, 2, 307, 2, 3, 2, 5, 2, 3586811,
    2, 3, 2, 53, 2, 10371563, 2, 3, 2, 7, 2, 31, 2, 3, 2, 4461887,
    2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 23, 2, 11, 2, 3, 2, 29, 2, 78313841, 2, 3, 2, 563, 2, 5,
    2, 3, 2, 7, 2, 617, 2, 3, 2, 5, 2, 19, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 67, 2, 173, 2, 3, 2, 1103, 2, 5, 2, 3,
    2, 88853, 2, 71, 2, 3, 2, 5, 2, 163, 2, 3, 2, 7, 2, 167,
    2, 3, 2, 13, 2, 11, 2, 3, 2, 683, 2, 5, 2, 3, 2, 41,
    2, 83, 2, 3, 2, 5, 2, 43, 2, 3, 2, 11, 2, 13, 2, 3,
    2, 73, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 51277883, 2, 79,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 8719, 2, 29, 2, 3, 2, 197,
    2, 137, 2, 3, 2, 17, 2, 5, 2, 3, 2, 23, 2, 19, 2, 3,
    2, 5, 2, 47, 2, 3, 2, 199, 2, 751, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 131, 2, 5, 2, 3, 2, 20106253, 2, 13, 2, 3, 2, 5,
    2, 1399, 2, 3, 2, 29, 2, 53, 2, 3, 2, 7, 2, 61, 2, 3,
    2, 71, 2, 5, 2, 3, 2, 157, 2, 7, 2, 3, 2, 5, 2, 2731,
    2, 3, 2, 349, 2, 953, 2, 3, 2, 19, 2, 232307, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 2521, 2, 3,
    2, 47, 2, 7, 2, 3, 2, 37, 2, 13, 2, 3, 2, 269, 2, 5,
    2, 3, 2, 43, 2, 22027, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7,
    2, 211, 2, 3, 2, 23, 2, 113, 2, 3, 2, 27449, 2, 5, 2, 3,
    2, 11, 2, 719597, 2, 3, 2, 5, 2, 29, 2, 3, 2, 13, 2, 17,
    2, 3, 2, 103, 2, 2777, 2, 3, 2, 7, 2, 5, 2, 3, 2, 39623,
    2, 37, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 11, 2, 3,
    2, 17, 2, 5381, 2, 3, 2, 419, 2, 5, 2, 3, 2, 5113, 2, 31,
    2, 3, 2, 5, 2, 197831, 2, 3, 2, 181, 2, 733, 2, 3, 2, 5672413,
    2, 7, 2, 3, 2, 599, 2, 5, 2, 3, 2, 13, 2, 179, 2, 3,
    2, 5, 2, 1129, 2, 3, 2, 202931, 2, 149, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 137, 2, 5, 2, 3, 2, 107, 2, 7, 2, 3, 2, 5,
    2, 1499, 2, 3, 2, 11, 2, 4648037, 2, 3, 2, 79, 2, 47, 2, 3,
    2, 61, 2, 5, 2, 3, 2, 7, 2, 59, 2, 3, 2, 5, 2, 2979049,
    2, 3, 2, 20271557, 2, 7, 2, 3, 2, 13, 2, 353, 2, 3, 2, 569,
    2, 5, 2, 3, 2, 37, 2, 29, 2, 3, 2, 5, 2, 71, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 11, 2, 41, 2, 3, 2, 151, 2, 5,
    2, 3, 2, 271, 2, 53, 2, 3, 2, 5, 2, 17, 2, 3, 2, 523,
    2, 103, 2, 3, 2, 43, 2, 5309, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 29, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 37,
    2, 3, 2, 727, 2, 199, 2, 3, 2, 11, 2, 5, 2, 3, 2, 19,
    2, 13, 2, 3, 2, 5, 2, 8521, 2, 3, 2, 41, 2, 67, 2, 3,
    2, 6131, 2, 7, 2, 3, 2, 5029261, 2, 5, 2, 3, 2, 127249, 2, 183498551,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 1579, 2, 43, 2, 3, 2, 7,
    2, 17, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 5, 2, 952873, 2, 3, 2, 9377, 2, 1373, 2, 3, 2, 769, 2, 13,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 89, 2, 3, 2, 5,
    2, 16747, 2, 3, 2, 31, 2, 7, 2, 3, 2, 4933, 2, 309031, 2, 3,
    2, 19, 2, 5, 2, 3, 2]

/-- Table 9 row: the prime after 88089672331629091 is 88089672331629091 + 1048. -/
theorem gap9_1048 : IsGapAt 88089672331629091 1048 :=
  isGapAt_of 88089672331629091 1048 (p88089672331629091) (by show Nat.Prime 88089672331630139; exact p88089672331630139) gds_1048 (by decide +kernel)

def gds_1052 : List ℕ := [
    2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 37, 2, 1019, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 11, 2, 17, 2, 3, 2, 97, 2, 13,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 67, 2, 151, 2, 3, 2, 5,
    2, 647, 2, 3, 2, 14650541, 2, 2099, 2, 3, 2, 17, 2, 7, 2, 3,
    2, 293, 2, 5, 2, 3, 2, 207661, 2, 19, 2, 3, 2, 5, 2, 269034791,
    2, 3, 2, 13, 2, 37, 2, 3, 2, 7, 2, 41, 2, 3, 2, 28001,
    2, 5, 2, 3, 2, 6733, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 103, 2, 59, 2, 3, 2, 12653, 2, 29, 2, 3, 2, 31, 2, 5,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 14906383, 2, 3, 2, 18493,
    2, 7, 2, 3, 2, 19, 2, 541, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 13, 2, 71, 2, 3, 2, 5, 2, 1423, 2, 3, 2, 7, 2, 23,
    2, 3, 2, 29, 2, 2963, 2, 3, 2, 61, 2, 5, 2, 3, 2, 77569,
    2, 10651, 2, 3, 2, 5, 2, 11, 2, 3, 2, 211, 2, 919, 2, 3,
    2, 276043, 2, 43, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 97,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 37, 2, 528137, 2, 3, 2, 13,
    2, 4139, 2, 3, 2, 1033, 2, 5, 2, 3, 2, 193, 2, 157, 2, 3,
    2, 5, 2, 83, 2, 3, 2, 17, 2, 11, 2, 3, 2, 127, 2, 7,
    2, 3, 2, 16538891, 2, 5, 2, 3, 2, 53, 2, 557, 2, 3, 2, 5,
    2, 25153, 2, 3, 2, 22043107, 2, 29, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 71, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5, 2, 103,
    2, 3, 2, 163, 2, 643, 2, 3, 2, 337, 2, 11, 2, 3, 2, 28867,
    2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 3465139, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 23, 2, 179, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 613, 2, 31, 2, 3, 2, 5, 2, 191, 2, 3, 2, 7,
    2, 619, 2, 3, 2, 1471, 2, 257, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 18418177, 2, 1061, 2, 3, 2, 5, 2, 6217, 2, 3, 2, 811, 2, 19,
    2, 3, 2, 11, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 214849,
    2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 67, 2, 653, 2, 3,
    2, 467, 2, 23, 2, 3, 2, 37, 2, 5, 2, 3, 2, 247099, 2, 11,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 13, 2, 711209, 2, 3, 2, 101,
    2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 19, 2, 53, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 9833, 2, 1583, 2, 3, 2, 7, 2, 181,
    2, 3, 2, 14347, 2, 5, 2, 3, 2, 1789, 2, 7, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 2741, 2, 17, 2, 3, 2, 1733, 2, 79, 2, 3,
    2, 33149, 2, 5, 2, 3, 2, 7, 2, 479, 2, 3, 2, 5, 2, 31,
    2, 3, 2, 73, 2, 7, 2, 3, 2, 17, 2, 9005149, 2, 3, 2, 16729409,
    2, 5, 2, 3, 2, 7356463, 2, 41, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 53, 2, 15461, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 97, 2, 461917, 2, 3, 2, 5, 2, 26927, 2, 3, 2, 10116811,
    2, 211, 2, 3, 2, 13, 2, 3343, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 43, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 8311, 2, 13,
    2, 3, 2, 1301, 2, 11, 2, 3, 2, 41, 2, 5, 2, 3, 2, 17,
    2, 61, 2, 3, 2, 5, 2, 45678977, 2, 3, 2, 11, 2, 233, 2, 3,
    2, 47, 2, 7, 2, 3, 2, 56207, 2, 5, 2, 3, 2, 29, 2, 331,
    2, 3, 2, 5, 2, 73, 2, 3, 2, 6301, 2, 113, 2, 3, 2, 7,
    2, 21563, 2, 3, 2, 190543, 2, 5, 2, 3, 2, 71, 2, 7, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 4609651, 2, 31, 2, 3, 2, 11, 2, 37,
    2, 3, 2, 12647, 2, 5, 2, 3, 2, 7, 2, 3371, 2, 3, 2, 5,
    2, 137, 2, 3, 2, 17, 2, 7, 2, 3, 2, 277, 2, 409, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 313, 2, 11, 2, 3, 2, 5, 2, 102967,
    2, 3, 2, 7, 2, 97, 2, 3, 2, 1200673, 2, 13, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 10211, 2, 59, 2, 3, 2, 5, 2, 41, 2, 3,
    2, 19, 2, 227, 2, 3, 2, 21121, 2, 17, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 397, 2, 52232497, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13,
    2, 23, 2, 3, 2, 31, 2, 19, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 11, 2, 101, 2, 3, 2, 5, 2, 13, 2, 3, 2, 108102497, 2, 40483,
    2, 3, 2, 37, 2, 7, 2, 3, 2, 257, 2, 5, 2, 3, 2, 23,
    2, 39567277, 2, 3, 2, 5, 2, 30859, 2, 3, 2, 83, 2, 11, 2, 3,
    2, 7, 2, 31, 2, 3, 2, 373, 2, 5, 2, 3, 2, 13, 2, 7,
    2, 3, 2, 5, 2, 151, 2, 3, 2, 263, 2, 103141, 2, 3, 2, 199,
    2, 66533, 2, 3, 2, 571531, 2, 5, 2, 3, 2, 7, 2, 37, 2, 3,
    2, 5, 2, 67, 2, 3, 2, 5881, 2, 7, 2, 3, 2, 41189, 2, 11,
    2, 3, 2, 6337, 2, 5, 2, 3, 2, 73, 2, 23, 2, 3, 2, 5,
    2, 7057, 2, 3, 2, 7, 2, 71, 2, 3, 2, 13, 2, 289896029, 2, 3,
    2, 24533, 2, 5, 2, 3, 2, 127, 2, 52473539, 2, 3, 2, 5, 2, 61,
    2, 3, 2, 137, 2, 13, 2, 3, 2, 23, 2]

/-- Table 9 row: the prime after 89219242873419107 is 89219242873419107 + 1052. -/
theorem gap9_1052 : IsGapAt 89219242873419107 1052 :=
  isGapAt_of 89219242873419107 1052 (p89219242873419107) (by show Nat.Prime 89219242873420159; exact p89219242873420159) gds_1052 (by decide +kernel)

def gds_1066 : List ℕ := [
    2, 3, 2, 7, 2, 29, 2, 3, 2, 17, 2, 249832181, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 41011, 2, 11, 2, 3, 2, 5, 2, 103, 2, 3,
    2, 19, 2, 1093, 2, 3, 2, 47, 2, 13, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 61, 2, 487, 2, 3, 2, 5, 2, 7, 2, 3, 2, 29,
    2, 73, 2, 3, 2, 71, 2, 19, 2, 3, 2, 3779, 2, 5, 2, 3,
    2, 37, 2, 23, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 113,
    2, 3, 2, 43, 2, 7, 2, 3, 2, 61068263, 2, 5, 2, 3, 2, 11,
    2, 53, 2, 3, 2, 5, 2, 13, 2, 3, 2, 13721, 2, 631, 2, 3,
    2, 7, 2, 811, 2, 3, 2, 11287, 2, 5, 2, 3, 2, 367, 2, 7,
    2, 3, 2, 5, 2, 181, 2, 3, 2, 5843, 2, 11, 2, 3, 2, 1543,
    2, 38461, 2, 3, 2, 41, 2, 5, 2, 3, 2, 7, 2, 59, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 9910301, 2, 7, 2, 3, 2, 11987, 2, 191,
    2, 3, 2, 1951, 2, 5, 2, 3, 2, 443, 2, 5923, 2, 3, 2, 5,
    2, 797, 2, 3, 2, 7, 2, 51749, 2, 3, 2, 53, 2, 11, 2, 3,
    2, 163, 2, 5, 2, 3, 2, 257, 2, 44633, 2, 3, 2, 5, 2, 281,
    2, 3, 2, 11, 2, 236063, 2, 3, 2, 13, 2, 605177, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 19, 2, 6883, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 6827, 2, 13, 2, 3, 2, 2347, 2, 17, 2, 3, 2, 109817243, 2, 5,
    2, 3, 2, 59, 2, 173, 2, 3, 2, 5, 2, 19, 2, 3, 2, 37,
    2, 31, 2, 3, 2, 11, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 47, 2, 5962867, 2, 3, 2, 5, 2, 41, 2, 3, 2, 10177, 2, 79,
    2, 3, 2, 7, 2, 677, 2, 3, 2, 89, 2, 5, 2, 3, 2, 199,
    2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 83, 2, 8047037, 2, 3,
    2, 29680213, 2, 8017, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 17,
    2, 3, 2, 5, 2, 131577221, 2, 3, 2, 14629, 2, 7, 2, 3, 2, 1174231,
    2, 353, 2, 3, 2, 13, 2, 5, 2, 3, 2, 29, 2, 19, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 7, 2, 269, 2, 3, 2, 31, 2, 13,
    2, 3, 2, 193943, 2, 5, 2, 3, 2, 11, 2, 43, 2, 3, 2, 5,
    2, 299406421, 2, 3, 2, 787, 2, 457, 2, 3, 2, 22470053, 2, 67, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 619, 2, 167, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 13, 2, 11, 2, 3, 2, 19, 2, 31, 2, 3, 2, 71,
    2, 5, 2, 3, 2, 2833, 2, 73, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 46807, 2, 9631, 2, 3, 2, 17, 2, 7, 2, 3, 2, 37, 2, 5,
    2, 3, 2, 148471, 2, 39570017, 2, 3, 2, 5, 2, 61, 2, 3, 2, 23,
    2, 431, 2, 3, 2, 7, 2, 11, 2, 3, 2, 227, 2, 5, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 5, 2, 5779, 2, 3, 2, 11, 2, 41,
    2, 3, 2, 250301, 2, 52102873, 2, 3, 2, 29, 2, 5, 2, 3, 2, 7,
    2, 2060749, 2, 3, 2, 5, 2, 37, 2, 3, 2, 19, 2, 7, 2, 3,
    2, 109, 2, 21997, 2, 3, 2, 31, 2, 5, 2, 3, 2, 17, 2, 134683849,
    2, 3, 2, 5, 2, 112297, 2, 3, 2, 7, 2, 23, 2, 3, 2, 11,
    2, 19, 2, 3, 2, 59, 2, 5, 2, 3, 2, 79, 2, 4273, 2, 3,
    2, 5, 2, 137, 2, 3, 2, 7529, 2, 13, 2, 3, 2, 211, 2, 313,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 11, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 150197, 2, 83, 2, 3, 2, 311, 2, 29, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 7039, 2, 101, 2, 3, 2, 5, 2, 127,
    2, 3, 2, 17, 2, 5309, 2, 3, 2, 67, 2, 7, 2, 3, 2, 709,
    2, 5, 2, 3, 2, 6633899, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 47317, 2, 19, 2, 3, 2, 7, 2, 1328269, 2, 3, 2, 1123, 2, 5,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 71, 2, 3, 2, 61,
    2, 186227, 2, 3, 2, 241, 2, 17, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 7, 2, 37447, 2, 3, 2, 5, 2, 79, 2, 3, 2, 10277713, 2, 7,
    2, 3, 2, 23, 2, 13, 2, 3, 2, 17, 2, 5, 2, 3, 2, 19,
    2, 5355307, 2, 3, 2, 5, 2, 670177, 2, 3, 2, 7, 2, 379, 2, 3,
    2, 131, 2, 261407, 2, 3, 2, 53, 2, 5, 2, 3, 2, 83, 2, 31,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 13, 2, 29, 2, 3, 2, 89,
    2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 1217, 2, 17, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 11, 2, 61, 2, 3, 2, 1597, 2, 23,
    2, 3, 2, 101, 2, 5, 2, 3, 2, 71, 2, 271, 2, 3, 2, 5,
    2, 227559911, 2, 3, 2, 29, 2, 157, 2, 3, 2, 277, 2, 7, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 13, 2, 197, 2, 3, 2, 5, 2, 43,
    2, 3, 2, 269, 2, 10009, 2, 3, 2, 7, 2, 1212853, 2, 3, 2, 563,
    2, 5, 2, 3, 2, 75181, 2, 7, 2, 3, 2, 5, 2, 193, 2, 3,
    2, 3527, 2, 17, 2, 3, 2, 59, 2, 521, 2, 3, 2, 2467, 2, 5,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 1627, 2, 3, 2, 5039,
    2, 7, 2, 3, 2, 13, 2, 3739, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 20431, 2, 37, 2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 19, 2, 26777, 2, 3, 2]

/-- Table 9 row: the prime after 98436147540371287 is 98436147540371287 + 1066. -/
theorem gap9_1066 : IsGapAt 98436147540371287 1066 :=
  isGapAt_of 98436147540371287 1066 (p98436147540371287) (by show Nat.Prime 98436147540372353; exact p98436147540372353) gds_1066 (by decide +kernel)

def gds_1094 : List ℕ := [
    2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 89, 2, 7, 2, 3, 2, 11, 2, 17, 2, 3, 2, 41, 2, 5,
    2, 3, 2, 19, 2, 23, 2, 3, 2, 5, 2, 431, 2, 3, 2, 7,
    2, 2617, 2, 3, 2, 239, 2, 46477, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 1061, 2, 11, 2, 3, 2, 5, 2, 19, 2, 3, 2, 59, 2, 139,
    2, 3, 2, 23, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 37,
    2, 73, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17863, 2, 5563, 2, 3,
    2, 150493459, 2, 25127, 2, 3, 2, 4242233, 2, 5, 2, 3, 2, 31, 2, 17,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 1789, 2, 3, 2, 7561,
    2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 11, 2, 1303, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 607, 2, 37, 2, 3, 2, 7, 2, 23,
    2, 3, 2, 56311, 2, 5, 2, 3, 2, 229, 2, 7, 2, 3, 2, 5,
    2, 41, 2, 3, 2, 173, 2, 11, 2, 3, 2, 3089, 2, 191, 2, 3,
    2, 2239, 2, 5, 2, 3, 2, 7, 2, 6829, 2, 3, 2, 5, 2, 67,
    2, 3, 2, 1830391, 2, 7, 2, 3, 2, 61, 2, 170944051, 2, 3, 2, 461,
    2, 5, 2, 3, 2, 29, 2, 26062063, 2, 3, 2, 5, 2, 99079, 2, 3,
    2, 7, 2, 883, 2, 3, 2, 17, 2, 11, 2, 3, 2, 2423, 2, 5,
    2, 3, 2, 41, 2, 3181, 2, 3, 2, 5, 2, 585911, 2, 3, 2, 11,
    2, 35339, 2, 3, 2, 13, 2, 823, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 1993, 2, 70607, 2, 3, 2, 5, 2, 7, 2, 3, 2, 37, 2, 13,
    2, 3, 2, 127, 2, 113, 2, 3, 2, 206083, 2, 5, 2, 3, 2, 577,
    2, 45707, 2, 3, 2, 5, 2, 53, 2, 3, 2, 1123, 2, 181, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 17, 2, 443,
    2, 3, 2, 5, 2, 31, 2, 3, 2, 19, 2, 131, 2, 3, 2, 7,
    2, 18142591, 2, 3, 2, 73, 2, 5, 2, 3, 2, 109, 2, 7, 2, 3,
    2, 5, 2, 199, 2, 3, 2, 163, 2, 179, 2, 3, 2, 47, 2, 19,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 1951, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 263, 2, 7, 2, 3, 2, 313, 2, 149, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 5507, 2, 2870761, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 233, 2, 3, 2, 20113, 2, 13, 2, 3, 2, 151,
    2, 5, 2, 3, 2, 11, 2, 107, 2, 3, 2, 5, 2, 1223, 2, 3,
    2, 23, 2, 55663, 2, 3, 2, 79, 2, 197, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 4003, 2, 307, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13,
    2, 11, 2, 3, 2, 379, 2, 17, 2, 3, 2, 37, 2, 5, 2, 3,
    2, 18143, 2, 103, 2, 3, 2, 5, 2, 13, 2, 3, 2, 10303, 2, 31,
    2, 3, 2, 251, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 1553,
    2, 127, 2, 3, 2, 5, 2, 37561, 2, 3, 2, 191, 2, 23, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 61, 2, 5, 2, 3, 2, 13, 2, 7,
    2, 3, 2, 5, 2, 37, 2, 3, 2, 11, 2, 1711049, 2, 3, 2, 9521,
    2, 67, 2, 3, 2, 1699, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 33289, 2, 7, 2, 3, 2, 12757, 2, 1759,
    2, 3, 2, 3617, 2, 5, 2, 3, 2, 37987, 2, 59, 2, 3, 2, 5,
    2, 7095437, 2, 3, 2, 7, 2, 857, 2, 3, 2, 11, 2, 41, 2, 3,
    2, 95027539, 2, 5, 2, 3, 2, 47, 2, 43, 2, 3, 2, 5, 2, 373,
    2, 3, 2, 853, 2, 13, 2, 3, 2, 1571, 2, 761, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 159569, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 28773181, 2, 17, 2, 3, 2, 149, 2, 31, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 50671, 2, 19, 2, 3, 2, 5, 2, 1873, 2, 3, 2, 29,
    2, 4289, 2, 3, 2, 17, 2, 7, 2, 3, 2, 6342983, 2, 5, 2, 3,
    2, 59, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 167423, 2, 137,
    2, 3, 2, 7, 2, 45599, 2, 3, 2, 337, 2, 5, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 5, 2, 389, 2, 3, 2, 73, 2, 359, 2, 3,
    2, 19, 2, 37, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 127481911,
    2, 3, 2, 5, 2, 523741, 2, 3, 2, 48108553, 2, 7, 2, 3, 2, 1148921,
    2, 13, 2, 3, 2, 31, 2, 5, 2, 3, 2, 17, 2, 751, 2, 3,
    2, 5, 2, 29, 2, 3, 2, 7, 2, 173, 2, 3, 2, 67, 2, 479,
    2, 3, 2, 197, 2, 5, 2, 3, 2, 431, 2, 89, 2, 3, 2, 5,
    2, 139, 2, 3, 2, 13, 2, 317, 2, 3, 2, 71, 2, 11, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 233, 2, 28431937, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 11, 2, 647, 2, 3, 2, 10103, 2, 43, 2, 3, 2, 103,
    2, 5, 2, 3, 2, 61, 2, 467, 2, 3, 2, 5, 2, 73, 2, 3,
    2, 17, 2, 53, 2, 3, 2, 37, 2, 7, 2, 3, 2, 4201751, 2, 5,
    2, 3, 2, 13, 2, 4567, 2, 3, 2, 5, 2, 23, 2, 3, 2, 211,
    2, 167, 2, 3, 2, 7, 2, 521, 2, 3, 2, 11699, 2, 5, 2, 3,
    2, 12157, 2, 7, 2, 3, 2, 5, 2, 223, 2, 3, 2, 881, 2, 547,
    2, 3, 2, 24953, 2, 17, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 5, 2, 63857, 2, 3, 2, 728837, 2, 7, 2, 3,
    2, 13, 2, 28057, 2, 3, 2, 11, 2, 5, 2, 3, 2, 53, 2, 61,
    2, 3, 2, 5, 2]

/-- Table 9 row: the prime after 139033656446725643 is 139033656446725643 + 1094. -/
theorem gap9_1094 : IsGapAt 139033656446725643 1094 :=
  isGapAt_of 139033656446725643 1094 (p139033656446725643) (by show Nat.Prime 139033656446726737; exact p139033656446726737) gds_1094 (by decide +kernel)

def gds_1114 : List ℕ := [
    2, 3, 2, 7, 2, 5, 2, 3, 2, 67, 2, 387397, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 2081, 2, 11, 2, 3, 2, 211, 2, 13, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 311, 2, 353, 2, 3, 2, 5, 2, 227,
    2, 3, 2, 43, 2, 343118551, 2, 3, 2, 59, 2, 7, 2, 3, 2, 29,
    2, 5, 2, 3, 2, 1403137, 2, 19, 2, 3, 2, 5, 2, 9049, 2, 3,
    2, 13, 2, 181, 2, 3, 2, 7, 2, 11, 2, 3, 2, 22618691, 2, 5,
    2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11,
    2, 41, 2, 3, 2, 12329, 2, 179, 2, 3, 2, 3118699, 2, 5, 2, 3,
    2, 7, 2, 11155051, 2, 3, 2, 5, 2, 43, 2, 3, 2, 2591, 2, 7,
    2, 3, 2, 19, 2, 10711919, 2, 3, 2, 1483, 2, 5, 2, 3, 2, 13,
    2, 73, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 1489, 2, 3,
    2, 11, 2, 29, 2, 3, 2, 113, 2, 5, 2, 3, 2, 491, 2, 3167,
    2, 3, 2, 5, 2, 2273, 2, 3, 2, 17, 2, 47, 2, 3, 2, 106681,
    2, 131, 2, 3, 2, 7, 2, 5, 2, 3, 2, 215351, 2, 11, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 2011, 2, 2225063, 2, 3, 2, 13, 2, 127,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 53, 2, 2887, 2, 3, 2, 5,
    2, 67979, 2, 3, 2, 19, 2, 13, 2, 3, 2, 4831, 2, 7, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 409, 2, 1702061, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 31, 2, 59, 2, 3, 2, 7, 2, 19, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 83, 2, 3,
    2, 151, 2, 892531, 2, 3, 2, 28581053, 2, 409237, 2, 3, 2, 383, 2, 5,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 983, 2, 3, 2, 433,
    2, 7, 2, 3, 2, 449, 2, 41, 2, 3, 2, 277363, 2, 5, 2, 3,
    2, 4204097, 2, 17, 2, 3, 2, 5, 2, 3241969, 2, 3, 2, 7, 2, 61231123,
    2, 3, 2, 710531, 2, 941, 2, 3, 2, 13, 2, 5, 2, 3, 2, 98605621,
    2, 1847, 2, 3, 2, 5, 2, 257, 2, 3, 2, 23, 2, 19, 2, 3,
    2, 20219, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 1607, 2, 106453,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 197, 2, 3, 2, 2293,
    2, 211, 2, 3, 2, 73, 2, 5, 2, 3, 2, 105542933, 2, 53, 2, 3,
    2, 5, 2, 37, 2, 3, 2, 13, 2, 17, 2, 3, 2, 31, 2, 7,
    2, 3, 2, 83, 2, 5, 2, 3, 2, 19, 2, 277, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 227, 2, 23, 2, 3, 2, 7, 2, 208686859, 2, 3,
    2, 24203, 2, 5, 2, 3, 2, 971, 2, 7, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 251, 2, 3301, 2, 3, 2, 1844837, 2, 31, 2, 3, 2, 370483801,
    2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 587, 2, 3,
    2, 79, 2, 7, 2, 3, 2, 43, 2, 12342823, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 47, 2, 3613, 2, 3, 2, 5, 2, 348431, 2, 3, 2, 7,
    2, 1373, 2, 3, 2, 100682849, 2, 73, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 17, 2, 18041, 2, 3, 2, 5, 2, 11, 2, 3, 2, 2287, 2, 151,
    2, 3, 2, 13, 2, 71, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11,
    2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 22501, 2, 13, 2, 3,
    2, 2927, 2, 11863, 2, 3, 2, 31, 2, 5, 2, 3, 2, 12211, 2, 283,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 97, 2, 11, 2, 3, 2, 23,
    2, 7, 2, 3, 2, 239, 2, 5, 2, 3, 2, 947, 2, 29, 2, 3,
    2, 5, 2, 3217, 2, 3, 2, 17, 2, 8501, 2, 3, 2, 7, 2, 79,
    2, 3, 2, 103, 2, 5, 2, 3, 2, 173309, 2, 7, 2, 3, 2, 5,
    2, 107, 2, 3, 2, 1601, 2, 61284437, 2, 3, 2, 127, 2, 11, 2, 3,
    2, 88928153, 2, 5, 2, 3, 2, 7, 2, 317, 2, 3, 2, 5, 2, 47,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 137, 2, 17, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 61, 2, 109, 2, 3, 2, 5, 2, 757, 2, 3,
    2, 7, 2, 1096201, 2, 3, 2, 181, 2, 13, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 35267, 2, 293, 2, 3, 2, 5, 2, 2297, 2, 3, 2, 19,
    2, 5099, 2, 3, 2, 11, 2, 337, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 31, 2, 41, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 173,
    2, 3, 2, 139, 2, 19, 2, 3, 2, 26641, 2, 5, 2, 3, 2, 101,
    2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 73, 2, 4679, 2, 3,
    2, 743, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 397, 2, 31,
    2, 3, 2, 5, 2, 23, 2, 3, 2, 257, 2, 101467369, 2, 3, 2, 7,
    2, 103, 2, 3, 2, 29, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 107, 2, 21169, 2, 3, 2, 367, 2, 1783,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 5519, 2, 3, 2, 5,
    2, 83629781, 2, 3, 2, 83, 2, 7, 2, 3, 2, 659, 2, 61493, 2, 3,
    2, 107677699, 2, 5, 2, 3, 2, 151213, 2, 59, 2, 3, 2, 5, 2, 36389,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 13, 2, 401, 2, 3, 2, 163,
    2, 5, 2, 3, 2, 2269, 2, 1009, 2, 3, 2, 5, 2, 73, 2, 3,
    2, 307, 2, 13, 2, 3, 2, 1619, 2, 29, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 19, 2, 1747, 2, 3, 2, 5, 2, 7, 2, 3, 2, 5557,
    2, 5417, 2, 3, 2, 36629, 2, 11, 2, 3, 2, 43, 2, 5, 2, 3,
    2, 58147, 2, 30853, 2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 199,
    2, 3, 2, 29, 2, 7, 2, 3, 2]

/-- Table 9 row: the prime after 198887512806988729 is 198887512806988729 + 1114. -/
theorem gap9_1114 : IsGapAt 198887512806988729 1114 :=
  isGapAt_of 198887512806988729 1114 (p198887512806988729) (by show Nat.Prime 198887512806989843; exact p198887512806989843) gds_1114 (by decide +kernel)

def gds_1124 : List ℕ := [
    2, 5, 2, 3, 2, 60103, 2, 293, 2, 3, 2, 5, 2, 3259177, 2, 3,
    2, 17, 2, 13, 2, 3, 2, 149, 2, 29, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 827, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23,
    2, 2327713, 2, 3, 2, 53, 2, 23327, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 31, 2, 509, 2, 3, 2, 5, 2, 83, 2, 3, 2, 107, 2, 6830093,
    2, 3, 2, 29, 2, 7, 2, 3, 2, 19477, 2, 5, 2, 3, 2, 59,
    2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 19, 2, 41, 2, 3,
    2, 7, 2, 139, 2, 3, 2, 17, 2, 5, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 5, 2, 179, 2, 3, 2, 400720843, 2, 23, 2, 3, 2, 37,
    2, 19, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 1069, 2, 3,
    2, 5, 2, 47, 2, 3, 2, 1321, 2, 7, 2, 3, 2, 653, 2, 13,
    2, 3, 2, 73, 2, 5, 2, 3, 2, 23, 2, 17, 2, 3, 2, 5,
    2, 241, 2, 3, 2, 7, 2, 29, 2, 3, 2, 127, 2, 11861959, 2, 3,
    2, 661, 2, 5, 2, 3, 2, 4201, 2, 37, 2, 3, 2, 5, 2, 399667,
    2, 3, 2, 13, 2, 2727121, 2, 3, 2, 392201, 2, 11, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 19441, 2, 113, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 11, 2, 19, 2, 3, 2, 549877, 2, 53, 2, 3, 2, 9787, 2, 5,
    2, 3, 2, 56983, 2, 23, 2, 3, 2, 5, 2, 14210753, 2, 3, 2, 8171,
    2, 17, 2, 3, 2, 167, 2, 7, 2, 3, 2, 33331, 2, 5, 2, 3,
    2, 13, 2, 26701, 2, 3, 2, 5, 2, 31, 2, 3, 2, 503, 2, 223,
    2, 3, 2, 7, 2, 73, 2, 3, 2, 587, 2, 5, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 5, 2, 1721, 2, 3, 2, 607, 2, 1987, 2, 3,
    2, 227, 2, 41, 2, 3, 2, 43, 2, 5, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 213361, 2, 7, 2, 3, 2, 13,
    2, 67, 2, 3, 2, 11, 2, 5, 2, 3, 2, 1811, 2, 5167, 2, 3,
    2, 5, 2, 1044779, 2, 3, 2, 7, 2, 13, 2, 3, 2, 1549, 2, 23,
    2, 3, 2, 12143, 2, 5, 2, 3, 2, 17, 2, 18286141, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 31, 2, 37, 2, 3, 2, 7559, 2, 43, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 11, 2, 127, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 34939, 2, 198659, 2, 3, 2, 71, 2, 1493, 2, 3, 2, 12799,
    2, 5, 2, 3, 2, 28514833, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 11587, 2, 11, 2, 3, 2, 19183, 2, 7, 2, 3, 2, 115429, 2, 5,
    2, 3, 2, 443, 2, 79, 2, 3, 2, 5, 2, 10499, 2, 3, 2, 17,
    2, 42841, 2, 3, 2, 7, 2, 691, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 44917, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 35983, 2, 199,
    2, 3, 2, 19, 2, 11, 2, 3, 2, 11059, 2, 5, 2, 3, 2, 7,
    2, 3343, 2, 3, 2, 5, 2, 53, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 293, 2, 17, 2, 3, 2, 23, 2, 5, 2, 3, 2, 29, 2, 46399,
    2, 3, 2, 5, 2, 719, 2, 3, 2, 7, 2, 149, 2, 3, 2, 31,
    2, 2751391, 2, 3, 2, 17, 2, 5, 2, 3, 2, 5009, 2, 33896633, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 2417, 2, 19249, 2, 3, 2, 11, 2, 109,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 1229, 2, 653927, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 19, 2, 1499, 2, 3, 2, 41, 2, 31, 2, 3,
    2, 53, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 43,
    2, 3, 2, 3967, 2, 373, 2, 3, 2, 240587, 2, 7, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 12241, 2, 47, 2, 3, 2, 5, 2, 1171, 2, 3,
    2, 23, 2, 66161, 2, 3, 2, 7, 2, 46658291, 2, 3, 2, 122377511, 2, 5,
    2, 3, 2, 7393, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 18160469,
    2, 193, 2, 3, 2, 13, 2, 6147937, 2, 3, 2, 29, 2, 5, 2, 3,
    2, 7, 2, 67, 2, 3, 2, 5, 2, 6473977, 2, 3, 2, 289859, 2, 7,
    2, 3, 2, 59, 2, 3877, 2, 3, 2, 31, 2, 5, 2, 3, 2, 12281,
    2, 643, 2, 3, 2, 5, 2, 2357, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 17, 2, 1453, 2, 3, 2, 26437, 2, 5, 2, 3, 2, 151, 2, 41,
    2, 3, 2, 5, 2, 273727, 2, 3, 2, 131, 2, 4914029, 2, 3, 2, 677,
    2, 8039, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 13, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 365389867, 2, 383, 2, 3, 2, 163, 2, 11,
    2, 3, 2, 71, 2, 5, 2, 3, 2, 19, 2, 577, 2, 3, 2, 5,
    2, 11519, 2, 3, 2, 11, 2, 20071, 2, 3, 2, 431, 2, 7, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 17, 2, 289241, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 493993, 2, 61, 2, 3, 2, 7, 2, 13, 2, 3, 2, 11261,
    2, 5, 2, 3, 2, 89, 2, 7, 2, 3, 2, 5, 2, 2988521, 2, 3,
    2, 75781, 2, 8123, 2, 3, 2, 11, 2, 5851, 2, 3, 2, 113999749, 2, 5,
    2, 3, 2, 7, 2, 251, 2, 3, 2, 5, 2, 17, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 23, 2, 217369, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 795251, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 59,
    2, 3, 2, 359, 2, 7457, 2, 3, 2, 11, 2, 5, 2, 3, 2, 67,
    2, 19, 2, 3, 2, 5, 2, 331, 2, 3, 2, 2383, 2, 29, 2, 3,
    2, 1723, 2, 1123, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 16981,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 173, 2, 13807, 2, 3, 2, 47,
    2, 17, 2, 3, 2, 27427, 2, 5, 2, 3, 2, 11, 2, 947, 2, 3,
    2, 5, 2]

/-- Table 9 row: the prime after 203153416523088323 is 203153416523088323 + 1124. -/
theorem gap9_1124 : IsGapAt 203153416523088323 1124 :=
  isGapAt_of 203153416523088323 1124 (p203153416523088323) (by show Nat.Prime 203153416523089447; exact p203153416523089447) gds_1124 (by decide +kernel)

def gds_1144 : List ℕ := [
    2, 3, 2, 1997, 2, 7, 2, 3, 2, 37, 2, 59, 2, 3, 2, 311,
    2, 5, 2, 3, 2, 22283, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 7, 2, 89, 2, 3, 2, 41849, 2, 17, 2, 3, 2, 113, 2, 5,
    2, 3, 2, 11, 2, 76001, 2, 3, 2, 5, 2, 1508687, 2, 3, 2, 19,
    2, 53, 2, 3, 2, 359, 2, 18919, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 1289, 2, 37, 2, 3, 2, 5, 2, 7, 2, 3, 2, 15559, 2, 11,
    2, 3, 2, 83, 2, 13, 2, 3, 2, 43, 2, 5, 2, 3, 2, 16222007,
    2, 41, 2, 3, 2, 5, 2, 2099, 2, 3, 2, 5061757, 2, 307, 2, 3,
    2, 59, 2, 7, 2, 3, 2, 373719883, 2, 5, 2, 3, 2, 2143, 2, 17,
    2, 3, 2, 5, 2, 607, 2, 3, 2, 13, 2, 431, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 179, 2, 5, 2, 3, 2, 53, 2, 7, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 11, 2, 137, 2, 3, 2, 647, 2, 43,
    2, 3, 2, 41, 2, 5, 2, 3, 2, 7, 2, 42863, 2, 3, 2, 5,
    2, 38513773, 2, 3, 2, 23, 2, 7, 2, 3, 2, 31, 2, 12503149, 2, 3,
    2, 109, 2, 5, 2, 3, 2, 13, 2, 15901, 2, 3, 2, 5, 2, 17483,
    2, 3, 2, 7, 2, 17, 2, 3, 2, 11, 2, 330227, 2, 3, 2, 24407,
    2, 5, 2, 3, 2, 151, 2, 389, 2, 3, 2, 5, 2, 25169, 2, 3,
    2, 47, 2, 29, 2, 3, 2, 17, 2, 31, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 2657,
    2, 23, 2, 3, 2, 13, 2, 200257667, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 1759, 2, 157, 2, 3, 2, 5, 2, 19, 2, 3, 2, 29, 2, 13,
    2, 3, 2, 2221, 2, 7, 2, 3, 2, 98717, 2, 5, 2, 3, 2, 23,
    2, 239, 2, 3, 2, 5, 2, 11, 2, 3, 2, 43, 2, 59, 2, 3,
    2, 7, 2, 1531, 2, 3, 2, 197, 2, 5, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 5, 2, 481721, 2, 3, 2, 37097, 2, 59063, 2, 3, 2, 27479,
    2, 149, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 5, 2, 6047, 2, 3, 2, 449084771, 2, 7, 2, 3, 2, 82120303, 2, 83,
    2, 3, 2, 2969, 2, 5, 2, 3, 2, 41, 2, 19, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 7, 2, 73, 2, 3, 2, 137, 2, 47, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 1913, 2, 79081517, 2, 3, 2, 5, 2, 29101,
    2, 3, 2, 17, 2, 67, 2, 3, 2, 23, 2, 11, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 228461, 2, 3019, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 11, 2, 71, 2, 3, 2, 19, 2, 16336091, 2, 3, 2, 5827, 2, 5,
    2, 3, 2, 449, 2, 151129357, 2, 3, 2, 5, 2, 133157, 2, 3, 2, 13,
    2, 1044733, 2, 3, 2, 1499, 2, 7, 2, 3, 2, 47, 2, 5, 2, 3,
    2, 79, 2, 151, 2, 3, 2, 5, 2, 13, 2, 3, 2, 238237, 2, 167,
    2, 3, 2, 7, 2, 23, 2, 3, 2, 17, 2, 5, 2, 3, 2, 31,
    2, 7, 2, 3, 2, 5, 2, 12269, 2, 3, 2, 20611, 2, 41, 2, 3,
    2, 859, 2, 33889, 2, 3, 2, 3347, 2, 5, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 5, 2, 148249, 2, 3, 2, 19, 2, 7, 2, 3, 2, 484536809,
    2, 461, 2, 3, 2, 11, 2, 5, 2, 3, 2, 2729, 2, 17, 2, 3,
    2, 5, 2, 222379, 2, 3, 2, 7, 2, 61, 2, 3, 2, 101, 2, 19,
    2, 3, 2, 37, 2, 5, 2, 3, 2, 29, 2, 49853, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 12503, 2, 4672441, 2, 3, 2, 13, 2, 53, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 11, 2, 479, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 113, 2, 13, 2, 3, 2, 131321, 2, 6238663, 2, 3, 2, 421,
    2, 5, 2, 3, 2, 400647719, 2, 47, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 67, 2, 11, 2, 3, 2, 1160147, 2, 7, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 34267, 2, 1783427, 2, 3, 2, 5, 2, 457, 2, 3, 2, 173,
    2, 19, 2, 3, 2, 7, 2, 659, 2, 3, 2, 2138971, 2, 5, 2, 3,
    2, 397, 2, 7, 2, 3, 2, 5, 2, 18757, 2, 3, 2, 2767, 2, 22343,
    2, 3, 2, 107, 2, 11, 2, 3, 2, 125261, 2, 5, 2, 3, 2, 7,
    2, 1861, 2, 3, 2, 5, 2, 31, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 761, 2, 41, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2, 263,
    2, 3, 2, 5, 2, 25693, 2, 3, 2, 7, 2, 67055071, 2, 3, 2, 43,
    2, 13, 2, 3, 2, 241, 2, 5, 2, 3, 2, 17, 2, 73, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 23, 2, 56909, 2, 3, 2, 11, 2, 257,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 2083, 2, 347, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 13, 2, 1567, 2, 3, 2, 118358407, 2, 71, 2, 3,
    2, 6581, 2, 5, 2, 3, 2, 157, 2, 11, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 31, 2, 43, 2, 3, 2, 269, 2, 7, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 853, 2, 181, 2, 3, 2, 5, 2, 11821, 2, 3,
    2, 17, 2, 23, 2, 3, 2, 7, 2, 139, 2, 3, 2, 1801, 2, 5,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 16267,
    2, 31, 2, 3, 2, 29, 2, 61, 2, 3, 2, 79, 2, 5, 2, 3,
    2, 7, 2, 619, 2, 3, 2, 5, 2, 233, 2, 3, 2, 349, 2, 7,
    2, 3, 2, 97, 2, 17, 2, 3, 2, 7393, 2, 5, 2, 3, 2, 1074251,
    2, 59, 2, 3, 2, 5, 2, 311101283, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 13, 2, 15765499, 2, 3, 2, 17, 2, 5, 2, 3, 2, 1129, 2, 89,
    2, 3, 2, 5, 2, 2707, 2, 3, 2, 4513, 2, 13, 2, 3, 2, 37,
    2, 6953029, 2, 3, 2, 7, 2, 5, 2, 3, 2, 297991, 2, 23, 2, 3,
    2, 5, 2, 7, 2, 3, 2]

/-- Table 9 row: the prime after 236552906662007587 is 236552906662007587 + 1144. -/
theorem gap9_1144 : IsGapAt 236552906662007587 1144 :=
  isGapAt_of 236552906662007587 1144 (p236552906662007587) (by show Nat.Prime 236552906662008731; exact p236552906662008731) gds_1144 (by decide +kernel)

def gds_1150 : List ℕ := [
    2, 3, 2, 67, 2, 151, 2, 3, 2, 503733803, 2, 5, 2, 3, 2, 103,
    2, 272721679, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 17, 2, 3,
    2, 7517, 2, 7, 2, 3, 2, 131104823, 2, 5, 2, 3, 2, 11, 2, 773,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 2179, 2, 3, 2, 7,
    2, 396731981, 2, 3, 2, 37, 2, 5, 2, 3, 2, 101, 2, 7, 2, 3,
    2, 5, 2, 31, 2, 3, 2, 337, 2, 11, 2, 3, 2, 4217, 2, 19,
    2, 3, 2, 159541, 2, 5, 2, 3, 2, 7, 2, 167, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 14369, 2, 7, 2, 3, 2, 4583, 2, 196429, 2, 3,
    2, 2557, 2, 5, 2, 3, 2, 43, 2, 67, 2, 3, 2, 5, 2, 37,
    2, 3, 2, 7, 2, 41, 2, 3, 2, 29, 2, 11, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 17, 2, 541, 2, 3, 2, 5, 2, 2305777, 2, 3,
    2, 11, 2, 21559, 2, 3, 2, 13, 2, 83, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 439, 2, 193, 2, 3, 2, 5, 2, 7, 2, 3, 2, 31,
    2, 13, 2, 3, 2, 241, 2, 227, 2, 3, 2, 109, 2, 5, 2, 3,
    2, 197, 2, 1223, 2, 3, 2, 5, 2, 17, 2, 3, 2, 59, 2, 5393,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 25282399, 2, 5, 2, 3, 2, 306121,
    2, 1019, 2, 3, 2, 5, 2, 6101, 2, 3, 2, 17, 2, 29, 2, 3,
    2, 7, 2, 13903, 2, 3, 2, 28349, 2, 5, 2, 3, 2, 19, 2, 7,
    2, 3, 2, 5, 2, 14081, 2, 3, 2, 23, 2, 142458653, 2, 3, 2, 173,
    2, 165653, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 8287, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 29, 2, 7, 2, 3, 2, 139663, 2, 17,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 17244811, 2, 521, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 7, 2, 151903, 2, 3, 2, 394481, 2, 13, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 11, 2, 14939, 2, 3, 2, 5, 2, 257,
    2, 3, 2, 1847, 2, 23, 2, 3, 2, 31, 2, 41, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 67, 2, 1549, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 13, 2, 11, 2, 3, 2, 106436023, 2, 127, 2, 3, 2, 97, 2, 5,
    2, 3, 2, 23, 2, 17, 2, 3, 2, 5, 2, 13, 2, 3, 2, 47,
    2, 405239, 2, 3, 2, 701, 2, 7, 2, 3, 2, 283, 2, 5, 2, 3,
    2, 89, 2, 7559, 2, 3, 2, 5, 2, 59, 2, 3, 2, 41, 2, 43,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 5737, 2, 5, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 5, 2, 2825981, 2, 3, 2, 11, 2, 1873, 2, 3,
    2, 19, 2, 991, 2, 3, 2, 8447, 2, 5, 2, 3, 2, 7, 2, 23,
    2, 3, 2, 5, 2, 318833, 2, 3, 2, 349, 2, 7, 2, 3, 2, 277,
    2, 199391293, 2, 3, 2, 659, 2, 5, 2, 3, 2, 271, 2, 937751, 2, 3,
    2, 5, 2, 73363, 2, 3, 2, 7, 2, 75167, 2, 3, 2, 11, 2, 401,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 335719, 2, 37, 2, 3, 2, 5,
    2, 10247, 2, 3, 2, 22651, 2, 13, 2, 3, 2, 181, 2, 233, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 33922639, 2, 11, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 19, 2, 51287, 2, 3, 2, 103, 2, 47, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 317, 2, 719, 2, 3, 2, 5, 2, 338426401, 2, 3,
    2, 191146513, 2, 269, 2, 3, 2, 1439, 2, 7, 2, 3, 2, 71, 2, 5,
    2, 3, 2, 17, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 294663497,
    2, 61, 2, 3, 2, 7, 2, 241, 2, 3, 2, 18041, 2, 5, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 5, 2, 15671, 2, 3, 2, 131, 2, 62483137,
    2, 3, 2, 41, 2, 3607, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7,
    2, 43, 2, 3, 2, 5, 2, 17, 2, 3, 2, 163, 2, 7, 2, 3,
    2, 35227, 2, 13, 2, 3, 2, 883, 2, 5, 2, 3, 2, 31, 2, 107309,
    2, 3, 2, 5, 2, 433, 2, 3, 2, 7, 2, 19, 2, 3, 2, 294210187,
    2, 379, 2, 3, 2, 6883, 2, 5, 2, 3, 2, 1171, 2, 251, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 13, 2, 37, 2, 3, 2, 107, 2, 11,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 547, 2, 31, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 11, 2, 103, 2, 3, 2, 53, 2, 17, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 19, 2, 821, 2, 3, 2, 5, 2, 16717633,
    2, 3, 2, 1181, 2, 487, 2, 3, 2, 109, 2, 7, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 13, 2, 41, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 257, 2, 2977861, 2, 3, 2, 7, 2, 137, 2, 3, 2, 43, 2, 5,
    2, 3, 2, 4778567, 2, 7, 2, 3, 2, 5, 2, 9467, 2, 3, 2, 307,
    2, 177476521, 2, 3, 2, 61, 2, 191, 2, 3, 2, 5147, 2, 5, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 5, 2, 71, 2, 3, 2, 37, 2, 7,
    2, 3, 2, 13, 2, 29, 2, 3, 2, 11, 2, 5, 2, 3, 2, 2971,
    2, 149, 2, 3, 2, 5, 2, 743, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 134087, 2, 43, 2, 3, 2, 89, 2, 5, 2, 3, 2, 9221, 2, 19,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 1174727, 2, 34157, 2, 3, 2, 29,
    2, 283, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 1595357, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 34763, 2, 17, 2, 3, 2, 113, 2, 53,
    2, 3, 2, 709, 2, 5, 2, 3, 2, 7103, 2, 13, 2, 3, 2, 5,
    2, 163, 2, 3, 2, 137063323, 2, 11, 2, 3, 2, 17, 2, 7, 2, 3,
    2, 157, 2, 5, 2, 3, 2, 71, 2, 223, 2, 3, 2, 5, 2, 80021,
    2, 3, 2, 311, 2, 79, 2, 3, 2, 7, 2, 1109, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 41, 2, 3,
    2, 31, 2, 29, 2, 3, 2, 25189, 2, 11, 2, 3, 2]

/-- Table 9 row: the prime after 293464161465135373 is 293464161465135373 + 1150. -/
theorem gap9_1150 : IsGapAt 293464161465135373 1150 :=
  isGapAt_of 293464161465135373 1150 (p293464161465135373) (by show Nat.Prime 293464161465136523; exact p293464161465136523) gds_1150 (by decide +kernel)

def gds_1172 : List ℕ := [
    2, 199813, 2, 3, 2, 5, 2, 107, 2, 3, 2, 73, 2, 11, 2, 3,
    2, 7, 2, 31, 2, 3, 2, 17, 2, 5, 2, 3, 2, 3469549, 2, 7,
    2, 3, 2, 5, 2, 164983171, 2, 3, 2, 800213, 2, 29501, 2, 3, 2, 13,
    2, 53, 2, 3, 2, 19427, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3,
    2, 5, 2, 73883, 2, 3, 2, 3217, 2, 7, 2, 3, 2, 113, 2, 11,
    2, 3, 2, 929, 2, 5, 2, 3, 2, 1999, 2, 17, 2, 3, 2, 5,
    2, 41, 2, 3, 2, 7, 2, 47, 2, 3, 2, 23, 2, 1009, 2, 3,
    2, 97, 2, 5, 2, 3, 2, 409, 2, 2269, 2, 3, 2, 5, 2, 4337,
    2, 3, 2, 521, 2, 1193, 2, 3, 2, 9041, 2, 109, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 19, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 1933, 2, 29, 2, 3, 2, 11, 2, 79, 2, 3, 2, 1021, 2, 5,
    2, 3, 2, 41, 2, 151, 2, 3, 2, 5, 2, 19, 2, 3, 2, 24953,
    2, 17, 2, 3, 2, 47, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 523, 2, 11, 2, 3, 2, 5, 2, 7297, 2, 3, 2, 29, 2, 6808793,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 149,
    2, 7, 2, 3, 2, 5, 2, 127, 2, 3, 2, 10456483, 2, 223, 2, 3,
    2, 3980113, 2, 40591, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 2287,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 7, 2, 3, 2, 19211,
    2, 829, 2, 3, 2, 331, 2, 5, 2, 3, 2, 11, 2, 19, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 7, 2, 12917, 2, 3, 2, 11423851, 2, 164363,
    2, 3, 2, 352907, 2, 5, 2, 3, 2, 17, 2, 59, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 2017, 2, 11, 2, 3, 2, 37, 2, 43, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 13, 2, 313, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 1321, 2, 4863589, 2, 3, 2, 19, 2, 363681107, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 7604497, 2, 31, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 3203, 2, 14087, 2, 3, 2, 163, 2, 7, 2, 3, 2, 479, 2, 5,
    2, 3, 2, 76801, 2, 37, 2, 3, 2, 5, 2, 139, 2, 3, 2, 11,
    2, 117881, 2, 3, 2, 7, 2, 1373, 2, 3, 2, 103, 2, 5, 2, 3,
    2, 59, 2, 7, 2, 3, 2, 5, 2, 1223, 2, 3, 2, 519316687, 2, 13,
    2, 3, 2, 4567, 2, 6469, 2, 3, 2, 53, 2, 5, 2, 3, 2, 7,
    2, 743, 2, 3, 2, 5, 2, 787, 2, 3, 2, 19, 2, 7, 2, 3,
    2, 11, 2, 17, 2, 3, 2, 387767047, 2, 5, 2, 3, 2, 1871, 2, 29,
    2, 3, 2, 5, 2, 67, 2, 3, 2, 7, 2, 89, 2, 3, 2, 193,
    2, 19, 2, 3, 2, 17, 2, 5, 2, 3, 2, 769, 2, 11, 2, 3,
    2, 5, 2, 467, 2, 3, 2, 179, 2, 283, 2, 3, 2, 97871, 2, 120937093,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 29, 2, 2945669, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 337, 2, 112807, 2, 3, 2, 101, 2, 41, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 22853, 2, 17, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 3701, 2, 23, 2, 3, 2, 3292931, 2, 7, 2, 3, 2, 2953,
    2, 5, 2, 3, 2, 11, 2, 994163, 2, 3, 2, 5, 2, 859, 2, 3,
    2, 3373, 2, 19, 2, 3, 2, 7, 2, 103, 2, 3, 2, 2081, 2, 5,
    2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 47, 2, 3, 2, 13,
    2, 11, 2, 3, 2, 353, 2, 229, 2, 3, 2, 2203, 2, 5, 2, 3,
    2, 7, 2, 4001, 2, 3, 2, 5, 2, 13, 2, 3, 2, 31, 2, 7,
    2, 3, 2, 104048383, 2, 228637, 2, 3, 2, 15937, 2, 5, 2, 3, 2, 19,
    2, 109124731, 2, 3, 2, 5, 2, 2873809, 2, 3, 2, 7, 2, 163, 2, 3,
    2, 17, 2, 11, 2, 3, 2, 29, 2, 5, 2, 3, 2, 13, 2, 23,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 31, 2, 3, 2, 241,
    2, 18973, 2, 3, 2, 7, 2, 5, 2, 3, 2, 43, 2, 1039421, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 37, 2, 109, 2, 3, 2, 23, 2, 16693,
    2, 3, 2, 59, 2, 5, 2, 3, 2, 71, 2, 6866621, 2, 3, 2, 5,
    2, 1069, 2, 3, 2, 30893, 2, 11593, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 17, 2, 3037, 2, 3, 2, 5, 2, 83,
    2, 3, 2, 28477, 2, 13, 2, 3, 2, 7, 2, 29, 2, 3, 2, 107,
    2, 5, 2, 3, 2, 761, 2, 7, 2, 3, 2, 5, 2, 553867, 2, 3,
    2, 4003, 2, 699953, 2, 3, 2, 31, 2, 23, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 7, 2, 2389, 2, 3, 2, 5, 2, 17, 2, 3, 2, 12101,
    2, 7, 2, 3, 2, 29, 2, 67, 2, 3, 2, 3767, 2, 5, 2, 3,
    2, 1152029, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 293,
    2, 3, 2, 19, 2, 31, 2, 3, 2, 6329, 2, 5, 2, 3, 2, 11,
    2, 30212323, 2, 3, 2, 5, 2, 1471, 2, 3, 2, 1621, 2, 2083, 2, 3,
    2, 307, 2, 643, 2, 3, 2, 7, 2, 5, 2, 3, 2, 185832391, 2, 101,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 11597, 2, 11, 2, 3, 2, 301583,
    2, 13, 2, 3, 2, 37, 2, 5, 2, 3, 2, 131, 2, 4789, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 2503, 2, 29, 2, 3, 2, 43, 2, 7,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 1567, 2, 144161, 2, 3, 2, 5,
    2, 89, 2, 3, 2, 13, 2, 209189003, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 241783, 2, 7, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 11, 2, 71, 2, 3, 2, 36467, 2, 19, 2, 3, 2, 410507,
    2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 79, 2, 3,
    2, 251, 2, 7, 2, 3, 2, 237143129, 2, 7361027, 2, 3, 2, 149, 2, 5,
    2, 3, 2, 13, 2, 349, 2, 3, 2, 5, 2, 69761, 2, 3, 2, 7,
    2, 2999, 2, 3, 2, 11, 2, 1319, 2, 3, 2, 41, 2, 5, 2, 3,
    2, 13249, 2]

/-- Table 9 row: the prime after 400240934741322419 is 400240934741322419 + 1172. -/
theorem gap9_1172 : IsGapAt 400240934741322419 1172 :=
  isGapAt_of 400240934741322419 1172 (p400240934741322419) (by show Nat.Prime 400240934741323591; exact p400240934741323591) gds_1172 (by decide +kernel)

def gds_1186 : List ℕ := [
    2, 3, 2, 31, 2, 71, 2, 3, 2, 13, 2, 7, 2, 3, 2, 13397,
    2, 5, 2, 3, 2, 53, 2, 307, 2, 3, 2, 5, 2, 1123, 2, 3,
    2, 73477, 2, 13, 2, 3, 2, 7, 2, 12329, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 61, 2, 7, 2, 3, 2, 5, 2, 3253, 2, 3, 2, 3011,
    2, 19, 2, 3, 2, 43, 2, 47, 2, 3, 2, 255097, 2, 5, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 5, 2, 937, 2, 3, 2, 191, 2, 7,
    2, 3, 2, 364340191, 2, 22343, 2, 3, 2, 11, 2, 5, 2, 3, 2, 23,
    2, 13, 2, 3, 2, 5, 2, 26407, 2, 3, 2, 7, 2, 65609, 2, 3,
    2, 631, 2, 433813, 2, 3, 2, 467, 2, 5, 2, 3, 2, 19, 2, 41,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 147853, 2, 43, 2, 3, 2, 223,
    2, 199, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 61, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 67, 2, 269, 2, 3, 2, 31, 2, 13,
    2, 3, 2, 14081, 2, 5, 2, 3, 2, 7688297, 2, 23, 2, 3, 2, 5,
    2, 13582117, 2, 3, 2, 1283, 2, 11, 2, 3, 2, 312909929, 2, 7, 2, 3,
    2, 41, 2, 5, 2, 3, 2, 151, 2, 53, 2, 3, 2, 5, 2, 2843,
    2, 3, 2, 13, 2, 275911, 2, 3, 2, 7, 2, 31, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 396119, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 284659, 2, 167, 2, 3, 2, 46447, 2, 11, 2, 3, 2, 59, 2, 5,
    2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 107, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 127, 2, 193, 2, 3, 2, 26686747, 2, 5, 2, 3,
    2, 13, 2, 4113929, 2, 3, 2, 5, 2, 236762093, 2, 3, 2, 7, 2, 363752449,
    2, 3, 2, 29, 2, 23, 2, 3, 2, 190663801, 2, 5, 2, 3, 2, 17,
    2, 47, 2, 3, 2, 5, 2, 529864219, 2, 3, 2, 37, 2, 641, 2, 3,
    2, 11, 2, 4153, 2, 3, 2, 7, 2, 5, 2, 3, 2, 1019, 2, 109,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 32029, 2, 73, 2, 3, 2, 13,
    2, 101, 2, 3, 2, 347, 2, 5, 2, 3, 2, 217221881, 2, 11, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 45484051, 2, 13, 2, 3, 2, 56873, 2, 7,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 113, 2, 2143, 2, 3, 2, 5,
    2, 434573, 2, 3, 2, 17, 2, 29, 2, 3, 2, 7, 2, 4723, 2, 3,
    2, 2293, 2, 5, 2, 3, 2, 41, 2, 7, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 19, 2, 79, 2, 3, 2, 176927, 2, 2083, 2, 3, 2, 809,
    2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 149, 2, 3,
    2, 29, 2, 7, 2, 3, 2, 6829, 2, 17, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 23651701, 2, 151, 2, 3, 2, 5, 2, 61, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 373, 2, 53, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 31, 2, 127, 2, 3, 2, 5, 2, 5189, 2, 3, 2, 71, 2, 228731,
    2, 3, 2, 83, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 157,
    2, 78787, 2, 3, 2, 5, 2, 7, 2, 3, 2, 101, 2, 223, 2, 3,
    2, 167, 2, 11, 2, 3, 2, 322591, 2, 5, 2, 3, 2, 179, 2, 17,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 11, 2, 19, 2, 3, 2, 59,
    2, 7, 2, 3, 2, 1709, 2, 5, 2, 3, 2, 17137, 2, 173, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 23, 2, 197, 2, 3, 2, 7, 2, 43,
    2, 3, 2, 35747, 2, 5, 2, 3, 2, 743, 2, 7, 2, 3, 2, 5,
    2, 104717, 2, 3, 2, 22619, 2, 251, 2, 3, 2, 11, 2, 821, 2, 3,
    2, 97, 2, 5, 2, 3, 2, 7, 2, 487447, 2, 3, 2, 5, 2, 67,
    2, 3, 2, 269, 2, 7, 2, 3, 2, 47, 2, 2711, 2, 3, 2, 797,
    2, 5, 2, 3, 2, 122188993, 2, 11, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 7, 2, 23, 2, 3, 2, 17, 2, 163, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 36467, 2, 263, 2, 3, 2, 5, 2, 991, 2, 3, 2, 61,
    2, 11119, 2, 3, 2, 13, 2, 71647, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 23, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13691, 2, 13,
    2, 3, 2, 109, 2, 78283, 2, 3, 2, 19, 2, 5, 2, 3, 2, 11,
    2, 73, 2, 3, 2, 5, 2, 247786901, 2, 3, 2, 43, 2, 5113, 2, 3,
    2, 66343, 2, 7, 2, 3, 2, 8101, 2, 5, 2, 3, 2, 17, 2, 19,
    2, 3, 2, 5, 2, 53, 2, 3, 2, 1590343, 2, 11, 2, 3, 2, 7,
    2, 37, 2, 3, 2, 521791, 2, 5, 2, 3, 2, 6133, 2, 7, 2, 3,
    2, 5, 2, 97, 2, 3, 2, 131, 2, 61, 2, 3, 2, 253159, 2, 83,
    2, 3, 2, 240073, 2, 5, 2, 3, 2, 7, 2, 29191, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 31, 2, 7, 2, 3, 2, 19, 2, 11, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 1063, 2, 1138741, 2, 3, 2, 5, 2, 79,
    2, 3, 2, 7, 2, 491, 2, 3, 2, 277, 2, 13, 2, 3, 2, 53,
    2, 5, 2, 3, 2, 1342153, 2, 204427, 2, 3, 2, 5, 2, 1511, 2, 3,
    2, 59, 2, 31, 2, 3, 2, 71, 2, 3527, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 47, 2, 1423, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13,
    2, 211, 2, 3, 2, 11, 2, 17, 2, 3, 2, 29, 2, 5, 2, 3,
    2, 133767371, 2, 3343, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 36298733,
    2, 3, 2, 197, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 127,
    2, 11, 2, 3, 2, 5, 2, 571, 2, 3, 2, 193, 2, 4001, 2, 3,
    2, 7, 2, 19, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 7,
    2, 3, 2, 5, 2, 30961387, 2, 3, 2, 3461, 2, 14639, 2, 3, 2, 31,
    2, 67, 2, 3, 2, 73, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 839, 2, 7, 2, 3, 2, 61, 2, 29,
    2, 3, 2, 107, 2, 5, 2, 3, 2, 11, 2, 907, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 7, 2, 1129, 2, 3, 2, 13, 2, 31, 2, 3,
    2]

/-- Table 9 row: the prime after 404444692323376357 is 404444692323376357 + 1186. -/
theorem gap9_1186 : IsGapAt 404444692323376357 1186 :=
  isGapAt_of 404444692323376357 1186 (p404444692323376357) (by show Nat.Prime 404444692323377543; exact p404444692323377543) gds_1186 (by decide +kernel)

def gds_1192 : List ℕ := [
    2, 3, 2, 5, 2, 11, 2, 3, 2, 23, 2, 17, 2, 3, 2, 29,
    2, 7, 2, 3, 2, 1381, 2, 5, 2, 3, 2, 11, 2, 317, 2, 3,
    2, 5, 2, 197, 2, 3, 2, 79, 2, 43, 2, 3, 2, 7, 2, 199,
    2, 3, 2, 103, 2, 5, 2, 3, 2, 1993, 2, 7, 2, 3, 2, 5,
    2, 1109, 2, 3, 2, 13, 2, 11, 2, 3, 2, 2393, 2, 71, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 7, 2, 89, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 97, 2, 7, 2, 3, 2, 2921929, 2, 337, 2, 3, 2, 37,
    2, 5, 2, 3, 2, 1567, 2, 19, 2, 3, 2, 5, 2, 56519, 2, 3,
    2, 7, 2, 29, 2, 3, 2, 139, 2, 11, 2, 3, 2, 563, 2, 5,
    2, 3, 2, 13, 2, 401, 2, 3, 2, 5, 2, 66947753, 2, 3, 2, 11,
    2, 4801, 2, 3, 2, 494125613, 2, 2707, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 31, 2, 41, 2, 3, 2, 5, 2, 7, 2, 3, 2, 29, 2, 60917,
    2, 3, 2, 19, 2, 79, 2, 3, 2, 13487, 2, 5, 2, 3, 2, 1013,
    2, 108211, 2, 3, 2, 5, 2, 17, 2, 3, 2, 71, 2, 853, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 67, 2, 5, 2, 3, 2, 6857, 2, 23,
    2, 3, 2, 5, 2, 607, 2, 3, 2, 17, 2, 13, 2, 3, 2, 7,
    2, 103, 2, 3, 2, 41, 2, 5, 2, 3, 2, 89, 2, 7, 2, 3,
    2, 5, 2, 99119, 2, 3, 2, 17047, 2, 1889, 2, 3, 2, 23, 2, 331,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 43, 2, 3, 2, 5,
    2, 29, 2, 3, 2, 19, 2, 7, 2, 3, 2, 134896963, 2, 17, 2, 3,
    2, 190941007, 2, 5, 2, 3, 2, 251, 2, 13, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 16369, 2, 3, 2, 61, 2, 19, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 11, 2, 1229, 2, 3, 2, 5, 2, 67, 2, 3,
    2, 83, 2, 233, 2, 3, 2, 109, 2, 23, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 6384467, 2, 2483179, 2, 3, 2, 5, 2, 7, 2, 3, 2, 53,
    2, 11, 2, 3, 2, 313, 2, 13, 2, 3, 2, 407302513, 2, 5, 2, 3,
    2, 8269, 2, 17, 2, 3, 2, 5, 2, 31, 2, 3, 2, 167, 2, 1399,
    2, 3, 2, 59, 2, 7, 2, 3, 2, 5197, 2, 5, 2, 3, 2, 35603,
    2, 491, 2, 3, 2, 5, 2, 209471, 2, 3, 2, 13, 2, 19, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 43, 2, 5, 2, 3, 2, 439423001, 2, 7,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 351727, 2, 3, 2, 521,
    2, 21304973, 2, 3, 2, 2791, 2, 5, 2, 3, 2, 7, 2, 8887, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 144524321, 2, 7, 2, 3, 2, 2131, 2, 11491,
    2, 3, 2, 661, 2, 5, 2, 3, 2, 13, 2, 2557, 2, 3, 2, 5,
    2, 72379, 2, 3, 2, 7, 2, 47, 2, 3, 2, 11, 2, 43, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 389, 2, 71089399, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 2237, 2, 647, 2, 3, 2, 7591, 2, 1723, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 838421, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 173, 2, 31, 2, 3, 2, 13, 2, 73, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 311, 2, 37, 2, 3, 2, 5, 2, 227, 2, 3, 2, 66137,
    2, 13, 2, 3, 2, 47, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 17, 2, 591516707, 2, 3, 2, 5, 2, 11, 2, 3, 2, 103, 2, 41,
    2, 3, 2, 7, 2, 15199, 2, 3, 2, 97, 2, 5, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 5, 2, 170565001, 2, 3, 2, 23, 2, 83, 2, 3,
    2, 52009, 2, 149, 2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 43, 2, 7, 2, 3, 2, 31,
    2, 8849, 2, 3, 2, 487, 2, 5, 2, 3, 2, 21383, 2, 5939, 2, 3,
    2, 5, 2, 467, 2, 3, 2, 7, 2, 653, 2, 3, 2, 19, 2, 67,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 37, 2, 13417, 2, 3, 2, 5,
    2, 4542149, 2, 3, 2, 59, 2, 23, 2, 3, 2, 101, 2, 11, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 271, 2, 137, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 11, 2, 29327, 2, 3, 2, 312677, 2, 17, 2, 3, 2, 163,
    2, 5, 2, 3, 2, 23, 2, 3739, 2, 3, 2, 5, 2, 211, 2, 3,
    2, 13, 2, 37, 2, 3, 2, 191, 2, 7, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 83, 2, 347, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19,
    2, 89209, 2, 3, 2, 7, 2, 490535069, 2, 3, 2, 2957, 2, 5, 2, 3,
    2, 30983, 2, 7, 2, 3, 2, 5, 2, 387799, 2, 3, 2, 73, 2, 4649,
    2, 3, 2, 293, 2, 19, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 5, 2, 6047, 2, 3, 2, 277, 2, 7, 2, 3,
    2, 807020677, 2, 6300467, 2, 3, 2, 11, 2, 5, 2, 3, 2, 51307, 2, 349,
    2, 3, 2, 5, 2, 269, 2, 3, 2, 7, 2, 48624341, 2, 3, 2, 23,
    2, 575623, 2, 3, 2, 2099, 2, 5, 2, 3, 2, 43, 2, 11677, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 37, 2, 29, 2, 3, 2, 13, 2, 3181,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 1337363, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 109, 2, 13, 2, 3, 2, 53, 2, 294659, 2, 3,
    2, 34519, 2, 5, 2, 3, 2, 1021, 2, 2063, 2, 3, 2, 5, 2, 73,
    2, 3, 2, 29, 2, 11, 2, 3, 2, 17, 2, 7, 2, 3, 2, 71,
    2, 5, 2, 3, 2, 61, 2, 787, 2, 3, 2, 5, 2, 811, 2, 3,
    2, 227, 2, 18097, 2, 3, 2, 7, 2, 167, 2, 3, 2, 15329, 2, 5,
    2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 47, 2, 3, 2, 194493223,
    2, 11623411, 2, 3, 2, 16361, 2, 11, 2, 3, 2, 20759, 2, 5, 2, 3,
    2, 7, 2, 727, 2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 23767, 2, 89, 2, 3, 2, 13, 2, 5, 2, 3, 2, 17,
    2, 31, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 144967, 2, 3,
    2, 569, 2, 13, 2, 3, 2]

/-- Table 9 row: the prime after 703390724952490921 is 703390724952490921 + 1192. -/
theorem gap9_1192 : IsGapAt 703390724952490921 1192 :=
  isGapAt_of 703390724952490921 1192 (p703390724952490921) (by show Nat.Prime 703390724952492113; exact p703390724952492113) gds_1192 (by decide +kernel)

def gds_1202 : List ℕ := [
    2, 29, 2, 3, 2, 11699257, 2, 13, 2, 3, 2, 109, 2, 5, 2, 3,
    2, 79, 2, 31, 2, 3, 2, 5, 2, 53, 2, 3, 2, 631, 2, 17,
    2, 3, 2, 21642503, 2, 7, 2, 3, 2, 311, 2, 5, 2, 3, 2, 247829,
    2, 7065089, 2, 3, 2, 5, 2, 11287, 2, 3, 2, 11, 2, 313, 2, 3,
    2, 7, 2, 43, 2, 3, 2, 421, 2, 5, 2, 3, 2, 139, 2, 7,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 23, 2, 101, 2, 3, 2, 41,
    2, 19, 2, 3, 2, 61, 2, 5, 2, 3, 2, 7, 2, 227153, 2, 3,
    2, 5, 2, 1861, 2, 3, 2, 199, 2, 7, 2, 3, 2, 11, 2, 149,
    2, 3, 2, 53, 2, 5, 2, 3, 2, 13, 2, 1237, 2, 3, 2, 5,
    2, 1289, 2, 3, 2, 7, 2, 1609, 2, 3, 2, 103, 2, 37, 2, 3,
    2, 1931, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2, 29,
    2, 3, 2, 167, 2, 23, 2, 3, 2, 479, 2, 433, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 451691, 2, 1249, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 5503, 2, 19, 2, 3, 2, 13, 2, 59, 2, 3, 2, 75869, 2, 5,
    2, 3, 2, 23, 2, 109, 2, 3, 2, 5, 2, 11, 2, 3, 2, 43,
    2, 13, 2, 3, 2, 677, 2, 7, 2, 3, 2, 47, 2, 5, 2, 3,
    2, 11, 2, 41, 2, 3, 2, 5, 2, 19843367, 2, 3, 2, 17, 2, 593,
    2, 3, 2, 7, 2, 137, 2, 3, 2, 4933, 2, 5, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 5, 2, 9479969, 2, 3, 2, 5162653, 2, 11, 2, 3,
    2, 37, 2, 1697, 2, 3, 2, 5350487, 2, 5, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 31, 2, 7, 2, 3, 2, 59,
    2, 17, 2, 3, 2, 41, 2, 5, 2, 3, 2, 263, 2, 29, 2, 3,
    2, 5, 2, 139, 2, 3, 2, 7, 2, 103, 2, 3, 2, 23, 2, 11,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 349, 2, 37, 2, 3, 2, 5,
    2, 743851, 2, 3, 2, 11, 2, 31, 2, 3, 2, 71, 2, 13, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 29, 2, 317, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 839, 2, 61770529, 2, 3, 2, 149, 2, 9719, 2, 3, 2, 307,
    2, 5, 2, 3, 2, 267523, 2, 17, 2, 3, 2, 5, 2, 997, 2, 3,
    2, 13, 2, 97, 2, 3, 2, 11, 2, 7, 2, 3, 2, 269, 2, 5,
    2, 3, 2, 61, 2, 1843579, 2, 3, 2, 5, 2, 13, 2, 3, 2, 2413951,
    2, 89, 2, 3, 2, 7, 2, 5119, 2, 3, 2, 79, 2, 5, 2, 3,
    2, 43, 2, 7, 2, 3, 2, 5, 2, 41, 2, 3, 2, 609556807, 2, 131,
    2, 3, 2, 19, 2, 199, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7,
    2, 107, 2, 3, 2, 5, 2, 3889, 2, 3, 2, 41893, 2, 7, 2, 3,
    2, 1583, 2, 2689, 2, 3, 2, 137, 2, 5, 2, 3, 2, 253639, 2, 5703679,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 59, 2, 3, 2, 17,
    2, 31, 2, 3, 2, 29, 2, 5, 2, 3, 2, 11, 2, 61, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 83, 2, 37, 2, 3, 2, 13, 2, 24113,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 15692437, 2, 24043, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 19, 2, 11, 2, 3, 2, 5232869, 2, 4229, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 617281243, 2, 79, 2, 3, 2, 5, 2, 6529097,
    2, 3, 2, 89, 2, 53, 2, 3, 2, 109, 2, 7, 2, 3, 2, 5777939,
    2, 5, 2, 3, 2, 17, 2, 71, 2, 3, 2, 5, 2, 1259, 2, 3,
    2, 59, 2, 5743, 2, 3, 2, 7, 2, 11, 2, 3, 2, 31, 2, 5,
    2, 3, 2, 19139, 2, 7, 2, 3, 2, 5, 2, 173, 2, 3, 2, 11,
    2, 47, 2, 3, 2, 118688527, 2, 14524487, 2, 3, 2, 863, 2, 5, 2, 3,
    2, 7, 2, 5737, 2, 3, 2, 5, 2, 17, 2, 3, 2, 37, 2, 7,
    2, 3, 2, 29, 2, 683, 2, 3, 2, 13, 2, 5, 2, 3, 2, 53,
    2, 18341, 2, 3, 2, 5, 2, 95166163, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 11, 2, 13, 2, 3, 2, 21997, 2, 5, 2, 3, 2, 8447, 2, 223,
    2, 3, 2, 5, 2, 3449, 2, 3, 2, 1453, 2, 113, 2, 3, 2, 47,
    2, 1283, 2, 3, 2, 7, 2, 5, 2, 3, 2, 24097, 2, 11, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 13, 2, 43, 2, 3, 2, 575689, 2, 17,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 19, 2, 48649, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 10529, 2, 23, 2, 3, 2, 1039, 2, 7, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 31, 2, 1874527, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 101, 2, 233, 2, 3, 2, 7, 2, 67, 2, 3, 2, 127,
    2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 59, 2, 3,
    2, 29, 2, 83, 2, 3, 2, 73, 2, 3011, 2, 3, 2, 283, 2, 5,
    2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 61, 2, 3, 2, 1543,
    2, 7, 2, 3, 2, 79, 2, 85324159, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 1181, 2, 53, 2, 3, 2, 5, 2, 1523, 2, 3, 2, 7, 2, 181,
    2, 3, 2, 13, 2, 41, 2, 3, 2, 29311, 2, 5, 2, 3, 2, 198121727,
    2, 19, 2, 3, 2, 5, 2, 89, 2, 3, 2, 59999, 2, 13, 2, 3,
    2, 3331, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 113, 2, 36457,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 17, 2, 3, 2, 23,
    2, 152860297, 2, 3, 2, 173, 2, 5, 2, 3, 2, 787, 2, 1151, 2, 3,
    2, 5, 2, 349, 2, 3, 2, 41, 2, 73, 2, 3, 2, 17, 2, 7,
    2, 3, 2, 3163, 2, 5, 2, 3, 2, 47, 2, 13, 2, 3, 2, 5,
    2, 71, 2, 3, 2, 130687, 2, 577, 2, 3, 2, 7, 2, 86748107, 2, 3,
    2, 2617, 2, 5, 2, 3, 2, 6421, 2, 7, 2, 3, 2, 5, 2, 31,
    2, 3, 2, 626948533, 2, 211, 2, 3, 2, 761249, 2, 23, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 127, 2, 3,
    2, 653, 2, 7, 2, 3, 2, 67, 2, 13, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 17, 2, 139, 2, 3, 2, 5, 2, 563, 2, 3, 2, 7,
    2]

/-- Table 9 row: the prime after 819615344996114321 is 819615344996114321 + 1202. -/
theorem gap9_1202 : IsGapAt 819615344996114321 1202 :=
  isGapAt_of 819615344996114321 1202 (p819615344996114321) (by show Nat.Prime 819615344996115523; exact p819615344996115523) gds_1202 (by decide +kernel)

def gds_1208 : List ℕ := [
    2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 1421389, 2, 11, 2, 3,
    2, 79, 2, 929, 2, 3, 2, 109, 2, 5, 2, 3, 2, 7, 2, 4243,
    2, 3, 2, 5, 2, 41, 2, 3, 2, 24621479, 2, 7, 2, 3, 2, 167667109,
    2, 28631, 2, 3, 2, 19, 2, 5, 2, 3, 2, 13, 2, 43, 2, 3,
    2, 5, 2, 420271, 2, 3, 2, 7, 2, 17, 2, 3, 2, 97, 2, 11,
    2, 3, 2, 103, 2, 5, 2, 3, 2, 1201, 2, 19, 2, 3, 2, 5,
    2, 202633099, 2, 3, 2, 11, 2, 239, 2, 3, 2, 17, 2, 887, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 41, 2, 167, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 31, 2, 4027, 2, 3, 2, 13, 2, 2459, 2, 3, 2, 855739,
    2, 5, 2, 3, 2, 16447, 2, 283, 2, 3, 2, 5, 2, 599, 2, 3,
    2, 66621991, 2, 13, 2, 3, 2, 11, 2, 7, 2, 3, 2, 67, 2, 5,
    2, 3, 2, 149, 2, 11793469, 2, 3, 2, 5, 2, 29, 2, 3, 2, 53,
    2, 23, 2, 3, 2, 7, 2, 1993, 2, 3, 2, 29663, 2, 5, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 5, 2, 547, 2, 3, 2, 229, 2, 147413663,
    2, 3, 2, 337, 2, 563, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7,
    2, 13, 2, 3, 2, 5, 2, 61, 2, 3, 2, 73, 2, 7, 2, 3,
    2, 17443, 2, 28041113, 2, 3, 2, 47, 2, 5, 2, 3, 2, 4337, 2, 97,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 41, 2, 3, 2, 163,
    2, 103, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 211, 2, 3,
    2, 5, 2, 67, 2, 3, 2, 17, 2, 1583, 2, 3, 2, 31, 2, 13,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 227, 2, 23, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 89, 2, 11, 2, 3, 2, 251677, 2, 607, 2, 3,
    2, 71, 2, 5, 2, 3, 2, 83, 2, 29, 2, 3, 2, 5, 2, 757,
    2, 3, 2, 13, 2, 12791, 2, 3, 2, 23, 2, 7, 2, 3, 2, 241,
    2, 5, 2, 3, 2, 1153584911, 2, 199, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 157, 2, 53, 2, 3, 2, 7, 2, 11, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 3931, 2, 3, 2, 11,
    2, 19, 2, 3, 2, 3011, 2, 571, 2, 3, 2, 47137, 2, 5, 2, 3,
    2, 7, 2, 47, 2, 3, 2, 5, 2, 1093, 2, 3, 2, 9013, 2, 7,
    2, 3, 2, 5797417, 2, 23, 2, 3, 2, 2281, 2, 5, 2, 3, 2, 3701,
    2, 17, 2, 3, 2, 5, 2, 257, 2, 3, 2, 7, 2, 290761, 2, 3,
    2, 11, 2, 727, 2, 3, 2, 31, 2, 5, 2, 3, 2, 19, 2, 307,
    2, 3, 2, 5, 2, 823, 2, 3, 2, 101, 2, 5813, 2, 3, 2, 13,
    2, 41, 2, 3, 2, 7, 2, 5, 2, 3, 2, 541, 2, 11, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 181, 2, 13, 2, 3, 2, 107, 2, 787,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 8839, 2, 61726513, 2, 3, 2, 5,
    2, 43, 2, 3, 2, 193, 2, 17, 2, 3, 2, 59, 2, 7, 2, 3,
    2, 29, 2, 5, 2, 3, 2, 697553, 2, 2269, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 41, 2, 61, 2, 3, 2, 7, 2, 37, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 71, 2, 3,
    2, 96377, 2, 1231, 2, 3, 2, 421, 2, 79, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 343661, 2, 3, 2, 3117553,
    2, 7, 2, 3, 2, 109, 2, 229, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 31, 2, 83, 2, 3, 2, 5, 2, 89, 2, 3, 2, 7, 2, 47507,
    2, 3, 2, 137, 2, 13, 2, 3, 2, 506743, 2, 5, 2, 3, 2, 17,
    2, 53, 2, 3, 2, 5, 2, 653, 2, 3, 2, 1889, 2, 47, 2, 3,
    2, 19, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 43, 2, 31,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 111043, 2, 3, 2, 29,
    2, 370373, 2, 3, 2, 151, 2, 5, 2, 3, 2, 71, 2, 191, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 23, 2, 643, 2, 3, 2, 1009, 2, 7,
    2, 3, 2, 176977, 2, 5, 2, 3, 2, 76781, 2, 692852123, 2, 3, 2, 5,
    2, 1831, 2, 3, 2, 17, 2, 59, 2, 3, 2, 7, 2, 829, 2, 3,
    2, 1141271, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 15887,
    2, 3, 2, 19, 2, 97, 2, 3, 2, 41, 2, 251, 2, 3, 2, 113,
    2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 22885579, 2, 3,
    2, 1787, 2, 7, 2, 3, 2, 301447, 2, 17, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 179, 2, 337, 2, 3, 2, 5, 2, 103, 2, 3, 2, 7,
    2, 181, 2, 3, 2, 13, 2, 386543, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 23, 2, 397, 2, 3, 2, 5, 2, 11, 2, 3, 2, 29, 2, 13,
    2, 3, 2, 791851, 2, 22861, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11,
    2, 413228437, 2, 3, 2, 5, 2, 7, 2, 3, 2, 977, 2, 3733, 2, 3,
    2, 67, 2, 61, 2, 3, 2, 258437, 2, 5, 2, 3, 2, 37, 2, 17,
    2, 3, 2, 5, 2, 269, 2, 3, 2, 257, 2, 11, 2, 3, 2, 43,
    2, 7, 2, 3, 2, 9661, 2, 5, 2, 3, 2, 313, 2, 13, 2, 3,
    2, 5, 2, 1013, 2, 3, 2, 6803, 2, 1559, 2, 3, 2, 7, 2, 53,
    2, 3, 2, 631, 2, 5, 2, 3, 2, 4073, 2, 7, 2, 3, 2, 5,
    2, 29, 2, 3, 2, 31, 2, 37, 2, 3, 2, 23, 2, 11, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 7, 2, 197, 2, 3, 2, 5, 2, 561191,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 11027, 2, 13, 2, 3, 2, 41,
    2, 5, 2, 3, 2, 47, 2, 67, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 7, 2, 31, 2, 3, 2, 17, 2, 853, 2, 3, 2, 739, 2, 5,
    2, 3, 2, 83334791, 2, 1414993, 2, 3, 2, 5, 2, 409, 2, 3, 2, 13,
    2, 271, 2, 3, 2, 11, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 2113, 2, 474555713, 2, 3, 2, 5, 2, 7, 2, 3, 2, 2801, 2, 127,
    2, 3, 2, 199, 2, 83, 2, 3, 2, 19, 2, 5, 2, 3, 2, 107,
    2, 11, 2, 3, 2, 5, 2]

/-- Table 9 row: the prime after 1331711247969025019 is 1331711247969025019 + 1208. -/
theorem gap9_1208 : IsGapAt 1331711247969025019 1208 :=
  isGapAt_of 1331711247969025019 1208 (p1331711247969025019) (by show Nat.Prime 1331711247969026227; exact p1331711247969026227) gds_1208 (by decide +kernel)

def gds_1264 : List ℕ := [
    2, 3, 2, 149, 2, 1277321753, 2, 3, 2, 263, 2, 5, 2, 3, 2, 29,
    2, 79589, 2, 3, 2, 5, 2, 71, 2, 3, 2, 4591, 2, 23, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 487, 2, 5, 2, 3, 2, 911, 2, 20719,
    2, 3, 2, 5, 2, 237949571, 2, 3, 2, 31729, 2, 13, 2, 3, 2, 7,
    2, 139, 2, 3, 2, 89, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3,
    2, 5, 2, 241, 2, 3, 2, 401, 2, 61, 2, 3, 2, 7583, 2, 103,
    2, 3, 2, 179, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5,
    2, 1277, 2, 3, 2, 67, 2, 7, 2, 3, 2, 37, 2, 53, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 19, 2, 13, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 7, 2, 409, 2, 3, 2, 31, 2, 59, 2, 3, 2, 6173,
    2, 5, 2, 3, 2, 71, 2, 23, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 17, 2, 79, 2, 3, 2, 517553, 2, 6389, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 11, 2, 37, 2, 3, 2, 5, 2, 7, 2, 3, 2, 709,
    2, 43, 2, 3, 2, 23, 2, 13, 2, 3, 2, 257177, 2, 5, 2, 3,
    2, 599694869, 2, 7741, 2, 3, 2, 5, 2, 373, 2, 3, 2, 1257009191, 2, 11,
    2, 3, 2, 223, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 173,
    2, 8641, 2, 3, 2, 5, 2, 167, 2, 3, 2, 13, 2, 509, 2, 3,
    2, 7, 2, 367, 2, 3, 2, 17, 2, 5, 2, 3, 2, 269, 2, 7,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 47, 2, 439, 2, 3, 2, 83,
    2, 11, 2, 3, 2, 1409, 2, 5, 2, 3, 2, 7, 2, 309450571, 2, 3,
    2, 5, 2, 10589, 2, 3, 2, 11, 2, 7, 2, 3, 2, 61, 2, 239,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 13, 2, 17, 2, 3, 2, 5,
    2, 41, 2, 3, 2, 7, 2, 27893, 2, 3, 2, 19, 2, 13807, 2, 3,
    2, 73, 2, 5, 2, 3, 2, 3917, 2, 635413, 2, 3, 2, 5, 2, 191,
    2, 3, 2, 349, 2, 47623, 2, 3, 2, 11, 2, 137, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 127, 2, 67763, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 4283, 2, 37, 2, 3, 2, 13, 2, 89, 2, 3, 2, 2039, 2, 5,
    2, 3, 2, 41, 2, 11, 2, 3, 2, 5, 2, 23, 2, 3, 2, 257,
    2, 13, 2, 3, 2, 67271, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 131, 2, 43, 2, 3, 2, 5, 2, 821, 2, 3, 2, 19, 2, 29,
    2, 3, 2, 7, 2, 47, 2, 3, 2, 23, 2, 5, 2, 3, 2, 79,
    2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 103, 2, 59, 2, 3,
    2, 3169, 2, 19, 2, 3, 2, 67, 2, 5, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 5, 2, 1487, 2, 3, 2, 29, 2, 7, 2, 3, 2, 193,
    2, 5417, 2, 3, 2, 53, 2, 5, 2, 3, 2, 977764169, 2, 467, 2, 3,
    2, 5, 2, 2203, 2, 3, 2, 7, 2, 11, 2, 3, 2, 101, 2, 109,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 17, 2, 31, 2, 3, 2, 5,
    2, 1087, 2, 3, 2, 167, 2, 41, 2, 3, 2, 89, 2, 13, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 211, 2, 51721, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 23, 2, 19, 2, 3, 2, 953, 2, 11, 2, 3, 2, 43,
    2, 5, 2, 3, 2, 267049, 2, 157, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 11, 2, 127, 2, 3, 2, 14717, 2, 7, 2, 3, 2, 137, 2, 5,
    2, 3, 2, 1136982061, 2, 7873, 2, 3, 2, 5, 2, 13, 2, 3, 2, 17,
    2, 223, 2, 3, 2, 7, 2, 587, 2, 3, 2, 61, 2, 5, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 5, 2, 103, 2, 3, 2, 97, 2, 23,
    2, 3, 2, 11, 2, 43, 2, 3, 2, 15679, 2, 5, 2, 3, 2, 7,
    2, 2971, 2, 3, 2, 5, 2, 19, 2, 3, 2, 4021, 2, 7, 2, 3,
    2, 4943, 2, 17, 2, 3, 2, 739, 2, 5, 2, 3, 2, 23, 2, 11,
    2, 3, 2, 5, 2, 31, 2, 3, 2, 7, 2, 701, 2, 3, 2, 163,
    2, 181, 2, 3, 2, 11, 2, 5, 2, 3, 2, 332957369, 2, 331, 2, 3,
    2, 5, 2, 151, 2, 3, 2, 73, 2, 719, 2, 3, 2, 13, 2, 179,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 596314349, 2, 29, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 227, 2, 13, 2, 3, 2, 197, 2, 41, 2, 3,
    2, 22307, 2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5, 2, 37,
    2, 3, 2, 53, 2, 419, 2, 3, 2, 572196563, 2, 7, 2, 3, 2, 1220765437,
    2, 5, 2, 3, 2, 29, 2, 246411241, 2, 3, 2, 5, 2, 8461, 2, 3,
    2, 31, 2, 11, 2, 3, 2, 7, 2, 37781, 2, 3, 2, 1549, 2, 5,
    2, 3, 2, 1444459, 2, 7, 2, 3, 2, 5, 2, 1826171, 2, 3, 2, 41,
    2, 193, 2, 3, 2, 19, 2, 337, 2, 3, 2, 4167073, 2, 5, 2, 3,
    2, 7, 2, 107, 2, 3, 2, 5, 2, 73, 2, 3, 2, 2884559, 2, 7,
    2, 3, 2, 129733, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 4373,
    2, 101, 2, 3, 2, 5, 2, 43, 2, 3, 2, 7, 2, 131, 2, 3,
    2, 17, 2, 13, 2, 3, 2, 27466613, 2, 5, 2, 3, 2, 1759, 2, 2713,
    2, 3, 2, 5, 2, 487, 2, 3, 2, 71, 2, 141242159, 2, 3, 2, 225287,
    2, 113, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19717, 2, 211, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 13, 2, 47, 2, 3, 2, 11, 2, 67,
    2, 3, 2, 29, 2, 5, 2, 3, 2, 61, 2, 28036361, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 293, 2, 53, 2, 3, 2, 31, 2, 7, 2, 3,
    2, 1039, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2, 6829,
    2, 3, 2, 941, 2, 163, 2, 3, 2, 7, 2, 86693, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 89, 2, 170114983, 2, 3, 2, 47, 2, 31, 2, 3, 2, 2351, 2, 5,
    2, 3, 2, 7, 2, 131422679, 2, 3, 2, 5, 2, 11, 2, 3, 2, 127,
    2, 7, 2, 3, 2, 41, 2, 29, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 11, 2, 61, 2, 3, 2, 5, 2, 463, 2, 3, 2, 7, 2, 19,
    2, 3, 2, 13, 2, 347, 2, 3, 2, 1601, 2, 5, 2, 3, 2, 3539,
    2, 59, 2, 3, 2, 5, 2, 1451, 2, 3, 2, 3643, 2, 11, 2, 3,
    2, 29, 2, 761, 2, 3, 2, 7, 2, 5, 2, 3, 2, 73, 2, 22111,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 233, 2, 271, 2, 3, 2]

/-- Table 9 row: the prime after 1798556720194308703 is 1798556720194308703 + 1264. -/
theorem gap9_1264 : IsGapAt 1798556720194308703 1264 :=
  isGapAt_of 1798556720194308703 1264 (p1798556720194308703) (by show Nat.Prime 1798556720194309967; exact p1798556720194309967) gds_1264 (by decide +kernel)

def gds_1290 : List ℕ := [
    2, 3, 2, 17, 2, 7, 2, 3, 2, 1433, 2, 5, 2, 3, 2, 223,
    2, 11, 2, 3, 2, 5, 2, 6955589, 2, 3, 2, 13, 2, 23, 2, 3,
    2, 7, 2, 67, 2, 3, 2, 11, 2, 5, 2, 3, 2, 2129, 2, 7,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 31, 2, 3, 2, 41,
    2, 94301149, 2, 3, 2, 4471007, 2, 5, 2, 3, 2, 7, 2, 349, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 137, 2, 7, 2, 3, 2, 83, 2, 19,
    2, 3, 2, 256723, 2, 5, 2, 3, 2, 11, 2, 43, 2, 3, 2, 5,
    2, 46309, 2, 3, 2, 7, 2, 112570433, 2, 3, 2, 73, 2, 103, 2, 3,
    2, 401, 2, 5, 2, 3, 2, 499, 2, 113, 2, 3, 2, 5, 2, 3131017,
    2, 3, 2, 1471, 2, 11, 2, 3, 2, 564620299, 2, 141257, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 139, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 2203, 2, 59219, 2, 3, 2, 13, 2, 89, 2, 3, 2, 61, 2, 5,
    2, 3, 2, 18288191, 2, 167, 2, 3, 2, 5, 2, 471101, 2, 3, 2, 17,
    2, 13, 2, 3, 2, 23, 2, 7, 2, 3, 2, 212637013, 2, 5, 2, 3,
    2, 109, 2, 41, 2, 3, 2, 5, 2, 53, 2, 3, 2, 11, 2, 700471,
    2, 3, 2, 7, 2, 31, 2, 3, 2, 29, 2, 5, 2, 3, 2, 173,
    2, 7, 2, 3, 2, 5, 2, 524591, 2, 3, 2, 107, 2, 73, 2, 3,
    2, 19699, 2, 17, 2, 3, 2, 43, 2, 5, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 5, 2, 3347, 2, 3, 2, 37, 2, 7, 2, 3, 2, 11,
    2, 23, 2, 3, 2, 17, 2, 5, 2, 3, 2, 88807, 2, 12163, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 7, 2, 283, 2, 3, 2, 49639, 2, 13090669,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 42526777, 2, 11, 2, 3, 2, 5,
    2, 75320573, 2, 3, 2, 1279, 2, 71, 2, 3, 2, 89, 2, 13, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 127, 2, 17, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 149, 2, 525566401, 2, 3, 2, 407573, 2, 257, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 181, 2, 24019, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 13, 2, 3217, 2, 3, 2, 29, 2, 7, 2, 3, 2, 151, 2, 5,
    2, 3, 2, 11, 2, 19, 2, 3, 2, 5, 2, 13, 2, 3, 2, 1741,
    2, 227, 2, 3, 2, 7, 2, 1117, 2, 3, 2, 59, 2, 5, 2, 3,
    2, 130343, 2, 7, 2, 3, 2, 5, 2, 41, 2, 3, 2, 691, 2, 11,
    2, 3, 2, 3613, 2, 5480947, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7,
    2, 467, 2, 3, 2, 5, 2, 34213, 2, 3, 2, 77795617, 2, 7, 2, 3,
    2, 17, 2, 131, 2, 3, 2, 37, 2, 5, 2, 3, 2, 47, 2, 1777,
    2, 3, 2, 5, 2, 91159, 2, 3, 2, 7, 2, 29, 2, 3, 2, 211,
    2, 11, 2, 3, 2, 105363821, 2, 5, 2, 3, 2, 31, 2, 241, 2, 3,
    2, 5, 2, 101, 2, 3, 2, 11, 2, 643, 2, 3, 2, 13, 2, 293,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 192613, 2, 1709, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 29, 2, 13, 2, 3, 2, 3527, 2, 7249841, 2, 3,
    2, 135391, 2, 5, 2, 3, 2, 17, 2, 31, 2, 3, 2, 5, 2, 43,
    2, 3, 2, 19, 2, 127, 2, 3, 2, 11, 2, 7, 2, 3, 2, 106604699,
    2, 5, 2, 3, 2, 20233, 2, 38653, 2, 3, 2, 5, 2, 10847, 2, 3,
    2, 53, 2, 50386943, 2, 3, 2, 7, 2, 19, 2, 3, 2, 207953, 2, 5,
    2, 3, 2, 7019, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 3607,
    2, 299731, 2, 3, 2, 151939, 2, 59, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 7, 2, 73, 2, 3, 2, 5, 2, 29, 2, 3, 2, 17, 2, 7,
    2, 3, 2, 1091, 2, 32361283, 2, 3, 2, 13, 2, 5, 2, 3, 2, 199,
    2, 317, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 420593881, 2, 3,
    2, 97, 2, 13, 2, 3, 2, 1151, 2, 5, 2, 3, 2, 11, 2, 181,
    2, 3, 2, 5, 2, 41813, 2, 3, 2, 131, 2, 19, 2, 3, 2, 3747703,
    2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 43, 2, 41316907, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 13, 2, 11, 2, 3, 2, 59, 2, 37,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 79, 2, 88214239, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 22391, 2, 67, 2, 3, 2, 78737, 2, 7, 2, 3,
    2, 419, 2, 5, 2, 3, 2, 19, 2, 23, 2, 3, 2, 5, 2, 563,
    2, 3, 2, 39133, 2, 53, 2, 3, 2, 7, 2, 11, 2, 3, 2, 109,
    2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 11, 2, 3313, 2, 3, 2, 23, 2, 2647, 2, 3, 2, 107, 2, 5,
    2, 3, 2, 7, 2, 179, 2, 3, 2, 5, 2, 83, 2, 3, 2, 31,
    2, 7, 2, 3, 2, 5018219, 2, 272417, 2, 3, 2, 2797, 2, 5, 2, 3,
    2, 29, 2, 97, 2, 3, 2, 5, 2, 12037, 2, 3, 2, 7, 2, 163,
    2, 3, 2, 11, 2, 41, 2, 3, 2, 19, 2, 5, 2, 3, 2, 53,
    2, 11202871, 2, 3, 2, 5, 2, 79, 2, 3, 2, 19387, 2, 13, 2, 3,
    2, 1700811403, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 817083409, 2, 11,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 1429, 2, 383, 2, 3, 2, 17,
    2, 411709, 2, 3, 2, 11, 2, 5, 2, 3, 2, 547, 2, 37, 2, 3,
    2, 5, 2, 61, 2, 3, 2, 41, 2, 59, 2, 3, 2, 43, 2, 7,
    2, 3, 2, 681866959, 2, 5, 2, 3, 2, 14243, 2, 13, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 787, 2, 739, 2, 3, 2, 7, 2, 64433, 2, 3,
    2, 47, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 75181927,
    2, 3, 2, 67, 2, 1097, 2, 3, 2, 31, 2, 1753, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 7, 2, 373, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 127, 2, 7, 2, 3, 2, 10799083, 2, 13, 2, 3, 2, 1213, 2, 5,
    2, 3, 2, 103, 2, 617, 2, 3, 2, 5, 2, 24517, 2, 3, 2, 7,
    2, 101, 2, 3, 2, 277859947, 2, 31, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 37, 2, 53, 2, 3, 2, 5, 2, 17, 2, 3, 2, 13, 2, 167,
    2, 3, 2, 857, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 313,
    2, 78853, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 15073, 2, 3,
    2, 733, 2, 19, 2, 3, 2, 197, 2, 5, 2, 3, 2, 6553, 2, 1889,
    2, 3, 2, 5, 2, 89, 2, 3, 2, 14042773, 2, 37, 2, 3, 2, 4283,
    2, 7, 2, 3, 2, 463, 2, 5, 2, 3, 2, 13, 2, 47, 2, 3,
    2, 5, 2, 311, 2, 3, 2, 61, 2]

/-- Table 9 row: the prime after 2980707563031238363 is 2980707563031238363 + 1290. -/
theorem gap9_1290 : IsGapAt 2980707563031238363 1290 :=
  isGapAt_of 2980707563031238363 1290 (p2980707563031238363) (by show Nat.Prime 2980707563031239653; exact p2980707563031239653) gds_1290 (by decide +kernel)

def gds_1306 : List ℕ := [
    2, 3, 2, 11, 2, 41, 2, 3, 2, 47, 2, 19, 2, 3, 2, 33937,
    2, 5, 2, 3, 2, 7, 2, 18253, 2, 3, 2, 5, 2, 11802991, 2, 3,
    2, 29, 2, 7, 2, 3, 2, 3697, 2, 10280593, 2, 3, 2, 59, 2, 5,
    2, 3, 2, 127163, 2, 53, 2, 3, 2, 5, 2, 149, 2, 3, 2, 7,
    2, 67, 2, 3, 2, 11, 2, 3851, 2, 3, 2, 83, 2, 5, 2, 3,
    2, 9127, 2, 101, 2, 3, 2, 5, 2, 17, 2, 3, 2, 224038159, 2, 23,
    2, 3, 2, 13, 2, 127, 2, 3, 2, 7, 2, 5, 2, 3, 2, 43,
    2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 13, 2, 3,
    2, 1291, 2, 1297, 2, 3, 2, 11, 2, 5, 2, 3, 2, 23, 2, 75649999,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 24414199, 2, 44809, 2, 3, 2, 53,
    2, 7, 2, 3, 2, 163, 2, 5, 2, 3, 2, 31, 2, 3330641, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 27943, 2, 287847067, 2, 3, 2, 7, 2, 17,
    2, 3, 2, 4903, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5,
    2, 1423, 2, 3, 2, 10853, 2, 11987, 2, 3, 2, 3061, 2, 757, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 293, 2, 7, 2, 3, 2, 1577554619, 2, 41, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 61, 2, 59368019, 2, 3, 2, 5, 2, 538585123, 2, 3,
    2, 7, 2, 107, 2, 3, 2, 23, 2, 13, 2, 3, 2, 101, 2, 5,
    2, 3, 2, 47, 2, 17, 2, 3, 2, 5, 2, 1303, 2, 3, 2, 61933,
    2, 53836061, 2, 3, 2, 919, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 5849651, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 8501,
    2, 3, 2, 37, 2, 1097, 2, 3, 2, 131, 2, 5, 2, 3, 2, 97,
    2, 19, 2, 3, 2, 5, 2, 13, 2, 3, 2, 621631, 2, 263, 2, 3,
    2, 43, 2, 7, 2, 3, 2, 277, 2, 5, 2, 3, 2, 29, 2, 61,
    2, 3, 2, 5, 2, 651239, 2, 3, 2, 199, 2, 17, 2, 3, 2, 7,
    2, 4451, 2, 3, 2, 1597, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 5, 2, 31, 2, 3, 2, 179, 2, 313423697, 2, 3, 2, 17, 2, 555147589,
    2, 3, 2, 5030239, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5,
    2, 169330039, 2, 3, 2, 185747, 2, 7, 2, 3, 2, 977, 2, 11027, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 135645911, 2, 2879, 2, 3, 2, 5, 2, 47,
    2, 3, 2, 7, 2, 139, 2, 3, 2, 13, 2, 79, 2, 3, 2, 24337,
    2, 5, 2, 3, 2, 6458167, 2, 42223, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 808169, 2, 13, 2, 3, 2, 3617, 2, 3108731, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 11, 2, 72007657, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19,
    2, 97, 2, 3, 2, 6619, 2, 1996229, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 37, 2, 1390929109, 2, 3, 2, 5, 2, 1553, 2, 3, 2, 47, 2, 11,
    2, 3, 2, 41, 2, 7, 2, 3, 2, 113, 2, 5, 2, 3, 2, 141917,
    2, 13, 2, 3, 2, 5, 2, 17, 2, 3, 2, 1399, 2, 31, 2, 3,
    2, 7, 2, 1019, 2, 3, 2, 1087, 2, 5, 2, 3, 2, 87083, 2, 7,
    2, 3, 2, 5, 2, 907, 2, 3, 2, 17, 2, 37, 2, 3, 2, 2743621,
    2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 173, 2, 3,
    2, 5, 2, 1732219, 2, 3, 2, 11, 2, 7, 2, 3, 2, 73, 2, 13,
    2, 3, 2, 8707, 2, 5, 2, 3, 2, 647, 2, 1733, 2, 3, 2, 5,
    2, 53, 2, 3, 2, 7, 2, 19, 2, 3, 2, 1571, 2, 17, 2, 3,
    2, 311533, 2, 5, 2, 3, 2, 229, 2, 43, 2, 3, 2, 5, 2, 110693537,
    2, 3, 2, 13, 2, 3671, 2, 3, 2, 11, 2, 514201, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 505966271, 2, 41, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 59, 2, 827, 2, 3, 2, 103, 2, 47, 2, 3, 2, 71, 2, 5,
    2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 853, 2, 3, 2, 37,
    2, 23, 2, 3, 2, 381511069, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 13, 2, 17, 2, 3, 2, 5, 2, 19, 2, 3, 2, 37171, 2, 73,
    2, 3, 2, 7, 2, 4957, 2, 3, 2, 41, 2, 5, 2, 3, 2, 23,
    2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 84307, 2, 29, 2, 3,
    2, 1217, 2, 10463, 2, 3, 2, 47, 2, 5, 2, 3, 2, 7, 2, 127,
    2, 3, 2, 5, 2, 67, 2, 3, 2, 197, 2, 7, 2, 3, 2, 13,
    2, 1405096169, 2, 3, 2, 19, 2, 5, 2, 3, 2, 101, 2, 2171881, 2, 3,
    2, 5, 2, 181513, 2, 3, 2, 7, 2, 11, 2, 3, 2, 316691, 2, 82051,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 251, 2, 19, 2, 3, 2, 5,
    2, 277, 2, 3, 2, 97, 2, 641, 2, 3, 2, 17, 2, 399613, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 499, 2, 149, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 239, 2, 79, 2, 3, 2, 23, 2, 11, 2, 3, 2, 94541,
    2, 5, 2, 3, 2, 504632729, 2, 13, 2, 3, 2, 5, 2, 41, 2, 3,
    2, 11, 2, 58036049, 2, 3, 2, 19, 2, 7, 2, 3, 2, 37, 2, 5,
    2, 3, 2, 1811, 2, 733, 2, 3, 2, 5, 2, 29, 2, 3, 2, 22945603,
    2, 25821581, 2, 3, 2, 7, 2, 659, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 5, 2, 71, 2, 3, 2, 1471, 2, 31177,
    2, 3, 2, 11, 2, 13, 2, 3, 2, 1579, 2, 5, 2, 3, 2, 7,
    2, 743, 2, 3, 2, 5, 2, 37, 2, 3, 2, 1213943, 2, 7, 2, 3,
    2, 306883, 2, 157, 2, 3, 2, 53629, 2, 5, 2, 3, 2, 31, 2, 11,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 61, 2, 3, 2, 271903,
    2, 233, 2, 3, 2, 11, 2, 5, 2, 3, 2, 107, 2, 1699, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 17, 2, 116009, 2, 3, 2, 14035069, 2, 19,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 281, 2, 31, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 24943, 2, 599, 2, 3, 2, 347, 2, 1049897, 2, 3,
    2, 3691, 2, 5, 2, 3, 2, 11, 2, 29, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 21773, 2, 241, 2, 3, 2, 1129, 2, 7, 2, 3, 2, 214177,
    2, 5, 2, 3, 2, 2017, 2, 4817, 2, 3, 2, 5, 2, 43, 2, 3,
    2, 267037, 2, 11, 2, 3, 2, 7, 2, 191, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 109, 2, 3, 2, 113,
    2, 19, 2, 3, 2, 13, 2, 67, 2, 3, 2, 35401, 2, 5, 2, 3,
    2, 7, 2, 673, 2, 3, 2, 5, 2, 34607, 2, 3, 2, 9511, 2, 7,
    2, 3, 2, 769, 2, 11, 2, 3, 2]

/-- Table 9 row: the prime after 3278018069102480227 is 3278018069102480227 + 1306. -/
theorem gap9_1306 : IsGapAt 3278018069102480227 1306 :=
  isGapAt_of 3278018069102480227 1306 (p3278018069102480227) (by show Nat.Prime 3278018069102481533; exact p3278018069102481533) gds_1306 (by decide +kernel)

end LeanLab.OeSHP2014
