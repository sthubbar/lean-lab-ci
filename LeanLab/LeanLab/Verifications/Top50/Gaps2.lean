/-
Maximal prime gap records, OEIS A002386 part 2: each row `IsGapAt p g`, zero sorry.
Divisors and Pratt certificates found by Python, checked by the Lean kernel.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.GapsBase

namespace LeanLab.Verifications.Top50.Gaps2

open LeanLab.Verifications.Top50.Gaps
open LeanLab.Verifications.Pratt (pB)

theorem p127976334671 : Nat.Prime 127976334671 := by
  refine Pratt.pratt 127976334671 29 [(2, 1), (5, 1), (6607, 1), (1936981, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p127976335139 : Nat.Prime 127976335139 := by
  refine Pratt.pratt 127976335139 2 [(2, 1), (17, 1), (1277, 1), (2947541, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p182226896239 : Nat.Prime 182226896239 := by
  refine Pratt.pratt 182226896239 3 [(2, 1), (3, 1), (86161, 1), (352493, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p182226896713 : Nat.Prime 182226896713 := by
  refine Pratt.pratt 182226896713 5 [(2, 3), (3, 2), (7, 1), (1493, 1), (242171, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p148315267 : Nat.Prime 148315267 := by
  refine Pratt.pratt 148315267 2 [(2, 1), (3, 3), (11, 2), (22699, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p241160624143 : Nat.Prime 241160624143 := by
  refine Pratt.pratt 241160624143 3 [(2, 1), (3, 1), (271, 1), (148315267, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p148315267

theorem p241160624629 : Nat.Prime 241160624629 := by
  refine Pratt.pratt 241160624629 2 [(2, 2), (3, 1), (7, 1), (11, 1), (31, 1), (8419237, 1)] (by norm_num)
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

theorem p72596651 : Nat.Prime 72596651 := by
  refine Pratt.pratt 72596651 2 [(2, 1), (5, 2), (7, 1), (41, 1), (5059, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p297501075799 : Nat.Prime 297501075799 := by
  refine Pratt.pratt 297501075799 3 [(2, 1), (3, 1), (683, 1), (72596651, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p72596651

theorem p297501076289 : Nat.Prime 297501076289 := by
  refine Pratt.pratt 297501076289 3 [(2, 6), (13, 1), (541, 1), (660949, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p303371455241 : Nat.Prime 303371455241 := by
  refine Pratt.pratt 303371455241 3 [(2, 3), (5, 1), (7, 1), (17, 1), (37, 1), (109, 1), (15803, 1)] (by norm_num)
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

theorem p303371455741 : Nat.Prime 303371455741 := by
  refine Pratt.pratt 303371455741 10 [(2, 2), (3, 1), (5, 1), (83, 1), (127, 1), (367, 1), (1307, 1)] (by norm_num)
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

theorem p304599508537 : Nat.Prime 304599508537 := by
  refine Pratt.pratt 304599508537 5 [(2, 3), (3, 1), (109, 1), (113, 1), (1030417, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p304599509 : Nat.Prime 304599509 := by
  refine Pratt.pratt 304599509 2 [(2, 2), (73, 1), (149, 1), (7001, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p6091990181 : Nat.Prime 6091990181 := by
  refine Pratt.pratt 6091990181 2 [(2, 2), (5, 1), (304599509, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p304599509

theorem p304599509051 : Nat.Prime 304599509051 := by
  refine Pratt.pratt 304599509051 2 [(2, 1), (5, 2), (6091990181, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p6091990181

theorem p416608695821 : Nat.Prime 416608695821 := by
  refine Pratt.pratt 416608695821 2 [(2, 2), (5, 1), (2749, 1), (7577459, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p416608696337 : Nat.Prime 416608696337 := by
  refine Pratt.pratt 416608696337 5 [(2, 4), (7, 1), (131, 1), (223, 1), (127331, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p15389683667 : Nat.Prime 15389683667 := by
  refine Pratt.pratt 15389683667 2 [(2, 1), (7, 1), (47, 1), (89, 1), (317, 1), (829, 1)] (by norm_num)
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

theorem p461690510011 : Nat.Prime 461690510011 := by
  refine Pratt.pratt 461690510011 12 [(2, 1), (3, 1), (5, 1), (15389683667, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p15389683667

theorem p13579132663 : Nat.Prime 13579132663 := by
  refine Pratt.pratt 13579132663 3 [(2, 1), (3, 2), (1697, 1), (444547, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p461690510543 : Nat.Prime 461690510543 := by
  refine Pratt.pratt 461690510543 5 [(2, 1), (17, 1), (13579132663, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p13579132663

theorem p614487453523 : Nat.Prime 614487453523 := by
  refine Pratt.pratt 614487453523 2 [(2, 1), (3, 1), (127, 1), (311, 1), (491, 1), (5281, 1)] (by norm_num)
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

theorem p614487454057 : Nat.Prime 614487454057 := by
  refine Pratt.pratt 614487454057 15 [(2, 3), (3, 2), (7, 1), (12377, 1), (98507, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p738832927927 : Nat.Prime 738832927927 := by
  refine Pratt.pratt 738832927927 3 [(2, 1), (3, 1), (1249, 1), (4969, 1), (19841, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p738832928467 : Nat.Prime 738832928467 := by
  refine Pratt.pratt 738832928467 2 [(2, 1), (3, 1), (17, 1), (12953, 1), (559211, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p13397563 : Nat.Prime 13397563 := by
  refine Pratt.pratt 13397563 2 [(2, 1), (3, 8), (1021, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p336573577687 : Nat.Prime 336573577687 := by
  refine Pratt.pratt 336573577687 3 [(2, 1), (3, 1), (53, 1), (79, 1), (13397563, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p13397563

theorem p1346294310749 : Nat.Prime 1346294310749 := by
  refine Pratt.pratt 1346294310749 2 [(2, 2), (336573577687, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p336573577687

theorem p25935163 : Nat.Prime 25935163 := by
  refine Pratt.pratt 25935163 2 [(2, 1), (3, 1), (11, 1), (392957, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p1346294311331 : Nat.Prime 1346294311331 := by
  refine Pratt.pratt 1346294311331 6 [(2, 1), (5, 1), (29, 1), (179, 1), (25935163, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p25935163

theorem p1505016553 : Nat.Prime 1505016553 := by
  refine Pratt.pratt 1505016553 7 [(2, 3), (3, 1), (13, 1), (719, 1), (6709, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p1408695493609 : Nat.Prime 1408695493609 := by
  refine Pratt.pratt 1408695493609 7 [(2, 3), (3, 2), (13, 1), (1505016553, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p1505016553

theorem p117391291183 : Nat.Prime 117391291183 := by
  refine Pratt.pratt 117391291183 5 [(2, 1), (3, 2), (11, 1), (29, 1), (3517, 1), (5813, 1)] (by norm_num)
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

theorem p1408695494197 : Nat.Prime 1408695494197 := by
  refine Pratt.pratt 1408695494197 2 [(2, 2), (3, 1), (117391291183, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p117391291183

theorem p86248403 : Nat.Prime 86248403 := by
  refine Pratt.pratt 86248403 2 [(2, 1), (313, 1), (137777, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p1968188556461 : Nat.Prime 1968188556461 := by
  refine Pratt.pratt 1968188556461 3 [(2, 2), (5, 1), (7, 1), (163, 1), (86248403, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p86248403

theorem p1968188557063 : Nat.Prime 1968188557063 := by
  refine Pratt.pratt 1968188557063 7 [(2, 1), (3, 1), (7, 1), (13, 1), (37, 1), (643, 1), (151517, 1)] (by norm_num)
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

theorem p2614941710599 : Nat.Prime 2614941710599 := by
  refine Pratt.pratt 2614941710599 3 [(2, 1), (3, 1), (7, 1), (71, 1), (1283, 1), (683483, 1)] (by norm_num)
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

theorem p2614941711251 : Nat.Prime 2614941711251 := by
  refine Pratt.pratt 2614941711251 11 [(2, 1), (5, 4), (11, 1), (1187, 1), (160217, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p7008947863 : Nat.Prime 7008947863 := by
  refine Pratt.pratt 7008947863 5 [(2, 1), (3, 1), (7, 1), (809, 1), (206279, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p7177162611713 : Nat.Prime 7177162611713 := by
  refine Pratt.pratt 7177162611713 3 [(2, 10), (7008947863, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p7008947863

theorem p7177162612387 : Nat.Prime 7177162612387 := by
  refine Pratt.pratt 7177162612387 3 [(2, 1), (3, 1), (13, 1), (97, 1), (109, 1), (8702819, 1)] (by norm_num)
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

theorem p12571862327 : Nat.Prime 12571862327 := by
  refine Pratt.pratt 12571862327 5 [(2, 1), (29, 1), (31, 1), (6992137, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p13829048559701 : Nat.Prime 13829048559701 := by
  refine Pratt.pratt 13829048559701 2 [(2, 2), (5, 2), (11, 1), (12571862327, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p12571862327

theorem p13829048560417 : Nat.Prime 13829048560417 := by
  refine Pratt.pratt 13829048560417 5 [(2, 5), (3, 1), (172097, 1), (837043, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p8916818849 : Nat.Prime 8916818849 := by
  refine Pratt.pratt 8916818849 3 [(2, 5), (7, 1), (23, 1), (29, 1), (37, 1), (1613, 1)] (by norm_num)
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

theorem p1087851899579 : Nat.Prime 1087851899579 := by
  refine Pratt.pratt 1087851899579 2 [(2, 1), (61, 1), (8916818849, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p8916818849

theorem p19581334192423 : Nat.Prime 19581334192423 := by
  refine Pratt.pratt 19581334192423 3 [(2, 1), (3, 2), (1087851899579, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p1087851899579

theorem p2102806507 : Nat.Prime 2102806507 := by
  refine Pratt.pratt 2102806507 2 [(2, 1), (3, 1), (263, 1), (367, 1), (3631, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p4895333548297 : Nat.Prime 4895333548297 := by
  refine Pratt.pratt 4895333548297 5 [(2, 3), (3, 1), (97, 1), (2102806507, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p2102806507

theorem p19581334193189 : Nat.Prime 19581334193189 := by
  refine Pratt.pratt 19581334193189 2 [(2, 2), (4895333548297, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p4895333548297

theorem p42842283925351 : Nat.Prime 42842283925351 := by
  refine Pratt.pratt 42842283925351 11 [(2, 1), (3, 1), (5, 2), (7, 1), (13, 1), (17, 1), (37, 1), (419, 1), (11909, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p40856339 : Nat.Prime 40856339 := by
  refine Pratt.pratt 40856339 2 [(2, 1), (17, 1), (941, 1), (1277, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p2677642745383 : Nat.Prime 2677642745383 := by
  refine Pratt.pratt 2677642745383 6 [(2, 1), (3, 2), (11, 1), (331, 1), (40856339, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p40856339

theorem p42842283926129 : Nat.Prime 42842283926129 := by
  refine Pratt.pratt 42842283926129 3 [(2, 4), (2677642745383, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p2677642745383

theorem p90874329411493 : Nat.Prime 90874329411493 := by
  refine Pratt.pratt 90874329411493 2 [(2, 2), (3, 2), (11, 1), (89, 1), (7529, 1), (342467, 1)] (by norm_num)
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

theorem p90874329412297 : Nat.Prime 90874329412297 := by
  refine Pratt.pratt 90874329412297 5 [(2, 3), (3, 1), (1094531, 1), (3459409, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p171231342420521 : Nat.Prime 171231342420521 := by
  refine Pratt.pratt 171231342420521 3 [(2, 3), (5, 1), (3319, 1), (22157, 1), (58211, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p171231342421327 : Nat.Prime 171231342421327 := by
  refine Pratt.pratt 171231342421327 5 [(2, 1), (3, 1), (11, 1), (523, 1), (2909, 1), (1705273, 1)] (by norm_num)
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

def ds_127976334671 : List ℕ := [
    2, 11, 2, 3, 2, 71, 2, 17, 2, 3, 2, 1579, 2, 5,
    2, 3, 2, 7, 2, 31, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 1951, 2, 7, 2, 3, 2, 13, 2, 37, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 359, 2, 59, 2, 3, 2, 5, 2, 313,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 79691, 2, 11, 2, 3,
    2, 997, 2, 5, 2, 3, 2, 122611, 2, 283, 2, 3, 2, 5,
    2, 5003, 2, 3, 2, 11, 2, 919, 2, 3, 2, 1301, 2, 29,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 41, 2, 17, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 40093, 2, 601, 2, 3, 2, 187069,
    2, 44633, 2, 3, 2, 96973, 2, 5, 2, 3, 2, 769, 2, 13,
    2, 3, 2, 5, 2, 17159, 2, 3, 2, 73, 2, 24551, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 59,
    2, 23767, 2, 3, 2, 5, 2, 137, 2, 3, 2, 571, 2, 421,
    2, 3, 2, 7, 2, 311, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 3343, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 113,
    2, 17, 2, 3, 2, 19, 2, 13, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 7, 2, 91193, 2, 3, 2, 5, 2, 163, 2, 3,
    2, 6947, 2, 7, 2, 3, 2, 17, 2, 202031, 2, 3, 2, 97,
    2, 5, 2, 3, 2, 661, 2, 37, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 29, 2, 3, 2, 151, 2, 4297, 2, 3,
    2, 79, 2, 5, 2, 3, 2, 11, 2, 71, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 23, 2, 149, 2, 3, 2, 1237, 2, 127,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 1297, 2, 43, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 19, 2, 11, 2, 3, 2, 17909,
    2, 10589, 2, 3, 2, 9001, 2, 5, 2, 3, 2, 13, 2, 207589,
    2, 3, 2, 5, 2, 227, 2, 3, 2, 4409, 2, 1913, 2, 3,
    2, 2503, 2, 7, 2, 3, 2, 53, 2, 5, 2, 3, 2, 7877,
    2, 67, 2, 3, 2, 5, 2, 20233, 2, 3, 2, 89, 2, 23,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 6073, 2, 5, 2, 3,
    2, 37, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 11,
    2, 2083, 2, 3, 2, 13, 2, 116789, 2, 3, 2, 71, 2, 5,
    2, 3, 2, 7, 2, 79, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 61, 2, 271, 2, 3, 2, 5683,
    2, 5, 2, 3, 2]

/-- A002386 row: the prime after 127976334671 is 127976334671 + 468. -/
theorem gap_127976334671 : IsGapAt 127976334671 468 :=
  isGapAt_of 127976334671 468 (p127976334671) (by show Nat.Prime 127976335139; exact p127976335139) ds_127976334671 (by decide +kernel)

def ds_182226896239 : List ℕ := [
    2, 3, 2, 7, 2, 5, 2, 3, 2, 461, 2, 25939, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 233323, 2, 19, 2, 3, 2, 13,
    2, 11, 2, 3, 2, 304687, 2, 5, 2, 3, 2, 347, 2, 17,
    2, 3, 2, 5, 2, 31, 2, 3, 2, 11, 2, 13, 2, 3,
    2, 163, 2, 7, 2, 3, 2, 383, 2, 5, 2, 3, 2, 61,
    2, 823, 2, 3, 2, 5, 2, 59, 2, 3, 2, 251, 2, 1619,
    2, 3, 2, 7, 2, 47, 2, 3, 2, 281, 2, 5, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 5, 2, 137, 2, 3, 2, 23,
    2, 173, 2, 3, 2, 11, 2, 145091, 2, 3, 2, 401, 2, 5,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 6971, 2, 7, 2, 3, 2, 379, 2, 787, 2, 3, 2, 1087,
    2, 5, 2, 3, 2, 3467, 2, 11, 2, 3, 2, 5, 2, 29,
    2, 3, 2, 7, 2, 208589, 2, 3, 2, 17, 2, 27583, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 467, 2, 61, 2, 3, 2, 5,
    2, 53, 2, 3, 2, 131, 2, 23, 2, 3, 2, 811, 2, 13,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 1657, 2, 265621, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 24001, 2, 31, 2, 3, 2, 761,
    2, 41077, 2, 3, 2, 269, 2, 5, 2, 3, 2, 11, 2, 19,
    2, 3, 2, 5, 2, 71, 2, 3, 2, 13, 2, 97, 2, 3,
    2, 167, 2, 7, 2, 3, 2, 139, 2, 5, 2, 3, 2, 17,
    2, 4093, 2, 3, 2, 5, 2, 13, 2, 3, 2, 127, 2, 11,
    2, 3, 2, 7, 2, 113, 2, 3, 2, 53, 2, 5, 2, 3,
    2, 8669, 2, 7, 2, 3, 2, 5, 2, 521, 2, 3, 2, 73,
    2, 11597, 2, 3, 2, 19, 2, 11087, 2, 3, 2, 41, 2, 5,
    2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 211, 2, 7, 2, 3, 2, 31, 2, 11, 2, 3, 2, 2141,
    2, 5, 2, 3, 2, 67, 2, 47, 2, 3, 2, 5, 2, 12149,
    2, 3, 2, 7, 2, 163, 2, 3, 2, 23, 2, 1039, 2, 3,
    2, 379283, 2, 5, 2, 3, 2, 29, 2, 3323, 2, 3, 2, 5,
    2, 337, 2, 3, 2, 1151, 2, 35089, 2, 3, 2, 13, 2, 31,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 89, 2, 59, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 19, 2, 13, 2, 3, 2, 11,
    2, 17, 2, 3, 2, 293, 2, 5, 2, 3, 2, 173, 2, 43,
    2, 3, 2, 5, 2, 73, 2, 3, 2, 59063, 2]

/-- A002386 row: the prime after 182226896239 is 182226896239 + 474. -/
theorem gap_182226896239 : IsGapAt 182226896239 474 :=
  isGapAt_of 182226896239 474 (p182226896239) (by show Nat.Prime 182226896713; exact p182226896713) ds_182226896239 (by decide +kernel)

def ds_241160624143 : List ℕ := [
    2, 3, 2, 1667, 2, 103, 2, 3, 2, 113363, 2, 5, 2, 3,
    2, 7, 2, 859, 2, 3, 2, 5, 2, 23, 2, 3, 2, 149,
    2, 7, 2, 3, 2, 11, 2, 191, 2, 3, 2, 1291, 2, 5,
    2, 3, 2, 19, 2, 79, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 7, 2, 179, 2, 3, 2, 17, 2, 193, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 109, 2, 11, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 127, 2, 37, 2, 3, 2, 13, 2, 317, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 8747, 2, 10847, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 457, 2, 13, 2, 3, 2, 92363, 2, 353,
    2, 3, 2, 43, 2, 5, 2, 3, 2, 293, 2, 71, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 97, 2, 269, 2, 3, 2, 3169,
    2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 11, 2, 47,
    2, 3, 2, 5, 2, 521, 2, 3, 2, 113, 2, 12703, 2, 3,
    2, 7, 2, 136057, 2, 3, 2, 2081, 2, 5, 2, 3, 2, 1361,
    2, 7, 2, 3, 2, 5, 2, 2027, 2, 3, 2, 23, 2, 11,
    2, 3, 2, 25169, 2, 43, 2, 3, 2, 1489, 2, 5, 2, 3,
    2, 7, 2, 29, 2, 3, 2, 5, 2, 17, 2, 3, 2, 37,
    2, 7, 2, 3, 2, 233, 2, 23669, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 61, 2, 2557, 2, 3, 2, 5, 2, 131, 2, 3,
    2, 7, 2, 271, 2, 3, 2, 19, 2, 11, 2, 3, 2, 71,
    2, 5, 2, 3, 2, 29, 2, 54767, 2, 3, 2, 5, 2, 109,
    2, 3, 2, 11, 2, 23, 2, 3, 2, 3631, 2, 59, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 55639, 2, 289967, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 13, 2, 31, 2, 3, 2, 173, 2, 17,
    2, 3, 2, 1039, 2, 5, 2, 3, 2, 23, 2, 41, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 30643, 2, 281, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 83, 2, 61,
    2, 3, 2, 5, 2, 73, 2, 3, 2, 19, 2, 2357, 2, 3,
    2, 7, 2, 53, 2, 3, 2, 2971, 2, 5, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 5, 2, 5743, 2, 3, 2, 103, 2, 821,
    2, 3, 2, 59, 2, 19, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 7, 2, 17, 2, 3, 2, 5, 2, 81569, 2, 3, 2, 107,
    2, 7, 2, 3, 2, 31, 2, 35117, 2, 3, 2, 29, 2, 5,
    2, 3, 2, 5003, 2, 409, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 7, 2, 1567, 2, 3, 2, 13, 2]

/-- A002386 row: the prime after 241160624143 is 241160624143 + 486. -/
theorem gap_241160624143 : IsGapAt 241160624143 486 :=
  isGapAt_of 241160624143 486 (p241160624143) (by show Nat.Prime 241160624629; exact p241160624629) ds_241160624143 (by decide +kernel)

def ds_297501075799 : List ℕ := [
    2, 3, 2, 11443, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 19, 2, 7, 2, 3, 2, 157,
    2, 37, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11, 2, 41,
    2, 3, 2, 5, 2, 3911, 2, 3, 2, 7, 2, 43, 2, 3,
    2, 1493, 2, 13, 2, 3, 2, 35419, 2, 5, 2, 3, 2, 31,
    2, 495433, 2, 3, 2, 5, 2, 5113, 2, 3, 2, 29, 2, 11,
    2, 3, 2, 1061, 2, 11551, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 1153, 2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13,
    2, 17, 2, 3, 2, 1831, 2, 199, 2, 3, 2, 41, 2, 5,
    2, 3, 2, 71, 2, 31, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 587, 2, 5507, 2, 3, 2, 17, 2, 7, 2, 3, 2, 1423,
    2, 5, 2, 3, 2, 61, 2, 2441, 2, 3, 2, 5, 2, 1303,
    2, 3, 2, 11, 2, 19, 2, 3, 2, 7, 2, 83, 2, 3,
    2, 103, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5,
    2, 29, 2, 3, 2, 251, 2, 1997, 2, 3, 2, 2029, 2, 1879,
    2, 3, 2, 443, 2, 5, 2, 3, 2, 7, 2, 59, 2, 3,
    2, 5, 2, 173, 2, 3, 2, 617, 2, 7, 2, 3, 2, 11,
    2, 23, 2, 3, 2, 1433, 2, 5, 2, 3, 2, 17, 2, 37,
    2, 3, 2, 5, 2, 1459, 2, 3, 2, 7, 2, 47, 2, 3,
    2, 13, 2, 1019, 2, 3, 2, 7621, 2, 5, 2, 3, 2, 124339,
    2, 11, 2, 3, 2, 5, 2, 19, 2, 3, 2, 97, 2, 13,
    2, 3, 2, 6737, 2, 15259, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 101, 2, 43, 2, 3, 2, 5, 2, 7, 2, 3, 2, 2819,
    2, 67, 2, 3, 2, 6917, 2, 193, 2, 3, 2, 60937, 2, 5,
    2, 3, 2, 59, 2, 157, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 17, 2, 79, 2, 3, 2, 47, 2, 7, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 93913, 2, 47881, 2, 3, 2, 7, 2, 103, 2, 3,
    2, 127, 2, 5, 2, 3, 2, 37, 2, 7, 2, 3, 2, 5,
    2, 337, 2, 3, 2, 2251, 2, 11, 2, 3, 2, 275131, 2, 17,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 113, 2, 3,
    2, 5, 2, 18313, 2, 3, 2, 31, 2, 7, 2, 3, 2, 26449,
    2, 13, 2, 3, 2, 17, 2, 5, 2, 3, 2, 1097, 2, 56467,
    2, 3, 2, 5, 2, 13553, 2, 3, 2, 7, 2, 37, 2, 3,
    2, 19, 2, 11, 2, 3, 2, 43, 2, 5, 2, 3, 2]

/-- A002386 row: the prime after 297501075799 is 297501075799 + 490. -/
theorem gap_297501075799 : IsGapAt 297501075799 490 :=
  isGapAt_of 297501075799 490 (p297501075799) (by show Nat.Prime 297501076289; exact p297501076289) ds_297501075799 (by decide +kernel)

def ds_303371455241 : List ℕ := [
    2, 19, 2, 3, 2, 7, 2, 4013, 2, 3, 2, 56921, 2, 5,
    2, 3, 2, 463663, 2, 7, 2, 3, 2, 5, 2, 41, 2, 3,
    2, 173, 2, 887, 2, 3, 2, 11, 2, 23, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 1523,
    2, 3, 2, 421, 2, 7, 2, 3, 2, 59, 2, 13, 2, 3,
    2, 170971, 2, 5, 2, 3, 2, 19, 2, 11, 2, 3, 2, 5,
    2, 1489, 2, 3, 2, 7, 2, 743, 2, 3, 2, 2689, 2, 5711,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 31, 2, 37, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 13, 2, 269, 2, 3, 2, 61,
    2, 97, 2, 3, 2, 7, 2, 5, 2, 3, 2, 2459, 2, 36527,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 2579, 2, 17, 2, 3,
    2, 63281, 2, 47, 2, 3, 2, 853, 2, 5, 2, 3, 2, 11,
    2, 31, 2, 3, 2, 5, 2, 23, 2, 3, 2, 1567, 2, 11483,
    2, 3, 2, 17, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 13, 2, 3067, 2, 3, 2, 5, 2, 131, 2, 3, 2, 12829,
    2, 11, 2, 3, 2, 7, 2, 29, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 661, 2, 7, 2, 3, 2, 5, 2, 101, 2, 3,
    2, 577, 2, 359, 2, 3, 2, 293, 2, 61, 2, 3, 2, 47,
    2, 5, 2, 3, 2, 7, 2, 313, 2, 3, 2, 5, 2, 1721,
    2, 3, 2, 103, 2, 7, 2, 3, 2, 13, 2, 11, 2, 3,
    2, 139, 2, 5, 2, 3, 2, 17, 2, 53, 2, 3, 2, 5,
    2, 151, 2, 3, 2, 7, 2, 13, 2, 3, 2, 19, 2, 479,
    2, 3, 2, 79, 2, 5, 2, 3, 2, 307, 2, 56941, 2, 3,
    2, 5, 2, 109, 2, 3, 2, 2953, 2, 37, 2, 3, 2, 1597,
    2, 179, 2, 3, 2, 7, 2, 5, 2, 3, 2, 7001, 2, 67,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 23, 2, 72973, 2, 3,
    2, 11, 2, 76207, 2, 3, 2, 71, 2, 5, 2, 3, 2, 137,
    2, 13, 2, 3, 2, 5, 2, 57781, 2, 3, 2, 17, 2, 29,
    2, 3, 2, 53, 2, 7, 2, 3, 2, 107, 2, 5, 2, 3,
    2, 89, 2, 11, 2, 3, 2, 5, 2, 83, 2, 3, 2, 19,
    2, 983, 2, 3, 2, 7, 2, 2027, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 101, 2, 7, 2, 3, 2, 5, 2, 6779, 2, 3,
    2, 29, 2, 23, 2, 3, 2, 3191, 2, 13, 2, 3, 2, 526501,
    2, 5, 2, 3, 2, 7, 2, 79, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 31, 2, 7, 2, 3, 2, 92413, 2, 1579, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 11, 2]

/-- A002386 row: the prime after 303371455241 is 303371455241 + 500. -/
theorem gap_303371455241 : IsGapAt 303371455241 500 :=
  isGapAt_of 303371455241 500 (p303371455241) (by show Nat.Prime 303371455741; exact p303371455741) ds_303371455241 (by decide +kernel)

def ds_304599508537 : List ℕ := [
    2, 3, 2, 29, 2, 11, 2, 3, 2, 887, 2, 7, 2, 3,
    2, 107, 2, 5, 2, 3, 2, 27011, 2, 3851, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 367, 2, 173, 2, 3, 2, 7, 2, 14489,
    2, 3, 2, 1601, 2, 5, 2, 3, 2, 27799, 2, 7, 2, 3,
    2, 5, 2, 123941, 2, 3, 2, 17, 2, 13, 2, 3, 2, 39887,
    2, 11, 2, 3, 2, 452611, 2, 5, 2, 3, 2, 7, 2, 89,
    2, 3, 2, 5, 2, 3929, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 211, 2, 151, 2, 3, 2, 499, 2, 5, 2, 3, 2, 103,
    2, 46919, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 157,
    2, 3, 2, 857, 2, 17, 2, 3, 2, 53, 2, 5, 2, 3,
    2, 451183, 2, 13, 2, 3, 2, 5, 2, 13997, 2, 3, 2, 19,
    2, 31, 2, 3, 2, 11, 2, 2887, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 61, 2, 229, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 3793, 2, 23, 2, 3, 2, 317, 2, 19, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 1187, 2, 11, 2, 3, 2, 5, 2, 18191,
    2, 3, 2, 41, 2, 4093, 2, 3, 2, 233, 2, 7, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 23, 2, 17, 2, 3, 2, 5,
    2, 281, 2, 3, 2, 2659, 2, 127, 2, 3, 2, 7, 2, 247771,
    2, 3, 2, 351749, 2, 5, 2, 3, 2, 89, 2, 7, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 13, 2, 2503, 2, 3, 2, 31,
    2, 4289, 2, 3, 2, 137, 2, 5, 2, 3, 2, 7, 2, 29,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 457, 2, 7, 2, 3,
    2, 139, 2, 563, 2, 3, 2, 2939, 2, 5, 2, 3, 2, 557,
    2, 23, 2, 3, 2, 5, 2, 155327, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 433, 2, 31, 2, 3, 2, 37, 2, 5, 2, 3,
    2, 13, 2, 521, 2, 3, 2, 5, 2, 6547, 2, 3, 2, 347,
    2, 3109, 2, 3, 2, 17, 2, 67, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 19, 2, 131, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 97, 2, 421, 2, 3, 2, 5281, 2, 11, 2, 3, 2, 478523,
    2, 5, 2, 3, 2, 73, 2, 4373, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 11, 2, 829, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 43, 2, 5, 2, 3, 2, 22409, 2, 107, 2, 3, 2, 5,
    2, 239, 2, 3, 2, 53, 2, 13, 2, 3, 2, 7, 2, 23,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3,
    2, 5, 2, 303839, 2, 3, 2, 6217, 2, 101, 2, 3, 2, 11,
    2, 919, 2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 359,
    2, 3, 2, 5, 2, 659, 2, 3, 2]

/-- A002386 row: the prime after 304599508537 is 304599508537 + 514. -/
theorem gap_304599508537 : IsGapAt 304599508537 514 :=
  isGapAt_of 304599508537 514 (p304599508537) (by show Nat.Prime 304599509051; exact p304599509051) ds_304599508537 (by decide +kernel)

def ds_416608695821 : List ℕ := [
    2, 41, 2, 3, 2, 5657, 2, 733, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 193, 2, 3,
    2, 251, 2, 7, 2, 3, 2, 23, 2, 31, 2, 3, 2, 229,
    2, 5, 2, 3, 2, 449629, 2, 29, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 59, 2, 3, 2, 89, 2, 43, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 11, 2, 73, 2, 3, 2, 5,
    2, 156733, 2, 3, 2, 19, 2, 21419, 2, 3, 2, 446603, 2, 13,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 29, 2, 271, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 239, 2, 11, 2, 3, 2, 113,
    2, 19, 2, 3, 2, 787, 2, 5, 2, 3, 2, 6203, 2, 157,
    2, 3, 2, 5, 2, 2939, 2, 3, 2, 13, 2, 227, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 75211,
    2, 127, 2, 3, 2, 5, 2, 13, 2, 3, 2, 59, 2, 86323,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 67, 2, 5, 2, 3,
    2, 37, 2, 7, 2, 3, 2, 5, 2, 7001, 2, 3, 2, 11,
    2, 149, 2, 3, 2, 151, 2, 461, 2, 3, 2, 181, 2, 5,
    2, 3, 2, 7, 2, 9781, 2, 3, 2, 5, 2, 179, 2, 3,
    2, 43, 2, 7, 2, 3, 2, 97, 2, 41, 2, 3, 2, 163,
    2, 5, 2, 3, 2, 17, 2, 133279, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 7, 2, 37, 2, 3, 2, 11, 2, 3067, 2, 3,
    2, 29, 2, 5, 2, 3, 2, 641419, 2, 311, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 79, 2, 83, 2, 3, 2, 13, 2, 204517,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 11, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 41, 2, 13, 2, 3, 2, 71837,
    2, 3037, 2, 3, 2, 11, 2, 5, 2, 3, 2, 31, 2, 457,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 17, 2, 7211, 2, 3,
    2, 1979, 2, 7, 2, 3, 2, 73, 2, 5, 2, 3, 2, 1601,
    2, 38053, 2, 3, 2, 5, 2, 11, 2, 3, 2, 47, 2, 643,
    2, 3, 2, 7, 2, 29, 2, 3, 2, 1217, 2, 5, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 5, 2, 59, 2, 3, 2, 37,
    2, 89, 2, 3, 2, 607, 2, 17, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 7, 2, 97, 2, 3, 2, 5, 2, 53, 2, 3,
    2, 23, 2, 7, 2, 3, 2, 29, 2, 79, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 83, 2, 19, 2, 3, 2, 5, 2, 269,
    2, 3, 2, 7, 2, 2389, 2, 3, 2, 71, 2, 13, 2, 3,
    2, 13933, 2, 5, 2, 3, 2, 43, 2, 229, 2, 3, 2, 5,
    2, 257, 2, 3, 2, 149, 2, 191, 2, 3, 2]

/-- A002386 row: the prime after 416608695821 is 416608695821 + 516. -/
theorem gap_416608695821 : IsGapAt 416608695821 516 :=
  isGapAt_of 416608695821 516 (p416608695821) (by show Nat.Prime 416608696337; exact p416608696337) ds_416608695821 (by decide +kernel)

def ds_461690510011 : List ℕ := [
    2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 149, 2, 3,
    2, 41, 2, 7, 2, 3, 2, 59771, 2, 5, 2, 3, 2, 11,
    2, 37, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 1289,
    2, 3, 2, 7, 2, 58909, 2, 3, 2, 367, 2, 5, 2, 3,
    2, 89, 2, 7, 2, 3, 2, 5, 2, 109, 2, 3, 2, 307,
    2, 11, 2, 3, 2, 1619, 2, 19, 2, 3, 2, 29, 2, 5,
    2, 3, 2, 7, 2, 43, 2, 3, 2, 5, 2, 61, 2, 3,
    2, 71, 2, 7, 2, 3, 2, 17, 2, 181, 2, 3, 2, 877,
    2, 5, 2, 3, 2, 1979, 2, 269, 2, 3, 2, 5, 2, 193,
    2, 3, 2, 7, 2, 23, 2, 3, 2, 179, 2, 11, 2, 3,
    2, 31, 2, 5, 2, 3, 2, 243671, 2, 83, 2, 3, 2, 5,
    2, 79, 2, 3, 2, 11, 2, 251, 2, 3, 2, 13, 2, 67,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 41, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 73, 2, 13, 2, 3, 2, 55201,
    2, 29, 2, 3, 2, 78283, 2, 5, 2, 3, 2, 17, 2, 649183,
    2, 3, 2, 5, 2, 1123, 2, 3, 2, 1009, 2, 461, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 76631, 2, 5, 2, 3, 2, 2677,
    2, 5431, 2, 3, 2, 5, 2, 839, 2, 3, 2, 2437, 2, 37,
    2, 3, 2, 7, 2, 149159, 2, 3, 2, 41, 2, 5, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 373,
    2, 17077, 2, 3, 2, 317, 2, 2621, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 7, 2, 643, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 23, 2, 123379, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 31, 2, 2287, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 84221, 2, 3, 2, 139, 2, 13, 2, 3,
    2, 5827, 2, 5, 2, 3, 2, 11, 2, 131, 2, 3, 2, 5,
    2, 113, 2, 3, 2, 107, 2, 29, 2, 3, 2, 7793, 2, 17,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 151, 2, 31, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 13, 2, 11, 2, 3, 2, 3041,
    2, 23, 2, 3, 2, 17, 2, 5, 2, 3, 2, 617, 2, 19,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 29, 2, 457, 2, 3,
    2, 67, 2, 7, 2, 3, 2, 12007, 2, 5, 2, 3, 2, 859,
    2, 64327, 2, 3, 2, 5, 2, 21319, 2, 3, 2, 53, 2, 61,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 79, 2, 5, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 5, 2, 47, 2, 3, 2, 11,
    2, 16427, 2, 3, 2, 19, 2, 4987, 2, 3, 2, 109, 2, 5,
    2, 3, 2, 7, 2, 233, 2, 3, 2, 5, 2, 227, 2, 3,
    2, 43, 2, 7, 2, 3, 2, 71, 2, 202021, 2, 3, 2]

/-- A002386 row: the prime after 461690510011 is 461690510011 + 532. -/
theorem gap_461690510011 : IsGapAt 461690510011 532 :=
  isGapAt_of 461690510011 532 (p461690510011) (by show Nat.Prime 461690510543; exact p461690510543) ds_461690510011 (by decide +kernel)

def ds_614487453523 : List ℕ := [
    2, 3, 2, 839, 2, 1151, 2, 3, 2, 47, 2, 5, 2, 3,
    2, 619681, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 31,
    2, 45139, 2, 3, 2, 71, 2, 7, 2, 3, 2, 79, 2, 5,
    2, 3, 2, 11, 2, 43, 2, 3, 2, 5, 2, 67, 2, 3,
    2, 699253, 2, 17, 2, 3, 2, 7, 2, 62297, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 1987, 2, 7, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 449, 2, 11, 2, 3, 2, 17, 2, 13, 2, 3,
    2, 73, 2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5,
    2, 1103, 2, 3, 2, 197, 2, 7, 2, 3, 2, 53, 2, 127,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 337, 2, 557, 2, 3,
    2, 5, 2, 41593, 2, 3, 2, 7, 2, 1733, 2, 3, 2, 163,
    2, 11, 2, 3, 2, 73651, 2, 5, 2, 3, 2, 19, 2, 97,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 37, 2, 3,
    2, 5857, 2, 271, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17,
    2, 47, 2, 3, 2, 5, 2, 7, 2, 3, 2, 373, 2, 7151,
    2, 3, 2, 31, 2, 126751, 2, 3, 2, 43, 2, 5, 2, 3,
    2, 13, 2, 59, 2, 3, 2, 5, 2, 89, 2, 3, 2, 863,
    2, 3911, 2, 3, 2, 11, 2, 7, 2, 3, 2, 78341, 2, 5,
    2, 3, 2, 149, 2, 857, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 23, 2, 41, 2, 3, 2, 7, 2, 31, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 13147, 2, 7, 2, 3, 2, 5, 2, 83,
    2, 3, 2, 17, 2, 1093, 2, 3, 2, 13, 2, 43, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5,
    2, 219503, 2, 3, 2, 37, 2, 7, 2, 3, 2, 24709, 2, 53,
    2, 3, 2, 29, 2, 5, 2, 3, 2, 59, 2, 3391, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 7, 2, 23, 2, 3, 2, 151,
    2, 17, 2, 3, 2, 109, 2, 5, 2, 3, 2, 11, 2, 887,
    2, 3, 2, 5, 2, 107, 2, 3, 2, 690143, 2, 131, 2, 3,
    2, 19, 2, 37517, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23,
    2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 500443, 2, 11,
    2, 3, 2, 199, 2, 1627, 2, 3, 2, 77237, 2, 5, 2, 3,
    2, 61, 2, 5167, 2, 3, 2, 5, 2, 476719, 2, 3, 2, 137,
    2, 173, 2, 3, 2, 1439, 2, 7, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 541, 2, 17, 2, 3, 2, 5, 2, 285179, 2, 3,
    2, 43, 2, 47, 2, 3, 2, 7, 2, 11, 2, 3, 2, 491,
    2, 5, 2, 3, 2, 2833, 2, 7, 2, 3, 2, 5, 2, 5479,
    2, 3, 2, 11, 2, 1759, 2, 3, 2, 29, 2, 41, 2, 3,
    2, 563, 2, 5, 2, 3, 2, 7, 2, 344921, 2, 3, 2, 5,
    2]

/-- A002386 row: the prime after 614487453523 is 614487453523 + 534. -/
theorem gap_614487453523 : IsGapAt 614487453523 534 :=
  isGapAt_of 614487453523 534 (p614487453523) (by show Nat.Prime 614487454057; exact p614487454057) ds_614487453523 (by decide +kernel)

def ds_738832927927 : List ℕ := [
    2, 3, 2, 7, 2, 1619, 2, 3, 2, 13, 2, 17, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 73, 2, 383, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 5077, 2, 13, 2, 3, 2, 31, 2, 103,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 404113, 2, 37, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 3371, 2, 29, 2, 3, 2, 41,
    2, 410323, 2, 3, 2, 179, 2, 5, 2, 3, 2, 11, 2, 1181,
    2, 3, 2, 5, 2, 619987, 2, 3, 2, 509, 2, 941, 2, 3,
    2, 20753, 2, 7, 2, 3, 2, 977, 2, 5, 2, 3, 2, 19,
    2, 13, 2, 3, 2, 5, 2, 1987, 2, 3, 2, 29, 2, 11,
    2, 3, 2, 7, 2, 59, 2, 3, 2, 48991, 2, 5, 2, 3,
    2, 83, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 51913,
    2, 463093, 2, 3, 2, 1031, 2, 751, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 73189, 2, 3,
    2, 9173, 2, 7, 2, 3, 2, 43, 2, 11, 2, 3, 2, 87407,
    2, 5, 2, 3, 2, 37, 2, 53, 2, 3, 2, 5, 2, 113017,
    2, 3, 2, 7, 2, 17, 2, 3, 2, 23, 2, 151, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 107, 2, 41, 2, 3, 2, 5,
    2, 29, 2, 3, 2, 13, 2, 139, 2, 3, 2, 17, 2, 67,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 883, 2, 19, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 4561, 2, 37, 2, 3, 2, 11,
    2, 419, 2, 3, 2, 79, 2, 5, 2, 3, 2, 12251, 2, 576217,
    2, 3, 2, 5, 2, 131, 2, 3, 2, 2083, 2, 251, 2, 3,
    2, 53, 2, 7, 2, 3, 2, 41, 2, 5, 2, 3, 2, 13,
    2, 11, 2, 3, 2, 5, 2, 167, 2, 3, 2, 3697, 2, 283,
    2, 3, 2, 7, 2, 139487, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 5, 2, 222109, 2, 3, 2, 378193,
    2, 149, 2, 3, 2, 38671, 2, 1861, 2, 3, 2, 5209, 2, 5,
    2, 3, 2, 7, 2, 8623, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 3701, 2, 7, 2, 3, 2, 13, 2, 257, 2, 3, 2, 47,
    2, 5, 2, 3, 2, 11, 2, 29, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 191, 2, 61, 2, 3,
    2, 68041, 2, 5, 2, 3, 2, 1399, 2, 79, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 17, 2, 11, 2, 3, 2, 73, 2, 499,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 29, 2, 31, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 70297, 2, 59, 2, 3, 2, 109589,
    2, 19, 2, 3, 2, 23, 2, 5, 2, 3, 2, 433, 2, 13,
    2, 3, 2, 5, 2, 173, 2, 3, 2, 46997, 2, 14081, 2, 3,
    2, 67, 2, 7, 2, 3, 2, 2039, 2, 5, 2, 3, 2, 66221,
    2, 43, 2, 3, 2, 5, 2]

/-- A002386 row: the prime after 738832927927 is 738832927927 + 540. -/
theorem gap_738832927927 : IsGapAt 738832927927 540 :=
  isGapAt_of 738832927927 540 (p738832927927) (by show Nat.Prime 738832928467; exact p738832928467) ds_738832927927 (by decide +kernel)

def ds_1346294310749 : List ℕ := [
    2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 739, 2, 149,
    2, 3, 2, 7, 2, 905143, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 5, 2, 73, 2, 3, 2, 847967,
    2, 179, 2, 3, 2, 53, 2, 599, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 7, 2, 101603, 2, 3, 2, 5, 2, 43, 2, 3,
    2, 401, 2, 7, 2, 3, 2, 313, 2, 13, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 2063, 2, 89, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 7, 2, 677, 2, 3, 2, 15107, 2, 7459, 2, 3,
    2, 193, 2, 5, 2, 3, 2, 91541, 2, 19, 2, 3, 2, 5,
    2, 109, 2, 3, 2, 13, 2, 4861, 2, 3, 2, 41, 2, 11,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 37, 2, 137, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 11, 2, 67, 2, 3, 2, 281,
    2, 5351, 2, 3, 2, 367, 2, 5, 2, 3, 2, 47, 2, 386927,
    2, 3, 2, 5, 2, 59, 2, 3, 2, 1033, 2, 101, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2, 13,
    2, 3389, 2, 3, 2, 5, 2, 727, 2, 3, 2, 31, 2, 37,
    2, 3, 2, 7, 2, 131, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 43, 2, 7, 2, 3, 2, 5, 2, 1933, 2, 3, 2, 61,
    2, 23, 2, 3, 2, 453923, 2, 53, 2, 3, 2, 164471, 2, 5,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 167, 2, 3,
    2, 21961, 2, 7, 2, 3, 2, 13, 2, 12517, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 23, 2, 17, 2, 3, 2, 5, 2, 823,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 277, 2, 29, 2, 3,
    2, 211339, 2, 5, 2, 3, 2, 73, 2, 22171, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 15541, 2, 173, 2, 3, 2, 1301, 2, 19,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 229, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 37, 2, 61, 2, 3, 2, 29,
    2, 863, 2, 3, 2, 41, 2, 5, 2, 3, 2, 79, 2, 13,
    2, 3, 2, 5, 2, 3259, 2, 3, 2, 179, 2, 11, 2, 3,
    2, 31, 2, 7, 2, 3, 2, 7283, 2, 5, 2, 3, 2, 1753,
    2, 1321, 2, 3, 2, 5, 2, 181, 2, 3, 2, 67, 2, 941,
    2, 3, 2, 7, 2, 90793, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 1049, 2, 7, 2, 3, 2, 5, 2, 1499, 2, 3, 2, 47,
    2, 19, 2, 3, 2, 78941, 2, 11, 2, 3, 2, 834949, 2, 5,
    2, 3, 2, 7, 2, 19843, 2, 3, 2, 5, 2, 113, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 43, 2, 193, 2, 3, 2, 317,
    2, 5, 2, 3, 2, 521, 2, 594721, 2, 3, 2, 5, 2, 41651,
    2, 3, 2, 7, 2, 769, 2, 3, 2, 449269, 2, 23, 2, 3,
    2, 223, 2, 5, 2, 3, 2, 17, 2, 59, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 29, 2, 751529, 2, 3, 2, 11, 2, 97,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 631, 2, 10847, 2, 3,
    2, 5, 2, 7, 2, 3, 2]

/-- A002386 row: the prime after 1346294310749 is 1346294310749 + 582. -/
theorem gap_1346294310749 : IsGapAt 1346294310749 582 :=
  isGapAt_of 1346294310749 582 (p1346294310749) (by show Nat.Prime 1346294311331; exact p1346294311331) ds_1346294310749 (by decide +kernel)

def ds_1408695493609 : List ℕ := [
    2, 3, 2, 59, 2, 5, 2, 3, 2, 167, 2, 13, 2, 3,
    2, 5, 2, 31, 2, 3, 2, 43, 2, 29, 2, 3, 2, 85259,
    2, 7, 2, 3, 2, 4283, 2, 5, 2, 3, 2, 725323, 2, 17,
    2, 3, 2, 5, 2, 23, 2, 3, 2, 2339, 2, 271, 2, 3,
    2, 7, 2, 419, 2, 3, 2, 13, 2, 5, 2, 3, 2, 643,
    2, 7, 2, 3, 2, 5, 2, 997207, 2, 3, 2, 19, 2, 492319,
    2, 3, 2, 37, 2, 13, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 5, 2, 43, 2, 3, 2, 109,
    2, 7, 2, 3, 2, 53, 2, 19, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 113, 2, 282769, 2, 3, 2, 5, 2, 2957, 2, 3,
    2, 7, 2, 17, 2, 3, 2, 41, 2, 67, 2, 3, 2, 59453,
    2, 5, 2, 3, 2, 863, 2, 37, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 5519, 2, 1861, 2, 3, 2, 17, 2, 6151, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 11, 2, 659, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 61, 2, 31, 2, 3, 2, 4591, 2, 283,
    2, 3, 2, 277, 2, 5, 2, 3, 2, 13, 2, 233, 2, 3,
    2, 5, 2, 101, 2, 3, 2, 23, 2, 11, 2, 3, 2, 1733,
    2, 7, 2, 3, 2, 313, 2, 5, 2, 3, 2, 433, 2, 594653,
    2, 3, 2, 5, 2, 479, 2, 3, 2, 3659, 2, 89, 2, 3,
    2, 7, 2, 910447, 2, 3, 2, 547, 2, 5, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 5, 2, 47, 2, 3, 2, 30029, 2, 229,
    2, 3, 2, 13, 2, 11, 2, 3, 2, 907, 2, 5, 2, 3,
    2, 7, 2, 41, 2, 3, 2, 5, 2, 131, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 31, 2, 53, 2, 3, 2, 103, 2, 5,
    2, 3, 2, 79, 2, 797, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 7, 2, 631, 2, 3, 2, 59, 2, 938803, 2, 3, 2, 181,
    2, 5, 2, 3, 2, 23, 2, 29, 2, 3, 2, 5, 2, 269,
    2, 3, 2, 17, 2, 37, 2, 3, 2, 11, 2, 31, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 600217, 2, 13, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 1213, 2, 97, 2, 3, 2, 67, 2, 829,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 29, 2, 11, 2, 3,
    2, 5, 2, 2663, 2, 3, 2, 89, 2, 708403, 2, 3, 2, 11087,
    2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 158621, 2, 19,
    2, 3, 2, 5, 2, 73, 2, 3, 2, 2081, 2, 521, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 17, 2, 5, 2, 3, 2, 98897,
    2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 11903, 2, 23669,
    2, 3, 2, 23, 2, 223, 2, 3, 2, 31, 2, 5, 2, 3,
    2, 7, 2, 532451, 2, 3, 2, 5, 2, 677, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 19, 2, 103, 2, 3, 2, 197, 2, 5,
    2, 3, 2, 64567, 2, 17, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 61, 2, 47, 2, 3, 2, 151,
    2, 5, 2, 3, 2, 131, 2, 113, 2, 3, 2, 5, 2]

/-- A002386 row: the prime after 1408695493609 is 1408695493609 + 588. -/
theorem gap_1408695493609 : IsGapAt 1408695493609 588 :=
  isGapAt_of 1408695493609 588 (p1408695493609) (by show Nat.Prime 1408695494197; exact p1408695494197) ds_1408695493609 (by decide +kernel)

def ds_1968188556461 : List ℕ := [
    2, 17, 2, 3, 2, 7, 2, 3181, 2, 3, 2, 53, 2, 5,
    2, 3, 2, 149, 2, 7, 2, 3, 2, 5, 2, 13007, 2, 3,
    2, 293, 2, 2657, 2, 3, 2, 17, 2, 11, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 7, 2, 101, 2, 3, 2, 5, 2, 139,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 13043, 2, 13, 2, 3,
    2, 12011, 2, 5, 2, 3, 2, 373859, 2, 3413, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 7, 2, 61, 2, 3, 2, 239, 2, 1867,
    2, 3, 2, 79, 2, 5, 2, 3, 2, 23, 2, 43, 2, 3,
    2, 5, 2, 263, 2, 3, 2, 13, 2, 567997, 2, 3, 2, 11,
    2, 103, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 131431,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 83663, 2, 7129, 2, 3,
    2, 193, 2, 19, 2, 3, 2, 163, 2, 5, 2, 3, 2, 1117,
    2, 11, 2, 3, 2, 5, 2, 131, 2, 3, 2, 109, 2, 47,
    2, 3, 2, 34963, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 13, 2, 23, 2, 3, 2, 5, 2, 17, 2, 3, 2, 31,
    2, 796177, 2, 3, 2, 7, 2, 797, 2, 3, 2, 331, 2, 5,
    2, 3, 2, 452161, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 17, 2, 83, 2, 3, 2, 23, 2, 29, 2, 3, 2, 101,
    2, 5, 2, 3, 2, 7, 2, 79, 2, 3, 2, 5, 2, 277,
    2, 3, 2, 1153, 2, 7, 2, 3, 2, 13, 2, 107, 2, 3,
    2, 43, 2, 5, 2, 3, 2, 1009, 2, 1049, 2, 3, 2, 5,
    2, 127, 2, 3, 2, 7, 2, 11, 2, 3, 2, 29, 2, 17,
    2, 3, 2, 1621, 2, 5, 2, 3, 2, 59, 2, 4483, 2, 3,
    2, 5, 2, 181, 2, 3, 2, 53, 2, 30449, 2, 3, 2, 61,
    2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 274357,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 599, 2, 12239, 2, 3,
    2, 41, 2, 11, 2, 3, 2, 367, 2, 5, 2, 3, 2, 9539,
    2, 13, 2, 3, 2, 5, 2, 19, 2, 3, 2, 11, 2, 647,
    2, 3, 2, 31, 2, 7, 2, 3, 2, 89, 2, 5, 2, 3,
    2, 83, 2, 17, 2, 3, 2, 5, 2, 37, 2, 3, 2, 257,
    2, 29, 2, 3, 2, 7, 2, 283, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 131, 2, 7, 2, 3, 2, 5, 2, 167, 2, 3,
    2, 4127, 2, 73, 2, 3, 2, 11, 2, 13, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 7, 2, 571, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 29, 2, 7, 2, 3, 2, 8101, 2, 163, 2, 3,
    2, 107, 2, 5, 2, 3, 2, 311, 2, 11, 2, 3, 2, 5,
    2, 1367, 2, 3, 2, 7, 2, 17, 2, 3, 2, 3229, 2, 157,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 1511, 2, 41, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 43, 2, 53, 2, 3, 2, 17,
    2, 9679, 2, 3, 2, 7, 2, 5, 2, 3, 2, 47, 2, 179,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 991031, 2, 3617, 2, 3,
    2, 19, 2, 36583, 2, 3, 2, 31, 2, 5, 2, 3, 2, 11,
    2, 1087543, 2, 3, 2, 5, 2, 29, 2, 3, 2, 359, 2]

/-- A002386 row: the prime after 1968188556461 is 1968188556461 + 602. -/
theorem gap_1968188556461 : IsGapAt 1968188556461 602 :=
  isGapAt_of 1968188556461 602 (p1968188556461) (by show Nat.Prime 1968188557063; exact p1968188557063) ds_1968188556461 (by decide +kernel)

def ds_2614941710599 : List ℕ := [
    2, 3, 2, 43, 2, 5, 2, 3, 2, 3929, 2, 1390547, 2, 3,
    2, 5, 2, 31, 2, 3, 2, 1399837, 2, 11, 2, 3, 2, 137,
    2, 172441, 2, 3, 2, 7, 2, 5, 2, 3, 2, 324451, 2, 13,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 96443, 2, 19, 2, 3,
    2, 79, 2, 17, 2, 3, 2, 1039, 2, 5, 2, 3, 2, 71,
    2, 62383, 2, 3, 2, 5, 2, 945463, 2, 3, 2, 6737, 2, 149,
    2, 3, 2, 101, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 167, 2, 233, 2, 3, 2, 5, 2, 60449, 2, 3, 2, 11,
    2, 3631, 2, 3, 2, 7, 2, 13, 2, 3, 2, 151, 2, 5,
    2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 1181, 2, 3,
    2, 31, 2, 7001, 2, 3, 2, 281, 2, 1361, 2, 3, 2, 883,
    2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 11, 2, 29399, 2, 3,
    2, 397, 2, 5, 2, 3, 2, 2161, 2, 421, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 7, 2, 23, 2, 3, 2, 397297, 2, 29,
    2, 3, 2, 457, 2, 5, 2, 3, 2, 47, 2, 11, 2, 3,
    2, 5, 2, 197, 2, 3, 2, 113, 2, 38317, 2, 3, 2, 443,
    2, 61, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 571,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 43, 2, 17, 2, 3,
    2, 29, 2, 509, 2, 3, 2, 59, 2, 5, 2, 3, 2, 41,
    2, 19, 2, 3, 2, 5, 2, 11, 2, 3, 2, 53, 2, 1297,
    2, 3, 2, 17, 2, 7, 2, 3, 2, 103, 2, 5, 2, 3,
    2, 11, 2, 283, 2, 3, 2, 5, 2, 661, 2, 3, 2, 73681,
    2, 2531, 2, 3, 2, 7, 2, 3547, 2, 3, 2, 11279, 2, 5,
    2, 3, 2, 14879, 2, 7, 2, 3, 2, 5, 2, 43, 2, 3,
    2, 941, 2, 11, 2, 3, 2, 19, 2, 5351, 2, 3, 2, 6043,
    2, 5, 2, 3, 2, 7, 2, 89, 2, 3, 2, 5, 2, 83,
    2, 3, 2, 149, 2, 7, 2, 3, 2, 23, 2, 31, 2, 3,
    2, 97, 2, 5, 2, 3, 2, 17, 2, 307, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 7, 2, 280909, 2, 3, 2, 73, 2, 11,
    2, 3, 2, 46811, 2, 5, 2, 3, 2, 379, 2, 13, 2, 3,
    2, 5, 2, 32869, 2, 3, 2, 11, 2, 41, 2, 3, 2, 257,
    2, 6269, 2, 3, 2, 7, 2, 5, 2, 3, 2, 521, 2, 743,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 229, 2, 3,
    2, 39607, 2, 23, 2, 3, 2, 13, 2, 5, 2, 3, 2, 9643,
    2, 101, 2, 3, 2, 5, 2, 505061, 2, 3, 2, 17, 2, 53,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3,
    2, 43, 2, 67, 2, 3, 2, 5, 2, 523, 2, 3, 2, 79,
    2, 461, 2, 3, 2, 7, 2, 20477, 2, 3, 2, 83, 2, 5,
    2, 3, 2, 89, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 13, 2, 73, 2, 3, 2, 107, 2, 17, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 7, 2, 2617, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 199, 2, 7, 2, 3, 2, 1423, 2, 1211261, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 53, 2, 37, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 7, 2, 19, 2, 3, 2, 59, 2, 9041,
    2, 3, 2, 593, 2, 5, 2, 3, 2, 11, 2, 1759, 2, 3,
    2, 5, 2, 1381, 2, 3, 2]

/-- A002386 row: the prime after 2614941710599 is 2614941710599 + 652. -/
theorem gap_2614941710599 : IsGapAt 2614941710599 652 :=
  isGapAt_of 2614941710599 652 (p2614941710599) (by show Nat.Prime 2614941711251; exact p2614941711251) ds_2614941710599 (by decide +kernel)

def ds_7177162611713 : List ℕ := [
    2, 5, 2, 3, 2, 1459, 2, 680129, 2, 3, 2, 5, 2, 1217,
    2, 3, 2, 7, 2, 193009, 2, 3, 2, 107, 2, 25409, 2, 3,
    2, 131, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5,
    2, 137, 2, 3, 2, 19, 2, 31, 2, 3, 2, 29, 2, 223,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 101117, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 191, 2, 89, 2, 3, 2, 23,
    2, 19, 2, 3, 2, 971, 2, 5, 2, 3, 2, 67, 2, 53,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 229, 2, 1523981, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 9043, 2, 5, 2, 3, 2, 11,
    2, 109, 2, 3, 2, 5, 2, 17, 2, 3, 2, 83, 2, 13,
    2, 3, 2, 7, 2, 101, 2, 3, 2, 59723, 2, 5, 2, 3,
    2, 73, 2, 7, 2, 3, 2, 5, 2, 1316647, 2, 3, 2, 17,
    2, 11, 2, 3, 2, 31, 2, 23, 2, 3, 2, 37, 2, 5,
    2, 3, 2, 7, 2, 97, 2, 3, 2, 5, 2, 269, 2, 3,
    2, 613, 2, 7, 2, 3, 2, 53, 2, 29399, 2, 3, 2, 139273,
    2, 5, 2, 3, 2, 59, 2, 13, 2, 3, 2, 5, 2, 157,
    2, 3, 2, 7, 2, 67, 2, 3, 2, 887, 2, 11, 2, 3,
    2, 41, 2, 5, 2, 3, 2, 1487, 2, 331, 2, 3, 2, 5,
    2, 37, 2, 3, 2, 11, 2, 9631, 2, 3, 2, 1040657, 2, 188957,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 127, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 769, 2, 863, 2, 3, 2, 283,
    2, 13, 2, 3, 2, 411779, 2, 5, 2, 3, 2, 246689, 2, 199,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 137, 2, 643, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 167, 2, 5, 2, 3, 2, 619,
    2, 17, 2, 3, 2, 5, 2, 29, 2, 3, 2, 13, 2, 71,
    2, 3, 2, 7, 2, 289951, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 81223, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 181,
    2, 499, 2, 3, 2, 61, 2, 56113, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 7, 2, 40883, 2, 3, 2, 5, 2, 41, 2, 3,
    2, 163, 2, 7, 2, 3, 2, 103, 2, 53, 2, 3, 2, 977107,
    2, 5, 2, 3, 2, 13, 2, 19, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 17, 2, 3, 2, 317, 2, 5693, 2, 3,
    2, 1439, 2, 5, 2, 3, 2, 11, 2, 47, 2, 3, 2, 5,
    2, 2777, 2, 3, 2, 212633, 2, 83, 2, 3, 2, 17, 2, 37,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 41, 2, 353, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 23, 2, 11, 2, 3, 2, 13,
    2, 61, 2, 3, 2, 3323, 2, 5, 2, 3, 2, 563, 2, 29,
    2, 3, 2, 5, 2, 353879, 2, 3, 2, 2089, 2, 13, 2, 3,
    2, 797, 2, 7, 2, 3, 2, 71263, 2, 5, 2, 3, 2, 31,
    2, 857, 2, 3, 2, 5, 2, 131, 2, 3, 2, 79, 2, 423853,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 59, 2, 5, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 5, 2, 1619, 2, 3, 2, 11,
    2, 23, 2, 3, 2, 73, 2, 266549, 2, 3, 2, 659, 2, 5,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 89, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 37, 2, 491, 2, 3, 2, 719,
    2, 5, 2, 3, 2, 23, 2, 202219, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 7, 2, 41, 2, 3, 2, 11, 2, 19, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 107, 2, 36821, 2, 3, 2, 5,
    2]

/-- A002386 row: the prime after 7177162611713 is 7177162611713 + 674. -/
theorem gap_7177162611713 : IsGapAt 7177162611713 674 :=
  isGapAt_of 7177162611713 674 (p7177162611713) (by show Nat.Prime 7177162612387; exact p7177162612387) ds_7177162611713 (by decide +kernel)

def ds_13829048559701 : List ℕ := [
    2, 13, 2, 3, 2, 14387, 2, 149, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 53, 2, 173, 2, 3, 2, 5, 2, 3448693, 2, 3,
    2, 29, 2, 11, 2, 3, 2, 43, 2, 7, 2, 3, 2, 89,
    2, 5, 2, 3, 2, 67, 2, 41, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 839, 2, 389, 2, 3, 2, 7, 2, 101, 2, 3,
    2, 23173, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5,
    2, 83, 2, 3, 2, 73, 2, 283, 2, 3, 2, 4079, 2, 11,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 337, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 11, 2, 7, 2, 3, 2, 47,
    2, 733, 2, 3, 2, 13, 2, 5, 2, 3, 2, 1920223, 2, 546253,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 10831, 2, 3,
    2, 269, 2, 13, 2, 3, 2, 59, 2, 5, 2, 3, 2, 199,
    2, 31, 2, 3, 2, 5, 2, 49009, 2, 3, 2, 23627, 2, 17,
    2, 3, 2, 11, 2, 709, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 3323141, 2, 947, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13,
    2, 439, 2, 3, 2, 17, 2, 37, 2, 3, 2, 463, 2, 5,
    2, 3, 2, 3634679, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 23, 2, 79063, 2, 3, 2, 15331, 2, 7, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 1091, 2, 467, 2, 3, 2, 5, 2, 1193,
    2, 3, 2, 101, 2, 131, 2, 3, 2, 7, 2, 157, 2, 3,
    2, 281, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 71, 2, 12041, 2, 3, 2, 19, 2, 112877,
    2, 3, 2, 347, 2, 5, 2, 3, 2, 7, 2, 29, 2, 3,
    2, 5, 2, 517403, 2, 3, 2, 145633, 2, 7, 2, 3, 2, 53,
    2, 61, 2, 3, 2, 95063, 2, 5, 2, 3, 2, 677, 2, 383,
    2, 3, 2, 5, 2, 31, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 13, 2, 1032709, 2, 3, 2, 11467, 2, 5, 2, 3, 2, 23,
    2, 43, 2, 3, 2, 5, 2, 17, 2, 3, 2, 1399, 2, 13,
    2, 3, 2, 151, 2, 59, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 47, 2, 19501, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17,
    2, 811, 2, 3, 2, 1709, 2, 11, 2, 3, 2, 211, 2, 5,
    2, 3, 2, 162499, 2, 37, 2, 3, 2, 5, 2, 909331, 2, 3,
    2, 11, 2, 241, 2, 3, 2, 36587, 2, 7, 2, 3, 2, 79,
    2, 5, 2, 3, 2, 15749, 2, 13, 2, 3, 2, 5, 2, 937,
    2, 3, 2, 31, 2, 1005661, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 139, 2, 5, 2, 3, 2, 174649, 2, 7, 2, 3, 2, 5,
    2, 263, 2, 3, 2, 1231, 2, 239, 2, 3, 2, 11, 2, 163,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 331, 2, 3,
    2, 5, 2, 11939, 2, 3, 2, 661, 2, 7, 2, 3, 2, 251,
    2, 13, 2, 3, 2, 29, 2, 5, 2, 3, 2, 683, 2, 11,
    2, 3, 2, 5, 2, 199, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 89, 2, 659, 2, 3, 2, 11, 2, 5, 2, 3, 2, 37,
    2, 17, 2, 3, 2, 5, 2, 47, 2, 3, 2, 13, 2, 2161,
    2, 3, 2, 97, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 3089, 2, 79, 2, 3, 2, 5, 2, 7, 2, 3, 2, 499,
    2, 179, 2, 3, 2, 1636543, 2, 43, 2, 3, 2, 113, 2, 5,
    2, 3, 2, 11, 2, 977, 2, 3, 2, 5, 2, 193, 2, 3,
    2, 152003, 2, 37, 2, 3, 2, 31, 2, 7, 2, 3, 2, 503,
    2, 5, 2, 3, 2, 13, 2, 307, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 47, 2, 11, 2, 3, 2, 7, 2, 151, 2, 3,
    2, 421, 2, 5, 2, 3, 2, 744377, 2, 7, 2, 3, 2, 5,
    2]

/-- A002386 row: the prime after 13829048559701 is 13829048559701 + 716. -/
theorem gap_13829048559701 : IsGapAt 13829048559701 716 :=
  isGapAt_of 13829048559701 716 (p13829048559701) (by show Nat.Prime 13829048560417; exact p13829048560417) ds_13829048559701 (by decide +kernel)

def ds_19581334192423 : List ℕ := [
    2, 3, 2, 7, 2, 181, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 23, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 1277,
    2, 11, 2, 3, 2, 11093, 2, 13, 2, 3, 2, 43, 2, 5,
    2, 3, 2, 7, 2, 53, 2, 3, 2, 5, 2, 4327, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 126457, 2, 109, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 29, 2, 71, 2, 3, 2, 5, 2, 223,
    2, 3, 2, 7, 2, 3593, 2, 3, 2, 93427, 2, 11, 2, 3,
    2, 1997, 2, 5, 2, 3, 2, 1181, 2, 19, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 11, 2, 1197349, 2, 3, 2, 479, 2, 17,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 271, 2, 83, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 163, 2, 16741, 2, 3, 2, 23,
    2, 47, 2, 3, 2, 17, 2, 5, 2, 3, 2, 13, 2, 3823,
    2, 3, 2, 5, 2, 269, 2, 3, 2, 4931, 2, 373, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 37, 2, 5, 2, 3, 2, 541,
    2, 5099, 2, 3, 2, 5, 2, 241, 2, 3, 2, 67, 2, 12203,
    2, 3, 2, 7, 2, 281, 2, 3, 2, 71, 2, 5, 2, 3,
    2, 52901, 2, 7, 2, 3, 2, 5, 2, 527623, 2, 3, 2, 2381,
    2, 296833, 2, 3, 2, 13, 2, 23, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 7, 2, 89, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 1087, 2, 7, 2, 3, 2, 2589343, 2, 79, 2, 3, 2, 421,
    2, 5, 2, 3, 2, 61, 2, 3187, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 157, 2, 3, 2, 83, 2, 179, 2, 3,
    2, 96959, 2, 5, 2, 3, 2, 11, 2, 71347, 2, 3, 2, 5,
    2, 739, 2, 3, 2, 6701, 2, 17, 2, 3, 2, 298943, 2, 19,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 21379, 2, 13, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 228427, 2, 11, 2, 3, 2, 17,
    2, 29, 2, 3, 2, 31, 2, 5, 2, 3, 2, 1783, 2, 7507,
    2, 3, 2, 5, 2, 23, 2, 3, 2, 2713973, 2, 499, 2, 3,
    2, 2237, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 372353,
    2, 61, 2, 3, 2, 5, 2, 389, 2, 3, 2, 3793, 2, 1193,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 41, 2, 7, 2, 3, 2, 5, 2, 6691, 2, 3, 2, 11,
    2, 19, 2, 3, 2, 173, 2, 3413, 2, 3, 2, 547097, 2, 5,
    2, 3, 2, 7, 2, 77761, 2, 3, 2, 5, 2, 163, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 557, 2, 37, 2, 3, 2, 457,
    2, 5, 2, 3, 2, 2099, 2, 59, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 7, 2, 359, 2, 3, 2, 11, 2, 401, 2, 3,
    2, 811, 2, 5, 2, 3, 2, 19, 2, 14071, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 49277, 2, 29, 2, 3, 2, 193, 2, 503,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 17, 2, 107, 2, 3, 2, 743,
    2, 463, 2, 3, 2, 11, 2, 5, 2, 3, 2, 137443, 2, 599,
    2, 3, 2, 5, 2, 229459, 2, 3, 2, 29, 2, 41, 2, 3,
    2, 73, 2, 7, 2, 3, 2, 67, 2, 5, 2, 3, 2, 59,
    2, 31, 2, 3, 2, 5, 2, 11, 2, 3, 2, 20599, 2, 6661,
    2, 3, 2, 7, 2, 17, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 5, 2, 263, 2, 3, 2, 523,
    2, 13, 2, 3, 2, 97, 2, 18583, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 53, 2, 3,
    2, 18859, 2, 7, 2, 3, 2, 8081, 2, 1019, 2, 3, 2, 1607,
    2, 5, 2, 3, 2, 23, 2, 37, 2, 3, 2, 5, 2, 29,
    2, 3, 2, 7, 2, 47, 2, 3, 2, 10067, 2, 787, 2, 3,
    2, 181, 2, 5, 2, 3, 2, 571, 2, 13, 2, 3, 2, 5,
    2, 67, 2, 3, 2, 2836271, 2, 73, 2, 3, 2, 19, 2, 11,
    2, 3, 2, 7, 2, 5, 2, 3, 2]

/-- A002386 row: the prime after 19581334192423 is 19581334192423 + 766. -/
theorem gap_19581334192423 : IsGapAt 19581334192423 766 :=
  isGapAt_of 19581334192423 766 (p19581334192423) (by show Nat.Prime 19581334193189; exact p19581334193189) ds_19581334192423 (by decide +kernel)

def ds_42842283925351 : List ℕ := [
    2, 3, 2, 5, 2, 7, 2, 3, 2, 257, 2, 13, 2, 3,
    2, 17, 2, 883, 2, 3, 2, 31, 2, 5, 2, 3, 2, 431911,
    2, 152639, 2, 3, 2, 5, 2, 37, 2, 3, 2, 251, 2, 2932691,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 5743, 2, 5, 2, 3,
    2, 50069, 2, 23, 2, 3, 2, 5, 2, 3243883, 2, 3, 2, 83,
    2, 97, 2, 3, 2, 7, 2, 343631, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 41, 2, 7, 2, 3, 2, 5, 2, 6661, 2, 3,
    2, 271, 2, 13687, 2, 3, 2, 23, 2, 43, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 509,
    2, 3, 2, 2113, 2, 7, 2, 3, 2, 73, 2, 1289, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 89, 2, 1259, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 7, 2, 3760147, 2, 3, 2, 211, 2, 13,
    2, 3, 2, 283, 2, 5, 2, 3, 2, 11, 2, 53, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 295837, 2, 384151, 2, 3, 2, 19,
    2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 31, 2, 47,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 11, 2, 3,
    2, 79, 2, 10069, 2, 3, 2, 355591, 2, 5, 2, 3, 2, 163,
    2, 531239, 2, 3, 2, 5, 2, 13, 2, 3, 2, 2333, 2, 41,
    2, 3, 2, 258331, 2, 7, 2, 3, 2, 191, 2, 5, 2, 3,
    2, 1523737, 2, 31, 2, 3, 2, 5, 2, 113, 2, 3, 2, 43,
    2, 73, 2, 3, 2, 7, 2, 11, 2, 3, 2, 29, 2, 5,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 151, 2, 3,
    2, 11, 2, 677, 2, 3, 2, 101, 2, 967, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 7, 2, 401, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 139, 2, 7, 2, 3, 2, 193, 2, 19, 2, 3,
    2, 41179, 2, 5, 2, 3, 2, 733, 2, 709507, 2, 3, 2, 5,
    2, 43, 2, 3, 2, 7, 2, 6203, 2, 3, 2, 11, 2, 1231,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 59, 2, 17, 2, 3,
    2, 5, 2, 109, 2, 3, 2, 127, 2, 13, 2, 3, 2, 37,
    2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2, 419, 2, 11,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 331, 2, 3579221, 2, 3,
    2, 3691, 2, 71, 2, 3, 2, 11, 2, 5, 2, 3, 2, 379,
    2, 2081, 2, 3, 2, 5, 2, 31, 2, 3, 2, 97, 2, 19,
    2, 3, 2, 29, 2, 7, 2, 3, 2, 92779, 2, 5, 2, 3,
    2, 325463, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 751,
    2, 17, 2, 3, 2, 7, 2, 41, 2, 3, 2, 113, 2, 5,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 1321, 2, 3,
    2, 23, 2, 686417, 2, 3, 2, 17, 2, 179, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 7, 2, 13799, 2, 3, 2, 5, 2, 919,
    2, 3, 2, 277087, 2, 7, 2, 3, 2, 67, 2, 13, 2, 3,
    2, 1158617, 2, 5, 2, 3, 2, 83, 2, 367, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 7, 2, 29, 2, 3, 2, 47, 2, 211,
    2, 3, 2, 27397, 2, 5, 2, 3, 2, 2131, 2, 983, 2, 3,
    2, 5, 2, 1804399, 2, 3, 2, 13, 2, 23, 2, 3, 2, 541,
    2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 3727,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 31, 2, 3,
    2, 61, 2, 197, 2, 3, 2, 19, 2, 5, 2, 3, 2, 23,
    2, 241, 2, 3, 2, 5, 2, 349, 2, 3, 2, 5717, 2, 283121,
    2, 3, 2, 5059, 2, 7, 2, 3, 2, 89, 2, 5, 2, 3,
    2, 13, 2, 19, 2, 3, 2, 5, 2, 17, 2, 3, 2, 79,
    2, 37, 2, 3, 2, 7, 2, 24593, 2, 3, 2, 51659, 2, 5,
    2, 3, 2, 181, 2, 7, 2, 3, 2, 5, 2, 761, 2, 3,
    2, 17, 2, 193, 2, 3, 2, 499, 2, 283, 2, 3, 2, 59,
    2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 29,
    2, 3, 2, 103, 2, 7, 2, 3, 2, 13, 2, 61, 2, 3,
    2, 11, 2, 5, 2, 3, 2]

/-- A002386 row: the prime after 42842283925351 is 42842283925351 + 778. -/
theorem gap_42842283925351 : IsGapAt 42842283925351 778 :=
  isGapAt_of 42842283925351 778 (p42842283925351) (by show Nat.Prime 42842283926129; exact p42842283926129) ds_42842283925351 (by decide +kernel)

def ds_90874329411493 : List ℕ := [
    2, 3, 2, 41, 2, 1009, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 7, 2, 173, 2, 3, 2, 5, 2, 211, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 31, 2, 150239, 2, 3, 2, 67, 2, 5,
    2, 3, 2, 24071, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 7, 2, 37, 2, 3, 2, 1531, 2, 157, 2, 3, 2, 463,
    2, 5, 2, 3, 2, 11, 2, 769, 2, 3, 2, 5, 2, 829,
    2, 3, 2, 89, 2, 252409, 2, 3, 2, 109, 2, 17, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 25171, 2, 2729, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 131, 2, 11, 2, 3, 2, 6135523, 2, 13,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 5099, 2, 5939, 2, 3,
    2, 5, 2, 97, 2, 3, 2, 859, 2, 8174783, 2, 3, 2, 53,
    2, 7, 2, 3, 2, 55411, 2, 5, 2, 3, 2, 101, 2, 19,
    2, 3, 2, 5, 2, 47, 2, 3, 2, 13, 2, 269, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 23561, 2, 5, 2, 3, 2, 71,
    2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 1543,
    2, 3, 2, 23, 2, 29, 2, 3, 2, 31, 2, 5, 2, 3,
    2, 7, 2, 43, 2, 3, 2, 5, 2, 1821191, 2, 3, 2, 1153,
    2, 7, 2, 3, 2, 19, 2, 2131, 2, 3, 2, 41, 2, 5,
    2, 3, 2, 13, 2, 5867, 2, 3, 2, 5, 2, 181, 2, 3,
    2, 7, 2, 23063, 2, 3, 2, 11, 2, 7191403, 2, 3, 2, 757,
    2, 5, 2, 3, 2, 128983, 2, 2707, 2, 3, 2, 5, 2, 107,
    2, 3, 2, 1567, 2, 17, 2, 3, 2, 179, 2, 23, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 797, 2, 11, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 383, 2, 137, 2, 3, 2, 13, 2, 1931,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 2609657, 2, 3299, 2, 3,
    2, 5, 2, 439, 2, 3, 2, 19, 2, 13, 2, 3, 2, 173,
    2, 7, 2, 3, 2, 653, 2, 5, 2, 3, 2, 397, 2, 197,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 79, 2, 29, 2, 3,
    2, 7, 2, 19, 2, 3, 2, 43, 2, 5, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 5, 2, 41, 2, 3, 2, 233, 2, 251,
    2, 3, 2, 5557, 2, 1019, 2, 3, 2, 37, 2, 5, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 5, 2, 23, 2, 3, 2, 29,
    2, 7, 2, 3, 2, 1091, 2, 47, 2, 3, 2, 73, 2, 5,
    2, 3, 2, 4066901, 2, 31, 2, 3, 2, 5, 2, 208129, 2, 3,
    2, 7, 2, 71, 2, 3, 2, 139, 2, 43, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 41, 2, 5179, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 107, 2, 19, 2, 3, 2, 144941, 2, 11, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 331, 2, 1451, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 11, 2, 347, 2, 3, 2, 8039, 2, 79,
    2, 3, 2, 47, 2, 5, 2, 3, 2, 1393039, 2, 18289, 2, 3,
    2, 5, 2, 29, 2, 3, 2, 13, 2, 101, 2, 3, 2, 13451,
    2, 7, 2, 3, 2, 1291, 2, 5, 2, 3, 2, 19, 2, 149,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 431, 2, 34511, 2, 3,
    2, 7, 2, 17, 2, 3, 2, 421, 2, 5, 2, 3, 2, 1663,
    2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 23, 2, 691,
    2, 3, 2, 4001, 2, 433, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 5, 2, 31, 2, 3, 2, 43,
    2, 7, 2, 3, 2, 19751, 2, 27043, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 1013827, 2, 1063, 2, 3, 2, 5, 2, 53, 2, 3,
    2, 7, 2, 83, 2, 3, 2, 59, 2, 34649, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 281, 2, 17, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 103, 2, 23, 2, 3, 2, 13, 2, 37, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 11, 2, 19, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 109, 2, 13, 2, 3, 2, 1327, 2, 7309,
    2, 3, 2, 2001397, 2, 5, 2, 3, 2, 23, 2, 2719, 2, 3,
    2, 5, 2, 6871, 2, 3, 2, 31, 2, 11, 2, 3, 2, 359,
    2, 7, 2, 3, 2, 53, 2, 5, 2, 3, 2, 29, 2, 9187,
    2, 3, 2, 5, 2]

/-- A002386 row: the prime after 90874329411493 is 90874329411493 + 804. -/
theorem gap_90874329411493 : IsGapAt 90874329411493 804 :=
  isGapAt_of 90874329411493 804 (p90874329411493) (by show Nat.Prime 90874329412297; exact p90874329412297) ds_90874329411493 (by decide +kernel)

def ds_171231342420521 : List ℕ := [
    2, 7, 2, 3, 2, 283, 2, 389357, 2, 3, 2, 113, 2, 5,
    2, 3, 2, 41, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 7, 2, 12809, 2, 3, 2, 2179, 2, 17359, 2, 3, 2, 53,
    2, 5, 2, 3, 2, 331, 2, 4698989, 2, 3, 2, 5, 2, 43,
    2, 3, 2, 17, 2, 89, 2, 3, 2, 19, 2, 11, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 251, 2, 1613, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 11, 2, 239, 2, 3, 2, 1583, 2, 13,
    2, 3, 2, 29, 2, 5, 2, 3, 2, 13921, 2, 1483, 2, 3,
    2, 5, 2, 131, 2, 3, 2, 47, 2, 149, 2, 3, 2, 101,
    2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 31, 2, 199,
    2, 3, 2, 5, 2, 433, 2, 3, 2, 13, 2, 3491093, 2, 3,
    2, 7, 2, 127, 2, 3, 2, 17, 2, 5, 2, 3, 2, 229,
    2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 41,
    2, 3, 2, 67, 2, 71, 2, 3, 2, 73, 2, 5, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 5, 2, 450811, 2, 3, 2, 103,
    2, 7, 2, 3, 2, 22481, 2, 19, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 13, 2, 17, 2, 3, 2, 5, 2, 18047, 2, 3,
    2, 7, 2, 3103531, 2, 3, 2, 3491, 2, 8971, 2, 3, 2, 8372467,
    2, 5, 2, 3, 2, 4077037, 2, 1824001, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 23, 2, 1373, 2, 3, 2, 29, 2, 8369, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 11, 2, 2999, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 79, 2, 4073, 2, 3, 2, 13, 2, 47,
    2, 3, 2, 2406689, 2, 5, 2, 3, 2, 139, 2, 67, 2, 3,
    2, 5, 2, 61, 2, 3, 2, 71, 2, 11, 2, 3, 2, 1523,
    2, 7, 2, 3, 2, 1279, 2, 5, 2, 3, 2, 102229, 2, 37,
    2, 3, 2, 5, 2, 751, 2, 3, 2, 53, 2, 23, 2, 3,
    2, 7, 2, 7745807, 2, 3, 2, 59, 2, 5, 2, 3, 2, 131,
    2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 223, 2, 29,
    2, 3, 2, 739, 2, 11, 2, 3, 2, 47, 2, 5, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 5, 2, 83, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 569, 2, 41, 2, 3, 2, 894259, 2, 5,
    2, 3, 2, 7963, 2, 5351, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 7, 2, 509, 2, 3, 2, 5449369, 2, 79, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 17, 2, 35963, 2, 3, 2, 5, 2, 587,
    2, 3, 2, 1377347, 2, 9073873, 2, 3, 2, 11, 2, 13, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 37, 2, 23, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 31, 2, 99041, 2, 3, 2, 1063, 2, 21313,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 19801, 2, 11, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 13, 2, 197, 2, 3, 2, 23,
    2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 2267, 2, 19,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 17, 2, 31, 2, 3,
    2, 7, 2, 8821, 2, 3, 2, 83, 2, 5, 2, 3, 2, 67,
    2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 491, 2, 143831,
    2, 3, 2, 277, 2, 59, 2, 3, 2, 1153, 2, 5, 2, 3,
    2, 7, 2, 137, 2, 3, 2, 5, 2, 109, 2, 3, 2, 73,
    2, 7, 2, 3, 2, 19, 2, 17, 2, 3, 2, 23689, 2, 5,
    2, 3, 2, 70459, 2, 3779, 2, 3, 2, 5, 2, 193, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 127, 2, 31627, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 53, 2, 1281871, 2, 3, 2, 5, 2, 431,
    2, 3, 2, 113, 2, 61, 2, 3, 2, 13, 2, 599, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 32173, 2, 331, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 37, 2, 13, 2, 3, 2, 59, 2, 11,
    2, 3, 2, 101, 2, 5, 2, 3, 2, 373, 2, 17, 2, 3,
    2, 5, 2, 269, 2, 3, 2, 11, 2, 1259, 2, 3, 2, 41,
    2, 7, 2, 3, 2, 3851, 2, 5, 2, 3, 2, 10037, 2, 151,
    2, 3, 2, 5, 2, 23, 2, 3, 2, 16747, 2, 601, 2, 3,
    2, 7, 2, 19, 2, 3, 2, 661, 2, 5, 2, 3, 2, 29,
    2, 7, 2, 3, 2, 5, 2]

/-- A002386 row: the prime after 171231342420521 is 171231342420521 + 806. -/
theorem gap_171231342420521 : IsGapAt 171231342420521 806 :=
  isGapAt_of 171231342420521 806 (p171231342420521) (by show Nat.Prime 171231342421327; exact p171231342421327) ds_171231342420521 (by decide +kernel)

end LeanLab.Verifications.Top50.Gaps2
