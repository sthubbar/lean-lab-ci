/-
P0005 Oliveira e Silva, Herzog, Pardi 2014, Table 9, page 2051, record-breaking first
occurrences P(g) of a prime gap g, part 4: each row IsGapAt P(g) g, that is P(g) and
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

theorem p21834433 : Nat.Prime 21834433 := by
  refine Pratt.pratt 21834433 7 [(2, 6), (3, 2), (37907, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p23340973 : Nat.Prime 23340973 := by
  refine Pratt.pratt 23340973 2 [(2, 2), (3, 1), (41, 1), (47441, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p26579827 : Nat.Prime 26579827 := by
  refine Pratt.pratt 26579827 3 [(2, 1), (3, 5), (7, 1), (13, 1), (601, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p28586501 : Nat.Prime 28586501 := by
  refine Pratt.pratt 28586501 2 [(2, 2), (5, 3), (57173, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p33535813 : Nat.Prime 33535813 := by
  refine Pratt.pratt 33535813 5 [(2, 2), (3, 1), (109, 1), (25639, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p57236831 : Nat.Prime 57236831 := by
  refine Pratt.pratt 57236831 7 [(2, 1), (5, 1), (7, 1), (817669, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p83444497 : Nat.Prime 83444497 := by
  refine Pratt.pratt 83444497 5 [(2, 4), (3, 1), (1738427, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p91187017 : Nat.Prime 91187017 := by
  refine Pratt.pratt 91187017 5 [(2, 3), (3, 1), (127, 1), (29917, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p124563701 : Nat.Prime 124563701 := by
  refine Pratt.pratt 124563701 2 [(2, 2), (5, 2), (29, 1), (42953, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p136193527 : Nat.Prime 136193527 := by
  refine Pratt.pratt 136193527 5 [(2, 1), (3, 2), (7, 1), (1080901, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p153519001 : Nat.Prime 153519001 := by
  refine Pratt.pratt 153519001 7 [(2, 3), (3, 1), (5, 3), (73, 1), (701, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p213637999 : Nat.Prime 213637999 := by
  refine Pratt.pratt 213637999 3 [(2, 1), (3, 1), (7, 1), (5086619, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p328179409 : Nat.Prime 328179409 := by
  refine Pratt.pratt 328179409 7 [(2, 4), (3, 1), (2027, 1), (3373, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p425277233 : Nat.Prime 425277233 := by
  refine Pratt.pratt 425277233 3 [(2, 4), (26579827, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p26579827
theorem p1819695211 : Nat.Prime 1819695211 := by
  refine Pratt.pratt 1819695211 3 [(2, 1), (3, 1), (5, 1), (41, 1), (67, 1), (71, 1), (311, 1)] (by norm_num)
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
theorem p4308360109 : Nat.Prime 4308360109 := by
  refine Pratt.pratt 4308360109 6 [(2, 2), (3, 1), (13, 1), (137, 1), (201589, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p4373483311 : Nat.Prime 4373483311 := by
  refine Pratt.pratt 4373483311 6 [(2, 1), (3, 2), (5, 1), (7, 1), (83, 1), (83639, 1)] (by norm_num)
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
theorem p4700035979 : Nat.Prime 4700035979 := by
  refine Pratt.pratt 4700035979 2 [(2, 1), (11, 1), (213637999, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p213637999
theorem p5103326797 : Nat.Prime 5103326797 := by
  refine Pratt.pratt 5103326797 2 [(2, 2), (3, 1), (425277233, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p425277233
theorem p7155155443 : Nat.Prime 7155155443 := by
  refine Pratt.pratt 7155155443 2 [(2, 1), (3, 1), (29, 1), (197, 1), (208739, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p10349521243 : Nat.Prime 10349521243 := by
  refine Pratt.pratt 10349521243 2 [(2, 1), (3, 1), (79, 1), (21834433, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p21834433
theorem p15570804593 : Nat.Prime 15570804593 := by
  refine Pratt.pratt 15570804593 3 [(2, 4), (7, 1), (23, 1), (193, 1), (31319, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p19410462553 : Nat.Prime 19410462553 := by
  refine Pratt.pratt 19410462553 7 [(2, 3), (3, 1), (13, 2), (37, 1), (129341, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p28620621773 : Nat.Prime 28620621773 := by
  refine Pratt.pratt 28620621773 2 [(2, 2), (7155155443, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p7155155443
theorem p57670145173 : Nat.Prime 57670145173 := by
  refine Pratt.pratt 57670145173 2 [(2, 2), (3, 2), (523, 1), (3062999, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p115369928587 : Nat.Prime 115369928587 := by
  refine Pratt.pratt 115369928587 2 [(2, 1), (3, 4), (11, 1), (37, 1), (1749779, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p156384689009 : Nat.Prime 156384689009 := by
  refine Pratt.pratt 156384689009 3 [(2, 4), (127, 1), (5651, 1), (13619, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p223326230443 : Nat.Prime 223326230443 := by
  refine Pratt.pratt 223326230443 5 [(2, 1), (3, 1), (7, 1), (29, 1), (37, 1), (4955537, 1)] (by norm_num)
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
theorem p278448635243 : Nat.Prime 278448635243 := by
  refine Pratt.pratt 278448635243 2 [(2, 1), (1249, 1), (8839, 1), (12611, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p346020871039 : Nat.Prime 346020871039 := by
  refine Pratt.pratt 346020871039 17 [(2, 1), (3, 1), (57670145173, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p57670145173
theorem p1310180551921 : Nat.Prime 1310180551921 := by
  refine Pratt.pratt 1310180551921 7 [(2, 4), (3, 2), (5, 1), (1819695211, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p1819695211
theorem p1841086484491 : Nat.Prime 1841086484491 := by
  refine Pratt.pratt 1841086484491 3 [(2, 1), (3, 1), (5, 1), (11, 1), (17, 1), (328179409, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p328179409
theorem p1841086484999 : Nat.Prime 1841086484999 := by
  refine Pratt.pratt 1841086484999 11 [(2, 1), (29, 2), (3001, 1), (364739, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p2209016910131 : Nat.Prime 2209016910131 := by
  refine Pratt.pratt 2209016910131 6 [(2, 1), (5, 1), (47, 1), (4700035979, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p4700035979
theorem p2209016910641 : Nat.Prime 2209016910641 := by
  refine Pratt.pratt 2209016910641 3 [(2, 4), (5, 1), (7193, 1), (3838831, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p2296497058133 : Nat.Prime 2296497058133 := by
  refine Pratt.pratt 2296497058133 2 [(2, 2), (401, 1), (439, 1), (1789, 1), (1823, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p2296497058651 : Nat.Prime 2296497058651 := by
  refine Pratt.pratt 2296497058651 3 [(2, 1), (3, 2), (5, 2), (5103326797, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p5103326797
theorem p2336167262449 : Nat.Prime 2336167262449 := by
  refine Pratt.pratt 2336167262449 7 [(2, 4), (3, 3), (41, 1), (419, 1), (433, 1), (727, 1)] (by norm_num)
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
theorem p2336167262969 : Nat.Prime 2336167262969 := by
  refine Pratt.pratt 2336167262969 3 [(2, 3), (7, 1), (11, 1), (17, 1), (67, 1), (3329657, 1)] (by norm_num)
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
theorem p2685642108881 : Nat.Prime 2685642108881 := by
  refine Pratt.pratt 2685642108881 6 [(2, 4), (5, 1), (18413, 1), (1823197, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p3922577571959 : Nat.Prime 3922577571959 := by
  refine Pratt.pratt 3922577571959 7 [(2, 1), (17, 1), (115369928587, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p115369928587
theorem p4153838986343 : Nat.Prime 4153838986343 := by
  refine Pratt.pratt 4153838986343 5 [(2, 1), (107, 1), (19410462553, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p19410462553
theorem p5371284217763 : Nat.Prime 5371284217763 := by
  refine Pratt.pratt 5371284217763 2 [(2, 1), (2685642108881, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p2685642108881
theorem p5371284218299 : Nat.Prime 5371284218299 := by
  refine Pratt.pratt 5371284218299 2 [(2, 1), (3, 1), (17, 1), (88897, 1), (592367, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p6010330572331 : Nat.Prime 6010330572331 := by
  refine Pratt.pratt 6010330572331 2 [(2, 1), (3, 1), (5, 1), (7, 1), (28620621773, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p28620621773
theorem p6010330572899 : Nat.Prime 6010330572899 := by
  refine Pratt.pratt 6010330572899 2 [(2, 1), (193, 1), (15570804593, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p15570804593
theorem p8817792098461 : Nat.Prime 8817792098461 := by
  refine Pratt.pratt 8817792098461 6 [(2, 2), (3, 1), (5, 1), (53, 1), (97, 1), (28586501, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p28586501
theorem p8817792099037 : Nat.Prime 8817792099037 := by
  refine Pratt.pratt 8817792099037 6 [(2, 2), (3, 1), (71, 1), (10349521243, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p10349521243
theorem p9383081340541 : Nat.Prime 9383081340541 := by
  refine Pratt.pratt 9383081340541 7 [(2, 2), (3, 1), (5, 1), (156384689009, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p156384689009
theorem p9383081341121 : Nat.Prime 9383081341121 := by
  refine Pratt.pratt 9383081341121 6 [(2, 6), (5, 1), (191, 1), (153519001, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p153519001
theorem p13730905888633 : Nat.Prime 13730905888633 := by
  refine Pratt.pratt 13730905888633 7 [(2, 3), (3, 2), (1531, 1), (124563701, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p124563701
theorem p18421111705933 : Nat.Prime 18421111705933 := by
  refine Pratt.pratt 18421111705933 6 [(2, 2), (3, 4), (13, 1), (4373483311, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p4373483311
theorem p20761252261751 : Nat.Prime 20761252261751 := by
  refine Pratt.pratt 20761252261751 7 [(2, 1), (5, 3), (7, 3), (11, 1), (13, 1), (1693103, 1)] (by norm_num)
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
theorem p20761252262341 : Nat.Prime 20761252262341 := by
  refine Pratt.pratt 20761252262341 2 [(2, 2), (3, 1), (5, 1), (346020871039, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p346020871039
theorem p20767330530329 : Nat.Prime 20767330530329 := by
  refine Pratt.pratt 20767330530329 3 [(2, 3), (4241, 1), (11279, 1), (54269, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p20767330530937 : Nat.Prime 20767330530937 := by
  refine Pratt.pratt 20767330530937 10 [(2, 3), (3, 2), (11, 1), (53, 1), (1847, 1), (267863, 1)] (by norm_num)
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
theorem p24923033918059 : Nat.Prime 24923033918059 := by
  refine Pratt.pratt 24923033918059 2 [(2, 1), (3, 1), (4153838986343, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p4153838986343
theorem p24923033918683 : Nat.Prime 24923033918683 := by
  refine Pratt.pratt 24923033918683 23 [(2, 1), (3, 1), (17, 1), (53, 1), (71, 1), (103, 1), (149, 1), (4231, 1)] (by norm_num)
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
theorem p33605480400197 : Nat.Prime 33605480400197 := by
  refine Pratt.pratt 33605480400197 2 [(2, 2), (61687, 1), (136193527, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p136193527
theorem p33605480400823 : Nat.Prime 33605480400823 := by
  refine Pratt.pratt 33605480400823 5 [(2, 1), (3, 2), (11, 2), (23, 1), (83, 1), (1129, 1), (7159, 1)] (by norm_num)
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
theorem p34140047613391 : Nat.Prime 34140047613391 := by
  refine Pratt.pratt 34140047613391 6 [(2, 1), (3, 2), (5, 1), (447439, 1), (847789, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p34140047614019 : Nat.Prime 34140047614019 := by
  refine Pratt.pratt 34140047614019 2 [(2, 1), (731333, 1), (23340973, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p23340973
theorem p45678685880759 : Nat.Prime 45678685880759 := by
  refine Pratt.pratt 45678685880759 7 [(2, 1), (7, 1), (61, 1), (641, 1), (83444497, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p83444497
theorem p45678685881391 : Nat.Prime 45678685881391 := by
  refine Pratt.pratt 45678685881391 3 [(2, 1), (3, 1), (5, 1), (23, 1), (41, 1), (5749, 1), (280859, 1)] (by norm_num)
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
theorem p51027160468351 : Nat.Prime 51027160468351 := by
  refine Pratt.pratt 51027160468351 3 [(2, 1), (3, 1), (5, 2), (11, 1), (19, 1), (61, 1), (79, 1), (337759, 1)] (by norm_num)
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
theorem p51027160468997 : Nat.Prime 51027160468997 := by
  refine Pratt.pratt 51027160468997 2 [(2, 2), (19, 1), (37, 1), (199, 1), (91187017, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p91187017
theorem p54916086007427 : Nat.Prime 54916086007427 := by
  refine Pratt.pratt 54916086007427 2 [(2, 1), (7, 1), (3922577571959, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p3922577571959
theorem p54916086008081 : Nat.Prime 54916086008081 := by
  refine Pratt.pratt 54916086008081 3 [(2, 4), (5, 1), (11, 2), (503, 1), (1381, 1), (8167, 1)] (by norm_num)
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
theorem p65862966031241 : Nat.Prime 65862966031241 := by
  refine Pratt.pratt 65862966031241 6 [(2, 3), (5, 1), (7, 1), (41, 1), (1741, 1), (3295343, 1)] (by norm_num)
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
theorem p65862966031897 : Nat.Prime 65862966031897 := by
  refine Pratt.pratt 65862966031897 5 [(2, 3), (3, 1), (11, 1), (41, 1), (1283, 1), (4742713, 1)] (by norm_num)
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
theorem p78610833115261 : Nat.Prime 78610833115261 := by
  refine Pratt.pratt 78610833115261 2 [(2, 2), (3, 1), (5, 1), (1310180551921, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p1310180551921
theorem p78610833115937 : Nat.Prime 78610833115937 := by
  refine Pratt.pratt 78610833115937 3 [(2, 5), (11, 1), (223326230443, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p223326230443
theorem p82385435331119 : Nat.Prime 82385435331119 := by
  refine Pratt.pratt 82385435331119 7 [(2, 1), (719689, 1), (57236831, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p57236831
theorem p82385435331799 : Nat.Prime 82385435331799 := by
  refine Pratt.pratt 82385435331799 3 [(2, 1), (3, 1), (13730905888633, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p13730905888633
theorem p110526670235599 : Nat.Prime 110526670235599 := by
  refine Pratt.pratt 110526670235599 3 [(2, 1), (3, 1), (18421111705933, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p18421111705933
theorem p110526670236287 : Nat.Prime 110526670236287 := by
  refine Pratt.pratt 110526670236287 5 [(2, 1), (101, 1), (127, 1), (4308360109, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p4308360109
theorem p143679495784681 : Nat.Prime 143679495784681 := by
  refine Pratt.pratt 143679495784681 7 [(2, 3), (3, 3), (5, 1), (3967, 1), (33535813, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p33535813
theorem p143679495785389 : Nat.Prime 143679495785389 := by
  refine Pratt.pratt 143679495785389 2 [(2, 2), (3, 1), (43, 1), (278448635243, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p278448635243
theorem p218356872845927 : Nat.Prime 218356872845927 := by
  refine Pratt.pratt 218356872845927 5 [(2, 1), (41, 1), (6211, 1), (16661, 1), (25733, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p218356872846649 : Nat.Prime 218356872846649 := by
  refine Pratt.pratt 218356872846649 7 [(2, 3), (3, 1), (131, 1), (78577, 1), (883871, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

def gds_508 : List ℕ := [
    2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 7, 2, 3, 2, 17,
    2, 19417, 2, 3, 2, 1597, 2, 5, 2, 3, 2, 149, 2, 19, 2, 3,
    2, 5, 2, 17971, 2, 3, 2, 7, 2, 821, 2, 3, 2, 109, 2, 1019,
    2, 3, 2, 4937, 2, 5, 2, 3, 2, 13, 2, 43, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 47, 2, 29, 2, 3, 2, 11, 2, 31, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 2473, 2, 197, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 3391, 2, 211, 2, 3, 2, 19, 2, 157, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2, 3433, 2, 3,
    2, 29, 2, 37, 2, 3, 2, 13, 2, 7, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 1489, 2, 15641, 2, 3, 2, 5, 2, 1381, 2, 3, 2, 613,
    2, 13, 2, 3, 2, 7, 2, 1237, 2, 3, 2, 1195979, 2, 5, 2, 3,
    2, 79, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 210869, 2, 372707,
    2, 3, 2, 41, 2, 71, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7,
    2, 1104889, 2, 3, 2, 5, 2, 59, 2, 3, 2, 17, 2, 7, 2, 3,
    2, 61553, 2, 67, 2, 3, 2, 43, 2, 5, 2, 3, 2, 521, 2, 13,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 11, 2, 3, 2, 205397,
    2, 19, 2, 3, 2, 8017, 2, 5, 2, 3, 2, 20173, 2, 44041, 2, 3,
    2, 5, 2, 163, 2, 3, 2, 37, 2, 555307, 2, 3, 2, 151, 2, 17,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 233, 2, 83, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 967, 2, 1151, 2, 3, 2, 14411, 2, 11, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 443, 2, 1699, 2, 3, 2, 5, 2, 79,
    2, 3, 2, 11, 2, 23, 2, 3, 2, 1531, 2, 7, 2, 3, 2, 47,
    2, 5, 2, 3, 2, 389, 2, 41, 2, 3, 2, 5, 2, 3889, 2, 3,
    2, 13, 2, 19, 2, 3, 2, 7, 2, 11159, 2, 3, 2, 42697, 2, 5,
    2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 53,
    2, 194057, 2, 3, 2, 11, 2, 115597, 2, 3, 2, 179, 2, 5, 2, 3,
    2, 7, 2, 29, 2, 3, 2, 5, 2, 317, 2, 3, 2, 199, 2, 7,
    2, 3, 2, 1607, 2, 107, 2, 3, 2, 41, 2, 5, 2, 3, 2, 13,
    2, 11, 2, 3, 2, 5, 2, 13183, 2, 3, 2, 7, 2, 293, 2, 3,
    2, 83, 2, 101, 2, 3, 2, 11, 2, 5, 2, 3, 2, 29, 2, 23,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 43, 2, 17, 2, 3, 2, 67,
    2, 4051, 2, 3, 2, 7, 2, 5, 2, 3, 2]

/-- Table 9 row: the prime after 1841086484491 is 1841086484491 + 508. -/
theorem gap9_508 : IsGapAt 1841086484491 508 :=
  isGapAt_of 1841086484491 508 (p1841086484491) (by show Nat.Prime 1841086484999; exact p1841086484999) gds_508 (by decide +kernel)

def gds_510 : List ℕ := [
    2, 11, 2, 3, 2, 229, 2, 13, 2, 3, 2, 41, 2, 5, 2, 3,
    2, 7, 2, 79, 2, 3, 2, 5, 2, 19, 2, 3, 2, 59, 2, 7,
    2, 3, 2, 4049, 2, 43, 2, 3, 2, 1447, 2, 5, 2, 3, 2, 17,
    2, 630481, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 139, 2, 3,
    2, 328687, 2, 11, 2, 3, 2, 149, 2, 5, 2, 3, 2, 613, 2, 151,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 167, 2, 3, 2, 83,
    2, 163, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23327, 2, 19259, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 77417, 2, 127, 2, 3, 2, 101, 2, 71,
    2, 3, 2, 1187, 2, 5, 2, 3, 2, 13, 2, 19, 2, 3, 2, 5,
    2, 1913, 2, 3, 2, 17, 2, 977, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 17401, 2, 908081, 2, 3, 2, 5, 2, 41,
    2, 3, 2, 199, 2, 379207, 2, 3, 2, 7, 2, 1249, 2, 3, 2, 263323,
    2, 5, 2, 3, 2, 533459, 2, 7, 2, 3, 2, 5, 2, 10337, 2, 3,
    2, 31, 2, 37, 2, 3, 2, 13, 2, 17, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 2243, 2, 3, 2, 761983,
    2, 7, 2, 3, 2, 181, 2, 1169747, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 41, 2, 53, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 31,
    2, 3, 2, 2381, 2, 31183, 2, 3, 2, 2351, 2, 5, 2, 3, 2, 11,
    2, 340583, 2, 3, 2, 5, 2, 43, 2, 3, 2, 23, 2, 2347, 2, 3,
    2, 1151, 2, 1078183, 2, 3, 2, 7, 2, 5, 2, 3, 2, 367, 2, 13,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 11, 2, 3, 2, 79,
    2, 409, 2, 3, 2, 359, 2, 5, 2, 3, 2, 73, 2, 266351, 2, 3,
    2, 5, 2, 136481, 2, 3, 2, 37, 2, 5039, 2, 3, 2, 53, 2, 7,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 417437, 2, 1697, 2, 3, 2, 5,
    2, 4637, 2, 3, 2, 113, 2, 23, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 191, 2, 5, 2, 3, 2, 3361, 2, 7, 2, 3, 2, 5, 2, 599,
    2, 3, 2, 11, 2, 17, 2, 3, 2, 167, 2, 83, 2, 3, 2, 1231,
    2, 5, 2, 3, 2, 7, 2, 691, 2, 3, 2, 5, 2, 701, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 17, 2, 31, 2, 3, 2, 29, 2, 5,
    2, 3, 2, 43, 2, 109, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7,
    2, 19, 2, 3, 2, 11, 2, 1325227, 2, 3, 2, 7537, 2, 5, 2, 3,
    2, 431, 2, 388573, 2, 3, 2, 5, 2, 482017, 2, 3, 2]

/-- Table 9 row: the prime after 2209016910131 is 2209016910131 + 510. -/
theorem gap9_510 : IsGapAt 2209016910131 510 :=
  isGapAt_of 2209016910131 510 (p2209016910131) (by show Nat.Prime 2209016910641; exact p2209016910641) gds_510 (by decide +kernel)

def gds_518 : List ℕ := [
    2, 5, 2, 3, 2, 151, 2, 11, 2, 3, 2, 5, 2, 43, 2, 3,
    2, 4889, 2, 31, 2, 3, 2, 229, 2, 159539, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 53, 2, 115903, 2, 3, 2, 5, 2, 7, 2, 3, 2, 197,
    2, 37, 2, 3, 2, 5987, 2, 70423, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 17, 2, 1454419, 2, 3, 2, 5, 2, 11, 2, 3, 2, 41, 2, 7321,
    2, 3, 2, 2437, 2, 7, 2, 3, 2, 64019, 2, 5, 2, 3, 2, 11,
    2, 181, 2, 3, 2, 5, 2, 19, 2, 3, 2, 1260841, 2, 2309, 2, 3,
    2, 7, 2, 4157, 2, 3, 2, 2833, 2, 5, 2, 3, 2, 109, 2, 7,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 13, 2, 11, 2, 3, 2, 31,
    2, 730297, 2, 3, 2, 227, 2, 5, 2, 3, 2, 7, 2, 673, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 17, 2, 7, 2, 3, 2, 937, 2, 463,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 43, 2, 113, 2, 3, 2, 5,
    2, 3109, 2, 3, 2, 7, 2, 47, 2, 3, 2, 101, 2, 11, 2, 3,
    2, 79, 2, 5, 2, 3, 2, 13, 2, 19, 2, 3, 2, 5, 2, 2311,
    2, 3, 2, 11, 2, 24469, 2, 3, 2, 4721, 2, 17, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 132137, 2, 53, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 557747, 2, 23, 2, 3, 2, 1051, 2, 17291, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 933001, 2, 642797, 2, 3, 2, 5, 2, 107, 2, 3, 2, 61,
    2, 277, 2, 3, 2, 11, 2, 7, 2, 3, 2, 67, 2, 5, 2, 3,
    2, 23, 2, 151, 2, 3, 2, 5, 2, 2963, 2, 3, 2, 2069, 2, 13,
    2, 3, 2, 7, 2, 95191, 2, 3, 2, 31, 2, 5, 2, 3, 2, 1447007,
    2, 7, 2, 3, 2, 5, 2, 109, 2, 3, 2, 1001723, 2, 173, 2, 3,
    2, 53, 2, 29, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 79,
    2, 3, 2, 5, 2, 131, 2, 3, 2, 33461, 2, 7, 2, 3, 2, 54647,
    2, 191, 2, 3, 2, 4057, 2, 5, 2, 3, 2, 4253, 2, 13, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 7, 2, 61, 2, 3, 2, 29, 2, 671911,
    2, 3, 2, 37, 2, 5, 2, 3, 2, 11, 2, 36607, 2, 3, 2, 5,
    2, 67, 2, 3, 2, 439, 2, 17, 2, 3, 2, 23, 2, 19, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 163901, 2, 332117, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 1129, 2, 11, 2, 3, 2, 17, 2, 13, 2, 3, 2, 149,
    2, 5, 2, 3, 2, 8093, 2, 41, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 107, 2, 773, 2, 3, 2, 9371, 2, 7, 2, 3, 2, 35999, 2, 5,
    2, 3, 2, 31, 2]

/-- Table 9 row: the prime after 2296497058133 is 2296497058133 + 518. -/
theorem gap9_518 : IsGapAt 2296497058133 518 :=
  isGapAt_of 2296497058133 518 (p2296497058133) (by show Nat.Prime 2296497058651; exact p2296497058651) gds_518 (by decide +kernel)

def gds_520 : List ℕ := [
    2, 3, 2, 997091, 2, 5, 2, 3, 2, 347, 2, 29, 2, 3, 2, 5,
    2, 739, 2, 3, 2, 7, 2, 11, 2, 3, 2, 1231, 2, 23, 2, 3,
    2, 53437, 2, 5, 2, 3, 2, 41, 2, 37, 2, 3, 2, 5, 2, 139,
    2, 3, 2, 18217, 2, 43, 2, 3, 2, 13, 2, 17, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 29, 2, 3833, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 71, 2, 13, 2, 3, 2, 400657, 2, 11, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 6857, 2, 97, 2, 3, 2, 5, 2, 173, 2, 3, 2, 11,
    2, 353, 2, 3, 2, 1907, 2, 7, 2, 3, 2, 102539, 2, 5, 2, 3,
    2, 79, 2, 823, 2, 3, 2, 5, 2, 31, 2, 3, 2, 263, 2, 197,
    2, 3, 2, 7, 2, 9907, 2, 3, 2, 47111, 2, 5, 2, 3, 2, 1308029,
    2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 107, 2, 19, 2, 3,
    2, 11, 2, 13339, 2, 3, 2, 47, 2, 5, 2, 3, 2, 7, 2, 53,
    2, 3, 2, 5, 2, 80149, 2, 3, 2, 17987, 2, 7, 2, 3, 2, 503,
    2, 359, 2, 3, 2, 13, 2, 5, 2, 3, 2, 1499, 2, 11, 2, 3,
    2, 5, 2, 193, 2, 3, 2, 7, 2, 191, 2, 3, 2, 257, 2, 13,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 19, 2, 1619, 2, 3, 2, 5,
    2, 10099, 2, 3, 2, 31, 2, 17, 2, 3, 2, 761, 2, 61, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 109, 2, 597497, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 13, 2, 379, 2, 3, 2, 17, 2, 113, 2, 3, 2, 227,
    2, 5, 2, 3, 2, 11, 2, 43, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 34057, 2, 31, 2, 3, 2, 1867, 2, 7, 2, 3, 2, 73, 2, 5,
    2, 3, 2, 3943, 2, 557, 2, 3, 2, 5, 2, 590323, 2, 3, 2, 23,
    2, 11, 2, 3, 2, 7, 2, 29, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 5, 2, 104009, 2, 3, 2, 1307, 2, 1997,
    2, 3, 2, 2593, 2, 101, 2, 3, 2, 5849, 2, 5, 2, 3, 2, 7,
    2, 19, 2, 3, 2, 5, 2, 690089, 2, 3, 2, 37, 2, 7, 2, 3,
    2, 29, 2, 11, 2, 3, 2, 6277, 2, 5, 2, 3, 2, 433787, 2, 433,
    2, 3, 2, 5, 2, 2381, 2, 3, 2, 7, 2, 23, 2, 3, 2, 13,
    2, 41, 2, 3, 2, 173, 2, 5, 2, 3, 2, 1509229, 2, 116681, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 449, 2, 13, 2, 3, 2, 19, 2, 73,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 1179047, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 17, 2, 11719, 2, 3, 2, 11, 2, 31, 2, 3,
    2, 61, 2, 5, 2, 3, 2]

/-- Table 9 row: the prime after 2336167262449 is 2336167262449 + 520. -/
theorem gap9_520 : IsGapAt 2336167262449 520 :=
  isGapAt_of 2336167262449 520 (p2336167262449) (by show Nat.Prime 2336167262969; exact p2336167262969) gds_520 (by decide +kernel)

def gds_536 : List ℕ := [
    2, 5, 2, 3, 2, 6089, 2, 17, 2, 3, 2, 5, 2, 211, 2, 3,
    2, 41, 2, 11, 2, 3, 2, 67, 2, 7, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 223, 2, 1049821, 2, 3, 2, 5, 2, 4723, 2, 3, 2, 151,
    2, 827, 2, 3, 2, 7, 2, 13, 2, 3, 2, 31, 2, 5, 2, 3,
    2, 839, 2, 7, 2, 3, 2, 5, 2, 197, 2, 3, 2, 409, 2, 29,
    2, 3, 2, 206411, 2, 11, 2, 3, 2, 73, 2, 5, 2, 3, 2, 7,
    2, 6091, 2, 3, 2, 5, 2, 23, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 331, 2, 53, 2, 3, 2, 142061, 2, 5, 2, 3, 2, 727, 2, 27691,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 71, 2, 3, 2, 17,
    2, 43, 2, 3, 2, 23, 2, 5, 2, 3, 2, 2999, 2, 67, 2, 3,
    2, 5, 2, 3209, 2, 3, 2, 2170757, 2, 347, 2, 3, 2, 11, 2, 1873,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 227, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 101, 2, 89, 2, 3, 2, 251, 2, 173, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 61, 2, 11, 2, 3, 2, 5, 2, 3491,
    2, 3, 2, 97, 2, 131, 2, 3, 2, 37811, 2, 7, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 17, 2, 19, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 83, 2, 10177, 2, 3, 2, 7, 2, 1201, 2, 3, 2, 345221, 2, 5,
    2, 3, 2, 47, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 23,
    2, 13, 2, 3, 2, 271, 2, 9013, 2, 3, 2, 449, 2, 5, 2, 3,
    2, 7, 2, 31, 2, 3, 2, 5, 2, 17, 2, 3, 2, 43, 2, 7,
    2, 3, 2, 19, 2, 378503, 2, 3, 2, 397, 2, 5, 2, 3, 2, 59,
    2, 61, 2, 3, 2, 5, 2, 2357, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 1604297, 2, 320953, 2, 3, 2, 2647, 2, 5, 2, 3, 2, 4691, 2, 13,
    2, 3, 2, 5, 2, 179, 2, 3, 2, 89, 2, 23, 2, 3, 2, 967,
    2, 45007, 2, 3, 2, 7, 2, 5, 2, 3, 2, 108223, 2, 193, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 229, 2, 19867, 2, 3, 2, 5153, 2, 11,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 23, 2, 29, 2, 3, 2, 5,
    2, 53, 2, 3, 2, 11, 2, 136189, 2, 3, 2, 485101, 2, 7, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 199, 2, 433, 2, 3, 2, 5, 2, 47,
    2, 3, 2, 197, 2, 20431, 2, 3, 2, 7, 2, 19, 2, 3, 2, 1019,
    2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3,
    2, 13, 2, 419, 2, 3, 2, 11, 2, 37, 2, 3, 2, 41, 2, 5,
    2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 13, 2, 3, 2, 73,
    2, 7, 2, 3, 2, 149113, 2]

/-- Table 9 row: the prime after 5371284217763 is 5371284217763 + 536. -/
theorem gap9_536 : IsGapAt 5371284217763 536 :=
  isGapAt_of 5371284217763 536 (p5371284217763) (by show Nat.Prime 5371284218299; exact p5371284218299) gds_536 (by decide +kernel)

def gds_568 : List ℕ := [
    2, 3, 2, 5, 2, 7, 2, 3, 2, 743, 2, 272093, 2, 3, 2, 643,
    2, 17, 2, 3, 2, 29, 2, 5, 2, 3, 2, 59, 2, 19, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 911, 2, 11743, 2, 3, 2, 31, 2, 7,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 11, 2, 7103, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 569, 2, 1239397, 2, 3, 2, 7, 2, 1871, 2, 3,
    2, 43, 2, 5, 2, 3, 2, 131, 2, 7, 2, 3, 2, 5, 2, 107,
    2, 3, 2, 36847, 2, 11, 2, 3, 2, 19, 2, 31, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 239, 2, 3,
    2, 28591, 2, 7, 2, 3, 2, 13, 2, 29, 2, 3, 2, 149, 2, 5,
    2, 3, 2, 617, 2, 541, 2, 3, 2, 5, 2, 10193, 2, 3, 2, 7,
    2, 13, 2, 3, 2, 7321, 2, 11, 2, 3, 2, 1979, 2, 5, 2, 3,
    2, 79843, 2, 1193, 2, 3, 2, 5, 2, 181, 2, 3, 2, 11, 2, 503,
    2, 3, 2, 29, 2, 1283831, 2, 3, 2, 7, 2, 5, 2, 3, 2, 42473,
    2, 173, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 17, 2, 3,
    2, 229, 2, 41, 2, 3, 2, 31, 2, 5, 2, 3, 2, 2306107, 2, 13,
    2, 3, 2, 5, 2, 113, 2, 3, 2, 23, 2, 2551, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 1082581, 2, 5, 2, 3, 2, 37, 2, 353, 2, 3,
    2, 5, 2, 61, 2, 3, 2, 163, 2, 461, 2, 3, 2, 7, 2, 67,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 1171, 2, 7, 2, 3, 2, 5,
    2, 12799, 2, 3, 2, 41, 2, 29, 2, 3, 2, 311, 2, 13, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 7, 2, 1289, 2, 3, 2, 5, 2, 71,
    2, 3, 2, 43, 2, 7, 2, 3, 2, 337, 2, 487, 2, 3, 2, 2801,
    2, 5, 2, 3, 2, 17, 2, 263, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 7, 2, 19, 2, 3, 2, 125737, 2, 533363, 2, 3, 2, 59, 2, 5,
    2, 3, 2, 11, 2, 103, 2, 3, 2, 5, 2, 13, 2, 3, 2, 257,
    2, 118901, 2, 3, 2, 1627643, 2, 2269, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 31, 2, 268613, 2, 3, 2, 5, 2, 7, 2, 3, 2, 53, 2, 11,
    2, 3, 2, 919, 2, 117833, 2, 3, 2, 1531, 2, 5, 2, 3, 2, 13,
    2, 28579, 2, 3, 2, 5, 2, 127, 2, 3, 2, 17, 2, 101, 2, 3,
    2, 83, 2, 7, 2, 3, 2, 113, 2, 5, 2, 3, 2, 71, 2, 23,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 37, 2, 137, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 6569, 2, 5, 2, 3, 2, 439289, 2, 7, 2, 3,
    2, 5, 2, 13499, 2, 3, 2, 11, 2, 499, 2, 3, 2, 13, 2, 17,
    2, 3, 2, 389, 2, 5, 2, 3, 2, 7, 2, 159079, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 251, 2, 7, 2, 3, 2, 41, 2, 67073, 2, 3,
    2, 17, 2, 5, 2, 3, 2]

/-- Table 9 row: the prime after 6010330572331 is 6010330572331 + 568. -/
theorem gap9_568 : IsGapAt 6010330572331 568 :=
  isGapAt_of 6010330572331 568 (p6010330572331) (by show Nat.Prime 6010330572899; exact p6010330572899) gds_568 (by decide +kernel)

def gds_576 : List ℕ := [
    2, 3, 2, 5, 2, 11, 2, 3, 2, 29, 2, 23, 2, 3, 2, 181,
    2, 7, 2, 3, 2, 41, 2, 5, 2, 3, 2, 11, 2, 79601, 2, 3,
    2, 5, 2, 67, 2, 3, 2, 17, 2, 2089, 2, 3, 2, 7, 2, 1033,
    2, 3, 2, 53, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 13, 2, 11, 2, 3, 2, 2113, 2, 71, 2, 3,
    2, 107, 2, 5, 2, 3, 2, 7, 2, 239, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 251, 2, 7, 2, 3, 2, 216743, 2, 17, 2, 3, 2, 208009,
    2, 5, 2, 3, 2, 37, 2, 2309761, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 7, 2, 383, 2, 3, 2, 167, 2, 11, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 13, 2, 23, 2, 3, 2, 5, 2, 31, 2, 3, 2, 11,
    2, 5279, 2, 3, 2, 134777, 2, 347, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 19, 2, 9803, 2, 3, 2, 5, 2, 7, 2, 3, 2, 197, 2, 37,
    2, 3, 2, 23, 2, 87323, 2, 3, 2, 1087, 2, 5, 2, 3, 2, 767359,
    2, 17, 2, 3, 2, 5, 2, 19, 2, 3, 2, 71, 2, 163, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 263, 2, 5, 2, 3, 2, 1847, 2, 1447,
    2, 3, 2, 5, 2, 149, 2, 3, 2, 349, 2, 13, 2, 3, 2, 7,
    2, 7883, 2, 3, 2, 821, 2, 5, 2, 3, 2, 41, 2, 7, 2, 3,
    2, 5, 2, 79, 2, 3, 2, 31, 2, 83, 2, 3, 2, 43, 2, 23,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5,
    2, 179, 2, 3, 2, 59, 2, 7, 2, 3, 2, 131, 2, 159473, 2, 3,
    2, 1399, 2, 5, 2, 3, 2, 191, 2, 13, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 31, 2, 3, 2, 17, 2, 47, 2, 3, 2, 61,
    2, 5, 2, 3, 2, 11, 2, 1187, 2, 3, 2, 5, 2, 4327, 2, 3,
    2, 53, 2, 43, 2, 3, 2, 229, 2, 181, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 137, 2, 73, 2, 3, 2, 5, 2, 7, 2, 3, 2, 113,
    2, 11, 2, 3, 2, 19, 2, 13, 2, 3, 2, 487, 2, 5, 2, 3,
    2, 7993, 2, 401, 2, 3, 2, 5, 2, 23, 2, 3, 2, 211, 2, 41,
    2, 3, 2, 359, 2, 7, 2, 3, 2, 47, 2, 5, 2, 3, 2, 17,
    2, 393611, 2, 3, 2, 5, 2, 15791, 2, 3, 2, 13, 2, 971, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 23, 2, 5, 2, 3, 2, 233, 2, 7,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 443, 2, 3, 2, 977,
    2, 4729, 2, 3, 2, 449, 2, 5, 2, 3, 2, 7, 2, 107, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 19, 2, 7, 2, 3, 2, 103, 2, 31,
    2, 3, 2, 29, 2, 5, 2, 3, 2, 13, 2, 353, 2, 3, 2, 5,
    2, 59, 2, 3, 2, 7, 2, 1711519, 2, 3, 2, 11, 2, 19, 2, 3,
    2, 37, 2, 5, 2, 3, 2, 239, 2, 235483, 2, 3, 2, 5, 2]

/-- Table 9 row: the prime after 8817792098461 is 8817792098461 + 576. -/
theorem gap9_576 : IsGapAt 8817792098461 576 :=
  isGapAt_of 8817792098461 576 (p8817792098461) (by show Nat.Prime 8817792099037; exact p8817792099037) gds_576 (by decide +kernel)

def gds_580 : List ℕ := [
    2, 3, 2, 5, 2, 191, 2, 3, 2, 101, 2, 17, 2, 3, 2, 239,
    2, 89, 2, 3, 2, 7, 2, 5, 2, 3, 2, 337, 2, 157, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 13, 2, 281, 2, 3, 2, 17, 2, 11,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 2903, 2, 23, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 11, 2, 521, 2, 3, 2, 1171, 2, 7, 2, 3,
    2, 29, 2, 5, 2, 3, 2, 2287, 2, 19, 2, 3, 2, 5, 2, 197,
    2, 3, 2, 313, 2, 275059, 2, 3, 2, 7, 2, 17183, 2, 3, 2, 67,
    2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 877, 2, 139, 2, 3, 2, 11, 2, 449, 2, 3, 2, 839, 2, 5,
    2, 3, 2, 7, 2, 71, 2, 3, 2, 5, 2, 2045629, 2, 3, 2, 2207,
    2, 7, 2, 3, 2, 19, 2, 688697, 2, 3, 2, 4943, 2, 5, 2, 3,
    2, 31, 2, 11, 2, 3, 2, 5, 2, 23899, 2, 3, 2, 7, 2, 71317,
    2, 3, 2, 13, 2, 23, 2, 3, 2, 11, 2, 5, 2, 3, 2, 179,
    2, 137, 2, 3, 2, 5, 2, 17, 2, 3, 2, 3833, 2, 13, 2, 3,
    2, 1873, 2, 47, 2, 3, 2, 7, 2, 5, 2, 3, 2, 491581, 2, 31,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 53, 2, 3, 2, 29,
    2, 60133, 2, 3, 2, 443, 2, 5, 2, 3, 2, 11, 2, 57977, 2, 3,
    2, 5, 2, 59, 2, 3, 2, 19, 2, 83, 2, 3, 2, 491, 2, 7,
    2, 3, 2, 71, 2, 5, 2, 3, 2, 43, 2, 13, 2, 3, 2, 5,
    2, 70313, 2, 3, 2, 131, 2, 11, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 47, 2, 5, 2, 3, 2, 911, 2, 7, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 277427, 2, 199, 2, 3, 2, 590363, 2, 37, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 7, 2, 41, 2, 3, 2, 5, 2, 293, 2, 3,
    2, 2544797, 2, 7, 2, 3, 2, 68819, 2, 11, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 61, 2, 861391, 2, 3, 2, 5, 2, 251, 2, 3, 2, 7,
    2, 181, 2, 3, 2, 45979, 2, 79, 2, 3, 2, 468493, 2, 5, 2, 3,
    2, 5347, 2, 17, 2, 3, 2, 5, 2, 31, 2, 3, 2, 13, 2, 19,
    2, 3, 2, 233, 2, 18757, 2, 3, 2, 7, 2, 5, 2, 3, 2, 83,
    2, 103, 2, 3, 2, 5, 2, 7, 2, 3, 2, 660983, 2, 12547, 2, 3,
    2, 11, 2, 1789, 2, 3, 2, 24977, 2, 5, 2, 3, 2, 3637, 2, 120049,
    2, 3, 2, 5, 2, 173, 2, 3, 2, 193, 2, 424757, 2, 3, 2, 37,
    2, 7, 2, 3, 2, 613, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3,
    2, 5, 2, 21401, 2, 3, 2, 23, 2, 17, 2, 3, 2, 7, 2, 50549,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 907, 2, 7, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 31, 2, 89, 2, 3, 2, 17, 2, 515857, 2, 3,
    2, 379, 2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5, 2, 11,
    2, 3, 2]

/-- Table 9 row: the prime after 9383081340541 is 9383081340541 + 580. -/
theorem gap9_580 : IsGapAt 9383081340541 580 :=
  isGapAt_of 9383081340541 580 (p9383081340541) (by show Nat.Prime 9383081341121; exact p9383081341121) gds_580 (by decide +kernel)

def gds_590 : List ℕ := [
    2, 179, 2, 3, 2, 7, 2, 19, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 47, 2, 7, 2, 3, 2, 5, 2, 71, 2, 3, 2, 67, 2, 11,
    2, 3, 2, 101, 2, 13, 2, 3, 2, 25589, 2, 5, 2, 3, 2, 7,
    2, 1553, 2, 3, 2, 5, 2, 31, 2, 3, 2, 191, 2, 7, 2, 3,
    2, 53, 2, 5471, 2, 3, 2, 8017, 2, 5, 2, 3, 2, 1049, 2, 331,
    2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 197, 2, 3, 2, 15581,
    2, 11, 2, 3, 2, 467, 2, 5, 2, 3, 2, 3491, 2, 29, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 11, 2, 19, 2, 3, 2, 1009, 2, 283,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 37, 2, 1013, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 17, 2, 313, 2, 3, 2, 50207, 2, 2785751, 2, 3,
    2, 211, 2, 5, 2, 3, 2, 13, 2, 4657, 2, 3, 2, 5, 2, 10039,
    2, 3, 2, 31, 2, 2447, 2, 3, 2, 11, 2, 7, 2, 3, 2, 83,
    2, 5, 2, 3, 2, 19, 2, 181, 2, 3, 2, 5, 2, 47, 2, 3,
    2, 1198447, 2, 37, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5669, 2, 5,
    2, 3, 2, 2381, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 1291,
    2, 31, 2, 3, 2, 13, 2, 6563, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 7, 2, 647, 2, 3, 2, 5, 2, 1063, 2, 3, 2, 23, 2, 7,
    2, 3, 2, 15959, 2, 53, 2, 3, 2, 6389, 2, 5, 2, 3, 2, 2963,
    2, 709847, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 1444483, 2, 3,
    2, 173, 2, 3067, 2, 3, 2, 19, 2, 5, 2, 3, 2, 11, 2, 17,
    2, 3, 2, 5, 2, 335743, 2, 3, 2, 270577, 2, 967, 2, 3, 2, 73,
    2, 1525703, 2, 3, 2, 7, 2, 5, 2, 3, 2, 59, 2, 13, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 37, 2, 11, 2, 3, 2, 31, 2, 727,
    2, 3, 2, 709, 2, 5, 2, 3, 2, 103, 2, 1109, 2, 3, 2, 5,
    2, 439, 2, 3, 2, 4889, 2, 2267, 2, 3, 2, 127, 2, 7, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 23, 2, 245983, 2, 3, 2, 5, 2, 223,
    2, 3, 2, 769, 2, 17, 2, 3, 2, 7, 2, 11, 2, 3, 2, 67,
    2, 5, 2, 3, 2, 251, 2, 7, 2, 3, 2, 5, 2, 1187, 2, 3,
    2, 11, 2, 71, 2, 3, 2, 17, 2, 29, 2, 3, 2, 79, 2, 5,
    2, 3, 2, 7, 2, 139739, 2, 3, 2, 5, 2, 241, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 197, 2, 47, 2, 3, 2, 3701, 2, 5, 2, 3,
    2, 905453, 2, 23, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 337,
    2, 3, 2, 11, 2, 97, 2, 3, 2, 23801, 2, 5, 2, 3, 2, 43,
    2, 89, 2, 3, 2, 5, 2, 10181, 2, 3, 2, 19, 2, 526831, 2, 3,
    2, 23, 2, 50777, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 11,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 607, 2, 61, 2, 3, 2, 494939,
    2, 19, 2, 3, 2, 11, 2, 5, 2, 3, 2, 1297, 2]

/-- Table 9 row: the prime after 20761252261751 is 20761252261751 + 590. -/
theorem gap9_590 : IsGapAt 20761252261751 590 :=
  isGapAt_of 20761252261751 590 (p20761252261751) (by show Nat.Prime 20761252262341; exact p20761252262341) gds_590 (by decide +kernel)

def gds_608 : List ℕ := [
    2, 7, 2, 3, 2, 5, 2, 6577, 2, 3, 2, 61, 2, 17203, 2, 3,
    2, 163, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 3083,
    2, 3, 2, 5, 2, 15791, 2, 3, 2, 4639, 2, 7, 2, 3, 2, 47,
    2, 167, 2, 3, 2, 454331, 2, 5, 2, 3, 2, 6229, 2, 3817063, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 7, 2, 17, 2, 3, 2, 127, 2, 21023,
    2, 3, 2, 37019, 2, 5, 2, 3, 2, 11, 2, 109, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 631, 2, 29, 2, 3, 2, 17, 2, 76651, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 31, 2, 769, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 43, 2, 11, 2, 3, 2, 709, 2, 137, 2, 3, 2, 211,
    2, 5, 2, 3, 2, 13, 2, 41, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 29, 2, 548687, 2, 3, 2, 1783, 2, 7, 2, 3, 2, 5581, 2, 5,
    2, 3, 2, 49663, 2, 31, 2, 3, 2, 5, 2, 19, 2, 3, 2, 131,
    2, 199, 2, 3, 2, 7, 2, 11, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 5, 2, 43, 2, 3, 2, 11, 2, 379177,
    2, 3, 2, 13, 2, 83, 2, 3, 2, 41, 2, 5, 2, 3, 2, 7,
    2, 1545989, 2, 3, 2, 5, 2, 379, 2, 3, 2, 42379, 2, 7, 2, 3,
    2, 79, 2, 97, 2, 3, 2, 19, 2, 5, 2, 3, 2, 59, 2, 641,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 644009, 2, 3, 2, 11,
    2, 151, 2, 3, 2, 449, 2, 5, 2, 3, 2, 2441, 2, 19, 2, 3,
    2, 5, 2, 157, 2, 3, 2, 17, 2, 8117, 2, 3, 2, 37, 2, 541,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 47, 2, 11, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 23, 2, 163, 2, 3, 2, 103, 2, 145723, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 166949, 2, 263, 2, 3, 2, 5, 2, 31,
    2, 3, 2, 47407, 2, 3990331, 2, 3, 2, 19, 2, 7, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 43, 2, 37, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 492253, 2, 1453, 2, 3, 2, 7, 2, 13, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 239, 2, 3, 2, 16141,
    2, 23, 2, 3, 2, 133813, 2, 113, 2, 3, 2, 314761, 2, 5, 2, 3,
    2, 7, 2, 29, 2, 3, 2, 5, 2, 523, 2, 3, 2, 13, 2, 7,
    2, 3, 2, 223, 2, 215309, 2, 3, 2, 2083, 2, 5, 2, 3, 2, 23,
    2, 17, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 457043, 2, 3,
    2, 181, 2, 61, 2, 3, 2, 2239, 2, 5, 2, 3, 2, 29, 2, 779591,
    2, 3, 2, 5, 2, 47, 2, 3, 2, 271, 2, 397, 2, 3, 2, 109,
    2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13, 2, 10399, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 11, 2, 31, 2, 3, 2, 227, 2, 7229,
    2, 3, 2, 39569, 2, 5, 2, 3, 2, 251, 2, 23, 2, 3, 2, 5,
    2, 373, 2, 3, 2, 1195549, 2, 17, 2, 3, 2, 3929, 2, 7, 2, 3,
    2, 389, 2, 5, 2, 3, 2, 3803, 2, 2243, 2, 3, 2, 5, 2]

/-- Table 9 row: the prime after 20767330530329 is 20767330530329 + 608. -/
theorem gap9_608 : IsGapAt 20767330530329 608 :=
  isGapAt_of 20767330530329 608 (p20767330530329) (by show Nat.Prime 20767330530937; exact p20767330530937) gds_608 (by decide +kernel)

def gds_624 : List ℕ := [
    2, 3, 2, 37, 2, 5, 2, 3, 2, 7, 2, 587, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 13, 2, 7, 2, 3, 2, 17, 2, 67, 2, 3,
    2, 991, 2, 5, 2, 3, 2, 53, 2, 11, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 7, 2, 98221, 2, 3, 2, 271, 2, 23, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 47, 2, 643, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 816317, 2, 6803, 2, 3, 2, 61, 2, 19, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 13, 2, 101, 2, 3, 2, 5, 2, 7, 2, 3, 2, 139,
    2, 41, 2, 3, 2, 7481, 2, 647, 2, 3, 2, 1937723, 2, 5, 2, 3,
    2, 11, 2, 419, 2, 3, 2, 5, 2, 1847, 2, 3, 2, 31, 2, 1489,
    2, 3, 2, 109, 2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2, 32911,
    2, 83, 2, 3, 2, 5, 2, 14717, 2, 3, 2, 540577, 2, 11, 2, 3,
    2, 7, 2, 809, 2, 3, 2, 2039, 2, 5, 2, 3, 2, 709, 2, 7,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 179, 2, 13, 2, 3, 2, 65089,
    2, 61, 2, 3, 2, 421973, 2, 5, 2, 3, 2, 7, 2, 2579, 2, 3,
    2, 5, 2, 641167, 2, 3, 2, 17, 2, 7, 2, 3, 2, 8783, 2, 11,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 2904001, 2, 53, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 7, 2, 43, 2, 3, 2, 71, 2, 29, 2, 3,
    2, 1947923, 2, 5, 2, 3, 2, 19, 2, 13, 2, 3, 2, 5, 2, 73,
    2, 3, 2, 4752949, 2, 8807, 2, 3, 2, 67, 2, 17, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 77719, 2, 181, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 9157, 2, 2152219, 2, 3, 2, 11, 2, 2750983, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 513083, 2, 2767, 2, 3, 2, 5, 2, 277, 2, 3, 2, 47,
    2, 3511, 2, 3, 2, 53, 2, 7, 2, 3, 2, 853, 2, 5, 2, 3,
    2, 479, 2, 11, 2, 3, 2, 5, 2, 4253, 2, 3, 2, 23, 2, 5869,
    2, 3, 2, 7, 2, 31, 2, 3, 2, 11, 2, 5, 2, 3, 2, 3079,
    2, 7, 2, 3, 2, 5, 2, 39233, 2, 3, 2, 13, 2, 123269, 2, 3,
    2, 59, 2, 229, 2, 3, 2, 57251, 2, 5, 2, 3, 2, 7, 2, 19,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 41, 2, 7, 2, 3, 2, 37,
    2, 599, 2, 3, 2, 61, 2, 5, 2, 3, 2, 11, 2, 167, 2, 3,
    2, 5, 2, 131, 2, 3, 2, 7, 2, 23, 2, 3, 2, 313, 2, 835951,
    2, 3, 2, 435419, 2, 5, 2, 3, 2, 13, 2, 303299, 2, 3, 2, 5,
    2, 9133, 2, 3, 2, 29, 2, 11, 2, 3, 2, 19, 2, 36529, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 23, 2, 37, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 4665263, 2, 797, 2, 3, 2, 17, 2, 47, 2, 3, 2, 2281,
    2, 5, 2, 3, 2, 151, 2, 71, 2, 3, 2, 5, 2, 1459, 2, 3,
    2, 457, 2, 324763, 2, 3, 2, 13, 2, 7, 2, 3, 2, 239, 2, 5,
    2, 3, 2, 73, 2, 1373, 2, 3, 2, 5, 2, 56897, 2, 3, 2, 11,
    2, 13, 2, 3, 2, 7, 2, 271, 2, 3, 2, 1030957, 2, 5, 2, 3,
    2, 1223, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 19, 2]

/-- Table 9 row: the prime after 24923033918059 is 24923033918059 + 624. -/
theorem gap9_624 : IsGapAt 24923033918059 624 :=
  isGapAt_of 24923033918059 624 (p24923033918059) (by show Nat.Prime 24923033918683; exact p24923033918683) gds_624 (by decide +kernel)

def gds_626 : List ℕ := [
    2, 8521, 2, 3, 2, 1279, 2, 5, 2, 3, 2, 8329, 2, 809, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 37, 2, 17, 2, 3, 2, 383, 2, 79,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 83, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 552749, 2, 97, 2, 3, 2, 17, 2, 379, 2, 3,
    2, 220873, 2, 5, 2, 3, 2, 19, 2, 13, 2, 3, 2, 5, 2, 3469,
    2, 3, 2, 107, 2, 11, 2, 3, 2, 1952339, 2, 7, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 61, 2, 43, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 67, 2, 75991, 2, 3, 2, 7, 2, 31, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 593, 2, 7, 2, 3, 2, 5, 2, 1039, 2, 3, 2, 1065709,
    2, 41, 2, 3, 2, 71, 2, 11, 2, 3, 2, 167, 2, 5, 2, 3,
    2, 7, 2, 229, 2, 3, 2, 5, 2, 563663, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 317, 2, 9349, 2, 3, 2, 19, 2, 5, 2, 3, 2, 331,
    2, 29, 2, 3, 2, 5, 2, 997, 2, 3, 2, 7, 2, 6037, 2, 3,
    2, 83, 2, 1741, 2, 3, 2, 73, 2, 5, 2, 3, 2, 32173, 2, 19,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 23, 2, 109, 2, 3, 2, 11,
    2, 719, 2, 3, 2, 7, 2, 5, 2, 3, 2, 29, 2, 179, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 17, 2, 1667, 2, 3, 2, 1459, 2, 89,
    2, 3, 2, 43, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5,
    2, 433, 2, 3, 2, 157, 2, 4649, 2, 3, 2, 19, 2, 7, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 100267, 2, 3491, 2, 3, 2, 5, 2, 37,
    2, 3, 2, 223, 2, 23, 2, 3, 2, 7, 2, 17, 2, 3, 2, 139,
    2, 5, 2, 3, 2, 4253, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 1487, 2, 1468109, 2, 3, 2, 13, 2, 43, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 7, 2, 59, 2, 3, 2, 5, 2, 359, 2, 3, 2, 613,
    2, 7, 2, 3, 2, 742537, 2, 41, 2, 3, 2, 199, 2, 5, 2, 3,
    2, 991, 2, 293, 2, 3, 2, 5, 2, 521, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 291899, 2, 101, 2, 3, 2, 29, 2, 5, 2, 3, 2, 31,
    2, 17, 2, 3, 2, 5, 2, 1297, 2, 3, 2, 97, 2, 271, 2, 3,
    2, 89, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 14341, 2, 13,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 41, 2, 857, 2, 3, 2, 47,
    2, 11, 2, 3, 2, 4394911, 2, 5, 2, 3, 2, 59, 2, 31, 2, 3,
    2, 5, 2, 260191, 2, 3, 2, 11, 2, 79, 2, 3, 2, 23, 2, 7,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 159193, 2, 103, 2, 3, 2, 5,
    2, 313, 2, 3, 2, 43, 2, 17, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 21683, 2, 5, 2, 3, 2, 241, 2, 7, 2, 3, 2, 5, 2, 419,
    2, 3, 2, 233, 2, 19, 2, 3, 2, 11, 2, 1621, 2, 3, 2, 71,
    2, 5, 2, 3, 2, 7, 2, 12277, 2, 3, 2, 5, 2, 61, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 29, 2, 23, 2, 3, 2, 2801, 2, 5,
    2, 3, 2, 131, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7,
    2]

/-- Table 9 row: the prime after 33605480400197 is 33605480400197 + 626. -/
theorem gap9_626 : IsGapAt 33605480400197 626 :=
  isGapAt_of 33605480400197 626 (p33605480400197) (by show Nat.Prime 33605480400823; exact p33605480400823) gds_626 (by decide +kernel)

def gds_628 : List ℕ := [
    2, 3, 2, 5, 2, 11, 2, 3, 2, 69833, 2, 5683, 2, 3, 2, 31,
    2, 2963, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 746413, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 11867, 2, 307, 2, 3, 2, 29, 2, 53,
    2, 3, 2, 7057, 2, 5, 2, 3, 2, 21499, 2, 13, 2, 3, 2, 5,
    2, 47591, 2, 3, 2, 37, 2, 11, 2, 3, 2, 269, 2, 7, 2, 3,
    2, 2203, 2, 5, 2, 3, 2, 1740703, 2, 176711, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 223, 2, 11969, 2, 3, 2, 7, 2, 797, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 43, 2, 7, 2, 3, 2, 5, 2, 61, 2, 3,
    2, 17, 2, 79, 2, 3, 2, 646889, 2, 11, 2, 3, 2, 641057, 2, 5,
    2, 3, 2, 7, 2, 19, 2, 3, 2, 5, 2, 3931, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 1553, 2, 419201, 2, 3, 2, 197, 2, 5, 2, 3,
    2, 4429631, 2, 463, 2, 3, 2, 5, 2, 41771, 2, 3, 2, 7, 2, 433,
    2, 3, 2, 1087, 2, 17, 2, 3, 2, 31, 2, 5, 2, 3, 2, 179,
    2, 257, 2, 3, 2, 5, 2, 13, 2, 3, 2, 29, 2, 47, 2, 3,
    2, 11, 2, 67, 2, 3, 2, 7, 2, 5, 2, 3, 2, 83, 2, 3391,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 19841, 2, 521, 2, 3, 2, 157,
    2, 4201, 2, 3, 2, 97, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3,
    2, 5, 2, 89, 2, 3, 2, 64663, 2, 109, 2, 3, 2, 1977749, 2, 7,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 4153, 2, 17, 2, 3, 2, 5,
    2, 2693, 2, 3, 2, 251, 2, 101, 2, 3, 2, 7, 2, 193, 2, 3,
    2, 1229, 2, 5, 2, 3, 2, 2341, 2, 7, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 19, 2, 233, 2, 3, 2, 13, 2, 2459, 2, 3, 2, 107,
    2, 5, 2, 3, 2, 7, 2, 6247, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 61, 2, 7, 2, 3, 2, 43, 2, 19, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 31, 2, 41, 2, 3, 2, 5, 2, 3011627, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 131, 2, 37493, 2, 3, 2, 2399599, 2, 5, 2, 3,
    2, 127321, 2, 160081, 2, 3, 2, 5, 2, 25667, 2, 3, 2, 111827, 2, 2017,
    2, 3, 2, 17, 2, 15259, 2, 3, 2, 7, 2, 5, 2, 3, 2, 79,
    2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 173, 2, 43, 2, 3,
    2, 4051, 2, 11, 2, 3, 2, 41, 2, 5, 2, 3, 2, 248851, 2, 113,
    2, 3, 2, 5, 2, 5089121, 2, 3, 2, 11, 2, 19, 2, 3, 2, 67,
    2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 263, 2, 29, 2, 3,
    2, 5, 2, 427013, 2, 3, 2, 23, 2, 2269, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 202841, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5,
    2, 223, 2, 3, 2, 4583, 2, 137, 2, 3, 2, 11, 2, 863, 2, 3,
    2, 103, 2, 5, 2, 3, 2, 7, 2, 83, 2, 3, 2, 5, 2, 59,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 127, 2, 37, 2, 3, 2, 52361,
    2, 5, 2, 3, 2, 47, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 7, 2, 23, 2, 3, 2, 479, 2, 2061013, 2, 3, 2, 11, 2, 5,
    2, 3, 2]

/-- Table 9 row: the prime after 34140047613391 is 34140047613391 + 628. -/
theorem gap9_628 : IsGapAt 34140047613391 628 :=
  isGapAt_of 34140047613391 628 (p34140047613391) (by show Nat.Prime 34140047614019; exact p34140047614019) gds_628 (by decide +kernel)

def gds_632 : List ℕ := [
    2, 2333, 2, 3, 2, 5, 2, 98323, 2, 3, 2, 5569, 2, 11, 2, 3,
    2, 4111, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 13, 2, 463,
    2, 3, 2, 5, 2, 155423, 2, 3, 2, 197, 2, 53, 2, 3, 2, 7,
    2, 229, 2, 3, 2, 2113, 2, 5, 2, 3, 2, 61, 2, 7, 2, 3,
    2, 5, 2, 10009, 2, 3, 2, 19, 2, 499, 2, 3, 2, 313, 2, 11,
    2, 3, 2, 503, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5,
    2, 37, 2, 3, 2, 11, 2, 7, 2, 3, 2, 13, 2, 19, 2, 3,
    2, 22921, 2, 5, 2, 3, 2, 103, 2, 58453, 2, 3, 2, 5, 2, 89,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 761, 2, 90397, 2, 3, 2, 563,
    2, 5, 2, 3, 2, 53, 2, 4019, 2, 3, 2, 5, 2, 269, 2, 3,
    2, 109, 2, 131, 2, 3, 2, 11, 2, 31, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 41, 2, 43, 2, 3, 2, 5, 2, 7, 2, 3, 2, 63773,
    2, 17, 2, 3, 2, 79, 2, 163, 2, 3, 2, 2609, 2, 5, 2, 3,
    2, 3622253, 2, 11, 2, 3, 2, 5, 2, 103583, 2, 3, 2, 193, 2, 19,
    2, 3, 2, 17, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 23,
    2, 97, 2, 3, 2, 5, 2, 113, 2, 3, 2, 673, 2, 1297537, 2, 3,
    2, 7, 2, 953, 2, 3, 2, 13, 2, 5, 2, 3, 2, 2087, 2, 7,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 97651, 2, 853, 2, 3, 2, 59,
    2, 13, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 1091, 2, 3,
    2, 5, 2, 151, 2, 3, 2, 8017, 2, 7, 2, 3, 2, 487, 2, 37,
    2, 3, 2, 71, 2, 5, 2, 3, 2, 17, 2, 23, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 7, 2, 11, 2, 3, 2, 21011, 2, 773, 2, 3,
    2, 43, 2, 5, 2, 3, 2, 199, 2, 29, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 76873, 2, 1544209, 2, 3, 2, 23, 2, 109, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 108961, 2, 769, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 17393, 2, 3468587, 2, 3, 2, 17749, 2, 11, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 13, 2, 8863, 2, 3, 2, 5, 2, 139, 2, 3, 2, 11,
    2, 49019, 2, 3, 2, 35291, 2, 7, 2, 3, 2, 2437709, 2, 5, 2, 3,
    2, 293, 2, 19, 2, 3, 2, 5, 2, 347, 2, 3, 2, 47, 2, 181,
    2, 3, 2, 7, 2, 23, 2, 3, 2, 113, 2, 5, 2, 3, 2, 31,
    2, 7, 2, 3, 2, 5, 2, 1619, 2, 3, 2, 728647, 2, 3719, 2, 3,
    2, 11, 2, 17, 2, 3, 2, 73, 2, 5, 2, 3, 2, 7, 2, 2999,
    2, 3, 2, 5, 2, 35141, 2, 3, 2, 281, 2, 7, 2, 3, 2, 19,
    2, 227, 2, 3, 2, 17, 2, 5, 2, 3, 2, 137, 2, 11, 2, 3,
    2, 5, 2, 61, 2, 3, 2, 7, 2, 4691, 2, 3, 2, 1399, 2, 331,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 23447, 2, 3617, 2, 3, 2, 5,
    2, 751, 2, 3, 2, 49117, 2, 668867, 2, 3, 2, 101, 2, 41, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 3915683, 2, 13, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 43, 2, 3851, 2, 3, 2, 263, 2, 464257, 2, 3, 2, 2399,
    2, 5, 2, 3, 2, 11, 2]

/-- Table 9 row: the prime after 45678685880759 is 45678685880759 + 632. -/
theorem gap9_632 : IsGapAt 45678685880759 632 :=
  isGapAt_of 45678685880759 632 (p45678685880759) (by show Nat.Prime 45678685881391; exact p45678685881391) gds_632 (by decide +kernel)

def gds_646 : List ℕ := [
    2, 3, 2, 5, 2, 389, 2, 3, 2, 7, 2, 89, 2, 3, 2, 37,
    2, 19, 2, 3, 2, 71, 2, 5, 2, 3, 2, 784457, 2, 73, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 21701, 2, 41, 2, 3, 2, 59, 2, 29,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 599, 2, 61, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 17, 2, 541, 2, 3, 2, 11, 2, 79, 2, 3,
    2, 281, 2, 5, 2, 3, 2, 263, 2, 37, 2, 3, 2, 5, 2, 43,
    2, 3, 2, 2533577, 2, 13, 2, 3, 2, 29, 2, 7, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 1307, 2, 11, 2, 3, 2, 5, 2, 31, 2, 3,
    2, 307, 2, 19, 2, 3, 2, 7, 2, 17, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 698183, 2, 7, 2, 3, 2, 5, 2, 211, 2, 3, 2, 103,
    2, 6007, 2, 3, 2, 958259, 2, 27481, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 89, 2, 7,
    2, 3, 2, 467, 2, 18503, 2, 3, 2, 383, 2, 5, 2, 3, 2, 11,
    2, 367, 2, 3, 2, 5, 2, 743, 2, 3, 2, 7, 2, 29, 2, 3,
    2, 4655471, 2, 97, 2, 3, 2, 13, 2, 5, 2, 3, 2, 37, 2, 17,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 23, 2, 11, 2, 3, 2, 1954273,
    2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 43, 2, 83, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 29, 2, 59, 2, 3, 2, 2053, 2, 41,
    2, 3, 2, 461, 2, 5, 2, 3, 2, 1265573, 2, 131, 2, 3, 2, 5,
    2, 71, 2, 3, 2, 13, 2, 31, 2, 3, 2, 1129, 2, 7, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 157, 2, 101, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 11, 2, 17, 2, 3, 2, 7, 2, 166781, 2, 3, 2, 137,
    2, 5, 2, 3, 2, 5515333, 2, 7, 2, 3, 2, 5, 2, 103, 2, 3,
    2, 41, 2, 6899, 2, 3, 2, 17, 2, 5119, 2, 3, 2, 1051, 2, 5,
    2, 3, 2, 7, 2, 19469, 2, 3, 2, 5, 2, 29, 2, 3, 2, 59,
    2, 7, 2, 3, 2, 11, 2, 1481, 2, 3, 2, 1907, 2, 5, 2, 3,
    2, 113131, 2, 47, 2, 3, 2, 5, 2, 61, 2, 3, 2, 7, 2, 73823,
    2, 3, 2, 19, 2, 133439, 2, 3, 2, 2549, 2, 5, 2, 3, 2, 71,
    2, 11, 2, 3, 2, 5, 2, 53, 2, 3, 2, 37, 2, 7753, 2, 3,
    2, 13, 2, 73, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 23,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 163307, 2, 13, 2, 3, 2, 74797,
    2, 31, 2, 3, 2, 1707977, 2, 5, 2, 3, 2, 8831, 2, 67, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 311, 2, 209579, 2, 3, 2, 23, 2, 7,
    2, 3, 2, 101, 2, 5, 2, 3, 2, 11, 2, 100003, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 19, 2, 79, 2, 3, 2, 7, 2, 227, 2, 3,
    2, 53, 2, 5, 2, 3, 2, 2977523, 2, 7, 2, 3, 2, 5, 2, 1789,
    2, 3, 2, 17, 2, 11, 2, 3, 2, 117911, 2, 19, 2, 3, 2, 1447,
    2, 5, 2, 3, 2, 7, 2, 13649, 2, 3, 2, 5, 2, 269, 2, 3,
    2, 8933, 2, 7, 2, 3, 2, 41, 2, 23, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 29, 2, 1847, 2, 3, 2, 5, 2, 59, 2, 3, 2, 7,
    2, 113, 2, 3, 2]

/-- Table 9 row: the prime after 51027160468351 is 51027160468351 + 646. -/
theorem gap9_646 : IsGapAt 51027160468351 646 :=
  isGapAt_of 51027160468351 646 (p51027160468351) (by show Nat.Prime 51027160468997; exact p51027160468997) gds_646 (by decide +kernel)

def gds_654 : List ℕ := [
    2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 23, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 73, 2, 11, 2, 3, 2, 3919, 2, 383,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 113, 2, 13, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 29, 2, 248783, 2, 3, 2, 23, 2, 7, 2, 3,
    2, 31, 2, 5, 2, 3, 2, 421, 2, 61, 2, 3, 2, 5, 2, 494873,
    2, 3, 2, 79, 2, 67, 2, 3, 2, 7, 2, 11, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 149, 2, 7, 2, 3, 2, 5, 2, 101, 2, 3,
    2, 11, 2, 451337, 2, 3, 2, 74453, 2, 13, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 7, 2, 47, 2, 3, 2, 5, 2, 389, 2, 3, 2, 1860821,
    2, 7, 2, 3, 2, 137, 2, 23, 2, 3, 2, 107, 2, 5, 2, 3,
    2, 229, 2, 19, 2, 3, 2, 5, 2, 29, 2, 3, 2, 7, 2, 33581,
    2, 3, 2, 11, 2, 2473, 2, 3, 2, 41, 2, 5, 2, 3, 2, 191,
    2, 43, 2, 3, 2, 5, 2, 13, 2, 3, 2, 2143, 2, 17, 2, 3,
    2, 19259, 2, 37, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23761, 2, 11,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 751, 2, 7121, 2, 3, 2, 17,
    2, 79, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 36061, 2, 3,
    2, 5, 2, 409, 2, 3, 2, 353, 2, 211, 2, 3, 2, 863, 2, 7,
    2, 3, 2, 12227, 2, 5, 2, 3, 2, 2029, 2, 89227, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 6421, 2, 1123, 2, 3, 2, 7, 2, 6637727, 2, 3,
    2, 223, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 697261,
    2, 3, 2, 8039, 2, 977, 2, 3, 2, 13, 2, 576509, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 41, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 37, 2, 3830317, 2, 3, 2, 43, 2, 5,
    2, 3, 2, 487, 2, 1279, 2, 3, 2, 5, 2, 2617, 2, 3, 2, 7,
    2, 103, 2, 3, 2, 6599, 2, 19, 2, 3, 2, 4129, 2, 5, 2, 3,
    2, 29, 2, 22709, 2, 3, 2, 5, 2, 17, 2, 3, 2, 257, 2, 47,
    2, 3, 2, 1117, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 41,
    2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 24517, 2, 3,
    2, 239, 2, 43, 2, 3, 2, 277, 2, 5, 2, 3, 2, 73, 2, 173,
    2, 3, 2, 5, 2, 2602939, 2, 3, 2, 23, 2, 271, 2, 3, 2, 898181,
    2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 181, 2, 113, 2, 3,
    2, 5, 2, 31, 2, 3, 2, 83, 2, 19, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 433, 2, 5, 2, 3, 2, 4021, 2, 7, 2, 3, 2, 5,
    2, 167, 2, 3, 2, 59, 2, 5507, 2, 3, 2, 139, 2, 97, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 823,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 5323, 2, 179, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 19, 2, 107, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 7, 2, 41, 2, 3, 2, 2585549, 2, 392827, 2, 3, 2, 251, 2, 5,
    2, 3, 2, 23, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3, 2, 31,
    2, 719063, 2, 3, 2, 19841, 2, 430267, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 11, 2, 163, 2, 3, 2, 5, 2, 7, 2, 3, 2]

/-- Table 9 row: the prime after 54916086007427 is 54916086007427 + 654. -/
theorem gap9_654 : IsGapAt 54916086007427 654 :=
  isGapAt_of 54916086007427 654 (p54916086007427) (by show Nat.Prime 54916086008081; exact p54916086008081) gds_654 (by decide +kernel)

def gds_656 : List ℕ := [
    2, 7309079, 2, 3, 2, 7, 2, 3361, 2, 3, 2, 131, 2, 5, 2, 3,
    2, 37, 2, 7, 2, 3, 2, 5, 2, 101, 2, 3, 2, 29, 2, 23,
    2, 3, 2, 19, 2, 17, 2, 3, 2, 401, 2, 5, 2, 3, 2, 7,
    2, 11, 2, 3, 2, 5, 2, 195427, 2, 3, 2, 8461, 2, 7, 2, 3,
    2, 43, 2, 821, 2, 3, 2, 11, 2, 5, 2, 3, 2, 23, 2, 368243,
    2, 3, 2, 5, 2, 137, 2, 3, 2, 7, 2, 37, 2, 3, 2, 206603,
    2, 151, 2, 3, 2, 13, 2, 5, 2, 3, 2, 1659187, 2, 281, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 127, 2, 41, 2, 3, 2, 7759, 2, 13,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 19, 2, 43, 2, 3, 2, 73, 2, 521, 2, 3,
    2, 71, 2, 5, 2, 3, 2, 429881, 2, 23, 2, 3, 2, 5, 2, 191,
    2, 3, 2, 13, 2, 11, 2, 3, 2, 435541, 2, 7, 2, 3, 2, 21433,
    2, 5, 2, 3, 2, 283, 2, 78163, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 67, 2, 522541, 2, 3, 2, 7, 2, 47, 2, 3, 2, 503, 2, 5,
    2, 3, 2, 101, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 37,
    2, 17, 2, 3, 2, 2081, 2, 11, 2, 3, 2, 4481, 2, 5, 2, 3,
    2, 7, 2, 6971, 2, 3, 2, 5, 2, 43151, 2, 3, 2, 11, 2, 7,
    2, 3, 2, 17, 2, 277, 2, 3, 2, 175067, 2, 5, 2, 3, 2, 53,
    2, 263, 2, 3, 2, 5, 2, 2111, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 643, 2, 23, 2, 3, 2, 47, 2, 5, 2, 3, 2, 307, 2, 29,
    2, 3, 2, 5, 2, 977021, 2, 3, 2, 94819, 2, 349, 2, 3, 2, 11,
    2, 149, 2, 3, 2, 7, 2, 5, 2, 3, 2, 223999, 2, 107, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 31, 2, 13, 2, 3, 2, 86767, 2, 41,
    2, 3, 2, 499, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5,
    2, 1831, 2, 3, 2, 292081, 2, 383, 2, 3, 2, 61, 2, 7, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 199, 2, 43, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 13063, 2, 31, 2, 3, 2, 7, 2, 2713, 2, 3, 2, 6659,
    2, 5, 2, 3, 2, 2897369, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 41, 2, 6143, 2, 3, 2, 18049, 2, 79, 2, 3, 2, 37, 2, 5,
    2, 3, 2, 7, 2, 89, 2, 3, 2, 5, 2, 577, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 94837, 2, 129539, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 313, 2, 47, 2, 3, 2, 5, 2, 373, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 146677, 2, 13, 2, 3, 2, 2089, 2, 5, 2, 3, 2, 5215913,
    2, 19, 2, 3, 2, 5, 2, 37, 2, 3, 2, 1871017, 2, 109, 2, 3,
    2, 31, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 191, 2, 112621,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 2153, 2, 3, 2, 1481,
    2, 11, 2, 3, 2, 17, 2, 5, 2, 3, 2, 71, 2, 6839923, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 11, 2, 5657, 2, 3, 2, 19, 2, 7,
    2, 3, 2, 59, 2, 5, 2, 3, 2, 331, 2, 97, 2, 3, 2, 5,
    2, 6791, 2, 3, 2, 23, 2, 101, 2, 3, 2, 7, 2, 6684677, 2, 3,
    2, 919, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2]

/-- Table 9 row: the prime after 65862966031241 is 65862966031241 + 656. -/
theorem gap9_656 : IsGapAt 65862966031241 656 :=
  isGapAt_of 65862966031241 656 (p65862966031241) (by show Nat.Prime 65862966031897; exact p65862966031897) gds_656 (by decide +kernel)

def gds_676 : List ℕ := [
    2, 3, 2, 5, 2, 173, 2, 3, 2, 1303, 2, 274829, 2, 3, 2, 997,
    2, 103, 2, 3, 2, 7, 2, 5, 2, 3, 2, 713873, 2, 560887, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 1153, 2, 23, 2, 3, 2, 315811, 2, 11,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 15259, 2, 13, 2, 3, 2, 5,
    2, 83, 2, 3, 2, 11, 2, 359, 2, 3, 2, 41, 2, 7, 2, 3,
    2, 281, 2, 5, 2, 3, 2, 23, 2, 19, 2, 3, 2, 5, 2, 89,
    2, 3, 2, 2672203, 2, 167, 2, 3, 2, 7, 2, 733, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 197, 2, 7, 2, 3, 2, 5, 2, 461, 2, 3,
    2, 5101631, 2, 31, 2, 3, 2, 11, 2, 13, 2, 3, 2, 47, 2, 5,
    2, 3, 2, 7, 2, 65497, 2, 3, 2, 5, 2, 30637, 2, 3, 2, 113,
    2, 7, 2, 3, 2, 19, 2, 2801, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 29, 2, 11, 2, 3, 2, 5, 2, 1782511, 2, 3, 2, 7, 2, 181,
    2, 3, 2, 73, 2, 127, 2, 3, 2, 11, 2, 5, 2, 3, 2, 21013,
    2, 307, 2, 3, 2, 5, 2, 13, 2, 3, 2, 61, 2, 67, 2, 3,
    2, 23, 2, 743, 2, 3, 2, 7, 2, 5, 2, 3, 2, 877, 2, 17,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 1576093, 2, 401, 2, 3, 2, 31,
    2, 568541, 2, 3, 2, 71, 2, 5, 2, 3, 2, 11, 2, 211, 2, 3,
    2, 5, 2, 439, 2, 3, 2, 19, 2, 53, 2, 3, 2, 37, 2, 7,
    2, 3, 2, 149, 2, 5, 2, 3, 2, 811, 2, 107, 2, 3, 2, 5,
    2, 906817, 2, 3, 2, 1103, 2, 11, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 41, 2, 5, 2, 3, 2, 63743, 2, 7, 2, 3, 2, 5, 2, 491,
    2, 3, 2, 619, 2, 17, 2, 3, 2, 13, 2, 131, 2, 3, 2, 29,
    2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5, 2, 16223, 2, 3,
    2, 1892383, 2, 7, 2, 3, 2, 17, 2, 11, 2, 3, 2, 413533, 2, 5,
    2, 3, 2, 53, 2, 2633, 2, 3, 2, 5, 2, 3023, 2, 3, 2, 7,
    2, 458971, 2, 3, 2, 15643, 2, 659, 2, 3, 2, 1637, 2, 5, 2, 3,
    2, 1973, 2, 43, 2, 3, 2, 5, 2, 5623, 2, 3, 2, 103, 2, 19,
    2, 3, 2, 167, 2, 59, 2, 3, 2, 7, 2, 5, 2, 3, 2, 239,
    2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 1933, 2, 1381, 2, 3,
    2, 11, 2, 29, 2, 3, 2, 337, 2, 5, 2, 3, 2, 17, 2, 661,
    2, 3, 2, 5, 2, 41, 2, 3, 2, 67, 2, 8222623, 2, 3, 2, 647893,
    2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2, 11, 2, 3,
    2, 5, 2, 521, 2, 3, 2, 191, 2, 80153, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 25913, 2, 7, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 79, 2, 1192181, 2, 3, 2, 59, 2, 1607, 2, 3,
    2, 1667609, 2, 5, 2, 3, 2, 7, 2, 13463, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 61, 2, 2851, 2, 3, 2, 43,
    2, 5, 2, 3, 2, 11, 2, 53, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 7, 2, 47, 2, 3, 2, 317, 2, 259121, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 31, 2, 89, 2, 3, 2, 5, 2, 103, 2, 3, 2, 23,
    2, 11, 2, 3, 2, 4951, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 13, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 5507233, 2, 163,
    2, 3, 2]

/-- Table 9 row: the prime after 78610833115261 is 78610833115261 + 676. -/
theorem gap9_676 : IsGapAt 78610833115261 676 :=
  isGapAt_of 78610833115261 676 (p78610833115261) (by show Nat.Prime 78610833115937; exact p78610833115937) gds_676 (by decide +kernel)

def gds_680 : List ℕ := [
    2, 13, 2, 3, 2, 5, 2, 53, 2, 3, 2, 31, 2, 11, 2, 3,
    2, 10831, 2, 243671, 2, 3, 2, 7, 2, 5, 2, 3, 2, 419, 2, 17,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 8779549, 2, 23, 2, 3, 2, 1097,
    2, 2777, 2, 3, 2, 13, 2, 5, 2, 3, 2, 227, 2, 181, 2, 3,
    2, 5, 2, 10331, 2, 3, 2, 5927, 2, 19, 2, 3, 2, 4007, 2, 7,
    2, 3, 2, 17483, 2, 5, 2, 3, 2, 23, 2, 65179, 2, 3, 2, 5,
    2, 41, 2, 3, 2, 11, 2, 29, 2, 3, 2, 7, 2, 32089, 2, 3,
    2, 53, 2, 5, 2, 3, 2, 307, 2, 7, 2, 3, 2, 5, 2, 37,
    2, 3, 2, 13, 2, 17, 2, 3, 2, 521, 2, 1632919, 2, 3, 2, 43,
    2, 5, 2, 3, 2, 7, 2, 47, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 29, 2, 7, 2, 3, 2, 11, 2, 127, 2, 3, 2, 4949521, 2, 5,
    2, 3, 2, 41, 2, 23, 2, 3, 2, 5, 2, 19, 2, 3, 2, 7,
    2, 71, 2, 3, 2, 31, 2, 65393, 2, 3, 2, 97, 2, 5, 2, 3,
    2, 13, 2, 11, 2, 3, 2, 5, 2, 157, 2, 3, 2, 131, 2, 619,
    2, 3, 2, 23, 2, 43, 2, 3, 2, 7, 2, 5, 2, 3, 2, 59,
    2, 193, 2, 3, 2, 5, 2, 7, 2, 3, 2, 792049, 2, 139, 2, 3,
    2, 457, 2, 31, 2, 3, 2, 19, 2, 5, 2, 3, 2, 17, 2, 20051,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 1371551, 2, 129419, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 1279, 2, 5, 2, 3, 2, 11, 2, 19, 2, 3,
    2, 5, 2, 173, 2, 3, 2, 443, 2, 13, 2, 3, 2, 7, 2, 23,
    2, 3, 2, 281, 2, 5, 2, 3, 2, 83, 2, 7, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 797917, 2, 11, 2, 3, 2, 433, 2, 37, 2, 3,
    2, 50341, 2, 5, 2, 3, 2, 7, 2, 5308553, 2, 3, 2, 5, 2, 316583,
    2, 3, 2, 17, 2, 7, 2, 3, 2, 19, 2, 217739, 2, 3, 2, 31,
    2, 5, 2, 3, 2, 19237, 2, 13, 2, 3, 2, 5, 2, 97, 2, 3,
    2, 7, 2, 167, 2, 3, 2, 1291, 2, 11, 2, 3, 2, 4211, 2, 5,
    2, 3, 2, 953, 2, 89, 2, 3, 2, 5, 2, 317, 2, 3, 2, 11,
    2, 47, 2, 3, 2, 283, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 109, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 1171, 2, 270833,
    2, 3, 2, 191, 2, 13, 2, 3, 2, 17, 2, 5, 2, 3, 2, 1769293,
    2, 84697, 2, 3, 2, 5, 2, 43, 2, 3, 2, 19, 2, 6605561, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 29, 2, 151,
    2, 3, 2, 5, 2, 163, 2, 3, 2, 13, 2, 379, 2, 3, 2, 7,
    2, 19, 2, 3, 2, 67, 2, 5, 2, 3, 2, 73, 2, 7, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 3271, 2, 467, 2, 3, 2, 397, 2, 137,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5,
    2, 61, 2, 3, 2, 1258207, 2, 7, 2, 3, 2, 743, 2, 41, 2, 3,
    2, 59, 2, 5, 2, 3, 2, 13, 2, 1709, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 6263, 2, 3, 2, 1277, 2, 71, 2, 3, 2, 107,
    2, 5, 2, 3, 2, 11, 2, 31, 2, 3, 2, 5, 2, 5711, 2, 3,
    2, 23, 2, 17, 2, 3, 2, 613, 2, 1336271, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 43, 2, 83, 2, 3, 2, 5, 2, 7, 2, 3, 2, 41,
    2, 11, 2, 3, 2, 13, 2]

/-- Table 9 row: the prime after 82385435331119 is 82385435331119 + 680. -/
theorem gap9_680 : IsGapAt 82385435331119 680 :=
  isGapAt_of 82385435331119 680 (p82385435331119) (by show Nat.Prime 82385435331799; exact p82385435331799) gds_680 (by decide +kernel)

def gds_688 : List ℕ := [
    2, 3, 2, 31, 2, 5, 2, 3, 2, 829, 2, 7, 2, 3, 2, 5,
    2, 1638947, 2, 3, 2, 103, 2, 47, 2, 3, 2, 23, 2, 193, 2, 3,
    2, 509, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 127, 2, 7, 2, 3, 2, 13, 2, 109, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 10457, 2, 32609, 2, 3, 2, 5, 2, 131, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 229, 2, 709, 2, 3, 2, 41, 2, 5,
    2, 3, 2, 80207, 2, 32831, 2, 3, 2, 5, 2, 11, 2, 3, 2, 339839,
    2, 3257, 2, 3, 2, 47, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 11, 2, 296557, 2, 3, 2, 5, 2, 7, 2, 3, 2, 457687, 2, 43,
    2, 3, 2, 12301, 2, 17, 2, 3, 2, 37, 2, 5, 2, 3, 2, 1567477,
    2, 13, 2, 3, 2, 5, 2, 147703, 2, 3, 2, 116491, 2, 11, 2, 3,
    2, 141461, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 31, 2, 3929,
    2, 3, 2, 5, 2, 353, 2, 3, 2, 83, 2, 71, 2, 3, 2, 7,
    2, 73, 2, 3, 2, 13, 2, 5, 2, 3, 2, 8269, 2, 7, 2, 3,
    2, 5, 2, 37, 2, 3, 2, 89, 2, 19, 2, 3, 2, 61, 2, 11,
    2, 3, 2, 1567, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 11, 2, 7, 2, 3, 2, 257, 2, 6052103, 2, 3,
    2, 277, 2, 5, 2, 3, 2, 125339, 2, 1291, 2, 3, 2, 5, 2, 220543,
    2, 3, 2, 7, 2, 22147, 2, 3, 2, 29, 2, 151, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 19, 2, 59, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 41233, 2, 149, 2, 3, 2, 11, 2, 177553, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 41, 2, 1499, 2, 3, 2, 5, 2, 7, 2, 3, 2, 1051,
    2, 17, 2, 3, 2, 211, 2, 61, 2, 3, 2, 1367, 2, 5, 2, 3,
    2, 13, 2, 11, 2, 3, 2, 5, 2, 137, 2, 3, 2, 53, 2, 101,
    2, 3, 2, 17, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 47,
    2, 43, 2, 3, 2, 5, 2, 1091, 2, 3, 2, 28669, 2, 29, 2, 3,
    2, 7, 2, 1493, 2, 3, 2, 19, 2, 5, 2, 3, 2, 59, 2, 7,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 23, 2, 97, 2, 3, 2, 13,
    2, 37, 2, 3, 2, 866081, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 5, 2, 2297, 2, 3, 2, 29, 2, 7, 2, 3, 2, 145133, 2, 113,
    2, 3, 2, 6659, 2, 5, 2, 3, 2, 17, 2, 373, 2, 3, 2, 5,
    2, 991409, 2, 3, 2, 7, 2, 11, 2, 3, 2, 24659, 2, 431, 2, 3,
    2, 3919, 2, 5, 2, 3, 2, 107, 2, 197, 2, 3, 2, 5, 2, 2365459,
    2, 3, 2, 2843, 2, 23, 2, 3, 2, 19, 2, 79, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 8803, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 31, 2, 60029, 2, 3, 2, 92353, 2, 11, 2, 3, 2, 43, 2, 5,
    2, 3, 2, 23, 2, 2017, 2, 3, 2, 5, 2, 29, 2, 3, 2, 11,
    2, 53, 2, 3, 2, 37, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 691, 2, 263, 2, 3, 2, 5, 2, 337, 2, 3, 2, 149, 2, 31,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 683, 2, 5, 2, 3, 2, 103,
    2, 7, 2, 3, 2, 5, 2, 73, 2, 3, 2, 19, 2, 4241, 2, 3,
    2, 11, 2, 17, 2, 3, 2, 1381, 2, 5, 2, 3, 2, 7, 2, 23,
    2, 3, 2, 5, 2, 5309, 2, 3, 2, 13, 2, 7, 2, 3, 2]

/-- Table 9 row: the prime after 110526670235599 is 110526670235599 + 688. -/
theorem gap9_688 : IsGapAt 110526670235599 688 :=
  isGapAt_of 110526670235599 688 (p110526670235599) (by show Nat.Prime 110526670236287; exact p110526670236287) gds_688 (by decide +kernel)

def gds_708 : List ℕ := [
    2, 3, 2, 5, 2, 287341, 2, 3, 2, 769, 2, 11, 2, 3, 2, 71,
    2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 19, 2, 37, 2, 3,
    2, 5, 2, 47, 2, 3, 2, 13, 2, 29, 2, 3, 2, 7, 2, 41,
    2, 3, 2, 233, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 23, 2, 59, 2, 3, 2, 3463, 2, 11, 2, 3,
    2, 10987, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 81527,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 353, 2, 4027493, 2, 3, 2, 1667,
    2, 5, 2, 3, 2, 13, 2, 31, 2, 3, 2, 5, 2, 401, 2, 3,
    2, 7, 2, 39719, 2, 3, 2, 229, 2, 4078073, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 43, 2, 149, 2, 3, 2, 5, 2, 89, 2, 3, 2, 2967803,
    2, 23, 2, 3, 2, 11, 2, 53, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 37, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 59, 2, 17,
    2, 3, 2, 13, 2, 1871, 2, 3, 2, 509147, 2, 5, 2, 3, 2, 23,
    2, 11, 2, 3, 2, 5, 2, 29, 2, 3, 2, 14759, 2, 13, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 373, 2, 191,
    2, 3, 2, 5, 2, 83, 2, 3, 2, 647909, 2, 37, 2, 3, 2, 7,
    2, 281, 2, 3, 2, 3727, 2, 5, 2, 3, 2, 941, 2, 7, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 11677, 2, 4359233, 2, 3, 2, 557, 2, 4952023,
    2, 3, 2, 97, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 2087, 2, 7, 2, 3, 2, 337, 2, 47, 2, 3,
    2, 6271, 2, 5, 2, 3, 2, 17, 2, 1319, 2, 3, 2, 5, 2, 283211,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 23, 2, 2861, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 5683, 2, 317, 2, 3, 2, 5, 2, 34591, 2, 3,
    2, 19, 2, 227, 2, 3, 2, 41, 2, 13, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 659, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 37,
    2, 919, 2, 3, 2, 43, 2, 11, 2, 3, 2, 47, 2, 5, 2, 3,
    2, 101, 2, 95413, 2, 3, 2, 5, 2, 59, 2, 3, 2, 11, 2, 157,
    2, 3, 2, 73, 2, 7, 2, 3, 2, 71, 2, 5, 2, 3, 2, 29,
    2, 1753, 2, 3, 2, 5, 2, 13, 2, 3, 2, 193, 2, 1051, 2, 3,
    2, 7, 2, 1493, 2, 3, 2, 160841, 2, 5, 2, 3, 2, 12043, 2, 7,
    2, 3, 2, 5, 2, 53, 2, 3, 2, 79, 2, 31, 2, 3, 2, 11,
    2, 17, 2, 3, 2, 4271, 2, 5, 2, 3, 2, 7, 2, 2731, 2, 3,
    2, 5, 2, 3373, 2, 3, 2, 953, 2, 7, 2, 3, 2, 499, 2, 773,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 109, 2, 11, 2, 3, 2, 5,
    2, 2459, 2, 3, 2, 7, 2, 1907, 2, 3, 2, 689921, 2, 21067, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 67, 2, 937, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 9318461, 2, 73, 2, 3, 2, 13, 2, 10667, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 19, 2, 17, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 199, 2, 13, 2, 3, 2, 31, 2, 727, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 11, 2, 61, 2, 3, 2, 5, 2, 19, 2, 3, 2, 827,
    2, 847549, 2, 3, 2, 797, 2, 7, 2, 3, 2, 421, 2, 5, 2, 3,
    2, 19379, 2, 127, 2, 3, 2, 5, 2, 379, 2, 3, 2, 487, 2, 11,
    2, 3, 2, 7, 2, 31, 2, 3, 2, 20047, 2, 5, 2, 3, 2, 103,
    2, 7, 2, 3, 2, 5, 2, 37, 2, 3, 2, 313, 2, 17, 2, 3,
    2, 853, 2]

/-- Table 9 row: the prime after 143679495784681 is 143679495784681 + 708. -/
theorem gap9_708 : IsGapAt 143679495784681 708 :=
  isGapAt_of 143679495784681 708 (p143679495784681) (by show Nat.Prime 143679495785389; exact p143679495785389) gds_708 (by decide +kernel)

def gds_722 : List ℕ := [
    2, 19, 2, 3, 2, 71, 2, 5, 2, 3, 2, 6545027, 2, 389, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 7, 2, 43, 2, 3, 2, 23, 2, 533149,
    2, 3, 2, 109, 2, 5, 2, 3, 2, 11, 2, 8619053, 2, 3, 2, 5,
    2, 37061, 2, 3, 2, 199, 2, 1549, 2, 3, 2, 3187, 2, 17, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 47, 2, 727, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 373, 2, 11, 2, 3, 2, 31, 2, 283, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 12473, 2, 55441, 2, 3, 2, 5, 2, 59, 2, 3,
    2, 277, 2, 19, 2, 3, 2, 13, 2, 7, 2, 3, 2, 151, 2, 5,
    2, 3, 2, 307, 2, 163, 2, 3, 2, 5, 2, 359, 2, 3, 2, 526387,
    2, 13, 2, 3, 2, 7, 2, 11, 2, 3, 2, 211, 2, 5, 2, 3,
    2, 7096477, 2, 7, 2, 3, 2, 5, 2, 4349, 2, 3, 2, 11, 2, 83,
    2, 3, 2, 13711, 2, 29, 2, 3, 2, 37, 2, 5, 2, 3, 2, 7,
    2, 207923, 2, 3, 2, 5, 2, 9011, 2, 3, 2, 41, 2, 7, 2, 3,
    2, 49477, 2, 113, 2, 3, 2, 97, 2, 5, 2, 3, 2, 103, 2, 13,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 853, 2, 3, 2, 11,
    2, 1901, 2, 3, 2, 193, 2, 5, 2, 3, 2, 337, 2, 109, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 61, 2, 17, 2, 3, 2, 73, 2, 521,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 1087, 2, 11, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 24481, 2, 223, 2, 3, 2, 17, 2, 13, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 307583, 2, 269, 2, 3, 2, 5, 2, 53,
    2, 3, 2, 439, 2, 647, 2, 3, 2, 157, 2, 7, 2, 3, 2, 137,
    2, 5, 2, 3, 2, 83, 2, 19, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 13, 2, 29, 2, 3, 2, 7, 2, 367, 2, 3, 2, 571, 2, 5,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 5507,
    2, 61, 2, 3, 2, 811, 2, 229, 2, 3, 2, 172969, 2, 5, 2, 3,
    2, 7, 2, 2609, 2, 3, 2, 5, 2, 97, 2, 3, 2, 29, 2, 7,
    2, 3, 2, 19, 2, 15683, 2, 3, 2, 53, 2, 5, 2, 3, 2, 13,
    2, 317, 2, 3, 2, 5, 2, 163199, 2, 3, 2, 7, 2, 2521, 2, 3,
    2, 41, 2, 199, 2, 3, 2, 43, 2, 5, 2, 3, 2, 31, 2, 59,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 97007, 2, 101, 2, 3, 2, 823,
    2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 107, 2, 25579, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 11, 2, 593, 2, 3, 2, 13, 2, 2791,
    2, 3, 2, 2393, 2, 5, 2, 3, 2, 139, 2, 31, 2, 3, 2, 5,
    2, 29, 2, 3, 2, 19, 2, 13, 2, 3, 2, 56957, 2, 7, 2, 3,
    2, 733, 2, 5, 2, 3, 2, 89, 2, 36017, 2, 3, 2, 5, 2, 1913,
    2, 3, 2, 4148581, 2, 67, 2, 3, 2, 7, 2, 17, 2, 3, 2, 632911,
    2, 5, 2, 3, 2, 23, 2, 7, 2, 3, 2, 5, 2, 131, 2, 3,
    2, 599, 2, 13831, 2, 3, 2, 6131, 2, 18587, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 6823, 2, 3, 2, 3433,
    2, 7, 2, 3, 2, 37, 2, 193, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 9413849, 2, 157, 2, 3, 2, 5, 2, 541, 2, 3, 2, 7, 2, 6359,
    2, 3, 2, 1635863, 2, 79, 2, 3, 2, 13, 2, 5, 2, 3, 2, 12093869,
    2, 17, 2, 3, 2, 5, 2, 11, 2, 3, 2, 10837, 2, 19, 2, 3,
    2, 109, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 29,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 43, 2, 71, 2, 3, 2, 23,
    2]

/-- Table 9 row: the prime after 218356872845927 is 218356872845927 + 722. -/
theorem gap9_722 : IsGapAt 218356872845927 722 :=
  isGapAt_of 218356872845927 722 (p218356872845927) (by show Nat.Prime 218356872846649; exact p218356872846649) gds_722 (by decide +kernel)

end LeanLab.OeSHP2014
