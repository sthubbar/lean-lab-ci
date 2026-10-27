/-
Maximal prime gap records, OEIS A002386 part 3: each row `IsGapAt p g`, zero sorry.
Divisors and Pratt certificates found by Python, checked by the Lean kernel.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.GapsBase

namespace LeanLab.Verifications.Top50.Gaps3

open LeanLab.Verifications.Top50.Gaps
open LeanLab.Verifications.Pratt (pB)

theorem p55580592317 : Nat.Prime 55580592317 := by
  refine Pratt.pratt 55580592317 2 [(2, 2), (23, 1), (107, 1), (1487, 1), (3797, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p218209405436543 : Nat.Prime 218209405436543 := by
  refine Pratt.pratt 218209405436543 5 [(2, 1), (13, 1), (151, 1), (55580592317, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p55580592317

theorem p180636925031 : Nat.Prime 180636925031 := by
  refine Pratt.pratt 180636925031 17 [(2, 1), (5, 1), (1723, 1), (2819, 1), (3719, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p218209405437449 : Nat.Prime 218209405437449 := by
  refine Pratt.pratt 218209405437449 3 [(2, 3), (151, 1), (180636925031, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p180636925031

theorem p69727951 : Nat.Prime 69727951 := by
  refine Pratt.pratt 69727951 3 [(2, 1), (3, 2), (5, 2), (23, 1), (6737, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p1189459969825483 : Nat.Prime 1189459969825483 := by
  refine Pratt.pratt 1189459969825483 2 [(2, 1), (3, 2), (17, 1), (107, 1), (521, 1), (69727951, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p69727951

theorem p2202108263 : Nat.Prime 2202108263 := by
  refine Pratt.pratt 2202108263 5 [(2, 1), (26711, 1), (41221, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p1189459969826399 : Nat.Prime 1189459969826399 := by
  refine Pratt.pratt 1189459969826399 13 [(2, 1), (270073, 1), (2202108263, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p2202108263

theorem p1123165739651 : Nat.Prime 1123165739651 := by
  refine Pratt.pratt 1123165739651 6 [(2, 1), (5, 2), (73, 1), (3571, 1), (86171, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p1686994940955803 : Nat.Prime 1686994940955803 := by
  refine Pratt.pratt 1686994940955803 2 [(2, 1), (751, 1), (1123165739651, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p1123165739651

theorem p2364214819 : Nat.Prime 2364214819 := by
  refine Pratt.pratt 2364214819 7 [(2, 1), (3, 1), (7, 2), (8041547, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p1686994940956727 : Nat.Prime 1686994940956727 := by
  refine Pratt.pratt 1686994940956727 5 [(2, 1), (47, 1), (7591, 1), (2364214819, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p2364214819

theorem p16469043077 : Nat.Prime 16469043077 := by
  refine Pratt.pratt 16469043077 2 [(2, 2), (5657, 1), (727817, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p1693182318746371 : Nat.Prime 1693182318746371 := by
  refine Pratt.pratt 1693182318746371 10 [(2, 1), (3, 1), (5, 1), (23, 1), (149, 1), (16469043077, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p16469043077

theorem p374276411 : Nat.Prime 374276411 := by
  refine Pratt.pratt 374276411 6 [(2, 1), (5, 1), (1109, 1), (33749, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p1693182318747503 : Nat.Prime 1693182318747503 := by
  refine Pratt.pratt 1693182318747503 5 [(2, 1), (11, 1), (61, 1), (3371, 1), (374276411, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p374276411

theorem p57523969021 : Nat.Prime 57523969021 := by
  refine Pratt.pratt 57523969021 10 [(2, 2), (3, 1), (5, 1), (7, 1), (367, 1), (373193, 1)] (by norm_num)
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

theorem p1289457289574737 : Nat.Prime 1289457289574737 := by
  refine Pratt.pratt 1289457289574737 5 [(2, 4), (3, 1), (467, 1), (57523969021, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p57523969021

theorem p43841547845541059 : Nat.Prime 43841547845541059 := by
  refine Pratt.pratt 43841547845541059 2 [(2, 1), (17, 1), (1289457289574737, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p1289457289574737

theorem p43841547845542243 : Nat.Prime 43841547845542243 := by
  refine Pratt.pratt 43841547845542243 2 [(2, 1), (3, 2), (47, 1), (139, 1), (118211, 1), (3153863, 1)] (by norm_num)
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

theorem p44045383561 : Nat.Prime 44045383561 := by
  refine Pratt.pratt 44045383561 17 [(2, 3), (3, 1), (5, 1), (881, 1), (416623, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p9225129405317207 : Nat.Prime 9225129405317207 := by
  refine Pratt.pratt 9225129405317207 5 [(2, 1), (104723, 1), (44045383561, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p44045383561

theorem p55350776431903243 : Nat.Prime 55350776431903243 := by
  refine Pratt.pratt 55350776431903243 2 [(2, 1), (3, 1), (9225129405317207, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p9225129405317207

theorem p126014881231 : Nat.Prime 126014881231 := by
  refine Pratt.pratt 126014881231 3 [(2, 1), (3, 2), (5, 1), (7, 2), (19, 1), (1503937, 1)] (by norm_num)
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

theorem p55350776431904441 : Nat.Prime 55350776431904441 := by
  refine Pratt.pratt 55350776431904441 3 [(2, 3), (5, 1), (79, 1), (139, 1), (126014881231, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p126014881231

theorem p3240386761 : Nat.Prime 3240386761 := by
  refine Pratt.pratt 3240386761 11 [(2, 3), (3, 1), (5, 1), (13, 1), (89, 1), (23339, 1)] (by norm_num)
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

theorem p9325833098159 : Nat.Prime 9325833098159 := by
  refine Pratt.pratt 9325833098159 7 [(2, 1), (1439, 1), (3240386761, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p3240386761

theorem p80873624627234849 : Nat.Prime 80873624627234849 := by
  refine Pratt.pratt 80873624627234849 3 [(2, 5), (271, 1), (9325833098159, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p9325833098159

theorem p57338149201 : Nat.Prime 57338149201 := by
  refine Pratt.pratt 57338149201 13 [(2, 4), (3, 1), (5, 2), (1559, 1), (30649, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p80873624627236069 : Nat.Prime 80873624627236069 := by
  refine Pratt.pratt 80873624627236069 2 [(2, 2), (3, 1), (117539, 1), (57338149201, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p57338149201

theorem p71725203416827 : Nat.Prime 71725203416827 := by
  refine Pratt.pratt 71725203416827 3 [(2, 1), (3, 3), (257, 1), (809, 1), (6388463, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p203986478517455989 : Nat.Prime 203986478517455989 := by
  refine Pratt.pratt 203986478517455989 6 [(2, 2), (3, 2), (79, 1), (71725203416827, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p71725203416827

theorem p107338607 : Nat.Prime 107338607 := by
  refine Pratt.pratt 107338607 5 [(2, 1), (3307, 1), (16229, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p26394469 : Nat.Prime 26394469 := by
  refine Pratt.pratt 26394469 2 [(2, 2), (3, 1), (37, 1), (59447, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p5666291069929367 : Nat.Prime 5666291069929367 := by
  refine Pratt.pratt 5666291069929367 5 [(2, 1), (26394469, 1), (107338607, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact p26394469
  · exact p107338607

theorem p203986478517457213 : Nat.Prime 203986478517457213 := by
  refine Pratt.pratt 203986478517457213 2 [(2, 2), (3, 2), (5666291069929367, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p5666291069929367

theorem p567798753109933 : Nat.Prime 567798753109933 := by
  refine Pratt.pratt 567798753109933 2 [(2, 2), (3, 3), (41, 1), (36467, 1), (3516307, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p218034721194214273 : Nat.Prime 218034721194214273 := by
  refine Pratt.pratt 218034721194214273 5 [(2, 7), (3, 1), (567798753109933, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p567798753109933

theorem p64891286069707 : Nat.Prime 64891286069707 := by
  refine Pratt.pratt 64891286069707 2 [(2, 1), (3, 2), (19, 1), (321991, 1), (589273, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p218034721194215521 : Nat.Prime 218034721194215521 := by
  refine Pratt.pratt 218034721194215521 31 [(2, 5), (3, 1), (5, 1), (7, 1), (64891286069707, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p64891286069707

theorem p877602949773241 : Nat.Prime 877602949773241 := by
  refine Pratt.pratt 877602949773241 7 [(2, 3), (3, 1), (5, 1), (37, 1), (61, 1), (15173, 1), (213557, 1)] (by norm_num)
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

theorem p305405826521087869 : Nat.Prime 305405826521087869 := by
  refine Pratt.pratt 305405826521087869 6 [(2, 2), (3, 1), (29, 1), (877602949773241, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p877602949773241

theorem p305405826521089141 : Nat.Prime 305405826521089141 := by
  refine Pratt.pratt 305405826521089141 6 [(2, 2), (3, 2), (5, 1), (7, 1), (11, 1), (991, 1), (17383, 1), (1279133, 1)] (by norm_num)
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

theorem p42169658413 : Nat.Prime 42169658413 := by
  refine Pratt.pratt 42169658413 5 [(2, 2), (3, 1), (7, 1), (15349, 1), (32707, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p352521223451364323 : Nat.Prime 352521223451364323 := by
  refine Pratt.pratt 352521223451364323 2 [(2, 1), (83, 1), (50359, 1), (42169658413, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p42169658413

theorem p2574087064267 : Nat.Prime 2574087064267 := by
  refine Pratt.pratt 2574087064267 2 [(2, 1), (3, 1), (47, 1), (281, 1), (349, 1), (93077, 1)] (by norm_num)
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

theorem p352521223451365651 : Nat.Prime 352521223451365651 := by
  refine Pratt.pratt 352521223451365651 2 [(2, 1), (3, 1), (5, 2), (11, 1), (83, 1), (2574087064267, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p2574087064267

theorem p18232161133 : Nat.Prime 18232161133 := by
  refine Pratt.pratt 18232161133 2 [(2, 2), (3, 1), (19, 1), (181, 1), (441799, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p401429925999153707 : Nat.Prime 401429925999153707 := by
  refine Pratt.pratt 401429925999153707 2 [(2, 1), (223, 1), (49367, 1), (18232161133, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p18232161133

theorem p401429925999155063 : Nat.Prime 401429925999155063 := by
  refine Pratt.pratt 401429925999155063 5 [(2, 1), (61, 1), (13963, 1), (407857, 1), (577781, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p402342697 : Nat.Prime 402342697 := by
  refine Pratt.pratt 402342697 5 [(2, 3), (3, 2), (7, 1), (137, 1), (5827, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p75730551800129 : Nat.Prime 75730551800129 := by
  refine Pratt.pratt 75730551800129 3 [(2, 6), (17, 1), (173, 1), (402342697, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p402342697

theorem p9087666216015481 : Nat.Prime 9087666216015481 := by
  refine Pratt.pratt 9087666216015481 14 [(2, 3), (3, 1), (5, 1), (75730551800129, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p75730551800129

theorem p418032645936712127 : Nat.Prime 418032645936712127 := by
  refine Pratt.pratt 418032645936712127 5 [(2, 1), (23, 1), (9087666216015481, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p9087666216015481

theorem p324339923543 : Nat.Prime 324339923543 := by
  refine Pratt.pratt 324339923543 5 [(2, 1), (347, 1), (1367, 1), (341879, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p418032645936713497 : Nat.Prime 418032645936713497 := by
  refine Pratt.pratt 418032645936713497 5 [(2, 3), (3, 6), (13, 1), (17, 1), (324339923543, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p324339923543

theorem p1121599249 : Nat.Prime 1121599249 := by
  refine Pratt.pratt 1121599249 31 [(2, 4), (3, 1), (7, 1), (11, 1), (303463, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p804212830686677669 : Nat.Prime 804212830686677669 := by
  refine Pratt.pratt 804212830686677669 2 [(2, 2), (761, 1), (235553, 1), (1121599249, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p1121599249

theorem p804212830686679111 : Nat.Prime 804212830686679111 := by
  refine Pratt.pratt 804212830686679111 3 [(2, 1), (3, 3), (5, 1), (5849, 1), (655913, 1), (776389, 1)] (by norm_num)
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

theorem p655664866807 : Nat.Prime 655664866807 := by
  refine Pratt.pratt 655664866807 3 [(2, 1), (3, 1), (23, 1), (1801, 1), (2638087, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p1425172824437699411 : Nat.Prime 1425172824437699411 := by
  refine Pratt.pratt 1425172824437699411 2 [(2, 1), (5, 1), (217363, 1), (655664866807, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p655664866807

theorem p712586412218850443 : Nat.Prime 712586412218850443 := by
  refine Pratt.pratt 712586412218850443 2 [(2, 1), (7, 1), (13, 1), (251, 1), (2352079, 1), (6631939, 1)] (by norm_num)
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

theorem p1425172824437700887 : Nat.Prime 1425172824437700887 := by
  refine Pratt.pratt 1425172824437700887 5 [(2, 1), (712586412218850443, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p712586412218850443

def ds_218209405436543 : List ℕ := [
    2, 5, 2, 3, 2, 23, 2, 73, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 7, 2, 10033867, 2, 3, 2, 19, 2, 31, 2, 3,
    2, 823, 2, 5, 2, 3, 2, 53, 2, 13, 2, 3, 2, 5,
    2, 67, 2, 3, 2, 17, 2, 61, 2, 3, 2, 7643, 2, 903479,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 157, 2, 44269, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 7417, 2, 5009, 2, 3, 2, 11,
    2, 9803, 2, 3, 2, 13, 2, 5, 2, 3, 2, 101, 2, 23,
    2, 3, 2, 5, 2, 6343, 2, 3, 2, 134363, 2, 599, 2, 3,
    2, 7369, 2, 7, 2, 3, 2, 68219, 2, 5, 2, 3, 2, 317,
    2, 11, 2, 3, 2, 5, 2, 181, 2, 3, 2, 19, 2, 103,
    2, 3, 2, 7, 2, 71, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 271, 2, 7, 2, 3, 2, 5, 2, 5701, 2, 3, 2, 13,
    2, 179, 2, 3, 2, 11971, 2, 19, 2, 3, 2, 347, 2, 5,
    2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 1439, 2, 7, 2, 3, 2, 89, 2, 8677, 2, 3, 2, 113,
    2, 5, 2, 3, 2, 11, 2, 17, 2, 3, 2, 5, 2, 37,
    2, 3, 2, 7, 2, 251, 2, 3, 2, 43, 2, 23, 2, 3,
    2, 12943781, 2, 5, 2, 3, 2, 13, 2, 53, 2, 3, 2, 5,
    2, 76649, 2, 3, 2, 701377, 2, 11, 2, 3, 2, 1979, 2, 607,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 3516427, 2, 7331, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 71, 2, 19, 2, 3, 2, 61,
    2, 839, 2, 3, 2, 73, 2, 5, 2, 3, 2, 47, 2, 41,
    2, 3, 2, 5, 2, 3209, 2, 3, 2, 83, 2, 17, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 109, 2, 5, 2, 3, 2, 31,
    2, 563, 2, 3, 2, 5, 2, 137, 2, 3, 2, 11, 2, 13,
    2, 3, 2, 7, 2, 1523, 2, 3, 2, 842791, 2, 5, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 1693,
    2, 157, 2, 3, 2, 2027, 2, 59, 2, 3, 2, 41, 2, 5,
    2, 3, 2, 7, 2, 31, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 10499, 2, 7, 2, 3, 2, 11, 2, 61, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 1511, 2, 13, 2, 3, 2, 5, 2, 7013,
    2, 3, 2, 7, 2, 182489, 2, 3, 2, 258061, 2, 37, 2, 3,
    2, 827, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5,
    2, 41761, 2, 3, 2, 848681, 2, 5281891, 2, 3, 2, 677, 2, 11719,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 7243, 2, 929, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 1049, 2, 101, 2, 3, 2, 59,
    2, 13, 2, 3, 2, 193, 2, 5, 2, 3, 2, 79, 2, 19,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 179, 2, 409, 2, 3,
    2, 1487, 2, 7, 2, 3, 2, 269, 2, 5, 2, 3, 2, 11,
    2, 109, 2, 3, 2, 5, 2, 41, 2, 3, 2, 13, 2, 89,
    2, 3, 2, 7, 2, 53, 2, 3, 2, 11497, 2, 5, 2, 3,
    2, 1997, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 47,
    2, 11, 2, 3, 2, 19, 2, 3833, 2, 3, 2, 290657, 2, 5,
    2, 3, 2, 7, 2, 1889, 2, 3, 2, 5, 2, 706099, 2, 3,
    2, 137, 2, 7, 2, 3, 2, 313, 2, 17, 2, 3, 2, 809,
    2, 5, 2, 3, 2, 13, 2, 5557, 2, 3, 2, 5, 2, 127,
    2, 3, 2, 7, 2, 23, 2, 3, 2, 307, 2, 11, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 149, 2, 37, 2, 3, 2, 5,
    2, 79, 2, 3, 2, 11, 2, 6379, 2, 3, 2, 24889, 2, 443,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2, 97, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 19, 2, 29, 2, 3, 2, 13,
    2, 15017, 2, 3, 2, 281, 2, 5, 2, 3, 2, 283, 2, 17,
    2, 3, 2, 5, 2, 167, 2, 3, 2, 73, 2, 13, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 43, 2, 5, 2, 3, 2, 331,
    2, 103, 2, 3, 2, 5, 2, 233, 2, 3, 2, 29, 2, 31,
    2, 3, 2, 7, 2, 47, 2, 3, 2, 50459, 2, 5, 2, 3,
    2, 449, 2, 7, 2, 3, 2, 5, 2, 7270451, 2, 3, 2, 471703,
    2, 41, 2, 3, 2, 4993, 2, 521, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 227, 2, 3,
    2, 9887, 2, 7, 2, 3, 2, 23, 2, 43, 2, 3, 2, 491,
    2, 5, 2, 3, 2, 971, 2, 67, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 19, 2, 3, 2, 17, 2, 308999, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 11, 2, 8113387, 2, 3, 2, 5,
    2, 29, 2, 3, 2, 107, 2, 37, 2, 3, 2, 31, 2, 13,
    2, 3, 2, 7, 2, 5, 2, 3, 2]

/-- A002386 row: the prime after 218209405436543 is 218209405436543 + 906. -/
theorem gap_218209405436543 : IsGapAt 218209405436543 906 :=
  isGapAt_of 218209405436543 906 (p218209405436543) (by show Nat.Prime 218209405437449; exact p218209405437449) ds_218209405436543 (by decide +kernel)

def ds_1189459969825483 : List ℕ := [
    2, 3, 2, 22907, 2, 18787, 2, 3, 2, 127, 2, 5, 2, 3,
    2, 17, 2, 11, 2, 3, 2, 5, 2, 1203863, 2, 3, 2, 101,
    2, 79, 2, 3, 2, 13, 2, 7, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 149, 2, 67, 2, 3, 2, 5, 2, 33071917, 2, 3,
    2, 587, 2, 13, 2, 3, 2, 7, 2, 87671, 2, 3, 2, 41,
    2, 5, 2, 3, 2, 641, 2, 7, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 19, 2, 47, 2, 3, 2, 71, 2, 193, 2, 3,
    2, 30694511, 2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 17, 2, 7, 2, 3, 2, 661, 2, 19,
    2, 3, 2, 61, 2, 5, 2, 3, 2, 109, 2, 13, 2, 3,
    2, 5, 2, 137, 2, 3, 2, 7, 2, 11, 2, 3, 2, 4231,
    2, 59, 2, 3, 2, 18869, 2, 5, 2, 3, 2, 4903, 2, 2897,
    2, 3, 2, 5, 2, 6619, 2, 3, 2, 14679341, 2, 4007, 2, 3,
    2, 47, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3, 2, 347,
    2, 1361, 2, 3, 2, 5, 2, 7, 2, 3, 2, 139, 2, 2969,
    2, 3, 2, 295513, 2, 11, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 222647, 2, 28279639, 2, 3, 2, 5, 2, 29, 2, 3, 2, 11,
    2, 19, 2, 3, 2, 43, 2, 7, 2, 3, 2, 599, 2, 5,
    2, 3, 2, 37, 2, 22475701, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 13, 2, 6691, 2, 3, 2, 7, 2, 479, 2, 3, 2, 223,
    2, 5, 2, 3, 2, 227, 2, 7, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 113, 2, 31, 2, 3, 2, 11, 2, 433, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 7, 2, 2953, 2, 3, 2, 5,
    2, 1829473, 2, 3, 2, 643, 2, 7, 2, 3, 2, 131, 2, 31087499,
    2, 3, 2, 1077751, 2, 5, 2, 3, 2, 13, 2, 11, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 7, 2, 158927, 2, 3, 2, 977,
    2, 157, 2, 3, 2, 11, 2, 5, 2, 3, 2, 103, 2, 71,
    2, 3, 2, 5, 2, 541, 2, 3, 2, 1997, 2, 17, 2, 3,
    2, 947, 2, 229, 2, 3, 2, 7, 2, 5, 2, 3, 2, 569,
    2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 137, 2, 18072293,
    2, 3, 2, 13, 2, 5153, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 11, 2, 89, 2, 3, 2, 5, 2, 277, 2, 3, 2, 23,
    2, 13, 2, 3, 2, 7537, 2, 7, 2, 3, 2, 971, 2, 5,
    2, 3, 2, 29, 2, 19, 2, 3, 2, 5, 2, 293261, 2, 3,
    2, 37, 2, 11, 2, 3, 2, 7, 2, 31, 2, 3, 2, 2549,
    2, 5, 2, 3, 2, 61, 2, 7, 2, 3, 2, 5, 2, 79,
    2, 3, 2, 1609, 2, 59, 2, 3, 2, 34471, 2, 1427, 2, 3,
    2, 71, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5,
    2, 107, 2, 3, 2, 9754523, 2, 7, 2, 3, 2, 19, 2, 11,
    2, 3, 2, 5431, 2, 5, 2, 3, 2, 724021, 2, 5737, 2, 3,
    2, 5, 2, 6538879, 2, 3, 2, 7, 2, 257, 2, 3, 2, 213407,
    2, 2814569, 2, 3, 2, 13, 2, 5, 2, 3, 2, 23, 2, 43,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 134033, 2, 383, 2, 3,
    2, 55823, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3, 2, 83,
    2, 61, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 3301,
    2, 3, 2, 11, 2, 1097, 2, 3, 2, 29, 2, 5, 2, 3,
    2, 1433, 2, 21493, 2, 3, 2, 5, 2, 47, 2, 3, 2, 13,
    2, 233, 2, 3, 2, 3253, 2, 7, 2, 3, 2, 7546069, 2, 5,
    2, 3, 2, 14867, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 30269, 2, 6037, 2, 3, 2, 7, 2, 17, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 26717, 2, 7, 2, 3, 2, 5, 2, 1120159,
    2, 3, 2, 53, 2, 161761, 2, 3, 2, 23, 2, 41, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 7, 2, 547, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 47, 2, 7, 2, 3, 2, 8753, 2, 29,
    2, 3, 2, 43, 2, 5, 2, 3, 2, 11, 2, 1123, 2, 3,
    2, 5, 2, 37, 2, 3, 2, 7, 2, 4163801, 2, 3, 2, 5820599,
    2, 11491, 2, 3, 2, 73, 2, 5, 2, 3, 2, 31, 2, 17,
    2, 3, 2, 5, 2, 71, 2, 3, 2, 41, 2, 11, 2, 3,
    2, 13, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 1054531,
    2, 523, 2, 3, 2, 5, 2, 7, 2, 3, 2, 2071591, 2, 13,
    2, 3, 2, 811, 2, 43, 2, 3, 2, 317, 2, 5, 2, 3,
    2, 4567, 2, 31, 2, 3, 2, 5, 2, 59, 2, 3, 2, 193,
    2, 677, 2, 3, 2, 16411, 2, 7, 2, 3, 2, 1327, 2, 5,
    2, 3, 2, 19, 2, 151, 2, 3, 2, 5, 2, 683, 2, 3,
    2, 11, 2, 17, 2, 3, 2, 7, 2, 2188451, 2, 3, 2, 22943,
    2, 5, 2, 3, 2]

/-- A002386 row: the prime after 1189459969825483 is 1189459969825483 + 916. -/
theorem gap_1189459969825483 : IsGapAt 1189459969825483 916 :=
  isGapAt_of 1189459969825483 916 (p1189459969825483) (by show Nat.Prime 1189459969826399; exact p1189459969826399) ds_1189459969825483 (by decide +kernel)

def ds_1686994940955803 : List ℕ := [
    2, 5, 2, 3, 2, 988147, 2, 313, 2, 3, 2, 5, 2, 1093,
    2, 3, 2, 7, 2, 11381033, 2, 3, 2, 37, 2, 3313, 2, 3,
    2, 47, 2, 5, 2, 3, 2, 163, 2, 11, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 19, 2, 443, 2, 3, 2, 13, 2, 139,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 71, 2, 877, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 359, 2, 13, 2, 3, 2, 89,
    2, 17, 2, 3, 2, 405439, 2, 5, 2, 3, 2, 53, 2, 37,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 5653, 2, 383, 2, 3,
    2, 8377, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 11,
    2, 197, 2, 3, 2, 5, 2, 23, 2, 3, 2, 5573, 2, 10867099,
    2, 3, 2, 7, 2, 885721, 2, 3, 2, 131, 2, 5, 2, 3,
    2, 149, 2, 7, 2, 3, 2, 5, 2, 883, 2, 3, 2, 31,
    2, 11, 2, 3, 2, 41, 2, 73, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 1381, 2, 3,
    2, 103, 2, 7, 2, 3, 2, 43, 2, 179, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 29, 2, 47, 2, 3, 2, 5, 2, 283,
    2, 3, 2, 7, 2, 31, 2, 3, 2, 337, 2, 11, 2, 3,
    2, 311, 2, 5, 2, 3, 2, 37, 2, 36599, 2, 3, 2, 5,
    2, 419, 2, 3, 2, 11, 2, 6258401, 2, 3, 2, 223, 2, 563,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 457, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 13, 2, 17, 2, 3, 2, 2087,
    2, 113, 2, 3, 2, 1433, 2, 5, 2, 3, 2, 373, 2, 53,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 23, 2, 37, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 109, 2, 5, 2, 3, 2, 157,
    2, 41, 2, 3, 2, 5, 2, 10738181, 2, 3, 2, 11731, 2, 61,
    2, 3, 2, 7, 2, 3989, 2, 3, 2, 1087, 2, 5, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 5, 2, 824773, 2, 3, 2, 47303,
    2, 24181877, 2, 3, 2, 101, 2, 15341369, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 7, 2, 1409, 2, 3, 2, 5, 2, 103, 2, 3,
    2, 439, 2, 7, 2, 3, 2, 53, 2, 31, 2, 3, 2, 41,
    2, 5, 2, 3, 2, 17, 2, 19, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 89, 2, 3, 2, 13, 2, 541, 2, 3,
    2, 127, 2, 5, 2, 3, 2, 11, 2, 59, 2, 3, 2, 5,
    2, 641, 2, 3, 2, 37, 2, 13, 2, 3, 2, 29961961, 2, 12325069,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 2270483, 2, 66629, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 79, 2, 11, 2, 3, 2, 19,
    2, 29, 2, 3, 2, 151, 2, 5, 2, 3, 2, 32743147, 2, 198673,
    2, 3, 2, 5, 2, 947, 2, 3, 2, 17, 2, 19513691, 2, 3,
    2, 167, 2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 900929,
    2, 13, 2, 3, 2, 5, 2, 308887, 2, 3, 2, 11087, 2, 4457,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 181, 2, 5, 2, 3,
    2, 59, 2, 7, 2, 3, 2, 5, 2, 41, 2, 3, 2, 11,
    2, 487, 2, 3, 2, 23, 2, 17, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 7, 2, 293, 2, 3, 2, 5, 2, 73, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 327473, 2, 13, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 983, 2, 680749, 2, 3, 2, 5, 2, 2161,
    2, 3, 2, 7, 2, 157, 2, 3, 2, 11, 2, 19, 2, 3,
    2, 4649, 2, 5, 2, 3, 2, 41, 2, 33311, 2, 3, 2, 5,
    2, 131, 2, 3, 2, 13, 2, 29, 2, 3, 2, 937, 2, 23,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 479, 2, 11, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 3209, 2, 223, 2, 3, 2, 5044547,
    2, 61, 2, 3, 2, 11, 2, 5, 2, 3, 2, 31, 2, 3096061,
    2, 3, 2, 5, 2, 5431, 2, 3, 2, 29, 2, 1549, 2, 3,
    2, 251, 2, 7, 2, 3, 2, 227, 2, 5, 2, 3, 2, 13,
    2, 41543, 2, 3, 2, 5, 2, 11, 2, 3, 2, 331, 2, 19,
    2, 3, 2, 7, 2, 71, 2, 3, 2, 19028221, 2, 5, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 5, 2, 648199, 2, 3, 2, 97,
    2, 17, 2, 3, 2, 5281, 2, 43, 2, 3, 2, 12043, 2, 5,
    2, 3, 2, 7, 2, 5333, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 233, 2, 7, 2, 3, 2, 13, 2, 50893, 2, 3, 2, 1018559,
    2, 5, 2, 3, 2, 19, 2, 1637, 2, 3, 2, 5, 2, 29,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 2767, 2, 218627, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 47, 2, 677, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 5356783, 2, 139, 2, 3, 2, 837467, 2, 11,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 73, 2, 337, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 11, 2, 10143659, 2, 3, 2]

/-- A002386 row: the prime after 1686994940955803 is 1686994940955803 + 924. -/
theorem gap_1686994940955803 : IsGapAt 1686994940955803 924 :=
  isGapAt_of 1686994940955803 924 (p1686994940955803) (by show Nat.Prime 1686994940956727; exact p1686994940956727) ds_1686994940955803 (by decide +kernel)

def ds_1693182318746371 : List ℕ := [
    2, 3, 2, 5, 2, 1787, 2, 3, 2, 263, 2, 131, 2, 3,
    2, 7, 2, 1307, 2, 3, 2, 23, 2, 5, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 5, 2, 709, 2, 3, 2, 1008563, 2, 11,
    2, 3, 2, 89, 2, 11177, 2, 3, 2, 47, 2, 5, 2, 3,
    2, 7, 2, 844867, 2, 3, 2, 5, 2, 17, 2, 3, 2, 2582681,
    2, 7, 2, 3, 2, 10531, 2, 13721, 2, 3, 2, 181, 2, 5,
    2, 3, 2, 4638377, 2, 35056849, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 7, 2, 167, 2, 3, 2, 13, 2, 11, 2, 3, 2, 31,
    2, 5, 2, 3, 2, 73, 2, 2797, 2, 3, 2, 5, 2, 59,
    2, 3, 2, 11, 2, 13, 2, 3, 2, 467, 2, 1499, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 149, 2, 22691, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 23, 2, 761, 2, 3, 2, 17571053, 2, 17,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 461, 2, 191, 2, 3,
    2, 5, 2, 1221593, 2, 3, 2, 17987, 2, 24192799, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 2287, 2, 13,
    2, 3, 2, 5, 2, 61, 2, 3, 2, 967229, 2, 2262409, 2, 3,
    2, 7, 2, 308851, 2, 3, 2, 761347, 2, 5, 2, 3, 2, 79,
    2, 7, 2, 3, 2, 5, 2, 293, 2, 3, 2, 23053, 2, 23,
    2, 3, 2, 362221, 2, 101, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 7, 2, 17, 2, 3, 2, 5, 2, 67, 2, 3, 2, 53,
    2, 7, 2, 3, 2, 19, 2, 13, 2, 3, 2, 431, 2, 5,
    2, 3, 2, 23, 2, 281, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 7, 2, 439, 2, 3, 2, 37, 2, 41, 2, 3, 2, 991,
    2, 5, 2, 3, 2, 11, 2, 229, 2, 3, 2, 5, 2, 97,
    2, 3, 2, 13, 2, 54139, 2, 3, 2, 227191, 2, 3301147, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 5522273, 2, 31, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 107, 2, 11, 2, 3, 2, 1019, 2, 28327799,
    2, 3, 2, 28607, 2, 5, 2, 3, 2, 463, 2, 23, 2, 3,
    2, 5, 2, 79, 2, 3, 2, 19, 2, 43, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 4489747, 2, 5, 2, 3, 2, 13, 2, 16301,
    2, 3, 2, 5, 2, 26699, 2, 3, 2, 4567, 2, 241, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 137, 2, 5, 2, 3, 2, 337,
    2, 7, 2, 3, 2, 5, 2, 127, 2, 3, 2, 11, 2, 23808853,
    2, 3, 2, 105251, 2, 71, 2, 3, 2, 29, 2, 5, 2, 3,
    2, 7, 2, 59, 2, 3, 2, 5, 2, 523, 2, 3, 2, 2551,
    2, 7, 2, 3, 2, 13, 2, 233, 2, 3, 2, 109, 2, 5,
    2, 3, 2, 17, 2, 2741, 2, 3, 2, 5, 2, 173, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 11, 2, 23, 2, 3, 2, 419,
    2, 5, 2, 3, 2, 37, 2, 389, 2, 3, 2, 5, 2, 31,
    2, 3, 2, 3391, 2, 19, 2, 3, 2, 73, 2, 18119, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 11725547, 2, 11, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 89, 2, 61, 2, 3, 2, 30941, 2, 29,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 53, 2, 13, 2, 3,
    2, 5, 2, 56747, 2, 3, 2, 17, 2, 37, 2, 3, 2, 47,
    2, 7, 2, 3, 2, 88589, 2, 5, 2, 3, 2, 19, 2, 746797,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 937, 2, 2621, 2, 3,
    2, 7, 2, 452531, 2, 3, 2, 13, 2, 5, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 5, 2, 19, 2, 3, 2, 31, 2, 659,
    2, 3, 2, 295247, 2, 13, 2, 3, 2, 102217, 2, 5, 2, 3,
    2, 7, 2, 353, 2, 3, 2, 5, 2, 3449, 2, 3, 2, 518239,
    2, 7, 2, 3, 2, 1297, 2, 251, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 1861, 2, 109, 2, 3, 2, 5, 2, 373463, 2, 3,
    2, 7, 2, 31, 2, 3, 2, 157, 2, 8087, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 6547, 2, 103, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 37, 2, 29, 2, 3, 2, 57367, 2, 11, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 199, 2, 17, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 11, 2, 587, 2, 3, 2, 367, 2, 107,
    2, 3, 2, 151, 2, 5, 2, 3, 2, 13, 2, 41, 2, 3,
    2, 5, 2, 687031, 2, 3, 2, 29, 2, 474709, 2, 3, 2, 61,
    2, 7, 2, 3, 2, 43, 2, 5, 2, 3, 2, 102481, 2, 2143,
    2, 3, 2, 5, 2, 947, 2, 3, 2, 23, 2, 24749, 2, 3,
    2, 7, 2, 5479, 2, 3, 2, 173, 2, 5, 2, 3, 2, 283,
    2, 7, 2, 3, 2, 5, 2, 33181, 2, 3, 2, 1567, 2, 17,
    2, 3, 2, 13, 2, 43997, 2, 3, 2, 41, 2, 5, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 5, 2, 2106523, 2, 3, 2, 54293,
    2, 7, 2, 3, 2, 17, 2, 31, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 569, 2, 24564011, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 7, 2, 23, 2, 3, 2, 67, 2, 61, 2, 3, 2, 59,
    2, 5, 2, 3, 2, 6679, 2, 12823, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 19, 2, 79103, 2, 3, 2, 383, 2, 6091, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 3187, 2, 6277, 2, 3, 2, 263647, 2, 19,
    2, 3, 2, 107, 2, 5, 2, 3, 2, 17, 2, 601, 2, 3,
    2, 5, 2, 673, 2, 3, 2, 739, 2, 11, 2, 3, 2, 71,
    2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 379, 2, 157,
    2, 3, 2, 5, 2, 37, 2, 3, 2, 131, 2, 263, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 1481321, 2, 5, 2, 3, 2, 197,
    2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 43, 2, 83,
    2, 3, 2, 36366269, 2, 11, 2, 3, 2, 2423, 2, 5, 2, 3,
    2, 7, 2, 29, 2, 3, 2, 5, 2, 113, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 23, 2, 53, 2, 3, 2]

/-- A002386 row: the prime after 1693182318746371 is 1693182318746371 + 1132. -/
theorem gap_1693182318746371 : IsGapAt 1693182318746371 1132 :=
  isGapAt_of 1693182318746371 1132 (p1693182318746371) (by show Nat.Prime 1693182318747503; exact p1693182318747503) ds_1693182318746371 (by decide +kernel)

def ds_43841547845541059 : List ℕ := [
    2, 7, 2, 3, 2, 5, 2, 47, 2, 3, 2, 101, 2, 1009,
    2, 3, 2, 41, 2, 149, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 7, 2, 61, 2, 3, 2, 5, 2, 2040097, 2, 3, 2, 229,
    2, 7, 2, 3, 2, 45868577, 2, 17, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 29, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 7, 2, 1709, 2, 3, 2, 67, 2, 367, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 11, 2, 19, 2, 3, 2, 5, 2, 163,
    2, 3, 2, 47, 2, 26325227, 2, 3, 2, 41731621, 2, 1447, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 719, 2, 2591, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 3601463, 2, 11, 2, 3, 2, 677357, 2, 13,
    2, 3, 2, 59, 2, 5, 2, 3, 2, 14200777, 2, 17, 2, 3,
    2, 5, 2, 37, 2, 3, 2, 1063, 2, 1307, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 12712499, 2, 5, 2, 3, 2, 19063129, 2, 23,
    2, 3, 2, 5, 2, 131, 2, 3, 2, 13, 2, 91367, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 173, 2, 5, 2, 3, 2, 137,
    2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 2557,
    2, 3, 2, 23, 2, 373, 2, 3, 2, 29, 2, 5, 2, 3,
    2, 7, 2, 6143, 2, 3, 2, 5, 2, 73, 2, 3, 2, 581863,
    2, 7, 2, 3, 2, 83, 2, 97, 2, 3, 2, 41, 2, 5,
    2, 3, 2, 13, 2, 2180491, 2, 3, 2, 5, 2, 90976243, 2, 3,
    2, 7, 2, 761, 2, 3, 2, 11, 2, 47, 2, 3, 2, 5167,
    2, 5, 2, 3, 2, 220793, 2, 31, 2, 3, 2, 5, 2, 43,
    2, 3, 2, 491, 2, 25997, 2, 3, 2, 149, 2, 19, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 151, 2, 11, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 29851, 2, 30851, 2, 3, 2, 13, 2, 29,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 7152407, 2, 345923, 2, 3,
    2, 5, 2, 39381887, 2, 3, 2, 419, 2, 13, 2, 3, 2, 3109,
    2, 7, 2, 3, 2, 47, 2, 5, 2, 3, 2, 17, 2, 89,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 347, 2, 79, 2, 3,
    2, 7, 2, 141209, 2, 3, 2, 109, 2, 5, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 5, 2, 41, 2, 3, 2, 467, 2, 19,
    2, 3, 2, 463, 2, 193, 2, 3, 2, 439, 2, 5, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3, 2, 62323,
    2, 7, 2, 3, 2, 36503107, 2, 197, 2, 3, 2, 46370053, 2, 5,
    2, 3, 2, 43, 2, 74587, 2, 3, 2, 5, 2, 31, 2, 3,
    2, 7, 2, 3271, 2, 3, 2, 59, 2, 229, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 19, 2, 113, 2, 3, 2, 5, 2, 48757,
    2, 3, 2, 743, 2, 29, 2, 3, 2, 37, 2, 11, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 73, 2, 311, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 11, 2, 157, 2, 3, 2, 127, 2, 17,
    2, 3, 2, 46681, 2, 5, 2, 3, 2, 89, 2, 47, 2, 3,
    2, 5, 2, 317, 2, 3, 2, 13, 2, 150881, 2, 3, 2, 1409,
    2, 7, 2, 3, 2, 17, 2, 5, 2, 3, 2, 27732673, 2, 37,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 31, 2, 67, 2, 3,
    2, 7, 2, 257, 2, 3, 2, 19, 2, 5, 2, 3, 2, 983,
    2, 7, 2, 3, 2, 5, 2, 269, 2, 3, 2, 23, 2, 270073,
    2, 3, 2, 97, 2, 8243, 2, 3, 2, 117163, 2, 5, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 5, 2, 62213, 2, 3, 2, 941,
    2, 7, 2, 3, 2, 223, 2, 547, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 1861, 2, 87679, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 7, 2, 107, 2, 3, 2, 146574287, 2, 9137, 2, 3, 2, 13285147,
    2, 5, 2, 3, 2, 79, 2, 499, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 277, 2, 23, 2, 3, 2, 13, 2, 1367, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 11, 2, 199, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 5035243, 2, 13, 2, 3, 2, 294001, 2, 181,
    2, 3, 2, 211, 2, 5, 2, 3, 2, 23, 2, 457, 2, 3,
    2, 5, 2, 19003601, 2, 3, 2, 1249, 2, 11, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 283, 2, 5, 2, 3, 2, 977, 2, 127,
    2, 3, 2, 5, 2, 102523, 2, 3, 2, 43721, 2, 37, 2, 3,
    2, 7, 2, 191, 2, 3, 2, 45904867, 2, 5, 2, 3, 2, 21665569,
    2, 7, 2, 3, 2, 5, 2, 54792653, 2, 3, 2, 19, 2, 47,
    2, 3, 2, 3877, 2, 11, 2, 3, 2, 197, 2, 5, 2, 3,
    2, 7, 2, 23, 2, 3, 2, 5, 2, 79, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 85831, 2, 19, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 17, 2, 1481, 2, 3, 2, 5, 2, 337, 2, 3,
    2, 7, 2, 149, 2, 3, 2, 23, 2, 13, 2, 3, 2, 643,
    2, 5, 2, 3, 2, 29, 2, 54959, 2, 3, 2, 5, 2, 1291,
    2, 3, 2, 71, 2, 1831, 2, 3, 2, 11, 2, 1429, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 53, 2, 6485497, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 13, 2, 131, 2, 3, 2, 73, 2, 108240149,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 1759, 2, 11, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 17, 2, 19, 2, 3, 2, 61,
    2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 4973071, 2, 101,
    2, 3, 2, 5, 2, 613, 2, 3, 2, 137, 2, 345041, 2, 3,
    2, 7, 2, 18397, 2, 3, 2, 139, 2, 5, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 997, 2, 9801523,
    2, 3, 2, 109, 2, 17, 2, 3, 2, 4373419, 2, 5, 2, 3,
    2, 7, 2, 43, 2, 3, 2, 5, 2, 59, 2, 3, 2, 21085091,
    2, 7, 2, 3, 2, 48311, 2, 20443, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 611113, 2, 307, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 13, 2, 61, 2, 3, 2, 257,
    2, 5, 2, 3, 2, 8629, 2, 3547, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 1319, 2, 13, 2, 3, 2, 11411, 2, 6916883, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 31, 2, 17, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 157, 2]

/-- A002386 row: the prime after 43841547845541059 is 43841547845541059 + 1184. -/
theorem gap_43841547845541059 : IsGapAt 43841547845541059 1184 :=
  isGapAt_of 43841547845541059 1184 (p43841547845541059) (by show Nat.Prime 43841547845542243; exact p43841547845542243) ds_43841547845541059 (by decide +kernel)

def ds_55350776431903243 : List ℕ := [
    2, 3, 2, 2617, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 1993, 2, 6703, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11,
    2, 421, 2, 3, 2, 13, 2, 23, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 619, 2, 29, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 31, 2, 13, 2, 3, 2, 6379, 2, 7, 2, 3, 2, 59,
    2, 5, 2, 3, 2, 432989, 2, 19, 2, 3, 2, 5, 2, 2953,
    2, 3, 2, 24950593, 2, 5869, 2, 3, 2, 7, 2, 43, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5,
    2, 329657, 2, 3, 2, 157, 2, 31, 2, 3, 2, 499, 2, 89,
    2, 3, 2, 4073, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 5, 2, 1531, 2, 3, 2, 64693, 2, 7, 2, 3, 2, 19,
    2, 47, 2, 3, 2, 11, 2, 5, 2, 3, 2, 179, 2, 17,
    2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 277, 2, 3,
    2, 5850827, 2, 3163, 2, 3, 2, 13, 2, 5, 2, 3, 2, 124918733,
    2, 457, 2, 3, 2, 5, 2, 11, 2, 3, 2, 75568463, 2, 4097113,
    2, 3, 2, 103, 2, 13, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 11, 2, 55313, 2, 3, 2, 5, 2, 7, 2, 3, 2, 211,
    2, 109, 2, 3, 2, 31, 2, 433, 2, 3, 2, 47, 2, 5,
    2, 3, 2, 27241, 2, 1783, 2, 3, 2, 5, 2, 23447, 2, 3,
    2, 13, 2, 11, 2, 3, 2, 691267, 2, 7, 2, 3, 2, 29,
    2, 5, 2, 3, 2, 61, 2, 1046849, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 41, 2, 129643, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 461, 2, 5, 2, 3, 2, 32266583, 2, 7, 2, 3, 2, 5,
    2, 785143, 2, 3, 2, 79, 2, 373, 2, 3, 2, 293, 2, 11,
    2, 3, 2, 67, 2, 5, 2, 3, 2, 7, 2, 926131, 2, 3,
    2, 5, 2, 43, 2, 3, 2, 11, 2, 7, 2, 3, 2, 3777131,
    2, 32789, 2, 3, 2, 163, 2, 5, 2, 3, 2, 11718821, 2, 191,
    2, 3, 2, 5, 2, 11483, 2, 3, 2, 7, 2, 9173, 2, 3,
    2, 71, 2, 29, 2, 3, 2, 98924879, 2, 5, 2, 3, 2, 17,
    2, 61, 2, 3, 2, 5, 2, 53, 2, 3, 2, 83, 2, 19,
    2, 3, 2, 11, 2, 120661, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 397, 2, 47, 2, 3, 2, 5, 2, 7, 2, 3, 2, 73,
    2, 13, 2, 3, 2, 29, 2, 10559, 2, 3, 2, 193, 2, 5,
    2, 3, 2, 18773, 2, 11, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 459047, 2, 587, 2, 3, 2, 5197, 2, 7, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 19, 2, 37, 2, 3, 2, 5, 2, 881,
    2, 3, 2, 17, 2, 131, 2, 3, 2, 7, 2, 97, 2, 3,
    2, 53, 2, 5, 2, 3, 2, 43, 2, 7, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 33739, 2, 1723, 2, 3, 2, 41, 2, 1289,
    2, 3, 2, 3463, 2, 5, 2, 3, 2, 7, 2, 251, 2, 3,
    2, 5, 2, 107, 2, 3, 2, 52434947, 2, 7, 2, 3, 2, 16661,
    2, 17, 2, 3, 2, 13, 2, 5, 2, 3, 2, 5851, 2, 23,
    2, 3, 2, 5, 2, 73, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 523, 2, 13, 2, 3, 2, 17, 2, 5, 2, 3, 2, 31,
    2, 149, 2, 3, 2, 5, 2, 173, 2, 3, 2, 29, 2, 3917,
    2, 3, 2, 23, 2, 977, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 37, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13,
    2, 59, 2, 3, 2, 288697, 2, 11, 2, 3, 2, 1543, 2, 5,
    2, 3, 2, 109, 2, 17, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 11, 2, 653, 2, 3, 2, 1191571, 2, 7, 2, 3, 2, 181,
    2, 5, 2, 3, 2, 379, 2, 41, 2, 3, 2, 5, 2, 643,
    2, 3, 2, 2003, 2, 37, 2, 3, 2, 7, 2, 23, 2, 3,
    2, 45413, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5,
    2, 29, 2, 3, 2, 107063149, 2, 83, 2, 3, 2, 11, 2, 268823,
    2, 3, 2, 191, 2, 5, 2, 3, 2, 7, 2, 443, 2, 3,
    2, 5, 2, 61, 2, 3, 2, 59, 2, 7, 2, 3, 2, 43,
    2, 223, 2, 3, 2, 41, 2, 5, 2, 3, 2, 229, 2, 11,
    2, 3, 2, 5, 2, 3301, 2, 3, 2, 7, 2, 892291, 2, 3,
    2, 13, 2, 137, 2, 3, 2, 11, 2, 5, 2, 3, 2, 197,
    2, 271, 2, 3, 2, 5, 2, 257, 2, 3, 2, 19, 2, 13,
    2, 3, 2, 2677, 2, 193, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 238531, 2, 12983, 2, 3, 2, 5, 2, 7, 2, 3, 2, 37,
    2, 43, 2, 3, 2, 208362043, 2, 19, 2, 3, 2, 409, 2, 5,
    2, 3, 2, 11, 2, 13912531, 2, 3, 2, 5, 2, 109, 2, 3,
    2, 87049, 2, 383, 2, 3, 2, 97, 2, 7, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 17, 2, 13, 2, 3, 2, 5, 2, 87797,
    2, 3, 2, 176629, 2, 11, 2, 3, 2, 7, 2, 1637, 2, 3,
    2, 32533, 2, 5, 2, 3, 2, 227, 2, 7, 2, 3, 2, 5,
    2, 41, 2, 3, 2, 288053, 2, 79, 2, 3, 2, 91529, 2, 37277,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 641, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 31, 2, 7, 2, 3, 2, 10009,
    2, 11, 2, 3, 2, 2207, 2, 5, 2, 3, 2, 33247, 2, 1301,
    2, 3, 2, 5, 2, 59, 2, 3, 2, 7, 2, 14783, 2, 3,
    2, 269, 2, 23029, 2, 3, 2, 74443321, 2, 5, 2, 3, 2, 41,
    2, 103, 2, 3, 2, 5, 2, 233, 2, 3, 2, 13, 2, 31,
    2, 3, 2, 143109359, 2, 72973, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 19, 2, 595271, 2, 3, 2, 5, 2, 7, 2, 3, 2, 503,
    2, 991, 2, 3, 2, 11, 2, 17, 2, 3, 2, 37, 2, 5,
    2, 3, 2, 47, 2, 97, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 199, 2, 7069, 2, 3, 2, 4074449, 2, 7, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 4817,
    2, 3, 2, 46348363, 2, 23, 2, 3, 2, 7, 2, 204487, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 53, 2, 7, 2, 3, 2, 5,
    2, 37, 2, 3, 2, 214003, 2, 787, 2, 3, 2, 31, 2, 14717,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 5, 2, 11, 2, 3, 2]

/-- A002386 row: the prime after 55350776431903243 is 55350776431903243 + 1198. -/
theorem gap_55350776431903243 : IsGapAt 55350776431903243 1198 :=
  isGapAt_of 55350776431903243 1198 (p55350776431903243) (by show Nat.Prime 55350776431904441; exact p55350776431904441) ds_55350776431903243 (by decide +kernel)

def ds_80873624627234849 : List ℕ := [
    2, 199, 2, 3, 2, 5, 2, 11, 2, 3, 2, 73, 2, 701,
    2, 3, 2, 419, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 11, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 6733,
    2, 809, 2, 3, 2, 5954633, 2, 23, 2, 3, 2, 251353, 2, 5,
    2, 3, 2, 5784749, 2, 181, 2, 3, 2, 5, 2, 5441, 2, 3,
    2, 47, 2, 11, 2, 3, 2, 14669, 2, 7, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 39371, 2, 17, 2, 3, 2, 5, 2, 761,
    2, 3, 2, 32869, 2, 499, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 67, 2, 5, 2, 3, 2, 223, 2, 7, 2, 3, 2, 5,
    2, 2237, 2, 3, 2, 571, 2, 19, 2, 3, 2, 1053757, 2, 11,
    2, 3, 2, 157, 2, 5, 2, 3, 2, 7, 2, 41, 2, 3,
    2, 5, 2, 73, 2, 3, 2, 11, 2, 7, 2, 3, 2, 241,
    2, 31, 2, 3, 2, 103, 2, 5, 2, 3, 2, 94752377, 2, 109,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 1889, 2, 59, 2, 3, 2, 211, 2, 5, 2, 3, 2, 19,
    2, 29, 2, 3, 2, 5, 2, 6701, 2, 3, 2, 107, 2, 4861,
    2, 3, 2, 11, 2, 647, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 13, 2, 154207649, 2, 3, 2, 5, 2, 7, 2, 3, 2, 61,
    2, 227, 2, 3, 2, 173, 2, 47, 2, 3, 2, 17383, 2, 5,
    2, 3, 2, 29, 2, 11, 2, 3, 2, 5, 2, 2459, 2, 3,
    2, 71, 2, 194758301, 2, 3, 2, 2207, 2, 7, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 113, 2, 37, 2, 3, 2, 5, 2, 9857,
    2, 3, 2, 3583, 2, 844601, 2, 3, 2, 7, 2, 83, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 43, 2, 13, 2, 3, 2, 877601, 2, 101,
    2, 3, 2, 47, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 5, 2, 10883, 2, 3, 2, 23, 2, 7, 2, 3, 2, 1013,
    2, 103, 2, 3, 2, 373, 2, 5, 2, 3, 2, 48271, 2, 89,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 7727, 2, 631, 2, 3, 2, 283027, 2, 5, 2, 3, 2, 9431,
    2, 13, 2, 3, 2, 5, 2, 43, 2, 3, 2, 17, 2, 244177,
    2, 3, 2, 19, 2, 3539, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 37, 2, 1499, 2, 3, 2, 5, 2, 7, 2, 3, 2, 151,
    2, 23, 2, 3, 2, 149, 2, 11, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 31, 2, 457, 2, 3, 2, 5, 2, 5632859, 2, 3,
    2, 11, 2, 2543, 2, 3, 2, 112921, 2, 7, 2, 3, 2, 127,
    2, 5, 2, 3, 2, 23, 2, 79, 2, 3, 2, 5, 2, 16292347,
    2, 3, 2, 95891, 2, 37, 2, 3, 2, 7, 2, 311, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 739, 2, 7, 2, 3, 2, 5,
    2, 167, 2, 3, 2, 13, 2, 59, 2, 3, 2, 11, 2, 29,
    2, 3, 2, 257, 2, 5, 2, 3, 2, 7, 2, 6907, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 1818221, 2, 7, 2, 3, 2, 1493,
    2, 19, 2, 3, 2, 63175591, 2, 5, 2, 3, 2, 43, 2, 11,
    2, 3, 2, 5, 2, 409, 2, 3, 2, 7, 2, 182131, 2, 3,
    2, 29, 2, 251, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13,
    2, 97, 2, 3, 2, 5, 2, 443, 2, 3, 2, 449, 2, 41,
    2, 3, 2, 23, 2, 67, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 201947, 2, 122597, 2, 3, 2, 5, 2, 7, 2, 3, 2, 37,
    2, 853, 2, 3, 2, 2185021, 2, 139, 2, 3, 2, 175327, 2, 5,
    2, 3, 2, 11, 2, 53, 2, 3, 2, 5, 2, 39868013, 2, 3,
    2, 3373, 2, 17, 2, 3, 2, 13, 2, 7, 2, 3, 2, 1151,
    2, 5, 2, 3, 2, 3671, 2, 95479, 2, 3, 2, 5, 2, 31,
    2, 3, 2, 6301, 2, 11, 2, 3, 2, 7, 2, 23, 2, 3,
    2, 359, 2, 5, 2, 3, 2, 12757, 2, 7, 2, 3, 2, 5,
    2, 127, 2, 3, 2, 8839, 2, 151, 2, 3, 2, 163, 2, 18059,
    2, 3, 2, 2719, 2, 5, 2, 3, 2, 7, 2, 4903, 2, 3,
    2, 5, 2, 3023, 2, 3, 2, 29, 2, 7, 2, 3, 2, 53,
    2, 11, 2, 3, 2, 641, 2, 5, 2, 3, 2, 32588429, 2, 13,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 47, 2, 3,
    2, 79, 2, 6203, 2, 3, 2, 38053, 2, 5, 2, 3, 2, 17,
    2, 307, 2, 3, 2, 5, 2, 1780021, 2, 3, 2, 31, 2, 14869,
    2, 3, 2, 43, 2, 38861, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 16655357, 2, 1538213, 2, 3, 2, 5, 2, 7, 2, 3, 2, 167,
    2, 4723, 2, 3, 2, 11, 2, 13, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 588167, 2, 15540997, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 421, 2, 31, 2, 3, 2, 47, 2, 7, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 4096349, 2, 11, 2, 3, 2, 5, 2, 6961,
    2, 3, 2, 13, 2, 43, 2, 3, 2, 7, 2, 173, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 9473, 2, 7, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 41, 2, 3613, 2, 3, 2, 113, 2, 1319,
    2, 3, 2, 61, 2, 5, 2, 3, 2, 7, 2, 71, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 130447, 2, 7, 2, 3, 2, 19,
    2, 17, 2, 3, 2, 27061, 2, 5, 2, 3, 2, 11, 2, 33934139,
    2, 3, 2, 5, 2, 521, 2, 3, 2, 7, 2, 73, 2, 3,
    2, 31, 2, 11827, 2, 3, 2, 17, 2, 5, 2, 3, 2, 2609,
    2, 67, 2, 3, 2, 5, 2, 5021, 2, 3, 2, 23, 2, 11,
    2, 3, 2, 131, 2, 313, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 1008437, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 1004363,
    2, 163, 2, 3, 2, 13, 2, 31, 2, 3, 2, 89, 2, 5,
    2, 3, 2, 1180159, 2, 17, 2, 3, 2, 5, 2, 563, 2, 3,
    2, 19, 2, 13, 2, 3, 2, 56099, 2, 7, 2, 3, 2, 71,
    2, 5, 2, 3, 2, 29, 2, 473971, 2, 3, 2, 5, 2, 181,
    2, 3, 2, 11, 2, 23, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 29027, 2, 5, 2, 3, 2, 811, 2, 7, 2, 3, 2, 5,
    2, 1426583, 2, 3, 2, 58699, 2, 70876103, 2, 3, 2, 126907367, 2, 37,
    2, 3, 2, 193, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 5, 2, 1909241, 2, 3, 2, 883, 2, 7, 2, 3, 2, 11,
    2]

/-- A002386 row: the prime after 80873624627234849 is 80873624627234849 + 1220. -/
theorem gap_80873624627234849 : IsGapAt 80873624627234849 1220 :=
  isGapAt_of 80873624627234849 1220 (p80873624627234849) (by show Nat.Prime 80873624627236069; exact p80873624627236069) ds_80873624627234849 (by decide +kernel)

def ds_203986478517455989 : List ℕ := [
    2, 3, 2, 211469, 2, 5, 2, 3, 2, 23, 2, 383, 2, 3,
    2, 5, 2, 397, 2, 3, 2, 13, 2, 89, 2, 3, 2, 184832771,
    2, 7, 2, 3, 2, 173, 2, 5, 2, 3, 2, 59, 2, 41,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 757, 2, 3,
    2, 7, 2, 6134137, 2, 3, 2, 13171, 2, 5, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 5, 2, 79, 2, 3, 2, 797681, 2, 43,
    2, 3, 2, 31, 2, 17, 2, 3, 2, 5081, 2, 5, 2, 3,
    2, 7, 2, 23, 2, 3, 2, 5, 2, 19, 2, 3, 2, 595577,
    2, 7, 2, 3, 2, 11, 2, 73, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 149, 2, 3169, 2, 3, 2, 5, 2, 61, 2, 3,
    2, 7, 2, 47, 2, 3, 2, 23, 2, 31, 2, 3, 2, 1579,
    2, 5, 2, 3, 2, 59453, 2, 11, 2, 3, 2, 5, 2, 1061,
    2, 3, 2, 53, 2, 67, 2, 3, 2, 13, 2, 158405921, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 103, 2, 17, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 89, 2, 13, 2, 3, 2, 643, 2, 907,
    2, 3, 2, 97, 2, 5, 2, 3, 2, 37, 2, 19, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 10799, 2, 15961753, 2, 3, 2, 47,
    2, 7, 2, 3, 2, 114269, 2, 5, 2, 3, 2, 11, 2, 519391,
    2, 3, 2, 5, 2, 113, 2, 3, 2, 2694847, 2, 127, 2, 3,
    2, 7, 2, 1266919, 2, 3, 2, 31, 2, 5, 2, 3, 2, 137,
    2, 7, 2, 3, 2, 5, 2, 41, 2, 3, 2, 5039, 2, 11,
    2, 3, 2, 19, 2, 29, 2, 3, 2, 283416031, 2, 5, 2, 3,
    2, 7, 2, 314189, 2, 3, 2, 5, 2, 197, 2, 3, 2, 11661289,
    2, 7, 2, 3, 2, 17, 2, 131, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 547769, 2, 43, 2, 3, 2, 5, 2, 1249, 2, 3,
    2, 7, 2, 38011, 2, 3, 2, 29, 2, 11, 2, 3, 2, 271,
    2, 5, 2, 3, 2, 41, 2, 977, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 11, 2, 53, 2, 3, 2, 3217, 2, 30491, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 3727, 2, 1619, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 13, 2, 523, 2, 3, 2, 25301, 2, 174890293,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 17, 2, 8353, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 37, 2, 251, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 4861, 2, 5, 2, 3, 2, 31, 2, 587,
    2, 3, 2, 5, 2, 223, 2, 3, 2, 443, 2, 29, 2, 3,
    2, 7, 2, 11031469, 2, 3, 2, 113, 2, 5, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 1675703, 2, 61,
    2, 3, 2, 2762713, 2, 157, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 7, 2, 31, 2, 3, 2, 5, 2, 683, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 4412377, 2, 179, 2, 3, 2, 101, 2, 5,
    2, 3, 2, 157669, 2, 79, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 7, 2, 19, 2, 3, 2, 13, 2, 239, 2, 3, 2, 887,
    2, 5, 2, 3, 2, 11, 2, 17669, 2, 3, 2, 5, 2, 211,
    2, 3, 2, 131, 2, 13, 2, 3, 2, 175277, 2, 17, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 2113, 2, 461, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 12239, 2, 11, 2, 3, 2, 692711, 2, 59,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 19, 2, 4027, 2, 3,
    2, 5, 2, 29, 2, 3, 2, 727, 2, 23, 2, 3, 2, 9521,
    2, 7, 2, 3, 2, 37, 2, 5, 2, 3, 2, 317, 2, 13,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 264183427, 2, 3257, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 929, 2, 5, 2, 3, 2, 23,
    2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 11, 2, 8848739,
    2, 3, 2, 1021, 2, 241, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 7, 2, 227, 2, 3, 2, 5, 2, 37, 2, 3, 2, 1621,
    2, 7, 2, 3, 2, 59, 2, 13, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 109, 2, 193, 2, 3, 2, 5, 2, 48103157, 2, 3,
    2, 7, 2, 294787, 2, 3, 2, 11, 2, 41, 2, 3, 2, 59879,
    2, 5, 2, 3, 2, 569, 2, 19, 2, 3, 2, 5, 2, 613,
    2, 3, 2, 13, 2, 17, 2, 3, 2, 53, 2, 855683, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 491, 2, 11, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 31, 2, 883, 2, 3, 2, 17, 2, 303217,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 73, 2, 309293, 2, 3,
    2, 5, 2, 43, 2, 3, 2, 41, 2, 10806127, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 23021, 2, 5, 2, 3, 2, 13, 2, 6203,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 279283981, 2, 31, 2, 3,
    2, 7, 2, 319873651, 2, 3, 2, 269, 2, 5, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 5, 2, 40255781, 2, 3, 2, 4271, 2, 379,
    2, 3, 2, 38693, 2, 23, 2, 3, 2, 673, 2, 5, 2, 3,
    2, 7, 2, 1860377, 2, 3, 2, 5, 2, 101, 2, 3, 2, 3853,
    2, 7, 2, 3, 2, 13, 2, 37, 2, 3, 2, 17959, 2, 5,
    2, 3, 2, 107, 2, 34429, 2, 3, 2, 5, 2, 67, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 109843, 2, 47, 2, 3, 2, 641,
    2, 5, 2, 3, 2, 2203, 2, 2141, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 761, 2, 103, 2, 3, 2, 31, 2, 11, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 43, 2, 2153, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 11, 2, 101986879, 2, 3, 2, 239, 2, 2677,
    2, 3, 2, 29, 2, 5, 2, 3, 2, 751, 2, 13, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 173, 2, 311, 2, 3, 2, 3511,
    2, 7, 2, 3, 2, 47, 2, 5, 2, 3, 2, 3659, 2, 89,
    2, 3, 2, 5, 2, 109159, 2, 3, 2, 59, 2, 19913, 2, 3,
    2, 7, 2, 17, 2, 3, 2, 13, 2, 5, 2, 3, 2, 51907,
    2, 7, 2, 3, 2, 5, 2, 5425283, 2, 3, 2, 28099, 2, 19,
    2, 3, 2, 157, 2, 13, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 5, 2, 24133, 2, 3, 2, 113,
    2, 7, 2, 3, 2, 431, 2, 29, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 31277, 2, 37, 2, 3, 2, 5, 2, 101063, 2, 3,
    2, 7, 2, 509, 2, 3, 2, 20183, 2, 419, 2, 3, 2, 31,
    2, 5, 2, 3, 2, 19, 2, 17, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 173696881, 2]

/-- A002386 row: the prime after 203986478517455989 is 203986478517455989 + 1224. -/
theorem gap_203986478517455989 : IsGapAt 203986478517455989 1224 :=
  isGapAt_of 203986478517455989 1224 (p203986478517455989) (by show Nat.Prime 203986478517457213; exact p203986478517457213) ds_203986478517455989 (by decide +kernel)

def ds_218034721194214273 : List ℕ := [
    2, 3, 2, 17, 2, 222526751, 2, 3, 2, 2791, 2, 5, 2, 3,
    2, 68539, 2, 61, 2, 3, 2, 5, 2, 2063, 2, 3, 2, 13,
    2, 115153, 2, 3, 2, 19, 2, 7, 2, 3, 2, 149, 2, 5,
    2, 3, 2, 257, 2, 37, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 11, 2, 23, 2, 3, 2, 7, 2, 41, 2, 3, 2, 933809,
    2, 5, 2, 3, 2, 2247461, 2, 7, 2, 3, 2, 5, 2, 119033,
    2, 3, 2, 103, 2, 31, 2, 3, 2, 67, 2, 29, 2, 3,
    2, 571, 2, 5, 2, 3, 2, 7, 2, 9526183, 2, 3, 2, 5,
    2, 13877, 2, 3, 2, 108203401, 2, 7, 2, 3, 2, 11, 2, 337,
    2, 3, 2, 71963, 2, 5, 2, 3, 2, 83, 2, 1117, 2, 3,
    2, 5, 2, 426779, 2, 3, 2, 7, 2, 27427, 2, 3, 2, 29,
    2, 76325927, 2, 3, 2, 2243, 2, 5, 2, 3, 2, 7229, 2, 11,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 21577, 2, 47, 2, 3,
    2, 13, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 37,
    2, 23, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 13,
    2, 3, 2, 31, 2, 5408989, 2, 3, 2, 3701, 2, 5, 2, 3,
    2, 53, 2, 67, 2, 3, 2, 5, 2, 11, 2, 3, 2, 113,
    2, 151, 2, 3, 2, 23, 2, 7, 2, 3, 2, 43, 2, 5,
    2, 3, 2, 11, 2, 229897, 2, 3, 2, 5, 2, 85819, 2, 3,
    2, 263, 2, 29, 2, 3, 2, 7, 2, 17, 2, 3, 2, 911,
    2, 5, 2, 3, 2, 15727, 2, 7, 2, 3, 2, 5, 2, 103,
    2, 3, 2, 331, 2, 11, 2, 3, 2, 191, 2, 2081, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 7, 2, 131, 2, 3, 2, 5,
    2, 189701, 2, 3, 2, 29, 2, 7, 2, 3, 2, 1093, 2, 23,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 1013, 2, 4876849, 2, 3,
    2, 5, 2, 115079, 2, 3, 2, 7, 2, 88996109, 2, 3, 2, 79,
    2, 11, 2, 3, 2, 1010881, 2, 5, 2, 3, 2, 19, 2, 17,
    2, 3, 2, 5, 2, 61, 2, 3, 2, 11, 2, 167, 2, 3,
    2, 41, 2, 350437883, 2, 3, 2, 7, 2, 5, 2, 3, 2, 379,
    2, 127, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 72719,
    2, 3, 2, 1387357, 2, 37139, 2, 3, 2, 1307, 2, 5, 2, 3,
    2, 107, 2, 53, 2, 3, 2, 5, 2, 13, 2, 3, 2, 97,
    2, 3235543, 2, 3, 2, 11, 2, 7, 2, 3, 2, 59, 2, 5,
    2, 3, 2, 5714671, 2, 83, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 229, 2, 17, 2, 3, 2, 7, 2, 277007, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 214063,
    2, 3, 2, 43, 2, 6079, 2, 3, 2, 17, 2, 19031, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5,
    2, 1523, 2, 3, 2, 163149401, 2, 7, 2, 3, 2, 53, 2, 109,
    2, 3, 2, 761, 2, 5, 2, 3, 2, 47, 2, 41, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 7, 2, 11789, 2, 3, 2, 13,
    2, 277, 2, 3, 2, 131, 2, 5, 2, 3, 2, 11, 2, 1248799,
    2, 3, 2, 5, 2, 43, 2, 3, 2, 195787, 2, 13, 2, 3,
    2, 19, 2, 601, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17,
    2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 61, 2, 11,
    2, 3, 2, 83, 2, 149, 2, 3, 2, 37, 2, 5, 2, 3,
    2, 438937, 2, 31, 2, 3, 2, 5, 2, 673, 2, 3, 2, 23,
    2, 1789, 2, 3, 2, 233, 2, 7, 2, 3, 2, 89, 2, 5,
    2, 3, 2, 29, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 78990817, 2, 113, 2, 3, 2, 7, 2, 11, 2, 3, 2, 82387,
    2, 5, 2, 3, 2, 103, 2, 7, 2, 3, 2, 5, 2, 37,
    2, 3, 2, 11, 2, 2242307, 2, 3, 2, 167, 2, 2677, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 7, 2, 439, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 17351, 2, 7, 2, 3, 2, 211, 2, 13,
    2, 3, 2, 121629881, 2, 5, 2, 3, 2, 43, 2, 2399, 2, 3,
    2, 5, 2, 769, 2, 3, 2, 7, 2, 129491, 2, 3, 2, 11,
    2, 17, 2, 3, 2, 31903649, 2, 5, 2, 3, 2, 23, 2, 983,
    2, 3, 2, 5, 2, 41, 2, 3, 2, 13, 2, 37889, 2, 3,
    2, 59, 2, 617, 2, 3, 2, 7, 2, 5, 2, 3, 2, 15766301,
    2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 47, 2, 73,
    2, 3, 2, 151, 2, 991, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 389, 2, 6907, 2, 3, 2, 5, 2, 107, 2, 3, 2, 758449,
    2, 19, 2, 3, 2, 4649, 2, 7, 2, 3, 2, 179, 2, 5,
    2, 3, 2, 13, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 67, 2, 227, 2, 3, 2, 7, 2, 1129, 2, 3, 2, 937,
    2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 71,
    2, 3, 2, 2676529, 2, 1909717, 2, 3, 2, 23, 2, 37, 2, 3,
    2, 335857, 2, 5, 2, 3, 2, 7, 2, 191969, 2, 3, 2, 5,
    2, 1171, 2, 3, 2, 31, 2, 7, 2, 3, 2, 13, 2, 29,
    2, 3, 2, 3547, 2, 5, 2, 3, 2, 173, 2, 401, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 7, 2, 13, 2, 3, 2, 61,
    2, 79, 2, 3, 2, 509, 2, 5, 2, 3, 2, 859, 2, 161869,
    2, 3, 2, 5, 2, 239, 2, 3, 2, 137, 2, 31, 2, 3,
    2, 17, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 283,
    2, 466183, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 41,
    2, 3, 2, 11536471, 2, 521, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 71, 2, 13, 2, 3, 2, 5, 2, 53, 2, 3, 2, 107,
    2, 7237, 2, 3, 2, 37, 2, 7, 2, 3, 2, 292667, 2, 5,
    2, 3, 2, 3583, 2, 19, 2, 3, 2, 5, 2, 131, 2, 3,
    2, 971, 2, 43, 2, 3, 2, 7, 2, 61, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 238207,
    2, 3, 2, 101, 2, 29, 2, 3, 2, 31, 2, 13, 2, 3,
    2, 457, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 59, 2, 7, 2, 3, 2, 19, 2, 211,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 1535767, 2, 547, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 7, 2, 109, 2, 3, 2, 89,
    2, 31, 2, 3, 2, 23, 2, 5, 2, 3, 2, 22453, 2, 2137,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2, 5659, 2, 3,
    2, 757, 2, 55337, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11,
    2]

/-- A002386 row: the prime after 218034721194214273 is 218034721194214273 + 1248. -/
theorem gap_218034721194214273 : IsGapAt 218034721194214273 1248 :=
  isGapAt_of 218034721194214273 1248 (p218034721194214273) (by show Nat.Prime 218034721194215521; exact p218034721194215521) ds_218034721194214273 (by decide +kernel)

def ds_305405826521087869 : List ℕ := [
    2, 3, 2, 7, 2, 5, 2, 3, 2, 19, 2, 163, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 17, 2, 27431, 2, 3, 2, 11,
    2, 47, 2, 3, 2, 13, 2, 5, 2, 3, 2, 89, 2, 151,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 4003, 2, 8427467, 2, 3,
    2, 37, 2, 7, 2, 3, 2, 1061, 2, 5, 2, 3, 2, 271,
    2, 11, 2, 3, 2, 5, 2, 61, 2, 3, 2, 59, 2, 3203,
    2, 3, 2, 7, 2, 17, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 103, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2, 13,
    2, 229529, 2, 3, 2, 199, 2, 23, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 7, 2, 37, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 239, 2, 7, 2, 3, 2, 84947, 2, 211, 2, 3, 2, 10663,
    2, 5, 2, 3, 2, 11, 2, 19, 2, 3, 2, 5, 2, 347,
    2, 3, 2, 7, 2, 494181269, 2, 3, 2, 139, 2, 227, 2, 3,
    2, 353, 2, 5, 2, 3, 2, 13, 2, 17, 2, 3, 2, 5,
    2, 43, 2, 3, 2, 29, 2, 11, 2, 3, 2, 7057, 2, 41,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 523, 2, 409, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 31, 2, 7907, 2, 3, 2, 19,
    2, 2165057, 2, 3, 2, 83, 2, 5, 2, 3, 2, 5639, 2, 127,
    2, 3, 2, 5, 2, 23, 2, 3, 2, 167, 2, 71, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 107, 2, 5, 2, 3, 2, 37,
    2, 334261117, 2, 3, 2, 5, 2, 331, 2, 3, 2, 11, 2, 13,
    2, 3, 2, 7, 2, 2473, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 109, 2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 61,
    2, 113, 2, 3, 2, 17, 2, 67, 2, 3, 2, 53, 2, 5,
    2, 3, 2, 7, 2, 73291, 2, 3, 2, 5, 2, 79, 2, 3,
    2, 19, 2, 7, 2, 3, 2, 11, 2, 229, 2, 3, 2, 3137,
    2, 5, 2, 3, 2, 43, 2, 13, 2, 3, 2, 5, 2, 13997,
    2, 3, 2, 7, 2, 375311, 2, 3, 2, 1699, 2, 19, 2, 3,
    2, 128431, 2, 5, 2, 3, 2, 4027, 2, 11, 2, 3, 2, 5,
    2, 547, 2, 3, 2, 1429, 2, 317, 2, 3, 2, 31, 2, 97,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 342165911, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 23, 2, 61, 2, 3, 2, 664667,
    2, 13, 2, 3, 2, 5147, 2, 5, 2, 3, 2, 18371, 2, 101,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 499, 2, 73, 2, 3,
    2, 1579, 2, 7, 2, 3, 2, 2282089, 2, 5, 2, 3, 2, 11,
    2, 29, 2, 3, 2, 5, 2, 17, 2, 3, 2, 13, 2, 19,
    2, 3, 2, 7, 2, 467, 2, 3, 2, 293, 2, 5, 2, 3,
    2, 2663, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 17,
    2, 11, 2, 3, 2, 41, 2, 743, 2, 3, 2, 257, 2, 5,
    2, 3, 2, 7, 2, 31371979, 2, 3, 2, 5, 2, 30937, 2, 3,
    2, 2039, 2, 7, 2, 3, 2, 53719, 2, 401, 2, 3, 2, 89,
    2, 5, 2, 3, 2, 13, 2, 52981, 2, 3, 2, 5, 2, 2707,
    2, 3, 2, 7, 2, 47, 2, 3, 2, 67, 2, 11, 2, 3,
    2, 31, 2, 5, 2, 3, 2, 4591, 2, 271, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 11, 2, 9337, 2, 3, 2, 43, 2, 691,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 2671, 2, 223, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 53, 2, 307, 2, 3, 2, 13,
    2, 2729, 2, 3, 2, 79, 2, 5, 2, 3, 2, 60851303, 2, 23,
    2, 3, 2, 5, 2, 769, 2, 3, 2, 4759, 2, 13, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 149,
    2, 17, 2, 3, 2, 5, 2, 607, 2, 3, 2, 2459, 2, 43,
    2, 3, 2, 7, 2, 179, 2, 3, 2, 29, 2, 5, 2, 3,
    2, 152992811, 2, 7, 2, 3, 2, 5, 2, 6269233, 2, 3, 2, 83,
    2, 3373, 2, 3, 2, 34259, 2, 5288557, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 7, 2, 13, 2, 3, 2, 5, 2, 433, 2, 3,
    2, 2213, 2, 7, 2, 3, 2, 61019369, 2, 13399, 2, 3, 2, 41,
    2, 5, 2, 3, 2, 31, 2, 9749, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 17, 2, 3, 2, 19, 2, 23, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 11, 2, 79, 2, 3, 2, 5,
    2, 8641, 2, 3, 2, 71, 2, 883, 2, 3, 2, 17, 2, 13,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 2749, 2, 31, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 347, 2, 11, 2, 3, 2, 461,
    2, 3407, 2, 3, 2, 491, 2, 5, 2, 3, 2, 2089, 2, 643,
    2, 3, 2, 5, 2, 112061, 2, 3, 2, 13, 2, 251, 2, 3,
    2, 29, 2, 7, 2, 3, 2, 232901, 2, 5, 2, 3, 2, 3517,
    2, 73, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 103,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 1537469, 2, 5, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 5, 2, 23, 2, 3, 2, 11,
    2, 3191, 2, 3, 2, 2693, 2, 19, 2, 3, 2, 109, 2, 5,
    2, 3, 2, 7, 2, 43, 2, 3, 2, 5, 2, 1123, 2, 3,
    2, 113371, 2, 7, 2, 3, 2, 197, 2, 163, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 67, 2, 97, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 7, 2, 29, 2, 3, 2, 11, 2, 37, 2, 3,
    2, 1601, 2, 5, 2, 3, 2, 41, 2, 66754141, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 17, 2, 306587, 2, 3, 2, 13, 2, 359,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 823, 2, 11, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 29, 2, 13, 2, 3, 2, 179,
    2, 30271, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13537, 2, 337697,
    2, 3, 2, 5, 2, 239, 2, 3, 2, 20269, 2, 419, 2, 3,
    2, 89, 2, 7, 2, 3, 2, 1871, 2, 5, 2, 3, 2, 3911,
    2, 313, 2, 3, 2, 5, 2, 11, 2, 3, 2, 23, 2, 67,
    2, 3, 2, 7, 2, 9137, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 5, 2, 47, 2, 3, 2, 31,
    2, 48163, 2, 3, 2, 37, 2, 19421, 2, 3, 2, 157, 2, 5,
    2, 3, 2, 7, 2, 53, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 588941, 2, 7, 2, 3, 2, 181, 2, 315527, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 1926851, 2, 17, 2, 3, 2, 5, 2, 4231,
    2, 3, 2, 7, 2, 23, 2, 3, 2, 113, 2, 13, 2, 3,
    2, 977, 2, 5, 2, 3, 2, 83, 2, 37, 2, 3, 2, 5,
    2, 2347, 2, 3, 2, 47, 2, 379, 2, 3, 2, 71, 2, 11,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 23, 2]

/-- A002386 row: the prime after 305405826521087869 is 305405826521087869 + 1272. -/
theorem gap_305405826521087869 : IsGapAt 305405826521087869 1272 :=
  isGapAt_of 305405826521087869 1272 (p305405826521087869) (by show Nat.Prime 305405826521089141; exact p305405826521089141) ds_305405826521087869 (by decide +kernel)

def ds_352521223451364323 : List ℕ := [
    2, 5, 2, 3, 2, 33599, 2, 7, 2, 3, 2, 5, 2, 2937791,
    2, 3, 2, 11, 2, 1321, 2, 3, 2, 9941, 2, 260005279, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 7, 2, 751, 2, 3, 2, 5,
    2, 87103987, 2, 3, 2, 29, 2, 7, 2, 3, 2, 277, 2, 487,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 47, 2, 19, 2, 3,
    2, 5, 2, 251, 2, 3, 2, 7, 2, 5082059, 2, 3, 2, 11,
    2, 13, 2, 3, 2, 173, 2, 5, 2, 3, 2, 43, 2, 17,
    2, 3, 2, 5, 2, 587, 2, 3, 2, 193, 2, 199, 2, 3,
    2, 541, 2, 73, 2, 3, 2, 7, 2, 5, 2, 3, 2, 321739417,
    2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 167,
    2, 3, 2, 19, 2, 269, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 593, 2, 1257749, 2, 3, 2, 5, 2, 13, 2, 3, 2, 23,
    2, 263, 2, 3, 2, 535093483, 2, 7, 2, 3, 2, 76920071, 2, 5,
    2, 3, 2, 61, 2, 4344467, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 19259, 2, 17, 2, 3, 2, 7, 2, 907, 2, 3, 2, 113,
    2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 2843,
    2, 3, 2, 983, 2, 557, 2, 3, 2, 17, 2, 1487, 2, 3,
    2, 211, 2, 5, 2, 3, 2, 7, 2, 83, 2, 3, 2, 5,
    2, 47, 2, 3, 2, 19, 2, 7, 2, 3, 2, 67, 2, 809,
    2, 3, 2, 3541, 2, 5, 2, 3, 2, 317, 2, 1229, 2, 3,
    2, 5, 2, 19311967, 2, 3, 2, 7, 2, 315928397, 2, 3, 2, 13,
    2, 19, 2, 3, 2, 563, 2, 5, 2, 3, 2, 23, 2, 41,
    2, 3, 2, 5, 2, 191, 2, 3, 2, 417721, 2, 13, 2, 3,
    2, 79, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17,
    2, 29, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 157,
    2, 3, 2, 43, 2, 37, 2, 3, 2, 71, 2, 5, 2, 3,
    2, 110479, 2, 31, 2, 3, 2, 5, 2, 197, 2, 3, 2, 421,
    2, 137, 2, 3, 2, 1123, 2, 7, 2, 3, 2, 41, 2, 5,
    2, 3, 2, 29, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 73, 2, 19, 2, 3, 2, 7, 2, 1433, 2, 3, 2, 163,
    2, 5, 2, 3, 2, 156059, 2, 7, 2, 3, 2, 5, 2, 11423,
    2, 3, 2, 17, 2, 43, 2, 3, 2, 23, 2, 631, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5,
    2, 107, 2, 3, 2, 383, 2, 7, 2, 3, 2, 167, 2, 13,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 19, 2, 139, 2, 3,
    2, 5, 2, 193, 2, 3, 2, 7, 2, 379, 2, 3, 2, 37,
    2, 17, 2, 3, 2, 263077, 2, 5, 2, 3, 2, 13691, 2, 53,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 103, 2, 3,
    2, 853, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11,
    2, 23201, 2, 3, 2, 5, 2, 7, 2, 3, 2, 229, 2, 431,
    2, 3, 2, 9521, 2, 109, 2, 3, 2, 29, 2, 5, 2, 3,
    2, 251, 2, 37, 2, 3, 2, 5, 2, 87541, 2, 3, 2, 151,
    2, 11, 2, 3, 2, 3511, 2, 7, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 13, 2, 17, 2, 3, 2, 5, 2, 491, 2, 3,
    2, 2860577, 2, 1663, 2, 3, 2, 7, 2, 797, 2, 3, 2, 47,
    2, 5, 2, 3, 2, 41, 2, 7, 2, 3, 2, 5, 2, 71,
    2, 3, 2, 1201, 2, 1873, 2, 3, 2, 137, 2, 11, 2, 3,
    2, 19597, 2, 5, 2, 3, 2, 7, 2, 125638537, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 11, 2, 7, 2, 3, 2, 13, 2, 29,
    2, 3, 2, 1237, 2, 5, 2, 3, 2, 191, 2, 43, 2, 3,
    2, 5, 2, 118549, 2, 3, 2, 7, 2, 13, 2, 3, 2, 19,
    2, 569, 2, 3, 2, 23, 2, 5, 2, 3, 2, 37, 2, 204931,
    2, 3, 2, 5, 2, 503, 2, 3, 2, 14159, 2, 31, 2, 3,
    2, 11, 2, 83, 2, 3, 2, 7, 2, 5, 2, 3, 2, 659,
    2, 5519, 2, 3, 2, 5, 2, 7, 2, 3, 2, 197, 2, 337,
    2, 3, 2, 227, 2, 293, 2, 3, 2, 7649, 2, 5, 2, 3,
    2, 71, 2, 11, 2, 3, 2, 5, 2, 101117, 2, 3, 2, 79,
    2, 37, 2, 3, 2, 268381357, 2, 7, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 2591, 2, 47, 2, 3, 2, 5, 2, 1082989, 2, 3,
    2, 19, 2, 307, 2, 3, 2, 7, 2, 53, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 23, 2, 29, 2, 3, 2, 31, 2, 13, 2, 3,
    2, 43, 2, 5, 2, 3, 2, 7, 2, 2356127, 2, 3, 2, 5,
    2, 1823, 2, 3, 2, 113, 2, 7, 2, 3, 2, 19337537, 2, 4447,
    2, 3, 2, 1297, 2, 5, 2, 3, 2, 199, 2, 2741, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 7, 2, 11, 2, 3, 2, 121519093,
    2, 31, 2, 3, 2, 2287, 2, 5, 2, 3, 2, 1568153, 2, 653,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 17, 2, 23, 2, 3,
    2, 270239, 2, 43, 2, 3, 2, 7, 2, 5, 2, 3, 2, 51193,
    2, 1979, 2, 3, 2, 5, 2, 7, 2, 3, 2, 157, 2, 19,
    2, 3, 2, 5167, 2, 11, 2, 3, 2, 59, 2, 5, 2, 3,
    2, 13, 2, 209357, 2, 3, 2, 5, 2, 77976709, 2, 3, 2, 11,
    2, 110233, 2, 3, 2, 6637, 2, 7, 2, 3, 2, 347, 2, 5,
    2, 3, 2, 4049, 2, 1097, 2, 3, 2, 5, 2, 29, 2, 3,
    2, 89, 2, 61, 2, 3, 2, 7, 2, 41, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 127,
    2, 3, 2, 67, 2, 71, 2, 3, 2, 11, 2, 117833, 2, 3,
    2, 5839, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 3673, 2, 7, 2, 3, 2, 3162847, 2, 107,
    2, 3, 2, 283, 2, 5, 2, 3, 2, 2341, 2, 11, 2, 3,
    2, 5, 2, 114229, 2, 3, 2, 7, 2, 9907, 2, 3, 2, 23,
    2, 113539, 2, 3, 2, 11, 2, 5, 2, 3, 2, 1993, 2, 103,
    2, 3, 2, 5, 2, 53, 2, 3, 2, 29641, 2, 53117, 2, 3,
    2, 17681, 2, 16931, 2, 3, 2, 7, 2, 5, 2, 3, 2, 140717,
    2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 2109871, 2, 135786289,
    2, 3, 2, 47, 2, 541, 2, 3, 2, 1747, 2, 5, 2, 3,
    2, 11, 2, 19, 2, 3, 2, 5, 2, 43, 2, 3, 2, 241,
    2, 17, 2, 3, 2, 281, 2, 7, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 31, 2, 17987, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 787529, 2, 11, 2, 3, 2, 7, 2, 13, 2, 3, 2, 53,
    2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 3002899,
    2, 3, 2, 587, 2, 149, 2, 3, 2, 19, 2, 591301, 2, 3,
    2, 117499601, 2, 5, 2, 3, 2, 7, 2, 31, 2, 3, 2, 5,
    2, 199, 2, 3, 2, 13, 2, 7, 2, 3, 2, 919, 2, 11,
    2, 3, 2, 107, 2, 5, 2, 3, 2, 1157333, 2]

/-- A002386 row: the prime after 352521223451364323 is 352521223451364323 + 1328. -/
theorem gap_352521223451364323 : IsGapAt 352521223451364323 1328 :=
  isGapAt_of 352521223451364323 1328 (p352521223451364323) (by show Nat.Prime 352521223451365651; exact p352521223451365651) ds_352521223451364323 (by decide +kernel)

def ds_401429925999153707 : List ℕ := [
    2, 7, 2, 3, 2, 4283, 2, 5, 2, 3, 2, 37, 2, 47,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 211, 2, 11, 2, 3,
    2, 7, 2, 28287619, 2, 3, 2, 103, 2, 5, 2, 3, 2, 14461,
    2, 7, 2, 3, 2, 5, 2, 571, 2, 3, 2, 71, 2, 353,
    2, 3, 2, 17, 2, 41, 2, 3, 2, 512190439, 2, 5, 2, 3,
    2, 7, 2, 61, 2, 3, 2, 5, 2, 23, 2, 3, 2, 265805171,
    2, 7, 2, 3, 2, 67, 2, 11, 2, 3, 2, 422857871, 2, 5,
    2, 3, 2, 41263, 2, 553181, 2, 3, 2, 5, 2, 31, 2, 3,
    2, 7, 2, 14003203, 2, 3, 2, 107, 2, 281, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 563, 2, 427949, 2, 3, 2, 5, 2, 3457,
    2, 3, 2, 19, 2, 1147417, 2, 3, 2, 13, 2, 263, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 17, 2, 15919, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 1409, 2, 13, 2, 3, 2, 11, 2, 19,
    2, 3, 2, 3368171, 2, 5, 2, 3, 2, 1109, 2, 37951, 2, 3,
    2, 5, 2, 157, 2, 3, 2, 5743, 2, 190577, 2, 3, 2, 13147,
    2, 7, 2, 3, 2, 101963, 2, 5, 2, 3, 2, 223, 2, 11,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 31, 2, 73, 2, 3,
    2, 7, 2, 103, 2, 3, 2, 11, 2, 5, 2, 3, 2, 79,
    2, 7, 2, 3, 2, 5, 2, 8235209, 2, 3, 2, 17, 2, 29,
    2, 3, 2, 550679, 2, 52707749, 2, 3, 2, 49003, 2, 5, 2, 3,
    2, 7, 2, 97, 2, 3, 2, 5, 2, 11, 2, 3, 2, 101,
    2, 7, 2, 3, 2, 8599, 2, 197, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 11, 2, 59, 2, 3, 2, 5, 2, 125029, 2, 3,
    2, 7, 2, 43, 2, 3, 2, 163, 2, 13, 2, 3, 2, 26783,
    2, 5, 2, 3, 2, 52743599, 2, 523, 2, 3, 2, 5, 2, 90641,
    2, 3, 2, 5011, 2, 11, 2, 3, 2, 271, 2, 25609333, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 19, 2, 32869073, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 13, 2, 593, 2, 3, 2, 41, 2, 509,
    2, 3, 2, 53, 2, 5, 2, 3, 2, 23, 2, 1531, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 419, 2, 4219, 2, 3, 2, 31,
    2, 7, 2, 3, 2, 62753, 2, 5, 2, 3, 2, 59, 2, 17,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 11, 2, 211, 2, 3,
    2, 7, 2, 13222169, 2, 3, 2, 37, 2, 5, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 5, 2, 1722323, 2, 3, 2, 479, 2, 194017,
    2, 3, 2, 71, 2, 31, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 7, 2, 23, 2, 3, 2, 5, 2, 797, 2, 3, 2, 114593,
    2, 7, 2, 3, 2, 11, 2, 173, 2, 3, 2, 11733739, 2, 5,
    2, 3, 2, 1426343, 2, 19, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 7, 2, 17, 2, 3, 2, 13, 2, 7187, 2, 3, 2, 5762941,
    2, 5, 2, 3, 2, 3481229, 2, 11, 2, 3, 2, 5, 2, 1021,
    2, 3, 2, 22639, 2, 13, 2, 3, 2, 17, 2, 552843997, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 4253, 2, 43, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 20841211, 2, 518587, 2, 3, 2, 19, 2, 110359,
    2, 3, 2, 31, 2, 5, 2, 3, 2, 89, 2, 29, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 1371151, 2, 67, 2, 3, 2, 3881,
    2, 7, 2, 3, 2, 41, 2, 5, 2, 3, 2, 11, 2, 13,
    2, 3, 2, 5, 2, 28547, 2, 3, 2, 103, 2, 109, 2, 3,
    2, 7, 2, 1009, 2, 3, 2, 139, 2, 5, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 5, 2, 607, 2, 3, 2, 61, 2, 11,
    2, 3, 2, 219277, 2, 1842229, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 7, 2, 193, 2, 3, 2, 5, 2, 149, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 131, 2, 13, 2, 3, 2, 79, 2, 5,
    2, 3, 2, 83, 2, 70919, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 7, 2, 324763, 2, 3, 2, 2957, 2, 11, 2, 3, 2, 43,
    2, 5, 2, 3, 2, 107, 2, 71, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 11, 2, 6353, 2, 3, 2, 3019, 2, 2729, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 31, 2, 11328881, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 137, 2, 61, 2, 3, 2, 2879, 2, 613,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 293, 2, 36527, 2, 3,
    2, 5, 2, 379, 2, 3, 2, 3461, 2, 4729, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 29, 2, 5, 2, 3, 2, 13, 2, 31,
    2, 3, 2, 5, 2, 47, 2, 3, 2, 659, 2, 19, 2, 3,
    2, 7, 2, 151, 2, 3, 2, 17, 2, 5, 2, 3, 2, 41,
    2, 7, 2, 3, 2, 5, 2, 385210439, 2, 3, 2, 67, 2, 727,
    2, 3, 2, 37, 2, 271, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 7, 2, 683, 2, 3, 2, 5, 2, 2819, 2, 3, 2, 2572649,
    2, 7, 2, 3, 2, 13, 2, 3391, 2, 3, 2, 43163851, 2, 5,
    2, 3, 2, 19, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 1277, 2, 29, 2, 3, 2, 73,
    2, 5, 2, 3, 2, 11, 2, 37, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 18690247, 2, 27043, 2, 3, 2, 1321, 2, 337121, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 148483, 2, 2269, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 43, 2, 11, 2, 3, 2, 29, 2, 59,
    2, 3, 2, 375143077, 2, 5, 2, 3, 2, 53, 2, 13, 2, 3,
    2, 5, 2, 31, 2, 3, 2, 4639, 2, 17, 2, 3, 2, 61,
    2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 317, 2, 83,
    2, 3, 2, 5, 2, 2112919, 2, 3, 2, 312356381, 2, 28069, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3, 2, 23,
    2, 7, 2, 3, 2, 5, 2, 43, 2, 3, 2, 11, 2, 1129,
    2, 3, 2, 21669259, 2, 13, 2, 3, 2, 1399, 2, 5, 2, 3,
    2, 7, 2, 307, 2, 3, 2, 5, 2, 14685169, 2, 3, 2, 61543,
    2, 7, 2, 3, 2, 59, 2, 47, 2, 3, 2, 89, 2, 5,
    2, 3, 2, 8867, 2, 835607, 2, 3, 2, 5, 2, 113, 2, 3,
    2, 7, 2, 20499847, 2, 3, 2, 11, 2, 61, 2, 3, 2, 7069,
    2, 5, 2, 3, 2, 17, 2, 23, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 29, 2, 37, 2, 3, 2, 79, 2, 7477, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 22535041, 2, 11, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 299063, 2, 31, 2, 3, 2, 23, 2, 1447,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 53, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 97, 2, 87649, 2, 3, 2, 9551,
    2, 7, 2, 3, 2, 397, 2, 5, 2, 3, 2, 43, 2, 25153993,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 17, 2, 2297, 2, 3,
    2, 7, 2, 41, 2, 3, 2, 67, 2, 5, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 5, 2, 29, 2, 3, 2, 313, 2, 18773,
    2, 3, 2, 13, 2, 19, 2, 3, 2, 3229, 2, 5, 2, 3,
    2, 7, 2, 1831, 2, 3, 2, 5, 2, 15814781, 2, 3, 2, 37,
    2, 7, 2, 3, 2, 31, 2, 17, 2, 3, 2]

/-- A002386 row: the prime after 401429925999153707 is 401429925999153707 + 1356. -/
theorem gap_401429925999153707 : IsGapAt 401429925999153707 1356 :=
  isGapAt_of 401429925999153707 1356 (p401429925999153707) (by show Nat.Prime 401429925999155063; exact p401429925999155063) ds_401429925999153707 (by decide +kernel)

def ds_418032645936712127 : List ℕ := [
    2, 115163, 2, 3, 2, 59, 2, 5, 2, 3, 2, 1381, 2, 971,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 146617, 2, 17, 2, 3,
    2, 13, 2, 199, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11,
    2, 97, 2, 3, 2, 5, 2, 7, 2, 3, 2, 149, 2, 13,
    2, 3, 2, 17, 2, 137, 2, 3, 2, 67399, 2, 5, 2, 3,
    2, 101, 2, 19, 2, 3, 2, 5, 2, 3457, 2, 3, 2, 1283,
    2, 11, 2, 3, 2, 37, 2, 7, 2, 3, 2, 2411, 2, 5,
    2, 3, 2, 701, 2, 16982299, 2, 3, 2, 5, 2, 29917, 2, 3,
    2, 23, 2, 53, 2, 3, 2, 7, 2, 16187, 2, 3, 2, 163,
    2, 5, 2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 157,
    2, 3, 2, 541, 2, 36137, 2, 3, 2, 19, 2, 11, 2, 3,
    2, 73, 2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5,
    2, 21317, 2, 3, 2, 11, 2, 7, 2, 3, 2, 631, 2, 41,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 4591, 2, 31, 2, 3,
    2, 5, 2, 69470881, 2, 3, 2, 7, 2, 23, 2, 3, 2, 43,
    2, 13, 2, 3, 2, 223, 2, 5, 2, 3, 2, 53, 2, 225529,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 1163, 2, 3313, 2, 3,
    2, 11, 2, 59, 2, 3, 2, 7, 2, 5, 2, 3, 2, 23,
    2, 28245397, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 237673,
    2, 3, 2, 547, 2, 106103, 2, 3, 2, 7229, 2, 5, 2, 3,
    2, 57587, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 417617,
    2, 43, 2, 3, 2, 349, 2, 7, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 37, 2, 577, 2, 3, 2, 5, 2, 25315781, 2, 3,
    2, 47, 2, 3907, 2, 3, 2, 7, 2, 17, 2, 3, 2, 137,
    2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 6148141, 2, 2141, 2, 3, 2, 59, 2, 174571, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 7, 2, 503, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 607, 2, 7, 2, 3, 2, 23, 2, 397,
    2, 3, 2, 127, 2, 5, 2, 3, 2, 79, 2, 107, 2, 3,
    2, 5, 2, 5021, 2, 3, 2, 7, 2, 11, 2, 3, 2, 13,
    2, 29, 2, 3, 2, 506629, 2, 5, 2, 3, 2, 97, 2, 17,
    2, 3, 2, 5, 2, 9007, 2, 3, 2, 71, 2, 13, 2, 3,
    2, 5659, 2, 163, 2, 3, 2, 7, 2, 5, 2, 3, 2, 3790543,
    2, 151871, 2, 3, 2, 5, 2, 7, 2, 3, 2, 7768601, 2, 67,
    2, 3, 2, 29, 2, 11, 2, 3, 2, 2081, 2, 5, 2, 3,
    2, 19, 2, 8677, 2, 3, 2, 5, 2, 419, 2, 3, 2, 11,
    2, 1171, 2, 3, 2, 41, 2, 7, 2, 3, 2, 93097, 2, 5,
    2, 3, 2, 10508299, 2, 13, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 37, 2, 17, 2, 3, 2, 7, 2, 251789, 2, 3, 2, 211,
    2, 5, 2, 3, 2, 8287, 2, 7, 2, 3, 2, 5, 2, 79,
    2, 3, 2, 7433, 2, 31, 2, 3, 2, 11, 2, 609157091, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 7, 2, 103, 2, 3, 2, 5,
    2, 439289, 2, 3, 2, 73, 2, 7, 2, 3, 2, 151, 2, 13,
    2, 3, 2, 19, 2, 5, 2, 3, 2, 307, 2, 11, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 7, 2, 97, 2, 3, 2, 617,
    2, 1809911, 2, 3, 2, 11, 2, 5, 2, 3, 2, 71597, 2, 19,
    2, 3, 2, 5, 2, 127, 2, 3, 2, 13, 2, 113, 2, 3,
    2, 8699, 2, 223, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17,
    2, 41, 2, 3, 2, 5, 2, 7, 2, 3, 2, 26297, 2, 7723,
    2, 3, 2, 31, 2, 116113, 2, 3, 2, 239, 2, 5, 2, 3,
    2, 11, 2, 271, 2, 3, 2, 5, 2, 61, 2, 3, 2, 59,
    2, 356642213, 2, 3, 2, 19, 2, 7, 2, 3, 2, 43, 2, 5,
    2, 3, 2, 13, 2, 61961, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 67, 2, 11, 2, 3, 2, 7, 2, 31, 2, 3, 2, 37,
    2, 5, 2, 3, 2, 463, 2, 7, 2, 3, 2, 5, 2, 29,
    2, 3, 2, 17, 2, 197, 2, 3, 2, 11813, 2, 12721, 2, 3,
    2, 317, 2, 5, 2, 3, 2, 7, 2, 47, 2, 3, 2, 5,
    2, 8647, 2, 3, 2, 23, 2, 7, 2, 3, 2, 13, 2, 11,
    2, 3, 2, 69941, 2, 5, 2, 3, 2, 3527, 2, 106787, 2, 3,
    2, 5, 2, 37, 2, 3, 2, 7, 2, 13, 2, 3, 2, 1777,
    2, 17, 2, 3, 2, 9648481, 2, 5, 2, 3, 2, 30119, 2, 515677,
    2, 3, 2, 5, 2, 357169, 2, 3, 2, 4153, 2, 811, 2, 3,
    2, 71, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3, 2, 113,
    2, 137, 2, 3, 2, 5, 2, 7, 2, 3, 2, 128450281, 2, 23,
    2, 3, 2, 11, 2, 151, 2, 3, 2, 3833069, 2, 5, 2, 3,
    2, 497411, 2, 13, 2, 3, 2, 5, 2, 41, 2, 3, 2, 532283,
    2, 9901, 2, 3, 2, 25482463, 2, 7, 2, 3, 2, 1048129, 2, 5,
    2, 3, 2, 23, 2, 11, 2, 3, 2, 5, 2, 59, 2, 3,
    2, 61, 2, 746531, 2, 3, 2, 7, 2, 719, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 709, 2, 7, 2, 3, 2, 5, 2, 1091,
    2, 3, 2, 43, 2, 19, 2, 3, 2, 150383, 2, 13, 2, 3,
    2, 103, 2, 5, 2, 3, 2, 7, 2, 279109, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 97, 2, 7, 2, 3, 2, 132383, 2, 2203,
    2, 3, 2, 612589489, 2, 5, 2, 3, 2, 11, 2, 23, 2, 3,
    2, 5, 2, 245502727, 2, 3, 2, 7, 2, 17, 2, 3, 2, 3391,
    2, 37, 2, 3, 2, 51503, 2, 5, 2, 3, 2, 19, 2, 227,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 18422249, 2, 11, 2, 3,
    2, 17, 2, 101, 2, 3, 2, 7, 2, 5, 2, 3, 2, 2377,
    2, 5452033, 2, 3, 2, 5, 2, 7, 2, 3, 2, 163, 2, 487,
    2, 3, 2, 4493, 2, 683, 2, 3, 2, 46411, 2, 5, 2, 3,
    2, 13, 2, 31, 2, 3, 2, 5, 2, 4373, 2, 3, 2, 83,
    2, 34543, 2, 3, 2, 7376849, 2, 7, 2, 3, 2, 67, 2, 5,
    2, 3, 2, 263, 2, 71, 2, 3, 2, 5, 2, 53353, 2, 3,
    2, 11, 2, 41, 2, 3, 2, 7, 2, 23, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 108457,
    2, 3, 2, 11897, 2, 3049, 2, 3, 2, 13, 2, 103, 2, 3,
    2, 1097, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3, 2, 5,
    2, 73897, 2, 3, 2, 509557, 2, 7, 2, 3, 2, 11, 2, 283,
    2, 3, 2, 277, 2, 5, 2, 3, 2, 43, 2, 9026449, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 7, 2, 12254189, 2, 3, 2, 107,
    2, 3137, 2, 3, 2, 447019, 2, 5, 2, 3, 2, 1277, 2, 11,
    2, 3, 2, 5, 2, 67, 2, 3, 2, 17, 2, 1031, 2, 3,
    2, 19, 2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2, 13907,
    2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 859751, 2, 434823047,
    2, 3, 2, 61, 2, 4139, 2, 3, 2, 9551, 2, 5, 2, 3,
    2, 251, 2, 113, 2, 3, 2, 5, 2, 11, 2, 3, 2, 84533,
    2, 599, 2, 3, 2, 29, 2, 7, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 11, 2, 547, 2, 3, 2, 5, 2]

/-- A002386 row: the prime after 418032645936712127 is 418032645936712127 + 1370. -/
theorem gap_418032645936712127 : IsGapAt 418032645936712127 1370 :=
  isGapAt_of 418032645936712127 1370 (p418032645936712127) (by show Nat.Prime 418032645936713497; exact p418032645936713497) ds_418032645936712127 (by decide +kernel)

def ds_804212830686677669 : List ℕ := [
    2, 7, 2, 3, 2, 5, 2, 701, 2, 3, 2, 100943, 2, 24537959,
    2, 3, 2, 11, 2, 28097, 2, 3, 2, 31, 2, 5, 2, 3,
    2, 7, 2, 152401693, 2, 3, 2, 5, 2, 503, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 3247961, 2, 785175763, 2, 3, 2, 47, 2, 5,
    2, 3, 2, 17, 2, 11, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 7, 2, 29, 2, 3, 2, 19, 2, 83, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 401, 2, 241, 2, 3, 2, 5, 2, 67,
    2, 3, 2, 121469, 2, 601, 2, 3, 2, 619, 2, 23099, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 13, 2, 977, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 29, 2, 23, 2, 3, 2, 113, 2, 305114041,
    2, 3, 2, 149, 2, 5, 2, 3, 2, 11, 2, 271, 2, 3,
    2, 5, 2, 967, 2, 3, 2, 17, 2, 53, 2, 3, 2, 115459,
    2, 7, 2, 3, 2, 229, 2, 5, 2, 3, 2, 23, 2, 73,
    2, 3, 2, 5, 2, 21589, 2, 3, 2, 19, 2, 11, 2, 3,
    2, 7, 2, 86861, 2, 3, 2, 1093, 2, 5, 2, 3, 2, 31,
    2, 7, 2, 3, 2, 5, 2, 251, 2, 3, 2, 139, 2, 13,
    2, 3, 2, 1061, 2, 17, 2, 3, 2, 127, 2, 5, 2, 3,
    2, 7, 2, 47, 2, 3, 2, 5, 2, 29, 2, 3, 2, 1901,
    2, 7, 2, 3, 2, 1873, 2, 11, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 53, 2, 23, 2, 3, 2, 5, 2, 26641, 2, 3,
    2, 7, 2, 673583513, 2, 3, 2, 593, 2, 25736771, 2, 3, 2, 541683091,
    2, 5, 2, 3, 2, 522881, 2, 13, 2, 3, 2, 5, 2, 13711,
    2, 3, 2, 89, 2, 257, 2, 3, 2, 23, 2, 4513, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 313, 2, 17, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 314779, 2, 19, 2, 3, 2, 11, 2, 541,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 663007, 2, 479, 2, 3,
    2, 5, 2, 16901, 2, 3, 2, 293, 2, 307, 2, 3, 2, 43,
    2, 7, 2, 3, 2, 4157, 2, 5, 2, 3, 2, 59, 2, 11,
    2, 3, 2, 5, 2, 347, 2, 3, 2, 2309, 2, 488239, 2, 3,
    2, 7, 2, 23, 2, 3, 2, 11, 2, 5, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 5, 2, 281, 2, 3, 2, 13, 2, 17,
    2, 3, 2, 263, 2, 131, 2, 3, 2, 97, 2, 5, 2, 3,
    2, 7, 2, 101533, 2, 3, 2, 5, 2, 11, 2, 3, 2, 27059,
    2, 7, 2, 3, 2, 17, 2, 41, 2, 3, 2, 73, 2, 5,
    2, 3, 2, 11, 2, 53, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 7, 2, 1531, 2, 3, 2, 21407, 2, 67, 2, 3, 2, 21871,
    2, 5, 2, 3, 2, 13, 2, 61, 2, 3, 2, 5, 2, 228353,
    2, 3, 2, 1663, 2, 11, 2, 3, 2, 17987, 2, 455503507, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 714869, 2, 103, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 41, 2, 23339, 2, 3, 2, 101, 2, 677,
    2, 3, 2, 823, 2, 5, 2, 3, 2, 17, 2, 19, 2, 3,
    2, 5, 2, 83, 2, 3, 2, 31, 2, 18188341, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 439, 2, 683,
    2, 3, 2, 5, 2, 1913, 2, 3, 2, 11, 2, 13, 2, 3,
    2, 7, 2, 71, 2, 3, 2, 3605741, 2, 5, 2, 3, 2, 349,
    2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 661, 2, 31,
    2, 3, 2, 19, 2, 331, 2, 3, 2, 29, 2, 5, 2, 3,
    2, 7, 2, 218212513, 2, 3, 2, 5, 2, 89, 2, 3, 2, 17,
    2, 7, 2, 3, 2, 11, 2, 501209, 2, 3, 2, 792991, 2, 5,
    2, 3, 2, 147919, 2, 13, 2, 3, 2, 5, 2, 167, 2, 3,
    2, 7, 2, 2029991, 2, 3, 2, 2437, 2, 37, 2, 3, 2, 78575249,
    2, 5, 2, 3, 2, 251, 2, 11, 2, 3, 2, 5, 2, 877,
    2, 3, 2, 23, 2, 109, 2, 3, 2, 107, 2, 17, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 79, 2, 5801, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 19, 2, 704309, 2, 3, 2, 31, 2, 13,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 215443, 2, 233, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 383, 2, 406271, 2, 3, 2, 41,
    2, 7, 2, 3, 2, 971, 2, 5, 2, 3, 2, 11, 2, 613,
    2, 3, 2, 5, 2, 431, 2, 3, 2, 13, 2, 23, 2, 3,
    2, 7, 2, 31, 2, 3, 2, 2795381, 2, 5, 2, 3, 2, 51361,
    2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 269, 2, 11,
    2, 3, 2, 37, 2, 599, 2, 3, 2, 49169, 2, 5, 2, 3,
    2, 7, 2, 1213, 2, 3, 2, 5, 2, 61, 2, 3, 2, 3851599,
    2, 7, 2, 3, 2, 667919207, 2, 499, 2, 3, 2, 43, 2, 5,
    2, 3, 2, 13, 2, 67, 2, 3, 2, 5, 2, 79, 2, 3,
    2, 7, 2, 19, 2, 3, 2, 18076181, 2, 11, 2, 3, 2, 359,
    2, 5, 2, 3, 2, 653, 2, 37, 2, 3, 2, 5, 2, 7753,
    2, 3, 2, 11, 2, 17, 2, 3, 2, 198073, 2, 857, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 1249, 2, 23, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 104791133, 2, 11743, 2, 3, 2, 13, 2, 43,
    2, 3, 2, 7577, 2, 5, 2, 3, 2, 19, 2, 1746761, 2, 3,
    2, 5, 2, 947, 2, 3, 2, 29, 2, 13, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 523252493, 2, 5, 2, 3, 2, 99989, 2, 197,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 167, 2, 9341, 2, 3,
    2, 7, 2, 1657277, 2, 3, 2, 41, 2, 5, 2, 3, 2, 41389,
    2, 7, 2, 3, 2, 5, 2, 73, 2, 3, 2, 19913, 2, 5827,
    2, 3, 2, 9133, 2, 30187, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 5, 2, 47, 2, 3, 2, 347,
    2, 7, 2, 3, 2, 59, 2, 23, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 1193, 2, 929, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 7, 2, 193, 2, 3, 2, 29587, 2, 1723, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 11, 2, 19, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 43, 2, 37, 2, 3, 2, 1579, 2, 13, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 67, 2, 491, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 17, 2, 11, 2, 3, 2, 71, 2, 7673,
    2, 3, 2, 5119, 2, 5, 2, 3, 2, 317, 2, 31, 2, 3,
    2, 5, 2, 41, 2, 3, 2, 13, 2, 102061, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 53, 2, 5, 2, 3, 2, 2570903, 2, 379,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 83, 2, 61, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 173, 2, 5, 2, 3, 2, 199409459,
    2, 7, 2, 3, 2, 5, 2, 113, 2, 3, 2, 11, 2, 2731,
    2, 3, 2, 1319, 2, 1517819, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 7, 2, 29, 2, 3, 2, 5, 2, 151027057, 2, 3, 2, 37,
    2, 7, 2, 3, 2, 1201, 2, 448421, 2, 3, 2, 202777, 2, 5,
    2, 3, 2, 199, 2, 1549, 2, 3, 2, 5, 2, 349, 2, 3,
    2, 7, 2, 59, 2, 3, 2, 11, 2, 3259, 2, 3, 2, 179,
    2, 5, 2, 3, 2, 29, 2, 17, 2, 3, 2, 5, 2, 10607,
    2, 3, 2, 128281213, 2, 6637, 2, 3, 2, 13, 2, 19, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 89, 2, 11, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 26141, 2, 13, 2, 3, 2, 3617281, 2, 502277,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 43, 2, 1109, 2, 3,
    2, 5, 2, 45319, 2, 3, 2, 23, 2, 609307, 2, 3, 2, 751,
    2, 7, 2, 3, 2, 509, 2, 5, 2, 3, 2, 214561, 2]

/-- A002386 row: the prime after 804212830686677669 is 804212830686677669 + 1442. -/
theorem gap_804212830686677669 : IsGapAt 804212830686677669 1442 :=
  isGapAt_of 804212830686677669 1442 (p804212830686677669) (by show Nat.Prime 804212830686679111; exact p804212830686679111) ds_804212830686677669 (by decide +kernel)

def ds_1425172824437699411 : List ℕ := [
    2, 17, 2, 3, 2, 79, 2, 269, 2, 3, 2, 37019, 2, 5,
    2, 3, 2, 27065459, 2, 769, 2, 3, 2, 5, 2, 2273, 2, 3,
    2, 13, 2, 3187, 2, 3, 2, 11, 2, 7, 2, 3, 2, 661,
    2, 5, 2, 3, 2, 107, 2, 73, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 181, 2, 4993, 2, 3, 2, 7, 2, 1567, 2, 3,
    2, 993253, 2, 5, 2, 3, 2, 787, 2, 7, 2, 3, 2, 5,
    2, 53, 2, 3, 2, 311, 2, 29, 2, 3, 2, 9168407, 2, 47,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 2776183, 2, 3,
    2, 5, 2, 139, 2, 3, 2, 211, 2, 7, 2, 3, 2, 83,
    2, 101, 2, 3, 2, 1433, 2, 5, 2, 3, 2, 17, 2, 122250157,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 8673107, 2, 3,
    2, 449, 2, 67, 2, 3, 2, 5527, 2, 5, 2, 3, 2, 11,
    2, 523, 2, 3, 2, 5, 2, 37, 2, 3, 2, 71, 2, 116447,
    2, 3, 2, 13, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 113383, 2, 2251, 2, 3, 2, 5, 2, 7, 2, 3, 2, 531359,
    2, 11, 2, 3, 2, 43, 2, 251, 2, 3, 2, 169243, 2, 5,
    2, 3, 2, 281, 2, 97, 2, 3, 2, 5, 2, 7130407, 2, 3,
    2, 17, 2, 114889, 2, 3, 2, 24023, 2, 7, 2, 3, 2, 1999631,
    2, 5, 2, 3, 2, 109, 2, 23, 2, 3, 2, 5, 2, 29,
    2, 3, 2, 31, 2, 657147307, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 437279, 2, 5, 2, 3, 2, 3347471, 2, 7, 2, 3, 2, 5,
    2, 476975971, 2, 3, 2, 11, 2, 19, 2, 3, 2, 23, 2, 17,
    2, 3, 2, 16747, 2, 5, 2, 3, 2, 7, 2, 68957909, 2, 3,
    2, 5, 2, 89391721, 2, 3, 2, 101, 2, 7, 2, 3, 2, 547,
    2, 258112223, 2, 3, 2, 13, 2, 5, 2, 3, 2, 508547617, 2, 59,
    2, 3, 2, 5, 2, 31437613, 2, 3, 2, 7, 2, 61, 2, 3,
    2, 11, 2, 13, 2, 3, 2, 647, 2, 5, 2, 3, 2, 19,
    2, 47, 2, 3, 2, 5, 2, 28591, 2, 3, 2, 229551227, 2, 29399,
    2, 3, 2, 47843, 2, 23, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 10238791, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13,
    2, 181, 2, 3, 2, 67, 2, 239, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 5431, 2, 29, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 9533, 2, 605609, 2, 3, 2, 31, 2, 7, 2, 3, 2, 428873,
    2, 5, 2, 3, 2, 59, 2, 151, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 79, 2, 18127, 2, 3, 2, 7, 2, 73, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5,
    2, 47933, 2, 3, 2, 53, 2, 17, 2, 3, 2, 3623, 2, 31,
    2, 3, 2, 41, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 54078419, 2, 7, 2, 3, 2, 17,
    2, 3805721, 2, 3, 2, 2777, 2, 5, 2, 3, 2, 3347, 2, 43,
    2, 3, 2, 5, 2, 11895823, 2, 3, 2, 7, 2, 6477203, 2, 3,
    2, 13, 2, 555829, 2, 3, 2, 23, 2, 5, 2, 3, 2, 193,
    2, 283, 2, 3, 2, 5, 2, 796871, 2, 3, 2, 383, 2, 13,
    2, 3, 2, 19, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 97, 2, 37, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11,
    2, 89, 2, 3, 2, 9869179, 2, 79, 2, 3, 2, 31, 2, 5,
    2, 3, 2, 17, 2, 179, 2, 3, 2, 5, 2, 197, 2, 3,
    2, 149, 2, 47, 2, 3, 2, 241, 2, 7, 2, 3, 2, 29,
    2, 5, 2, 3, 2, 503, 2, 13, 2, 3, 2, 5, 2, 41,
    2, 3, 2, 107, 2, 81199, 2, 3, 2, 7, 2, 431, 2, 3,
    2, 307, 2, 5, 2, 3, 2, 3701, 2, 7, 2, 3, 2, 5,
    2, 17, 2, 3, 2, 19, 2, 53, 2, 3, 2, 577, 2, 61,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 5, 2, 122448839, 2, 3, 2, 17, 2, 7, 2, 3, 2, 47,
    2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 37, 2, 182641,
    2, 3, 2, 5, 2, 2797, 2, 3, 2, 7, 2, 443, 2, 3,
    2, 8093, 2, 29, 2, 3, 2, 14083, 2, 5, 2, 3, 2, 1051,
    2, 2903569, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13, 2, 23,
    2, 3, 2, 70373, 2, 17, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 11, 2, 199, 2, 3, 2, 5, 2, 7, 2, 3, 2, 1693,
    2, 37, 2, 3, 2, 29, 2, 3272879, 2, 3, 2, 17, 2, 5,
    2, 3, 2, 23, 2, 641, 2, 3, 2, 5, 2, 337, 2, 3,
    2, 263, 2, 11, 2, 3, 2, 475681, 2, 7, 2, 3, 2, 2475089,
    2, 5, 2, 3, 2, 13, 2, 31, 2, 3, 2, 5, 2, 64811,
    2, 3, 2, 107201, 2, 919, 2, 3, 2, 7, 2, 1571, 2, 3,
    2, 109, 2, 5, 2, 3, 2, 463, 2, 7, 2, 3, 2, 5,
    2, 73, 2, 3, 2, 56209, 2, 41, 2, 3, 2, 101, 2, 11,
    2, 3, 2, 32569, 2, 5, 2, 3, 2, 7, 2, 23, 2, 3,
    2, 5, 2, 83, 2, 3, 2, 11, 2, 7, 2, 3, 2, 13,
    2, 510707, 2, 3, 2, 61, 2, 5, 2, 3, 2, 173099, 2, 113,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 23, 2, 293, 2, 3, 2, 2679401, 2, 5, 2, 3, 2, 137,
    2, 41183, 2, 3, 2, 5, 2, 173, 2, 3, 2, 29, 2, 17,
    2, 3, 2, 11, 2, 739, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 47, 2, 53, 2, 3, 2, 5, 2, 7, 2, 3, 2, 197,
    2, 2711, 2, 3, 2, 17, 2, 59, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 257, 2, 11, 2, 3, 2, 5, 2, 31, 2, 3,
    2, 977, 2, 197927, 2, 3, 2, 40459499, 2, 7, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 756919, 2, 19, 2, 3, 2, 5, 2, 331,
    2, 3, 2, 844999, 2, 79, 2, 3, 2, 7, 2, 107, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 157, 2, 7, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 118043, 2, 7069, 2, 3, 2, 53, 2, 13,
    2, 3, 2, 103, 2, 5, 2, 3, 2, 7, 2, 677, 2, 3,
    2, 5, 2, 89, 2, 3, 2, 2371801, 2, 7, 2, 3, 2, 19,
    2, 41, 2, 3, 2, 3329, 2, 5, 2, 3, 2, 233, 2, 271,
    2, 3, 2, 5, 2, 90067, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 113, 2, 2687, 2, 3, 2, 37, 2, 5, 2, 3, 2, 73,
    2, 373, 2, 3, 2, 5, 2, 13, 2, 3, 2, 67, 2, 38851,
    2, 3, 2, 2027, 2, 457, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 43, 2, 2819, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17,
    2, 31, 2, 3, 2, 66533, 2, 11, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 13, 2, 5087, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 11, 2, 3313, 2, 3, 2, 163, 2, 7, 2, 3, 2, 6263,
    2, 5, 2, 3, 2, 4003, 2, 29, 2, 3, 2, 5, 2, 71,
    2, 3, 2, 47, 2, 1808887, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 107, 2, 5, 2, 3, 2, 61, 2, 7, 2, 3, 2, 5,
    2, 131, 2, 3, 2, 165553, 2, 281, 2, 3, 2, 11, 2, 53,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 7, 2, 7121, 2, 3,
    2, 5, 2, 151, 2, 3, 2, 15541, 2, 7, 2, 3, 2, 31,
    2, 563, 2, 3, 2, 223, 2, 5, 2, 3, 2, 244639, 2, 11,
    2, 3, 2, 5, 2, 409, 2, 3, 2, 7, 2, 59, 2, 3,
    2, 349279013, 2, 167, 2, 3, 2, 11, 2, 5, 2, 3, 2, 79,
    2, 17, 2, 3, 2, 5, 2, 3907, 2, 3, 2, 149211191, 2, 19,
    2, 3, 2, 865102109, 2, 31, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 71, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 1675759,
    2, 30689, 2, 3, 2]

/-- A002386 row: the prime after 1425172824437699411 is 1425172824437699411 + 1476. -/
theorem gap_1425172824437699411 : IsGapAt 1425172824437699411 1476 :=
  isGapAt_of 1425172824437699411 1476 (p1425172824437699411) (by show Nat.Prime 1425172824437700887; exact p1425172824437700887) ds_1425172824437699411 (by decide +kernel)

end LeanLab.Verifications.Top50.Gaps3
