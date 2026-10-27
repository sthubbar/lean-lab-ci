/-
Maximal prime gap records, OEIS A002386 part 1: each row `IsGapAt p g`, zero sorry.
Divisors and Pratt certificates found by Python, checked by the Lean kernel.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.GapsBase

namespace LeanLab.Verifications.Top50.Gaps1

open LeanLab.Verifications.Top50.Gaps
open LeanLab.Verifications.Pratt (pB)

theorem p17051707 : Nat.Prime 17051707 := by
  refine Pratt.pratt 17051707 2 [(2, 1), (3, 2), (7, 2), (19333, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p17051887 : Nat.Prime 17051887 := by
  refine Pratt.pratt 17051887 5 [(2, 1), (3, 2), (947327, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p20831323 : Nat.Prime 20831323 := by
  refine Pratt.pratt 20831323 2 [(2, 1), (3, 1), (223, 1), (15569, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p20831533 : Nat.Prime 20831533 := by
  refine Pratt.pratt 20831533 2 [(2, 2), (3, 1), (1735961, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p47326693 : Nat.Prime 47326693 := by
  refine Pratt.pratt 47326693 2 [(2, 2), (3, 1), (7, 1), (563413, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p47326913 : Nat.Prime 47326913 := by
  refine Pratt.pratt 47326913 3 [(2, 6), (17, 1), (43499, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p122164747 : Nat.Prime 122164747 := by
  refine Pratt.pratt 122164747 3 [(2, 1), (3, 1), (11, 2), (191, 1), (881, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p122164969 : Nat.Prime 122164969 := by
  refine Pratt.pratt 122164969 7 [(2, 3), (3, 1), (79, 1), (64433, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p189695659 : Nat.Prime 189695659 := by
  refine Pratt.pratt 189695659 2 [(2, 1), (3, 1), (19, 1), (1663997, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p189695893 : Nat.Prime 189695893 := by
  refine Pratt.pratt 189695893 2 [(2, 2), (3, 1), (37, 1), (427243, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p191912783 : Nat.Prime 191912783 := by
  refine Pratt.pratt 191912783 5 [(2, 1), (23, 1), (653, 1), (6389, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p191913031 : Nat.Prime 191913031 := by
  refine Pratt.pratt 191913031 3 [(2, 1), (3, 3), (5, 1), (109, 1), (6521, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p387096133 : Nat.Prime 387096133 := by
  refine Pratt.pratt 387096133 23 [(2, 2), (3, 1), (31, 1), (1040581, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p193548191 : Nat.Prime 193548191 := by
  refine Pratt.pratt 193548191 7 [(2, 1), (5, 1), (11, 1), (31, 1), (211, 1), (269, 1)] (by norm_num)
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

theorem p387096383 : Nat.Prime 387096383 := by
  refine Pratt.pratt 387096383 5 [(2, 1), (193548191, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p193548191

theorem p436273009 : Nat.Prime 436273009 := by
  refine Pratt.pratt 436273009 11 [(2, 4), (3, 1), (9089021, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p436273291 : Nat.Prime 436273291 := by
  refine Pratt.pratt 436273291 2 [(2, 1), (3, 4), (5, 1), (37, 1), (14557, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p1294268491 : Nat.Prime 1294268491 := by
  refine Pratt.pratt 1294268491 2 [(2, 1), (3, 3), (5, 1), (4793587, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p1294268779 : Nat.Prime 1294268779 := by
  refine Pratt.pratt 1294268779 2 [(2, 1), (3, 2), (11, 1), (113, 1), (57847, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p1453168141 : Nat.Prime 1453168141 := by
  refine Pratt.pratt 1453168141 2 [(2, 2), (3, 1), (5, 1), (2837, 1), (8537, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p1453168433 : Nat.Prime 1453168433 := by
  refine Pratt.pratt 1453168433 3 [(2, 4), (17, 1), (151, 1), (35381, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p575235637 : Nat.Prime 575235637 := by
  refine Pratt.pratt 575235637 2 [(2, 2), (3, 1), (103, 1), (223, 1), (2087, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p2300942549 : Nat.Prime 2300942549 := by
  refine Pratt.pratt 2300942549 2 [(2, 2), (575235637, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p575235637

theorem p27392177 : Nat.Prime 27392177 := by
  refine Pratt.pratt 27392177 3 [(2, 4), (7, 2), (34939, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p2300942869 : Nat.Prime 2300942869 := by
  refine Pratt.pratt 2300942869 6 [(2, 2), (3, 1), (7, 1), (27392177, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p27392177

theorem p3842610773 : Nat.Prime 3842610773 := by
  refine Pratt.pratt 3842610773 2 [(2, 2), (7, 2), (11, 1), (13, 1), (47, 1), (2917, 1)] (by norm_num)
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

theorem p137236111 : Nat.Prime 137236111 := by
  refine Pratt.pratt 137236111 15 [(2, 1), (3, 1), (5, 1), (11, 1), (197, 1), (2111, 1)] (by norm_num)
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

theorem p3842611109 : Nat.Prime 3842611109 := by
  refine Pratt.pratt 3842611109 2 [(2, 2), (7, 1), (137236111, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p137236111

theorem p239022631 : Nat.Prime 239022631 := by
  refine Pratt.pratt 239022631 7 [(2, 1), (3, 3), (5, 1), (7, 1), (11, 1), (11497, 1)] (by norm_num)
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

theorem p4302407359 : Nat.Prime 4302407359 := by
  refine Pratt.pratt 4302407359 3 [(2, 1), (3, 2), (239022631, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p239022631

theorem p4302407713 : Nat.Prime 4302407713 := by
  refine Pratt.pratt 4302407713 5 [(2, 5), (3, 1), (53, 1), (845599, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p38038669 : Nat.Prime 38038669 := by
  refine Pratt.pratt 38038669 2 [(2, 2), (3, 1), (3169889, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p10726904659 : Nat.Prime 10726904659 := by
  refine Pratt.pratt 10726904659 2 [(2, 1), (3, 1), (47, 1), (38038669, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p38038669

theorem p16760789 : Nat.Prime 16760789 := by
  refine Pratt.pratt 16760789 2 [(2, 2), (11, 1), (167, 1), (2281, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p134086313 : Nat.Prime 134086313 := by
  refine Pratt.pratt 134086313 3 [(2, 3), (16760789, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p16760789

theorem p10726905041 : Nat.Prime 10726905041 := by
  refine Pratt.pratt 10726905041 3 [(2, 4), (5, 1), (134086313, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p134086313

theorem p20678048297 : Nat.Prime 20678048297 := by
  refine Pratt.pratt 20678048297 3 [(2, 3), (31, 1), (83, 1), (163, 1), (6163, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p20678048681 : Nat.Prime 20678048681 := by
  refine Pratt.pratt 20678048681 3 [(2, 3), (5, 1), (977, 1), (529121, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p22367084959 : Nat.Prime 22367084959 := by
  refine Pratt.pratt 22367084959 6 [(2, 1), (3, 3), (10091, 1), (41047, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p22367085353 : Nat.Prime 22367085353 := by
  refine Pratt.pratt 22367085353 3 [(2, 3), (953, 1), (2933773, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p25056082087 : Nat.Prime 25056082087 := by
  refine Pratt.pratt 25056082087 5 [(2, 1), (3, 1), (7, 4), (587, 1), (2963, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p48558299 : Nat.Prime 48558299 := by
  refine Pratt.pratt 48558299 2 [(2, 1), (59, 1), (79, 1), (5209, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p97116599 : Nat.Prime 97116599 := by
  refine Pratt.pratt 97116599 13 [(2, 1), (48558299, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p48558299

theorem p25056082543 : Nat.Prime 25056082543 := by
  refine Pratt.pratt 25056082543 3 [(2, 1), (3, 1), (43, 1), (97116599, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p97116599

theorem p11841371 : Nat.Prime 11841371 := by
  refine Pratt.pratt 11841371 2 [(2, 1), (5, 1), (19, 1), (62323, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p42652618343 : Nat.Prime 42652618343 := by
  refine Pratt.pratt 42652618343 5 [(2, 1), (1801, 1), (11841371, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p11841371

theorem p53449397 : Nat.Prime 53449397 := by
  refine Pratt.pratt 53449397 2 [(2, 2), (7, 2), (11, 1), (13, 1), (1907, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p42652618807 : Nat.Prime 42652618807 := by
  refine Pratt.pratt 42652618807 13 [(2, 1), (3, 1), (7, 1), (19, 1), (53449397, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p53449397

def ds_2 : List ℕ := []

/-- A002386 row: the prime after 2 is 2 + 1. -/
theorem gap_2 : IsGapAt 2 1 :=
  isGapAt_of 2 1 (pB (by decide +kernel)) (by show Nat.Prime 3; exact pB (by decide +kernel)) ds_2 (by decide +kernel)

def ds_3 : List ℕ := [2]

/-- A002386 row: the prime after 3 is 3 + 2. -/
theorem gap_3 : IsGapAt 3 2 :=
  isGapAt_of 3 2 (pB (by decide +kernel)) (by show Nat.Prime 5; exact pB (by decide +kernel)) ds_3 (by decide +kernel)

def ds_7 : List ℕ := [2, 3, 2]

/-- A002386 row: the prime after 7 is 7 + 4. -/
theorem gap_7 : IsGapAt 7 4 :=
  isGapAt_of 7 4 (pB (by decide +kernel)) (by show Nat.Prime 11; exact pB (by decide +kernel)) ds_7 (by decide +kernel)

def ds_23 : List ℕ := [2, 5, 2, 3, 2]

/-- A002386 row: the prime after 23 is 23 + 6. -/
theorem gap_23 : IsGapAt 23 6 :=
  isGapAt_of 23 6 (pB (by decide +kernel)) (by show Nat.Prime 29; exact pB (by decide +kernel)) ds_23 (by decide +kernel)

def ds_89 : List ℕ := [2, 7, 2, 3, 2, 5, 2]

/-- A002386 row: the prime after 89 is 89 + 8. -/
theorem gap_89 : IsGapAt 89 8 :=
  isGapAt_of 89 8 (pB (by decide +kernel)) (by show Nat.Prime 97; exact pB (by decide +kernel)) ds_89 (by decide +kernel)

def ds_113 : List ℕ := [2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2]

/-- A002386 row: the prime after 113 is 113 + 14. -/
theorem gap_113 : IsGapAt 113 14 :=
  isGapAt_of 113 14 (pB (by decide +kernel)) (by show Nat.Prime 127; exact pB (by decide +kernel)) ds_113 (by decide +kernel)

def ds_523 : List ℕ := [2, 3, 2, 17, 2, 23, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2]

/-- A002386 row: the prime after 523 is 523 + 18. -/
theorem gap_523 : IsGapAt 523 18 :=
  isGapAt_of 523 18 (pB (by decide +kernel)) (by show Nat.Prime 541; exact pB (by decide +kernel)) ds_523 (by decide +kernel)

def ds_887 : List ℕ := [2, 7, 2, 3, 2, 19, 2, 5, 2, 3, 2, 29, 2, 17, 2, 3, 2, 5, 2]

/-- A002386 row: the prime after 887 is 887 + 20. -/
theorem gap_887 : IsGapAt 887 20 :=
  isGapAt_of 887 20 (pB (by decide +kernel)) (by show Nat.Prime 907; exact pB (by decide +kernel)) ds_887 (by decide +kernel)

def ds_1129 : List ℕ := [2, 3, 2, 11, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5, 2, 31, 2, 3, 2]

/-- A002386 row: the prime after 1129 is 1129 + 22. -/
theorem gap_1129 : IsGapAt 1129 22 :=
  isGapAt_of 1129 22 (pB (by decide +kernel)) (by show Nat.Prime 1151; exact pB (by decide +kernel)) ds_1129 (by decide +kernel)

def ds_1327 : List ℕ := [
    2, 3, 2, 11, 2, 31, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5,
    2, 23, 2, 3, 2]

/-- A002386 row: the prime after 1327 is 1327 + 34. -/
theorem gap_1327 : IsGapAt 1327 34 :=
  isGapAt_of 1327 34 (pB (by decide +kernel)) (by show Nat.Prime 1361; exact pB (by decide +kernel)) ds_1327 (by decide +kernel)

def ds_9551 : List ℕ := [
    2, 41, 2, 3, 2, 19, 2, 11, 2, 3, 2, 73, 2, 5,
    2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 61, 2, 3,
    2, 11, 2, 7, 2, 3, 2]

/-- A002386 row: the prime after 9551 is 9551 + 36. -/
theorem gap_9551 : IsGapAt 9551 36 :=
  isGapAt_of 9551 36 (pB (by decide +kernel)) (by show Nat.Prime 9587; exact pB (by decide +kernel)) ds_9551 (by decide +kernel)

def ds_15683 : List ℕ := [
    2, 5, 2, 3, 2, 29, 2, 13, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 7, 2, 41, 2, 3, 2, 113, 2, 23, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 11, 2, 79, 2, 3, 2, 5,
    2]

/-- A002386 row: the prime after 15683 is 15683 + 44. -/
theorem gap_15683 : IsGapAt 15683 44 :=
  isGapAt_of 15683 44 (pB (by decide +kernel)) (by show Nat.Prime 15727; exact pB (by decide +kernel)) ds_15683 (by decide +kernel)

def ds_19609 : List ℕ := [
    2, 3, 2, 11, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 67, 2, 29, 2, 3, 2, 73,
    2, 41, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 43,
    2, 3, 2, 5, 2, 11, 2, 3, 2]

/-- A002386 row: the prime after 19609 is 19609 + 52. -/
theorem gap_19609 : IsGapAt 19609 52 :=
  isGapAt_of 19609 52 (pB (by decide +kernel)) (by show Nat.Prime 19661; exact pB (by decide +kernel)) ds_19609 (by decide +kernel)

def ds_31397 : List ℕ := [
    2, 17, 2, 3, 2, 31, 2, 5, 2, 3, 2, 7, 2, 101,
    2, 3, 2, 5, 2, 89, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 11, 2, 53, 2, 3, 2, 17, 2, 5, 2, 3, 2, 149,
    2, 23, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 71,
    2, 3, 2, 83, 2, 163, 2, 3, 2, 73, 2, 5, 2, 3,
    2]

/-- A002386 row: the prime after 31397 is 31397 + 72. -/
theorem gap_31397 : IsGapAt 31397 72 :=
  isGapAt_of 31397 72 (pB (by decide +kernel)) (by show Nat.Prime 31469; exact pB (by decide +kernel)) ds_31397 (by decide +kernel)

def ds_155921 : List ℕ := [
    2, 41, 2, 3, 2, 241, 2, 211, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 7, 2, 17, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 277, 2, 7, 2, 3, 2, 83, 2, 263, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 11, 2, 19, 2, 3, 2, 5, 2, 61,
    2, 3, 2, 7, 2, 151, 2, 3, 2, 13, 2, 389, 2, 3,
    2, 47, 2, 5, 2, 3, 2, 257, 2, 73, 2, 3, 2, 5,
    2]

/-- A002386 row: the prime after 155921 is 155921 + 86. -/
theorem gap_155921 : IsGapAt 155921 86 :=
  isGapAt_of 155921 86 (pB (by decide +kernel)) (by show Nat.Prime 156007; exact pB (by decide +kernel)) ds_155921 (by decide +kernel)

def ds_360653 : List ℕ := [
    2, 5, 2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 59,
    2, 3, 2, 101, 2, 29, 2, 3, 2, 19, 2, 11, 2, 3,
    2, 293, 2, 5, 2, 3, 2, 7, 2, 373, 2, 3, 2, 5,
    2, 107, 2, 3, 2, 11, 2, 7, 2, 3, 2, 197, 2, 23,
    2, 3, 2, 37, 2, 5, 2, 3, 2, 163, 2, 137, 2, 3,
    2, 5, 2, 43, 2, 3, 2, 7, 2, 181, 2, 3, 2, 13,
    2, 151, 2, 3, 2, 97, 2, 5, 2, 3, 2]

/-- A002386 row: the prime after 360653 is 360653 + 96. -/
theorem gap_360653 : IsGapAt 360653 96 :=
  isGapAt_of 360653 96 (pB (by decide +kernel)) (by show Nat.Prime 360749; exact pB (by decide +kernel)) ds_360653 (by decide +kernel)

def ds_370261 : List ℕ := [
    2, 3, 2, 5, 2, 479, 2, 3, 2, 11, 2, 43, 2, 3,
    2, 17, 2, 7, 2, 3, 2, 379, 2, 5, 2, 3, 2, 349,
    2, 19, 2, 3, 2, 5, 2, 353, 2, 3, 2, 29, 2, 367,
    2, 3, 2, 7, 2, 67, 2, 3, 2, 47, 2, 5, 2, 3,
    2, 547, 2, 7, 2, 3, 2, 5, 2, 107, 2, 3, 2, 13,
    2, 37, 2, 3, 2, 11, 2, 199, 2, 3, 2, 59, 2, 5,
    2, 3, 2, 7, 2, 179, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 383, 2, 7, 2, 3, 2, 19, 2, 23, 2, 3, 2]

/-- A002386 row: the prime after 370261 is 370261 + 112. -/
theorem gap_370261 : IsGapAt 370261 112 :=
  isGapAt_of 370261 112 (pB (by decide +kernel)) (by show Nat.Prime 370373; exact pB (by decide +kernel)) ds_370261 (by decide +kernel)

def ds_492113 : List ℕ := [
    2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 199,
    2, 3, 2, 23, 2, 17, 2, 3, 2, 37, 2, 181, 2, 3,
    2, 523, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 223, 2, 7, 2, 3, 2, 13, 2, 463,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 677, 2, 577, 2, 3,
    2, 5, 2, 31, 2, 3, 2, 7, 2, 13, 2, 3, 2, 331,
    2, 139, 2, 3, 2, 509, 2, 5, 2, 3, 2, 61, 2, 37,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 43, 2, 23, 2, 3,
    2]

/-- A002386 row: the prime after 492113 is 492113 + 114. -/
theorem gap_492113 : IsGapAt 492113 114 :=
  isGapAt_of 492113 114 (pB (by decide +kernel)) (by show Nat.Prime 492227; exact pB (by decide +kernel)) ds_492113 (by decide +kernel)

def ds_1349533 : List ℕ := [
    2, 3, 2, 7, 2, 53, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 503, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 97,
    2, 719, 2, 3, 2, 1091, 2, 13, 2, 3, 2, 29, 2, 5,
    2, 3, 2, 7, 2, 67, 2, 3, 2, 5, 2, 137, 2, 3,
    2, 107, 2, 7, 2, 3, 2, 41, 2, 419, 2, 3, 2, 577,
    2, 5, 2, 3, 2, 103, 2, 557, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 19, 2, 127, 2, 3,
    2, 239, 2, 5, 2, 3, 2, 71, 2, 43, 2, 3, 2, 5,
    2, 13, 2, 3, 2]

/-- A002386 row: the prime after 1349533 is 1349533 + 118. -/
theorem gap_1349533 : IsGapAt 1349533 118 :=
  isGapAt_of 1349533 118 (pB (by decide +kernel)) (by show Nat.Prime 1349651; exact pB (by decide +kernel)) ds_1349533 (by decide +kernel)

def ds_1357201 : List ℕ := [
    2, 3, 2, 5, 2, 23, 2, 3, 2, 31, 2, 11, 2, 3,
    2, 257, 2, 47, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17,
    2, 103, 2, 3, 2, 5, 2, 7, 2, 3, 2, 149, 2, 113,
    2, 3, 2, 307, 2, 127, 2, 3, 2, 23, 2, 5, 2, 3,
    2, 137, 2, 349, 2, 3, 2, 5, 2, 571, 2, 3, 2, 37,
    2, 31, 2, 3, 2, 53, 2, 7, 2, 3, 2, 229, 2, 5,
    2, 3, 2, 73, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 11, 2, 19, 2, 3, 2, 7, 2, 727, 2, 3, 2, 47,
    2, 5, 2, 3, 2, 181, 2, 7, 2, 3, 2, 5, 2, 449,
    2, 3, 2, 17, 2]

/-- A002386 row: the prime after 1357201 is 1357201 + 132. -/
theorem gap_1357201 : IsGapAt 1357201 132 :=
  isGapAt_of 1357201 132 (pB (by decide +kernel)) (by show Nat.Prime 1357333; exact pB (by decide +kernel)) ds_1357201 (by decide +kernel)

def ds_2010733 : List ℕ := [
    2, 3, 2, 67, 2, 991, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 13, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 251,
    2, 41, 2, 3, 2, 11, 2, 1103, 2, 3, 2, 29, 2, 5,
    2, 3, 2, 59, 2, 419, 2, 3, 2, 5, 2, 79, 2, 3,
    2, 71, 2, 367, 2, 3, 2, 1151, 2, 7, 2, 3, 2, 617,
    2, 5, 2, 3, 2, 43, 2, 11, 2, 3, 2, 5, 2, 641,
    2, 3, 2, 23, 2, 487, 2, 3, 2, 7, 2, 887, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 37, 2, 7, 2, 3, 2, 5,
    2, 167, 2, 3, 2, 107, 2, 13, 2, 3, 2, 1367, 2, 293,
    2, 3, 2, 593, 2, 5, 2, 3, 2, 7, 2, 67, 2, 3,
    2, 5, 2, 11, 2, 3, 2]

/-- A002386 row: the prime after 2010733 is 2010733 + 148. -/
theorem gap_2010733 : IsGapAt 2010733 148 :=
  isGapAt_of 2010733 148 (pB (by decide +kernel)) (by show Nat.Prime 2010881; exact pB (by decide +kernel)) ds_2010733 (by decide +kernel)

def ds_4652353 : List ℕ := [
    2, 3, 2, 1237, 2, 19, 2, 3, 2, 73, 2, 5, 2, 3,
    2, 1511, 2, 23, 2, 3, 2, 5, 2, 1097, 2, 3, 2, 157,
    2, 29, 2, 3, 2, 31, 2, 7, 2, 3, 2, 41, 2, 5,
    2, 3, 2, 83, 2, 13, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 97, 2, 67, 2, 3, 2, 7, 2, 823, 2, 3, 2, 1567,
    2, 5, 2, 3, 2, 373, 2, 7, 2, 3, 2, 5, 2, 1583,
    2, 3, 2, 17, 2, 397, 2, 3, 2, 109, 2, 31, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5,
    2, 107, 2, 3, 2, 43, 2, 7, 2, 3, 2, 911, 2, 13,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 173, 2, 37, 2, 3,
    2, 5, 2, 2029, 2, 3, 2, 7, 2, 691, 2, 3, 2]

/-- A002386 row: the prime after 4652353 is 4652353 + 154. -/
theorem gap_4652353 : IsGapAt 4652353 154 :=
  isGapAt_of 4652353 154 (pB (by decide +kernel)) (by show Nat.Prime 4652507; exact pB (by decide +kernel)) ds_4652353 (by decide +kernel)

def ds_17051707 : List ℕ := [
    2, 3, 2, 3433, 2, 7, 2, 3, 2, 23, 2, 179, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 101, 2, 17, 2, 3, 2, 5,
    2, 823, 2, 3, 2, 7, 2, 53, 2, 3, 2, 317, 2, 11,
    2, 3, 2, 103, 2, 5, 2, 3, 2, 19, 2, 2741, 2, 3,
    2, 5, 2, 31, 2, 3, 2, 11, 2, 571, 2, 3, 2, 41,
    2, 43, 2, 3, 2, 7, 2, 5, 2, 3, 2, 653, 2, 349,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 2351, 2, 3,
    2, 691, 2, 23, 2, 3, 2, 113, 2, 5, 2, 3, 2, 311,
    2, 613, 2, 3, 2, 5, 2, 13, 2, 3, 2, 2851, 2, 17,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 277, 2, 5, 2, 3,
    2, 53, 2, 73, 2, 3, 2, 5, 2, 37, 2, 3, 2, 941,
    2, 337, 2, 3, 2, 7, 2, 167, 2, 3, 2, 19, 2, 5,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2]

/-- A002386 row: the prime after 17051707 is 17051707 + 180. -/
theorem gap_17051707 : IsGapAt 17051707 180 :=
  isGapAt_of 17051707 180 (p17051707) (by show Nat.Prime 17051887; exact p17051887) ds_17051707 (by decide +kernel)

def ds_20831323 : List ℕ := [
    2, 3, 2, 11, 2, 71, 2, 3, 2, 37, 2, 5, 2, 3,
    2, 389, 2, 17, 2, 3, 2, 5, 2, 283, 2, 3, 2, 101,
    2, 19, 2, 3, 2, 2333, 2, 1223, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 877, 2, 1487, 2, 3, 2, 47, 2, 1217, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 23, 2, 547, 2, 3, 2, 5, 2, 37,
    2, 3, 2, 31, 2, 167, 2, 3, 2, 1019, 2, 7, 2, 3,
    2, 83, 2, 5, 2, 3, 2, 19, 2, 79, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 103, 2, 17, 2, 3, 2, 7, 2, 173,
    2, 3, 2, 4079, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 71, 2, 13, 2, 3, 2, 17,
    2, 43, 2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2, 23,
    2, 3, 2, 5, 2, 593, 2, 3, 2, 421, 2, 7, 2, 3,
    2, 151, 2, 107, 2, 3, 2, 139, 2, 5, 2, 3, 2, 199,
    2, 1433, 2, 3, 2, 5, 2, 3823, 2, 3, 2, 7, 2]

/-- A002386 row: the prime after 20831323 is 20831323 + 210. -/
theorem gap_20831323 : IsGapAt 20831323 210 :=
  isGapAt_of 20831323 210 (p20831323) (by show Nat.Prime 20831533; exact p20831533) ds_20831323 (by decide +kernel)

def ds_47326693 : List ℕ := [
    2, 3, 2, 11, 2, 7, 2, 3, 2, 43, 2, 5, 2, 3,
    2, 23, 2, 331, 2, 3, 2, 5, 2, 2939, 2, 3, 2, 13,
    2, 67, 2, 3, 2, 7, 2, 89, 2, 3, 2, 2521, 2, 5,
    2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 41, 2, 29, 2, 3, 2, 5477, 2, 17, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 7, 2, 1399, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 829, 2, 7, 2, 3, 2, 137, 2, 43, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 13, 2, 23, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 7, 2, 307, 2, 3, 2, 431, 2, 109,
    2, 3, 2, 2753, 2, 5, 2, 3, 2, 11, 2, 6793, 2, 3,
    2, 5, 2, 1279, 2, 3, 2, 1777, 2, 349, 2, 3, 2, 23,
    2, 73, 2, 3, 2, 7, 2, 5, 2, 3, 2, 139, 2, 17,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 743, 2, 11, 2, 3,
    2, 13, 2, 1931, 2, 3, 2, 101, 2, 5, 2, 3, 2, 6073,
    2, 19, 2, 3, 2, 5, 2, 1277, 2, 3, 2, 1409, 2, 13,
    2, 3, 2, 89, 2, 7, 2, 3, 2]

/-- A002386 row: the prime after 47326693 is 47326693 + 220. -/
theorem gap_47326693 : IsGapAt 47326693 220 :=
  isGapAt_of 47326693 220 (p47326693) (by show Nat.Prime 47326913; exact p47326913) ds_47326693 (by decide +kernel)

def ds_122164747 : List ℕ := [
    2, 3, 2, 59, 2, 23, 2, 3, 2, 11, 2, 1321, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 31, 2, 17, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 443, 2, 13, 2, 3, 2, 37, 2, 41,
    2, 3, 2, 8923, 2, 5, 2, 3, 2, 23, 2, 11, 2, 3,
    2, 5, 2, 97, 2, 3, 2, 10139, 2, 19, 2, 3, 2, 227,
    2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 739, 2, 31,
    2, 3, 2, 5, 2, 2699, 2, 3, 2, 53, 2, 73, 2, 3,
    2, 7, 2, 29, 2, 3, 2, 101, 2, 5, 2, 3, 2, 229,
    2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 41, 2, 17,
    2, 3, 2, 1399, 2, 571, 2, 3, 2, 61, 2, 5, 2, 3,
    2, 7, 2, 23, 2, 3, 2, 5, 2, 419, 2, 3, 2, 103,
    2, 7, 2, 3, 2, 17, 2, 5113, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 67, 2, 1993, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 23, 2, 13, 2, 3, 2, 71,
    2, 5, 2, 3, 2, 9941, 2, 149, 2, 3, 2, 5, 2, 797,
    2, 3, 2, 83, 2, 251, 2, 3, 2, 131, 2]

/-- A002386 row: the prime after 122164747 is 122164747 + 222. -/
theorem gap_122164747 : IsGapAt 122164747 222 :=
  isGapAt_of 122164747 222 (p122164747) (by show Nat.Prime 122164969; exact p122164969) ds_122164747 (by decide +kernel)

def ds_189695659 : List ℕ := [
    2, 3, 2, 139, 2, 5, 2, 3, 2, 79, 2, 11, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 7, 2, 73, 2, 3, 2, 383,
    2, 4241, 2, 3, 2, 11, 2, 5, 2, 3, 2, 29, 2, 13,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 173, 2, 47, 2, 3,
    2, 7481, 2, 2659, 2, 3, 2, 7, 2, 5, 2, 3, 2, 131,
    2, 397, 2, 3, 2, 5, 2, 7, 2, 3, 2, 17, 2, 23,
    2, 3, 2, 43, 2, 283, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 11, 2, 523, 2, 3, 2, 5, 2, 1163, 2, 3, 2, 547,
    2, 883, 2, 3, 2, 5717, 2, 7, 2, 3, 2, 181, 2, 5,
    2, 3, 2, 23, 2, 19, 2, 3, 2, 5, 2, 59, 2, 3,
    2, 167, 2, 11, 2, 3, 2, 7, 2, 17, 2, 3, 2, 6043,
    2, 5, 2, 3, 2, 97, 2, 7, 2, 3, 2, 5, 2, 67,
    2, 3, 2, 13, 2, 43, 2, 3, 2, 1759, 2, 5009, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 7, 2, 31, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 109, 2, 7, 2, 3, 2, 19, 2, 11,
    2, 3, 2, 29, 2, 5, 2, 3, 2, 5309, 2, 23, 2, 3,
    2, 5, 2, 503, 2, 3, 2, 7, 2]

/-- A002386 row: the prime after 189695659 is 189695659 + 234. -/
theorem gap_189695659 : IsGapAt 189695659 234 :=
  isGapAt_of 189695659 234 (p189695659) (by show Nat.Prime 189695893; exact p189695893) ds_189695659 (by decide +kernel)

def ds_191912783 : List ℕ := [
    2, 5, 2, 3, 2, 191, 2, 7, 2, 3, 2, 5, 2, 47,
    2, 3, 2, 439, 2, 2399, 2, 3, 2, 29, 2, 11, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 7, 2, 37, 2, 3, 2, 5,
    2, 43, 2, 3, 2, 11, 2, 7, 2, 3, 2, 227, 2, 73,
    2, 3, 2, 251, 2, 5, 2, 3, 2, 83, 2, 13, 2, 3,
    2, 5, 2, 67, 2, 3, 2, 7, 2, 19, 2, 3, 2, 13711,
    2, 197, 2, 3, 2, 6073, 2, 5, 2, 3, 2, 173, 2, 17,
    2, 3, 2, 5, 2, 1117, 2, 3, 2, 47, 2, 61, 2, 3,
    2, 11, 2, 59, 2, 3, 2, 7, 2, 5, 2, 3, 2, 31,
    2, 3181, 2, 3, 2, 5, 2, 7, 2, 3, 2, 109, 2, 29,
    2, 3, 2, 449, 2, 13, 2, 3, 2, 5479, 2, 5, 2, 3,
    2, 19, 2, 11, 2, 3, 2, 5, 2, 53, 2, 3, 2, 257,
    2, 107, 2, 3, 2, 1063, 2, 7, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 37, 2, 31, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 13, 2, 17, 2, 3, 2, 7, 2, 23, 2, 3, 2, 10627,
    2, 5, 2, 3, 2, 43, 2, 7, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 599, 2, 199, 2, 3, 2, 17, 2, 2861, 2, 3,
    2, 11527, 2, 5, 2, 3, 2, 7, 2]

/-- A002386 row: the prime after 191912783 is 191912783 + 248. -/
theorem gap_191912783 : IsGapAt 191912783 248 :=
  isGapAt_of 191912783 248 (p191912783) (by show Nat.Prime 191913031; exact p191913031) ds_191912783 (by decide +kernel)

def ds_387096133 : List ℕ := [
    2, 3, 2, 17, 2, 19, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 11, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 2861,
    2, 31, 2, 3, 2, 1031, 2, 109, 2, 3, 2, 283, 2, 5,
    2, 3, 2, 61, 2, 233, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 43, 2, 11, 2, 3, 2, 347, 2, 7, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 1907, 2, 41, 2, 3, 2, 5, 2, 157,
    2, 3, 2, 2441, 2, 131, 2, 3, 2, 7, 2, 13, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 17, 2, 7, 2, 3, 2, 5,
    2, 19081, 2, 3, 2, 97, 2, 19, 2, 3, 2, 37, 2, 11,
    2, 3, 2, 29, 2, 5, 2, 3, 2, 7, 2, 179, 2, 3,
    2, 5, 2, 43, 2, 3, 2, 11, 2, 7, 2, 3, 2, 31,
    2, 1193, 2, 3, 2, 41, 2, 5, 2, 3, 2, 1171, 2, 61,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 83, 2, 3,
    2, 571, 2, 67, 2, 3, 2, 173, 2, 5, 2, 3, 2, 19,
    2, 37, 2, 3, 2, 5, 2, 101, 2, 3, 2, 17, 2, 2663,
    2, 3, 2, 11, 2, 31, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 13, 2, 107, 2, 3, 2, 5, 2, 7, 2, 3, 2, 23,
    2, 15131, 2, 3, 2, 137, 2, 29, 2, 3, 2]

/-- A002386 row: the prime after 387096133 is 387096133 + 250. -/
theorem gap_387096133 : IsGapAt 387096133 250 :=
  isGapAt_of 387096133 250 (p387096133) (by show Nat.Prime 387096383; exact p387096383) ds_387096133 (by decide +kernel)

def ds_436273009 : List ℕ := [
    2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 5903, 2, 3,
    2, 5, 2, 2089, 2, 3, 2, 37, 2, 7, 2, 3, 2, 61,
    2, 23, 2, 3, 2, 149, 2, 5, 2, 3, 2, 16231, 2, 53,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 2251, 2, 3,
    2, 127, 2, 1747, 2, 3, 2, 199, 2, 5, 2, 3, 2, 11,
    2, 59, 2, 3, 2, 5, 2, 41, 2, 3, 2, 17, 2, 4507,
    2, 3, 2, 13, 2, 131, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 373, 2, 4789, 2, 3, 2, 5, 2, 7, 2, 3, 2, 571,
    2, 11, 2, 3, 2, 2671, 2, 29, 2, 3, 2, 107, 2, 5,
    2, 3, 2, 2207, 2, 43, 2, 3, 2, 5, 2, 1123, 2, 3,
    2, 9283, 2, 9257, 2, 3, 2, 53, 2, 7, 2, 3, 2, 401,
    2, 5, 2, 3, 2, 41, 2, 1567, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 1607, 2, 2447, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 17, 2, 5, 2, 3, 2, 31, 2, 7, 2, 3, 2, 5,
    2, 6367, 2, 3, 2, 11, 2, 971, 2, 3, 2, 1583, 2, 193,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 19, 2, 3,
    2, 5, 2, 101, 2, 3, 2, 13411, 2, 7, 2, 3, 2, 67,
    2, 163, 2, 3, 2, 13, 2, 5, 2, 3, 2, 17467, 2, 17,
    2, 3, 2, 5, 2, 2953, 2, 3, 2, 7, 2, 6691, 2, 3,
    2, 11, 2, 13, 2, 3, 2, 89, 2, 5, 2, 3, 2, 103,
    2]

/-- A002386 row: the prime after 436273009 is 436273009 + 282. -/
theorem gap_436273009 : IsGapAt 436273009 282 :=
  isGapAt_of 436273009 282 (p436273009) (by show Nat.Prime 436273291; exact p436273291) ds_436273009 (by decide +kernel)

def ds_1294268491 : List ℕ := [
    2, 3, 2, 5, 2, 17, 2, 3, 2, 7549, 2, 11, 2, 3,
    2, 7, 2, 673, 2, 3, 2, 1307, 2, 5, 2, 3, 2, 19037,
    2, 7, 2, 3, 2, 5, 2, 89, 2, 3, 2, 17, 2, 53,
    2, 3, 2, 61, 2, 4871, 2, 3, 2, 19, 2, 5, 2, 3,
    2, 7, 2, 83, 2, 3, 2, 5, 2, 127, 2, 3, 2, 13121,
    2, 7, 2, 3, 2, 43, 2, 11, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 29, 2, 19, 2, 3, 2, 5, 2, 331, 2, 3,
    2, 7, 2, 157, 2, 3, 2, 373, 2, 13, 2, 3, 2, 131,
    2, 5, 2, 3, 2, 433, 2, 73, 2, 3, 2, 5, 2, 2311,
    2, 3, 2, 37, 2, 523, 2, 3, 2, 23, 2, 179, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 53, 2, 101, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 13, 2, 43, 2, 3, 2, 11, 2, 61,
    2, 3, 2, 59, 2, 5, 2, 3, 2, 587, 2, 13451, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 67, 2, 107, 2, 3, 2, 1459,
    2, 7, 2, 3, 2, 31, 2, 5, 2, 3, 2, 251, 2, 11,
    2, 3, 2, 5, 2, 347, 2, 3, 2, 887, 2, 307, 2, 3,
    2, 7, 2, 23, 2, 3, 2, 11, 2, 5, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 5, 2, 163, 2, 3, 2, 389, 2, 19727,
    2, 3, 2, 4013, 2, 8501, 2, 3, 2, 29, 2, 5, 2, 3,
    2, 7, 2, 2503, 2, 3, 2, 5, 2, 11, 2, 3, 2, 19,
    2, 7, 2, 3, 2, 25889, 2]

/-- A002386 row: the prime after 1294268491 is 1294268491 + 288. -/
theorem gap_1294268491 : IsGapAt 1294268491 288 :=
  isGapAt_of 1294268491 288 (p1294268491) (by show Nat.Prime 1294268779; exact p1294268779) ds_1294268491 (by decide +kernel)

def ds_1453168141 : List ℕ := [
    2, 3, 2, 5, 2, 71, 2, 3, 2, 53, 2, 577, 2, 3,
    2, 7, 2, 67, 2, 3, 2, 29, 2, 5, 2, 3, 2, 61,
    2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 2459, 2, 31,
    2, 3, 2, 43, 2, 11, 2, 3, 2, 829, 2, 5, 2, 3,
    2, 7, 2, 4091, 2, 3, 2, 5, 2, 41, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 193, 2, 6653, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 37, 2, 47, 2, 3, 2, 5, 2, 89, 2, 3,
    2, 7, 2, 149, 2, 3, 2, 199, 2, 13, 2, 3, 2, 1493,
    2, 5, 2, 3, 2, 317, 2, 401, 2, 3, 2, 5, 2, 23,
    2, 3, 2, 109, 2, 43, 2, 3, 2, 11, 2, 17, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 41, 2, 61, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 13, 2, 37, 2, 3, 2, 31, 2, 163,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 607, 2, 11, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 3821, 2, 197, 2, 3, 2, 29,
    2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 97, 2, 433,
    2, 3, 2, 5, 2, 2069, 2, 3, 2, 113, 2, 53, 2, 3,
    2, 7, 2, 31, 2, 3, 2, 24407, 2, 5, 2, 3, 2, 13,
    2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 107, 2, 19,
    2, 3, 2, 269, 2, 83, 2, 3, 2, 6871, 2, 5, 2, 3,
    2, 7, 2, 139, 2, 3, 2, 5, 2, 127, 2, 3, 2, 227,
    2, 7, 2, 3, 2, 67, 2, 367, 2, 3, 2]

/-- A002386 row: the prime after 1453168141 is 1453168141 + 292. -/
theorem gap_1453168141 : IsGapAt 1453168141 292 :=
  isGapAt_of 1453168141 292 (p1453168141) (by show Nat.Prime 1453168433; exact p1453168433) ds_1453168141 (by decide +kernel)

def ds_2300942549 : List ℕ := [
    2, 211, 2, 3, 2, 5, 2, 131, 2, 3, 2, 19597, 2, 23,
    2, 3, 2, 7, 2, 37, 2, 3, 2, 271, 2, 5, 2, 3,
    2, 13, 2, 7, 2, 3, 2, 5, 2, 769, 2, 3, 2, 41,
    2, 59, 2, 3, 2, 227, 2, 43, 2, 3, 2, 353, 2, 5,
    2, 3, 2, 7, 2, 11, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 29, 2, 7, 2, 3, 2, 18947, 2, 1831, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 17, 2, 727, 2, 3, 2, 5, 2, 103,
    2, 3, 2, 7, 2, 71, 2, 3, 2, 13, 2, 107, 2, 3,
    2, 3613, 2, 5, 2, 3, 2, 47, 2, 39139, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 151, 2, 13, 2, 3, 2, 1049, 2, 53,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2, 23, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 59, 2, 577, 2, 3, 2, 37,
    2, 163, 2, 3, 2, 97, 2, 5, 2, 3, 2, 31, 2, 19,
    2, 3, 2, 5, 2, 29, 2, 3, 2, 17, 2, 11, 2, 3,
    2, 23, 2, 7, 2, 3, 2, 61, 2, 5, 2, 3, 2, 26681,
    2, 13, 2, 3, 2, 5, 2, 223, 2, 3, 2, 43, 2, 347,
    2, 3, 2, 7, 2, 8689, 2, 3, 2, 2281, 2, 5, 2, 3,
    2, 541, 2, 7, 2, 3, 2, 5, 2, 653, 2, 3, 2, 39191,
    2, 109, 2, 3, 2, 19, 2, 11, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 7, 2, 17107, 2, 3, 2, 5, 2, 7489, 2, 3,
    2, 11, 2, 7, 2, 3, 2, 41, 2, 13, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 83, 2, 7933, 2, 3, 2, 5, 2, 43,
    2, 3, 2, 7, 2, 2053, 2, 3, 2, 167, 2]

/-- A002386 row: the prime after 2300942549 is 2300942549 + 320. -/
theorem gap_2300942549 : IsGapAt 2300942549 320 :=
  isGapAt_of 2300942549 320 (p2300942549) (by show Nat.Prime 2300942869; exact p2300942869) ds_2300942549 (by decide +kernel)

def ds_3842610773 : List ℕ := [
    2, 5, 2, 3, 2, 7, 2, 2593, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 53849, 2, 7, 2, 3, 2, 31, 2, 353, 2, 3,
    2, 103, 2, 5, 2, 3, 2, 29, 2, 13, 2, 3, 2, 5,
    2, 131, 2, 3, 2, 7, 2, 53, 2, 3, 2, 11, 2, 1931,
    2, 3, 2, 8087, 2, 5, 2, 3, 2, 37, 2, 887, 2, 3,
    2, 5, 2, 1303, 2, 3, 2, 23, 2, 389, 2, 3, 2, 107,
    2, 31, 2, 3, 2, 7, 2, 5, 2, 3, 2, 19739, 2, 11,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 61, 2, 197, 2, 3,
    2, 60631, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3, 2, 109,
    2, 19, 2, 3, 2, 5, 2, 23663, 2, 3, 2, 83, 2, 37,
    2, 3, 2, 317, 2, 7, 2, 3, 2, 457, 2, 5, 2, 3,
    2, 17, 2, 269, 2, 3, 2, 5, 2, 11, 2, 3, 2, 13,
    2, 23, 2, 3, 2, 7, 2, 18913, 2, 3, 2, 101, 2, 5,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 401, 2, 1279, 2, 3, 2, 19, 2, 41, 2, 3, 2, 29,
    2, 5, 2, 3, 2, 7, 2, 113, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 67, 2, 7, 2, 3, 2, 47, 2, 103, 2, 3,
    2, 521, 2, 5, 2, 3, 2, 13, 2, 43, 2, 3, 2, 5,
    2, 1367, 2, 3, 2, 7, 2, 409, 2, 3, 2, 397, 2, 5443,
    2, 3, 2, 14747, 2, 5, 2, 3, 2, 167, 2, 2591, 2, 3,
    2, 5, 2, 48677, 2, 3, 2, 37, 2, 163, 2, 3, 2, 58481,
    2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 131, 2, 23,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 71, 2, 3,
    2, 13, 2, 17, 2, 3, 2, 349, 2, 5, 2, 3, 2]

/-- A002386 row: the prime after 3842610773 is 3842610773 + 336. -/
theorem gap_3842610773 : IsGapAt 3842610773 336 :=
  isGapAt_of 3842610773 336 (p3842610773) (by show Nat.Prime 3842611109; exact p3842611109) ds_3842610773 (by decide +kernel)

def ds_4302407359 : List ℕ := [
    2, 3, 2, 191, 2, 5, 2, 3, 2, 13, 2, 317, 2, 3,
    2, 5, 2, 71, 2, 3, 2, 59, 2, 2399, 2, 3, 2, 79,
    2, 7, 2, 3, 2, 23, 2, 5, 2, 3, 2, 283, 2, 47,
    2, 3, 2, 5, 2, 33563, 2, 3, 2, 173, 2, 17, 2, 3,
    2, 7, 2, 353, 2, 3, 2, 3527, 2, 5, 2, 3, 2, 1489,
    2, 7, 2, 3, 2, 5, 2, 2417, 2, 3, 2, 43, 2, 19,
    2, 3, 2, 13, 2, 1381, 2, 3, 2, 5903, 2, 5, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 5, 2, 181, 2, 3, 2, 37,
    2, 7, 2, 3, 2, 3767, 2, 67, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 277, 2, 29, 2, 3, 2, 5, 2, 73, 2, 3,
    2, 7, 2, 509, 2, 3, 2, 1069, 2, 31, 2, 3, 2, 17579,
    2, 5, 2, 3, 2, 19, 2, 643, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 23, 2, 1871, 2, 3, 2, 4133, 2, 113, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 11, 2, 13, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 109, 2, 719, 2, 3, 2, 673, 2, 7517,
    2, 3, 2, 12721, 2, 5, 2, 3, 2, 281, 2, 569, 2, 3,
    2, 5, 2, 5939, 2, 3, 2, 463, 2, 11, 2, 3, 2, 1093,
    2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 2543, 2, 41,
    2, 3, 2, 5, 2, 17, 2, 3, 2, 379, 2, 23, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 19, 2, 5, 2, 3, 2, 5179,
    2, 7, 2, 3, 2, 5, 2, 139, 2, 3, 2, 17, 2, 61,
    2, 3, 2, 163, 2, 11, 2, 3, 2, 179, 2, 5, 2, 3,
    2, 7, 2, 19, 2, 3, 2, 5, 2, 233, 2, 3, 2, 11,
    2, 7, 2, 3, 2, 6793, 2, 6703, 2, 3, 2, 37, 2, 5,
    2, 3, 2, 43, 2, 197, 2, 3, 2, 5, 2, 13, 2, 3,
    2, 7, 2]

/-- A002386 row: the prime after 4302407359 is 4302407359 + 354. -/
theorem gap_4302407359 : IsGapAt 4302407359 354 :=
  isGapAt_of 4302407359 354 (p4302407359) (by show Nat.Prime 4302407713; exact p4302407713) ds_4302407359 (by decide +kernel)

def ds_10726904659 : List ℕ := [
    2, 3, 2, 547, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 5, 2, 101, 2, 3, 2, 17, 2, 11, 2, 3, 2, 55819,
    2, 19, 2, 3, 2, 313, 2, 5, 2, 3, 2, 7, 2, 149,
    2, 3, 2, 5, 2, 6269, 2, 3, 2, 617, 2, 7, 2, 3,
    2, 61, 2, 631, 2, 3, 2, 1453, 2, 5, 2, 3, 2, 7243,
    2, 283, 2, 3, 2, 5, 2, 53, 2, 3, 2, 7, 2, 29,
    2, 3, 2, 13, 2, 11, 2, 3, 2, 257, 2, 5, 2, 3,
    2, 97, 2, 9733, 2, 3, 2, 5, 2, 773, 2, 3, 2, 11,
    2, 13, 2, 3, 2, 613, 2, 1523, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 653, 2, 229, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 29, 2, 19, 2, 3, 2, 81973, 2, 769, 2, 3, 2, 12637,
    2, 5, 2, 3, 2, 67, 2, 103, 2, 3, 2, 5, 2, 5573,
    2, 3, 2, 12043, 2, 239, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 53, 2, 5, 2, 3, 2, 557, 2, 13, 2, 3, 2, 5,
    2, 71, 2, 3, 2, 2729, 2, 6247, 2, 3, 2, 7, 2, 89,
    2, 3, 2, 59, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3,
    2, 5, 2, 23, 2, 3, 2, 967, 2, 47, 2, 3, 2, 179,
    2, 389, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 19979,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 31, 2, 7, 2, 3,
    2, 7283, 2, 13, 2, 3, 2, 23, 2, 5, 2, 3, 2, 241,
    2, 1987, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 17,
    2, 3, 2, 12037, 2, 281, 2, 3, 2, 173, 2, 5, 2, 3,
    2, 11, 2, 12413, 2, 3, 2, 5, 2, 83, 2, 3, 2, 13,
    2, 31, 2, 3, 2, 17, 2, 41, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 71, 2, 43, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 2297, 2, 11, 2, 3, 2, 17539, 2, 113, 2, 3, 2, 1301,
    2, 5, 2, 3, 2, 1459, 2, 19, 2, 3, 2, 5, 2, 347,
    2, 3, 2]

/-- A002386 row: the prime after 10726904659 is 10726904659 + 382. -/
theorem gap_10726904659 : IsGapAt 10726904659 382 :=
  isGapAt_of 10726904659 382 (p10726904659) (by show Nat.Prime 10726905041; exact p10726905041) ds_10726904659 (by decide +kernel)

def ds_20678048297 : List ℕ := [
    2, 6311, 2, 3, 2, 11, 2, 5, 2, 3, 2, 2267, 2, 17,
    2, 3, 2, 5, 2, 23, 2, 3, 2, 7, 2, 42793, 2, 3,
    2, 19, 2, 67, 2, 3, 2, 15661, 2, 5, 2, 3, 2, 13,
    2, 181, 2, 3, 2, 5, 2, 11, 2, 3, 2, 4337, 2, 103,
    2, 3, 2, 821, 2, 18539, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 11, 2, 193, 2, 3, 2, 5, 2, 7, 2, 3, 2, 1093,
    2, 167, 2, 3, 2, 1453, 2, 31, 2, 3, 2, 1031, 2, 5,
    2, 3, 2, 9227, 2, 37, 2, 3, 2, 5, 2, 1303, 2, 3,
    2, 2251, 2, 11, 2, 3, 2, 13, 2, 7, 2, 3, 2, 59,
    2, 5, 2, 3, 2, 97, 2, 991, 2, 3, 2, 5, 2, 29,
    2, 3, 2, 19, 2, 13, 2, 3, 2, 7, 2, 71, 2, 3,
    2, 101, 2, 5, 2, 3, 2, 163, 2, 7, 2, 3, 2, 5,
    2, 124147, 2, 3, 2, 79, 2, 353, 2, 3, 2, 3851, 2, 11,
    2, 3, 2, 57713, 2, 5, 2, 3, 2, 7, 2, 34613, 2, 3,
    2, 5, 2, 1049, 2, 3, 2, 11, 2, 7, 2, 3, 2, 43,
    2, 461, 2, 3, 2, 31, 2, 5, 2, 3, 2, 104879, 2, 13,
    2, 3, 2, 5, 2, 41, 2, 3, 2, 7, 2, 4493, 2, 3,
    2, 967, 2, 359, 2, 3, 2, 3023, 2, 5, 2, 3, 2, 17,
    2, 18371, 2, 3, 2, 5, 2, 137, 2, 3, 2, 269, 2, 4999,
    2, 3, 2, 11, 2, 131, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 106823, 2, 257, 2, 3, 2, 5, 2, 7, 2, 3, 2, 71,
    2, 19, 2, 3, 2, 67, 2, 13, 2, 3, 2, 1213, 2, 5,
    2, 3, 2, 41, 2, 11, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 659, 2, 37, 2, 3, 2, 349, 2, 7, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 23, 2, 431, 2, 3, 2, 5, 2, 1723,
    2, 3, 2, 13, 2, 113, 2, 3, 2, 7, 2, 59, 2, 3,
    2, 73127, 2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5,
    2, 11, 2, 3, 2]

/-- A002386 row: the prime after 20678048297 is 20678048297 + 384. -/
theorem gap_20678048297 : IsGapAt 20678048297 384 :=
  isGapAt_of 20678048297 384 (p20678048297) (by show Nat.Prime 20678048681; exact p20678048681) ds_20678048297 (by decide +kernel)

def ds_22367084959 : List ℕ := [
    2, 3, 2, 53, 2, 5, 2, 3, 2, 823, 2, 7, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 19, 2, 10079, 2, 3, 2, 13,
    2, 37847, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7, 2, 31,
    2, 3, 2, 5, 2, 37, 2, 3, 2, 17, 2, 7, 2, 3,
    2, 131, 2, 19, 2, 3, 2, 1367, 2, 5, 2, 3, 2, 5573,
    2, 6047, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 7307,
    2, 3, 2, 167, 2, 1153, 2, 3, 2, 1289, 2, 5, 2, 3,
    2, 11, 2, 79, 2, 3, 2, 5, 2, 43, 2, 3, 2, 773,
    2, 127591, 2, 3, 2, 33629, 2, 17, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 821, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 41, 2, 11, 2, 3, 2, 89, 2, 1433, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 65629, 2, 127763, 2, 3, 2, 5, 2, 1103,
    2, 3, 2, 11717, 2, 19, 2, 3, 2, 1097, 2, 7, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 23, 2, 68903, 2, 3, 2, 5,
    2, 179, 2, 3, 2, 6829, 2, 47, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 211, 2, 5, 2, 3, 2, 97, 2, 7, 2, 3,
    2, 5, 2, 31, 2, 3, 2, 11, 2, 1009, 2, 3, 2, 2063,
    2, 71, 2, 3, 2, 461, 2, 5, 2, 3, 2, 7, 2, 49741,
    2, 3, 2, 5, 2, 6911, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 157, 2, 29, 2, 3, 2, 661, 2, 5, 2, 3, 2, 43,
    2, 23, 2, 3, 2, 5, 2, 13, 2, 3, 2, 7, 2, 109,
    2, 3, 2, 11, 2, 563, 2, 3, 2, 50263, 2, 5, 2, 3,
    2, 61, 2, 283, 2, 3, 2, 5, 2, 1129, 2, 3, 2, 53,
    2, 17, 2, 3, 2, 23, 2, 10069, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 31, 2, 223, 2, 3, 2, 17, 2, 59, 2, 3, 2, 11,
    2, 5, 2, 3, 2, 2213, 2, 1453, 2, 3, 2, 5, 2, 139,
    2, 3, 2, 71, 2, 151, 2, 3, 2, 41, 2, 7, 2, 3,
    2]

/-- A002386 row: the prime after 22367084959 is 22367084959 + 394. -/
theorem gap_22367084959 : IsGapAt 22367084959 394 :=
  isGapAt_of 22367084959 394 (p22367084959) (by show Nat.Prime 22367085353; exact p22367085353) ds_22367084959 (by decide +kernel)

def ds_25056082087 : List ℕ := [
    2, 3, 2, 3769, 2, 7, 2, 3, 2, 19, 2, 29, 2, 3,
    2, 13, 2, 5, 2, 3, 2, 8863, 2, 17, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 7, 2, 1871, 2, 3, 2, 1277, 2, 13,
    2, 3, 2, 37, 2, 5, 2, 3, 2, 11, 2, 110597, 2, 3,
    2, 5, 2, 661, 2, 3, 2, 53, 2, 9043, 2, 3, 2, 29,
    2, 373, 2, 3, 2, 7, 2, 5, 2, 3, 2, 151, 2, 23,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 13, 2, 11, 2, 3,
    2, 16879, 2, 13591, 2, 3, 2, 131, 2, 5, 2, 3, 2, 223,
    2, 691, 2, 3, 2, 5, 2, 13, 2, 3, 2, 19, 2, 17,
    2, 3, 2, 23, 2, 7, 2, 3, 2, 11831, 2, 5, 2, 3,
    2, 3637, 2, 3631, 2, 3, 2, 5, 2, 41, 2, 3, 2, 43,
    2, 25111, 2, 3, 2, 7, 2, 11, 2, 3, 2, 313, 2, 5,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 61, 2, 3,
    2, 11, 2, 29, 2, 3, 2, 13297, 2, 251, 2, 3, 2, 1201,
    2, 5, 2, 3, 2, 7, 2, 311, 2, 3, 2, 5, 2, 10789,
    2, 3, 2, 1009, 2, 7, 2, 3, 2, 167, 2, 23, 2, 3,
    2, 93913, 2, 5, 2, 3, 2, 41, 2, 79, 2, 3, 2, 5,
    2, 43, 2, 3, 2, 7, 2, 8807, 2, 3, 2, 11, 2, 63347,
    2, 3, 2, 1487, 2, 5, 2, 3, 2, 17, 2, 31, 2, 3,
    2, 5, 2, 23201, 2, 3, 2, 2473, 2, 13, 2, 3, 2, 277,
    2, 8581, 2, 3, 2, 7, 2, 5, 2, 3, 2, 647, 2, 11,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 14057, 2, 67, 2, 3,
    2, 80449, 2, 71, 2, 3, 2, 11, 2, 5, 2, 3, 2, 10529,
    2, 163, 2, 3, 2, 5, 2, 17, 2, 3, 2, 78007, 2, 149,
    2, 3, 2, 241, 2, 7, 2, 3, 2, 857, 2, 5, 2, 3,
    2, 19, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2, 17,
    2, 601, 2, 3, 2, 7, 2, 113, 2, 3, 2, 9871, 2, 5,
    2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 137, 2, 41, 2, 3, 2, 2531, 2, 1063, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 7, 2, 123583, 2, 3, 2, 5, 2, 103333,
    2, 3, 2, 61, 2, 7, 2, 3, 2, 1459, 2, 13, 2, 3,
    2, 383, 2, 5, 2, 3, 2, 461, 2, 173, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 7, 2]

/-- A002386 row: the prime after 25056082087 is 25056082087 + 456. -/
theorem gap_25056082087 : IsGapAt 25056082087 456 :=
  isGapAt_of 25056082087 456 (p25056082087) (by show Nat.Prime 25056082543; exact p25056082543) ds_25056082087 (by decide +kernel)

def ds_42652618343 : List ℕ := [
    2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 8663,
    2, 3, 2, 89599, 2, 733, 2, 3, 2, 17, 2, 19, 2, 3,
    2, 103, 2, 5, 2, 3, 2, 7, 2, 223, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 739, 2, 7, 2, 3, 2, 137, 2, 15991,
    2, 3, 2, 127, 2, 5, 2, 3, 2, 1321, 2, 13, 2, 3,
    2, 5, 2, 131, 2, 3, 2, 7, 2, 1777, 2, 3, 2, 31,
    2, 23143, 2, 3, 2, 23, 2, 5, 2, 3, 2, 193, 2, 1051,
    2, 3, 2, 5, 2, 41, 2, 3, 2, 827, 2, 101, 2, 3,
    2, 63629, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17,
    2, 3671, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 19,
    2, 3, 2, 47, 2, 13, 2, 3, 2, 421, 2, 5, 2, 3,
    2, 317, 2, 37, 2, 3, 2, 5, 2, 683, 2, 3, 2, 53,
    2, 113, 2, 3, 2, 1669, 2, 7, 2, 3, 2, 43, 2, 5,
    2, 3, 2, 41, 2, 3187, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 13, 2, 109, 2, 3, 2, 7, 2, 67, 2, 3, 2, 3391,
    2, 5, 2, 3, 2, 19, 2, 7, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 17, 2, 487, 2, 3, 2, 307, 2, 29, 2, 3,
    2, 7349, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5,
    2, 19, 2, 3, 2, 59, 2, 7, 2, 3, 2, 491, 2, 43,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 13, 2, 743, 2, 3,
    2, 5, 2, 55381, 2, 3, 2, 7, 2, 199, 2, 3, 2, 29,
    2, 17, 2, 3, 2, 349, 2, 5, 2, 3, 2, 37, 2, 77447,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 283, 2, 23, 2, 3,
    2, 9643, 2, 433, 2, 3, 2, 7, 2, 5, 2, 3, 2, 11,
    2, 1613, 2, 3, 2, 5, 2, 7, 2, 3, 2, 2857, 2, 41,
    2, 3, 2, 13, 2, 983, 2, 3, 2, 5701, 2, 5, 2, 3,
    2, 23, 2, 19, 2, 3, 2, 5, 2, 173, 2, 3, 2, 277,
    2, 11, 2, 3, 2, 271, 2, 7, 2, 3, 2, 229, 2, 5,
    2, 3, 2, 71, 2, 17, 2, 3, 2, 5, 2, 7207, 2, 3,
    2, 4421, 2, 29, 2, 3, 2, 7, 2, 83, 2, 3, 2, 967,
    2, 5, 2, 3, 2, 47, 2, 7, 2, 3, 2, 5, 2, 73,
    2, 3, 2, 43, 2, 99257, 2, 3, 2, 19, 2, 11, 2, 3,
    2, 79, 2, 5, 2, 3, 2, 7, 2, 13, 2, 3, 2, 5,
    2]

/-- A002386 row: the prime after 42652618343 is 42652618343 + 464. -/
theorem gap_42652618343 : IsGapAt 42652618343 464 :=
  isGapAt_of 42652618343 464 (p42652618343) (by show Nat.Prime 42652618807; exact p42652618807) ds_42652618343 (by decide +kernel)

end LeanLab.Verifications.Top50.Gaps1
