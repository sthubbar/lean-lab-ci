/-
P0005 Oliveira e Silva, Herzog, Pardi 2014, Math. Comp. 83, 2033 to 2060, Table 5 page 2044,
the rows not already in Sinisalo 1993 Table 2, part 1: minGB S(p) = p. Divisors and Pratt
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

theorem p15222379 : Nat.Prime 15222379 := by
  refine Pratt.pratt 15222379 2 [(2, 1), (3, 1), (17, 1), (149239, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p36181471 : Nat.Prime 36181471 := by
  refine Pratt.pratt 36181471 7 [(2, 1), (3, 1), (5, 1), (13, 1), (113, 1), (821, 1)] (by norm_num)
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
theorem p44969987 : Nat.Prime 44969987 := by
  refine Pratt.pratt 44969987 2 [(2, 1), (1319, 1), (17047, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p67225399 : Nat.Prime 67225399 := by
  refine Pratt.pratt 67225399 3 [(2, 1), (3, 1), (101, 1), (110933, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p287154929 : Nat.Prime 287154929 := by
  refine Pratt.pratt 287154929 3 [(2, 4), (37, 1), (485059, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p406788253 : Nat.Prime 406788253 := by
  refine Pratt.pratt 406788253 2 [(2, 2), (3, 1), (13, 1), (19, 1), (71, 1), (1933, 1)] (by norm_num)
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
theorem p1487703787 : Nat.Prime 1487703787 := by
  refine Pratt.pratt 1487703787 2 [(2, 1), (3, 1), (83, 1), (373, 1), (8009, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p1627153013 : Nat.Prime 1627153013 := by
  refine Pratt.pratt 1627153013 2 [(2, 2), (406788253, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p406788253
theorem p2744326943 : Nat.Prime 2744326943 := by
  refine Pratt.pratt 2744326943 5 [(2, 1), (7, 1), (227, 1), (863539, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p5121979003 : Nat.Prime 5121979003 := by
  refine Pratt.pratt 5121979003 12 [(2, 1), (3, 3), (7, 1), (149, 1), (211, 1), (431, 1)] (by norm_num)
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
theorem p52425873277 : Nat.Prime 52425873277 := by
  refine Pratt.pratt 52425873277 2 [(2, 2), (3, 1), (7, 1), (41, 1), (15222379, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p15222379
theorem p78904236053 : Nat.Prime 78904236053 := by
  refine Pratt.pratt 78904236053 2 [(2, 2), (179, 1), (1709, 1), (64483, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p330748963081 : Nat.Prime 330748963081 := by
  refine Pratt.pratt 330748963081 14 [(2, 3), (3, 1), (5, 1), (41, 1), (67225399, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p67225399
theorem p743891043761 : Nat.Prime 743891043761 := by
  refine Pratt.pratt 743891043761 3 [(2, 4), (5, 1), (257, 1), (36181471, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p36181471
theorem p838813972433 : Nat.Prime 838813972433 := by
  refine Pratt.pratt 838813972433 3 [(2, 4), (52425873277, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p52425873277
theorem p1578084721061 : Nat.Prime 1578084721061 := by
  refine Pratt.pratt 1578084721061 3 [(2, 2), (5, 1), (78904236053, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p78904236053
theorem p2541246749219 : Nat.Prime 2541246749219 := by
  refine Pratt.pratt 2541246749219 2 [(2, 1), (463, 1), (2744326943, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p2744326943
theorem p3228317217791 : Nat.Prime 3228317217791 := by
  refine Pratt.pratt 3228317217791 7 [(2, 1), (5, 1), (7, 1), (31, 1), (1487703787, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p1487703787
theorem p6046500596309 : Nat.Prime 6046500596309 := by
  refine Pratt.pratt 6046500596309 2 [(2, 2), (929, 1), (1627153013, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p1627153013
theorem p7119550814171 : Nat.Prime 7119550814171 := by
  refine Pratt.pratt 7119550814171 2 [(2, 1), (5, 1), (139, 1), (5121979003, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p5121979003
theorem p7405567519187 : Nat.Prime 7405567519187 := by
  refine Pratt.pratt 7405567519187 2 [(2, 1), (82339, 1), (44969987, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p44969987
theorem p10770353848811 : Nat.Prime 10770353848811 := by
  refine Pratt.pratt 10770353848811 2 [(2, 1), (5, 1), (653819, 1), (1647299, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p17455158893933 : Nat.Prime 17455158893933 := by
  refine Pratt.pratt 17455158893933 2 [(2, 2), (83, 1), (8387, 1), (6268723, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p18566952587039 : Nat.Prime 18566952587039 := by
  refine Pratt.pratt 18566952587039 23 [(2, 1), (929, 1), (11351, 1), (880361, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p27066507915593 : Nat.Prime 27066507915593 := by
  refine Pratt.pratt 27066507915593 5 [(2, 3), (79, 1), (151, 1), (233, 1), (313, 1), (3889, 1)] (by norm_num)
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
theorem p36361448355647 : Nat.Prime 36361448355647 := by
  refine Pratt.pratt 36361448355647 5 [(2, 1), (23, 1), (151, 1), (1459, 1), (3587989, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p39028377643559 : Nat.Prime 39028377643559 := by
  refine Pratt.pratt 39028377643559 13 [(2, 1), (59, 1), (330748963081, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p330748963081
theorem p40854680368547 : Nat.Prime 40854680368547 := by
  refine Pratt.pratt 40854680368547 2 [(2, 1), (11, 1), (29, 1), (223, 1), (287154929, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p287154929
theorem p44776706178803 : Nat.Prime 44776706178803 := by
  refine Pratt.pratt 44776706178803 2 [(2, 1), (13, 1), (331, 1), (1609, 1), (3233663, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p54133015831187 : Nat.Prime 54133015831187 := by
  refine Pratt.pratt 54133015831187 2 [(2, 1), (27066507915593, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p27066507915593

def ds_2441 : List ℕ := [
    2, 7, 13, 3, 31, 3, 5, 3,
    2297, 11, 3, 3, 17, 3, 5, 23,
    7, 3, 3, 15271, 3, 3, 13, 479,
    3, 7, 3, 5, 3, 196307, 3, 3371,
    5, 3, 157, 3, 3, 3, 5, 668089,
    19, 3, 23, 3, 5, 3, 3, 3,
    5, 3, 8933, 13, 3, 89, 5, 548519,
    7, 3, 3, 179, 3, 11, 3, 7,
    3, 5, 3, 3, 5, 3, 7, 11,
    3, 3, 3, 31, 1049, 3, 941, 3,
    71, 3, 829, 3, 3, 29, 17, 3,
    97, 3, 5, 7, 3, 11, 3, 337,
    173, 7, 3, 3, 3, 5, 7, 31,
    3, 3, 5, 67, 10847, 3, 3, 3,
    5, 3, 3, 283, 3, 5, 17, 14939,
    3, 3, 5, 109, 3, 2879, 3, 349,
    3, 3, 3, 23, 3, 3, 15797, 3,
    7, 3, 5, 37, 3, 11, 3, 5,
    3, 421, 3, 5, 3, 13, 3, 23,
    3, 5, 3, 313, 3, 269761, 3, 7,
    5, 11, 3, 1637, 5, 7, 3, 3,
    3, 41, 11, 3, 37, 3, 3, 7459,
    3, 17, 3, 3, 3, 19, 3, 5,
    59447, 7, 3, 3, 3, 7, 3, 17,
    3, 47, 5, 7, 3, 3, 5, 389,
    9811, 3, 3, 3, 41, 5, 3, 11,
    443, 3, 3, 405073, 3, 5, 7, 3,
    3, 7, 5, 258109, 3, 3, 13, 3,
    5, 3, 19, 296801, 3, 643, 3, 3,
    3, 11, 3, 5, 3, 18269, 31, 43,
    212671, 3, 3, 3, 277, 1201, 3, 7,
    3, 2729, 3, 191, 5, 3, 7, 430303,
    3, 3, 5, 3, 3, 5, 3, 3,
    5, 3, 23, 13, 3, 239633, 3, 3,
    3, 3, 3, 3, 5, 3, 3, 11,
    7, 3, 5, 3, 3, 31, 3, 5,
    3, 19, 765283, 5, 165817, 241, 3, 7,
    3, 7477, 17, 3, 3, 5, 3, 19,
    3, 3, 5, 3, 101, 3, 269429, 100193,
    17, 3, 5, 3, 229, 13, 3, 1933,
    3, 3, 11, 3, 3539, 3, 3, 3,
    5, 17551, 3, 5, 3, 7, 3, 5,
    3, 11, 3, 3, 3, 5, 47, 3,
    53, 11, 3, 3, 83, 5, 3, 3,
    205823, 3, 3, 149, 23, 7, 5, 13,
    3]

theorem prime_sub_2441 : Nat.Prime (743891046202 - 2441) := by
  show Nat.Prime 743891043761
  exact p743891043761

theorem check_2441 : allC 743891046202 2441 P10k ds_2441 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 743891046202 is 2441. -/
theorem minGB_S_2441 : minGB 743891046202 = 2441 :=
  minGB_eq_of P10k P10k_complete 743891046202 2441 (by norm_num) (by norm_num) prime_sub_2441 ds_2441 check_2441

def ds_2459 : List ℕ := [
    2, 11, 7, 3, 3943, 3, 5, 3,
    13, 43, 3, 3, 192013, 3, 5, 317,
    9007, 3, 3, 1201, 3, 3, 29, 7,
    3, 13, 3, 5, 3, 11, 3, 7,
    5, 3, 396293, 3, 3, 3, 5, 7,
    11, 3, 1213, 3, 5, 3, 3, 3,
    5, 3, 149, 17, 3, 31, 5, 139,
    401, 3, 3, 42463, 3, 199, 3, 11,
    3, 5, 3, 3, 5, 3, 516617, 157,
    3, 3, 3, 7, 1901, 3, 283, 3,
    107, 3, 19, 3, 3, 11, 33503, 3,
    179, 3, 5, 59, 3, 13, 3, 223,
    7, 25453, 3, 3, 3, 5, 1013, 13,
    3, 3, 5, 7, 160651, 3, 3, 3,
    5, 3, 3, 11, 3, 5, 23, 19,
    3, 3, 5, 353, 3, 281, 3, 7,
    3, 3, 3, 803287, 3, 3, 7, 3,
    11, 3, 5, 31, 3, 97, 3, 5,
    3, 11, 3, 5, 3, 461, 3, 13,
    3, 5, 3, 35419, 3, 7, 3, 101,
    5, 17, 3, 7, 5, 53, 3, 3,
    3, 7, 600827, 3, 239, 3, 3, 983,
    3, 43, 3, 3, 3, 655241, 3, 5,
    11, 67, 3, 3, 3, 197, 3, 2141,
    3, 7, 5, 13, 3, 3, 5, 7,
    19, 3, 3, 3, 17, 5, 3, 375857,
    6529, 3, 3, 11, 3, 5, 43, 3,
    3, 17, 5, 8861, 3, 3, 30703, 3,
    5, 3, 7, 108929, 3, 41, 3, 3,
    3, 23, 3, 5, 3, 47, 11, 67,
    769, 3, 3, 3, 31, 7, 3, 19,
    3, 13, 3, 7, 5, 3, 2129, 23,
    3, 3, 5, 3, 3, 5, 3, 3,
    5, 3, 76387, 35069, 3, 173, 3, 3,
    3, 3, 3, 3, 5, 3, 3, 7,
    29, 3, 5, 3, 3, 17, 3, 5,
    3, 37, 127, 5, 19, 139, 3, 257,
    3, 13, 7, 3, 3, 5, 3, 79,
    3, 3, 5, 3, 1367, 3, 7, 2503,
    89, 3, 5, 3, 283, 31, 3, 13,
    3, 3, 19, 3, 101, 3, 3, 3,
    5, 405659, 3, 5, 3, 157, 3, 5,
    3, 7, 3, 3, 3, 5, 23, 3,
    37, 47, 3, 3, 43, 5, 3, 3,
    17, 3, 3, 73, 7, 191, 5, 11,
    3, 7, 5]

theorem prime_sub_2459 : Nat.Prime (838813974892 - 2459) := by
  show Nat.Prime 838813972433
  exact p838813972433

theorem check_2459 : allC 838813974892 2459 P10k ds_2459 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 838813974892 is 2459. -/
theorem minGB_S_2459 : minGB 838813974892 = 2459 :=
  minGB_eq_of P10k P10k_complete 838813974892 2459 (by norm_num) (by norm_num) prime_sub_2459 ds_2459 check_2459

def ds_2663 : List ℕ := [
    2, 11, 7, 3, 59, 3, 479, 3,
    47147, 5, 3, 3, 13, 3, 7, 483971,
    5, 3, 3, 743, 3, 3, 7873, 5,
    3, 19, 3, 7489, 3, 11, 3, 7,
    41, 3, 5, 3, 3, 3, 443, 7,
    5, 3, 17, 3, 13, 3, 3, 3,
    233, 3, 616547, 5, 3, 139, 7, 701,
    5, 3, 3, 35141, 3, 17, 3, 11,
    3, 94999, 3, 3, 971, 3, 13, 5,
    3, 3, 3, 7, 5, 3, 47, 3,
    5, 3, 13, 3, 3, 11, 5, 3,
    1123, 3, 7, 5, 3, 23, 3, 53,
    5, 31, 3, 3, 3, 19, 773, 5,
    3, 3, 13, 7, 5, 3, 3, 3,
    359, 3, 3, 11, 3, 347, 191, 5,
    3, 3, 7, 47, 3, 17, 3, 5,
    3, 3, 3, 13, 3, 3, 7, 3,
    11, 3, 397, 5, 3, 13, 3, 649613,
    3, 5, 3, 98533, 3, 223, 3, 449,
    3, 7, 3, 1151, 3, 5, 3, 25229,
    61, 107, 3, 7, 13, 41333, 3, 3,
    3, 7, 5, 3, 73, 3, 3, 5,
    3, 19577, 3, 3, 3, 16573, 3, 7,
    11, 5, 3, 3, 3, 43, 3, 10253,
    3, 7, 592309, 463247, 3, 3, 67, 7,
    5, 3, 3, 3, 5, 5281, 3, 928679,
    5, 3, 3, 11, 3, 7, 5, 3,
    3, 1427, 11, 151, 3, 3, 5, 3,
    59, 3, 7, 5, 3, 31, 3, 3,
    3, 37, 3, 1553, 3, 21401, 5, 87719,
    13, 3, 3, 3, 9511, 5, 3, 29,
    3, 19, 3, 7, 97, 3, 41, 5,
    3, 3, 31, 3, 3, 43, 3, 3,
    11, 3, 5, 17, 3, 23, 3, 3,
    3, 3, 3, 3, 83, 3, 3, 7,
    17, 3, 251, 3, 3, 23, 3, 373,
    3, 5, 37489, 73, 13, 593, 3, 5,
    3, 157, 5, 3, 3, 6221, 3, 149,
    3, 3, 11, 3, 5, 3, 7, 5,
    617, 3, 76679, 3, 5, 503, 3, 5,
    3, 3, 283, 3, 19, 3, 3, 3,
    163, 2879, 3, 107, 3, 6491, 3, 19,
    3, 7, 3, 3, 3, 1103, 5, 3,
    17, 5, 3, 3, 41, 7, 3, 3,
    13, 3, 3, 1213, 5, 53, 13267, 11,
    3, 7, 244997, 5, 3, 3, 1229, 3,
    3, 1091, 3, 2377, 5, 3, 3, 5,
    37, 3, 5, 3, 11, 379, 3, 47,
    3]

theorem prime_sub_2663 : Nat.Prime (1578084723724 - 2663) := by
  show Nat.Prime 1578084721061
  exact p1578084721061

theorem check_2663 : allC 1578084723724 2663 P10k ds_2663 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 1578084723724 is 2663. -/
theorem minGB_S_2663 : minGB 1578084723724 = 2663 :=
  minGB_eq_of P10k P10k_complete 1578084723724 2663 (by norm_num) (by norm_num) prime_sub_2663 ds_2663 check_2663

def ds_2837 : List ℕ := [
    2, 941, 7, 3, 5, 3, 73, 3,
    11, 223547, 3, 3, 5, 3, 7, 17,
    215329, 3, 3, 5, 3, 3, 59, 7,
    3, 5, 3, 1297, 3, 653, 3, 5,
    53, 3, 281, 3, 3, 3, 29, 7,
    131, 3, 5, 3, 173, 3, 3, 3,
    101, 3, 13, 19, 3, 5, 7, 1093,
    887, 3, 3, 5, 3, 503, 3, 5,
    3, 31, 3, 3, 691, 3, 11, 17,
    3, 3, 3, 7, 13, 3, 5, 3,
    11, 3, 5, 3, 3, 21143, 2897, 3,
    5, 3, 7, 23, 3, 5, 3, 31,
    7, 5, 3, 3, 3, 2251, 17, 709,
    3, 3, 74027, 7, 71, 3, 3, 3,
    11, 3, 3, 5, 3, 9311, 41, 67,
    3, 3, 7, 11, 3, 5, 3, 7,
    3, 3, 3, 379, 3, 3, 5, 3,
    53, 3, 5347, 19, 3, 5, 3, 719,
    3, 283, 3, 13, 3, 29, 3, 5,
    3, 7, 3, 5, 3, 7, 3, 5,
    11, 1030291, 3, 5, 43, 563, 3, 3,
    3, 7, 140627, 3, 5, 3, 3, 1217,
    3, 5, 3, 3, 3, 5, 3, 7,
    757, 5261, 3, 3, 3, 5, 3, 401,
    3, 5, 1787, 49207, 3, 3, 83, 7,
    491, 3, 3, 3, 251, 11, 3, 36017,
    97, 3, 3, 5, 3, 7, 12101, 3,
    3, 5, 1597, 4003, 3, 3, 11, 3,
    9491, 3, 7, 61, 3, 5, 3, 3,
    3, 5, 3, 157579, 3, 19, 59, 5,
    37, 3, 3, 3, 6337, 7, 3, 5,
    3, 17, 3, 5, 11, 3, 149969, 31,
    3, 3, 13, 3, 3, 261323, 3, 3,
    155303, 3, 17159, 5, 3, 29, 3, 3,
    3, 3, 3, 3, 17, 3, 3, 5,
    149, 3, 5417, 3, 3, 5, 3, 71,
    3, 17, 5, 29, 872671, 5, 3, 13,
    3, 47, 7, 3, 3, 23, 3, 11,
    3, 3, 13, 3, 163, 3, 7, 11,
    5, 3, 167, 3, 487, 5, 3, 41,
    3, 3, 5, 3, 1669, 3, 3, 3,
    59, 83, 3, 2063, 3, 137, 3, 11,
    3, 7, 3, 3, 3, 17, 599, 3,
    11, 13, 3, 3, 5, 7, 3, 3,
    5, 3, 3, 139, 7, 5, 13, 589219,
    3, 5, 271, 677, 3, 3, 587, 3,
    3, 5, 3, 1013, 23, 3, 3, 15161,
    5, 3, 7, 3, 5, 19, 3, 223217,
    3, 11, 3, 3, 3, 23, 3, 7,
    1090757, 3, 5, 3, 3, 11, 3, 5,
    3, 6653, 3, 7, 427169, 3, 3, 5,
    3, 7, 3]

theorem prime_sub_2837 : Nat.Prime (2541246752056 - 2837) := by
  show Nat.Prime 2541246749219
  exact p2541246749219

theorem check_2837 : allC 2541246752056 2837 P10k ds_2837 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 2541246752056 is 2837. -/
theorem minGB_S_2837 : minGB 2541246752056 = 2837 :=
  minGB_eq_of P10k P10k_complete 2541246752056 2837 (by norm_num) (by norm_num) prime_sub_2837 ds_2837 check_2837

def ds_2963 : List ℕ := [
    2, 7, 19, 3, 1009, 3, 7, 3,
    677, 5, 3, 3, 13, 3, 7121, 141833,
    5, 3, 3, 73, 3, 3, 269, 5,
    3, 7, 3, 23, 3, 2539, 3, 11,
    5749, 3, 5, 3, 3, 3, 7993, 1777,
    5, 3, 53, 3, 11, 3, 3, 3,
    7, 3, 19, 5, 3, 61, 79, 11,
    5, 3, 3, 17, 3, 331, 3, 7,
    3, 67, 3, 3, 19, 3, 7, 5,
    3, 3, 3, 17, 5, 3, 311, 3,
    5, 3, 13, 3, 3, 29, 5, 3,
    11, 3, 1237, 5, 3, 929, 3, 43,
    5, 7, 3, 3, 3, 193, 7, 5,
    3, 3, 13, 11, 5, 3, 3, 3,
    29, 3, 3, 41, 3, 7, 8209, 5,
    3, 3, 109453, 163, 3, 31, 3, 5,
    3, 3, 3, 13, 3, 3, 43, 3,
    7, 3, 23, 5, 3, 13, 3, 53,
    3, 5, 3, 7, 3, 157, 3, 601,
    3, 31, 3, 251, 3, 5, 3, 7,
    71, 10357, 3, 607, 13, 7, 3, 3,
    3, 32869, 5, 3, 19, 3, 3, 5,
    3, 47, 3, 3, 3, 233, 3, 17,
    571, 5, 3, 3, 3, 7, 3, 907,
    3, 983, 11, 7, 3, 3, 2221, 59,
    5, 3, 3, 3, 5, 7, 3, 449,
    5, 3, 3, 17, 3, 307009, 5, 3,
    3, 7, 13, 19, 3, 3, 5, 3,
    353, 3, 255887, 5, 3, 11, 3, 3,
    3, 4261, 3, 7, 3, 142757, 5, 4091,
    13, 3, 3, 3, 479, 5, 3, 7,
    3, 11, 3, 13, 17, 3, 7, 5,
    3, 3, 673, 3, 3, 33863, 3, 3,
    7, 3, 5, 149, 3, 34171, 3, 3,
    3, 3, 3, 3, 4729, 3, 3, 17,
    7, 3, 11, 3, 3, 41, 3, 236107,
    3, 5, 23, 7, 11, 59, 3, 5,
    3, 401, 5, 3, 3, 103, 3, 31,
    3, 3, 457381, 3, 5, 3, 83, 5,
    61, 3, 97, 3, 5, 11, 3, 5,
    3, 3, 107, 3, 79, 3, 3, 3,
    46807, 2819, 3, 101, 3, 7, 3, 311,
    3, 323759, 3, 3, 3, 720497, 5, 3,
    223, 5, 3, 3, 1223, 29, 3, 3,
    13, 3, 3, 358879, 5, 7, 53, 17,
    3, 11, 37, 5, 3, 3, 151, 3,
    3, 29, 3, 199, 5, 3, 3, 5,
    23, 3, 5, 3, 7, 773, 3, 239,
    3, 7, 3, 3, 3, 1164533, 3, 13,
    5, 3, 375899, 3, 3, 5, 3, 19,
    3, 47, 3, 88339, 5, 3, 3, 859279,
    3, 5, 3, 11, 101, 3, 3, 5393,
    5, 3, 506213, 11, 5, 3, 13, 5,
    3, 7]

theorem prime_sub_2963 : Nat.Prime (3228317220754 - 2963) := by
  show Nat.Prime 3228317217791
  exact p3228317217791

theorem check_2963 : allC 3228317220754 2963 P10k ds_2963 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 3228317220754 is 2963. -/
theorem minGB_S_2963 : minGB 3228317220754 = 2963 :=
  minGB_eq_of P10k P10k_complete 3228317220754 2963 (by norm_num) (by norm_num) prime_sub_2963 ds_2963 check_2963

def ds_2969 : List ℕ := [
    2, 5, 383, 3, 67, 3, 569897, 3,
    5, 11, 3, 3, 7, 3, 347, 5,
    35837, 3, 3, 40129, 3, 3, 5, 4549,
    3, 23, 3, 28123, 3, 5, 3, 83,
    19, 3, 41, 3, 3, 3, 7, 5,
    47, 3, 13, 3, 1823, 3, 3, 3,
    11, 3, 5, 23, 3, 7, 28559, 5,
    13, 3, 3, 1637, 3, 5, 3, 773,
    3, 419, 3, 3, 13, 3, 5, 11,
    3, 3, 3, 5, 17, 3, 197, 3,
    7, 3, 859, 3, 3, 5, 4567, 3,
    7, 3, 37, 19, 3, 11, 3, 5,
    72337, 89003, 3, 3, 3, 11, 5, 277,
    3, 3, 7, 5, 31, 3, 3, 3,
    101, 3, 3, 41, 3, 2382817, 5, 13,
    3, 3, 709, 5, 3, 887, 3, 1097,
    3, 3, 3, 5, 3, 3, 2113, 3,
    5, 3, 7, 59, 3, 11, 3, 227,
    3, 7, 3, 149, 3, 5, 3, 7,
    3, 11, 3, 37, 3, 23, 3, 57559,
    1747, 5, 3, 13, 3463, 5, 3, 3,
    3, 5, 11, 3, 61, 3, 3, 7,
    3, 6907, 3, 3, 3, 7, 3, 87767,
    5, 151, 3, 3, 3, 11, 3, 5,
    3, 43, 157, 5, 3, 3, 7, 5,
    2054089, 3, 3, 3, 7, 19, 3, 5,
    3299, 3, 3, 7, 3, 17, 163, 3,
    3, 13, 223, 5, 3, 3, 17, 3,
    7, 3, 5, 13, 3, 8377, 3, 3,
    3, 11, 3, 449, 3, 5, 421, 7,
    5, 3, 3, 3, 5, 29, 3, 89,
    3, 5, 3, 1353259, 79, 3, 5, 19,
    3, 3, 7, 3, 3, 2579, 3, 3,
    43, 3, 6491, 7, 3, 5, 3, 3,
    3, 3, 3, 3, 18311, 3, 3, 11,
    5, 3, 7, 3, 3, 41, 3, 11,
    3, 7, 31, 13, 5, 7, 3, 877,
    3, 5, 295951, 3, 3, 239, 3, 5,
    3, 3, 5861, 3, 349, 3, 5, 99139,
    29, 3, 31, 3, 7, 863, 3, 61,
    3, 3, 7, 3, 5, 3, 3, 3,
    11, 5, 3, 6803, 3, 5, 3, 7,
    3, 5, 3, 3, 3, 13, 7, 3,
    5, 11, 3, 3, 7, 397, 3, 3,
    52561, 3, 3, 5, 54779, 75539, 19, 5,
    3, 541, 23, 31, 3, 3, 7, 3,
    3, 13, 3, 5, 8147, 3, 3, 59,
    547, 3, 13, 3, 83, 5, 3, 470957,
    3, 5, 3, 3, 3, 7, 3, 5,
    1418453, 3, 1330103, 3, 3, 7, 3, 389,
    3, 5, 3, 29, 2275813, 3, 3, 11,
    3, 127, 3, 17, 5, 3, 3, 23,
    373, 3, 7, 5, 37, 3, 19603, 7,
    3, 7879, 5]

theorem prime_sub_2969 : Nat.Prime (6046500599278 - 2969) := by
  show Nat.Prime 6046500596309
  exact p6046500596309

theorem check_2969 : allC 6046500599278 2969 P10k ds_2969 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 6046500599278 is 2969. -/
theorem minGB_S_2969 : minGB 6046500599278 = 2969 :=
  minGB_eq_of P10k P10k_complete 6046500599278 2969 (by norm_num) (by norm_num) prime_sub_2969 ds_2969 check_2969

def ds_3023 : List ℕ := [
    2, 43, 898673, 3, 7, 3, 3989, 3,
    13, 5, 3, 3, 1019, 3, 17, 7,
    5, 3, 3, 23, 3, 3, 911, 5,
    3, 11, 3, 2267, 3, 19, 3, 173,
    7, 3, 5, 3, 3, 3, 11, 83,
    5, 3, 7297, 3, 929, 3, 3, 3,
    19, 3, 11, 5, 3, 17, 13, 7,
    5, 3, 3, 37, 3, 26713, 3, 11119,
    3, 127, 3, 3, 7, 3, 17, 5,
    3, 3, 3, 47, 5, 3, 59, 3,
    5, 3, 7, 3, 3, 47149, 5, 3,
    89, 3, 6133, 5, 3, 13, 3, 37,
    5, 896111, 3, 3, 3, 7, 11, 5,
    3, 3, 1187, 33851, 5, 3, 3, 3,
    31, 3, 3, 7, 3, 13, 353, 5,
    3, 3, 271, 7, 3, 53, 3, 5,
    3, 3, 3, 1171, 3, 3, 11, 3,
    1811, 3, 19, 5, 3, 239873, 3, 11,
    3, 5, 3, 3643, 3, 17, 3, 13,
    3, 5821, 3, 19, 3, 5, 3, 1021,
    37, 101, 3, 197, 7, 239, 3, 3,
    3, 2557, 5, 3, 8447, 3, 3, 5,
    3, 7, 3, 3, 3, 11, 3, 71,
    7, 5, 3, 3, 3, 131, 3, 1129,
    3, 337, 7, 13, 3, 3, 139, 11,
    5, 3, 3, 3, 5, 29, 3, 158407,
    5, 3, 3, 12451, 3, 3307, 5, 3,
    3, 31, 19, 17, 3, 3, 5, 3,
    13, 3, 92861, 5, 3, 23, 3, 3,
    3, 7, 3, 11, 3, 13469, 5, 47,
    7, 3, 3, 3, 11, 5, 3, 347,
    3, 13, 3, 9421, 7, 3, 37, 5,
    3, 3, 43, 3, 3, 83, 3, 3,
    193, 3, 5, 521, 3, 7, 3, 3,
    3, 3, 3, 3, 4561, 3, 3, 41,
    19, 3, 937, 3, 3, 9857, 3, 2503507,
    3, 5, 7, 128449, 4493, 137, 3, 5,
    3, 13, 5, 3, 3, 151, 3, 23,
    3, 3, 7, 3, 5, 3, 89, 5,
    11, 3, 17, 3, 5, 7, 3, 5,
    3, 3, 23, 3, 7, 3, 3, 3,
    13, 11, 3, 7, 3, 6551, 3, 787,
    3, 179, 3, 3, 3, 22091, 5, 3,
    2953, 5, 3, 3, 443, 47, 3, 3,
    103, 3, 3, 17, 5, 11, 23, 113,
    3, 13, 7, 5, 3, 3, 11, 3,
    3, 7, 3, 11, 5, 3, 3, 5,
    62143, 3, 5, 3, 19, 2371, 3, 7,
    3, 31, 3, 3, 3, 9151, 3, 23,
    5, 3, 9733, 3, 3, 5, 3, 7,
    3, 13, 3, 683, 5, 3, 3, 17,
    3, 5, 3, 56923, 29, 3, 3, 15731,
    5, 3, 1451, 17, 5, 3, 43, 5,
    3, 811, 19, 5, 3, 5, 3, 1039,
    3]

theorem prime_sub_3023 : Nat.Prime (7119550817194 - 3023) := by
  show Nat.Prime 7119550814171
  exact p7119550814171

theorem check_3023 : allC 7119550817194 3023 P10k ds_3023 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 7119550817194 is 3023. -/
theorem minGB_S_3023 : minGB 7119550817194 = 3023 :=
  minGB_eq_of P10k P10k_complete 7119550817194 3023 (by norm_num) (by norm_num) prime_sub_3023 ds_3023 check_3023

def ds_3137 : List ℕ := [
    2, 2789, 19, 3, 17351, 3, 97, 3,
    13, 5, 3, 3, 7, 3, 941, 139,
    5, 3, 3, 199, 3, 3, 7, 5,
    3, 13, 3, 4561, 3, 127, 3, 29,
    331, 3, 5, 3, 3, 3, 7, 56443,
    5, 3, 11, 3, 37, 3, 3, 3,
    131, 3, 19, 5, 3, 7, 11, 5099,
    5, 3, 3, 61, 3, 7, 3, 101,
    3, 23, 3, 3, 19, 3, 568523, 5,
    3, 3, 3, 971, 5, 3, 79, 3,
    5, 3, 7933, 3, 3, 47, 5, 3,
    7, 3, 71789, 5, 3, 13, 3, 7,
    5, 11, 3, 3, 3, 5347, 293, 5,
    3, 3, 7, 23, 5, 3, 3, 3,
    247873, 3, 3, 31, 3, 13, 11, 5,
    3, 3, 479, 223, 3, 17, 3, 5,
    3, 3, 3, 22273, 3, 3, 653, 3,
    2111, 3, 7, 5, 3, 103, 3, 29,
    3, 5, 3, 173, 3, 37, 3, 7,
    3, 139, 3, 1874153, 3, 5, 3, 1361,
    163, 43, 3, 983, 181, 11, 3, 3,
    3, 31, 5, 3, 19, 3, 3, 5,
    3, 317, 3, 3, 3, 7, 3, 71387,
    1202987, 5, 3, 3, 3, 2393291, 3, 59,
    3, 11, 89, 13, 3, 3, 7, 13591,
    5, 3, 3, 3, 5, 593, 3, 23,
    5, 3, 3, 7, 3, 37, 5, 3,
    3, 557, 239, 19, 3, 3, 5, 3,
    7, 3, 2221, 5, 3, 2897, 3, 3,
    3, 243367, 3, 19, 3, 10267, 5, 7,
    29, 3, 3, 3, 7, 5, 3, 31,
    3, 13, 3, 19, 4649, 3, 573143, 5,
    3, 3, 7, 3, 3, 53, 3, 3,
    23, 3, 5, 7, 3, 2029, 3, 3,
    3, 3, 3, 3, 3019, 3, 3, 229,
    17, 3, 7, 3, 3, 29, 3, 1493,
    3, 5, 24077, 11, 149, 7, 3, 5,
    3, 7, 5, 3, 3, 1823, 3, 1051,
    3, 3, 17, 3, 5, 3, 71, 5,
    311, 3, 67, 3, 5, 23, 3, 5,
    3, 3, 7, 3, 1709, 3, 3, 3,
    13, 977, 3, 11, 3, 43, 3, 7,
    3, 1931, 3, 3, 3, 79, 5, 3,
    17, 5, 3, 3, 7, 617, 3, 3,
    823, 3, 3, 7, 5, 102611, 37, 673,
    3, 13, 6823, 5, 3, 3, 7, 3,
    3, 389, 3, 683, 5, 3, 3, 5,
    1193, 3, 5, 3, 53, 11, 3, 1039,
    3, 23, 3, 3, 3, 7, 3, 50647,
    5, 3, 45569, 3, 3, 5, 3, 17,
    3, 13, 3, 1063, 5, 3, 3, 23,
    3, 5, 3, 449, 17, 3, 3, 37,
    5, 3, 7, 163, 5, 3, 97, 5,
    3, 2437, 11, 5, 3, 5, 3, 1502551,
    3, 7, 3, 191, 3, 3, 3, 3,
    19, 5, 3, 5, 3]

theorem prime_sub_3137 : Nat.Prime (7405567522324 - 3137) := by
  show Nat.Prime 7405567519187
  exact p7405567519187

theorem check_3137 : allC 7405567522324 3137 P10k ds_3137 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 7405567522324 is 3137. -/
theorem minGB_S_3137 : minGB 7405567522324 = 3137 :=
  minGB_eq_of P10k P10k_complete 7405567522324 3137 (by norm_num) (by norm_num) prime_sub_3137 ds_3137 check_3137

def ds_3203 : List ℕ := [
    2, 13, 953, 3, 417671, 3, 2053, 3,
    8069, 5, 3, 3, 29, 3, 2398273, 11,
    5, 3, 3, 7, 3, 3, 19, 5,
    3, 23, 3, 13, 3, 7, 3, 41,
    17, 3, 5, 3, 3, 3, 521, 1103,
    5, 3, 673, 3, 7, 3, 3, 3,
    557, 3, 1255201, 5, 3, 11, 47, 13,
    5, 3, 3, 7, 3, 3049, 3, 19,
    3, 11, 3, 3, 439, 3, 79, 5,
    3, 3, 3, 11, 5, 3, 3361, 3,
    5, 3, 547, 3, 3, 17, 5, 3,
    127, 3, 101, 5, 3, 7, 3, 5953,
    5, 31, 3, 3, 3, 829, 29, 5,
    3, 3, 1091, 37, 5, 3, 3, 3,
    7, 3, 3, 367, 3, 11, 13, 5,
    3, 3, 163, 52529, 3, 7, 3, 5,
    3, 3, 3, 7, 3, 3, 2882489, 3,
    509, 3, 1867249, 5, 3, 47, 3, 7,
    3, 5, 3, 269, 3, 1531, 3, 19,
    3, 13, 3, 7, 3, 5, 3, 71,
    1885859, 7, 3, 1319, 11, 21323, 3, 3,
    3, 89, 5, 3, 401, 3, 3, 5,
    3, 43, 3, 3, 3, 197, 3, 149,
    47, 5, 3, 3, 3, 61, 3, 7,
    3, 2909, 59, 3907, 3, 3, 349, 19,
    5, 3, 3, 3, 5, 13, 3, 307,
    5, 3, 3, 79, 3, 11, 5, 3,
    3, 17, 71, 7, 3, 3, 5, 3,
    463, 3, 13, 5, 3, 19, 3, 3,
    3, 23, 3, 373, 3, 216901, 5, 13,
    661, 3, 3, 3, 2719, 5, 3, 11,
    3, 7, 3, 971, 29, 3, 3413, 5,
    3, 3, 11, 3, 3, 7, 3, 3,
    619, 3, 5, 433, 3, 6781, 3, 3,
    3, 3, 3, 3, 157349, 3, 3, 113,
    13, 3, 1033, 3, 3, 17, 3, 7,
    3, 5, 11, 19, 73, 757, 3, 5,
    3, 17, 5, 3, 3, 1489, 3, 7,
    3, 3, 1297, 3, 5, 3, 83, 5,
    67, 3, 7, 3, 5, 75583, 3, 5,
    3, 3, 1841849, 3, 901273, 3, 3, 3,
    31091, 7, 3, 11087, 3, 311, 3, 137,
    3, 197, 3, 3, 3, 7, 5, 3,
    257, 5, 3, 3, 43, 797, 3, 3,
    7, 3, 3, 34501, 5, 467, 265987, 7,
    3, 1279, 13, 5, 3, 3, 19, 3,
    3, 227, 3, 11261, 5, 3, 3, 5,
    7, 3, 5, 3, 857249, 7, 3, 379,
    3, 263, 3, 3, 3, 17, 3, 11,
    5, 3, 8209, 3, 3, 5, 3, 1051,
    3, 31, 3, 4603, 5, 3, 3, 7,
    3, 5, 3, 13, 7, 3, 3, 23,
    5, 3, 1459, 331, 5, 3, 7, 5,
    3, 11, 53, 5, 3, 5, 3, 7,
    3, 11, 3, 743, 3, 3, 3, 3,
    41, 5, 3, 5, 3, 7, 3, 113,
    3, 3, 3, 48823]

theorem prime_sub_3203 : Nat.Prime (10770353852014 - 3203) := by
  show Nat.Prime 10770353848811
  exact p10770353848811

theorem check_3203 : allC 10770353852014 3203 P10k ds_3203 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 10770353852014 is 3203. -/
theorem minGB_S_3203 : minGB 10770353852014 = 3203 :=
  minGB_eq_of P10k P10k_complete 10770353852014 3203 (by norm_num) (by norm_num) prime_sub_3203 ds_3203 check_3203

def ds_3323 : List ℕ := [
    2, 7, 1559, 3, 5, 3, 7, 3,
    281, 103, 3, 3, 5, 3, 11, 19,
    7, 3, 3, 5, 3, 3, 23, 16421,
    3, 5, 3, 499, 3, 11, 3, 5,
    1780459, 3, 17, 3, 3, 3, 19, 199,
    11, 3, 5, 3, 13, 3, 3, 3,
    7, 3, 59, 47, 3, 5, 29, 34141,
    7, 3, 3, 5, 3, 1207033, 3, 5,
    3, 12511, 3, 3, 197, 3, 7, 23,
    3, 3, 3, 107, 157, 3, 5, 3,
    83, 3, 5, 3, 3, 11, 89, 3,
    5, 3, 61, 7, 3, 5, 3, 1169281,
    11, 5, 3, 3, 3, 17, 7, 167,
    3, 3, 13, 3299, 37, 3, 3, 3,
    9277, 3, 3, 5, 3, 7, 570839, 17,
    3, 3, 1999, 647, 3, 5, 3, 172787,
    3, 3, 3, 13, 3, 3, 5, 3,
    7, 3, 2214161, 397, 3, 5, 3, 131,
    3, 11, 3, 7, 3, 17, 3, 5,
    3, 205529, 3, 5, 3, 31, 3, 5,
    101, 29, 3, 5, 13, 7, 3, 3,
    3, 263, 6229, 3, 5, 3, 3, 23,
    3, 5, 3, 3, 3, 5, 3, 524053,
    11, 7, 3, 3, 3, 5, 3, 53,
    3, 5, 23, 7, 3, 3, 311, 796937,
    73, 3, 3, 3, 223, 7, 3, 1165121,
    13, 3, 3, 5, 3, 19, 7, 3,
    3, 5, 11, 17, 3, 3, 1301, 3,
    8377, 3, 11, 283, 3, 5, 3, 3,
    3, 5, 3, 7, 3, 269, 11, 5,
    13, 3, 3, 3, 101, 11027, 3, 5,
    3, 1291, 3, 5, 953, 3, 7, 4253,
    3, 3, 71, 3, 3, 73, 3, 3,
    7, 3, 37, 5, 3, 18289, 3, 3,
    3, 3, 3, 3, 251, 3, 3, 5,
    7, 3, 1033, 3, 3, 5, 3, 19,
    3, 62047, 5, 7, 13, 5, 3, 7,
    3, 809, 67, 3, 3, 29, 3, 59,
    3, 3, 11, 3, 9929, 3, 71, 13,
    5, 3, 17, 3, 2496097, 5, 3, 1426429,
    3, 3, 5, 3, 23, 3, 3, 3,
    4001, 47, 3, 233, 3, 7, 3, 463,
    3, 157, 3, 3, 3, 61, 107, 3,
    19, 137, 3, 3, 5, 11, 3, 3,
    5, 3, 3, 17, 131, 5, 31, 11,
    3, 5, 19, 13, 3, 3, 307, 3,
    3, 5, 3, 73, 13421, 3, 3, 7,
    5, 3, 571, 3, 5, 254791, 3, 1093,
    3, 7, 3, 3, 3, 11, 3, 13,
    17, 3, 5, 3, 3, 901547, 3, 5,
    3, 11, 3, 47, 7, 3, 3, 5,
    3, 11, 3, 34877, 23, 3, 3, 5,
    8521, 3, 569, 17, 83, 3, 13, 33641,
    3, 7, 7103, 239, 3, 7, 3, 5,
    3, 173, 3, 5, 3, 3, 3, 3,
    7, 15287, 3, 23, 3, 151, 3, 7,
    3, 3, 3, 5, 789491, 7, 3, 5,
    3, 5, 3, 23, 3, 3, 661, 3,
    3, 3, 3]

theorem prime_sub_3323 : Nat.Prime (17455158897256 - 3323) := by
  show Nat.Prime 17455158893933
  exact p17455158893933

theorem check_3323 : allC 17455158897256 3323 P10k ds_3323 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 17455158897256 is 3323. -/
theorem minGB_S_3323 : minGB 17455158897256 = 3323 :=
  minGB_eq_of P10k P10k_complete 17455158897256 3323 (by norm_num) (by norm_num) prime_sub_3323 ds_3323 check_3323

def ds_3449 : List ℕ := [
    2, 5, 11, 3, 59, 3, 29, 3,
    5, 7, 3, 3, 17, 3, 53, 5,
    286103, 3, 3, 7, 3, 3, 5, 31,
    3, 19, 3, 13, 3, 5, 3, 1361,
    11, 3, 229, 3, 3, 3, 479, 5,
    443, 3, 29, 3, 7, 3, 3, 3,
    735653, 3, 5, 7, 3, 313, 47, 5,
    11, 3, 3, 7, 3, 5, 3, 557,
    3, 647, 3, 3, 17, 3, 5, 349,
    3, 3, 3, 5, 233, 3, 11, 3,
    13, 3, 37, 3, 3, 5, 7, 3,
    31, 3, 11, 4051, 3, 7, 3, 5,
    691, 1693, 3, 3, 3, 19, 5, 251,
    3, 3, 1399, 5, 11, 3, 3, 3,
    7, 3, 3, 599, 3, 31, 5, 7,
    3, 3, 2003, 5, 3, 7, 3, 59,
    3, 3, 3, 5, 3, 3, 23, 3,
    5, 3, 11, 13, 3, 41, 3, 7,
    3, 143567, 3, 17, 3, 5, 3, 11059,
    3, 13, 3, 7, 3, 11, 3, 109,
    127, 5, 3, 79, 2033021, 5, 3, 3,
    3, 5, 31, 3, 101, 3, 3, 29303,
    3, 11, 3, 3, 3, 2803, 3, 37,
    5, 417271, 3, 3, 3, 6703, 3, 5,
    3, 199, 179, 5, 3, 3, 48947, 5,
    353, 3, 3, 3, 11, 13, 3, 5,
    7, 3, 3, 67, 3, 4973, 37, 3,
    3, 6247, 17, 5, 3, 3, 29, 3,
    59, 3, 5, 1213, 3, 23, 3, 3,
    3, 1481, 3, 33331, 3, 5, 7, 13,
    5, 3, 3, 3, 5, 41, 3, 17,
    3, 5, 3, 1433, 2452487, 3, 5, 116731,
    3, 3, 53, 3, 3, 7, 3, 3,
    19, 3, 7, 11, 3, 5, 3, 3,
    3, 3, 3, 3, 11, 3, 3, 19,
    5, 3, 3389, 3, 3, 223, 3, 7,
    3, 1067537, 13, 139, 5, 29, 3, 31,
    3, 5, 13, 3, 3, 173, 3, 5,
    3, 3, 697681, 3, 19, 3, 5, 193,
    17, 3, 7, 3, 367, 1163, 3, 7,
    3, 3, 23, 3, 5, 3, 3, 3,
    37, 5, 3, 281, 3, 5, 3, 19,
    3, 5, 3, 3, 3, 7, 89, 3,
    5, 7, 3, 3, 5347, 2039, 3, 3,
    7, 3, 3, 5, 19501, 38177, 23, 5,
    3, 97, 11, 11867, 3, 3, 683, 3,
    3, 1237, 3, 5, 7, 3, 3, 11,
    7, 3, 19, 3, 71, 5, 3, 661,
    3, 5, 3, 3, 3, 401, 3, 5,
    2321531, 3, 11, 3, 3, 1771493, 3, 139,
    3, 5, 3, 11, 41, 3, 3, 7,
    3, 61, 3, 13, 5, 3, 3, 1151,
    31, 3, 17, 5, 11, 3, 7, 736871,
    3, 1451, 5, 7, 3, 17, 3, 7,
    3, 5, 3, 11, 3, 3, 3, 3,
    5, 67601, 3, 131, 3, 7, 3, 1607,
    3, 3, 3, 577, 5, 43, 3, 7,
    3, 31, 3, 2240807, 3, 3, 397, 3,
    3, 3, 3, 5, 191, 3, 3, 7,
    47, 3, 11, 3, 7, 3, 17, 5,
    3]

theorem prime_sub_3449 : Nat.Prime (18566952590488 - 3449) := by
  show Nat.Prime 18566952587039
  exact p18566952587039

theorem check_3449 : allC 18566952590488 3449 P10k ds_3449 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 18566952590488 is 3449. -/
theorem minGB_S_3449 : minGB 18566952590488 = 3449 :=
  minGB_eq_of P10k P10k_complete 18566952590488 3449 (by norm_num) (by norm_num) prime_sub_3449 ds_3449 check_3449

def ds_3557 : List ℕ := [
    2, 7, 4057, 3, 53, 3, 7, 3,
    11, 5, 3, 3, 47, 3, 139, 71,
    5, 3, 3, 192581, 3, 3, 111977, 5,
    3, 7, 3, 1097903, 3, 37, 3, 23,
    13, 3, 5, 3, 3, 3, 12983, 19,
    5, 3, 528127, 3, 233, 3, 3, 3,
    7, 3, 89, 5, 3, 31, 421, 447893,
    5, 3, 3, 59, 3, 13, 3, 7,
    3, 67, 3, 3, 82217, 3, 7, 5,
    3, 3, 3, 5273683, 5, 3, 19, 3,
    5, 3, 43, 3, 3, 491, 5, 3,
    3119783, 3, 29, 5, 3, 8527, 3, 86959,
    5, 7, 3, 3, 3, 37, 7, 5,
    3, 3, 2782421, 131, 5, 3, 3, 3,
    11, 3, 3, 29, 3, 7, 41, 5,
    3, 3, 1108123, 11, 3, 1499, 3, 5,
    3, 3, 3, 19, 3, 3, 13, 3,
    7, 3, 453367, 5, 3, 23, 3, 1373,
    3, 5, 3, 7, 3, 683, 3, 11,
    3, 47, 3, 331, 3, 5, 3, 7,
    11, 7237, 3, 19, 197, 7, 3, 3,
    3, 11, 5, 3, 405991, 3, 3, 5,
    3, 157, 3, 3, 3, 3163, 3, 23,
    103, 5, 3, 3, 3, 7, 3, 29,
    3, 31, 2311, 7, 3, 3, 1049, 37,
    5, 3, 3, 3, 5, 7, 3, 53,
    5, 3, 3, 89, 3, 13, 5, 3,
    3, 7, 31, 23, 3, 3, 5, 3,
    19, 3, 11621, 5, 3, 47, 3, 3,
    3, 323549, 3, 7, 3, 347, 5, 23,
    67, 3, 3, 3, 31, 5, 3, 7,
    3, 1613, 3, 53, 11, 3, 7, 5,
    3, 3, 41, 3, 3, 37, 3, 3,
    7, 3, 5, 43, 3, 47, 3, 3,
    3, 3, 3, 3, 23, 3, 3, 149,
    7, 3, 2129279, 3, 3, 11, 3, 293,
    3, 5, 1063, 7, 143971, 13, 3, 5,
    3, 1493, 5, 3, 3, 19, 3, 11,
    3, 3, 13187, 3, 5, 3, 23, 5,
    1027931, 3, 13, 3, 5, 19, 3, 5,
    3, 3, 211, 3, 38833, 3, 3, 3,
    29, 557, 3, 43, 3, 7, 3, 11,
    3, 79, 3, 3, 3, 31, 5, 3,
    11, 5, 3, 3, 337, 3446687, 3, 3,
    29, 3, 3, 4363, 5, 7, 277, 163,
    3, 621337, 173, 5, 3, 3, 13, 3,
    3, 11, 3, 467, 5, 3, 3, 5,
    457, 3, 5, 3, 7, 13, 3, 113,
    3, 7, 3, 3, 3, 739, 3, 120623,
    5, 3, 13, 3, 3, 5, 3, 101,
    3, 23, 3, 37, 5, 3, 3, 250501,
    3, 5, 3, 73, 1447, 3, 3, 11,
    5, 3, 331, 29, 5, 3, 11, 5,
    3, 7, 1591417, 5, 3, 5, 3, 43,
    3, 13, 3, 7, 3, 3, 3, 3,
    7, 5, 3, 5, 3, 19, 3, 7,
    3, 3, 3, 11, 3371, 5, 3, 37,
    3, 7, 3, 11, 3, 3, 5, 3,
    3, 3, 3, 11, 5, 3, 3, 101,
    5, 3, 1951, 3, 5, 3, 151, 13,
    3, 5, 3, 7, 3, 59, 3, 13,
    3, 3, 3, 43, 3, 67, 5, 3,
    3]

theorem prime_sub_3557 : Nat.Prime (36361448359204 - 3557) := by
  show Nat.Prime 36361448355647
  exact p36361448355647

theorem check_3557 : allC 36361448359204 3557 P10k ds_3557 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 36361448359204 is 3557. -/
theorem minGB_S_3557 : minGB 36361448359204 = 3557 :=
  minGB_eq_of P10k P10k_complete 36361448359204 3557 (by norm_num) (by norm_num) prime_sub_3557 ds_3557 check_3557

def ds_3659 : List ℕ := [
    2, 5, 19, 3, 13, 3, 1999, 3,
    5, 7, 3, 3, 53, 3, 11, 5,
    907, 3, 3, 7, 3, 3, 5, 13,
    3, 139, 3, 23, 3, 5, 3, 11059,
    43, 3, 29, 3, 3, 3, 13, 5,
    11, 3, 179, 3, 7, 3, 3, 3,
    2521, 3, 5, 7, 3, 79493, 353, 5,
    659, 3, 3, 7, 3, 5, 3, 11,
    3, 149, 3, 3, 19, 3, 5, 53,
    3, 3, 3, 5, 563, 3, 13, 3,
    103, 3, 367, 3, 3, 5, 7, 3,
    19, 3, 9319, 13, 3, 7, 3, 5,
    11, 23, 3, 3, 3, 13, 5, 37,
    3, 3, 1693, 5, 119047, 3, 3, 3,
    7, 3, 3, 11, 3, 73, 5, 7,
    3, 3, 53, 5, 3, 7, 3, 160507,
    3, 3, 3, 5, 3, 3, 3923, 3,
    5, 3, 23, 17, 3, 51169, 3, 7,
    3, 11, 3, 229, 3, 5, 3, 919,
    3, 59, 3, 7, 3, 127, 3, 173,
    13, 5, 3, 11, 452009, 5, 3, 3,
    3, 5, 29, 3, 19, 3, 3, 313991,
    3, 251, 3, 3, 3, 131, 3, 239,
    5, 47, 3, 3, 3, 1291, 3, 5,
    3, 13, 35279, 5, 3, 3, 17, 5,
    6547, 3, 3, 3, 13, 41, 3, 5,
    7, 3, 3, 11, 3, 1811, 17, 3,
    3, 79, 11, 5, 3, 3, 375251, 3,
    43, 3, 5, 2663, 3, 31, 3, 3,
    3, 3604891, 3, 19, 3, 5, 7, 2083,
    5, 3, 3, 3, 5, 1733, 3, 13,
    3, 5, 3, 19, 83, 3, 5, 877,
    3, 3, 31, 3, 3, 7, 3, 3,
    11, 3, 7, 113, 3, 5, 3, 3,
    3, 3, 3, 3, 941, 3, 3, 983,
    5, 3, 89, 3, 3, 101, 3, 7,
    3, 29, 23, 312047, 5, 17, 3, 53,
    3, 5, 173, 3, 3, 5495053, 3, 5,
    3, 3, 11, 3, 13, 3, 5, 61861,
    7001, 3, 7, 3, 871963, 43801, 3, 7,
    3, 3, 4079, 3, 5, 3, 3, 3,
    4021, 5, 3, 17, 3, 5, 3, 53,
    3, 5, 3, 3, 3, 7, 79, 3,
    5, 7, 3, 3, 13, 11, 3, 3,
    7, 3, 3, 5, 19, 29, 457, 5,
    3, 17, 157303, 43, 3, 3, 101, 3,
    3, 107, 3, 5, 7, 3, 3, 4410187,
    7, 3, 109, 3, 11, 5, 3, 59,
    3, 5, 3, 3, 3, 11, 3, 5,
    211, 3, 1787, 3, 3, 23, 3, 13,
    3, 5, 3, 61, 37, 3, 3, 7,
    3, 11, 3, 73, 5, 3, 3, 1869029,
    22643, 3, 13, 5, 71, 3, 7, 31,
    3, 437191, 5, 7, 3, 41, 3, 7,
    3, 5, 3, 607, 3, 3, 3, 3,
    5, 233, 3, 138181, 3, 7, 3, 1231,
    3, 3, 3, 257, 5, 13, 3, 7,
    3, 719, 3, 17, 3, 3, 17321, 3,
    3, 3, 3, 5, 1181, 3, 3, 7,
    17, 3, 401, 3, 7, 3, 683, 5,
    3, 89, 3, 17, 3, 34981, 3, 41,
    3, 3, 3, 5437, 3, 5, 19, 3,
    3, 7, 3, 3, 419, 3, 5, 3,
    3, 181, 5, 3, 3, 3]

theorem prime_sub_3659 : Nat.Prime (39028377647218 - 3659) := by
  show Nat.Prime 39028377643559
  exact p39028377643559

theorem check_3659 : allC 39028377647218 3659 P10k ds_3659 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 39028377647218 is 3659. -/
theorem minGB_S_3659 : minGB 39028377647218 = 3659 :=
  minGB_eq_of P10k P10k_complete 39028377647218 3659 (by norm_num) (by norm_num) prime_sub_3659 ds_3659 check_3659

def ds_3677 : List ℕ := [
    2, 61, 7, 3, 67, 3, 13, 3,
    19, 5, 3, 3, 1321, 3, 7, 29,
    5, 3, 3, 41, 3, 3, 18701, 5,
    3, 59, 3, 53, 3, 1787, 3, 7,
    19, 3, 5, 3, 3, 3, 23, 7,
    5, 3, 11, 3, 397, 3, 3, 3,
    29, 3, 47, 5, 3, 13, 7, 101,
    5, 3, 3, 22751, 3, 563, 3, 31,
    3, 41, 3, 3, 89, 3, 17, 5,
    3, 3, 3, 7, 5, 3, 29, 3,
    5, 3, 37, 3, 3, 23, 5, 3,
    4759, 3, 7, 5, 3, 61, 3, 73,
    5, 11, 3, 3, 3, 17, 13, 5,
    3, 3, 11, 7, 5, 3, 3, 3,
    340573, 3, 3, 13, 3, 3217381, 11, 5,
    3, 3, 7, 31, 3, 1249, 3, 5,
    3, 3, 3, 53, 3, 3, 7, 3,
    227, 3, 13, 5, 3, 19, 3, 139,
    3, 5, 3, 23, 3, 17, 3, 89,
    3, 7, 3, 3338879, 3, 5, 3, 73,
    2116481, 13, 3, 7, 5843, 11, 3, 3,
    3, 7, 5, 3, 13, 3, 3, 5,
    3, 43, 3, 3, 3, 641, 3, 7,
    79, 5, 3, 3, 3, 1181, 3, 19,
    3, 7, 13, 157, 3, 3, 67, 7,
    5, 3, 3, 3, 5, 19, 3, 769,
    5, 3, 3, 41, 3, 7, 5, 3,
    3, 47, 211, 17, 3, 3, 5, 3,
    31, 3, 7, 5, 3, 1493, 3, 3,
    3, 2887, 3, 401, 3, 88969, 5, 11,
    761, 3, 3, 3, 27893, 5, 3, 159569,
    3, 149, 3, 7, 103, 3, 31, 5,
    3, 3, 877, 3, 3, 257, 3, 3,
    53, 3, 5, 23167, 3, 13, 3, 3,
    3, 3, 3, 3, 191, 3, 3, 7,
    23, 3, 19, 3, 3, 59, 3, 1567,
    3, 5, 97, 11, 109, 461, 3, 5,
    3, 11, 5, 3, 3, 4829779, 3, 5099,
    3, 3, 821, 3, 5, 3, 7, 5,
    101, 3, 17, 3, 5, 144479, 3, 5,
    3, 3, 29, 3, 3221, 3, 3, 3,
    37, 58909, 3, 11, 3, 3733883, 3, 862483,
    3, 7, 3, 3, 3, 9677, 5, 3,
    53, 5, 3, 3, 43, 7, 3, 3,
    173, 3, 3, 17, 5, 310363, 19, 67,
    3, 7, 464953, 5, 3, 3, 149, 3,
    3, 19, 3, 31, 5, 3, 3, 5,
    13, 3, 5, 3, 1027067, 11, 3, 33863,
    3, 29, 3, 3, 3, 61, 3, 7,
    5, 3, 373, 3, 3, 5, 3, 71,
    3, 3989, 3, 7, 5, 3, 3, 17,
    3, 5, 3, 29, 103, 3, 3, 7,
    5, 3, 11, 7, 5, 3, 23, 5,
    3, 197, 11, 5, 3, 5, 3, 29,
    3, 41, 3, 521, 3, 3, 3, 3,
    3982247, 5, 3, 5, 3, 13, 3, 71,
    3, 3, 3, 1127957, 23, 5, 3, 109,
    3, 383, 3, 353, 3, 3, 5, 3,
    3, 3, 3, 7, 5, 3, 3, 4373459,
    5, 3, 13, 3, 5, 3, 7, 17,
    3, 5, 3, 103, 3, 281, 3, 7,
    3, 3, 3, 13, 3, 7, 5, 3,
    3, 11, 3, 3, 229, 3, 71, 3,
    3, 7, 11, 3, 3, 3, 5, 19,
    3]

theorem prime_sub_3677 : Nat.Prime (40854680372224 - 3677) := by
  show Nat.Prime 40854680368547
  exact p40854680368547

theorem check_3677 : allC 40854680372224 3677 P10k ds_3677 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 40854680372224 is 3677. -/
theorem minGB_S_3677 : minGB 40854680372224 = 3677 :=
  minGB_eq_of P10k P10k_complete 40854680372224 3677 (by norm_num) (by norm_num) prime_sub_3677 ds_3677 check_3677

def ds_3701 : List ℕ := [
    2, 1009, 41, 3, 19, 3, 4649, 3,
    7, 5, 3, 3, 23, 3, 11321, 29,
    5, 3, 3, 67, 3, 3, 593, 5,
    3, 13, 3, 7, 3, 4273, 3, 11,
    109, 3, 5, 3, 3, 3, 83, 379,
    5, 3, 7, 3, 11, 3, 3, 3,
    29, 3, 7, 5, 3, 37, 13, 11,
    5, 3, 3, 61, 3, 137, 3, 59,
    3, 7, 3, 3, 1259, 3, 19, 5,
    3, 3, 3, 71, 5, 3, 7, 3,
    5, 3, 281, 3, 3, 7, 5, 3,
    11, 3, 17, 5, 3, 13, 3, 1031,
    5, 1335233, 3, 3, 3, 31, 25643, 5,
    3, 3, 47, 11, 5, 3, 3, 3,
    181, 3, 3, 7829, 3, 13, 7, 5,
    3, 3, 449, 75209, 3, 242647, 3, 5,
    3, 3, 3, 31, 3, 3, 107, 3,
    17, 3, 1458727, 5, 3, 7, 3, 9929,
    3, 5, 3, 11, 3, 7, 3, 13,
    3, 359, 3, 3049, 3, 5, 3, 2417,
    7, 26591, 3, 661, 17, 1889, 3, 3,
    3, 61, 5, 3, 7, 3, 3, 5,
    3, 2647, 3, 3, 3, 2334259, 3, 29,
    983, 5, 3, 3, 3, 19, 3, 83,
    3, 17, 11, 13, 3, 3, 4727851, 665303,
    5, 3, 3, 3, 5, 67, 3, 7,
    5, 3, 3, 31, 3, 179, 5, 3,
    3, 37, 7, 59, 3, 3, 5, 3,
    13, 3, 43, 5, 3, 7, 3, 3,
    3, 41, 3, 17, 3, 7, 5, 4159,
    251761, 3, 3, 3, 3271, 5, 3, 4529263,
    3, 11, 3, 1192391, 19, 3, 53, 5,
    3, 3, 149, 3, 3, 563, 3, 3,
    23, 3, 5, 19, 3, 241, 3, 3,
    3, 3, 3, 3, 7, 3, 3, 293,
    2357, 3, 11, 3, 3, 7, 3, 479,
    3, 5, 307, 127, 7, 53, 3, 5,
    3, 13, 5, 3, 3, 7, 3, 108359,
    3, 3, 37, 3, 5, 3, 19, 5,
    7, 3, 71, 3, 5, 11, 3, 5,
    3, 3, 29, 3, 461, 3, 3, 3,
    7, 65647, 3, 109049, 3, 11, 3, 2777,
    3, 10957, 3, 3, 3, 97, 5, 3,
    7, 5, 3, 3, 179813, 2969, 3, 3,
    179, 3, 3, 807409, 5, 5953, 7, 2333,
    3, 11, 103, 5, 3, 3, 61, 3,
    3, 149, 3, 7, 5, 3, 3, 5,
    53117, 3, 5, 3, 3733, 19, 3, 83,
    3, 23, 3, 3, 3, 107, 3, 37,
    5, 3, 7, 3, 3, 5, 3, 2053,
    3, 7, 3, 401, 5, 3, 3, 23,
    3, 5, 3, 7, 47, 3, 3, 19,
    5, 3, 929, 11, 5, 3, 191, 5,
    3, 41, 7, 5, 3, 5, 3, 29,
    3, 389, 3, 359, 3, 3, 3, 3,
    571, 5, 3, 5, 3, 37, 3, 11,
    3, 3, 3, 10837, 19, 5, 3, 13,
    3, 619, 3, 7, 3, 3, 5, 3,
    3, 3, 3, 17, 5, 3, 3, 31,
    5, 3, 331, 3, 5, 3, 47, 390527,
    3, 5, 3, 97, 3, 7, 3, 23,
    3, 3, 3, 17, 3, 13, 5, 3,
    3, 42131, 3, 3, 37, 3, 7, 3,
    3, 3449, 73, 3, 3, 3, 5, 25321,
    3, 7, 3, 3]

theorem prime_sub_3701 : Nat.Prime (44776706182504 - 3701) := by
  show Nat.Prime 44776706178803
  exact p44776706178803

theorem check_3701 : allC 44776706182504 3701 P10k ds_3701 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 44776706182504 is 3701. -/
theorem minGB_S_3701 : minGB 44776706182504 = 3701 :=
  minGB_eq_of P10k P10k_complete 44776706182504 3701 (by norm_num) (by norm_num) prime_sub_3701 ds_3701 check_3701

def ds_3761 : List ℕ := [
    2, 5, 149, 3, 13, 3, 11, 3,
    5, 7, 3, 3, 946697, 3, 113, 5,
    271, 3, 3, 7, 3, 3, 5, 13,
    3, 29, 3, 1709, 3, 5, 3, 59,
    19, 3, 11, 3, 3, 3, 13, 5,
    689257, 3, 401, 3, 7, 3, 3, 3,
    97, 3, 5, 7, 3, 19, 23, 5,
    131, 3, 3, 7, 3, 5, 3, 970043,
    3, 9371, 3, 3, 11, 3, 5, 26003,
    3, 3, 3, 5, 107, 3, 13, 3,
    457, 3, 239, 3, 3, 5, 7, 3,
    103, 3, 37, 11, 3, 7, 3, 5,
    647, 2707, 3, 3, 3, 13, 5, 757,
    3, 3, 397, 5, 703033, 3, 3, 3,
    7, 3, 3, 61, 3, 3467, 5, 7,
    3, 3, 11, 5, 3, 7, 3, 2477,
    3, 3, 3, 5, 3, 3, 919, 3,
    5, 3, 29, 11, 3, 19, 3, 7,
    3, 59, 3, 53, 3, 5, 3, 83,
    3, 2566063, 3, 7, 3, 4508923, 3, 11,
    13, 5, 3, 29, 167, 5, 3, 3,
    3, 5, 157, 3, 107, 3, 3, 19,
    3, 15559, 3, 3, 3, 1201, 3, 31,
    5, 43, 3, 3, 3, 191, 3, 5,
    3, 13, 829, 5, 3, 3, 17, 5,
    41, 3, 3, 3, 13, 19, 3, 5,
    7, 3, 3, 643, 3, 133963, 17, 3,
    3, 23, 43, 5, 3, 3, 13241, 3,
    307, 3, 5, 1187, 3, 101, 3, 3,
    3, 67, 3, 2633, 3, 5, 7, 1181,
    5, 3, 3, 3, 5, 13649, 3, 13,
    3, 5, 3, 11, 556607, 3, 5, 19,
    3, 3, 23, 3, 3, 7, 3, 3,
    103, 3, 7, 41, 3, 5, 3, 3,
    3, 3, 3, 3, 6073, 3, 3, 53,
    5, 3, 19, 3, 3, 1409, 3, 7,
    3, 3371, 59, 383, 5, 11, 3, 107449,
    3, 5, 167, 3, 3, 11, 3, 5,
    3, 3, 31, 3, 13, 3, 5, 69473,
    113, 3, 7, 3, 227, 5407, 3, 7,
    3, 3, 43, 3, 5, 3, 3, 3,
    17191, 5, 3, 17, 3, 5, 3, 6696343,
    3, 5, 3, 3, 3, 7, 89, 3,
    5, 7, 3, 3, 13, 139, 3, 3,
    7, 3, 3, 5, 31, 251, 19, 5,
    3, 17, 53, 11, 3, 3, 1644899, 3,
    3, 19, 3, 5, 7, 3, 3, 79,
    7, 3, 59, 3, 3137, 5, 3, 11,
    3, 5, 3, 3, 3, 37, 3, 5,
    2971, 3, 29, 3, 3, 12823, 3, 13,
    3, 5, 3, 1109, 11, 3, 3, 7,
    3, 13, 3, 61, 5, 3, 3, 5961239,
    23, 3, 13, 5, 37, 3, 7, 337,
    3, 31, 5, 7, 3, 6007, 3, 7,
    3, 5, 3, 3851, 3, 3, 3, 3,
    5, 67, 3, 11, 3, 7, 3, 6678383,
    3, 3, 3, 139, 5, 13, 3, 7,
    3, 11, 3, 17, 3, 3, 239, 3,
    3, 3, 3, 5, 19, 3, 3, 7,
    17, 3, 83, 3, 7, 3, 29, 5,
    3, 11, 3, 17, 3, 3343337, 3, 67,
    3, 3, 3, 79, 3, 5, 193, 3,
    3, 7, 3, 3, 11, 3, 5, 3,
    3, 2849813, 5, 3, 3, 3, 163, 19,
    3, 13, 3, 3, 31, 3, 53, 3,
    3, 3]

theorem prime_sub_3761 : Nat.Prime (54133015834948 - 3761) := by
  show Nat.Prime 54133015831187
  exact p54133015831187

theorem check_3761 : allC 54133015834948 3761 P10k ds_3761 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 54133015834948 is 3761. -/
theorem minGB_S_3761 : minGB 54133015834948 = 3761 :=
  minGB_eq_of P10k P10k_complete 54133015834948 3761 (by norm_num) (by norm_num) prime_sub_3761 ds_3761 check_3761

end LeanLab.OeSHP2014
