/-
P0041 Sinisalo 1993, Table 2, rows 52 to 67: for each listed prime p and its
S(p), the least Goldbach prime of S(p) is p. Divisors and Pratt certificates found by Python,
checked by the Lean kernel, with the lab's Top50 machinery. That S(p) is the LEAST such n is
Sinisalo's search, not checked here. Run 20261018T1103Z-12430, unit U-0940.
AI-written Lean code, Claude, 2026-10-18. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.Base

namespace LeanLab.Sinisalo1993

open LeanLab.Verifications LeanLab.Verifications.Top50
open LeanLab.Verifications.Pratt (pB)

theorem p50833121 : Nat.Prime 50833121 := by
  refine Pratt.pratt 50833121 6 [(2, 5), (5, 1), (13, 1), (24439, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p135382769 : Nat.Prime 135382769 := by
  refine Pratt.pratt 135382769 3 [(2, 4), (8461423, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p933353191 : Nat.Prime 933353191 := by
  refine Pratt.pratt 933353191 6 [(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (134683, 1)] (by norm_num)
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
theorem p966528583 : Nat.Prime 966528583 := by
  refine Pratt.pratt 966528583 3 [(2, 1), (3, 1), (3583, 1), (44959, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p2203581833 : Nat.Prime 2203581833 := by
  refine Pratt.pratt 2203581833 3 [(2, 3), (1223, 1), (225223, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p2538832213 : Nat.Prime 2538832213 := by
  refine Pratt.pratt 2538832213 2 [(2, 2), (3, 2), (7, 1), (19, 1), (530249, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p2816591873 : Nat.Prime 2816591873 := by
  refine Pratt.pratt 2816591873 3 [(2, 11), (199, 1), (6911, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p4407163667 : Nat.Prime 4407163667 := by
  refine Pratt.pratt 4407163667 2 [(2, 1), (2203581833, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p2203581833
theorem p5801827313 : Nat.Prime 5801827313 := by
  refine Pratt.pratt 5801827313 3 [(2, 4), (1019, 1), (355853, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p8946629297 : Nat.Prime 8946629297 := by
  refine Pratt.pratt 8946629297 3 [(2, 4), (11, 1), (50833121, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p50833121
theorem p9615480379 : Nat.Prime 9615480379 := by
  refine Pratt.pratt 9615480379 2 [(2, 1), (3, 1), (7, 1), (151, 1), (563, 1), (2693, 1)] (by norm_num)
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
theorem p13035100163 : Nat.Prime 13035100163 := by
  refine Pratt.pratt 13035100163 2 [(2, 1), (7, 1), (31, 1), (107, 1), (280699, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p21439963841 : Nat.Prime 21439963841 := by
  refine Pratt.pratt 21439963841 6 [(2, 6), (5, 1), (367, 1), (182561, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p26070200327 : Nat.Prime 26070200327 := by
  refine Pratt.pratt 26070200327 5 [(2, 1), (13035100163, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p13035100163
theorem p30325740257 : Nat.Prime 30325740257 := by
  refine Pratt.pratt 30325740257 3 [(2, 5), (7, 1), (135382769, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p135382769
theorem p30834369889 : Nat.Prime 30834369889 := by
  refine Pratt.pratt 30834369889 26 [(2, 5), (3, 1), (7, 1), (17, 1), (2699087, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p32652625669 : Nat.Prime 32652625669 := by
  refine Pratt.pratt 32652625669 2 [(2, 2), (3, 1), (13, 1), (349, 1), (353, 1), (1699, 1)] (by norm_num)
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
theorem p44460314819 : Nat.Prime 44460314819 := by
  refine Pratt.pratt 44460314819 2 [(2, 1), (23, 1), (966528583, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p966528583
theorem p64243960901 : Nat.Prime 64243960901 := by
  refine Pratt.pratt 64243960901 3 [(2, 2), (5, 2), (7, 1), (19, 1), (4830373, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p65334723371 : Nat.Prime 65334723371 := by
  refine Pratt.pratt 65334723371 2 [(2, 1), (5, 1), (7, 1), (933353191, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p933353191
theorem p113843128331 : Nat.Prime 113843128331 := by
  refine Pratt.pratt 113843128331 2 [(2, 1), (5, 1), (109, 1), (449, 1), (457, 1), (509, 1)] (by norm_num)
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
theorem p244808990963 : Nat.Prime 244808990963 := by
  refine Pratt.pratt 244808990963 2 [(2, 1), (2267, 1), (6163, 1), (8761, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p384619215161 : Nat.Prime 384619215161 := by
  refine Pratt.pratt 384619215161 6 [(2, 3), (5, 1), (9615480379, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p9615480379

def ds_1429 : List ℕ := [
    2, 47, 3, 5, 3, 31, 3, 29, 3, 3, 41, 5,
    3, 19, 3, 3, 3, 433, 5, 3, 4817, 7, 3, 3,
    5, 3, 11, 3, 17, 3, 5, 3, 3, 5021, 3, 89,
    5, 7, 3, 3, 3, 229, 3, 23, 3, 31, 17, 271,
    3, 757, 3, 3, 13, 3, 3, 3, 3, 19, 5, 3,
    61, 3, 5, 3, 17, 3, 7, 5, 3, 557, 3, 3,
    5, 7, 47, 3, 3, 5, 3, 449, 3, 331, 3, 11,
    881, 3, 3, 5, 3, 35317, 3, 3, 5, 3, 7, 3,
    3, 3, 41, 7, 5, 3, 3, 3, 31, 5, 3, 3,
    3, 20627, 5, 19, 3, 17, 11, 3, 26479, 3, 3, 3,
    47, 197, 3, 3, 40039, 3, 7, 3, 5, 73, 149, 3,
    7, 5, 3, 41, 3, 5, 3, 3, 313, 3, 17, 3,
    11, 3, 43, 3, 487, 3, 5, 3, 23, 3, 5, 3,
    7, 3, 5, 3, 3, 3, 5, 3, 3, 3, 1117, 5,
    12841, 3, 3, 13, 3, 173, 673, 3, 307, 3, 29, 19,
    5, 3, 11, 3, 3, 3, 5, 181, 7, 3, 127, 3,
    7, 3, 3, 3, 37, 7, 3, 3, 3, 17, 5, 7103,
    3, 3, 59, 3, 3, 11, 5, 3, 7789, 3, 3, 3769,
    5, 3, 3, 3, 7, 79, 3, 7, 3]

theorem prime_sub_1429 : Nat.Prime (2538833642 - 1429) := by
  show Nat.Prime 2538832213
  exact p2538832213

theorem check_1429 : allC 2538833642 1429 P10k ds_1429 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 2538833642 is 1429. -/
theorem minGB_S_1429 : minGB 2538833642 = 1429 :=
  minGB_eq_of P10k P10k_complete 2538833642 1429 (by norm_num) (by norm_num) prime_sub_1429 ds_1429 check_1429

def ds_1439 : List ℕ := [
    2, 181, 11, 3, 16067, 3, 5, 3, 1931, 7, 3, 3,
    23, 3, 5, 2017, 1259, 3, 3, 7, 3, 3, 7547, 13121,
    3, 5881, 3, 5, 3, 7, 3, 43, 5, 3, 673, 3,
    3, 3, 5, 113, 17, 3, 397, 3, 5, 3, 3, 3,
    5, 3, 19, 7, 3, 857, 5, 661, 11, 3, 3, 7,
    3, 659, 3, 137, 3, 5, 3, 3, 5, 3, 101, 937,
    3, 3, 3, 17, 43, 3, 11, 3, 163, 3, 1021, 3,
    3, 11273, 7, 3, 19, 3, 5, 53, 3, 7, 3, 109,
    223, 71, 3, 3, 3, 5, 4909, 149, 3, 3, 5, 23,
    11, 3, 3, 3, 5, 3, 3, 443, 3, 5, 24329, 7,
    3, 3, 5, 4637, 3, 7, 3, 14143, 3, 3, 3, 7,
    3, 3, 37, 3, 41, 3, 5, 4243, 3, 29, 3, 5,
    3, 9157, 3, 5, 3, 11, 3, 67, 3, 5, 3, 7,
    3, 11, 3, 103, 5, 7, 3, 383, 5, 37, 3, 3,
    3, 293, 41, 3, 19, 3, 3, 2551, 3, 11, 3, 3,
    3, 1009, 3, 5, 59, 31, 3, 3, 3, 313, 3, 7,
    3, 4931, 5, 11, 3, 3, 5, 157, 653, 3, 3, 3,
    11, 5, 3, 23, 7, 3, 3, 17, 3, 5, 1031, 3,
    3, 7727, 5, 7, 3, 3, 127, 3, 5, 3, 53]

theorem prime_sub_1439 : Nat.Prime (2816593312 - 1439) := by
  show Nat.Prime 2816591873
  exact p2816591873

theorem check_1439 : allC 2816593312 1439 P10k ds_1439 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 2816593312 is 1439. -/
theorem minGB_S_1439 : minGB 2816593312 = 1439 :=
  minGB_eq_of P10k P10k_complete 2816593312 1439 (by norm_num) (by norm_num) prime_sub_1439 ds_1439 check_1439

def ds_1451 : List ℕ := [
    2, 5, 13, 3, 16631, 3, 89, 3, 5, 1093, 3, 3,
    7, 3, 41, 5, 11, 3, 3, 1063, 3, 3, 5, 12377,
    3, 17, 3, 131, 3, 5, 3, 23, 617, 3, 19, 3,
    3, 3, 7, 5, 16183, 3, 11, 3, 2207, 3, 3, 3,
    1013, 3, 5, 13, 3, 7, 11, 5, 23, 3, 3, 181,
    3, 5, 3, 211, 3, 13, 3, 3, 29, 3, 5, 2503,
    3, 3, 3, 5, 11, 3, 571, 3, 7, 3, 73, 3,
    3, 5, 6863, 3, 7, 3, 36629, 97, 3, 19, 3, 5,
    17, 11, 3, 3, 3, 709, 5, 179, 3, 3, 7, 5,
    479, 3, 3, 3, 16927, 3, 3, 59, 3, 43, 5, 269,
    3, 3, 139, 5, 3, 61, 3, 11, 3, 3, 3, 5,
    3, 3, 51347, 3, 5, 3, 7, 103, 3, 23, 3, 47,
    3, 7, 3, 313, 3, 5, 3, 7, 3, 79, 3, 2063,
    3, 101, 3, 13, 19, 5, 3, 12917, 691, 5, 3, 3,
    3, 5, 13, 3, 41, 3, 3, 7, 3, 19, 3, 3,
    3, 7, 3, 13, 5, 47, 3, 3, 3, 1553, 3, 5,
    3, 11, 1789, 5, 3, 3, 7, 5, 28349, 3, 3, 3,
    7, 41, 3, 5, 19, 3, 3, 7, 3, 73, 157, 3,
    3, 79, 181, 5, 3, 3, 13, 3, 7, 3, 5, 37549,
    3]

theorem prime_sub_1451 : Nat.Prime (4407165118 - 1451) := by
  show Nat.Prime 4407163667
  exact p4407163667

theorem check_1451 : allC 4407165118 1451 P10k ds_1451 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 4407165118 is 1451. -/
theorem minGB_S_1451 : minGB 4407165118 = 1451 :=
  minGB_eq_of P10k P10k_complete 4407165118 1451 (by norm_num) (by norm_num) prime_sub_1451 ds_1451 check_1451

def ds_1493 : List ℕ := [
    2, 389, 401, 3, 5, 3, 691, 3, 109, 31, 3, 3,
    5, 3, 227, 7, 11, 3, 3, 5, 3, 3, 4217, 1093,
    3, 5, 3, 97, 3, 26267, 3, 5, 7, 3, 19, 3,
    3, 3, 67757, 8167, 7, 3, 5, 3, 1723, 3, 3, 3,
    107, 3, 331, 47, 3, 5, 11, 7, 29, 3, 3, 5,
    3, 13, 3, 5, 3, 431, 3, 3, 7, 3, 23, 139,
    3, 3, 3, 12473, 7, 3, 5, 3, 89, 3, 5, 3,
    3, 29, 13, 3, 5, 3, 11597, 37, 3, 5, 3, 3313,
    1259, 5, 3, 3, 3, 7, 15107, 19477, 3, 3, 11, 4153,
    7, 3, 3, 3, 29, 3, 3, 5, 3, 5479, 11, 5059,
    3, 3, 109, 7, 3, 5, 3, 11, 3, 3, 3, 5281,
    3, 3, 5, 3, 31, 3, 53, 7, 3, 5, 3, 1933,
    3, 13, 3, 17, 3, 1051, 3, 5, 3, 30367, 3, 5,
    3, 41, 3, 5, 19, 89, 3, 5, 7, 11, 3, 3,
    3, 2887, 7, 3, 5, 3, 3, 11, 3, 5, 3, 3,
    3, 5, 3, 149, 7, 3301, 3, 3, 3, 5, 3, 17,
    3, 5, 7, 139, 3, 3, 43, 18379, 7, 3, 3, 3,
    61, 1069, 3, 421, 19, 3, 3, 5, 3, 13, 23, 3,
    3, 5, 17, 659, 3, 3, 227, 3, 163, 3, 53, 7,
    3, 5, 3, 3, 3, 5, 3, 29, 3]

theorem prime_sub_1493 : Nat.Prime (5801828806 - 1493) := by
  show Nat.Prime 5801827313
  exact p5801827313

theorem check_1493 : allC 5801828806 1493 P10k ds_1493 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 5801828806 is 1493. -/
theorem minGB_S_1493 : minGB 5801828806 = 1493 :=
  minGB_eq_of P10k P10k_complete 5801828806 1493 (by norm_num) (by norm_num) prime_sub_1493 ds_1493 check_1493

def ds_1559 : List ℕ := [
    2, 229, 17, 3, 5, 3, 83, 3, 7, 23, 3, 3,
    5, 3, 47, 11, 13, 3, 3, 5, 3, 3, 587, 733,
    3, 5, 3, 7, 3, 359, 3, 5, 13, 3, 7, 3,
    3, 3, 23, 179, 1087, 3, 5, 3, 31, 3, 3, 3,
    3371, 3, 7, 1289, 3, 5, 37, 3739, 29, 3, 3, 5,
    3, 13, 3, 5, 3, 7, 3, 3, 43441, 3, 1609, 7,
    3, 3, 3, 11, 77933, 3, 5, 3, 223, 3, 5, 3,
    3, 7, 11, 3, 5, 3, 163, 19, 3, 5, 3, 43,
    997, 5, 3, 3, 3, 197, 109, 7, 3, 3, 107, 19,
    151, 3, 3, 3, 17, 3, 3, 5, 3, 11, 7, 97,
    3, 3, 53, 13, 3, 5, 3, 17, 3, 3, 3, 7351,
    3, 3, 5, 3, 1753, 3, 45329, 457, 3, 5, 3, 1931,
    3, 13, 3, 23, 3, 7, 3, 5, 3, 29297, 3, 5,
    3, 1871, 3, 5, 7, 7649, 3, 5, 11, 4441, 3, 3,
    3, 61, 43, 3, 5, 3, 3, 19, 3, 5, 3, 3,
    3, 5, 3, 5003, 11681, 11, 3, 3, 3, 5, 3, 19,
    3, 5, 59, 191, 3, 3, 41, 181, 13, 3, 3, 3,
    401, 19, 3, 7, 701, 3, 3, 5, 3, 11, 73, 3,
    3, 5, 7, 11, 3, 3, 7, 3, 28657, 3, 17, 11,
    3, 5, 3, 3, 3, 5, 3, 29, 3, 7, 31, 5,
    3463, 3, 3, 3, 293]

theorem prime_sub_1559 : Nat.Prime (8946630856 - 1559) := by
  show Nat.Prime 8946629297
  exact p8946629297

theorem check_1559 : allC 8946630856 1559 P10k ds_1559 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 8946630856 is 1559. -/
theorem minGB_S_1559 : minGB 8946630856 = 1559 :=
  minGB_eq_of P10k P10k_complete 8946630856 1559 (by norm_num) (by norm_num) prime_sub_1559 ds_1559 check_1559

def ds_1571 : List ℕ := [
    2, 1109, 7, 3, 6197, 3, 5, 3, 19, 36161, 3, 3,
    11, 3, 5, 443, 71, 3, 3, 3041, 3, 3, 281, 7,
    3, 661, 3, 5, 3, 293, 3, 7, 5, 3, 29, 3,
    3, 3, 5, 7, 22003, 3, 41, 3, 5, 3, 3, 3,
    5, 3, 61, 11, 3, 19, 5, 31, 421, 3, 3, 13,
    3, 6949, 3, 59, 3, 5, 3, 3, 5, 3, 157, 13,
    3, 3, 3, 7, 73, 3, 34439, 3, 23, 3, 37, 3,
    3, 18457, 31, 3, 569, 3, 5, 19, 3, 10099, 3, 11,
    7, 102587, 3, 3, 3, 5, 7517, 11, 3, 3, 5, 7,
    61, 3, 3, 3, 5, 3, 3, 9817, 3, 5, 37, 397,
    3, 3, 5, 41, 3, 11, 3, 7, 3, 3, 3, 241,
    3, 3, 7, 3, 499, 3, 5, 79, 3, 19, 3, 5,
    3, 47, 3, 5, 3, 53, 3, 16097, 3, 5, 3, 71,
    3, 7, 3, 149, 5, 409, 3, 7, 5, 13, 3, 3,
    3, 7, 29, 3, 11, 3, 3, 19, 3, 13, 3, 3,
    3, 63697, 3, 5, 83, 23, 3, 3, 3, 113, 3, 11,
    3, 7, 5, 29, 3, 3, 5, 7, 11, 3, 3, 3,
    2953, 5, 3, 79, 4241, 3, 3, 191, 3, 5, 37, 3,
    3, 11, 5, 13, 3, 3, 5171, 3, 5, 3, 7, 919,
    3, 13, 3, 3, 3, 43573, 3, 5, 3, 11, 53, 797,
    23, 3, 3, 3, 181, 7, 3]

theorem prime_sub_1571 : Nat.Prime (21439965412 - 1571) := by
  show Nat.Prime 21439963841
  exact p21439963841

theorem check_1571 : allC 21439965412 1571 P10k ds_1571 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 21439965412 is 1571. -/
theorem minGB_S_1571 : minGB 21439965412 = 1571 :=
  minGB_eq_of P10k P10k_complete 21439965412 1571 (by norm_num) (by norm_num) prime_sub_1571 ds_1571 check_1571

def ds_1787 : List ℕ := [
    2, 8581, 7, 3, 11, 3, 47, 3, 31, 5, 3, 3,
    179, 3, 7, 6121, 5, 3, 3, 19, 3, 3, 67, 5,
    3, 98713, 3, 29, 3, 47137, 3, 7, 83, 3, 5, 3,
    3, 3, 17, 7, 5, 3, 2111, 3, 701, 3, 3, 3,
    37, 3, 2689, 5, 3, 113, 7, 23, 5, 3, 3, 13,
    3, 41, 3, 110459, 3, 12583, 3, 3, 109, 3, 199, 5,
    3, 3, 3, 7, 5, 3, 23, 3, 5, 3, 1619, 3,
    3, 17257, 5, 3, 197, 3, 7, 5, 3, 121403, 3, 173,
    5, 1289, 3, 3, 3, 59, 43, 5, 3, 3, 71, 7,
    5, 3, 3, 3, 167, 3, 3, 19, 3, 1481, 307, 5,
    3, 3, 7, 73, 3, 383, 3, 5, 3, 3, 3, 79,
    3, 3, 7, 3, 1361, 3, 1399, 5, 3, 43, 3, 13,
    3, 5, 3, 14407, 3, 47, 3, 17, 3, 7, 3, 59,
    3, 5, 3, 18041, 61, 23, 3, 7, 29, 13, 3, 3,
    3, 7, 5, 3, 41, 3, 3, 5, 3, 13, 3, 3,
    3, 23, 3, 7, 32401, 5, 3, 3, 3, 29, 3, 148549,
    3, 7, 17, 929, 3, 3, 13, 7, 5, 3, 3, 3,
    5, 41, 3, 2549, 5, 3, 3, 271, 3, 7, 5, 3,
    3, 22453, 23, 13, 3, 3, 5, 3, 47, 3, 7, 5,
    3, 13, 3, 3, 3, 557, 3, 191, 3, 17, 5, 31,
    41, 3, 3, 3, 19, 5, 3, 239, 3, 419, 3, 7,
    13, 3, 829, 5, 3, 3, 1231, 3, 3, 19, 3, 3,
    17, 3, 5, 487, 3, 1217, 3, 3, 3, 3, 3, 3]

theorem prime_sub_1787 : Nat.Prime (26070202114 - 1787) := by
  show Nat.Prime 26070200327
  exact p26070200327

theorem check_1787 : allC 26070202114 1787 P10k ds_1787 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 26070202114 is 1787. -/
theorem minGB_S_1787 : minGB 26070202114 = 1787 :=
  minGB_eq_of P10k P10k_complete 26070202114 1787 (by norm_num) (by norm_num) prime_sub_1787 ds_1787 check_1787

def ds_1811 : List ℕ := [
    2, 5, 3527, 3, 13, 3, 11, 3, 5, 1787, 3, 3,
    7, 3, 193, 5, 17, 3, 3, 137, 3, 3, 5, 13,
    3, 233, 3, 73907, 3, 5, 3, 23, 29, 3, 11, 3,
    3, 3, 7, 5, 919, 3, 53, 3, 67, 3, 3, 3,
    1451, 3, 5, 70111, 3, 7, 239, 5, 23, 3, 3, 11,
    3, 5, 3, 29, 3, 26393, 3, 3, 11, 3, 5, 47,
    3, 3, 3, 5, 223, 3, 13, 3, 7, 3, 3089, 3,
    3, 5, 683, 3, 7, 3, 17, 11, 3, 37123, 3, 5,
    19, 577, 3, 3, 3, 13, 5, 17, 3, 3, 7, 5,
    67, 3, 3, 3, 283, 3, 3, 47, 3, 37, 5, 29,
    3, 3, 11, 5, 3, 29921, 3, 419, 3, 3, 3, 5,
    3, 3, 41, 3, 5, 3, 7, 11, 3, 23, 3, 53,
    3, 7, 3, 2287, 3, 5, 3, 7, 3, 109, 3, 32233,
    3, 79, 3, 11, 13, 5, 3, 101161, 17, 5, 3, 3,
    3, 5, 59, 3, 2549, 3, 3, 7, 3, 89, 3, 3,
    3, 7, 3, 23, 5, 83, 3, 3, 3, 31, 3, 5,
    3, 13, 71, 5, 3, 3, 7, 5, 6133, 3, 3, 3,
    7, 97, 3, 5, 47737, 3, 3, 7, 3, 19, 181, 3,
    3, 163, 103, 5, 3, 3, 107, 3, 7, 3, 5, 61,
    3, 227, 3, 3, 3, 167, 3, 17, 3, 5, 41, 7,
    5, 3, 3, 3, 5, 3697, 3, 13, 3, 5, 3, 11,
    83, 3, 5, 142963, 3, 3, 7, 3, 3, 11, 3, 3,
    271, 3, 31, 7, 3, 5, 3, 3, 3, 3, 3, 3,
    23, 3, 3]

theorem prime_sub_1811 : Nat.Prime (30325742068 - 1811) := by
  show Nat.Prime 30325740257
  exact p30325740257

theorem check_1811 : allC 30325742068 1811 P10k ds_1811 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 30325742068 is 1811. -/
theorem minGB_S_1811 : minGB 30325742068 = 1811 :=
  minGB_eq_of P10k P10k_complete 30325742068 1811 (by norm_num) (by norm_num) prime_sub_1811 ds_1811 check_1811

def ds_1867 : List ℕ := [
    2, 16651, 3, 19, 3, 7, 3, 13, 3, 3, 5, 683,
    3, 29, 3, 3, 3, 5, 11, 3, 61, 2593, 3, 3,
    7, 3, 23539, 3, 233, 3, 919, 3, 3, 7, 3, 5,
    83, 103, 3, 3, 3, 5, 3, 41, 3, 11, 5, 7,
    3, 23, 3, 3, 5, 3, 3, 3, 3, 5, 47, 3,
    2341, 3, 7, 3, 257, 3, 5, 619, 3, 7, 3, 3,
    23, 181, 73, 3, 3, 11, 3, 13, 3, 5, 3, 7,
    41, 3, 3, 17, 3, 11, 3, 3, 13, 3, 102059, 3,
    3, 3, 157, 5, 241, 3, 3, 3, 5, 19, 3, 3,
    3, 5, 131, 6269, 3, 307, 5, 3, 7, 3, 3, 3,
    5, 151, 3, 3, 5, 3, 25913, 3, 7, 37, 29, 3,
    5, 31, 3, 7, 3, 11897, 3, 3, 5, 3, 109, 3,
    191, 3, 7, 3, 11, 3, 13, 3, 1297, 3, 211, 3,
    19, 3, 7, 3, 3, 3, 17, 3, 3, 3, 5, 769,
    193, 3, 3, 5, 3, 13, 59063, 3, 5, 3, 7, 17,
    29, 3, 137, 3, 3, 3, 263, 11, 31, 3, 83, 3,
    5, 3, 3, 3, 5, 4889, 3, 3, 3, 5, 449, 1021,
    3, 3, 419, 3, 3, 5, 197, 3, 19301, 3, 3, 5,
    7213, 3, 3, 3, 5, 7, 3, 13, 3, 1811, 3, 3,
    6163, 3, 11, 43, 5, 3, 7, 3, 19, 3, 3, 3,
    3, 5, 11519, 331, 3, 3, 7, 3, 13, 3, 16529, 3,
    3, 7, 3, 3, 5, 179, 3, 13, 67, 3, 41, 7,
    3, 25969, 3, 3, 569, 3, 5, 23, 113, 4783, 7, 11,
    3, 2609, 5, 3, 3, 5, 3, 5]

theorem prime_sub_1867 : Nat.Prime (30834371756 - 1867) := by
  show Nat.Prime 30834369889
  exact p30834369889

theorem check_1867 : allC 30834371756 1867 P10k ds_1867 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 30834371756 is 1867. -/
theorem minGB_S_1867 : minGB 30834371756 = 1867 :=
  minGB_eq_of P10k P10k_complete 30834371756 1867 (by norm_num) (by norm_num) prime_sub_1867 ds_1867 check_1867

def ds_1873 : List ℕ := [
    2, 7, 3, 5, 3, 25097, 3, 6551, 3, 3, 7, 5,
    3, 149, 3, 3, 3, 17, 5, 3, 7, 1109, 3, 3,
    5, 3, 5807, 3, 353, 3, 5, 3, 3, 11, 3, 31,
    5, 17, 3, 3, 3, 43, 3, 67, 3, 7, 14627, 13,
    3, 643, 3, 3, 7, 3, 3, 3, 3, 11, 5, 3,
    7, 3, 5, 3, 60869, 3, 134513, 5, 3, 139, 3, 3,
    5, 29, 13, 3, 3, 5, 3, 7, 3, 14543, 3, 47,
    43, 3, 3, 5, 3, 102013, 3, 3, 5, 3, 4523, 3,
    3, 3, 31, 9851, 5, 3, 3, 3, 17, 5, 3, 3,
    3, 11, 5, 13, 3, 7, 257, 3, 12391, 3, 3, 3,
    7, 17, 3, 3, 13, 3, 19, 3, 5, 11, 103319, 3,
    3821, 5, 3, 13, 3, 5, 3, 3, 79, 3, 19, 3,
    7, 3, 41, 3, 23, 3, 5, 3, 7211, 3, 5, 3,
    5897, 3, 5, 3, 3, 3, 5, 3, 3, 3, 449, 5,
    37889, 3, 3, 131, 3, 64301, 7, 3, 19, 3, 11, 29,
    5, 3, 193, 3, 3, 3, 5, 7, 11, 3, 136319, 3,
    83, 3, 3, 3, 7487, 43, 3, 3, 3, 109, 5, 7,
    3, 3, 19, 3, 3, 7, 5, 3, 20483, 3, 3, 4421,
    5, 3, 3, 3, 159701, 67, 3, 59, 3, 557, 3, 3,
    5, 3, 31, 7, 13, 3, 37, 3, 17, 3, 3, 3,
    3, 61, 7, 13, 3, 3, 5, 3, 3919, 3, 5, 3,
    3, 1193, 3, 3, 19, 5, 3, 5, 5827, 3, 7, 17,
    3, 971, 3, 3, 11, 3, 30137, 5, 7, 79, 5, 13,
    3, 11, 67, 3, 3, 149, 3, 13, 5, 3]

theorem prime_sub_1873 : Nat.Prime (32652627542 - 1873) := by
  show Nat.Prime 32652625669
  exact p32652625669

theorem check_1873 : allC 32652627542 1873 P10k ds_1873 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 32652627542 is 1873. -/
theorem minGB_S_1873 : minGB 32652627542 = 1873 :=
  minGB_eq_of P10k P10k_complete 32652627542 1873 (by norm_num) (by norm_num) prime_sub_1873 ds_1873 check_1873

def ds_1889 : List ℕ := [
    2, 5, 11, 3, 37, 3, 7, 3, 5, 43, 3, 3,
    13, 3, 643, 5, 7, 3, 3, 11, 3, 3, 5, 34471,
    3, 7, 3, 47, 3, 5, 3, 103, 11, 3, 19, 3,
    3, 3, 53, 5, 17, 3, 7877, 3, 13, 3, 3, 3,
    7, 3, 5, 29, 3, 105769, 23, 5, 7, 3, 3, 17,
    3, 5, 3, 7, 3, 383, 3, 3, 5503, 3, 5, 139,
    3, 3, 3, 5, 41, 3, 11, 3, 277, 3, 13, 3,
    3, 5, 1117, 3, 4003, 3, 11, 7, 3, 19, 3, 5,
    13, 7, 3, 3, 3, 2053, 5, 157, 3, 3, 13, 5,
    11, 3, 3, 3, 88241, 3, 3, 149, 3, 7, 5, 101,
    3, 3, 37, 5, 3, 89477, 3, 19, 3, 3, 3, 5,
    3, 3, 29, 3, 5, 3, 11, 23, 3, 13, 3, 8233,
    3, 359, 3, 7, 3, 5, 3, 41, 3, 487, 3, 173917,
    3, 11, 3, 7, 19, 5, 3, 1013, 13, 5, 3, 3,
    3, 5, 1741, 3, 947, 3, 3, 71, 3, 11, 3, 3,
    3, 1697, 3, 17, 5, 7, 3, 3, 3, 7, 3, 5,
    3, 109, 577, 5, 3, 3, 61, 5, 2039, 3, 3, 3,
    11, 7, 3, 5, 13, 3, 3, 17, 3, 15217, 7, 3,
    3, 7, 13, 5, 3, 3, 2909, 3, 181, 3, 5, 53,
    3, 13873, 3, 3, 3, 31, 3, 7, 3, 5, 23, 157,
    5, 3, 3, 3, 5, 73, 3, 7, 3, 5, 3, 13,
    17, 3, 5, 41, 3, 3, 23, 3, 3, 31, 3, 3,
    7, 3, 17, 11, 3, 5, 3, 3, 3, 3, 3, 3,
    11, 3, 3, 17, 5, 3, 661, 3, 3, 101, 3, 8581,
    3]

theorem prime_sub_1889 : Nat.Prime (44460316708 - 1889) := by
  show Nat.Prime 44460314819
  exact p44460314819

theorem check_1889 : allC 44460316708 1889 P10k ds_1889 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 44460316708 is 1889. -/
theorem minGB_S_1889 : minGB 44460316708 = 1889 :=
  minGB_eq_of P10k P10k_complete 44460316708 1889 (by norm_num) (by norm_num) prime_sub_1889 ds_1889 check_1889

def ds_1907 : List ℕ := [
    2, 5, 37, 3, 7, 3, 14153, 3, 5, 23, 3, 3,
    5827, 3, 11, 5, 727, 3, 3, 61, 3, 3, 5, 13859,
    3, 811, 3, 83, 3, 5, 3, 109, 7, 3, 17, 3,
    3, 3, 23, 5, 7, 3, 199, 3, 2113, 3, 3, 3,
    37, 3, 5, 827, 3, 17, 63659, 5, 59, 3, 3, 409,
    3, 5, 3, 11, 3, 1699, 3, 3, 7, 3, 5, 87803,
    3, 3, 3, 5, 7, 3, 19379, 3, 1237, 3, 7, 3,
    3, 5, 37, 3, 307, 3, 13, 2423, 3, 127, 3, 5,
    11, 19, 3, 3, 3, 7, 5, 80207, 3, 3, 73, 5,
    7, 3, 3, 3, 20753, 3, 3, 7, 3, 271, 5, 17,
    3, 3, 29, 5, 3, 13, 3, 23, 3, 3, 3, 5,
    3, 3, 17, 3, 5, 3, 79, 7, 3, 178247, 3, 113,
    3, 11, 3, 13, 3, 5, 3, 1831, 3, 3359, 3, 389,
    3, 134053, 3, 166867, 823, 5, 3, 11, 7, 5, 3, 3,
    3, 5, 7, 3, 41, 3, 3, 71329, 3, 7, 3, 3,
    3, 13, 3, 601, 5, 107, 3, 3, 3, 397, 3, 5,
    3, 167, 7, 5, 3, 3, 2663, 5, 7, 3, 3, 3,
    151, 41, 3, 5, 64483, 3, 3, 11, 3, 53, 19, 3,
    3, 139, 11, 5, 3, 3, 23, 3, 31, 3, 5, 7,
    3, 281, 3, 3, 3, 7, 3, 1531, 3, 5, 11, 4259,
    5, 3, 3, 3, 5, 13, 3, 103, 3, 5, 3, 83,
    7, 3, 5, 50101, 3, 3, 13, 3, 3, 13441, 3, 3,
    11, 3, 12911, 29, 3, 5, 3, 3, 3, 3, 3, 3,
    1033, 3, 3, 183971, 5, 3, 8087, 3, 3, 13, 3, 99409,
    3, 19, 7]

theorem prime_sub_1907 : Nat.Prime (64243962808 - 1907) := by
  show Nat.Prime 64243960901
  exact p64243960901

theorem check_1907 : allC 64243962808 1907 P10k ds_1907 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 64243962808 is 1907. -/
theorem minGB_S_1907 : minGB 64243962808 = 1907 :=
  minGB_eq_of P10k P10k_complete 64243962808 1907 (by norm_num) (by norm_num) prime_sub_1907 ds_1907 check_1907

def ds_1997 : List ℕ := [
    2, 5, 17, 3, 11, 3, 7, 3, 5, 13, 3, 3,
    29, 3, 2161, 5, 7, 3, 3, 257, 3, 3, 5, 157,
    3, 7, 3, 13, 3, 5, 3, 271, 19, 3, 209987, 3,
    3, 3, 2503, 5, 239, 3, 30703, 3, 37, 3, 3, 3,
    7, 3, 5, 23, 3, 19, 269, 5, 7, 3, 3, 31,
    3, 5, 3, 7, 3, 47, 3, 3, 1663, 3, 5, 73,
    3, 3, 3, 5, 29, 3, 8867, 3, 13, 3, 89, 3,
    3, 5, 85133, 3, 443, 3, 31, 7, 3, 179, 3, 5,
    457, 7, 3, 3, 3, 311, 5, 167, 3, 3, 24809, 5,
    47, 3, 3, 3, 17, 3, 3, 37, 3, 7, 5, 1019,
    3, 3, 367, 5, 3, 88007, 3, 17, 3, 3, 3, 5,
    3, 3, 8707, 3, 5, 3, 73, 13, 3, 17, 3, 4663,
    3, 31, 3, 7, 3, 5, 3, 47, 3, 13, 3, 29,
    3, 23, 3, 7, 223, 5, 3, 53, 49937, 5, 3, 3,
    3, 5, 421, 3, 157, 3, 3, 19, 3, 991, 3, 3,
    3, 6257, 3, 20149, 5, 7, 3, 3, 3, 7, 3, 5,
    3, 181, 122251, 5, 3, 3, 109, 5, 17, 3, 3, 3,
    29, 7, 3, 5, 53, 3, 3, 6563, 3, 37, 7, 3,
    3, 7, 491, 5, 3, 3, 643, 3, 151, 3, 5, 347,
    3, 1607, 3, 3, 3, 23, 3, 7, 3, 5, 43, 13,
    5, 3, 3, 3, 5, 41, 3, 7, 3, 5, 3, 71,
    29, 3, 5, 19, 3, 3, 17, 3, 3, 13, 3, 3,
    7, 3, 353, 1171, 3, 5, 3, 3, 3, 3, 3, 3,
    94099, 3, 3, 2371, 5, 3, 19, 3, 3, 109, 3, 12211,
    3, 65099, 13, 7, 5, 180547, 3, 7, 3, 5, 13, 3,
    3]

theorem prime_sub_1997 : Nat.Prime (65334725368 - 1997) := by
  show Nat.Prime 65334723371
  exact p65334723371

theorem check_1997 : allC 65334725368 1997 P10k ds_1997 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 65334725368 is 1997. -/
theorem minGB_S_1997 : minGB 65334725368 = 1997 :=
  minGB_eq_of P10k P10k_complete 65334725368 1997 (by norm_num) (by norm_num) prime_sub_1997 ds_1997 check_1997

def ds_2027 : List ℕ := [
    2, 5, 223, 3, 193, 3, 71, 3, 5, 7591, 3, 3,
    7, 3, 719, 5, 131, 3, 3, 8689, 3, 3, 5, 11,
    3, 17, 3, 43, 3, 5, 3, 103, 191, 3, 31, 3,
    3, 3, 7, 5, 14489, 3, 13, 3, 59, 3, 3, 3,
    3391, 3, 5, 331, 3, 7, 2083, 5, 13, 3, 3, 89,
    3, 5, 3, 18427, 3, 79, 3, 3, 13, 3, 5, 20771,
    3, 3, 3, 5, 23, 3, 43543, 3, 7, 3, 10987, 3,
    3, 5, 6977, 3, 7, 3, 47, 2557, 3, 84431, 3, 5,
    17, 31, 3, 3, 3, 101, 5, 307, 3, 3, 7, 5,
    83, 3, 3, 3, 11, 3, 3, 5569, 3, 19, 5, 13,
    3, 3, 107, 5, 3, 2141, 3, 5077, 3, 3, 3, 5,
    3, 3, 19, 3, 5, 3, 7, 155581, 3, 1873, 3, 304069,
    3, 7, 3, 149, 3, 5, 3, 7, 3, 61, 3, 1721,
    3, 1723, 3, 23, 11, 5, 3, 13, 303377, 5, 3, 3,
    3, 5, 17, 3, 47, 3, 3, 7, 3, 2447, 3, 3,
    3, 7, 3, 67, 5, 41, 3, 3, 3, 2129, 3, 5,
    3, 1423, 281, 5, 3, 3, 7, 5, 32869, 3, 3, 3,
    7, 11, 3, 5, 7193, 3, 3, 7, 3, 53, 107, 3,
    3, 13, 103, 5, 3, 3, 11, 3, 7, 3, 5, 13,
    3, 31, 3, 3, 3, 37, 3, 112589, 3, 5, 67, 7,
    5, 3, 3, 3, 5, 19, 3, 367, 3, 5, 3, 41,
    11, 3, 5, 61, 3, 3, 7, 3, 3, 173, 3, 3,
    359, 3, 73, 7, 3, 5, 3, 3, 3, 3, 3, 3,
    19, 3, 3, 6089, 5, 3, 7, 3, 3, 11, 3, 47,
    3, 7, 19, 13, 5, 7, 3, 10979, 3, 5, 14537, 3,
    3, 503, 3, 5, 3, 3]

theorem prime_sub_2027 : Nat.Prime (113843130358 - 2027) := by
  show Nat.Prime 113843128331
  exact p113843128331

theorem check_2027 : allC 113843130358 2027 P10k ds_2027 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 113843130358 is 2027. -/
theorem minGB_S_2027 : minGB 113843130358 = 2027 :=
  minGB_eq_of P10k P10k_complete 113843130358 2027 (by norm_num) (by norm_num) prime_sub_2027 ds_2027 check_2027

def ds_2153 : List ℕ := [
    2, 6971, 329143, 3, 5, 3, 11, 3, 7, 347, 3, 3,
    5, 3, 163, 30187, 39883, 3, 3, 5, 3, 3, 11, 37,
    3, 5, 3, 7, 3, 23, 3, 5, 19, 3, 7, 3,
    3, 3, 17, 5167, 83, 3, 5, 3, 29, 3, 3, 3,
    293, 3, 7, 971, 3, 5, 36529, 53, 17, 3, 3, 5,
    3, 12953, 3, 5, 3, 7, 3, 3, 11, 3, 41, 7,
    3, 3, 3, 17257, 13, 3, 5, 3, 1987, 3, 5, 3,
    3, 7, 34729, 3, 5, 3, 13, 11, 3, 5, 3, 20123,
    659, 5, 3, 3, 3, 97, 61, 7, 3, 3, 61687, 19,
    41, 3, 3, 3, 281, 3, 3, 5, 3, 43, 7, 36563,
    3, 3, 11, 613, 3, 5, 3, 29, 3, 3, 3, 11,
    3, 3, 5, 3, 191, 3, 67, 11, 3, 5, 3, 181,
    3, 31, 3, 13, 3, 7, 3, 5, 3, 353, 3, 5,
    3, 61, 3, 5, 7, 1229, 3, 5, 37, 17, 3, 3,
    3, 13, 171023, 3, 5, 3, 3, 19, 3, 5, 3, 3,
    3, 5, 3, 467, 137, 727, 3, 3, 3, 5, 3, 19,
    3, 5, 17, 154153, 3, 3, 23, 601, 103, 3, 3, 3,
    135271, 19, 3, 7, 17, 3, 3, 5, 3, 73, 3659, 3,
    3, 5, 7, 2477, 3, 3, 7, 3, 197, 3, 149, 152639,
    3, 5, 3, 3, 3, 5, 3, 1499, 3, 7, 342803, 5,
    212057, 3, 3, 3, 2063, 13, 3, 5, 3, 31, 3, 5,
    47, 3, 389, 7, 3, 3, 13, 3, 3, 11, 3, 3,
    17, 3, 1709, 5, 3, 11, 3, 3, 3, 3, 3, 3,
    7, 3, 3, 5, 223049, 3, 19, 3, 3, 5, 3, 98347,
    3, 47, 5, 23, 7, 5, 3, 13, 3, 593, 113, 3,
    3, 7, 3, 17, 3, 3, 13, 3, 7, 3, 11, 59,
    5, 3, 37, 3, 1823, 5, 3, 11, 3, 3, 5, 3]

theorem prime_sub_2153 : Nat.Prime (244808993116 - 2153) := by
  show Nat.Prime 244808990963
  exact p244808990963

theorem check_2153 : allC 244808993116 2153 P10k ds_2153 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 244808993116 is 2153. -/
theorem minGB_S_2153 : minGB 244808993116 = 2153 :=
  minGB_eq_of P10k P10k_complete 244808993116 2153 (by norm_num) (by norm_num) prime_sub_2153 ds_2153 check_2153

def ds_2351 : List ℕ := [
    2, 19, 7, 3, 17, 3, 5, 3, 13, 173, 3, 3,
    19, 3, 5, 947, 61, 3, 3, 373, 3, 3, 2143, 7,
    3, 11, 3, 5, 3, 17, 3, 7, 5, 3, 101, 3,
    3, 3, 5, 7, 13, 3, 149, 3, 5, 3, 3, 3,
    5, 3, 11, 73, 3, 48871, 5, 23, 19, 3, 3, 113,
    3, 223, 3, 599, 3, 5, 3, 3, 5, 3, 4253, 47,
    3, 3, 3, 7, 2897, 3, 23, 3, 17, 3, 11, 3,
    3, 5309, 379073, 3, 1597, 3, 5, 41, 3, 13, 3, 29,
    7, 17, 3, 3, 3, 5, 11, 13, 3, 3, 5, 7,
    271, 3, 3, 3, 5, 3, 3, 47, 3, 5, 23603, 37,
    3, 3, 5, 311, 3, 163, 3, 7, 3, 3, 3, 99391,
    3, 3, 7, 3, 43517, 3, 5, 109, 3, 29269, 3, 5,
    3, 19, 3, 5, 3, 2857, 3, 13, 3, 5, 3, 2011,
    3, 7, 3, 134243, 5, 19, 3, 7, 5, 1523, 3, 3,
    3, 7, 2633, 3, 17, 3, 3, 43, 3, 3989, 3, 3,
    3, 11, 3, 5, 37, 353, 3, 3, 3, 154691, 3, 283,
    3, 7, 5, 13, 3, 3, 5, 7, 23, 3, 3, 3,
    59, 5, 3, 1093, 11, 3, 3, 240707, 3, 5, 167, 3,
    3, 101, 5, 29, 3, 3, 19, 3, 5, 3, 7, 17,
    3, 494731, 3, 3, 3, 64513, 3, 5, 3, 643, 23203, 7583,
    19, 3, 3, 3, 11, 7, 3, 139, 3, 13, 3, 7,
    5, 3, 59, 11, 3, 3, 5, 3, 3, 5, 3, 3,
    5, 3, 41, 29, 3, 487, 3, 3, 3, 3, 3, 3,
    5, 3, 3, 7, 43, 3, 5, 3, 3, 97, 3, 5,
    3, 61, 383, 5, 83, 11057, 3, 11, 3, 13, 7, 3,
    3, 5, 3, 499, 3, 3, 5, 3, 137, 3, 7, 29,
    11, 3, 5, 3, 36559, 26371, 3, 13, 3, 3, 277, 3,
    17, 3, 3, 3, 5, 11, 3, 5, 3, 29, 3, 5,
    3, 7, 3, 3, 3, 5, 373, 3, 23, 43, 3, 3]

theorem prime_sub_2351 : Nat.Prime (384619217512 - 2351) := by
  show Nat.Prime 384619215161
  exact p384619215161

theorem check_2351 : allC 384619217512 2351 P10k ds_2351 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 384619217512 is 2351. -/
theorem minGB_S_2351 : minGB 384619217512 = 2351 :=
  minGB_eq_of P10k P10k_complete 384619217512 2351 (by norm_num) (by norm_num) prime_sub_2351 ds_2351 check_2351

end LeanLab.Sinisalo1993
