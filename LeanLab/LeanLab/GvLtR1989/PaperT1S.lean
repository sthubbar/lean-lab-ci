/-
P0042 Granville, van de Lune, te Riele 1989, Checking the Goldbach conjecture on a vector
computer, Number Theory and Applications, Kluwer, 423 to 433, CWI copy ir.cwi.nl/pub/1570.
Read in Claude in Chrome 2026-10-18 from the page images, run 20261018T1103Z-12430, U-0942.
Table 1 S(q) column: minGB S(q) = q for all 35 printed rows; Section 3 text: the three n
below 2·10^10 outside Table 3 with p(n) above 1861, and the Stein-Stein worst case 60119912.
Divisors and Pratt certificates by Python, checked by the kernel. That each S(q) is the LEAST
such n is the authors' search; the lab's Python reproduced all 35 to 4·10^7.
AI-written Lean code, Claude, 2026-10-18. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.Base

namespace LeanLab.GvLtR1989.Paper

open LeanLab.Verifications LeanLab.Verifications.Top50
open LeanLab.Verifications.Pratt (pB)

theorem p15860219 : Nat.Prime 15860219 := by
  refine Pratt.pratt 15860219 2 [(2, 1), (11, 1), (17, 1), (42407, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p17725529 : Nat.Prime 17725529 := by
  refine Pratt.pratt 17725529 3 [(2, 3), (2215691, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p60118819 : Nat.Prime 60118819 := by
  refine Pratt.pratt 60118819 2 [(2, 1), (3, 1), (149, 1), (67247, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p15317793877 : Nat.Prime 15317793877 := by
  refine Pratt.pratt 15317793877 5 [(2, 2), (3, 1), (7, 1), (11, 1), (47, 1), (521, 1), (677, 1)] (by norm_num)
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
theorem p18113545313 : Nat.Prime 18113545313 := by
  refine Pratt.pratt 18113545313 3 [(2, 5), (16421, 1), (34471, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p19326121571 : Nat.Prime 19326121571 := by
  refine Pratt.pratt 19326121571 2 [(2, 1), (5, 1), (7, 1), (37, 1), (311, 1), (23993, 1)] (by norm_num)
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

def ds_S3 : List ℕ := [
    2]

theorem prime_sub_S3 : Nat.Prime (6 - 3) := by
  show Nat.Prime 3
  exact pB (by decide +kernel)

theorem check_S3 : allC 6 3 P10k ds_S3 = true := by decide +kernel

theorem minGB_S3 : minGB 6 = 3 :=
  minGB_eq_of P10k P10k_complete 6 3 (by norm_num) (by norm_num) prime_sub_S3 ds_S3 check_S3

def ds_S5 : List ℕ := [
    2, 3]

theorem prime_sub_S5 : Nat.Prime (12 - 5) := by
  show Nat.Prime 7
  exact pB (by decide +kernel)

theorem check_S5 : allC 12 5 P10k ds_S5 = true := by decide +kernel

theorem minGB_S5 : minGB 12 = 5 :=
  minGB_eq_of P10k P10k_complete 12 5 (by norm_num) (by norm_num) prime_sub_S5 ds_S5 check_S5

def ds_S7 : List ℕ := [
    2, 3, 5]

theorem prime_sub_S7 : Nat.Prime (30 - 7) := by
  show Nat.Prime 23
  exact pB (by decide +kernel)

theorem check_S7 : allC 30 7 P10k ds_S7 = true := by decide +kernel

theorem minGB_S7 : minGB 30 = 7 :=
  minGB_eq_of P10k P10k_complete 30 7 (by norm_num) (by norm_num) prime_sub_S7 ds_S7 check_S7

def ds_S11 : List ℕ := [
    2, 11, 7, 3]

theorem prime_sub_S11 : Nat.Prime (124 - 11) := by
  show Nat.Prime 113
  exact pB (by decide +kernel)

theorem check_S11 : allC 124 11 P10k ds_S11 = true := by decide +kernel

theorem minGB_S11 : minGB 124 = 11 :=
  minGB_eq_of P10k P10k_complete 124 11 (by norm_num) (by norm_num) prime_sub_S11 ds_S11 check_S11

def ds_S13 : List ℕ := [
    2, 7, 3, 5, 3]

theorem prime_sub_S13 : Nat.Prime (122 - 13) := by
  show Nat.Prime 109
  exact pB (by decide +kernel)

theorem check_S13 : allC 122 13 P10k ds_S13 = true := by decide +kernel

theorem minGB_S13 : minGB 122 = 13 :=
  minGB_eq_of P10k P10k_complete 122 13 (by norm_num) (by norm_num) prime_sub_S13 ds_S13 check_S13

def ds_S17 : List ℕ := [
    2, 5, 7, 3, 11, 3]

theorem prime_sub_S17 : Nat.Prime (418 - 17) := by
  show Nat.Prime 401
  exact pB (by decide +kernel)

theorem check_S17 : allC 418 17 P10k ds_S17 = true := by decide +kernel

theorem minGB_S17 : minGB 418 = 17 :=
  minGB_eq_of P10k P10k_complete 418 17 (by norm_num) (by norm_num) prime_sub_S17 ds_S17 check_S17

def ds_S19 : List ℕ := [
    2, 5, 3, 7, 3, 5, 3]

theorem prime_sub_S19 : Nat.Prime (98 - 19) := by
  show Nat.Prime 79
  exact pB (by decide +kernel)

theorem check_S19 : allC 98 19 P10k ds_S19 = true := by decide +kernel

theorem minGB_S19 : minGB 98 = 19 :=
  minGB_eq_of P10k P10k_complete 98 19 (by norm_num) (by norm_num) prime_sub_S19 ds_S19 check_S19

def ds_S23 : List ℕ := [
    2, 7, 5, 3, 11, 3, 7, 3]

theorem prime_sub_S23 : Nat.Prime (220 - 23) := by
  show Nat.Prime 197
  exact pB (by decide +kernel)

theorem check_S23 : allC 220 23 P10k ds_S23 = true := by decide +kernel

theorem minGB_S23 : minGB 220 = 23 :=
  minGB_eq_of P10k P10k_complete 220 23 (by norm_num) (by norm_num) prime_sub_S23 ds_S23 check_S23

def ds_S29 : List ℕ := [
    2, 7, 11, 3, 5, 3, 7, 3, 17]

theorem prime_sub_S29 : Nat.Prime (346 - 29) := by
  show Nat.Prime 317
  exact pB (by decide +kernel)

theorem check_S29 : allC 346 29 P10k ds_S29 = true := by decide +kernel

theorem minGB_S29 : minGB 346 = 29 :=
  minGB_eq_of P10k P10k_complete 346 29 (by norm_num) (by norm_num) prime_sub_S29 ds_S29 check_S29

def ds_S31 : List ℕ := [
    2, 5, 3, 7, 3, 5, 3, 17, 3, 3]

theorem prime_sub_S31 : Nat.Prime (308 - 31) := by
  show Nat.Prime 277
  exact pB (by decide +kernel)

theorem check_S31 : allC 308 31 P10k ds_S31 = true := by decide +kernel

theorem minGB_S31 : minGB 308 = 31 :=
  minGB_eq_of P10k P10k_complete 308 31 (by norm_num) (by norm_num) prime_sub_S31 ds_S31 check_S31

def ds_S37 : List ℕ := [
    2, 31, 3, 7, 3, 13, 3, 5, 3, 3, 11]

theorem prime_sub_S37 : Nat.Prime (1274 - 37) := by
  show Nat.Prime 1237
  exact pB (by decide +kernel)

theorem check_S37 : allC 1274 37 P10k ds_S37 = true := by decide +kernel

theorem minGB_S37 : minGB 1274 = 37 :=
  minGB_eq_of P10k P10k_complete 1274 37 (by norm_num) (by norm_num) prime_sub_S37 ds_S37 check_S37

def ds_S41 : List ℕ := [
    2, 7, 17, 3, 11, 3, 7, 3, 19, 5, 3, 3]

theorem prime_sub_S41 : Nat.Prime (1144 - 41) := by
  show Nat.Prime 1103
  exact pB (by decide +kernel)

theorem check_S41 : allC 1144 41 P10k ds_S41 = true := by decide +kernel

theorem minGB_S41 : minGB 1144 = 41 :=
  minGB_eq_of P10k P10k_complete 1144 41 (by norm_num) (by norm_num) prime_sub_S41 ds_S41 check_S41

def ds_S43 : List ℕ := [
    2, 7, 3, 5, 3, 13, 3, 23, 3, 3, 7, 5,
    3]

theorem prime_sub_S43 : Nat.Prime (962 - 43) := by
  show Nat.Prime 919
  exact pB (by decide +kernel)

theorem check_S43 : allC 962 43 P10k ds_S43 = true := by decide +kernel

theorem minGB_S43 : minGB 962 = 43 :=
  minGB_eq_of P10k P10k_complete 962 43 (by norm_num) (by norm_num) prime_sub_S43 ds_S43 check_S43

def ds_S47 : List ℕ := [
    2, 7, 19, 3, 5, 3, 7, 3, 13, 17, 3, 3,
    5, 3]

theorem prime_sub_S47 : Nat.Prime (556 - 47) := by
  show Nat.Prime 509
  exact pB (by decide +kernel)

theorem check_S47 : allC 556 47 P10k ds_S47 = true := by decide +kernel

theorem minGB_S47 : minGB 556 = 47 :=
  minGB_eq_of P10k P10k_complete 556 47 (by norm_num) (by norm_num) prime_sub_S47 ds_S47 check_S47

def ds_S53 : List ℕ := [
    2, 13, 23, 3, 41, 3, 5, 3, 19, 13, 3, 3,
    7, 3, 5]

theorem prime_sub_S53 : Nat.Prime (2512 - 53) := by
  show Nat.Prime 2459
  exact pB (by decide +kernel)

theorem check_S53 : allC 2512 53 P10k ds_S53 = true := by decide +kernel

theorem minGB_S53 : minGB 2512 = 53 :=
  minGB_eq_of P10k P10k_complete 2512 53 (by norm_num) (by norm_num) prime_sub_S53 ds_S53 check_S53

def ds_S59 : List ℕ := [
    2, 13, 7, 3, 5, 3, 11, 3, 31, 13, 3, 3,
    5, 3, 7, 23]

theorem prime_sub_S59 : Nat.Prime (3526 - 59) := by
  show Nat.Prime 3467
  exact pB (by decide +kernel)

theorem check_S59 : allC 3526 59 P10k ds_S59 = true := by decide +kernel

theorem minGB_S59 : minGB 3526 = 59 :=
  minGB_eq_of P10k P10k_complete 3526 59 (by norm_num) (by norm_num) prime_sub_S59 ds_S59 check_S59

def ds_S61 : List ℕ := [
    2, 7, 3, 5, 3, 37, 3, 29, 3, 3, 7, 5,
    3, 13, 3, 3, 3]

theorem prime_sub_S61 : Nat.Prime (1382 - 61) := by
  show Nat.Prime 1321
  exact pB (by decide +kernel)

theorem check_S61 : allC 1382 61 P10k ds_S61 = true := by decide +kernel

theorem minGB_S61 : minGB 1382 = 61 :=
  minGB_eq_of P10k P10k_complete 1382 61 (by norm_num) (by norm_num) prime_sub_S61 ds_S61 check_S61

def ds_S67 : List ℕ := [
    2, 17, 3, 43, 3, 19, 3, 11, 3, 3, 5, 17,
    3, 7, 3, 3, 3, 5]

theorem prime_sub_S67 : Nat.Prime (1856 - 67) := by
  show Nat.Prime 1789
  exact pB (by decide +kernel)

theorem check_S67 : allC 1856 67 P10k ds_S67 = true := by decide +kernel

theorem minGB_S67 : minGB 1856 = 67 :=
  minGB_eq_of P10k P10k_complete 1856 67 (by norm_num) (by norm_num) prime_sub_S67 ds_S67 check_S67

def ds_S71 : List ℕ := [
    2, 5, 7, 3, 17, 3, 43, 3, 5, 13, 3, 3,
    23, 3, 7, 5, 47, 3, 3]

theorem prime_sub_S71 : Nat.Prime (4618 - 71) := by
  show Nat.Prime 4547
  exact pB (by decide +kernel)

theorem check_S71 : allC 4618 71 P10k ds_S71 = true := by decide +kernel

theorem minGB_S71 : minGB 4618 = 71 :=
  minGB_eq_of P10k P10k_complete 4618 71 (by norm_num) (by norm_num) prime_sub_S71 ds_S71 check_S71

def ds_S73 : List ℕ := [
    2, 23, 3, 5, 3, 11, 3, 7, 3, 3, 31, 5,
    3, 13, 3, 3, 3, 7, 5, 3]

theorem prime_sub_S73 : Nat.Prime (992 - 73) := by
  show Nat.Prime 919
  exact pB (by decide +kernel)

theorem check_S73 : allC 992 73 P10k ds_S73 = true := by decide +kernel

theorem minGB_S73 : minGB 992 = 73 :=
  minGB_eq_of P10k P10k_complete 992 73 (by norm_num) (by norm_num) prime_sub_S73 ds_S73 check_S73

def ds_S79 : List ℕ := [
    2, 5, 3, 37, 3, 5, 3, 29, 3, 3, 7, 19,
    3, 5, 3, 3, 3, 13, 11, 3, 5]

theorem prime_sub_S79 : Nat.Prime (3818 - 79) := by
  show Nat.Prime 3739
  exact pB (by decide +kernel)

theorem check_S79 : allC 3818 79 P10k ds_S79 = true := by decide +kernel

theorem minGB_S79 : minGB 3818 = 79 :=
  minGB_eq_of P10k P10k_complete 3818 79 (by norm_num) (by norm_num) prime_sub_S79 ds_S79 check_S79

def ds_S83 : List ℕ := [
    2, 17, 7, 3, 41, 3, 5, 3, 31, 11, 3, 3,
    19, 3, 5, 47, 73, 3, 3, 17, 3, 3]

theorem prime_sub_S83 : Nat.Prime (7432 - 83) := by
  show Nat.Prime 7349
  exact pB (by decide +kernel)

theorem check_S83 : allC 7432 83 P10k ds_S83 = true := by decide +kernel

theorem minGB_S83 : minGB 7432 = 83 :=
  minGB_eq_of P10k P10k_complete 7432 83 (by norm_num) (by norm_num) prime_sub_S83 ds_S83 check_S83

def ds_S89 : List ℕ := [
    2, 5, 53, 3, 17, 3, 7, 3, 5, 11, 3, 3,
    47, 3, 29, 5, 7, 3, 3, 97, 3, 3, 5]

theorem prime_sub_S89 : Nat.Prime (12778 - 89) := by
  show Nat.Prime 12689
  exact pB (by decide +kernel)

theorem check_S89 : allC 12778 89 P10k ds_S89 = true := by decide +kernel

theorem minGB_S89 : minGB 12778 = 89 :=
  minGB_eq_of P10k P10k_complete 12778 89 (by norm_num) (by norm_num) prime_sub_S89 ds_S89 check_S89

def ds_S97 : List ℕ := [
    2, 5, 3, 7, 3, 5, 3, 59, 3, 3, 19, 13,
    3, 5, 3, 3, 3, 61, 23, 3, 5, 17, 3, 3]

theorem prime_sub_S97 : Nat.Prime (5978 - 97) := by
  show Nat.Prime 5881
  exact pB (by decide +kernel)

theorem check_S97 : allC 5978 97 P10k ds_S97 = true := by decide +kernel

theorem minGB_S97 : minGB 5978 = 97 :=
  minGB_eq_of P10k P10k_complete 5978 97 (by norm_num) (by norm_num) prime_sub_S97 ds_S97 check_S97

def ds_S113 : List ℕ := [
    2, 47, 7, 3, 5, 3, 11, 3, 103, 71, 3, 3,
    5, 3, 7, 13, 73, 3, 3, 5, 3, 3, 11, 7,
    3, 5, 3, 19, 3]

theorem prime_sub_S113 : Nat.Prime (19696 - 113) := by
  show Nat.Prime 19583
  exact pB (by decide +kernel)

theorem check_S113 : allC 19696 113 P10k ds_S113 = true := by decide +kernel

theorem minGB_S113 : minGB 19696 = 113 :=
  minGB_eq_of P10k P10k_complete 19696 113 (by norm_num) (by norm_num) prime_sub_S113 ds_S113 check_S113

def ds_S127 : List ℕ := [
    2, 5, 3, 17, 3, 5, 3, 53, 3, 3, 43, 7,
    3, 5, 3, 3, 3, 19, 13, 3, 5, 7, 3, 3,
    23, 3, 5, 3, 17, 3]

theorem prime_sub_S127 : Nat.Prime (6008 - 127) := by
  show Nat.Prime 5881
  exact pB (by decide +kernel)

theorem check_S127 : allC 6008 127 P10k ds_S127 = true := by decide +kernel

theorem minGB_S127 : minGB 6008 = 127 :=
  minGB_eq_of P10k P10k_complete 6008 127 (by norm_num) (by norm_num) prime_sub_S127 ds_S127 check_S127

def ds_S263 : List ℕ := [
    2, 23, 53, 3, 5, 3, 11, 3, 7, 79, 3, 3,
    5, 3, 19, 373, 127, 3, 3, 5, 3, 3, 11, 641,
    3, 5, 3, 7, 3, 467, 3, 5, 547, 3, 7, 3,
    3, 3, 109, 41, 13, 3, 5, 3, 17, 3, 3, 3,
    227, 3, 7, 47, 3, 5, 13]

theorem prime_sub_S263 : Nat.Prime (485326 - 263) := by
  show Nat.Prime 485063
  exact pB (by decide +kernel)

theorem check_S263 : allC 485326 263 P10k ds_S263 = true := by decide +kernel

theorem minGB_S263 : minGB 485326 = 263 :=
  minGB_eq_of P10k P10k_complete 485326 263 (by norm_num) (by norm_num) prime_sub_S263 ds_S263 check_S263

def ds_S269 : List ℕ := [
    2, 5, 23, 3, 443, 3, 37, 3, 5, 7, 3, 3,
    79, 3, 43, 5, 13, 3, 3, 7, 3, 3, 5, 491,
    3, 137, 3, 191, 3, 5, 3, 17, 13, 3, 167, 3,
    3, 3, 19, 5, 83, 3, 31, 3, 7, 3, 3, 3,
    11, 3, 5, 7, 3, 601, 251, 5]

theorem prime_sub_S269 : Nat.Prime (407128 - 269) := by
  show Nat.Prime 406859
  exact pB (by decide +kernel)

theorem check_S269 : allC 407128 269 P10k ds_S269 = true := by decide +kernel

theorem minGB_S269 : minGB 407128 = 269 :=
  minGB_eq_of P10k P10k_complete 407128 269 (by norm_num) (by norm_num) prime_sub_S269 ds_S269 check_S269

def ds_S271 : List ℕ := [
    2, 5, 3, 23, 3, 5, 3, 157, 3, 3, 37, 31,
    3, 5, 3, 3, 3, 59, 7, 3, 5, 229, 3, 3,
    241, 3, 5, 3, 7, 3, 17, 3, 3, 47, 3, 7,
    67, 5, 3, 3, 3, 13, 3, 5, 3, 199, 359, 5,
    3, 17, 3, 3, 11, 3, 3, 3, 3]

theorem prime_sub_S271 : Nat.Prime (137708 - 271) := by
  show Nat.Prime 137437
  exact pB (by decide +kernel)

theorem check_S271 : allC 137708 271 P10k ds_S271 = true := by decide +kernel

theorem minGB_S271 : minGB 137708 = 271 :=
  minGB_eq_of P10k P10k_complete 137708 271 (by norm_num) (by norm_num) prime_sub_S271 ds_S271 check_S271

def ds_S317 : List ℕ := [
    2, 5, 29, 3, 41, 3, 13, 3, 5, 7, 3, 3,
    151, 3, 109, 5, 17, 3, 3, 7, 3, 3, 5, 67,
    3, 167, 3, 739, 3, 5, 3, 137, 193, 3, 19, 3,
    3, 3, 619, 5, 29, 3, 257, 3, 7, 3, 3, 3,
    11, 3, 5, 7, 3, 13, 41, 5, 379, 3, 3, 7,
    3, 5, 3, 83, 3]

theorem prime_sub_S317 : Nat.Prime (686638 - 317) := by
  show Nat.Prime 686321
  exact pB (by decide +kernel)

theorem check_S317 : allC 686638 317 P10k ds_S317 = true := by decide +kernel

theorem minGB_S317 : minGB 686638 = 317 :=
  minGB_eq_of P10k P10k_complete 686638 317 (by norm_num) (by norm_num) prime_sub_S317 ds_S317 check_S317

def ds_S331 : List ℕ := [
    2, 5, 3, 11, 3, 5, 3, 7, 3, 3, 97, 37,
    3, 5, 3, 3, 3, 7, 53, 3, 5, 13, 3, 3,
    89, 3, 5, 3, 79, 3, 19, 3, 3, 11, 3, 313,
    13, 5, 3, 3, 3, 131, 3, 5, 3, 73, 199, 5,
    3, 7, 3, 3, 19, 3, 3, 3, 3, 7, 17, 3,
    5, 3, 29, 3, 5, 3]

theorem prime_sub_S331 : Nat.Prime (128168 - 331) := by
  show Nat.Prime 127837
  exact pB (by decide +kernel)

theorem check_S331 : allC 128168 331 P10k ds_S331 = true := by decide +kernel

theorem minGB_S331 : minGB 128168 = 331 :=
  minGB_eq_of P10k P10k_complete 128168 331 (by norm_num) (by norm_num) prime_sub_S331 ds_S331 check_S331

def ds_S569 : List ℕ := [
    2, 5, 7, 3, 17, 3, 2833, 3, 5, 19, 3, 3,
    569, 3, 7, 5, 523, 3, 3, 11, 3, 3, 5, 7,
    3, 37, 3, 103, 3, 5, 3, 7, 11, 3, 2297, 3,
    3, 3, 29, 5, 467, 3, 109, 3, 59, 3, 3, 3,
    251, 3, 5, 647, 3, 23, 7, 5, 11, 3, 3, 41,
    3, 5, 3, 73, 3, 17, 3, 3, 743, 3, 5, 151,
    3, 3, 3, 5, 23, 3, 11, 3, 17, 3, 1699, 3,
    3, 5, 2153, 3, 3919, 3, 7, 3821, 3, 3769, 3, 5,
    7, 17, 3, 3, 3, 1511, 5]

theorem prime_sub_S569 : Nat.Prime (17726098 - 569) := by
  show Nat.Prime 17725529
  exact p17725529

theorem check_S569 : allC 17726098 569 P10k ds_S569 = true := by decide +kernel

theorem minGB_S569 : minGB 17726098 = 569 :=
  minGB_eq_of P10k P10k_complete 17726098 569 (by norm_num) (by norm_num) prime_sub_S569 ds_S569 check_S569

def ds_S571 : List ℕ := [
    2, 5, 3, 17, 3, 5, 3, 997, 3, 3, 11, 7,
    3, 5, 3, 3, 3, 13, 131, 3, 5, 7, 3, 3,
    11, 3, 5, 3, 17, 3, 43, 3, 3, 13, 3, 29,
    47, 5, 3, 3, 3, 37, 3, 5, 3, 503, 17, 5,
    3, 11, 3, 3, 23, 3, 3, 3, 3, 223, 67, 3,
    5, 3, 283, 3, 5, 3, 7, 593, 3, 41, 3, 3,
    257, 5, 23, 3, 3, 19, 3, 109, 3, 61, 3, 5,
    47, 3, 3, 7, 3, 5, 3, 3, 227, 3, 7, 3,
    3, 3, 5, 7, 71, 3, 3, 3]

theorem prime_sub_S571 : Nat.Prime (4493498 - 571) := by
  show Nat.Prime 4492927
  exact pB (by decide +kernel)

theorem check_S571 : allC 4493498 571 P10k ds_S571 = true := by decide +kernel

theorem minGB_S571 : minGB 4493498 = 571 :=
  minGB_eq_of P10k P10k_complete 4493498 571 (by norm_num) (by norm_num) prime_sub_S571 ds_S571 check_S571

def ds_S599 : List ℕ := [
    2, 5, 17, 3, 3877, 3, 11, 3, 5, 7, 3, 3,
    23, 3, 379, 5, 2339, 3, 3, 7, 3, 3, 5, 443,
    3, 107, 3, 17, 3, 5, 3, 19, 2293, 3, 11, 3,
    3, 3, 29, 5, 23, 3, 137, 3, 7, 3, 3, 3,
    673, 3, 5, 7, 3, 97, 31, 5, 61, 3, 3, 7,
    3, 5, 3, 13, 3, 23, 3, 3, 11, 3, 5, 19,
    3, 3, 3, 5, 13, 3, 1087, 3, 41, 3, 83, 3,
    3, 5, 7, 3, 433, 3, 13, 11, 3, 7, 3, 5,
    37, 157, 3, 3, 3, 359, 5, 43, 3, 3, 19, 5]

theorem prime_sub_S599 : Nat.Prime (15860818 - 599) := by
  show Nat.Prime 15860219
  exact p15860219

theorem check_S599 : allC 15860818 599 P10k ds_S599 = true := by decide +kernel

theorem minGB_S599 : minGB 15860818 = 599 :=
  minGB_eq_of P10k P10k_complete 15860818 599 (by norm_num) (by norm_num) prime_sub_S599 ds_S599 check_S599

def ds_S601 : List ℕ := [
    2, 7, 3, 5, 3, 17, 3, 37, 3, 3, 7, 5,
    3, 29, 3, 3, 3, 293, 5, 3, 7, 23, 3, 3,
    5, 3, 19, 3, 223, 3, 5, 3, 3, 71, 3, 13,
    5, 577, 3, 3, 3, 11, 3, 113, 3, 7, 757, 61,
    3, 13, 3, 3, 7, 3, 3, 3, 3, 449, 5, 3,
    7, 3, 5, 3, 11, 3, 19, 5, 3, 281, 3, 3,
    5, 191, 11, 3, 3, 5, 3, 7, 3, 17, 3, 89,
    167, 3, 3, 5, 3, 13, 3, 3, 5, 3, 503, 3,
    3, 3, 17, 13, 5, 3, 3, 3, 373, 5, 3, 3,
    3]

theorem prime_sub_S601 : Nat.Prime (1077422 - 601) := by
  show Nat.Prime 1076821
  exact pB (by decide +kernel)

theorem check_S601 : allC 1077422 601 P10k ds_S601 = true := by decide +kernel

theorem minGB_S601 : minGB 1077422 = 601 :=
  minGB_eq_of P10k P10k_complete 1077422 601 (by norm_num) (by norm_num) prime_sub_S601 ds_S601 check_S601

def ds_n18113547184 : List ℕ := [
    2, 2617, 7, 3, 37, 3, 23, 3, 283, 5, 3, 3,
    103, 3, 7, 967, 5, 3, 3, 31727, 3, 3, 13, 5,
    3, 43, 3, 19, 3, 41, 3, 7, 271, 3, 5, 3,
    3, 3, 331, 7, 5, 3, 34511, 3, 751, 3, 3, 3,
    11, 3, 37, 5, 3, 577, 7, 149, 5, 3, 3, 17,
    3, 11, 3, 1217, 3, 13, 3, 3, 79, 3, 127, 5,
    3, 3, 3, 7, 5, 3, 10753, 3, 5, 3, 23, 3,
    3, 223, 5, 3, 211, 3, 7, 5, 3, 11, 3, 67,
    5, 263, 3, 3, 3, 11, 19, 5, 3, 3, 17, 7,
    5, 3, 3, 3, 43, 3, 3, 31, 3, 29, 3659, 5,
    3, 3, 7, 8707, 3, 71, 3, 5, 3, 3, 3, 94229,
    3, 3, 7, 3, 151, 3, 1951, 5, 3, 11, 3, 31,
    3, 5, 3, 97, 3, 13, 3, 491, 3, 7, 3, 251,
    3, 5, 3, 13, 8467, 11, 3, 7, 109, 23, 3, 3,
    3, 7, 5, 3, 47, 3, 3, 5, 3, 23893, 3, 3,
    3, 3643, 3, 7, 13099, 5, 3, 3, 3, 11, 3, 89,
    3, 7, 61, 73, 3, 3, 11, 7, 5, 3, 3, 3,
    5, 103, 3, 11, 5, 3, 3, 17, 3, 7, 5, 3,
    3, 19, 193, 257, 3, 3, 5, 3, 199, 3, 7, 5,
    3, 743, 3, 3, 3, 11, 3, 13, 3, 59, 5, 349,
    163, 3, 3, 3, 61, 5, 3, 31, 3, 1433, 3, 7,
    17, 3, 11, 5, 3, 3, 191, 3, 3, 7591, 3, 3,
    89, 3, 5, 13, 3, 653, 3, 3, 3, 3, 3, 3,
    37, 3, 3, 7, 15649, 3, 59, 3, 3]

theorem prime_sub_n18113547184 : Nat.Prime (18113547184 - 1871) := by
  show Nat.Prime 18113545313
  exact p18113545313

theorem check_n18113547184 : allC 18113547184 1871 P10k ds_n18113547184 = true := by decide +kernel

theorem minGB_n18113547184 : minGB 18113547184 = 1871 :=
  minGB_eq_of P10k P10k_complete 18113547184 1871 (by norm_num) (by norm_num) prime_sub_n18113547184 ds_n18113547184 check_n18113547184

def ds_n19326123574 : List ℕ := [
    2, 31, 1583, 3, 191, 3, 13, 3, 7, 5, 3, 3,
    71, 3, 127, 34939, 5, 3, 3, 181, 3, 3, 113093, 5,
    3, 101159, 3, 7, 3, 5563, 3, 11, 941, 3, 5, 3,
    3, 3, 82633, 13, 5, 3, 7, 3, 11, 3, 3, 3,
    43, 3, 7, 5, 3, 13, 89, 11, 5, 3, 3, 1201,
    3, 463, 3, 167, 3, 7, 3, 3, 16519, 3, 23, 5,
    3, 3, 3, 1877, 5, 3, 7, 3, 5, 3, 50177, 3,
    3, 7, 5, 3, 11, 3, 17, 5, 3, 23, 3, 607,
    5, 101, 3, 3, 3, 829, 13, 5, 3, 3, 467, 11,
    5, 3, 3, 3, 29, 3, 3, 13, 3, 149, 7, 5,
    3, 3, 19, 41, 3, 163, 3, 5, 3, 3, 3, 43,
    3, 3, 457, 3, 17, 3, 13, 5, 3, 7, 3, 47,
    3, 5, 3, 11, 3, 7, 3, 137, 3, 1019, 3, 61,
    3, 5, 3, 83, 7, 13, 3, 4519, 17, 2657, 3, 3,
    3, 389, 5, 3, 7, 3, 3, 5, 3, 53, 3, 3,
    3, 135581, 3, 827, 103, 5, 3, 3, 3, 59, 3, 6317,
    3, 17, 11, 227, 3, 3, 193, 37483, 5, 3, 3, 3,
    5, 61, 3, 7, 5, 3, 3, 37, 3, 991, 5, 3,
    3, 19, 7, 18287, 3, 3, 5, 3, 110543, 3, 1427, 5,
    3, 7, 3, 3, 3, 547, 3, 17, 3, 7, 5, 18553,
    37, 3, 3, 3, 31, 5, 3, 127, 3, 11, 3, 1453,
    1741, 3, 58031, 5, 3, 3, 1171, 3, 3, 41, 3, 3,
    53, 3, 5, 103, 3, 13, 3, 3, 3, 3, 3, 3,
    7, 3, 3, 13, 251, 3, 11, 3, 3, 7, 3, 54443,
    3, 5, 18457, 10193, 7, 19, 3, 5, 3, 10853, 5, 3,
    3, 7, 3]

theorem prime_sub_n19326123574 : Nat.Prime (19326123574 - 2003) := by
  show Nat.Prime 19326121571
  exact p19326121571

theorem check_n19326123574 : allC 19326123574 2003 P10k ds_n19326123574 = true := by decide +kernel

theorem minGB_n19326123574 : minGB 19326123574 = 2003 :=
  minGB_eq_of P10k P10k_complete 19326123574 2003 (by norm_num) (by norm_num) prime_sub_n19326123574 ds_n19326123574 check_n19326123574

def ds_n15317795894 : List ℕ := [
    2, 6959, 3, 38177, 3, 59, 3, 5, 3, 3, 479, 7,
    3, 149, 3, 3, 3, 109, 61, 3, 17, 5, 3, 3,
    37, 3, 14639, 3, 5, 3, 557, 3, 3, 5, 3, 91943,
    23, 7, 3, 3, 3, 11, 3, 13, 3, 5, 107, 31,
    3, 5, 3, 3, 191, 3, 3, 3, 3, 13, 17, 3,
    19, 3, 32941, 3, 11, 3, 7, 15373, 3, 5, 3, 3,
    59, 7, 5, 3, 3, 19, 3, 5, 3, 30313, 3, 23,
    5, 3, 3, 7, 3, 21937, 3, 3, 23189, 3, 5, 3,
    3, 3, 53, 7, 13469, 3, 3, 3, 23, 11, 3, 3,
    3, 449, 281, 39829, 3, 5, 100523, 3, 11, 3, 3, 3,
    13, 81637, 3, 3, 67, 3, 5, 3, 83, 55711, 5, 3,
    7, 1571, 3, 5, 3, 17, 3, 3, 983, 3, 103, 3,
    5, 3, 19, 3, 5, 3, 7, 3, 353, 3, 11, 3,
    5, 3, 47, 3, 3, 3, 19, 3, 3, 3, 17, 233,
    5, 3, 3, 41, 3, 953, 5, 3, 13, 3, 3727, 5,
    7, 3, 17, 3, 3, 3, 137, 23, 5, 3, 31, 3,
    7, 3, 3, 3, 29, 7, 3, 3, 3, 108707, 11, 5,
    3, 3, 5, 3, 3, 1951, 7, 3, 11, 3, 3, 15787,
    32321, 3, 3, 3, 7, 5, 3, 7, 3, 5, 3, 3,
    91141, 3, 257, 5, 11299, 3, 43, 3, 5, 3, 3, 3,
    3, 61, 3733, 5, 3, 3, 11, 3, 5, 3, 13, 3,
    3, 5, 3, 3, 167, 491, 3, 131, 127, 3, 5, 49807,
    3, 5, 3, 3, 29, 3, 43, 120623, 13, 5, 8429, 47,
    3, 5, 7, 3, 3, 11, 3, 79, 101, 3, 37, 3,
    5, 3, 3, 3, 3, 3, 199, 3, 23, 3, 3, 13,
    19, 3, 5, 3, 7]

theorem prime_sub_n15317795894 : Nat.Prime (15317795894 - 2017) := by
  show Nat.Prime 15317793877
  exact p15317793877

theorem check_n15317795894 : allC 15317795894 2017 P10k ds_n15317795894 = true := by decide +kernel

theorem minGB_n15317795894 : minGB 15317795894 = 2017 :=
  minGB_eq_of P10k P10k_complete 15317795894 2017 (by norm_num) (by norm_num) prime_sub_n15317795894 ds_n15317795894 check_n15317795894

def ds_n60119912 : List ℕ := [
    2, 47, 3, 5, 3, 7, 3, 383, 3, 3, 31, 5,
    3, 79, 3, 3, 3, 11, 5, 3, 13, 167, 3, 3,
    5, 3, 2719, 3, 17, 3, 5, 3, 3, 7, 3, 13,
    5, 173, 3, 3, 3, 7, 3, 11, 3, 109, 17, 7,
    3, 13, 3, 3, 283, 3, 3, 3, 3, 127, 5, 3,
    19, 3, 5, 3, 17, 3, 29, 5, 3, 7, 3, 3,
    5, 23, 47, 3, 3, 5, 3, 113, 3, 1069, 3, 7,
    83, 3, 3, 5, 3, 13, 3, 3, 5, 3, 37, 3,
    3, 3, 11, 13, 5, 3, 3, 3, 101, 5, 3, 3,
    3, 7, 5, 137, 3, 13, 2969, 3, 7, 3, 3, 3,
    47, 223, 3, 3, 61, 3, 43, 3, 5, 71, 19, 3,
    41, 5, 3, 7, 3, 5, 3, 3, 7, 3, 17, 3,
    4027, 3, 7, 3, 59, 3, 5, 3, 139, 3, 5, 3,
    11, 3, 5, 3, 3, 3, 5, 3, 3, 3, 79, 5,
    13, 3, 3, 7, 3, 127, 4507, 3, 11, 3, 7, 2531,
    5, 3]

theorem prime_sub_n60119912 : Nat.Prime (60119912 - 1093) := by
  show Nat.Prime 60118819
  exact p60118819

theorem check_n60119912 : allC 60119912 1093 P10k ds_n60119912 = true := by decide +kernel

theorem minGB_n60119912 : minGB 60119912 = 1093 :=
  minGB_eq_of P10k P10k_complete 60119912 1093 (by norm_num) (by norm_num) prime_sub_n60119912 ds_n60119912 check_n60119912

end LeanLab.GvLtR1989.Paper
