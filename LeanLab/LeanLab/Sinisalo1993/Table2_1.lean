/-
P0041 Sinisalo 1993, Table 2, rows 1 to 17: for each listed prime p and its
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


def ds_3 : List ℕ := [
    2]

theorem prime_sub_3 : Nat.Prime (6 - 3) := by
  show Nat.Prime 3
  exact pB (by decide +kernel)

theorem check_3 : allC 6 3 P10k ds_3 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 6 is 3. -/
theorem minGB_S_3 : minGB 6 = 3 :=
  minGB_eq_of P10k P10k_complete 6 3 (by norm_num) (by norm_num) prime_sub_3 ds_3 check_3

def ds_5 : List ℕ := [
    2, 3]

theorem prime_sub_5 : Nat.Prime (12 - 5) := by
  show Nat.Prime 7
  exact pB (by decide +kernel)

theorem check_5 : allC 12 5 P10k ds_5 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 12 is 5. -/
theorem minGB_S_5 : minGB 12 = 5 :=
  minGB_eq_of P10k P10k_complete 12 5 (by norm_num) (by norm_num) prime_sub_5 ds_5 check_5

def ds_7 : List ℕ := [
    2, 3, 5]

theorem prime_sub_7 : Nat.Prime (30 - 7) := by
  show Nat.Prime 23
  exact pB (by decide +kernel)

theorem check_7 : allC 30 7 P10k ds_7 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 30 is 7. -/
theorem minGB_S_7 : minGB 30 = 7 :=
  minGB_eq_of P10k P10k_complete 30 7 (by norm_num) (by norm_num) prime_sub_7 ds_7 check_7

def ds_11 : List ℕ := [
    2, 11, 7, 3]

theorem prime_sub_11 : Nat.Prime (124 - 11) := by
  show Nat.Prime 113
  exact pB (by decide +kernel)

theorem check_11 : allC 124 11 P10k ds_11 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 124 is 11. -/
theorem minGB_S_11 : minGB 124 = 11 :=
  minGB_eq_of P10k P10k_complete 124 11 (by norm_num) (by norm_num) prime_sub_11 ds_11 check_11

def ds_17 : List ℕ := [
    2, 5, 7, 3, 11, 3]

theorem prime_sub_17 : Nat.Prime (418 - 17) := by
  show Nat.Prime 401
  exact pB (by decide +kernel)

theorem check_17 : allC 418 17 P10k ds_17 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 418 is 17. -/
theorem minGB_S_17 : minGB 418 = 17 :=
  minGB_eq_of P10k P10k_complete 418 17 (by norm_num) (by norm_num) prime_sub_17 ds_17 check_17

def ds_37 : List ℕ := [
    2, 31, 3, 7, 3, 13, 3, 5, 3, 3, 11]

theorem prime_sub_37 : Nat.Prime (1274 - 37) := by
  show Nat.Prime 1237
  exact pB (by decide +kernel)

theorem check_37 : allC 1274 37 P10k ds_37 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 1274 is 37. -/
theorem minGB_S_37 : minGB 1274 = 37 :=
  minGB_eq_of P10k P10k_complete 1274 37 (by norm_num) (by norm_num) prime_sub_37 ds_37 check_37

def ds_53 : List ℕ := [
    2, 13, 23, 3, 41, 3, 5, 3, 19, 13, 3, 3,
    7, 3, 5]

theorem prime_sub_53 : Nat.Prime (2512 - 53) := by
  show Nat.Prime 2459
  exact pB (by decide +kernel)

theorem check_53 : allC 2512 53 P10k ds_53 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 2512 is 53. -/
theorem minGB_S_53 : minGB 2512 = 53 :=
  minGB_eq_of P10k P10k_complete 2512 53 (by norm_num) (by norm_num) prime_sub_53 ds_53 check_53

def ds_59 : List ℕ := [
    2, 13, 7, 3, 5, 3, 11, 3, 31, 13, 3, 3,
    5, 3, 7, 23]

theorem prime_sub_59 : Nat.Prime (3526 - 59) := by
  show Nat.Prime 3467
  exact pB (by decide +kernel)

theorem check_59 : allC 3526 59 P10k ds_59 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 3526 is 59. -/
theorem minGB_S_59 : minGB 3526 = 59 :=
  minGB_eq_of P10k P10k_complete 3526 59 (by norm_num) (by norm_num) prime_sub_59 ds_59 check_59

def ds_71 : List ℕ := [
    2, 5, 7, 3, 17, 3, 43, 3, 5, 13, 3, 3,
    23, 3, 7, 5, 47, 3, 3]

theorem prime_sub_71 : Nat.Prime (4618 - 71) := by
  show Nat.Prime 4547
  exact pB (by decide +kernel)

theorem check_71 : allC 4618 71 P10k ds_71 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 4618 is 71. -/
theorem minGB_S_71 : minGB 4618 = 71 :=
  minGB_eq_of P10k P10k_complete 4618 71 (by norm_num) (by norm_num) prime_sub_71 ds_71 check_71

def ds_83 : List ℕ := [
    2, 17, 7, 3, 41, 3, 5, 3, 31, 11, 3, 3,
    19, 3, 5, 47, 73, 3, 3, 17, 3, 3]

theorem prime_sub_83 : Nat.Prime (7432 - 83) := by
  show Nat.Prime 7349
  exact pB (by decide +kernel)

theorem check_83 : allC 7432 83 P10k ds_83 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 7432 is 83. -/
theorem minGB_S_83 : minGB 7432 = 83 :=
  minGB_eq_of P10k P10k_complete 7432 83 (by norm_num) (by norm_num) prime_sub_83 ds_83 check_83

def ds_89 : List ℕ := [
    2, 5, 53, 3, 17, 3, 7, 3, 5, 11, 3, 3,
    47, 3, 29, 5, 7, 3, 3, 97, 3, 3, 5]

theorem prime_sub_89 : Nat.Prime (12778 - 89) := by
  show Nat.Prime 12689
  exact pB (by decide +kernel)

theorem check_89 : allC 12778 89 P10k ds_89 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 12778 is 89. -/
theorem minGB_S_89 : minGB 12778 = 89 :=
  minGB_eq_of P10k P10k_complete 12778 89 (by norm_num) (by norm_num) prime_sub_89 ds_89 check_89

def ds_101 : List ℕ := [
    2, 5, 97, 3, 19, 3, 11, 3, 5, 131, 3, 3,
    71, 3, 109, 5, 13, 3, 3, 17, 3, 3, 5, 31,
    3]

theorem prime_sub_101 : Nat.Prime (26098 - 101) := by
  show Nat.Prime 25997
  exact pB (by decide +kernel)

theorem check_101 : allC 26098 101 P10k ds_101 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 26098 is 101. -/
theorem minGB_S_101 : minGB 26098 = 101 :=
  minGB_eq_of P10k P10k_complete 26098 101 (by norm_num) (by norm_num) prime_sub_101 ds_101 check_101

def ds_131 : List ℕ := [
    2, 179, 17, 3, 7, 3, 5, 3, 47, 127, 3, 3,
    13, 3, 5, 7, 11, 3, 3, 149, 3, 3, 23, 67,
    3, 73, 3, 5, 3, 53, 3]

theorem prime_sub_131 : Nat.Prime (34192 - 131) := by
  show Nat.Prime 34061
  exact pB (by decide +kernel)

theorem check_131 : allC 34192 131 P10k ds_131 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 34192 is 131. -/
theorem minGB_S_131 : minGB 34192 = 131 :=
  minGB_eq_of P10k P10k_complete 34192 131 (by norm_num) (by norm_num) prime_sub_131 ds_131 check_131

def ds_149 : List ℕ := [
    2, 5, 11, 3, 17, 3, 7, 3, 5, 13, 3, 3,
    31, 3, 67, 5, 7, 3, 3, 11, 3, 3, 5, 41,
    3, 7, 3, 13, 3, 5, 3, 61, 11, 3]

theorem prime_sub_149 : Nat.Prime (37768 - 149) := by
  show Nat.Prime 37619
  exact pB (by decide +kernel)

theorem check_149 : allC 37768 149 P10k ds_149 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 37768 is 149. -/
theorem minGB_S_149 : minGB 37768 = 149 :=
  minGB_eq_of P10k P10k_complete 37768 149 (by norm_num) (by norm_num) prime_sub_149 ds_149 check_149

def ds_167 : List ℕ := [
    2, 181, 139, 3, 37, 3, 89, 3, 13, 5, 3, 3,
    11, 3, 131, 31, 5, 3, 3, 7, 3, 3, 19, 5,
    3, 13, 3, 11, 3, 7, 3, 191, 23, 3, 5, 3,
    3, 3]

theorem prime_sub_167 : Nat.Prime (59914 - 167) := by
  show Nat.Prime 59747
  exact pB (by decide +kernel)

theorem check_167 : allC 59914 167 P10k ds_167 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 59914 is 167. -/
theorem minGB_S_167 : minGB 59914 = 167 :=
  minGB_eq_of P10k P10k_complete 59914 167 (by norm_num) (by norm_num) prime_sub_167 ds_167 check_167

def ds_179 : List ℕ := [
    2, 47, 7, 3, 5, 3, 29, 3, 37, 17, 3, 3,
    5, 3, 7, 89, 83, 3, 3, 5, 3, 3, 107, 7,
    3, 5, 3, 71, 3, 13, 3, 5, 11, 3, 151, 3,
    3, 3, 23, 7]

theorem prime_sub_179 : Nat.Prime (88786 - 179) := by
  show Nat.Prime 88607
  exact pB (by decide +kernel)

theorem check_179 : allC 88786 179 P10k ds_179 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 88786 is 179. -/
theorem minGB_S_179 : minGB 88786 = 179 :=
  minGB_eq_of P10k P10k_complete 88786 179 (by norm_num) (by norm_num) prime_sub_179 ds_179 check_179

def ds_191 : List ℕ := [
    2, 5, 59, 3, 11, 3, 239, 3, 5, 43, 3, 3,
    7, 3, 13, 5, 199, 3, 3, 151, 3, 3, 5, 19,
    3, 101, 3, 61, 3, 5, 3, 163, 17, 3, 31, 3,
    3, 3, 7, 5, 23, 3]

theorem prime_sub_191 : Nat.Prime (97768 - 191) := by
  show Nat.Prime 97577
  exact pB (by decide +kernel)

theorem check_191 : allC 97768 191 P10k ds_191 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 97768 is 191. -/
theorem minGB_S_191 : minGB 97768 = 191 :=
  minGB_eq_of P10k P10k_complete 97768 191 (by norm_num) (by norm_num) prime_sub_191 ds_191 check_191

end LeanLab.Sinisalo1993
