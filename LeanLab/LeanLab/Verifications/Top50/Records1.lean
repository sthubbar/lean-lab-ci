/-
OEIS A025018 and A025019, the records of the least Goldbach prime, rows 1 to 23: `minGB n = p` for each row, zero sorry.
Divisors and Pratt certificates found by Python, checked by the Lean kernel.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.Base

namespace LeanLab.Verifications.Top50.Records1

open LeanLab.Verifications LeanLab.Verifications.Top50
open LeanLab.Verifications.Pratt (pB)


def ds_2 : List ℕ := []

theorem prime_sub_2 : Nat.Prime (4 - 2) := by
  show Nat.Prime 2
  exact pB (by decide +kernel)

theorem check_2 : allC 4 2 P10k ds_2 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 4 is 2. -/
theorem minGB_2 : minGB 4 = 2 :=
  minGB_eq_of P10k P10k_complete 4 2 (by norm_num) (by norm_num) prime_sub_2 ds_2 check_2

def ds_3 : List ℕ := [
    2]

theorem prime_sub_3 : Nat.Prime (6 - 3) := by
  show Nat.Prime 3
  exact pB (by decide +kernel)

theorem check_3 : allC 6 3 P10k ds_3 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 6 is 3. -/
theorem minGB_3 : minGB 6 = 3 :=
  minGB_eq_of P10k P10k_complete 6 3 (by norm_num) (by norm_num) prime_sub_3 ds_3 check_3

def ds_5 : List ℕ := [
    2, 3]

theorem prime_sub_5 : Nat.Prime (12 - 5) := by
  show Nat.Prime 7
  exact pB (by decide +kernel)

theorem check_5 : allC 12 5 P10k ds_5 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 12 is 5. -/
theorem minGB_5 : minGB 12 = 5 :=
  minGB_eq_of P10k P10k_complete 12 5 (by norm_num) (by norm_num) prime_sub_5 ds_5 check_5

def ds_7 : List ℕ := [
    2, 3, 5]

theorem prime_sub_7 : Nat.Prime (30 - 7) := by
  show Nat.Prime 23
  exact pB (by decide +kernel)

theorem check_7 : allC 30 7 P10k ds_7 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 30 is 7. -/
theorem minGB_7 : minGB 30 = 7 :=
  minGB_eq_of P10k P10k_complete 30 7 (by norm_num) (by norm_num) prime_sub_7 ds_7 check_7

def ds_19 : List ℕ := [
    2, 5, 3, 7, 3, 5, 3]

theorem prime_sub_19 : Nat.Prime (98 - 19) := by
  show Nat.Prime 79
  exact pB (by decide +kernel)

theorem check_19 : allC 98 19 P10k ds_19 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 98 is 19. -/
theorem minGB_19 : minGB 98 = 19 :=
  minGB_eq_of P10k P10k_complete 98 19 (by norm_num) (by norm_num) prime_sub_19 ds_19 check_19

def ds_23 : List ℕ := [
    2, 7, 5, 3, 11, 3, 7, 3]

theorem prime_sub_23 : Nat.Prime (220 - 23) := by
  show Nat.Prime 197
  exact pB (by decide +kernel)

theorem check_23 : allC 220 23 P10k ds_23 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 220 is 23. -/
theorem minGB_23 : minGB 220 = 23 :=
  minGB_eq_of P10k P10k_complete 220 23 (by norm_num) (by norm_num) prime_sub_23 ds_23 check_23

def ds_31 : List ℕ := [
    2, 5, 3, 7, 3, 5, 3, 17, 3, 3]

theorem prime_sub_31 : Nat.Prime (308 - 31) := by
  show Nat.Prime 277
  exact pB (by decide +kernel)

theorem check_31 : allC 308 31 P10k ds_31 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 308 is 31. -/
theorem minGB_31 : minGB 308 = 31 :=
  minGB_eq_of P10k P10k_complete 308 31 (by norm_num) (by norm_num) prime_sub_31 ds_31 check_31

def ds_47 : List ℕ := [
    2, 7, 19, 3, 5, 3, 7, 3, 13, 17, 3, 3,
    5, 3]

theorem prime_sub_47 : Nat.Prime (556 - 47) := by
  show Nat.Prime 509
  exact pB (by decide +kernel)

theorem check_47 : allC 556 47 P10k ds_47 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 556 is 47. -/
theorem minGB_47 : minGB 556 = 47 :=
  minGB_eq_of P10k P10k_complete 556 47 (by norm_num) (by norm_num) prime_sub_47 ds_47 check_47

def ds_73 : List ℕ := [
    2, 23, 3, 5, 3, 11, 3, 7, 3, 3, 31, 5,
    3, 13, 3, 3, 3, 7, 5, 3]

theorem prime_sub_73 : Nat.Prime (992 - 73) := by
  show Nat.Prime 919
  exact pB (by decide +kernel)

theorem check_73 : allC 992 73 P10k ds_73 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 992 is 73. -/
theorem minGB_73 : minGB 992 = 73 :=
  minGB_eq_of P10k P10k_complete 992 73 (by norm_num) (by norm_num) prime_sub_73 ds_73 check_73

def ds_103 : List ℕ := [
    2, 7, 3, 5, 3, 11, 3, 43, 3, 3, 7, 5,
    3, 23, 3, 3, 3, 29, 5, 3, 7, 11, 3, 3,
    5, 3]

theorem prime_sub_103 : Nat.Prime (2642 - 103) := by
  show Nat.Prime 2539
  exact pB (by decide +kernel)

theorem check_103 : allC 2642 103 P10k ds_103 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 2642 is 103. -/
theorem minGB_103 : minGB 2642 = 103 :=
  minGB_eq_of P10k P10k_complete 2642 103 (by norm_num) (by norm_num) prime_sub_103 ds_103 check_103

def ds_139 : List ℕ := [
    2, 7, 3, 5, 3, 23, 3, 53, 3, 3, 7, 5,
    3, 73, 3, 3, 3, 47, 5, 3, 7, 67, 3, 3,
    5, 3, 11, 3, 19, 3, 5, 3, 3]

theorem prime_sub_139 : Nat.Prime (5372 - 139) := by
  show Nat.Prime 5233
  exact pB (by decide +kernel)

theorem check_139 : allC 5372 139 P10k ds_139 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 5372 is 139. -/
theorem minGB_139 : minGB 5372 = 139 :=
  minGB_eq_of P10k P10k_complete 5372 139 (by norm_num) (by norm_num) prime_sub_139 ds_139 check_139

def ds_173 : List ℕ := [
    2, 13, 41, 3, 5, 3, 31, 3, 11, 13, 3, 3,
    5, 3, 47, 73, 53, 3, 3, 5, 3, 3, 7, 11,
    3, 5, 3, 13, 3, 71, 3, 5, 37, 3, 19, 3,
    3, 3, 7]

theorem prime_sub_173 : Nat.Prime (7426 - 173) := by
  show Nat.Prime 7253
  exact pB (by decide +kernel)

theorem check_173 : allC 7426 173 P10k ds_173 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 7426 is 173. -/
theorem minGB_173 : minGB 7426 = 173 :=
  minGB_eq_of P10k P10k_complete 7426 173 (by norm_num) (by norm_num) prime_sub_173 ds_173 check_173

def ds_211 : List ℕ := [
    2, 19, 3, 5, 3, 7, 3, 53, 3, 3, 41, 5,
    3, 157, 3, 3, 3, 29, 5, 3, 13, 19, 3, 3,
    5, 3, 137, 3, 173, 3, 5, 3, 3, 7, 3, 13,
    5, 31, 3, 3, 3, 7, 3, 19, 3, 17]

theorem prime_sub_211 : Nat.Prime (43532 - 211) := by
  show Nat.Prime 43321
  exact pB (by decide +kernel)

theorem check_211 : allC 43532 211 P10k ds_211 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 43532 is 211. -/
theorem minGB_211 : minGB 43532 = 211 :=
  minGB_eq_of P10k P10k_complete 43532 211 (by norm_num) (by norm_num) prime_sub_211 ds_211 check_211

def ds_233 : List ℕ := [
    2, 11, 73, 3, 193, 3, 211, 3, 59, 5, 3, 3,
    67, 3, 11, 47, 5, 3, 3, 7, 3, 3, 41, 5,
    3, 29, 3, 43, 3, 7, 3, 53, 61, 3, 5, 3,
    3, 3, 17, 139, 5, 3, 191, 3, 7, 3, 3, 3,
    19, 3]

theorem prime_sub_233 : Nat.Prime (54244 - 233) := by
  show Nat.Prime 54011
  exact pB (by decide +kernel)

theorem check_233 : allC 54244 233 P10k ds_233 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 54244 is 233. -/
theorem minGB_233 : minGB 54244 = 233 :=
  minGB_eq_of P10k P10k_complete 54244 233 (by norm_num) (by norm_num) prime_sub_233 ds_233 check_233

def ds_293 : List ℕ := [
    2, 13, 151, 3, 41, 3, 17, 3, 19, 5, 3, 3,
    37, 3, 23, 191, 5, 3, 3, 7, 3, 3, 29, 5,
    3, 11, 3, 13, 3, 7, 3, 233, 19, 3, 5, 3,
    3, 3, 11, 89, 5, 3, 199, 3, 7, 3, 3, 3,
    67, 3, 11, 5, 3, 19, 29, 13, 5, 3, 3, 7,
    3]

theorem prime_sub_293 : Nat.Prime (63274 - 293) := by
  show Nat.Prime 62981
  exact pB (by decide +kernel)

theorem check_293 : allC 63274 293 P10k ds_293 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 63274 is 293. -/
theorem minGB_293 : minGB 63274 = 293 :=
  minGB_eq_of P10k P10k_complete 63274 293 (by norm_num) (by norm_num) prime_sub_293 ds_293 check_293

def ds_313 : List ℕ := [
    2, 197, 3, 5, 3, 7, 3, 89, 3, 3, 11, 5,
    3, 199, 3, 3, 3, 17, 5, 3, 47, 29, 3, 3,
    5, 3, 337, 3, 19, 3, 5, 3, 3, 7, 3, 61,
    5, 11, 3, 3, 3, 7, 3, 37, 3, 53, 83, 7,
    3, 11, 3, 3, 67, 3, 3, 3, 3, 151, 5, 3,
    149, 3, 5, 3]

theorem prime_sub_313 : Nat.Prime (113672 - 313) := by
  show Nat.Prime 113359
  exact pB (by decide +kernel)

theorem check_313 : allC 113672 313 P10k ds_313 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 113672 is 313. -/
theorem minGB_313 : minGB 113672 = 313 :=
  minGB_eq_of P10k P10k_complete 113672 313 (by norm_num) (by norm_num) prime_sub_313 ds_313 check_313

def ds_331 : List ℕ := [
    2, 5, 3, 11, 3, 5, 3, 7, 3, 3, 97, 37,
    3, 5, 3, 3, 3, 7, 53, 3, 5, 13, 3, 3,
    89, 3, 5, 3, 79, 3, 19, 3, 3, 11, 3, 313,
    13, 5, 3, 3, 3, 131, 3, 5, 3, 73, 199, 5,
    3, 7, 3, 3, 19, 3, 3, 3, 3, 7, 17, 3,
    5, 3, 29, 3, 5, 3]

theorem prime_sub_331 : Nat.Prime (128168 - 331) := by
  show Nat.Prime 127837
  exact pB (by decide +kernel)

theorem check_331 : allC 128168 331 P10k ds_331 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 128168 is 331. -/
theorem minGB_331 : minGB 128168 = 331 :=
  minGB_eq_of P10k P10k_complete 128168 331 (by norm_num) (by norm_num) prime_sub_331 ds_331 check_331

def ds_359 : List ℕ := [
    2, 5, 199, 3, 433, 3, 7, 3, 5, 73, 3, 3,
    29, 3, 11, 5, 7, 3, 3, 263, 3, 3, 5, 31,
    3, 7, 3, 317, 3, 5, 3, 331, 97, 3, 173, 3,
    3, 3, 79, 5, 11, 3, 19, 3, 43, 3, 3, 3,
    7, 3, 5, 23, 3, 277, 281, 5, 7, 3, 3, 149,
    3, 5, 3, 7, 3, 389, 3, 3, 421, 3, 5]

theorem prime_sub_359 : Nat.Prime (194428 - 359) := by
  show Nat.Prime 194069
  exact pB (by decide +kernel)

theorem check_359 : allC 194428 359 P10k ds_359 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 194428 is 359. -/
theorem minGB_359 : minGB 194428 = 359 :=
  minGB_eq_of P10k P10k_complete 194428 359 (by norm_num) (by norm_num) prime_sub_359 ds_359 check_359

def ds_383 : List ℕ := [
    2, 7, 5, 3, 163, 3, 7, 3, 11, 13, 3, 3,
    17, 3, 199, 433, 7, 3, 3, 73, 3, 3, 29, 11,
    3, 7, 3, 13, 3, 263, 3, 31, 373, 3, 317, 3,
    3, 3, 83, 331, 97, 3, 173, 3, 131, 3, 3, 3,
    7, 3, 19, 43, 3, 359, 29, 13, 7, 3, 3, 23,
    3, 277, 3, 7, 3, 31, 3, 3, 17, 3, 7, 389,
    3, 3, 3]

theorem prime_sub_383 : Nat.Prime (194470 - 383) := by
  show Nat.Prime 194087
  exact pB (by decide +kernel)

theorem check_383 : allC 194470 383 P10k ds_383 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 194470 is 383. -/
theorem minGB_383 : minGB 194470 = 383 :=
  minGB_eq_of P10k P10k_complete 194470 383 (by norm_num) (by norm_num) prime_sub_383 ds_383 check_383

def ds_389 : List ℕ := [
    2, 13, 7, 3, 277, 3, 5, 3, 37, 13, 3, 3,
    43, 3, 5, 61, 257, 3, 3, 11, 3, 3, 379, 7,
    3, 23, 3, 5, 3, 19, 3, 7, 5, 3, 17, 3,
    3, 3, 5, 7, 101, 3, 157, 3, 5, 3, 3, 3,
    5, 3, 103, 23, 3, 17, 5, 13, 11, 3, 3, 71,
    3, 29, 3, 31, 3, 5, 3, 3, 5, 3, 17, 193,
    3, 3, 3, 7]

theorem prime_sub_389 : Nat.Prime (413572 - 389) := by
  show Nat.Prime 413183
  exact pB (by decide +kernel)

theorem check_389 : allC 413572 389 P10k ds_389 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 413572 is 389. -/
theorem minGB_389 : minGB 413572 = 389 :=
  minGB_eq_of P10k P10k_complete 413572 389 (by norm_num) (by norm_num) prime_sub_389 ds_389 check_389

def ds_523 : List ℕ := [
    2, 419, 3, 5, 3, 7, 3, 607, 3, 3, 13, 5,
    3, 29, 3, 3, 3, 31, 5, 3, 17, 43, 3, 3,
    5, 3, 263, 3, 13, 3, 5, 3, 3, 7, 3, 487,
    5, 587, 3, 3, 3, 7, 3, 41, 3, 53, 677, 7,
    3, 79, 3, 3, 151, 3, 3, 3, 3, 461, 5, 3,
    89, 3, 5, 3, 11, 3, 283, 5, 3, 7, 3, 3,
    5, 23, 11, 3, 3, 5, 3, 211, 3, 13, 3, 7,
    41, 3, 3, 5, 3, 19, 3, 3, 5, 3, 13, 3,
    3, 3]

theorem prime_sub_523 : Nat.Prime (503222 - 523) := by
  show Nat.Prime 502699
  exact pB (by decide +kernel)

theorem check_523 : allC 503222 523 P10k ds_523 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 503222 is 523. -/
theorem minGB_523 : minGB 503222 = 523 :=
  minGB_eq_of P10k P10k_complete 503222 523 (by norm_num) (by norm_num) prime_sub_523 ds_523 check_523

def ds_601 : List ℕ := [
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

theorem prime_sub_601 : Nat.Prime (1077422 - 601) := by
  show Nat.Prime 1076821
  exact pB (by decide +kernel)

theorem check_601 : allC 1077422 601 P10k ds_601 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 1077422 is 601. -/
theorem minGB_601 : minGB 1077422 = 601 :=
  minGB_eq_of P10k P10k_complete 1077422 601 (by norm_num) (by norm_num) prime_sub_601 ds_601 check_601

def ds_727 : List ℕ := [
    2, 5, 3, 19, 3, 5, 3, 13, 3, 3, 47, 233,
    3, 5, 3, 3, 3, 11, 197, 3, 5, 1399, 3, 3,
    13, 3, 5, 3, 73, 3, 7, 3, 3, 101, 3, 409,
    251, 5, 3, 3, 3, 29, 3, 5, 3, 1019, 7, 5,
    3, 37, 3, 3, 421, 3, 3, 3, 3, 1237, 149, 3,
    5, 3, 131, 3, 5, 3, 13, 7, 3, 19, 3, 3,
    31, 5, 7, 3, 3, 347, 3, 13, 3, 7, 3, 5,
    1693, 3, 3, 11, 3, 5, 3, 3, 13, 3, 1259, 3,
    3, 3, 5, 877, 7, 3, 3, 3, 43, 19, 3, 3,
    3, 71, 1361, 5, 3, 1447, 7, 3, 5, 3, 3, 3,
    257, 5, 3, 3, 19, 3, 53, 3]

theorem prime_sub_727 : Nat.Prime (3526958 - 727) := by
  show Nat.Prime 3526231
  exact pB (by decide +kernel)

theorem check_727 : allC 3526958 727 P10k ds_727 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 3526958 is 727. -/
theorem minGB_727 : minGB 3526958 = 727 :=
  minGB_eq_of P10k P10k_complete 3526958 727 (by norm_num) (by norm_num) prime_sub_727 ds_727 check_727

end LeanLab.Verifications.Top50.Records1
