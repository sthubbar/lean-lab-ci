/-
P0041 Sinisalo 1993, Table 2, rows 18 to 34: for each listed prime p and its
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

theorem p14341367 : Nat.Prime 14341367 := by
  refine Pratt.pratt 14341367 15 [(2, 1), (13, 1), (59, 1), (9349, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p16253291 : Nat.Prime 16253291 := by
  refine Pratt.pratt 16253291 2 [(2, 1), (5, 1), (1625329, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
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
theorem p20756699 : Nat.Prime 20756699 := by
  refine Pratt.pratt 20756699 2 [(2, 1), (1291, 1), (8039, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p32506583 : Nat.Prime 32506583 := by
  refine Pratt.pratt 32506583 5 [(2, 1), (16253291, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p16253291

def ds_197 : List ℕ := [
    2, 5, 7, 3, 241, 3, 11, 3, 5, 131, 3, 3,
    37, 3, 7, 5, 19, 3, 3, 197, 3, 3, 5, 7,
    3, 107, 3, 139, 3, 5, 3, 7, 17, 3, 11, 3,
    3, 3, 167, 5, 109, 3, 313, 3]

theorem prime_sub_197 : Nat.Prime (112558 - 197) := by
  show Nat.Prime 112361
  exact pB (by decide +kernel)

theorem check_197 : allC 112558 197 P10k ds_197 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 112558 is 197. -/
theorem minGB_S_197 : minGB 112558 = 197 :=
  minGB_eq_of P10k P10k_complete 112558 197 (by norm_num) (by norm_num) prime_sub_197 ds_197 check_197

def ds_223 : List ℕ := [
    2, 19, 3, 5, 3, 31, 3, 13, 3, 3, 53, 5,
    3, 59, 3, 3, 3, 11, 5, 3, 127, 19, 3, 3,
    5, 3, 97, 3, 17, 3, 5, 3, 3, 137, 3, 257,
    5, 227, 3, 3, 3, 211, 3, 11, 3, 23, 17]

theorem prime_sub_223 : Nat.Prime (221942 - 223) := by
  show Nat.Prime 221719
  exact pB (by decide +kernel)

theorem check_223 : allC 221942 223 P10k ds_223 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 221942 is 223. -/
theorem minGB_S_223 : minGB 221942 = 223 :=
  minGB_eq_of P10k P10k_complete 221942 223 (by norm_num) (by norm_num) prime_sub_223 ds_223 check_223

def ds_257 : List ℕ := [
    2, 17, 29, 3, 179, 3, 269, 3, 23, 5, 3, 3,
    7, 3, 13, 31, 5, 3, 3, 17, 3, 3, 7, 5,
    3, 19, 3, 283, 3, 41, 3, 11, 199, 3, 5, 3,
    3, 3, 7, 17, 5, 3, 71, 3, 11, 3, 3, 3,
    43, 3, 307, 5, 3, 7]

theorem prime_sub_257 : Nat.Prime (237544 - 257) := by
  show Nat.Prime 237287
  exact pB (by decide +kernel)

theorem check_257 : allC 237544 257 P10k ds_257 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 237544 is 257. -/
theorem minGB_S_257 : minGB 237544 = 257 :=
  minGB_eq_of P10k P10k_complete 237544 257 (by norm_num) (by norm_num) prime_sub_257 ds_257 check_257

def ds_263 : List ℕ := [
    2, 23, 53, 3, 5, 3, 11, 3, 7, 79, 3, 3,
    5, 3, 19, 373, 127, 3, 3, 5, 3, 3, 11, 641,
    3, 5, 3, 7, 3, 467, 3, 5, 547, 3, 7, 3,
    3, 3, 109, 41, 13, 3, 5, 3, 17, 3, 3, 3,
    227, 3, 7, 47, 3, 5, 13]

theorem prime_sub_263 : Nat.Prime (485326 - 263) := by
  show Nat.Prime 485063
  exact pB (by decide +kernel)

theorem check_263 : allC 485326 263 P10k ds_263 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 485326 is 263. -/
theorem minGB_S_263 : minGB 485326 = 263 :=
  minGB_eq_of P10k P10k_complete 485326 263 (by norm_num) (by norm_num) prime_sub_263 ds_263 check_263

def ds_281 : List ℕ := [
    2, 5, 487, 3, 41, 3, 7, 3, 5, 67, 3, 3,
    13, 3, 17, 5, 7, 3, 3, 157, 3, 3, 5, 61,
    3, 7, 3, 359, 3, 5, 3, 31, 557, 3, 17, 3,
    3, 3, 11, 5, 113, 3, 541, 3, 13, 3, 3, 3,
    7, 3, 5, 43, 3, 17, 41, 5, 7, 3, 3]

theorem prime_sub_281 : Nat.Prime (642358 - 281) := by
  show Nat.Prime 642077
  exact pB (by decide +kernel)

theorem check_281 : allC 642358 281 P10k ds_281 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 642358 is 281. -/
theorem minGB_S_281 : minGB 642358 = 281 :=
  minGB_eq_of P10k P10k_complete 642358 281 (by norm_num) (by norm_num) prime_sub_281 ds_281 check_281

def ds_317 : List ℕ := [
    2, 5, 29, 3, 41, 3, 13, 3, 5, 7, 3, 3,
    151, 3, 109, 5, 17, 3, 3, 7, 3, 3, 5, 67,
    3, 167, 3, 739, 3, 5, 3, 137, 193, 3, 19, 3,
    3, 3, 619, 5, 29, 3, 257, 3, 7, 3, 3, 3,
    11, 3, 5, 7, 3, 13, 41, 5, 379, 3, 3, 7,
    3, 5, 3, 83, 3]

theorem prime_sub_317 : Nat.Prime (686638 - 317) := by
  show Nat.Prime 686321
  exact pB (by decide +kernel)

theorem check_317 : allC 686638 317 P10k ds_317 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 686638 is 317. -/
theorem minGB_S_317 : minGB 686638 = 317 :=
  minGB_eq_of P10k P10k_complete 686638 317 (by norm_num) (by norm_num) prime_sub_317 ds_317 check_317

def ds_347 : List ℕ := [
    2, 5, 107, 3, 13, 3, 23, 3, 5, 17, 3, 3,
    47, 3, 37, 5, 11, 3, 3, 193, 3, 3, 5, 13,
    3, 313, 3, 7, 3, 5, 3, 17, 19, 3, 7, 3,
    3, 3, 13, 5, 83, 3, 7, 3, 59, 3, 3, 3,
    41, 3, 5, 569, 3, 19, 11, 5, 37, 3, 3, 277,
    3, 5, 3, 29, 3, 7, 3, 3]

theorem prime_sub_347 : Nat.Prime (1042078 - 347) := by
  show Nat.Prime 1041731
  exact pB (by decide +kernel)

theorem check_347 : allC 1042078 347 P10k ds_347 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 1042078 is 347. -/
theorem minGB_S_347 : minGB 1042078 = 347 :=
  minGB_eq_of P10k P10k_complete 1042078 347 (by norm_num) (by norm_num) prime_sub_347 ds_347 check_347

def ds_379 : List ℕ := [
    2, 5, 3, 43, 3, 5, 3, 7, 3, 3, 41, 17,
    3, 5, 3, 3, 3, 7, 19, 3, 5, 23, 3, 3,
    13, 3, 5, 3, 11, 3, 47, 3, 3, 17, 3, 173,
    31, 5, 3, 3, 3, 19, 3, 5, 3, 983, 71, 5,
    3, 7, 3, 3, 11, 3, 3, 3, 3, 7, 37, 3,
    5, 3, 11, 3, 5, 3, 13, 131, 3, 439, 3, 3,
    601, 5]

theorem prime_sub_379 : Nat.Prime (1172918 - 379) := by
  show Nat.Prime 1172539
  exact pB (by decide +kernel)

theorem check_379 : allC 1172918 379 P10k ds_379 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 1172918 is 379. -/
theorem minGB_S_379 : minGB 1172918 = 379 :=
  minGB_eq_of P10k P10k_complete 1172918 379 (by norm_num) (by norm_num) prime_sub_379 ds_379 check_379

def ds_401 : List ℕ := [
    2, 353, 29, 3, 11, 3, 5, 3, 19, 131, 3, 3,
    7, 3, 5, 41, 17, 3, 3, 293, 3, 3, 7, 233,
    3, 349, 3, 5, 3, 67, 3, 127, 5, 3, 37, 3,
    3, 3, 5, 853, 29, 3, 709, 3, 5, 3, 3, 3,
    5, 3, 13, 47, 3, 7, 5, 17, 31, 3, 3, 61,
    3, 7, 3, 13, 3, 5, 3, 3, 5, 3, 29, 23,
    3, 3, 3, 479, 13, 3]

theorem prime_sub_401 : Nat.Prime (2041402 - 401) := by
  show Nat.Prime 2041001
  exact pB (by decide +kernel)

theorem check_401 : allC 2041402 401 P10k ds_401 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 2041402 is 401. -/
theorem minGB_S_401 : minGB 2041402 = 401 :=
  minGB_eq_of P10k P10k_complete 2041402 401 (by norm_num) (by norm_num) prime_sub_401 ds_401 check_401

def ds_419 : List ℕ := [
    2, 5, 13, 3, 11, 3, 887, 3, 5, 79, 3, 3,
    19, 3, 17, 5, 61, 3, 3, 359, 3, 3, 5, 53,
    3, 317, 3, 7, 3, 5, 3, 419, 1153, 3, 7, 3,
    3, 3, 1193, 5, 127, 3, 7, 3, 31, 3, 3, 3,
    37, 3, 5, 13, 3, 17, 23, 5, 19, 3, 3, 41,
    3, 5, 3, 941, 3, 7, 3, 3, 29, 3, 5, 7,
    3, 3, 3, 5, 859, 3, 7, 3]

theorem prime_sub_419 : Nat.Prime (2406448 - 419) := by
  show Nat.Prime 2406029
  exact pB (by decide +kernel)

theorem check_419 : allC 2406448 419 P10k ds_419 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 2406448 is 419. -/
theorem minGB_S_419 : minGB 2406448 = 419 :=
  minGB_eq_of P10k P10k_complete 2406448 419 (by norm_num) (by norm_num) prime_sub_419 ds_419 check_419

def ds_463 : List ℕ := [
    2, 7, 3, 139, 3, 101, 3, 5, 3, 3, 7, 11,
    3, 13, 3, 3, 3, 223, 541, 3, 7, 5, 3, 3,
    41, 3, 11, 3, 5, 3, 31, 3, 3, 5, 3, 2003,
    7, 37, 3, 3, 3, 167, 3, 373, 3, 5, 787, 521,
    3, 5, 3, 3, 7, 3, 3, 3, 3, 179, 13, 3,
    7, 3, 17, 3, 31, 3, 19, 113, 3, 5, 3, 3,
    7, 29, 5, 3, 3, 53, 3, 5, 3, 211, 3, 11,
    5, 3, 3, 61, 3]

theorem prime_sub_463 : Nat.Prime (4288574 - 463) := by
  show Nat.Prime 4288111
  exact pB (by decide +kernel)

theorem check_463 : allC 4288574 463 P10k ds_463 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 4288574 is 463. -/
theorem minGB_S_463 : minGB 4288574 = 463 :=
  minGB_eq_of P10k P10k_complete 4288574 463 (by norm_num) (by norm_num) prime_sub_463 ds_463 check_463

def ds_487 : List ℕ := [
    2, 5, 3, 19, 3, 5, 3, 7, 3, 3, 13, 719,
    3, 5, 3, 3, 3, 7, 223, 3, 5, 11, 3, 3,
    421, 3, 5, 3, 13, 3, 17, 3, 3, 307, 3, 773,
    167, 5, 3, 3, 3, 487, 3, 5, 3, 37, 11, 5,
    3, 7, 3, 3, 2137, 3, 3, 3, 3, 7, 11, 3,
    5, 3, 103, 3, 5, 3, 17, 727, 3, 19, 3, 3,
    1693, 5, 967, 3, 3, 7, 3, 11, 3, 13, 3, 5,
    7, 3, 3, 859, 3, 5, 3, 3]

theorem prime_sub_487 : Nat.Prime (4938848 - 487) := by
  show Nat.Prime 4938361
  exact pB (by decide +kernel)

theorem check_487 : allC 4938848 487 P10k ds_487 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 4938848 is 487. -/
theorem minGB_S_487 : minGB 4938848 = 487 :=
  minGB_eq_of P10k P10k_complete 4938848 487 (by norm_num) (by norm_num) prime_sub_487 ds_487 check_487

def ds_509 : List ℕ := [
    2, 13, 11, 3, 5, 3, 1723, 3, 229, 13, 3, 3,
    5, 3, 787, 113, 73, 3, 3, 5, 3, 3, 7, 269,
    3, 5, 3, 13, 3, 389, 3, 5, 11, 3, 19, 3,
    3, 3, 7, 71, 23, 3, 5, 3, 191, 3, 3, 3,
    431, 3, 109, 2003, 3, 5, 101, 13, 11, 3, 3, 5,
    3, 7, 3, 5, 3, 23, 3, 3, 17, 3, 29, 1627,
    3, 3, 3, 37, 83, 3, 5, 3, 7, 3, 5, 3,
    3, 167, 17, 3, 5, 3, 11, 661, 3, 5, 3, 7]

theorem prime_sub_509 : Nat.Prime (9292156 - 509) := by
  show Nat.Prime 9291647
  exact pB (by decide +kernel)

theorem check_509 : allC 9292156 509 P10k ds_509 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 9292156 is 509. -/
theorem minGB_S_509 : minGB 9292156 = 509 :=
  minGB_eq_of P10k P10k_complete 9292156 509 (by norm_num) (by norm_num) prime_sub_509 ds_509 check_509

def ds_521 : List ℕ := [
    2, 5, 2593, 3, 11, 3, 31, 3, 5, 7, 3, 3,
    13, 3, 41, 5, 17, 3, 3, 7, 3, 3, 5, 73,
    3, 71, 3, 941, 3, 5, 3, 1637, 19, 3, 79, 3,
    3, 3, 47, 5, 337, 3, 101, 3, 7, 3, 3, 3,
    43, 3, 5, 7, 3, 19, 29, 5, 491, 3, 3, 7,
    3, 5, 3, 967, 3, 137, 3, 3, 1823, 3, 5, 727,
    3, 3, 3, 5, 31, 3, 83, 3, 773, 3, 13, 3,
    3, 5, 7, 3, 1279, 3, 17, 19, 3, 7, 3, 5,
    13]

theorem prime_sub_521 : Nat.Prime (14341888 - 521) := by
  show Nat.Prime 14341367
  exact p14341367

theorem check_521 : allC 14341888 521 P10k ds_521 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 14341888 is 521. -/
theorem minGB_S_521 : minGB 14341888 = 521 :=
  minGB_eq_of P10k P10k_complete 14341888 521 (by norm_num) (by norm_num) prime_sub_521 ds_521 check_521

def ds_569 : List ℕ := [
    2, 5, 7, 3, 17, 3, 2833, 3, 5, 19, 3, 3,
    569, 3, 7, 5, 523, 3, 3, 11, 3, 3, 5, 7,
    3, 37, 3, 103, 3, 5, 3, 7, 11, 3, 2297, 3,
    3, 3, 29, 5, 467, 3, 109, 3, 59, 3, 3, 3,
    251, 3, 5, 647, 3, 23, 7, 5, 11, 3, 3, 41,
    3, 5, 3, 73, 3, 17, 3, 3, 743, 3, 5, 151,
    3, 3, 3, 5, 23, 3, 11, 3, 17, 3, 1699, 3,
    3, 5, 2153, 3, 3919, 3, 7, 3821, 3, 3769, 3, 5,
    7, 17, 3, 3, 3, 1511, 5]

theorem prime_sub_569 : Nat.Prime (17726098 - 569) := by
  show Nat.Prime 17725529
  exact p17725529

theorem check_569 : allC 17726098 569 P10k ds_569 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 17726098 is 569. -/
theorem minGB_S_569 : minGB 17726098 = 569 :=
  minGB_eq_of P10k P10k_complete 17726098 569 (by norm_num) (by norm_num) prime_sub_569 ds_569 check_569

def ds_593 : List ℕ := [
    2, 7, 139, 3, 103, 3, 5, 3, 13, 61, 3, 3,
    107, 3, 5, 1657, 7, 3, 3, 17, 3, 3, 11, 59,
    3, 7, 3, 5, 3, 1493, 3, 521, 5, 3, 11, 3,
    3, 3, 5, 17, 13, 3, 19, 3, 5, 3, 3, 3,
    5, 3, 173, 683, 3, 149, 5, 41, 7, 3, 3, 11,
    3, 293, 3, 7, 3, 5, 3, 3, 5, 3, 7, 97,
    3, 3, 3, 163, 499, 3, 1279, 3, 19, 3, 3257, 3,
    3, 59, 317, 3, 43, 3, 5, 7, 3, 13, 3, 229,
    41, 7, 3, 3, 3, 5, 7, 13, 3, 3, 5]

theorem prime_sub_593 : Nat.Prime (20757292 - 593) := by
  show Nat.Prime 20756699
  exact p20756699

theorem check_593 : allC 20757292 593 P10k ds_593 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 20757292 is 593. -/
theorem minGB_S_593 : minGB 20757292 = 593 :=
  minGB_eq_of P10k P10k_complete 20757292 593 (by norm_num) (by norm_num) prime_sub_593 ds_593 check_593

def ds_659 : List ℕ := [
    2, 797, 7, 3, 29, 3, 5, 3, 41, 17, 3, 3,
    37, 3, 5, 11, 43, 3, 3, 59, 3, 3, 257, 7,
    3, 2557, 3, 5, 3, 151, 3, 7, 5, 3, 2731, 3,
    3, 3, 5, 7, 263, 3, 167, 3, 5, 3, 3, 3,
    5, 3, 17, 31, 3, 11, 5, 37, 41, 3, 3, 61,
    3, 137, 3, 97, 3, 5, 3, 3, 5, 3, 23, 29,
    3, 3, 3, 7, 19, 3, 79, 3, 113, 3, 2677, 3,
    3, 13, 11, 3, 277, 3, 5, 487, 3, 23, 3, 19,
    7, 13, 3, 3, 3, 5, 139, 421, 3, 3, 5, 7,
    13, 3, 3, 3, 5, 3, 3, 17, 3, 5, 5039]

theorem prime_sub_659 : Nat.Prime (32507242 - 659) := by
  show Nat.Prime 32506583
  exact p32506583

theorem check_659 : allC 32507242 659 P10k ds_659 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 32507242 is 659. -/
theorem minGB_S_659 : minGB 32507242 = 659 :=
  minGB_eq_of P10k P10k_complete 32507242 659 (by norm_num) (by norm_num) prime_sub_659 ds_659 check_659

end LeanLab.Sinisalo1993
