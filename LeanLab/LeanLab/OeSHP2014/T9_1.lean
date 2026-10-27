/-
P0005 Oliveira e Silva, Herzog, Pardi 2014, Table 9, page 2051, record-breaking first
occurrences P(g) of a prime gap g, part 1: each row IsGapAt P(g) g, that is P(g) and
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


def gds_1 : List ℕ := [
    ]

/-- Table 9 row: the prime after 2 is 2 + 1. -/
theorem gap9_1 : IsGapAt 2 1 :=
  isGapAt_of 2 1 (pB (by decide +kernel)) (by show Nat.Prime 3; exact pB (by decide +kernel)) gds_1 (by decide +kernel)

def gds_2 : List ℕ := [
    2]

/-- Table 9 row: the prime after 3 is 3 + 2. -/
theorem gap9_2 : IsGapAt 3 2 :=
  isGapAt_of 3 2 (pB (by decide +kernel)) (by show Nat.Prime 5; exact pB (by decide +kernel)) gds_2 (by decide +kernel)

def gds_4 : List ℕ := [
    2, 3, 2]

/-- Table 9 row: the prime after 7 is 7 + 4. -/
theorem gap9_4 : IsGapAt 7 4 :=
  isGapAt_of 7 4 (pB (by decide +kernel)) (by show Nat.Prime 11; exact pB (by decide +kernel)) gds_4 (by decide +kernel)

def gds_6 : List ℕ := [
    2, 5, 2, 3, 2]

/-- Table 9 row: the prime after 23 is 23 + 6. -/
theorem gap9_6 : IsGapAt 23 6 :=
  isGapAt_of 23 6 (pB (by decide +kernel)) (by show Nat.Prime 29; exact pB (by decide +kernel)) gds_6 (by decide +kernel)

def gds_8 : List ℕ := [
    2, 7, 2, 3, 2, 5, 2]

/-- Table 9 row: the prime after 89 is 89 + 8. -/
theorem gap9_8 : IsGapAt 89 8 :=
  isGapAt_of 89 8 (pB (by decide +kernel)) (by show Nat.Prime 97; exact pB (by decide +kernel)) gds_8 (by decide +kernel)

def gds_10 : List ℕ := [
    2, 3, 2, 11, 2, 5, 2, 3, 2]

/-- Table 9 row: the prime after 139 is 139 + 10. -/
theorem gap9_10 : IsGapAt 139 10 :=
  isGapAt_of 139 10 (pB (by decide +kernel)) (by show Nat.Prime 149; exact pB (by decide +kernel)) gds_10 (by decide +kernel)

def gds_12 : List ℕ := [
    2, 3, 2, 7, 2, 5, 2, 3, 2, 11, 2]

/-- Table 9 row: the prime after 199 is 199 + 12. -/
theorem gap9_12 : IsGapAt 199 12 :=
  isGapAt_of 199 12 (pB (by decide +kernel)) (by show Nat.Prime 211; exact pB (by decide +kernel)) gds_12 (by decide +kernel)

def gds_16 : List ℕ := [
    2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 19, 2, 3, 2]

/-- Table 9 row: the prime after 1831 is 1831 + 16. -/
theorem gap9_16 : IsGapAt 1831 16 :=
  isGapAt_of 1831 16 (pB (by decide +kernel)) (by show Nat.Prime 1847; exact pB (by decide +kernel)) gds_16 (by decide +kernel)

def gds_26 : List ℕ := [
    2, 37, 2, 3, 2, 13, 2, 5, 2, 3, 2, 19, 2, 47, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 41, 2]

/-- Table 9 row: the prime after 2477 is 2477 + 26. -/
theorem gap9_26 : IsGapAt 2477 26 :=
  isGapAt_of 2477 26 (pB (by decide +kernel)) (by show Nat.Prime 2503; exact pB (by decide +kernel)) gds_26 (by decide +kernel)

def gds_28 : List ℕ := [
    2, 3, 2, 5, 2, 13, 2, 3, 2, 11, 2, 19, 2, 3, 2, 29,
    2, 7, 2, 3, 2, 41, 2, 5, 2, 3, 2]

/-- Table 9 row: the prime after 2971 is 2971 + 28. -/
theorem gap9_28 : IsGapAt 2971 28 :=
  isGapAt_of 2971 28 (pB (by decide +kernel)) (by show Nat.Prime 2999; exact pB (by decide +kernel)) gds_28 (by decide +kernel)

def gds_30 : List ℕ := [
    2, 3, 2, 11, 2, 13, 2, 3, 2, 59, 2, 31, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 7, 2, 29, 2, 3, 2, 5, 2]

/-- Table 9 row: the prime after 4297 is 4297 + 30. -/
theorem gap9_30 : IsGapAt 4297 30 :=
  isGapAt_of 4297 30 (pB (by decide +kernel)) (by show Nat.Prime 4327; exact pB (by decide +kernel)) gds_30 (by decide +kernel)

def gds_32 : List ℕ := [
    2, 7, 2, 3, 2, 29, 2, 11, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 71, 2, 31, 2, 3, 2, 5, 2, 41, 2, 3, 2, 7, 2]

/-- Table 9 row: the prime after 5591 is 5591 + 32. -/
theorem gap9_32 : IsGapAt 5591 32 :=
  isGapAt_of 5591 32 (pB (by decide +kernel)) (by show Nat.Prime 5623; exact pB (by decide +kernel)) gds_32 (by decide +kernel)

def gds_36 : List ℕ := [
    2, 41, 2, 3, 2, 19, 2, 11, 2, 3, 2, 73, 2, 5, 2, 3,
    2, 7, 2, 17, 2, 3, 2, 5, 2, 61, 2, 3, 2, 11, 2, 7,
    2, 3, 2]

/-- Table 9 row: the prime after 9551 is 9551 + 36. -/
theorem gap9_36 : IsGapAt 9551 36 :=
  isGapAt_of 9551 36 (pB (by decide +kernel)) (by show Nat.Prime 9587; exact pB (by decide +kernel)) gds_36 (by decide +kernel)

def gds_38 : List ℕ := [
    2, 5, 2, 3, 2, 37, 2, 71, 2, 3, 2, 5, 2, 127, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 17, 2, 67, 2, 3, 2, 113, 2, 5,
    2, 3, 2, 109, 2]

/-- Table 9 row: the prime after 30593 is 30593 + 38. -/
theorem gap9_38 : IsGapAt 30593 38 :=
  isGapAt_of 30593 38 (pB (by decide +kernel)) (by show Nat.Prime 30631; exact pB (by decide +kernel)) gds_38 (by decide +kernel)

def gds_46 : List ℕ := [
    2, 3, 2, 41, 2, 257, 2, 3, 2, 7, 2, 5, 2, 3, 2, 59,
    2, 17, 2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 227, 2, 3,
    2, 13, 2, 11, 2, 3, 2, 149, 2, 5, 2, 3, 2]

/-- Table 9 row: the prime after 81463 is 81463 + 46. -/
theorem gap9_46 : IsGapAt 81463 46 :=
  isGapAt_of 81463 46 (pB (by decide +kernel)) (by show Nat.Prime 81509; exact pB (by decide +kernel)) gds_46 (by decide +kernel)

def gds_56 : List ℕ := [
    2, 5, 2, 3, 2, 211, 2, 79, 2, 3, 2, 5, 2, 23, 2, 3,
    2, 103, 2, 11, 2, 3, 2, 53, 2, 19, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 47, 2, 157, 2, 3, 2, 5, 2, 7, 2, 3, 2, 13,
    2, 41, 2, 3, 2, 17, 2]

/-- Table 9 row: the prime after 82073 is 82073 + 56. -/
theorem gap9_56 : IsGapAt 82073 56 :=
  isGapAt_of 82073 56 (pB (by decide +kernel)) (by show Nat.Prime 82129; exact pB (by decide +kernel)) gds_56 (by decide +kernel)

def gds_64 : List ℕ := [
    2, 3, 2, 257, 2, 5, 2, 3, 2, 19, 2, 271, 2, 3, 2, 5,
    2, 109, 2, 3, 2, 283, 2, 13, 2, 3, 2, 73, 2, 7, 2, 3,
    2, 23, 2, 5, 2, 3, 2, 53, 2, 61, 2, 3, 2, 5, 2, 19,
    2, 3, 2, 43, 2, 17, 2, 3, 2, 7, 2, 11, 2, 3, 2]

/-- Table 9 row: the prime after 89689 is 89689 + 64. -/
theorem gap9_64 : IsGapAt 89689 64 :=
  isGapAt_of 89689 64 (pB (by decide +kernel)) (by show Nat.Prime 89753; exact pB (by decide +kernel)) gds_64 (by decide +kernel)

def gds_66 : List ℕ := [
    2, 5, 2, 3, 2, 13, 2, 11, 2, 3, 2, 5, 2, 167, 2, 3,
    2, 31, 2, 17, 2, 3, 2, 257, 2, 7, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 127, 2, 157, 2, 3, 2, 5, 2, 79, 2, 3, 2, 59,
    2, 241, 2, 3, 2, 7, 2, 61, 2, 3, 2, 19, 2, 5, 2, 3,
    2]

/-- Table 9 row: the prime after 162143 is 162143 + 66. -/
theorem gap9_66 : IsGapAt 162143 66 :=
  isGapAt_of 162143 66 (pB (by decide +kernel)) (by show Nat.Prime 162209; exact pB (by decide +kernel)) gds_66 (by decide +kernel)

def gds_70 : List ℕ := [
    2, 3, 2, 53, 2, 5, 2, 3, 2, 7, 2, 11, 2, 3, 2, 5,
    2, 281, 2, 3, 2, 13, 2, 7, 2, 3, 2, 83, 2, 41, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 317, 2, 59, 2, 3, 2, 5, 2, 13,
    2, 3, 2, 7, 2, 19, 2, 3, 2, 17, 2, 37, 2, 3, 2, 61,
    2, 5, 2, 3, 2]

/-- Table 9 row: the prime after 173359 is 173359 + 70. -/
theorem gap9_70 : IsGapAt 173359 70 :=
  isGapAt_of 173359 70 (pB (by decide +kernel)) (by show Nat.Prime 173429; exact pB (by decide +kernel)) gds_70 (by decide +kernel)

def gds_74 : List ℕ := [
    2, 13, 2, 3, 2, 271, 2, 5, 2, 3, 2, 401, 2, 311, 2, 3,
    2, 5, 2, 17, 2, 3, 2, 7, 2, 47, 2, 3, 2, 239, 2, 41,
    2, 3, 2, 293, 2, 5, 2, 3, 2, 23, 2, 167, 2, 3, 2, 5,
    2, 173, 2, 3, 2, 13, 2, 113, 2, 3, 2, 11, 2, 131, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 37, 2]

/-- Table 9 row: the prime after 404597 is 404597 + 74. -/
theorem gap9_74 : IsGapAt 404597 74 :=
  isGapAt_of 404597 74 (pB (by decide +kernel)) (by show Nat.Prime 404671; exact pB (by decide +kernel)) gds_74 (by decide +kernel)

def gds_80 : List ℕ := [
    2, 5, 2, 3, 2, 73, 2, 281, 2, 3, 2, 5, 2, 43, 2, 3,
    2, 19, 2, 17, 2, 3, 2, 163, 2, 431, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 23, 2, 11, 2, 3, 2, 5, 2, 7, 2, 3, 2, 79,
    2, 71, 2, 3, 2, 17, 2, 13, 2, 3, 2, 11, 2, 5, 2, 3,
    2, 421, 2, 127, 2, 3, 2, 5, 2, 29, 2, 3, 2, 661, 2]

/-- Table 9 row: the prime after 542603 is 542603 + 80. -/
theorem gap9_80 : IsGapAt 542603 80 :=
  isGapAt_of 542603 80 (pB (by decide +kernel)) (by show Nat.Prime 542683; exact pB (by decide +kernel)) gds_80 (by decide +kernel)

def gds_88 : List ℕ := [
    2, 3, 2, 719, 2, 5, 2, 3, 2, 17, 2, 11, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 29, 2, 61, 2, 3, 2, 37, 2, 107, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 157, 2, 113, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 19, 2, 229, 2, 3, 2, 43, 2, 179, 2, 3, 2, 223,
    2, 5, 2, 3, 2, 13, 2, 683, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 73, 2, 53, 2, 3, 2]

/-- Table 9 row: the prime after 544279 is 544279 + 88. -/
theorem gap9_88 : IsGapAt 544279 88 :=
  isGapAt_of 544279 88 (pB (by decide +kernel)) (by show Nat.Prime 544367; exact pB (by decide +kernel)) gds_88 (by decide +kernel)

end LeanLab.OeSHP2014
