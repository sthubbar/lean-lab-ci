/-
P0005 Oliveira e Silva, Herzog, Pardi 2014, Table 9, page 2051, record-breaking first
occurrences P(g) of a prime gap g, part 2: each row IsGapAt P(g) g, that is P(g) and
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

theorem p10343761 : Nat.Prime 10343761 := by
  refine Pratt.pratt 10343761 11 [(2, 4), (3, 1), (5, 1), (7, 1), (47, 1), (131, 1)] (by norm_num)
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
theorem p10343903 : Nat.Prime 10343903 := by
  refine Pratt.pratt 10343903 5 [(2, 1), (5171951, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p11981443 : Nat.Prime 11981443 := by
  refine Pratt.pratt 11981443 2 [(2, 1), (3, 1), (11, 1), (181537, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p11981587 : Nat.Prime 11981587 := by
  refine Pratt.pratt 11981587 3 [(2, 1), (3, 1), (311, 1), (6421, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p13626257 : Nat.Prime 13626257 := by
  refine Pratt.pratt 13626257 3 [(2, 4), (7, 1), (89, 1), (1367, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p13626407 : Nat.Prime 13626407 := by
  refine Pratt.pratt 13626407 5 [(2, 1), (53, 1), (128551, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p14540153 : Nat.Prime 14540153 := by
  refine Pratt.pratt 14540153 3 [(2, 3), (11, 1), (165229, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p17983717 : Nat.Prime 17983717 := by
  refine Pratt.pratt 17983717 2 [(2, 2), (3, 1), (137, 1), (10939, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p17983873 : Nat.Prime 17983873 := by
  refine Pratt.pratt 17983873 5 [(2, 7), (3, 2), (67, 1), (233, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p20937821 : Nat.Prime 20937821 := by
  refine Pratt.pratt 20937821 2 [(2, 2), (5, 1), (23, 2), (1979, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p41875643 : Nat.Prime 41875643 := by
  refine Pratt.pratt 41875643 2 [(2, 1), (20937821, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p20937821
theorem p49269581 : Nat.Prime 49269581 := by
  refine Pratt.pratt 49269581 2 [(2, 2), (5, 1), (2463479, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p49269739 : Nat.Prime 49269739 := by
  refine Pratt.pratt 49269739 2 [(2, 1), (3, 1), (7, 1), (523, 1), (2243, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p49769891 : Nat.Prime 49769891 := by
  refine Pratt.pratt 49769891 10 [(2, 1), (5, 1), (1487, 1), (3347, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p68311091 : Nat.Prime 68311091 := by
  refine Pratt.pratt 68311091 2 [(2, 1), (5, 1), (43, 1), (158863, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p83751121 : Nat.Prime 83751121 := by
  refine Pratt.pratt 83751121 7 [(2, 4), (3, 2), (5, 1), (293, 1), (397, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p83751287 : Nat.Prime 83751287 := by
  refine Pratt.pratt 83751287 5 [(2, 1), (41875643, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p41875643
theorem p147684137 : Nat.Prime 147684137 := by
  refine Pratt.pratt 147684137 3 [(2, 3), (839, 1), (22003, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p147684323 : Nat.Prime 147684323 := by
  refine Pratt.pratt 147684323 2 [(2, 1), (479, 1), (154159, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p149309711 : Nat.Prime 149309711 := by
  refine Pratt.pratt 149309711 13 [(2, 1), (5, 1), (11, 1), (1357361, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p166726367 : Nat.Prime 166726367 := by
  refine Pratt.pratt 166726367 5 [(2, 1), (37, 1), (2253059, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p166726561 : Nat.Prime 166726561 := by
  refine Pratt.pratt 166726561 19 [(2, 5), (3, 1), (5, 1), (7, 1), (11, 1), (13, 1), (347, 1)] (by norm_num)
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
theorem p378043979 : Nat.Prime 378043979 := by
  refine Pratt.pratt 378043979 2 [(2, 1), (13, 1), (14540153, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p14540153
theorem p378044179 : Nat.Prime 378044179 := by
  refine Pratt.pratt 378044179 2 [(2, 1), (3, 1), (19, 1), (3316177, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p409866323 : Nat.Prime 409866323 := by
  refine Pratt.pratt 409866323 2 [(2, 1), (97, 1), (2112713, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p409866547 : Nat.Prime 409866547 := by
  refine Pratt.pratt 409866547 3 [(2, 1), (3, 1), (68311091, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p68311091
theorem p519653371 : Nat.Prime 519653371 := by
  refine Pratt.pratt 519653371 17 [(2, 1), (3, 1), (5, 1), (509, 1), (34031, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p519653597 : Nat.Prime 519653597 := by
  refine Pratt.pratt 519653597 12 [(2, 2), (7, 1), (11, 1), (1687187, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p895858039 : Nat.Prime 895858039 := by
  refine Pratt.pratt 895858039 3 [(2, 1), (3, 2), (49769891, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p49769891
theorem p895858267 : Nat.Prime 895858267 := by
  refine Pratt.pratt 895858267 2 [(2, 1), (3, 1), (149309711, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p149309711
theorem p1202442089 : Nat.Prime 1202442089 := by
  refine Pratt.pratt 1202442089 3 [(2, 3), (9743, 1), (15427, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p1202442343 : Nat.Prime 1202442343 := by
  refine Pratt.pratt 1202442343 3 [(2, 1), (3, 1), (41, 1), (4887977, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p1872851947 : Nat.Prime 1872851947 := by
  refine Pratt.pratt 1872851947 3 [(2, 1), (3, 1), (7, 1), (5279, 1), (8447, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p1872852203 : Nat.Prime 1872852203 := by
  refine Pratt.pratt 1872852203 2 [(2, 1), (13, 1), (41, 1), (53, 1), (33149, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

def gds_92 : List ℕ := [
    2, 7, 2, 3, 2, 5, 2, 17, 2, 3, 2, 619, 2, 11, 2, 3,
    2, 101, 2, 23, 2, 3, 2, 59, 2, 5, 2, 3, 2, 7, 2, 13,
    2, 3, 2, 5, 2, 509, 2, 3, 2, 17, 2, 7, 2, 3, 2, 109,
    2, 433, 2, 3, 2, 31, 2, 5, 2, 3, 2, 467, 2, 293, 2, 3,
    2, 5, 2, 199, 2, 3, 2, 7, 2, 431, 2, 3, 2, 251, 2, 11,
    2, 3, 2, 13, 2, 5, 2, 3, 2, 163, 2]

/-- Table 9 row: the prime after 927869 is 927869 + 92. -/
theorem gap9_92 : IsGapAt 927869 92 :=
  isGapAt_of 927869 92 (pB (by decide +kernel)) (by show Nat.Prime 927961; exact pB (by decide +kernel)) gds_92 (by decide +kernel)

def gds_94 : List ℕ := [
    2, 3, 2, 7, 2, 13, 2, 3, 2, 23, 2, 61, 2, 3, 2, 19,
    2, 5, 2, 3, 2, 59, 2, 11, 2, 3, 2, 5, 2, 353, 2, 3,
    2, 67, 2, 787, 2, 3, 2, 269, 2, 89, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 179, 2, 19, 2, 3, 2, 5, 2, 7, 2, 3, 2, 157,
    2, 29, 2, 3, 2, 97, 2, 809, 2, 3, 2, 359, 2, 5, 2, 3,
    2, 73, 2, 13, 2, 3, 2, 5, 2, 11, 2, 3, 2]

/-- Table 9 row: the prime after 1100977 is 1100977 + 94. -/
theorem gap9_94 : IsGapAt 1100977 94 :=
  isGapAt_of 1100977 94 (pB (by decide +kernel)) (by show Nat.Prime 1101071; exact pB (by decide +kernel)) gds_94 (by decide +kernel)

def gds_102 : List ℕ := [
    2, 3, 2, 13, 2, 5, 2, 3, 2, 67, 2, 31, 2, 3, 2, 5,
    2, 43, 2, 3, 2, 7, 2, 11, 2, 3, 2, 17, 2, 13, 2, 3,
    2, 163, 2, 5, 2, 3, 2, 139, 2, 179, 2, 3, 2, 5, 2, 47,
    2, 3, 2, 19, 2, 1181, 2, 3, 2, 233, 2, 37, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 59, 2, 89, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 13, 2, 107, 2, 3, 2, 617, 2, 11, 2, 3, 2, 29, 2, 5,
    2, 3, 2, 53, 2]

/-- Table 9 row: the prime after 1444309 is 1444309 + 102. -/
theorem gap9_102 : IsGapAt 1444309 102 :=
  isGapAt_of 1444309 102 (pB (by decide +kernel)) (by show Nat.Prime 1444411; exact pB (by decide +kernel)) gds_102 (by decide +kernel)

def gds_108 : List ℕ := [
    2, 3, 2, 19, 2, 29, 2, 3, 2, 37, 2, 5, 2, 3, 2, 677,
    2, 11, 2, 3, 2, 5, 2, 13, 2, 3, 2, 31, 2, 503, 2, 3,
    2, 97, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 113, 2, 547,
    2, 3, 2, 5, 2, 151, 2, 3, 2, 43, 2, 17, 2, 3, 2, 7,
    2, 23, 2, 3, 2, 1451, 2, 5, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 5, 2, 11, 2, 3, 2, 103, 2, 31, 2, 3, 2, 17, 2, 263,
    2, 3, 2, 619, 2, 5, 2, 3, 2, 7, 2]

/-- Table 9 row: the prime after 2238823 is 2238823 + 108. -/
theorem gap9_108 : IsGapAt 2238823 108 :=
  isGapAt_of 2238823 108 (pB (by decide +kernel)) (by show Nat.Prime 2238931; exact pB (by decide +kernel)) gds_108 (by decide +kernel)

def gds_116 : List ℕ := [
    2, 5, 2, 3, 2, 271, 2, 593, 2, 3, 2, 5, 2, 1433, 2, 3,
    2, 29, 2, 11, 2, 3, 2, 7, 2, 1997, 2, 3, 2, 37, 2, 5,
    2, 3, 2, 13, 2, 7, 2, 3, 2, 5, 2, 479, 2, 3, 2, 761,
    2, 23, 2, 3, 2, 41, 2, 47, 2, 3, 2, 89, 2, 5, 2, 3,
    2, 7, 2, 1117, 2, 3, 2, 5, 2, 31, 2, 3, 2, 233, 2, 7,
    2, 3, 2, 1787, 2, 11, 2, 3, 2, 373, 2, 5, 2, 3, 2, 23,
    2, 43, 2, 3, 2, 5, 2, 17, 2, 3, 2, 7, 2, 107, 2, 3,
    2, 13, 2]

/-- Table 9 row: the prime after 5845193 is 5845193 + 116. -/
theorem gap9_116 : IsGapAt 5845193 116 :=
  isGapAt_of 5845193 116 (pB (by decide +kernel)) (by show Nat.Prime 5845309; exact pB (by decide +kernel)) gds_116 (by decide +kernel)

def gds_124 : List ℕ := [
    2, 3, 2, 7, 2, 13, 2, 3, 2, 211, 2, 5, 2, 3, 2, 23,
    2, 7, 2, 3, 2, 5, 2, 11, 2, 3, 2, 389, 2, 251, 2, 3,
    2, 19, 2, 41, 2, 3, 2, 107, 2, 5, 2, 3, 2, 7, 2, 619,
    2, 3, 2, 5, 2, 43, 2, 3, 2, 13, 2, 7, 2, 3, 2, 1907,
    2, 17, 2, 3, 2, 2339, 2, 5, 2, 3, 2, 31, 2, 1109, 2, 3,
    2, 5, 2, 13, 2, 3, 2, 7, 2, 11, 2, 3, 2, 127, 2, 73,
    2, 3, 2, 17, 2, 5, 2, 3, 2, 67, 2, 23, 2, 3, 2, 5,
    2, 29, 2, 3, 2, 41, 2, 311, 2, 3, 2]

/-- Table 9 row: the prime after 6752623 is 6752623 + 124. -/
theorem gap9_124 : IsGapAt 6752623 124 :=
  isGapAt_of 6752623 124 (pB (by decide +kernel)) (by show Nat.Prime 6752747; exact pB (by decide +kernel)) gds_124 (by decide +kernel)

def gds_134 : List ℕ := [
    2, 109, 2, 3, 2, 23, 2, 5, 2, 3, 2, 7, 2, 769, 2, 3,
    2, 5, 2, 67, 2, 3, 2, 2027, 2, 7, 2, 3, 2, 61, 2, 11,
    2, 3, 2, 191, 2, 5, 2, 3, 2, 421, 2, 127, 2, 3, 2, 5,
    2, 263, 2, 3, 2, 7, 2, 167, 2, 3, 2, 383, 2, 17, 2, 3,
    2, 43, 2, 5, 2, 3, 2, 457, 2, 53, 2, 3, 2, 5, 2, 149,
    2, 3, 2, 1019, 2, 29, 2, 3, 2, 13, 2, 859, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 19, 2, 1973, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 71, 2, 13, 2, 3, 2, 11, 2, 257, 2, 3, 2, 1361, 2, 5,
    2, 3, 2, 101, 2]

/-- Table 9 row: the prime after 6958667 is 6958667 + 134. -/
theorem gap9_134 : IsGapAt 6958667 134 :=
  isGapAt_of 6958667 134 (pB (by decide +kernel)) (by show Nat.Prime 6958801; exact pB (by decide +kernel)) gds_134 (by decide +kernel)

def gds_140 : List ℕ := [
    2, 19, 2, 3, 2, 5, 2, 919, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 43, 2, 61, 2, 3, 2, 179, 2, 5, 2, 3, 2, 13, 2, 1117,
    2, 3, 2, 5, 2, 37, 2, 3, 2, 857, 2, 23, 2, 3, 2, 739,
    2, 83, 2, 3, 2, 7, 2, 5, 2, 3, 2, 31, 2, 17, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 563, 2, 271, 2, 3, 2, 19, 2, 11,
    2, 3, 2, 821, 2, 5, 2, 3, 2, 23, 2, 547, 2, 3, 2, 5,
    2, 2719, 2, 3, 2, 11, 2, 43, 2, 3, 2, 13, 2, 7, 2, 3,
    2, 431, 2, 5, 2, 3, 2, 47, 2, 31, 2, 3, 2, 5, 2, 97,
    2, 3, 2, 163, 2, 13, 2, 3, 2, 7, 2]

/-- Table 9 row: the prime after 7621259 is 7621259 + 140. -/
theorem gap9_140 : IsGapAt 7621259 140 :=
  isGapAt_of 7621259 140 (pB (by decide +kernel)) (by show Nat.Prime 7621399; exact pB (by decide +kernel)) gds_140 (by decide +kernel)

def gds_142 : List ℕ := [
    2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 11, 2, 3, 2, 71,
    2, 43, 2, 3, 2, 739, 2, 5, 2, 3, 2, 97, 2, 1619, 2, 3,
    2, 5, 2, 107, 2, 3, 2, 13, 2, 17, 2, 3, 2, 29, 2, 7,
    2, 3, 2, 23, 2, 5, 2, 3, 2, 769, 2, 59, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 37, 2, 2963, 2, 3, 2, 7, 2, 11, 2, 3,
    2, 173, 2, 5, 2, 3, 2, 41, 2, 7, 2, 3, 2, 5, 2, 269,
    2, 3, 2, 11, 2, 31, 2, 3, 2, 359, 2, 1019, 2, 3, 2, 179,
    2, 5, 2, 3, 2, 7, 2, 73, 2, 3, 2, 5, 2, 607, 2, 3,
    2, 131, 2, 7, 2, 3, 2, 491, 2, 389, 2, 3, 2]

/-- Table 9 row: the prime after 10343761 is 10343761 + 142. -/
theorem gap9_142 : IsGapAt 10343761 142 :=
  isGapAt_of 10343761 142 (p10343761) (by show Nat.Prime 10343903; exact p10343903) gds_142 (by decide +kernel)

def gds_144 : List ℕ := [
    2, 3, 2, 17, 2, 367, 2, 3, 2, 11, 2, 5, 2, 3, 2, 7,
    2, 173, 2, 3, 2, 5, 2, 2087, 2, 3, 2, 41, 2, 7, 2, 3,
    2, 43, 2, 401, 2, 3, 2, 1327, 2, 5, 2, 3, 2, 13, 2, 263,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 113, 2, 3, 2, 1499,
    2, 229, 2, 3, 2, 2143, 2, 5, 2, 3, 2, 11, 2, 1229, 2, 3,
    2, 5, 2, 541, 2, 3, 2, 31, 2, 19, 2, 3, 2, 97, 2, 107,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 23, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 127, 2, 11, 2, 3, 2, 13, 2, 47, 2, 3,
    2, 607, 2, 5, 2, 3, 2, 2069, 2, 1873, 2, 3, 2, 5, 2]

/-- Table 9 row: the prime after 11981443 is 11981443 + 144. -/
theorem gap9_144 : IsGapAt 11981443 144 :=
  isGapAt_of 11981443 144 (p11981443) (by show Nat.Prime 11981587; exact p11981587) gds_144 (by decide +kernel)

def gds_150 : List ℕ := [
    2, 29, 2, 3, 2, 7, 2, 5, 2, 3, 2, 97, 2, 709, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 23, 2, 11, 2, 3, 2, 19, 2, 563,
    2, 3, 2, 197, 2, 5, 2, 3, 2, 17, 2, 13, 2, 3, 2, 5,
    2, 2879, 2, 3, 2, 163, 2, 43, 2, 3, 2, 29, 2, 7, 2, 3,
    2, 37, 2, 5, 2, 3, 2, 31, 2, 113, 2, 3, 2, 5, 2, 2153,
    2, 3, 2, 1451, 2, 107, 2, 3, 2, 7, 2, 11, 2, 3, 2, 13,
    2, 5, 2, 3, 2, 83, 2, 7, 2, 3, 2, 5, 2, 17, 2, 3,
    2, 11, 2, 23, 2, 3, 2, 613, 2, 13, 2, 3, 2, 947, 2, 5,
    2, 3, 2, 7, 2, 31, 2, 3, 2, 5, 2, 37, 2, 3, 2, 17,
    2, 7, 2, 3, 2]

/-- Table 9 row: the prime after 13626257 is 13626257 + 150. -/
theorem gap9_150 : IsGapAt 13626257 150 :=
  isGapAt_of 13626257 150 (p13626257) (by show Nat.Prime 13626407; exact p13626407) gds_150 (by decide +kernel)

def gds_156 : List ℕ := [
    2, 3, 2, 7, 2, 23, 2, 3, 2, 317, 2, 167, 2, 3, 2, 1031,
    2, 5, 2, 3, 2, 17, 2, 29, 2, 3, 2, 5, 2, 19, 2, 3,
    2, 31, 2, 307, 2, 3, 2, 11, 2, 503, 2, 3, 2, 7, 2, 5,
    2, 3, 2, 23, 2, 13, 2, 3, 2, 5, 2, 7, 2, 3, 2, 1453,
    2, 1481, 2, 3, 2, 1069, 2, 41, 2, 3, 2, 1609, 2, 5, 2, 3,
    2, 29, 2, 11, 2, 3, 2, 5, 2, 17, 2, 3, 2, 107, 2, 31,
    2, 3, 2, 1597, 2, 7, 2, 3, 2, 11, 2, 5, 2, 3, 2, 199,
    2, 271, 2, 3, 2, 5, 2, 61, 2, 3, 2, 17, 2, 2671, 2, 3,
    2, 7, 2, 13, 2, 3, 2, 137, 2, 5, 2, 3, 2, 83, 2, 7,
    2, 3, 2, 5, 2, 11, 2, 3, 2, 41, 2]

/-- Table 9 row: the prime after 17983717 is 17983717 + 156. -/
theorem gap9_156 : IsGapAt 17983717 156 :=
  isGapAt_of 17983717 156 (p17983717) (by show Nat.Prime 17983873; exact p17983873) gds_156 (by decide +kernel)

def gds_158 : List ℕ := [
    2, 11, 2, 3, 2, 17, 2, 67, 2, 3, 2, 2593, 2, 5, 2, 3,
    2, 89, 2, 5059, 2, 3, 2, 5, 2, 37, 2, 3, 2, 23, 2, 911,
    2, 3, 2, 967, 2, 7, 2, 3, 2, 13, 2, 5, 2, 3, 2, 6793,
    2, 263, 2, 3, 2, 5, 2, 29, 2, 3, 2, 19, 2, 313, 2, 3,
    2, 7, 2, 11, 2, 3, 2, 3517, 2, 5, 2, 3, 2, 41, 2, 7,
    2, 3, 2, 5, 2, 401, 2, 3, 2, 11, 2, 509, 2, 3, 2, 47,
    2, 19, 2, 3, 2, 4783, 2, 5, 2, 3, 2, 7, 2, 2293, 2, 3,
    2, 5, 2, 271, 2, 3, 2, 13, 2, 7, 2, 3, 2, 1193, 2, 1483,
    2, 3, 2, 83, 2, 5, 2, 3, 2, 101, 2, 137, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 7, 2, 2909, 2, 3, 2, 11, 2]

/-- Table 9 row: the prime after 49269581 is 49269581 + 158. -/
theorem gap9_158 : IsGapAt 49269581 158 :=
  isGapAt_of 49269581 158 (p49269581) (by show Nat.Prime 49269739; exact p49269739) gds_158 (by decide +kernel)

def gds_166 : List ℕ := [
    2, 3, 2, 5, 2, 727, 2, 3, 2, 109, 2, 47, 2, 3, 2, 641,
    2, 67, 2, 3, 2, 7, 2, 5, 2, 3, 2, 59, 2, 11, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 13, 2, 17, 2, 3, 2, 2137, 2, 593,
    2, 3, 2, 11, 2, 5, 2, 3, 2, 157, 2, 31, 2, 3, 2, 5,
    2, 13, 2, 3, 2, 457, 2, 113, 2, 3, 2, 17, 2, 7, 2, 3,
    2, 173, 2, 5, 2, 3, 2, 8669, 2, 23, 2, 3, 2, 5, 2, 11,
    2, 3, 2, 19, 2, 1031, 2, 3, 2, 7, 2, 43, 2, 3, 2, 41,
    2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 6691, 2, 3,
    2, 137, 2, 139, 2, 3, 2, 23, 2, 19, 2, 3, 2, 6011, 2, 5,
    2, 3, 2, 7, 2, 521, 2, 3, 2, 5, 2, 719, 2, 3, 2, 2357,
    2, 7, 2, 3, 2]

/-- Table 9 row: the prime after 83751121 is 83751121 + 166. -/
theorem gap9_166 : IsGapAt 83751121 166 :=
  isGapAt_of 83751121 166 (p83751121) (by show Nat.Prime 83751287; exact p83751287) gds_166 (by decide +kernel)

def gds_186 : List ℕ := [
    2, 59, 2, 3, 2, 769, 2, 5, 2, 3, 2, 97, 2, 17, 2, 3,
    2, 5, 2, 227, 2, 3, 2, 229, 2, 11, 2, 3, 2, 1217, 2, 19,
    2, 3, 2, 7, 2, 5, 2, 3, 2, 193, 2, 103, 2, 3, 2, 5,
    2, 7, 2, 3, 2, 151, 2, 1237, 2, 3, 2, 89, 2, 13, 2, 3,
    2, 223, 2, 5, 2, 3, 2, 109, 2, 29, 2, 3, 2, 5, 2, 31,
    2, 3, 2, 6581, 2, 521, 2, 3, 2, 3433, 2, 7, 2, 3, 2, 61,
    2, 5, 2, 3, 2, 389, 2, 347, 2, 3, 2, 5, 2, 5449, 2, 3,
    2, 11, 2, 17, 2, 3, 2, 7, 2, 79, 2, 3, 2, 8123, 2, 5,
    2, 3, 2, 29, 2, 7, 2, 3, 2, 5, 2, 13, 2, 3, 2, 67,
    2, 19, 2, 3, 2, 17, 2, 107, 2, 3, 2, 47, 2, 5, 2, 3,
    2, 7, 2, 1231, 2, 3, 2, 5, 2, 83, 2, 3, 2, 23, 2, 7,
    2, 3, 2, 11, 2, 2903, 2, 3, 2]

/-- Table 9 row: the prime after 147684137 is 147684137 + 186. -/
theorem gap9_186 : IsGapAt 147684137 186 :=
  isGapAt_of 147684137 186 (p147684137) (by show Nat.Prime 147684323; exact p147684323) gds_186 (by decide +kernel)

def gds_194 : List ℕ := [
    2, 337, 2, 3, 2, 11, 2, 5, 2, 3, 2, 23, 2, 149, 2, 3,
    2, 5, 2, 19, 2, 3, 2, 13, 2, 53, 2, 3, 2, 137, 2, 7,
    2, 3, 2, 37, 2, 5, 2, 3, 2, 103, 2, 383, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 359, 2, 29, 2, 3, 2, 7, 2, 17, 2, 3,
    2, 4241, 2, 5, 2, 3, 2, 11, 2, 7, 2, 3, 2, 5, 2, 683,
    2, 3, 2, 131, 2, 2617, 2, 3, 2, 101, 2, 41, 2, 3, 2, 17,
    2, 5, 2, 3, 2, 7, 2, 23, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 29, 2, 7, 2, 3, 2, 11621, 2, 127, 2, 3, 2, 439, 2, 5,
    2, 3, 2, 53, 2, 19, 2, 3, 2, 5, 2, 59, 2, 3, 2, 7,
    2, 509, 2, 3, 2, 23, 2, 5399, 2, 3, 2, 43, 2, 5, 2, 3,
    2, 739, 2, 17, 2, 3, 2, 5, 2, 1481, 2, 3, 2, 41, 2, 3331,
    2, 3, 2, 13, 2, 11, 2, 3, 2, 7, 2, 5, 2, 3, 2, 3191,
    2]

/-- Table 9 row: the prime after 166726367 is 166726367 + 194. -/
theorem gap9_194 : IsGapAt 166726367 194 :=
  isGapAt_of 166726367 194 (p166726367) (by show Nat.Prime 166726561; exact p166726561) gds_194 (by decide +kernel)

def gds_200 : List ℕ := [
    2, 7, 2, 3, 2, 5, 2, 1031, 2, 3, 2, 13, 2, 79, 2, 3,
    2, 7699, 2, 139, 2, 3, 2, 43, 2, 5, 2, 3, 2, 7, 2, 17,
    2, 3, 2, 5, 2, 13, 2, 3, 2, 181, 2, 7, 2, 3, 2, 691,
    2, 11, 2, 3, 2, 7753, 2, 5, 2, 3, 2, 31, 2, 647, 2, 3,
    2, 5, 2, 911, 2, 3, 2, 7, 2, 151, 2, 3, 2, 3319, 2, 37,
    2, 3, 2, 12799, 2, 5, 2, 3, 2, 13, 2, 53, 2, 3, 2, 5,
    2, 23, 2, 3, 2, 199, 2, 19, 2, 3, 2, 29, 2, 43, 2, 3,
    2, 7, 2, 5, 2, 3, 2, 113, 2, 31, 2, 3, 2, 5, 2, 7,
    2, 3, 2, 101, 2, 17, 2, 3, 2, 11, 2, 17599, 2, 3, 2, 23,
    2, 5, 2, 3, 2, 293, 2, 233, 2, 3, 2, 5, 2, 2731, 2, 3,
    2, 149, 2, 89, 2, 3, 2, 13, 2, 7, 2, 3, 2, 773, 2, 5,
    2, 3, 2, 19, 2, 11, 2, 3, 2, 5, 2, 83, 2, 3, 2, 47,
    2, 13, 2, 3, 2, 7, 2]

/-- Table 9 row: the prime after 378043979 is 378043979 + 200. -/
theorem gap9_200 : IsGapAt 378043979 200 :=
  isGapAt_of 378043979 200 (p378043979) (by show Nat.Prime 378044179; exact p378044179) gds_200 (by decide +kernel)

def gds_224 : List ℕ := [
    2, 5, 2, 3, 2, 1049, 2, 7, 2, 3, 2, 5, 2, 347, 2, 3,
    2, 461, 2, 1237, 2, 3, 2, 11, 2, 389, 2, 3, 2, 13, 2, 5,
    2, 3, 2, 7, 2, 6869, 2, 3, 2, 5, 2, 29, 2, 3, 2, 23,
    2, 7, 2, 3, 2, 331, 2, 13, 2, 3, 2, 101, 2, 5, 2, 3,
    2, 107, 2, 11, 2, 3, 2, 5, 2, 151, 2, 3, 2, 7, 2, 67,
    2, 3, 2, 31, 2, 479, 2, 3, 2, 11, 2, 5, 2, 3, 2, 97,
    2, 4327, 2, 3, 2, 5, 2, 37, 2, 3, 2, 13, 2, 227, 2, 3,
    2, 53, 2, 929, 2, 3, 2, 7, 2, 5, 2, 3, 2, 89, 2, 59,
    2, 3, 2, 5, 2, 7, 2, 3, 2, 19, 2, 23, 2, 3, 2, 9631,
    2, 31, 2, 3, 2, 3967, 2, 5, 2, 3, 2, 11, 2, 17, 2, 3,
    2, 5, 2, 109, 2, 3, 2, 3547, 2, 15919, 2, 3, 2, 43, 2, 7,
    2, 3, 2, 61, 2, 5, 2, 3, 2, 13, 2, 401, 2, 3, 2, 5,
    2, 619, 2, 3, 2, 2693, 2, 11, 2, 3, 2, 7, 2, 14669, 2, 3,
    2, 83, 2, 5, 2, 3, 2, 4057, 2, 7, 2, 3, 2, 5, 2]

/-- Table 9 row: the prime after 409866323 is 409866323 + 224. -/
theorem gap9_224 : IsGapAt 409866323 224 :=
  isGapAt_of 409866323 224 (p409866323) (by show Nat.Prime 409866547; exact p409866547) gds_224 (by decide +kernel)

def gds_226 : List ℕ := [
    2, 3, 2, 5, 2, 6899, 2, 3, 2, 13, 2, 101, 2, 3, 2, 11,
    2, 79, 2, 3, 2, 7, 2, 5, 2, 3, 2, 17, 2, 19, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 1871, 2, 5413, 2, 3, 2, 13399, 2, 37,
    2, 3, 2, 2039, 2, 5, 2, 3, 2, 14627, 2, 11, 2, 3, 2, 5,
    2, 103, 2, 3, 2, 229, 2, 149, 2, 3, 2, 883, 2, 7, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 13, 2, 3137, 2, 3, 2, 5, 2, 17,
    2, 3, 2, 3119, 2, 71, 2, 3, 2, 7, 2, 47, 2, 3, 2, 5839,
    2, 5, 2, 3, 2, 1459, 2, 7, 2, 3, 2, 5, 2, 11, 2, 3,
    2, 17, 2, 10007, 2, 3, 2, 7951, 2, 191, 2, 3, 2, 23, 2, 5,
    2, 3, 2, 7, 2, 21673, 2, 3, 2, 5, 2, 31, 2, 3, 2, 911,
    2, 7, 2, 3, 2, 13, 2, 7537, 2, 3, 2, 211, 2, 5, 2, 3,
    2, 21187, 2, 131, 2, 3, 2, 5, 2, 41, 2, 3, 2, 7, 2, 11,
    2, 3, 2, 37, 2, 17, 2, 3, 2, 47, 2, 5, 2, 3, 2, 15187,
    2, 29, 2, 3, 2, 5, 2, 5441, 2, 3, 2, 19, 2, 3221, 2, 3,
    2]

/-- Table 9 row: the prime after 519653371 is 519653371 + 226. -/
theorem gap9_226 : IsGapAt 519653371 226 :=
  isGapAt_of 519653371 226 (p519653371) (by show Nat.Prime 519653597; exact p519653597) gds_226 (by decide +kernel)

def gds_228 : List ℕ := [
    2, 3, 2, 5417, 2, 5, 2, 3, 2, 71, 2, 11, 2, 3, 2, 5,
    2, 31, 2, 3, 2, 7, 2, 20347, 2, 3, 2, 13, 2, 89, 2, 3,
    2, 11, 2, 5, 2, 3, 2, 443, 2, 439, 2, 3, 2, 5, 2, 43,
    2, 3, 2, 197, 2, 13, 2, 3, 2, 37, 2, 53, 2, 3, 2, 7,
    2, 5, 2, 3, 2, 421, 2, 29, 2, 3, 2, 5, 2, 7, 2, 3,
    2, 8039, 2, 223, 2, 3, 2, 127, 2, 17, 2, 3, 2, 743, 2, 5,
    2, 3, 2, 11, 2, 20921, 2, 3, 2, 5, 2, 97, 2, 3, 2, 19,
    2, 4567, 2, 3, 2, 16829, 2, 7, 2, 3, 2, 17, 2, 5, 2, 3,
    2, 29, 2, 13, 2, 3, 2, 5, 2, 4421, 2, 3, 2, 31, 2, 11,
    2, 3, 2, 7, 2, 19, 2, 3, 2, 499, 2, 5, 2, 3, 2, 16103,
    2, 7, 2, 3, 2, 5, 2, 137, 2, 3, 2, 23, 2, 2423, 2, 3,
    2, 23981, 2, 28597, 2, 3, 2, 13, 2, 5, 2, 3, 2, 7, 2, 17,
    2, 3, 2, 5, 2, 113, 2, 3, 2, 41, 2, 7, 2, 3, 2, 89,
    2, 11, 2, 3, 2, 6781, 2, 5, 2, 3, 2, 43, 2, 61, 2, 3,
    2, 5, 2]

/-- Table 9 row: the prime after 895858039 is 895858039 + 228. -/
theorem gap9_228 : IsGapAt 895858039 228 :=
  isGapAt_of 895858039 228 (p895858039) (by show Nat.Prime 895858267; exact p895858267) gds_228 (by decide +kernel)

def gds_254 : List ℕ := [
    2, 223, 2, 3, 2, 5, 2, 347, 2, 3, 2, 7, 2, 367, 2, 3,
    2, 1667, 2, 11, 2, 3, 2, 17, 2, 5, 2, 3, 2, 157, 2, 31751,
    2, 3, 2, 5, 2, 10771, 2, 3, 2, 11, 2, 14723, 2, 3, 2, 13,
    2, 23, 2, 3, 2, 7, 2, 5, 2, 3, 2, 8563, 2, 19, 2, 3,
    2, 5, 2, 7, 2, 3, 2, 7411, 2, 13, 2, 3, 2, 29, 2, 37,
    2, 3, 2, 79, 2, 5, 2, 3, 2, 389, 2, 17, 2, 3, 2, 5,
    2, 61, 2, 3, 2, 3169, 2, 3191, 2, 3, 2, 11, 2, 7, 2, 3,
    2, 73, 2, 5, 2, 3, 2, 173, 2, 8423, 2, 3, 2, 5, 2, 53,
    2, 3, 2, 239, 2, 127, 2, 3, 2, 7, 2, 31, 2, 3, 2, 67,
    2, 5, 2, 3, 2, 43, 2, 7, 2, 3, 2, 5, 2, 9551, 2, 3,
    2, 167, 2, 4759, 2, 3, 2, 1601, 2, 967, 2, 3, 2, 11, 2, 5,
    2, 3, 2, 7, 2, 1951, 2, 3, 2, 5, 2, 23, 2, 3, 2, 17341,
    2, 7, 2, 3, 2, 137, 2, 541, 2, 3, 2, 13, 2, 5, 2, 3,
    2, 433, 2, 41, 2, 3, 2, 5, 2, 11, 2, 3, 2, 7, 2, 47,
    2, 3, 2, 17, 2, 13, 2, 3, 2, 23, 2, 5, 2, 3, 2, 11,
    2, 79, 2, 3, 2, 5, 2, 1499, 2, 3, 2, 19, 2]

/-- Table 9 row: the prime after 1202442089 is 1202442089 + 254. -/
theorem gap9_254 : IsGapAt 1202442089 254 :=
  isGapAt_of 1202442089 254 (p1202442089) (by show Nat.Prime 1202442343; exact p1202442343) gds_254 (by decide +kernel)

def gds_256 : List ℕ := [
    2, 3, 2, 61, 2, 7, 2, 3, 2, 8179, 2, 11, 2, 3, 2, 32713,
    2, 5, 2, 3, 2, 599, 2, 17, 2, 3, 2, 5, 2, 37, 2, 3,
    2, 7, 2, 19, 2, 3, 2, 29, 2, 101, 2, 3, 2, 673, 2, 5,
    2, 3, 2, 383, 2, 3803, 2, 3, 2, 5, 2, 13, 2, 3, 2, 31,
    2, 367, 2, 3, 2, 523, 2, 2347, 2, 3, 2, 7, 2, 5, 2, 3,
    2, 14813, 2, 1277, 2, 3, 2, 5, 2, 7, 2, 3, 2, 97, 2, 53,
    2, 3, 2, 11, 2, 1583, 2, 3, 2, 4967, 2, 5, 2, 3, 2, 13,
    2, 109, 2, 3, 2, 5, 2, 2857, 2, 3, 2, 4219, 2, 17, 2, 3,
    2, 36473, 2, 7, 2, 3, 2, 199, 2, 5, 2, 3, 2, 83, 2, 11,
    2, 3, 2, 5, 2, 19, 2, 3, 2, 4759, 2, 29, 2, 3, 2, 7,
    2, 127, 2, 3, 2, 11, 2, 5, 2, 3, 2, 23, 2, 7, 2, 3,
    2, 5, 2, 20411, 2, 3, 2, 79, 2, 1747, 2, 3, 2, 13, 2, 67,
    2, 3, 2, 43, 2, 5, 2, 3, 2, 7, 2, 25303, 2, 3, 2, 5,
    2, 11, 2, 3, 2, 29, 2, 7, 2, 3, 2, 317, 2, 113, 2, 3,
    2, 19, 2, 5, 2, 3, 2, 11, 2, 22039, 2, 3, 2, 5, 2, 89,
    2, 3, 2, 7, 2, 47, 2, 3, 2, 31, 2, 37, 2, 3, 2]

/-- Table 9 row: the prime after 1872851947 is 1872851947 + 256. -/
theorem gap9_256 : IsGapAt 1872851947 256 :=
  isGapAt_of 1872851947 256 (p1872851947) (by show Nat.Prime 1872852203; exact p1872852203) gds_256 (by decide +kernel)

end LeanLab.OeSHP2014
