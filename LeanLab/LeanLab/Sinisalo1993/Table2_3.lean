/-
P0041 Sinisalo 1993, Table 2, rows 35 to 51: for each listed prime p and its
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

theorem p34362019 : Nat.Prime 34362019 := by
  refine Pratt.pratt 34362019 2 [(2, 1), (3, 2), (41, 1), (101, 1), (461, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p37890101 : Nat.Prime 37890101 := by
  refine Pratt.pratt 37890101 2 [(2, 2), (5, 2), (378901, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p49357367 : Nat.Prime 49357367 := by
  refine Pratt.pratt 49357367 5 [(2, 1), (1567, 1), (15749, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p67854541 : Nat.Prime 67854541 := by
  refine Pratt.pratt 67854541 17 [(2, 2), (3, 1), (5, 1), (13, 1), (86993, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p68787293 : Nat.Prime 68787293 := by
  refine Pratt.pratt 68787293 2 [(2, 2), (7, 1), (37, 1), (67, 1), (991, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p74858269 : Nat.Prime 74858269 := by
  refine Pratt.pratt 74858269 2 [(2, 2), (3, 1), (229, 1), (27241, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p129795803 : Nat.Prime 129795803 := by
  refine Pratt.pratt 129795803 2 [(2, 1), (19, 1), (3415679, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p144516049 : Nat.Prime 144516049 := by
  refine Pratt.pratt 144516049 7 [(2, 4), (3, 1), (17, 1), (29, 1), (31, 1), (197, 1)] (by norm_num)
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
theorem p150386021 : Nat.Prime 150386021 := by
  refine Pratt.pratt 150386021 3 [(2, 2), (5, 1), (1907, 1), (3943, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p206891543 : Nat.Prime 206891543 := by
  refine Pratt.pratt 206891543 5 [(2, 1), (11, 1), (13, 1), (53, 1), (13649, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p247012187 : Nat.Prime 247012187 := by
  refine Pratt.pratt 247012187 2 [(2, 1), (883, 1), (139871, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p277231373 : Nat.Prime 277231373 := by
  refine Pratt.pratt 277231373 2 [(2, 2), (11, 1), (6300713, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p292221859 : Nat.Prime 292221859 := by
  refine Pratt.pratt 292221859 2 [(2, 1), (3, 1), (5701, 1), (8543, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p299433077 : Nat.Prime 299433077 := by
  refine Pratt.pratt 299433077 2 [(2, 2), (74858269, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p74858269
theorem p379409603 : Nat.Prime 379409603 := by
  refine Pratt.pratt 379409603 2 [(2, 1), (11, 1), (13, 1), (1326607, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p554462747 : Nat.Prime 554462747 := by
  refine Pratt.pratt 554462747 2 [(2, 1), (277231373, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p277231373
theorem p678545411 : Nat.Prime 678545411 := by
  refine Pratt.pratt 678545411 2 [(2, 1), (5, 1), (67854541, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p67854541
theorem p1168887437 : Nat.Prime 1168887437 := by
  refine Pratt.pratt 1168887437 2 [(2, 2), (292221859, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p292221859
theorem p1673267009 : Nat.Prime 1673267009 := by
  refine Pratt.pratt 1673267009 3 [(2, 6), (7, 1), (337, 1), (11083, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p1927527587 : Nat.Prime 1927527587 := by
  refine Pratt.pratt 1927527587 2 [(2, 1), (733, 1), (1314821, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p2331463987 : Nat.Prime 2331463987 := by
  refine Pratt.pratt 2331463987 3 [(2, 1), (3, 5), (4797251, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

def ds_739 : List ℕ := [
    2, 5, 3, 37, 3, 5, 3, 223, 3, 3, 7, 59,
    3, 5, 3, 3, 3, 19, 11, 3, 5, 13, 3, 3,
    17, 3, 5, 3, 1597, 3, 1223, 3, 3, 191, 3, 139,
    7, 5, 3, 3, 3, 109, 3, 5, 3, 7, 43, 5,
    3, 23, 3, 3, 7, 3, 3, 3, 3, 73, 1607, 3,
    5, 3, 179, 3, 5, 3, 11, 167, 3, 4861, 3, 3,
    7, 5, 1997, 3, 3, 11, 3, 7, 3, 61, 3, 5,
    701, 3, 3, 107, 3, 5, 3, 3, 1117, 3, 2311, 3,
    3, 3, 5, 47, 13, 3, 3, 3, 29, 7, 3, 3,
    3, 3511, 17, 5, 3, 7, 19, 3, 5, 3, 3, 3,
    7, 5, 3, 3, 977, 3, 17, 3, 11, 5]

theorem prime_sub_739 : Nat.Prime (34362758 - 739) := by
  show Nat.Prime 34362019
  exact p34362019

theorem check_739 : allC 34362758 739 P10k ds_739 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 34362758 is 739. -/
theorem minGB_S_739 : minGB 34362758 = 739 :=
  minGB_eq_of P10k P10k_complete 34362758 739 (by norm_num) (by norm_num) prime_sub_739 ds_739 check_739

def ds_743 : List ℕ := [
    2, 17, 7, 3, 131, 3, 13, 3, 23, 5, 3, 3,
    59, 3, 7, 29, 5, 3, 3, 17, 3, 3, 607, 5,
    3, 11, 3, 2039, 3, 19, 3, 7, 53, 3, 5, 3,
    3, 3, 11, 7, 5, 3, 2467, 3, 2153, 3, 3, 3,
    19, 3, 11, 5, 3, 13, 7, 151, 5, 3, 3, 331,
    3, 149, 3, 79, 3, 3889, 3, 3, 1381, 3, 163, 5,
    3, 3, 3, 7, 5, 3, 29, 3, 5, 3, 11, 3,
    3, 31, 5, 3, 2143, 3, 7, 5, 3, 43, 3, 1609,
    5, 127, 3, 3, 3, 173, 11, 5, 3, 3, 37, 7,
    5, 3, 3, 3, 137, 3, 3, 13, 3, 199, 41, 5,
    3, 3, 7, 17, 3, 113, 3, 5, 3, 3, 3]

theorem prime_sub_743 : Nat.Prime (37890844 - 743) := by
  show Nat.Prime 37890101
  exact p37890101

theorem check_743 : allC 37890844 743 P10k ds_743 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 37890844 is 743. -/
theorem minGB_S_743 : minGB 37890844 = 743 :=
  minGB_eq_of P10k P10k_complete 37890844 743 (by norm_num) (by norm_num) prime_sub_743 ds_743 check_743

def ds_761 : List ℕ := [
    2, 5, 17, 3, 3917, 3, 11, 3, 5, 7, 3, 3,
    29, 3, 4219, 5, 23, 3, 3, 7, 3, 3, 5, 677,
    3, 2803, 3, 17, 3, 5, 3, 13, 19, 3, 11, 3,
    3, 3, 1579, 5, 137, 3, 43, 3, 7, 3, 3, 3,
    293, 3, 5, 7, 3, 19, 2819, 5, 31, 3, 3, 7,
    3, 5, 3, 17, 3, 571, 3, 3, 11, 3, 5, 3253,
    3, 3, 3, 5, 29, 3, 41, 3, 71, 3, 467, 3,
    3, 5, 7, 3, 37, 3, 47, 11, 3, 7, 3, 5,
    421, 13, 3, 3, 3, 59, 5, 863, 3, 3, 79, 5,
    13, 3, 3, 3, 7, 3, 3, 31, 3, 41, 5, 7,
    3, 3, 11, 5, 3, 7, 3, 17, 3, 3, 3, 5,
    3, 3]

theorem prime_sub_761 : Nat.Prime (49358128 - 761) := by
  show Nat.Prime 49357367
  exact p49357367

theorem check_761 : allC 49358128 761 P10k ds_761 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 49358128 is 761. -/
theorem minGB_S_761 : minGB 49358128 = 761 :=
  minGB_eq_of P10k P10k_complete 49358128 761 (by norm_num) (by norm_num) prime_sub_761 ds_761 check_761

def ds_773 : List ℕ := [
    2, 2999, 1979, 3, 5, 3, 11, 3, 2069, 19, 3, 3,
    5, 3, 3769, 7, 1481, 3, 3, 5, 3, 3, 11, 31,
    3, 5, 3, 113, 3, 13, 3, 5, 7, 3, 11, 3,
    3, 3, 17, 2137, 7, 3, 5, 3, 197, 3, 3, 3,
    107, 3, 89, 73, 3, 5, 19, 7, 13, 3, 3, 5,
    3, 37, 3, 5, 3, 79, 3, 3, 7, 3, 3259, 131,
    3, 3, 3, 743, 7, 3, 5, 3, 97, 3, 5, 3,
    3, 29, 2447, 3, 5, 3, 881, 11, 3, 5, 3, 13,
    1451, 5, 3, 3, 3, 7, 23, 643, 3, 3, 617, 1459,
    7, 3, 3, 3, 29, 3, 3, 5, 3, 31, 1699, 13,
    3, 3, 11, 7, 3, 5, 3, 139, 3, 3, 3, 11,
    3, 3, 5, 3]

theorem prime_sub_773 : Nat.Prime (68788066 - 773) := by
  show Nat.Prime 68787293
  exact p68787293

theorem check_773 : allC 68788066 773 P10k ds_773 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 68788066 is 773. -/
theorem minGB_S_773 : minGB 68788066 = 773 :=
  minGB_eq_of P10k P10k_complete 68788066 773 (by norm_num) (by norm_num) prime_sub_773 ds_773 check_773

def ds_839 : List ℕ := [
    2, 7, 59, 3, 607, 3, 5, 3, 19, 23, 3, 3,
    11, 3, 5, 13, 7, 3, 3, 523, 3, 3, 409, 193,
    3, 7, 3, 5, 3, 41, 3, 13, 5, 3, 2179, 3,
    3, 3, 5, 11, 389, 3, 6563, 3, 5, 3, 3, 3,
    5, 3, 73, 11, 3, 19, 5, 97, 7, 3, 3, 1439,
    3, 31, 3, 7, 3, 5, 3, 3, 5, 3, 7, 41,
    3, 3, 3, 37, 619, 3, 17, 3, 307, 3, 101, 3,
    3, 13, 3259, 3, 1811, 3, 5, 7, 3, 191, 3, 11,
    3319, 7, 3, 3, 3, 5, 7, 11, 3, 3, 5, 19,
    13, 3, 3, 3, 5, 3, 3, 109, 3, 5, 547, 61,
    3, 3, 5, 199, 3, 11, 3, 23, 3, 3, 3, 443,
    3, 3, 71, 3, 7, 3, 5, 17, 3, 19, 3, 5,
    3]

theorem prime_sub_839 : Nat.Prime (129796642 - 839) := by
  show Nat.Prime 129795803
  exact p129795803

theorem check_839 : allC 129796642 839 P10k ds_839 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 129796642 is 839. -/
theorem minGB_S_839 : minGB 129796642 = 839 :=
  minGB_eq_of P10k P10k_complete 129796642 839 (by norm_num) (by norm_num) prime_sub_839 ds_839 check_839

def ds_853 : List ℕ := [
    2, 1997, 3, 5, 3, 11, 3, 7, 3, 3, 419, 5,
    3, 73, 3, 3, 3, 7, 5, 3, 2053, 11, 3, 3,
    5, 3, 7, 3, 19, 3, 5, 3, 3, 487, 3, 23,
    5, 149, 3, 3, 3, 337, 3, 37, 3, 3251, 11, 19,
    3, 7, 3, 3, 107, 3, 3, 3, 3, 7, 5, 3,
    13, 3, 5, 3, 7, 3, 1427, 5, 3, 4759, 3, 3,
    5, 83, 10111, 3, 3, 5, 3, 11, 3, 6967, 3, 409,
    7, 3, 3, 5, 3, 17, 3, 3, 5, 3, 4463, 3,
    3, 3, 7, 11, 5, 3, 3, 3, 89, 5, 3, 3,
    3, 1031, 5, 163, 3, 10211, 3511, 3, 61, 3, 3, 3,
    383, 11, 3, 3, 7, 3, 29, 3, 5, 7, 11, 3,
    13, 5, 3, 17, 3, 5, 3, 3, 4999, 3, 31, 3,
    13, 3]

theorem prime_sub_853 : Nat.Prime (144516902 - 853) := by
  show Nat.Prime 144516049
  exact p144516049

theorem check_853 : allC 144516902 853 P10k ds_853 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 144516902 is 853. -/
theorem minGB_S_853 : minGB 144516902 = 853 :=
  minGB_eq_of P10k P10k_complete 144516902 853 (by norm_num) (by norm_num) prime_sub_853 ds_853 check_853

def ds_911 : List ℕ := [
    2, 7, 67, 3, 31, 3, 5, 3, 1423, 23, 3, 3,
    257, 3, 5, 17, 7, 3, 3, 631, 3, 3, 79, 19,
    3, 7, 3, 5, 3, 11, 3, 2131, 5, 3, 6143, 3,
    3, 3, 5, 37, 11, 3, 139, 3, 5, 3, 3, 3,
    5, 3, 47, 59, 3, 107, 5, 127, 7, 3, 3, 173,
    3, 13, 3, 7, 3, 5, 3, 3, 5, 3, 7, 17,
    3, 3, 3, 31, 349, 3, 1429, 3, 373, 3, 19, 3,
    3, 11, 13, 3, 17, 3, 5, 7, 3, 947, 3, 11783,
    11, 7, 3, 3, 3, 5, 7, 31, 3, 3, 5, 59,
    191, 3, 3, 3, 5, 3, 3, 11, 3, 5, 1637, 19,
    3, 3, 5, 13, 3, 701, 3, 23, 3, 3, 3, 1979,
    3, 3, 13, 3, 7, 3, 5, 67, 3, 6907, 3, 5,
    3, 11, 3, 5, 3, 53, 3, 8111, 3, 5, 3]

theorem prime_sub_911 : Nat.Prime (150386932 - 911) := by
  show Nat.Prime 150386021
  exact p150386021

theorem check_911 : allC 150386932 911 P10k ds_911 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 150386932 is 911. -/
theorem minGB_S_911 : minGB 150386932 = 911 :=
  minGB_eq_of P10k P10k_complete 150386932 911 (by norm_num) (by norm_num) prime_sub_911 ds_911 check_911

def ds_941 : List ℕ := [
    2, 31, 43, 3, 269, 3, 29, 3, 3931, 5, 3, 3,
    53, 3, 41, 17, 5, 3, 3, 7, 3, 3, 1987, 5,
    3, 23, 3, 1021, 3, 7, 3, 8089, 5023, 3, 5, 3,
    3, 3, 179, 19, 5, 3, 29, 3, 7, 3, 3, 3,
    11, 3, 4481, 5, 3, 31, 17, 43, 5, 3, 3, 7,
    3, 11, 3, 59, 3, 47, 3, 3, 101, 3, 277, 5,
    3, 3, 3, 13, 5, 3, 19, 3, 5, 3, 61, 3,
    3, 211, 5, 3, 13, 3, 127, 5, 3, 7, 3, 89,
    5, 43, 3, 3, 3, 11, 17, 5, 3, 3, 11131, 4903,
    5, 3, 3, 3, 7, 3, 3, 263, 3, 131, 23, 5,
    3, 3, 53, 1031, 3, 7, 3, 5, 3, 3, 3, 7,
    3, 3, 487, 3, 13, 3, 61, 5, 3, 11, 3, 7,
    3, 5, 3, 19, 3, 383, 3, 47, 3, 11, 3, 7,
    3, 5, 3]

theorem prime_sub_941 : Nat.Prime (206892484 - 941) := by
  show Nat.Prime 206891543
  exact p206891543

theorem check_941 : allC 206892484 941 P10k ds_941 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 206892484 is 941. -/
theorem minGB_S_941 : minGB 206892484 = 941 :=
  minGB_eq_of P10k P10k_complete 206892484 941 (by norm_num) (by norm_num) prime_sub_941 ds_941 check_941

def ds_977 : List ℕ := [
    2, 5503, 3109, 3, 47, 3, 37, 3, 113, 5, 3, 3,
    7, 3, 13, 17, 5, 3, 3, 73, 3, 3, 7, 5,
    3, 11, 3, 317, 3, 5231, 3, 173, 43, 3, 5, 3,
    3, 3, 7, 31, 5, 3, 61, 3, 157, 3, 3, 3,
    733, 3, 11, 5, 3, 7, 17, 19, 5, 3, 3, 13,
    3, 7, 3, 67, 3, 23, 3, 3, 107, 3, 277, 5,
    3, 3, 3, 137, 5, 3, 59, 3, 5, 3, 11, 3,
    3, 7129, 5, 3, 7, 3, 79, 5, 3, 19, 3, 7,
    5, 103, 3, 3, 3, 61, 11, 5, 3, 3, 7, 13,
    5, 3, 3, 3, 227, 3, 3, 7219, 3, 29, 43, 5,
    3, 3, 10909, 37, 3, 113, 3, 5, 3, 3, 3, 109,
    3, 3, 11, 3, 331, 3, 7, 5, 3, 29, 3, 11,
    3, 5, 3, 47, 3, 3929, 3, 7, 3, 53, 3, 43,
    3, 5, 3, 79, 19, 433, 3, 17]

theorem prime_sub_977 : Nat.Prime (247013164 - 977) := by
  show Nat.Prime 247012187
  exact p247012187

theorem check_977 : allC 247013164 977 P10k ds_977 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 247013164 is 977. -/
theorem minGB_S_977 : minGB 247013164 = 977 :=
  minGB_eq_of P10k P10k_complete 247013164 977 (by norm_num) (by norm_num) prime_sub_977 ds_977 check_977

def ds_1031 : List ℕ := [
    2, 5, 13933, 3, 163, 3, 11, 3, 5, 7, 3, 3,
    113, 3, 7013, 5, 16183, 3, 3, 7, 3, 3, 5, 29,
    3, 37, 3, 6343, 3, 5, 3, 19, 17, 3, 11, 3,
    3, 3, 23, 5, 31, 3, 389, 3, 7, 3, 3, 3,
    281, 3, 5, 7, 3, 911, 47, 5, 167, 3, 3, 7,
    3, 5, 3, 13, 3, 59, 3, 3, 11, 3, 5, 19,
    3, 3, 3, 5, 13, 3, 607, 3, 61, 3, 397, 3,
    3, 5, 7, 3, 89, 3, 13, 11, 3, 7, 3, 5,
    311, 347, 3, 3, 3, 2333, 5, 83, 3, 3, 19, 5,
    199, 3, 3, 3, 7, 3, 3, 43, 3, 17, 5, 7,
    3, 3, 11, 5, 3, 7, 3, 23, 3, 3, 3, 5,
    3, 3, 683, 3, 5, 3, 11677, 11, 3, 47, 3, 7,
    3, 7213, 3, 13, 3, 5, 3, 839, 3, 541, 3, 7,
    3, 19, 3, 11, 449, 5, 3, 109, 193, 5, 3, 3,
    3, 5, 4793, 3]

theorem prime_sub_1031 : Nat.Prime (299434108 - 1031) := by
  show Nat.Prime 299433077
  exact p299433077

theorem check_1031 : allC 299434108 1031 P10k ds_1031 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 299434108 is 1031. -/
theorem minGB_S_1031 : minGB 299434108 = 1031 :=
  minGB_eq_of P10k P10k_complete 299434108 1031 (by norm_num) (by norm_num) prime_sub_1031 ds_1031 check_1031

def ds_1049 : List ℕ := [
    2, 47, 7, 3, 17, 3, 5, 3, 13, 53, 3, 3,
    1129, 3, 5, 23, 431, 3, 3, 11, 3, 3, 271, 7,
    3, 13, 3, 5, 3, 17, 3, 7, 5, 3, 8971, 3,
    3, 3, 5, 7, 13, 3, 23, 3, 5, 3, 3, 3,
    5, 3, 73, 2707, 3, 193, 5, 577, 11, 3, 3, 43,
    3, 97, 3, 127, 3, 5, 3, 3, 5, 3, 2953, 89,
    3, 3, 3, 7, 2003, 3, 11, 3, 17, 3, 19, 3,
    3, 31, 1231, 3, 131, 3, 5, 37, 3, 13, 3, 313,
    7, 17, 3, 3, 3, 5, 883, 13, 3, 3, 5, 7,
    11, 3, 3, 3, 5, 3, 3, 179, 3, 5, 151, 19,
    3, 3, 5, 2381, 3, 37, 3, 7, 3, 3, 3, 23,
    3, 3, 7, 3, 19, 3, 5, 227, 3, 421, 3, 5,
    3, 29, 3, 5, 3, 11, 3, 13, 3, 5, 3, 1087,
    3, 7, 3, 17099, 5, 379, 3, 7, 5, 53, 3, 3,
    3, 7, 23, 3, 17, 3, 3]

theorem prime_sub_1049 : Nat.Prime (379410652 - 1049) := by
  show Nat.Prime 379409603
  exact p379409603

theorem check_1049 : allC 379410652 1049 P10k ds_1049 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 379410652 is 1049. -/
theorem minGB_S_1049 : minGB 379410652 = 1049 :=
  minGB_eq_of P10k P10k_complete 379410652 1049 (by norm_num) (by norm_num) prime_sub_1049 ds_1049 check_1049

def ds_1061 : List ℕ := [
    2, 5, 2437, 3, 137, 3, 7, 3, 5, 71, 3, 3,
    11, 3, 1103, 5, 7, 3, 3, 23, 3, 3, 5, 19,
    3, 7, 3, 11, 3, 5, 3, 677, 13451, 3, 67, 3,
    3, 3, 191, 5, 43, 3, 227, 3, 13, 3, 3, 3,
    7, 3, 5, 11, 3, 29, 17, 5, 7, 3, 3, 1867,
    3, 5, 3, 7, 3, 19, 3, 3, 23, 3, 5, 17,
    3, 3, 3, 5, 149, 3, 107, 3, 37, 3, 13, 3,
    3, 5, 1637, 3, 17, 3, 4663, 7, 3, 79, 3, 5,
    13, 7, 3, 3, 3, 73, 5, 11, 3, 3, 13, 5,
    29, 3, 3, 3, 937, 3, 3, 37, 3, 7, 5, 19,
    3, 3, 41, 5, 3, 11, 3, 47, 3, 3, 3, 5,
    3, 3, 23, 3, 5, 3, 9187, 12491, 3, 13, 3, 1789,
    3, 89, 3, 7, 3, 5, 3, 71, 3, 19, 3, 2161,
    3, 167, 3, 7, 29, 5, 3, 17, 13, 5, 3, 3,
    3, 5, 151, 3, 11, 3, 3, 2131, 3]

theorem prime_sub_1061 : Nat.Prime (554463808 - 1061) := by
  show Nat.Prime 554462747
  exact p554462747

theorem check_1061 : allC 554463808 1061 P10k ds_1061 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 554463808 is 1061. -/
theorem minGB_S_1061 : minGB 554463808 = 1061 :=
  minGB_eq_of P10k P10k_complete 554463808 1061 (by norm_num) (by norm_num) prime_sub_1061 ds_1061 check_1061

def ds_1091 : List ℕ := [
    2, 19249, 83, 3, 7, 3, 5, 3, 13, 11, 3, 3,
    73, 3, 5, 7, 307, 3, 3, 139, 3, 3, 199, 89,
    3, 13, 3, 5, 3, 547, 3, 61, 5, 3, 487, 3,
    3, 3, 5, 421, 7, 3, 449, 3, 5, 3, 3, 3,
    5, 3, 41, 29, 3, 613, 5, 7, 15913, 3, 3, 19,
    3, 11, 3, 47, 3, 5, 3, 3, 5, 3, 43, 11,
    3, 3, 3, 193, 7, 3, 293, 3, 1223, 3, 7, 3,
    3, 1097, 3271, 3, 17, 3, 5, 23, 3, 11, 3, 83,
    19, 1753, 3, 3, 3, 5, 17, 13, 3, 3, 5, 47,
    7, 3, 3, 3, 5, 3, 3, 7, 3, 5, 37, 59,
    3, 3, 5, 7, 3, 1889, 3, 67, 3, 3, 3, 2447,
    3, 3, 29, 3, 4079, 3, 5, 7, 3, 11, 3, 5,
    3, 16069, 3, 5, 3, 31, 3, 13, 3, 5, 3, 53,
    3, 101, 3, 373, 5, 11, 3, 17, 5, 137, 3, 3,
    3, 59, 7, 3, 23, 3, 3, 31, 3, 7, 3, 3,
    3]

theorem prime_sub_1091 : Nat.Prime (678546502 - 1091) := by
  show Nat.Prime 678545411
  exact p678545411

theorem check_1091 : allC 678546502 1091 P10k ds_1091 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 678546502 is 1091. -/
theorem minGB_S_1091 : minGB 678546502 = 1091 :=
  minGB_eq_of P10k P10k_complete 678546502 1091 (by norm_num) (by norm_num) prime_sub_1091 ds_1091 check_1091

def ds_1097 : List ℕ := [
    2, 19, 29, 3, 11, 3, 1861, 3, 7, 5, 3, 3,
    19, 3, 13, 193, 5, 3, 3, 3853, 3, 3, 23, 5,
    3, 151, 3, 7, 3, 11197, 3, 4817, 17, 3, 5, 3,
    3, 3, 607, 3877, 5, 3, 7, 3, 73, 3, 3, 3,
    43, 3, 7, 5, 3, 61, 167, 197, 5, 3, 3, 13,
    3, 131, 3, 107, 3, 7, 3, 3, 79, 3, 29, 5,
    3, 3, 3, 19, 5, 3, 7, 3, 5, 3, 191, 3,
    3, 7, 5, 3, 47, 3, 1381, 5, 3, 5113, 3, 619,
    5, 13513, 3, 3, 3, 2273, 823, 5, 3, 3, 431, 13,
    5, 3, 3, 3, 53, 3, 3, 479, 3, 17, 7, 5,
    3, 3, 491, 8747, 3, 29, 3, 5, 3, 3, 3, 43,
    3, 3, 331, 3, 23, 3, 41, 5, 3, 7, 3, 13,
    3, 5, 3, 229, 3, 7, 3, 3413, 3, 277, 3, 23,
    3, 5, 3, 199, 7, 17, 3, 13163, 139, 13, 3, 3,
    3, 29423, 5, 3, 7, 3, 3, 5, 3, 13, 3, 3,
    3, 101, 3]

theorem prime_sub_1097 : Nat.Prime (1168888534 - 1097) := by
  show Nat.Prime 1168887437
  exact p1168887437

theorem check_1097 : allC 1168888534 1097 P10k ds_1097 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 1168888534 is 1097. -/
theorem minGB_S_1097 : minGB 1168888534 = 1097 :=
  minGB_eq_of P10k P10k_complete 1168888534 1097 (by norm_num) (by norm_num) prime_sub_1097 ds_1097 check_1097

def ds_1283 : List ℕ := [
    2, 7, 1609, 3, 11161, 3, 5, 3, 19, 89, 3, 3,
    67, 3, 5, 23, 7, 3, 3, 331, 3, 3, 293, 487,
    3, 7, 3, 5, 3, 11, 3, 9733, 5, 3, 59, 3,
    3, 3, 5, 193, 11, 3, 23, 3, 5, 3, 3, 3,
    5, 3, 31, 127, 3, 19, 5, 1201, 7, 3, 3, 7547,
    3, 13, 3, 7, 3, 5, 3, 3, 5, 3, 7, 41,
    3, 3, 3, 37, 1861, 3, 17, 3, 31, 3, 163, 3,
    3, 11, 13, 3, 233, 3, 5, 7, 3, 619, 3, 17,
    11, 7, 3, 3, 3, 5, 7, 29, 3, 3, 5, 19,
    151, 3, 3, 3, 5, 3, 3, 11, 3, 5, 313, 47,
    3, 3, 5, 13, 3, 173, 3, 5179, 3, 3, 3, 23,
    3, 3, 13, 3, 7, 3, 5, 17, 3, 19, 3, 5,
    3, 11, 3, 5, 3, 19441, 3, 23, 3, 5, 3, 17,
    3, 97, 3, 7, 5, 13469, 3, 11, 5, 7, 3, 3,
    3, 17, 23, 3, 443, 3, 3, 19, 3, 15859, 3, 3,
    3, 29, 3, 5, 11, 7, 3, 3, 3, 7, 3, 19,
    3, 577, 5, 7, 3, 3, 5, 47, 13, 3, 3, 3,
    103, 5, 3]

theorem prime_sub_1283 : Nat.Prime (1673268292 - 1283) := by
  show Nat.Prime 1673267009
  exact p1673267009

theorem check_1283 : allC 1673268292 1283 P10k ds_1283 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 1673268292 is 1283. -/
theorem minGB_S_1283 : minGB 1673268292 = 1283 :=
  minGB_eq_of P10k P10k_complete 1673268292 1283 (by norm_num) (by norm_num) prime_sub_1283 ds_1283 check_1283

def ds_1301 : List ℕ := [
    2, 5, 7, 3, 29, 3, 16823, 3, 5, 41, 3, 3,
    613, 3, 7, 5, 67, 3, 3, 2447, 3, 3, 5, 7,
    3, 27749, 3, 1367, 3, 5, 3, 7, 53, 3, 19, 3,
    3, 3, 157, 5, 107, 3, 17, 3, 11, 3, 3, 3,
    71, 3, 5, 1873, 3, 5479, 7, 5, 5639, 3, 3, 691,
    3, 5, 3, 13, 3, 31, 3, 3, 101, 3, 5, 29,
    3, 3, 3, 5, 13, 3, 137, 3, 41161, 3, 8443, 3,
    3, 5, 151, 3, 11, 3, 7, 23, 3, 19, 3, 5,
    7, 41, 3, 3, 3, 2081, 5, 733, 3, 3, 103, 5,
    17, 3, 3, 3, 23, 3, 3, 409, 3, 619, 5, 11,
    3, 3, 7, 5, 3, 13, 3, 7, 3, 3, 3, 5,
    3, 3, 7, 3, 5, 3, 89, 18413, 3, 107, 3, 37,
    3, 10433, 3, 11, 3, 5, 3, 29, 3, 7, 3, 14929,
    3, 7, 3, 2551, 19, 5, 3, 7, 32141, 5, 3, 3,
    3, 5, 967, 3, 23, 3, 3, 37, 3, 19, 3, 3,
    3, 13, 3, 7, 5, 17, 3, 3, 3, 4153, 3, 5,
    3, 7, 11, 5, 3, 3, 113, 5, 29, 3, 3, 3,
    41, 17939, 3, 5, 19, 3, 3]

theorem prime_sub_1301 : Nat.Prime (1927528888 - 1301) := by
  show Nat.Prime 1927527587
  exact p1927527587

theorem check_1301 : allC 1927528888 1301 P10k ds_1301 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 1927528888 is 1301. -/
theorem minGB_S_1301 : minGB 1927528888 = 1301 :=
  minGB_eq_of P10k P10k_complete 1927528888 1301 (by norm_num) (by norm_num) prime_sub_1301 ds_1301 check_1301

def ds_1327 : List ℕ := [
    2, 7, 3, 38303, 3, 11, 3, 5, 3, 3, 7, 449,
    3, 89, 3, 3, 3, 13, 7121, 3, 7, 5, 3, 3,
    151, 3, 1993, 3, 5, 3, 17, 3, 3, 5, 3, 181,
    7, 673, 3, 3, 3, 149, 3, 29, 3, 5, 11, 19,
    3, 5, 3, 3, 7, 3, 3, 3, 3, 967, 11, 3,
    7, 3, 2441, 3, 2579, 3, 17, 19, 3, 5, 3, 3,
    7, 13, 5, 3, 3, 8447, 3, 5, 3, 347, 3, 17,
    5, 3, 3, 127, 3, 23, 3, 3, 59, 3, 5, 3,
    3, 3, 1759, 11, 137, 3, 3, 3, 97, 7, 3, 3,
    3, 23, 11, 71, 3, 5, 37, 3, 3929, 3, 3, 3,
    7, 11, 3, 3, 107, 3, 5, 3, 281, 293, 5, 3,
    47, 30011, 3, 5, 3, 7, 3, 3, 1307, 3, 18287, 3,
    5, 3, 31, 3, 5, 3, 23, 3, 103, 3, 19, 3,
    5, 3, 11, 3, 3, 3, 61, 3, 3, 3, 2153, 7,
    5, 3, 3, 19, 3, 47, 5, 3, 16127, 3, 29, 5,
    499, 3, 41, 3, 3, 3, 769, 7, 5, 3, 13, 3,
    163, 3, 3, 3, 11, 8941, 3, 3, 3, 13, 29, 5,
    3, 3, 5, 3, 3, 7, 37, 3, 53, 3, 3, 13597]

theorem prime_sub_1327 : Nat.Prime (2331465314 - 1327) := by
  show Nat.Prime 2331463987
  exact p2331463987

theorem check_1327 : allC 2331465314 1327 P10k ds_1327 = true := by decide +kernel

/-- Table 2 row: the least Goldbach prime of 2331465314 is 1327. -/
theorem minGB_S_1327 : minGB 2331465314 = 1327 :=
  minGB_eq_of P10k P10k_complete 2331465314 1327 (by norm_num) (by norm_num) prime_sub_1327 ds_1327 check_1327

end LeanLab.Sinisalo1993
