/-
OEIS A025018 and A025019, the records of the least Goldbach prime, rows 24 to 46: `minGB n = p` for each row, zero sorry.
Divisors and Pratt certificates found by Python, checked by the Lean kernel.
AI-written Lean code, Claude, 2026-10-17, run 20261017T1402Z-26900. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.Base

namespace LeanLab.Verifications.Top50.Records2

open LeanLab.Verifications LeanLab.Verifications.Top50
open LeanLab.Verifications.Pratt (pB)

theorem p10759093 : Nat.Prime 10759093 := by
  refine Pratt.pratt 10759093 5 [(2, 2), (3, 1), (19, 1), (47189, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p24105953 : Nat.Prime 24105953 := by
  refine Pratt.pratt 24105953 3 [(2, 5), (13, 1), (57947, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p27788881 : Nat.Prime 27788881 := by
  refine Pratt.pratt 27788881 19 [(2, 4), (3, 1), (5, 1), (7, 2), (17, 1), (139, 1)] (by norm_num)
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

theorem p37997899 : Nat.Prime 37997899 := by
  refine Pratt.pratt 37997899 3 [(2, 1), (3, 1), (41, 1), (83, 1), (1861, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
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

theorem p113631659 : Nat.Prime 113631659 := by
  refine Pratt.pratt 113631659 6 [(2, 1), (7, 1), (8116547, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p187851541 : Nat.Prime 187851541 := by
  refine Pratt.pratt 187851541 7 [(2, 2), (3, 1), (5, 1), (509, 1), (6151, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p335069411 : Nat.Prime 335069411 := by
  refine Pratt.pratt 335069411 2 [(2, 1), (5, 1), (13, 1), (37, 1), (69661, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p20995517 : Nat.Prime 20995517 := by
  refine Pratt.pratt 20995517 2 [(2, 2), (5248879, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p419910341 : Nat.Prime 419910341 := by
  refine Pratt.pratt 419910341 2 [(2, 2), (5, 1), (20995517, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p20995517

theorem p721011649 : Nat.Prime 721011649 := by
  refine Pratt.pratt 721011649 13 [(2, 6), (3, 1), (7, 1), (536467, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p1847131981 : Nat.Prime 1847131981 := by
  refine Pratt.pratt 1847131981 6 [(2, 2), (3, 1), (5, 1), (211, 1), (145903, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p7473200159 : Nat.Prime 7473200159 := by
  refine Pratt.pratt 7473200159 17 [(2, 1), (23, 1), (61, 1), (2663293, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p11001078493 : Nat.Prime 11001078493 := by
  refine Pratt.pratt 11001078493 2 [(2, 2), (3, 1), (10141, 1), (90401, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p12703941193 : Nat.Prime 12703941193 := by
  refine Pratt.pratt 12703941193 5 [(2, 3), (3, 1), (2711, 1), (195253, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p21248556799 : Nat.Prime 21248556799 := by
  refine Pratt.pratt 21248556799 3 [(2, 1), (3, 1), (7, 1), (53, 1), (347, 1), (27509, 1)] (by norm_num)
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

theorem p35884078033 : Nat.Prime 35884078033 := by
  refine Pratt.pratt 35884078033 5 [(2, 4), (3, 1), (11, 1), (89, 1), (763621, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p105963809401 : Nat.Prime 105963809401 := by
  refine Pratt.pratt 105963809401 11 [(2, 3), (3, 2), (5, 2), (19, 1), (31, 1), (89, 1), (1123, 1)] (by norm_num)
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

theorem p244885592509 : Nat.Prime 244885592509 := by
  refine Pratt.pratt 244885592509 6 [(2, 2), (3, 1), (109, 1), (131, 1), (157, 1), (9103, 1)] (by norm_num)
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

theorem p599533542901 : Nat.Prime 599533542901 := by
  refine Pratt.pratt 599533542901 6 [(2, 2), (3, 2), (5, 2), (839, 1), (793979, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p3132059290543 : Nat.Prime 3132059290543 := by
  refine Pratt.pratt 3132059290543 3 [(2, 1), (3, 3), (7, 3), (13, 1), (19, 1), (359, 1), (1907, 1)] (by norm_num)
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

theorem p42963847 : Nat.Prime 42963847 := by
  refine Pratt.pratt 42963847 3 [(2, 1), (3, 1), (127, 1), (56383, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p3620821169773 : Nat.Prime 3620821169773 := by
  refine Pratt.pratt 3620821169773 7 [(2, 2), (3, 2), (2341, 1), (42963847, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p42963847

theorem p2241579631 : Nat.Prime 2241579631 := by
  refine Pratt.pratt 2241579631 3 [(2, 1), (3, 1), (5, 1), (4421, 1), (16901, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem p4438327669381 : Nat.Prime 4438327669381 := by
  refine Pratt.pratt 4438327669381 2 [(2, 2), (3, 2), (5, 1), (11, 1), (2241579631, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p2241579631

def ds_751 : List ℕ := [
    2, 13, 3, 11, 3, 7, 3, 5, 3, 3, 1489, 137,
    3, 53, 3, 3, 3, 613, 17, 3, 11, 5, 3, 3,
    7, 3, 41, 3, 5, 3, 19, 3, 3, 5, 3, 131,
    79, 349, 3, 3, 3, 7, 3, 59, 3, 5, 13, 7,
    3, 5, 3, 3, 19, 3, 3, 3, 3, 11, 83, 3,
    23, 3, 7, 3, 29, 3, 211, 11, 3, 5, 3, 3,
    13, 17, 5, 3, 3, 67, 3, 5, 3, 23, 3, 7,
    5, 3, 3, 521, 3, 257, 3, 3, 29, 3, 5, 3,
    3, 3, 13, 1193, 59, 3, 3, 3, 43, 17, 3, 3,
    3, 7, 89, 101, 3, 5, 79, 3, 7, 3, 3, 3,
    29, 73, 3, 3, 1747, 3, 5, 3, 7, 11, 5, 3]

theorem prime_sub_751 : Nat.Prime (3807404 - 751) := by
  show Nat.Prime 3806653
  exact pB (by decide +kernel)

theorem check_751 : allC 3807404 751 P10k ds_751 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 3807404 is 751. -/
theorem minGB_751 : minGB 3807404 = 751 :=
  minGB_eq_of P10k P10k_complete 3807404 751 (by norm_num) (by norm_num) prime_sub_751 ds_751 check_751

def ds_829 : List ℕ := [
    2, 97, 3, 5, 3, 19, 3, 7, 3, 3, 397, 5,
    3, 13, 3, 3, 3, 7, 5, 3, 2887, 137, 3, 3,
    5, 3, 7, 3, 107, 3, 5, 3, 3, 29, 3, 11,
    5, 17, 3, 3, 3, 907, 3, 61, 3, 13, 37, 23,
    3, 7, 3, 3, 19, 3, 3, 3, 3, 7, 5, 3,
    11, 3, 5, 3, 7, 3, 829, 5, 3, 11, 3, 3,
    5, 197, 73, 3, 3, 5, 3, 271, 3, 419, 3, 13,
    7, 3, 3, 5, 3, 2447, 3, 3, 5, 3, 23, 3,
    3, 3, 7, 47, 5, 3, 3, 3, 17, 5, 3, 3,
    3, 349, 5, 11, 3, 1423, 487, 3, 461, 3, 3, 3,
    29, 17, 3, 3, 7, 3, 467, 3, 5, 7, 181, 3,
    107, 5, 3, 179, 3, 5, 3, 3, 11, 3, 13, 3]

theorem prime_sub_829 : Nat.Prime (10759922 - 829) := by
  show Nat.Prime 10759093
  exact p10759093

theorem check_829 : allC 10759922 829 P10k ds_829 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 10759922 is 829. -/
theorem minGB_829 : minGB 10759922 = 829 :=
  minGB_eq_of P10k P10k_complete 10759922 829 (by norm_num) (by norm_num) prime_sub_829 ds_829 check_829

def ds_929 : List ℕ := [
    2, 157, 19, 3, 31, 3, 5, 3, 7, 1747, 3, 3,
    11, 3, 5, 23, 13, 3, 3, 41, 3, 3, 17, 251,
    3, 101, 3, 5, 3, 83, 3, 59, 5, 3, 7, 3,
    3, 3, 5, 11, 43, 3, 7, 3, 5, 3, 3, 3,
    5, 3, 7, 11, 3, 139, 5, 3391, 79, 3, 3, 229,
    3, 13, 3, 73, 3, 5, 3, 3, 5, 3, 61, 7,
    3, 3, 3, 31, 17, 3, 7, 3, 997, 3, 89, 3,
    3, 7, 13, 3, 19, 3, 5, 113, 3, 17, 3, 11,
    3343, 53, 3, 3, 3, 5, 41, 7, 3, 3, 5, 17,
    167, 3, 3, 3, 5, 3, 3, 3779, 3, 5, 7, 103,
    3, 3, 5, 13, 3, 11, 3, 29, 3, 3, 3, 23,
    3, 3, 13, 3, 137, 3, 5, 41, 3, 7, 3, 5,
    3, 13, 3, 5, 3, 7, 3, 23, 3, 5, 3, 47,
    3]

theorem prime_sub_929 : Nat.Prime (24106882 - 929) := by
  show Nat.Prime 24105953
  exact p24105953

theorem check_929 : allC 24106882 929 P10k ds_929 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 24106882 is 929. -/
theorem minGB_929 : minGB 24106882 = 929 :=
  minGB_eq_of P10k P10k_complete 24106882 929 (by norm_num) (by norm_num) prime_sub_929 ds_929 check_929

def ds_997 : List ℕ := [
    2, 5, 3, 631, 3, 5, 3, 29, 3, 3, 101, 41,
    3, 5, 3, 3, 3, 11, 7, 3, 5, 19, 3, 3,
    17, 3, 5, 3, 7, 3, 11, 3, 3, 43, 3, 7,
    653, 5, 3, 3, 3, 13, 3, 5, 3, 17, 257, 5,
    3, 53, 3, 3, 1787, 3, 3, 3, 3, 367, 7, 3,
    5, 3, 19, 3, 5, 3, 31, 13, 3, 1747, 3, 3,
    29, 5, 877, 3, 3, 43, 3, 241, 3, 19, 3, 5,
    2777, 3, 3, 11, 3, 5, 3, 3, 7, 3, 229, 3,
    3, 3, 5, 29, 37, 3, 3, 3, 7, 167, 3, 3,
    3, 79, 17, 5, 3, 2713, 239, 3, 5, 3, 3, 3,
    137, 5, 3, 3, 71, 3, 17, 3, 13, 5, 7, 3,
    491, 67, 3, 37, 3, 11, 3, 3, 17, 3, 5, 3,
    971, 3, 5, 3, 139, 3, 19, 3, 5, 3, 7, 3,
    11, 3, 59, 3, 3, 3, 211, 3, 3, 3, 7]

theorem prime_sub_997 : Nat.Prime (27789878 - 997) := by
  show Nat.Prime 27788881
  exact p27788881

theorem check_997 : allC 27789878 997 P10k ds_997 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 27789878 is 997. -/
theorem minGB_997 : minGB 27789878 = 997 :=
  minGB_eq_of P10k P10k_complete 27789878 997 (by norm_num) (by norm_num) prime_sub_997 ds_997 check_997

def ds_1039 : List ℕ := [
    2, 5, 3, 173, 3, 5, 3, 7, 3, 3, 661, 31,
    3, 5, 3, 3, 3, 7, 3881, 3, 5, 17, 3, 3,
    19, 3, 5, 3, 11, 3, 83, 3, 3, 43, 3, 29,
    127, 5, 3, 3, 3, 17, 3, 5, 3, 197, 13, 5,
    3, 7, 3, 3, 11, 3, 3, 3, 3, 7, 997, 3,
    5, 3, 11, 3, 5, 3, 47, 3187, 3, 107, 3, 3,
    13, 5, 563, 3, 3, 7, 3, 31, 3, 4507, 3, 5,
    7, 3, 3, 3137, 3, 5, 3, 3, 17, 3, 29, 3,
    3, 3, 5, 113, 1217, 3, 3, 3, 11, 773, 3, 3,
    3, 13, 7, 5, 3, 3461, 1301, 3, 5, 3, 3, 3,
    23, 5, 3, 3, 7, 3, 241, 3, 227, 5, 229, 3,
    4451, 13, 3, 11, 3, 1499, 3, 3, 283, 3, 5, 3,
    727, 3, 5, 3, 7, 3, 397, 3, 5, 3, 613, 3,
    127, 3, 23, 3, 3, 3, 11, 3, 3, 3, 13, 17,
    19, 3, 3, 29, 3, 5]

theorem prime_sub_1039 : Nat.Prime (37998938 - 1039) := by
  show Nat.Prime 37997899
  exact p37997899

theorem check_1039 : allC 37998938 1039 P10k ds_1039 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 37998938 is 1039. -/
theorem minGB_1039 : minGB 37998938 = 1039 :=
  minGB_eq_of P10k P10k_complete 37998938 1039 (by norm_num) (by norm_num) prime_sub_1039 ds_1039 check_1039

def ds_1093 : List ℕ := [
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

theorem prime_sub_1093 : Nat.Prime (60119912 - 1093) := by
  show Nat.Prime 60118819
  exact p60118819

theorem check_1093 : allC 60119912 1093 P10k ds_1093 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 60119912 is 1093. -/
theorem minGB_1093 : minGB 60119912 = 1093 :=
  minGB_eq_of P10k P10k_complete 60119912 1093 (by norm_num) (by norm_num) prime_sub_1093 ds_1093 check_1093

def ds_1163 : List ℕ := [
    2, 3797, 29, 3, 17, 3, 5, 3, 7, 47, 3, 3,
    199, 3, 5, 7207, 31, 3, 3, 7253, 3, 3, 11, 523,
    3, 1129, 3, 5, 3, 17, 3, 61, 5, 3, 7, 3,
    3, 3, 5, 13, 29, 3, 7, 3, 5, 3, 3, 3,
    5, 3, 7, 53, 3, 13, 5, 19, 1523, 3, 3, 11,
    3, 1291, 3, 47, 3, 5, 3, 3, 5, 3, 29, 7,
    3, 3, 3, 37, 823, 3, 7, 3, 17, 3, 31, 3,
    3, 7, 101, 3, 41, 3, 5, 11, 3, 19, 3, 229,
    1039, 17, 3, 3, 3, 5, 13, 7, 3, 3, 5, 47,
    241, 3, 3, 3, 5, 3, 3, 13, 3, 5, 7, 71,
    3, 3, 5, 293, 3, 23, 3, 13, 3, 3, 3, 11,
    3, 3, 409, 3, 3361, 3, 5, 11, 3, 7, 3, 5,
    3, 23, 3, 5, 3, 7, 3, 79, 3, 5, 3, 97,
    3, 17, 3, 11, 5, 13, 3, 983, 5, 373, 3, 3,
    3, 2207, 3701, 3, 7, 3, 3, 29, 3, 19, 3, 3,
    3, 83, 3, 5, 1087, 13, 3, 3, 3, 43, 3]

theorem prime_sub_1163 : Nat.Prime (113632822 - 1163) := by
  show Nat.Prime 113631659
  exact p113631659

theorem check_1163 : allC 113632822 1163 P10k ds_1163 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 113632822 is 1163. -/
theorem minGB_1163 : minGB 113632822 = 1163 :=
  minGB_eq_of P10k P10k_complete 113632822 1163 (by norm_num) (by norm_num) prime_sub_1163 ds_1163 check_1163

def ds_1321 : List ℕ := [
    2, 5431, 3, 5, 3, 1907, 3, 47, 3, 3, 8741, 5,
    3, 7, 3, 3, 3, 139, 5, 3, 167, 479, 3, 3,
    5, 3, 13099, 3, 11, 3, 5, 3, 3, 53, 3, 4421,
    5, 197, 3, 3, 3, 43, 3, 17, 3, 37, 7, 13,
    3, 29, 3, 3, 11, 3, 3, 3, 3, 31, 5, 3,
    73, 3, 5, 3, 10259, 3, 6091, 5, 3, 3323, 3, 3,
    5, 11, 7, 3, 3, 5, 3, 109, 3, 7, 3, 461,
    11, 3, 3, 5, 3, 7, 3, 3, 5, 3, 17, 3,
    3, 3, 23, 967, 5, 3, 3, 3, 11, 5, 3, 3,
    3, 17, 5, 13, 3, 3023, 7, 3, 31, 3, 3, 3,
    23, 7, 3, 3, 13, 3, 281, 3, 5, 191, 61, 3,
    29, 5, 3, 11, 3, 5, 3, 3, 271, 3, 2113, 3,
    31, 3, 5591, 3, 151, 3, 5, 3, 7, 3, 5, 3,
    5119, 3, 5, 3, 3, 3, 5, 3, 3, 3, 71, 5,
    7, 3, 3, 19, 3, 11, 211, 3, 7, 3, 109, 1627,
    5, 3, 7, 3, 3, 3, 5, 6089, 1013, 3, 41, 3,
    4919, 3, 3, 3, 31, 17, 3, 3, 3, 11, 5, 19,
    3, 3, 739, 3, 3, 1709, 5, 3, 7, 3, 3]

theorem prime_sub_1321 : Nat.Prime (187852862 - 1321) := by
  show Nat.Prime 187851541
  exact p187851541

theorem check_1321 : allC 187852862 1321 P10k ds_1321 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 187852862 is 1321. -/
theorem minGB_1321 : minGB 187852862 = 1321 :=
  minGB_eq_of P10k P10k_complete 187852862 1321 (by norm_num) (by norm_num) prime_sub_1321 ds_1321 check_1321

def ds_1427 : List ℕ := [
    2, 5, 17, 3, 7, 3, 107, 3, 5, 2011, 3, 3,
    71, 3, 11, 5, 37, 3, 3, 1163, 3, 3, 5, 13,
    3, 41, 3, 17, 3, 5, 3, 6823, 7, 3, 97, 3,
    3, 3, 13, 5, 7, 3, 23, 3, 12049, 3, 3, 3,
    29, 3, 5, 31, 3, 5099, 193, 5, 313, 3, 3, 37,
    3, 5, 3, 11, 3, 79, 3, 3, 7, 3, 5, 1249,
    3, 3, 3, 5, 7, 3, 13, 3, 83, 3, 7, 3,
    3, 5, 3257, 3, 19, 3, 23, 13, 3, 3733, 3, 5,
    11, 6047, 3, 3, 3, 7, 5, 5653, 3, 3, 109, 5,
    7, 3, 3, 3, 17, 3, 3, 7, 3, 47, 5, 107,
    3, 3, 14411, 5, 3, 89, 3, 17, 3, 3, 3, 5,
    3, 3, 233, 3, 5, 3, 31, 7, 3, 17, 3, 61,
    3, 11, 3, 5827, 3, 5, 3, 23, 3, 317, 3, 73,
    3, 47, 3, 269, 13, 5, 3, 11, 7, 5, 3, 3,
    3, 5, 7, 3, 19, 3, 3, 11437, 3, 7, 3, 3,
    3, 67, 3, 29, 5, 1009, 3, 3, 3, 173, 3, 5,
    3, 13, 7, 5, 3, 3, 101, 5, 7, 3, 3, 3,
    13, 127, 3, 5, 271, 3, 3, 11, 3, 137, 71, 3,
    3, 211, 11, 5, 3, 3, 389, 3]

theorem prime_sub_1427 : Nat.Prime (335070838 - 1427) := by
  show Nat.Prime 335069411
  exact p335069411

theorem check_1427 : allC 335070838 1427 P10k ds_1427 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 335070838 is 1427. -/
theorem minGB_1427 : minGB 335070838 = 1427 :=
  minGB_eq_of P10k P10k_complete 335070838 1427 (by norm_num) (by norm_num) prime_sub_1427 ds_1427 check_1427

def ds_1583 : List ℕ := [
    2, 11, 7, 3, 19, 3, 4271, 3, 233, 5, 3, 3,
    17, 3, 7, 6673, 5, 3, 3, 37, 3, 3, 73, 5,
    3, 151, 3, 13, 3, 11, 3, 7, 1283, 3, 5, 3,
    3, 3, 541, 7, 5, 3, 211, 3, 43, 3, 3, 3,
    12497, 3, 83, 5, 3, 59, 7, 13, 5, 3, 3, 1823,
    3, 37, 3, 11, 3, 197, 3, 3, 17, 3, 19, 5,
    3, 3, 3, 7, 5, 3, 31, 3, 5, 3, 181, 3,
    3, 11, 5, 3, 41, 3, 7, 5, 3, 1511, 3, 53,
    5, 73, 3, 3, 3, 487, 1087, 5, 3, 3, 31, 7,
    5, 3, 3, 3, 79, 3, 3, 11, 3, 113, 13, 5,
    3, 3, 7, 2909, 3, 307, 3, 5, 3, 3, 3, 6883,
    3, 3, 7, 3, 11, 3, 7457, 5, 3, 53, 3, 29,
    3, 5, 3, 17, 3, 9629, 3, 67, 3, 7, 3, 12073,
    3, 5, 3, 163, 23, 41, 3, 7, 523, 3079, 3, 3,
    3, 7, 5, 3, 409, 3, 3, 5, 3, 17, 3, 3,
    3, 79, 3, 7, 11, 5, 3, 3, 3, 19, 3, 17,
    3, 7, 47, 12889, 3, 3, 1607, 7, 5, 3, 3, 3,
    5, 13, 3, 61, 5, 3, 3, 11, 3, 7, 5, 3,
    3, 23, 11, 179, 3, 3, 5, 3, 199, 3, 7, 5,
    3, 157, 3, 3, 3, 15139, 3, 43, 3, 19, 5, 13,
    29, 3, 3, 3, 15737, 5, 3, 17, 3]

theorem prime_sub_1583 : Nat.Prime (419911924 - 1583) := by
  show Nat.Prime 419910341
  exact p419910341

theorem check_1583 : allC 419911924 1583 P10k ds_1583 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 419911924 is 1583. -/
theorem minGB_1583 : minGB 419911924 = 1583 :=
  minGB_eq_of P10k P10k_complete 419911924 1583 (by norm_num) (by norm_num) prime_sub_1583 ds_1583 check_1583

def ds_1789 : List ℕ := [
    2, 5, 3, 53, 3, 5, 3, 7, 3, 3, 23, 17,
    3, 5, 3, 3, 3, 7, 13, 3, 5, 11, 3, 3,
    29, 3, 5, 3, 79, 3, 19, 3, 3, 17, 3, 103,
    83, 5, 3, 3, 3, 2437, 3, 5, 3, 4337, 11, 5,
    3, 7, 3, 3, 17, 3, 3, 3, 3, 7, 11, 3,
    5, 3, 23, 3, 5, 3, 61, 1373, 3, 601, 3, 3,
    151, 5, 13, 3, 3, 7, 3, 11, 3, 823, 3, 5,
    7, 3, 3, 13, 3, 5, 3, 3, 991, 3, 12923, 3,
    3, 3, 5, 11, 17, 3, 3, 3, 1217, 5569, 3, 3,
    3, 401, 7, 5, 3, 29, 9391, 3, 5, 3, 3, 3,
    43, 5, 3, 3, 7, 3, 257, 3, 197, 5, 11, 3,
    17, 193, 3, 13, 3, 2113, 3, 3, 19, 3, 5, 3,
    157, 3, 5, 3, 7, 3, 281, 3, 5, 3, 211, 3,
    43, 3, 11, 3, 3, 3, 29, 3, 3, 3, 677, 23,
    41, 3, 3, 5939, 3, 5, 19, 3, 491, 3, 5, 7,
    809, 3, 5, 3, 3, 3, 139, 5, 251, 3, 5, 3,
    269, 3, 3, 3, 11, 5, 3, 3, 3, 113, 7, 11447,
    3, 3, 7, 3, 3, 127, 1129, 3, 5, 3, 3, 7,
    14071, 3, 3, 3, 19, 11, 3, 5, 3, 61, 3, 3,
    7, 3, 5, 167, 13, 3, 5, 3, 7, 3, 3, 3,
    3, 7, 5, 13, 3, 3, 17, 3, 37, 3, 11, 3,
    3, 19, 3, 3, 131, 13, 3, 7, 5, 3, 17, 5,
    3, 7, 3, 3, 5, 3, 7, 41, 5, 26717, 15959, 5,
    3]

theorem prime_sub_1789 : Nat.Prime (721013438 - 1789) := by
  show Nat.Prime 721011649
  exact p721011649

theorem check_1789 : allC 721013438 1789 P10k ds_1789 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 721013438 is 1789. -/
theorem minGB_1789 : minGB 721013438 = 1789 :=
  minGB_eq_of P10k P10k_complete 721013438 1789 (by norm_num) (by norm_num) prime_sub_1789 ds_1789 check_1789

def ds_1861 : List ℕ := [
    2, 79, 3, 5, 3, 233, 3, 293, 3, 3, 19, 5,
    3, 7, 3, 3, 3, 277, 5, 3, 13, 41, 3, 3,
    5, 3, 11, 3, 337, 3, 5, 3, 3, 23, 3, 13,
    5, 89, 3, 3, 3, 197, 3, 7817, 3, 1063, 7, 61,
    3, 13, 3, 3, 6827, 3, 3, 3, 3, 409, 5, 3,
    16603, 3, 5, 3, 34297, 3, 29, 5, 3, 21067, 3, 3,
    5, 19, 7, 3, 3, 5, 3, 661, 3, 7, 3, 11,
    107, 3, 3, 5, 3, 7, 3, 3, 5, 3, 11, 3,
    3, 3, 1597, 13, 5, 3, 3, 3, 41, 5, 3, 3,
    3, 19, 5, 47, 3, 13, 7, 3, 503, 3, 3, 3,
    17, 7, 3, 3, 23, 3, 1289, 3, 5, 31, 157, 3,
    2971, 5, 3, 97, 3, 5, 3, 3, 7013, 3, 151, 3,
    11, 3, 13, 3, 43, 3, 5, 3, 7, 3, 5, 3,
    31, 3, 5, 3, 3, 3, 5, 3, 3, 3, 4691, 5,
    7, 3, 3, 431, 3, 977, 11411, 3, 7, 3, 41, 17,
    5, 3, 7, 3, 3, 3, 5, 15149, 83, 3, 317, 3,
    17, 3, 3, 3, 29, 12539, 3, 3, 3, 37, 5, 647,
    3, 3, 311, 3, 3, 11, 5, 3, 7, 3, 3, 13,
    5, 3, 3, 3, 23, 13, 3, 11, 3, 7, 3, 3,
    5, 3, 37, 47, 7, 3, 73, 3, 11, 3, 3, 3,
    3, 4003, 28403, 29, 3, 3, 5, 3, 17, 3, 5, 3,
    3, 757, 3, 3, 11, 5, 3, 5, 31, 3, 3547, 3823,
    3, 10303, 3, 3, 7, 3, 19, 5, 11, 18523, 5, 17,
    3, 13, 41, 3, 3, 9209, 3]

theorem prime_sub_1861 : Nat.Prime (1847133842 - 1861) := by
  show Nat.Prime 1847131981
  exact p1847131981

theorem check_1861 : allC 1847133842 1861 P10k ds_1861 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 1847133842 is 1861. -/
theorem minGB_1861 : minGB 1847133842 = 1861 :=
  minGB_eq_of P10k P10k_complete 1847133842 1861 (by norm_num) (by norm_num) prime_sub_1861 ds_1861 check_1861

def ds_1877 : List ℕ := [
    2, 11, 22777, 3, 5, 3, 59, 3, 2083, 10313, 3, 3,
    5, 3, 11, 13, 103, 3, 3, 5, 3, 3, 7, 37,
    3, 5, 3, 23, 3, 11, 3, 5, 31, 3, 17, 3,
    3, 3, 7, 2833, 11, 3, 5, 3, 307, 3, 3, 3,
    19, 3, 5839, 101, 3, 5, 83437, 71, 6361, 3, 3, 5,
    3, 7, 3, 5, 3, 29, 3, 3, 653, 3, 17, 47,
    3, 3, 3, 23, 109, 3, 5, 3, 7, 3, 5, 3,
    3, 11, 211, 3, 5, 3, 41, 311, 3, 5, 3, 7,
    11, 5, 3, 3, 3, 17, 79, 19, 3, 3, 7, 193,
    13, 3, 3, 3, 191, 3, 3, 5, 3, 461, 43, 17,
    3, 3, 13, 19, 3, 5, 3, 61, 3, 3, 3, 607,
    3, 3, 5, 3, 11, 3, 7, 83, 3, 5, 3, 1759,
    3, 7, 3, 491, 3, 17, 3, 5, 3, 39163, 3, 5,
    3, 107, 3, 5, 49639, 51977, 3, 5, 37, 241, 3, 3,
    3, 29, 163, 3, 5, 3, 3, 7, 3, 5, 3, 3,
    3, 5, 3, 149, 11, 4421, 3, 3, 3, 5, 3, 113,
    3, 5, 29, 373, 3, 3, 7, 13, 137, 3, 3, 3,
    7, 233, 3, 223, 55987, 3, 3, 5, 3, 83, 577, 3,
    3, 5, 11, 17, 3, 3, 29437, 3, 7, 3, 11, 31,
    3, 5, 3, 3, 3, 5, 3, 23, 3, 173, 11, 5,
    5279, 3, 3, 3, 7, 919, 3, 5, 3, 337, 3, 5,
    199, 3, 13, 179, 3, 3, 7, 3, 3, 839, 3, 3,
    11, 3, 19, 5, 3, 1733, 3, 3, 3, 3, 3, 3,
    59, 3, 3, 5, 19, 3, 7, 3, 3, 5, 3]

theorem prime_sub_1877 : Nat.Prime (7473202036 - 1877) := by
  show Nat.Prime 7473200159
  exact p7473200159

theorem check_1877 : allC 7473202036 1877 P10k ds_1877 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 7473202036 is 1877. -/
theorem minGB_1877 : minGB 7473202036 = 1877 :=
  minGB_eq_of P10k P10k_complete 7473202036 1877 (by norm_num) (by norm_num) prime_sub_1877 ds_1877 check_1877

def ds_1879 : List ℕ := [
    2, 491, 3, 5, 3, 14951, 3, 41, 3, 3, 17, 5,
    3, 31, 3, 3, 3, 13, 5, 3, 11, 7, 3, 3,
    5, 3, 181, 3, 379, 3, 5, 3, 3, 11, 3, 269,
    5, 7, 3, 3, 3, 317, 3, 45613, 3, 313, 19, 353,
    3, 31, 3, 3, 107, 3, 3, 3, 3, 11, 5, 3,
    6793, 3, 5, 3, 307, 3, 7, 5, 3, 29, 3, 3,
    5, 7, 58763, 3, 3, 5, 3, 8467, 3, 109, 3, 937,
    17, 3, 3, 5, 3, 2039, 3, 3, 5, 3, 7, 3,
    3, 3, 29, 7, 5, 3, 3, 3, 139, 5, 3, 3,
    3, 11, 5, 9041, 3, 251, 2927, 3, 17, 3, 3, 3,
    27773, 23, 3, 3, 101, 3, 7, 3, 5, 11, 73, 3,
    7, 5, 3, 373, 3, 5, 3, 3, 23, 3, 257, 3,
    84401, 3, 14563, 3, 42641, 3, 5, 3, 107, 3, 5, 3,
    7, 3, 5, 3, 3, 3, 5, 3, 3, 3, 1433, 5,
    19, 3, 3, 79, 3, 10427, 97, 3, 17, 3, 11, 149,
    5, 3, 37, 3, 3, 3, 5, 19, 7, 3, 13, 3,
    7, 3, 3, 3, 59, 7, 3, 3, 3, 13, 5, 41,
    3, 3, 131, 3, 3, 17977, 5, 3, 41981, 3, 3, 4817,
    5, 3, 3, 3, 7, 6373, 3, 7, 3, 9437, 3, 3,
    5, 3, 38317, 11, 1193, 3, 1409, 3, 71, 3, 3, 3,
    3, 31, 13, 7, 3, 3, 5, 3, 19, 3, 5, 3,
    3, 43, 3, 3, 13, 5, 3, 5, 17, 3, 887, 19,
    3, 13, 3, 3, 11, 3, 29, 5, 15053, 7, 5, 241,
    3, 11, 7, 3, 3, 523, 3, 401, 5, 3, 293, 3]

theorem prime_sub_1879 : Nat.Prime (11001080372 - 1879) := by
  show Nat.Prime 11001078493
  exact p11001078493

theorem check_1879 : allC 11001080372 1879 P10k ds_1879 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 11001080372 is 1879. -/
theorem minGB_1879 : minGB 11001080372 = 1879 :=
  minGB_eq_of P10k P10k_complete 11001080372 1879 (by norm_num) (by norm_num) prime_sub_1879 ds_1879 check_1879

def ds_2029 : List ℕ := [
    2, 11, 3, 5, 3, 17, 3, 7, 3, 3, 19, 5,
    3, 509, 3, 3, 3, 7, 5, 3, 271, 61, 3, 3,
    5, 3, 7, 3, 233, 3, 5, 3, 3, 13, 3, 59,
    5, 103, 3, 3, 3, 73, 3, 29, 3, 151, 3541, 11,
    3, 7, 3, 3, 23, 3, 3, 3, 3, 7, 5, 3,
    389, 3, 5, 3, 7, 3, 199, 5, 3, 1471, 3, 3,
    5, 13, 23, 3, 3, 5, 3, 4597, 3, 11, 3, 149,
    7, 3, 3, 5, 3, 107, 3, 3, 5, 3, 5167, 3,
    3, 3, 7, 29, 5, 3, 3, 3, 3217, 5, 3, 3,
    3, 19, 5, 857, 3, 11, 131, 3, 41947, 3, 3, 3,
    67, 5791, 3, 3, 7, 3, 839, 3, 5, 7, 523, 3,
    11, 5, 3, 443, 3, 5, 3, 3, 61, 3, 229, 3,
    17, 3, 349, 3, 7, 3, 5, 3, 11, 3, 5, 3,
    13, 3, 5, 3, 3, 3, 5, 3, 3, 3, 43, 5,
    4919, 3, 3, 37957, 3, 17, 9419, 3, 113, 3, 29, 7,
    5, 3, 19949, 3, 3, 3, 5, 2297, 787, 3, 7, 3,
    19, 3, 3, 3, 14207, 11, 3, 3, 3, 13, 5, 43,
    3, 3, 7, 3, 3, 1733, 5, 3, 53569, 3, 3, 7,
    5, 3, 3, 3, 1721, 19, 3, 41, 3, 431, 3, 3,
    5, 3, 617, 31, 47, 3, 23, 3, 7, 3, 3, 3,
    3, 7, 11, 8447, 3, 3, 5, 3, 7127, 3, 5, 3,
    3, 11, 3, 3, 13, 5, 3, 5, 353, 3, 41, 50599,
    3, 7, 3, 3, 101, 3, 7, 5, 47, 23, 5, 7,
    3, 163, 10613, 3, 3, 31, 3, 821, 5, 3, 11, 3,
    613, 3, 3, 3, 3, 3, 13, 3, 7, 3, 3, 5,
    7, 3, 1613, 3, 13, 5, 3]

theorem prime_sub_2029 : Nat.Prime (12703943222 - 2029) := by
  show Nat.Prime 12703941193
  exact p12703941193

theorem check_2029 : allC 12703943222 2029 P10k ds_2029 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 12703943222 is 2029. -/
theorem minGB_2029 : minGB 12703943222 = 2029 :=
  minGB_eq_of P10k P10k_complete 12703943222 2029 (by norm_num) (by norm_num) prime_sub_2029 ds_2029 check_2029

def ds_2089 : List ℕ := [
    2, 5, 3, 11, 3, 5, 3, 419, 3, 3, 19, 13,
    3, 5, 3, 3, 3, 719, 7, 3, 5, 23, 3, 3,
    17, 3, 5, 3, 7, 3, 103, 3, 3, 11, 3, 7,
    73, 5, 3, 3, 3, 1907, 3, 5, 3, 17, 33203, 5,
    3, 13463, 3, 3, 61, 3, 3, 3, 3, 11, 7, 3,
    5, 3, 151, 3, 5, 3, 1933, 11, 3, 13, 3, 3,
    563, 5, 157, 3, 3, 197, 3, 137, 3, 101, 3, 5,
    2203, 3, 3, 37, 3, 5, 3, 3, 7, 3, 47, 3,
    3, 3, 5, 79, 83, 3, 3, 3, 7, 89759, 3, 3,
    3, 11, 17, 5, 3, 857, 23, 3, 5, 3, 3, 3,
    13, 5, 3, 3, 41, 3, 17, 3, 3469, 5, 7, 3,
    211, 241, 3, 23, 3, 659, 3, 3, 17, 3, 5, 3,
    19, 3, 5, 3, 91813, 3, 22531, 3, 5, 3, 7, 3,
    547, 3, 41, 3, 3, 3, 93979, 3, 3, 3, 7, 11,
    149, 3, 3, 317, 3, 5, 89, 3, 13, 3, 5, 31,
    43, 3, 5, 3, 3, 3, 7, 5, 11, 3, 5, 3,
    19, 3, 3, 3, 7, 5, 3, 3, 3, 107, 811, 135077,
    3, 3, 1097, 3, 3, 1193, 143977, 3, 5, 3, 3, 17,
    7, 3, 3, 3, 3559, 19, 3, 5, 3, 41, 3, 3,
    467, 3, 5, 11, 73, 3, 5, 3, 79, 3, 3, 3,
    3, 251, 5, 59447, 3, 3, 37, 3, 7, 3, 13, 3,
    3, 16267, 3, 3, 7, 17, 3, 11, 5, 3, 1093, 5,
    3, 293, 3, 3, 5, 3, 19, 7, 5, 11903, 229, 5,
    3, 7, 307, 3, 3, 7, 3, 29, 71, 3, 5, 3,
    42179, 3, 3, 3, 3, 3, 5, 3, 1973, 3, 3, 11,
    5, 3, 7, 3, 23, 211, 3, 233, 3, 5, 3, 3,
    3, 5, 3]

theorem prime_sub_2089 : Nat.Prime (21248558888 - 2089) := by
  show Nat.Prime 21248556799
  exact p21248556799

theorem check_2089 : allC 21248558888 2089 P10k ds_2089 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 21248558888 is 2089. -/
theorem minGB_2089 : minGB 21248558888 = 2089 :=
  minGB_eq_of P10k P10k_complete 21248558888 2089 (by norm_num) (by norm_num) prime_sub_2089 ds_2089 check_2089

def ds_2803 : List ℕ := [
    2, 887, 3, 101, 3, 73, 3, 13, 3, 3, 5, 7,
    3, 11, 3, 3, 3, 5, 97, 3, 31991, 7, 3, 3,
    13, 3, 2797, 3, 11, 3, 17, 3, 3, 29, 3, 5,
    1129, 7, 3, 3, 3, 5, 3, 83, 3, 19, 5, 89,
    3, 17, 3, 3, 5, 3, 3, 3, 3, 5, 7621, 3,
    5303, 3, 11, 3, 19, 3, 5, 23, 3, 337, 3, 3,
    3253, 7, 43, 3, 3, 2087, 3, 13, 3, 5, 3, 17,
    11, 3, 3, 7, 3, 27179, 3, 3, 13, 3, 7, 3,
    3, 3, 5741, 5, 139, 3, 3, 3, 5, 37, 3, 3,
    3, 5, 41, 23, 3, 173, 5, 3, 13, 3, 3, 3,
    5, 31, 3, 3, 5, 3, 7, 3, 71, 113, 17, 3,
    5, 89, 3, 11, 3, 937, 3, 3, 5, 3, 3163, 3,
    769, 3, 41, 3, 31, 3, 7, 3, 19, 3, 2417, 3,
    7, 3, 149, 3, 3, 3, 11, 3, 3, 3, 5, 19,
    29, 3, 3, 5, 3, 11, 653, 3, 5, 3, 47, 3617,
    7, 3, 127, 3, 3, 3, 59, 13841, 7, 3, 43, 3,
    5, 3, 3, 3, 5, 7, 3, 3, 3, 5, 3169, 17,
    3, 3, 587, 3, 3, 5, 7, 3, 23, 3, 3, 5,
    73, 3, 3, 3, 5, 557, 3, 7, 3, 11, 3, 3,
    10631, 3, 17, 811, 5, 3, 53, 3, 541, 3, 3, 3,
    3, 5, 463, 7, 3, 3, 19, 3, 13, 3, 131, 3,
    3, 66851, 3, 3, 5, 11, 3, 13, 61, 3, 43, 11,
    3, 117101, 3, 3, 16831, 3, 5, 761, 28181, 7, 233, 1567,
    3, 31, 5, 3, 3, 5, 3, 5, 191, 3, 739, 3,
    29, 3, 3, 3, 3, 3, 5059, 3, 5, 3, 3, 163,
    23, 3, 881, 3, 5, 43913, 3, 61, 3, 7, 3, 3,
    3, 41, 3, 11, 3, 3, 467, 3, 5, 7, 3, 1511,
    3, 5, 7, 13, 3, 3, 5, 3, 79, 3, 5, 3,
    17, 3, 5, 11, 7433, 3, 3, 5, 3, 3, 5, 7,
    3, 3, 5, 691, 3, 131, 7, 3, 3, 3, 3, 3,
    13, 3, 3, 3, 3301, 7, 3, 1483, 5, 3, 3457, 3,
    3, 5, 7, 3, 3, 13, 3, 11, 3, 3, 461, 3,
    122149, 3, 5, 17, 7, 3, 2357, 3, 3, 19, 3, 79,
    31, 3, 5, 3, 11, 3, 7, 3, 3, 5, 37, 3]

theorem prime_sub_2803 : Nat.Prime (35884080836 - 2803) := by
  show Nat.Prime 35884078033
  exact p35884078033

theorem check_2803 : allC 35884080836 2803 P10k ds_2803 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 35884080836 is 2803. -/
theorem minGB_2803 : minGB 35884080836 = 2803 :=
  minGB_eq_of P10k P10k_complete 35884080836 2803 (by norm_num) (by norm_num) prime_sub_2803 ds_2803 check_2803

def ds_3061 : List ℕ := [
    2, 19, 3, 5, 3, 11, 3, 29, 3, 3, 1063, 5,
    3, 61, 3, 3, 3, 43, 5, 3, 41, 11, 3, 3,
    5, 3, 192617, 3, 7, 3, 5, 3, 3, 10391, 3, 7,
    5, 347, 3, 3, 3, 149119, 3, 7, 3, 19501, 11, 99929,
    3, 23, 3, 3, 31, 3, 3, 3, 3, 17, 5, 3,
    8011, 3, 5, 3, 13, 3, 163, 5, 3, 3037, 3, 3,
    5, 17, 79, 3, 3, 5, 3, 11, 3, 19, 3, 17053,
    157, 3, 3, 5, 3, 823, 3, 3, 5, 3, 65957, 3,
    3, 3, 83, 11, 5, 3, 3, 3, 7, 5, 3, 3,
    3, 733, 5, 7, 3, 58657, 251, 3, 23, 3, 3, 3,
    229, 11, 3, 3, 3851, 3, 2767, 3, 5, 131, 7, 3,
    37, 5, 3, 197, 3, 5, 3, 3, 41, 3, 7, 3,
    1609, 3, 67, 3, 13, 3, 5, 3, 17, 3, 5, 3,
    23, 3, 5, 3, 3, 3, 5, 3, 3, 3, 7, 5,
    73, 3, 3, 53, 3, 7, 191, 3, 839, 3, 29, 11,
    5, 3, 13, 3, 3, 3, 5, 245269, 8263, 3, 117319, 3,
    13, 3, 3, 3, 7, 284083, 3, 3, 3, 3119, 5, 13,
    3, 3, 797, 3, 3, 17, 5, 3, 41, 3, 3, 59,
    5, 3, 3, 3, 157, 11, 3, 197273, 3, 113, 3, 3,
    5, 3, 7, 461, 23, 3, 13, 3, 421, 3, 3, 3,
    3, 11, 31, 41, 3, 3, 5, 3, 7, 3, 5, 3,
    3, 23, 3, 3, 7, 5, 3, 5, 7, 3, 3253, 71,
    3, 17, 3, 3, 199, 3, 3299, 5, 2389, 29, 5, 383,
    3, 7, 17, 3, 3, 7, 3, 11, 5, 3, 7, 3,
    541, 3, 3, 3, 3, 3, 29, 3, 13, 3, 3, 5,
    11, 3, 7, 3, 11821, 5, 3, 13, 3, 787, 3, 3,
    3, 7, 3, 13037, 3, 3, 6719, 3, 19, 5, 3, 209267,
    3, 23, 211, 88093, 3, 3, 947, 3, 61, 3, 7, 3,
    309359, 3, 29, 5, 7, 3, 3, 17, 3, 3, 13, 5,
    3, 3, 139, 5, 3, 43, 11, 3, 3, 3, 3, 3,
    5, 3, 3, 3, 5, 19, 3, 7, 11, 3, 1459, 3,
    3, 1553, 5, 3, 3, 11471, 3, 5, 3, 3, 5, 3,
    31, 3, 7, 5, 571, 3, 108961, 3, 3, 5, 3, 7,
    11, 3, 13, 3, 37, 3, 5, 3, 3, 389, 5, 3,
    29, 3, 185099, 3, 3, 11, 5, 3, 3, 5, 3, 3,
    3, 5, 3, 3, 577, 3, 3, 3, 37, 3, 1783, 3,
    167, 3, 5, 3, 7]

theorem prime_sub_3061 : Nat.Prime (105963812462 - 3061) := by
  show Nat.Prime 105963809401
  exact p105963809401

theorem check_3061 : allC 105963812462 3061 P10k ds_3061 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 105963812462 is 3061. -/
theorem minGB_3061 : minGB 105963812462 = 3061 :=
  minGB_eq_of P10k P10k_complete 105963812462 3061 (by norm_num) (by norm_num) prime_sub_3061 ds_3061 check_3061

def ds_3163 : List ℕ := [
    2, 11, 3, 5, 3, 19, 3, 23, 3, 3, 141833, 5,
    3, 17, 3, 3, 3, 997, 5, 3, 153533, 43, 3, 3,
    5, 3, 38611, 3, 7, 3, 5, 3, 3, 37, 3, 7,
    5, 31, 3, 3, 3, 29, 3, 7, 3, 464327, 13, 11,
    3, 1283, 3, 3, 19, 3, 3, 3, 3, 5437, 5, 3,
    7669, 3, 5, 3, 41, 3, 9439, 5, 3, 17, 3, 3,
    5, 463, 271, 3, 3, 5, 3, 1367, 3, 11, 3, 23,
    109, 3, 3, 5, 3, 809, 3, 3, 5, 3, 211229, 3,
    3, 3, 13, 53, 5, 3, 3, 3, 7, 5, 3, 3,
    3, 13, 5, 7, 3, 11, 241, 3, 683, 3, 3, 3,
    61, 8731, 3, 3, 1433, 3, 23, 3, 5, 389, 7, 3,
    11, 5, 3, 79, 3, 5, 3, 3, 19, 3, 7, 3,
    1129, 3, 43, 3, 17, 3, 5, 3, 11, 3, 5, 3,
    265747, 3, 5, 3, 3, 3, 5, 3, 3, 3, 7, 5,
    28051, 3, 3, 73, 3, 7, 19, 3, 29, 3, 17, 13,
    5, 3, 31, 3, 3, 3, 5, 23, 727, 3, 19, 3,
    242639, 3, 3, 3, 7, 11, 3, 3, 3, 2251, 5, 37,
    3, 3, 11, 3, 3, 487, 5, 3, 13, 3, 3, 197,
    5, 3, 3, 3, 13, 23, 3, 1487, 3, 283, 3, 3,
    5, 3, 7, 13, 17, 3, 557, 3, 509, 3, 3, 3,
    3, 40939, 11, 50359, 3, 3, 5, 3, 7, 3, 5, 3,
    3, 11, 3, 3, 7, 5, 3, 5, 7, 3, 148157, 13,
    3, 461, 3, 3, 19, 3, 11, 5, 137, 61, 5, 5443,
    3, 7, 315059, 3, 3, 7, 3, 103, 5, 3, 7, 3,
    17, 3, 3, 3, 3, 3, 101, 3, 19, 3, 3, 5,
    139, 3, 7, 3, 181, 5, 3, 743, 3, 653, 3, 3,
    3, 7, 3, 23, 3, 3, 424001, 3, 53, 5, 3, 43,
    3, 13, 19, 11, 3, 3, 7993, 3, 13, 3, 7, 3,
    11, 3, 41, 5, 7, 3, 3, 431, 3, 3, 47, 5,
    3, 3, 454501, 5, 3, 163, 17, 3, 3, 3, 3, 3,
    5, 3, 3, 3, 5, 13, 3, 7, 19, 3, 101, 3,
    3, 13, 5, 3, 3, 17, 3, 5, 3, 3, 5, 3,
    43, 3, 7, 5, 59, 3, 416201, 3, 3, 5, 3, 7,
    3671, 3, 11, 3, 19, 3, 5, 3, 3, 29, 5, 3,
    37, 3, 29587, 3, 3, 97171, 5, 3, 3, 5, 3, 3,
    3, 5, 3, 3, 31, 3, 3, 3, 350747, 3, 17, 3,
    13, 3, 5, 3, 7, 11, 5, 5557, 3, 3, 71, 3,
    491, 3]

theorem prime_sub_3163 : Nat.Prime (244885595672 - 3163) := by
  show Nat.Prime 244885592509
  exact p244885592509

theorem check_3163 : allC 244885595672 3163 P10k ds_3163 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 244885595672 is 3163. -/
theorem minGB_3163 : minGB 244885595672 = 3163 :=
  minGB_eq_of P10k P10k_complete 244885595672 3163 (by norm_num) (by norm_num) prime_sub_3163 ds_3163 check_3163

def ds_3457 : List ℕ := [
    2, 5, 3, 1621, 3, 5, 3, 7, 3, 3, 29, 23,
    3, 5, 3, 3, 3, 7, 617, 3, 5, 263, 3, 3,
    13, 3, 5, 3, 11, 3, 367, 3, 3, 72461, 3, 347,
    421, 5, 3, 3, 3, 601, 3, 5, 3, 47, 154787, 5,
    3, 7, 3, 3, 11, 3, 3, 3, 3, 7, 139, 3,
    5, 3, 11, 3, 5, 3, 13, 19, 3, 17, 3, 3,
    1423, 5, 29, 3, 3, 7, 3, 13, 3, 210943, 3, 5,
    7, 3, 3, 439, 3, 5, 3, 3, 13, 3, 3203, 3,
    3, 3, 5, 1571, 103, 3, 3, 3, 11, 1297, 3, 3,
    3, 43, 7, 5, 3, 59, 197, 3, 5, 3, 3, 3,
    281, 5, 3, 3, 7, 3, 389, 3, 23, 5, 2549, 3,
    227, 17, 3, 11, 3, 953, 3, 3, 4643, 3, 5, 3,
    224617, 3, 5, 3, 7, 3, 13, 3, 5, 3, 19, 3,
    3617, 3, 463, 3, 3, 3, 11, 3, 3, 3, 3251, 124693,
    1237, 3, 3, 19, 3, 5, 131, 3, 36451, 3, 5, 7,
    383, 3, 5, 3, 3, 3, 43, 5, 33617, 3, 5, 3,
    1669, 3, 3, 3, 157, 5, 3, 3, 3, 11, 7, 19,
    3, 3, 7, 3, 3, 337, 11, 3, 5, 3, 3, 7,
    41, 3, 3, 3, 33863, 223, 3, 5, 3, 11, 3, 3,
    7, 3, 5, 2957, 17, 3, 5, 3, 7, 3, 3, 3,
    3, 7, 5, 41617, 3, 3, 101, 3, 13, 3, 29, 3,
    3, 47, 3, 3, 241, 11, 3, 7, 5, 3, 547, 5,
    3, 7, 3, 3, 5, 3, 7, 48523, 5, 11, 17, 5,
    3, 179, 113, 3, 3, 23, 3, 6287, 7, 3, 5, 3,
    17, 3, 3, 3, 3, 3, 5, 3, 7, 3, 3, 57719,
    5, 3, 37, 3, 4481, 173, 3, 997, 3, 5, 3, 3,
    3, 5, 3, 11, 3, 3, 5, 3, 54037, 73, 3, 5,
    3, 7, 83, 5, 3, 3, 11, 3, 229, 3, 251, 3,
    149, 3, 13, 7, 5, 3, 3, 41, 3, 3, 67, 281,
    3, 3, 7, 641, 3, 5, 17, 3, 3, 3, 3, 3,
    13, 3, 3, 3, 29, 5, 3, 5, 23, 3, 7, 3,
    3, 11, 41, 3, 3, 5, 3, 11, 3, 3, 1597, 3,
    23, 3, 13, 83, 5, 3, 151, 3, 3, 7, 3, 5,
    89, 3, 19, 3, 7, 3, 5279, 3, 3, 7, 17, 3,
    5, 3, 5, 3, 3, 12653, 127, 3, 3, 37, 3, 3,
    3, 7, 3, 3, 5, 3, 3, 3, 137, 3, 7, 3,
    47, 3, 26903, 3, 41, 13, 53, 11, 3, 3, 37, 3,
    307, 3, 5, 3, 7, 43, 19, 3, 3, 3, 13, 3,
    1433, 3, 5, 3, 683, 271, 3, 19, 17, 5, 71, 3,
    3, 37, 5, 3, 3, 709, 3, 5, 3, 6053, 3, 3,
    5, 3]

theorem prime_sub_3457 : Nat.Prime (599533546358 - 3457) := by
  show Nat.Prime 599533542901
  exact p599533542901

theorem check_3457 : allC 599533546358 3457 P10k ds_3457 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 599533546358 is 3457. -/
theorem minGB_3457 : minGB 599533546358 = 3457 :=
  minGB_eq_of P10k P10k_complete 599533546358 3457 (by norm_num) (by norm_num) prime_sub_3457 ds_3457 check_3457

def ds_3463 : List ℕ := [
    2, 765983, 3, 271, 3, 7, 3, 13, 3, 3, 5, 6827,
    3, 31, 3, 3, 3, 5, 443, 3, 43, 137, 3, 3,
    7, 3, 47699, 3, 23, 3, 151, 3, 3, 7, 3, 5,
    7349, 223, 3, 3, 3, 5, 3, 17, 3, 304553, 5, 7,
    3, 29, 3, 3, 5, 3, 3, 3, 3, 5, 2713, 3,
    281, 3, 7, 3, 11, 3, 5, 313, 3, 7, 3, 3,
    19, 47, 11, 3, 3, 17, 3, 13, 3, 5, 3, 7,
    41, 3, 3, 37, 3, 5413, 3, 3, 13, 3, 17, 3,
    3, 3, 23, 5, 61, 3, 3, 3, 5, 11, 3, 3,
    3, 5, 1237, 4639, 3, 112031, 5, 3, 7, 3, 3, 3,
    5, 2141, 3, 3, 5, 3, 11, 3, 7, 127, 3271, 3,
    5, 52883, 3, 7, 3, 31, 3, 3, 5, 3, 19, 3,
    199, 3, 7, 3, 10289, 3, 13, 3, 887, 3, 11, 3,
    6397, 3, 7, 3, 3, 3, 83, 3, 3, 3, 5, 67,
    17, 3, 3, 5, 3, 13, 11, 3, 5, 3, 7, 727817,
    1733, 3, 176087, 3, 3, 3, 68449, 37, 79, 3, 4057, 3,
    5, 3, 3, 3, 5, 17, 3, 3, 3, 5, 11, 810377,
    3, 3, 19, 3, 3, 5, 53, 3, 11, 3, 3, 5,
    4481, 3, 3, 3, 5, 7, 3, 13, 3, 29287, 3, 3,
    29, 3, 73369, 24281, 5, 3, 7, 3, 23, 3, 3, 3,
    3, 5, 189151, 557, 3, 3, 7, 3, 13, 3, 241, 3,
    3, 7, 3, 3, 5, 23, 3, 13, 101, 3, 41, 7,
    3, 11, 3, 3, 17, 3, 5, 263, 1973, 233, 7, 47,
    3, 37, 5, 3, 3, 5, 3, 5, 457, 3, 2677, 3,
    43, 3, 3, 3, 3, 3, 53, 3, 5, 3, 3, 7,
    569, 3, 5821, 3, 5, 149, 3, 7, 3, 109, 3, 3,
    3, 181, 3, 31, 3, 3, 7, 3, 5, 43, 3, 29,
    3, 5, 23, 13, 3, 3, 5, 3, 7, 3, 5, 3,
    101, 3, 5, 229, 11, 3, 3, 5, 3, 3, 5, 47,
    3, 3, 5, 61, 3, 4159, 566759, 3, 3, 3, 3, 3,
    13, 3, 3, 3, 433, 1291, 3, 431, 5, 3, 17, 3,
    3, 5, 11, 3, 3, 13, 3, 7, 3, 3, 19, 3,
    7, 3, 5, 37, 139, 3, 11, 3, 3, 109, 3, 113,
    171827, 3, 5, 3, 13, 3, 1103, 3, 3, 5, 157, 3,
    1223, 3, 31, 3, 3, 5, 478823, 3, 3, 11, 3, 3,
    3, 389, 3, 3, 7, 3, 3, 3, 5, 3, 5, 3,
    11, 3, 7, 3, 17, 5, 1151, 7, 3, 3, 61, 3,
    5, 3, 7, 3, 43, 5, 29, 3, 3, 3, 11, 3,
    353, 3, 17, 3, 271, 5, 3, 5, 163, 599, 393901, 3,
    3, 5, 37, 3, 3, 5, 3, 7, 3, 5, 3, 3,
    66179, 3, 7, 3]

theorem prime_sub_3463 : Nat.Prime (3132059294006 - 3463) := by
  show Nat.Prime 3132059290543
  exact p3132059290543

theorem check_3463 : allC 3132059294006 3463 P10k ds_3463 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 3132059294006 is 3463. -/
theorem minGB_3463 : minGB 3132059294006 = 3463 :=
  minGB_eq_of P10k P10k_complete 3132059294006 3463 (by norm_num) (by norm_num) prime_sub_3463 ds_3463 check_3463

def ds_3529 : List ℕ := [
    2, 11, 3, 5, 3, 181, 3, 29, 3, 3, 139, 5,
    3, 23, 3, 3, 3, 89, 5, 3, 13, 71, 3, 3,
    5, 3, 358783, 3, 7, 3, 5, 3, 3, 323837, 3, 7,
    5, 73, 3, 3, 3, 23, 3, 7, 3, 3613, 97259, 11,
    3, 13, 3, 3, 47, 3, 3, 3, 3, 31, 5, 3,
    53, 3, 5, 3, 193381, 3, 17, 5, 3, 67, 3, 3,
    5, 199, 19, 3, 3, 5, 3, 30013, 3, 11, 3, 17,
    37, 3, 3, 5, 3, 13, 3, 3, 5, 3, 167, 3,
    3, 3, 43, 13, 5, 3, 3, 3, 7, 5, 3, 3,
    3, 53, 5, 7, 3, 11, 125963, 3, 31, 3, 3, 3,
    37, 2129, 3, 3, 149, 3, 178757, 3, 5, 23, 7, 3,
    11, 5, 3, 1601, 3, 5, 3, 3, 127, 3, 7, 3,
    31, 3, 13, 3, 41, 3, 5, 3, 11, 3, 5, 3,
    53, 3, 5, 3, 3, 3, 5, 3, 3, 3, 7, 5,
    13, 3, 3, 46327, 3, 7, 43, 3, 115873, 3, 19, 113,
    5, 3, 157, 3, 3, 3, 5, 839, 89, 3, 67, 3,
    1193, 3, 3, 3, 7, 11, 3, 3, 3, 170669, 5, 17,
    3, 3, 11, 3, 3, 19, 5, 3, 138617, 3, 3, 13,
    5, 3, 3, 3, 461, 13, 3, 23, 3, 101, 3, 3,
    5, 3, 7, 1181, 433, 3, 317, 3, 559739, 3, 3, 3,
    3, 59, 11, 37, 3, 3, 5, 3, 7, 3, 5, 3,
    3, 11, 3, 3, 7, 5, 3, 5, 7, 3, 195103, 1913,
    3, 23, 3, 3, 24683, 3, 11, 5, 2803, 17, 5, 71,
    3, 7, 131, 3, 3, 7, 3, 17, 5, 3, 7, 3,
    179, 3, 3, 3, 3, 3, 29, 3, 2671, 3, 3, 5,
    37, 3, 7, 3, 233, 5, 3, 638933, 3, 877, 3, 3,
    3, 7, 3, 19, 3, 3, 23, 3, 31, 5, 3, 1453339,
    3, 4549, 13, 11, 3, 3, 12983, 3, 59, 3, 7, 3,
    11, 3, 29, 5, 7, 3, 3, 493457, 3, 3, 773, 5,
    3, 3, 17, 5, 3, 5297, 23, 3, 3, 3, 3, 3,
    5, 3, 3, 3, 5, 17, 3, 7, 15269, 3, 463, 3,
    3, 2833, 5, 3, 3, 59, 3, 5, 3, 3, 5, 3,
    19, 3, 7, 5, 97607, 3, 31, 3, 3, 5, 3, 7,
    1901, 3, 11, 3, 257, 3, 5, 3, 3, 73, 5, 3,
    13, 3, 307, 3, 3, 283, 5, 3, 3, 5, 3, 3,
    3, 5, 3, 3, 179, 3, 3, 3, 36527, 3, 19, 3,
    61, 3, 5, 3, 7, 11, 5, 23, 3, 3, 163, 3,
    11119, 3, 67, 3, 1249, 1381, 5, 3, 3, 3, 5, 3,
    19, 3, 2089, 3, 7, 13, 3, 7, 5, 26489, 41, 3,
    3, 1949, 7, 3, 3, 43, 3, 131, 3, 11, 3, 3,
    31, 3, 5, 3, 53, 3, 7, 3, 29, 7, 5, 3]

theorem prime_sub_3529 : Nat.Prime (3620821173302 - 3529) := by
  show Nat.Prime 3620821169773
  exact p3620821169773

theorem check_3529 : allC 3620821173302 3529 P10k ds_3529 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 3620821173302 is 3529. -/
theorem minGB_3529 : minGB 3620821173302 = 3529 :=
  minGB_eq_of P10k P10k_complete 3620821173302 3529 (by norm_num) (by norm_num) prime_sub_3529 ds_3529 check_3529

def ds_3613 : List ℕ := [
    2, 929, 3, 13, 3, 293, 3, 5, 3, 3, 5927, 21997,
    3, 269, 3, 3, 3, 7, 31, 3, 1861, 5, 3, 3,
    62423, 3, 7, 3, 5, 3, 11, 3, 3, 5, 3, 3089,
    733, 13, 3, 3, 3, 79, 3, 11, 3, 5, 17, 557,
    3, 5, 3, 3, 13, 3, 3, 3, 3, 7, 23, 3,
    359, 3, 103, 3, 7, 3, 59, 21767, 3, 5, 3, 3,
    53, 977357, 5, 3, 3, 7, 3, 5, 3, 41, 3, 14321,
    5, 3, 3, 11, 3, 43, 3, 3, 5563, 3, 5, 3,
    3, 3, 7, 19, 321779, 3, 3, 3, 173, 3527, 3, 3,
    3, 1613, 7, 413737, 3, 5, 13, 3, 139, 3, 3, 3,
    245711, 197, 3, 3, 7, 3, 5, 3, 67, 7, 5, 3,
    2081, 126733, 3, 5, 3, 11, 3, 3, 31, 3, 17, 3,
    5, 3, 11, 3, 5, 3, 251, 3, 19, 3, 137, 3,
    5, 3, 431063, 3, 3, 3, 23, 3, 3, 3, 563, 19,
    5, 3, 3, 13, 3, 179, 5, 3, 11, 3, 28439, 5,
    439, 3, 744199, 3, 3, 3, 11, 9791, 5, 3, 7, 3,
    29, 3, 3, 3, 83, 66089, 3, 3, 3, 17, 7, 5,
    3, 3, 5, 3, 3, 7727, 334717, 3, 47, 3, 3, 7,
    283, 3, 3, 3, 11, 5, 3, 645839, 3, 5, 3, 3,
    7, 3, 19, 5, 761, 3, 211, 3, 5, 3, 3, 3,
    3, 7, 103, 5, 3, 3, 13, 3, 5, 3, 163, 3,
    3, 5, 3, 3, 37, 853, 3, 7, 3083, 3, 5, 29,
    3, 5, 3, 3, 13, 3, 7, 59, 43, 5, 11, 7,
    3, 5, 13, 3, 3, 6529, 3, 929, 7, 3, 286249, 3,
    5, 3, 3, 3, 3, 3, 23, 3, 7, 3, 3, 607,
    7, 3, 5, 3, 43, 135479, 3, 5, 3, 88423, 3, 3,
    3, 701, 3, 5, 3, 3, 13, 3, 308149, 19, 3, 41,
    3, 7, 5, 7, 3, 3, 370673, 3, 5, 3, 17, 3,
    5, 3, 2377, 7, 194413, 3, 3, 139, 3, 3, 1940849, 13,
    3, 3, 7, 313, 3, 251, 5, 3, 3, 3, 3, 3,
    11, 3, 3, 3, 1039, 379, 3, 11, 601969, 3, 5, 3,
    3, 79, 17, 3, 3, 19, 3, 1579, 3, 3, 173, 3,
    5, 3, 31, 127, 1069, 3, 5, 3, 3, 7, 3, 47,
    5, 3, 37, 3, 5, 3, 11, 3, 3, 7, 337, 3,
    95273, 3, 7, 3, 3, 3191, 31, 3, 3, 78809, 3, 3,
    3, 7, 3, 3, 37, 3, 3, 3, 13, 3, 7, 3,
    5, 3, 23, 3, 5, 71, 17, 5, 3, 3, 5, 3,
    1017277, 3, 11, 3, 5, 179, 181, 3, 3, 3, 2269, 3,
    5, 3, 7, 3, 5, 17, 3, 43, 1483861, 23, 5, 3,
    3, 2857, 905147, 3, 3, 11, 3, 17, 3, 19, 3, 3,
    29, 3, 30293, 3, 7, 3, 5, 3, 5, 73, 13, 3,
    5, 3, 3, 67, 7, 3, 5, 151, 3, 101, 3, 29]

theorem prime_sub_3613 : Nat.Prime (4438327672994 - 3613) := by
  show Nat.Prime 4438327669381
  exact p4438327669381

theorem check_3613 : allC 4438327672994 3613 P10k ds_3613 = true := by decide +kernel

/-- Record row: the least Goldbach prime of 4438327672994 is 3613. -/
theorem minGB_3613 : minGB 4438327672994 = 3613 :=
  minGB_eq_of P10k P10k_complete 4438327672994 3613 (by norm_num) (by norm_num) prime_sub_3613 ds_3613 check_3613

end LeanLab.Verifications.Top50.Records2
