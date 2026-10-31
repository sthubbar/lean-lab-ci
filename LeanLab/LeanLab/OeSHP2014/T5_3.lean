/-
P0005 Oliveira e Silva, Herzog, Pardi 2014, Math. Comp. 83, 2033 to 2060, Table 5 page 2044,
the rows not already in Sinisalo 1993 Table 2, part 3: minGB S(p) = p. Divisors and Pratt
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

theorem p10924763 : Nat.Prime 10924763 := by
  refine Pratt.pratt 10924763 2 [(2, 1), (859, 1), (6359, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p16363817 : Nat.Prime 16363817 := by
  refine Pratt.pratt 16363817 3 [(2, 3), (7, 1), (103, 1), (2837, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p34359443 : Nat.Prime 34359443 := by
  refine Pratt.pratt 34359443 2 [(2, 1), (13, 1), (1321517, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p43082167 : Nat.Prime 43082167 := by
  refine Pratt.pratt 43082167 5 [(2, 1), (3, 1), (233, 1), (30817, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p138212929 : Nat.Prime 138212929 := by
  refine Pratt.pratt 138212929 11 [(2, 6), (3, 2), (7, 2), (59, 1), (83, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p312493199 : Nat.Prime 312493199 := by
  refine Pratt.pratt 312493199 7 [(2, 1), (4231, 1), (36929, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p567280543 : Nat.Prime 567280543 := by
  refine Pratt.pratt 567280543 3 [(2, 1), (3, 1), (29, 1), (647, 1), (5039, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p2179183823 : Nat.Prime 2179183823 := by
  refine Pratt.pratt 2179183823 5 [(2, 1), (8689, 1), (125399, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p4146387871 : Nat.Prime 4146387871 := by
  refine Pratt.pratt 4146387871 3 [(2, 1), (3, 1), (5, 1), (138212929, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p138212929
theorem p4208875417 : Nat.Prime 4208875417 := by
  refine Pratt.pratt 4208875417 5 [(2, 3), (3, 2), (79, 1), (739957, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p4843689833 : Nat.Prime 4843689833 := by
  refine Pratt.pratt 4843689833 3 [(2, 3), (37, 1), (16363817, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p16363817
theorem p7283642489 : Nat.Prime 7283642489 := by
  refine Pratt.pratt 7283642489 3 [(2, 3), (8663, 1), (105097, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p130122536627 : Nat.Prime 130122536627 := by
  refine Pratt.pratt 130122536627 2 [(2, 1), (331, 1), (1151, 1), (170773, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p206197371439 : Nat.Prime 206197371439 := by
  refine Pratt.pratt 206197371439 3 [(2, 1), (3, 1), (23, 1), (1699, 1), (879449, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p988273747477477 : Nat.Prime 988273747477477 := by
  refine Pratt.pratt 988273747477477 5 [(2, 2), (3, 2), (3769, 1), (7283642489, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p7283642489
theorem p1842054285131699 : Nat.Prime 1842054285131699 := by
  refine Pratt.pratt 1842054285131699 2 [(2, 1), (11, 1), (267941, 1), (312493199, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p312493199
theorem p2303608290770057 : Nat.Prime 2303608290770057 := by
  refine Pratt.pratt 2303608290770057 3 [(2, 3), (507599, 1), (567280543, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p567280543
theorem p2748443296346999 : Nat.Prime 2748443296346999 := by
  refine Pratt.pratt 2748443296346999 11 [(2, 1), (630613, 1), (2179183823, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p2179183823
theorem p3771671520127351 : Nat.Prime 3771671520127351 := by
  refine Pratt.pratt 3771671520127351 6 [(2, 1), (3, 1), (5, 2), (7, 1), (37, 1), (149603, 1), (648937, 1)] (by norm_num)
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
theorem p4463039219932529 : Nat.Prime 4463039219932529 := by
  refine Pratt.pratt 4463039219932529 3 [(2, 4), (67273, 1), (4146387871, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p4146387871
theorem p5122498676190887 : Nat.Prime 5122498676190887 := by
  refine Pratt.pratt 5122498676190887 5 [(2, 1), (643, 1), (1065733, 1), (3737597, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p6198478168622573 : Nat.Prime 6198478168622573 := by
  refine Pratt.pratt 6198478168622573 3 [(2, 2), (7, 1), (149, 1), (353, 1), (4208875417, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p4208875417
theorem p14211744403069643 : Nat.Prime 14211744403069643 := by
  refine Pratt.pratt 14211744403069643 2 [(2, 1), (11, 1), (13, 1), (10259, 1), (4843689833, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p4843689833
theorem p15812379959639633 : Nat.Prime 15812379959639633 := by
  refine Pratt.pratt 15812379959639633 3 [(2, 4), (988273747477477, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p988273747477477
theorem p20017986381364871 : Nat.Prime 20017986381364871 := by
  refine Pratt.pratt 20017986381364871 7 [(2, 1), (5, 1), (1373, 1), (42433, 1), (34359443, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p34359443
theorem p31821625829244467 : Nat.Prime 31821625829244467 := by
  refine Pratt.pratt 31821625829244467 2 [(2, 1), (31, 1), (41, 1), (223, 1), (1303, 1), (43082167, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p43082167
theorem p48033787978018637 : Nat.Prime 48033787978018637 := by
  refine Pratt.pratt 48033787978018637 2 [(2, 2), (19, 1), (71, 1), (137, 1), (92959, 1), (698977, 1)] (by norm_num)
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
theorem p55104008958359483 : Nat.Prime 55104008958359483 := by
  refine Pratt.pratt 55104008958359483 2 [(2, 1), (11, 1), (17467, 1), (51043, 1), (2809351, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p107157207101888297 : Nat.Prime 107157207101888297 := by
  refine Pratt.pratt 107157207101888297 3 [(2, 3), (17, 1), (163, 1), (442469, 1), (10924763, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p10924763
theorem p182745307201013897 : Nat.Prime 182745307201013897 := by
  refine Pratt.pratt 182745307201013897 3 [(2, 3), (139, 1), (797, 1), (206197371439, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p206197371439
theorem p237098616193715987 : Nat.Prime 237098616193715987 := by
  refine Pratt.pratt 237098616193715987 2 [(2, 1), (31, 1), (29389, 1), (130122536627, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p130122536627

def ds_4937 : List ℕ := [
    2, 19, 523, 3, 5, 3, 31, 3,
    3299, 293, 3, 3, 5, 3, 1010461, 7,
    457, 3, 3, 5, 3, 3, 389, 109,
    3, 5, 3, 47, 3, 43, 3, 5,
    7, 3, 467, 3, 3, 3, 29019083, 353,
    7, 3, 5, 3, 11, 3, 3, 3,
    348461, 3, 13, 1151, 3, 5, 17, 7,
    19, 3, 3, 5, 3, 5229293, 3, 5,
    3, 167, 3, 3, 7, 3, 13163, 17,
    3, 3, 3, 19, 7, 3, 5, 3,
    32687, 3, 5, 3, 3, 1087, 313, 3,
    5, 3, 13, 127, 3, 5, 3, 15361,
    23, 5, 3, 3, 3, 7, 17, 157,
    3, 3, 643, 11, 7, 3, 3, 3,
    97, 3, 3, 5, 3, 23, 23293, 11,
    3, 3, 41, 7, 3, 5, 3, 661,
    3, 3, 3, 109, 3, 3, 5, 3,
    29, 3, 71, 7, 3, 5, 3, 6007,
    3, 19, 3, 11, 3, 3808109, 3, 5,
    3, 43, 3, 5, 3, 283, 3, 5,
    29, 19, 3, 5, 7, 19914371, 3, 3,
    3, 13, 7, 3, 5, 3, 3, 13147,
    3, 5, 3, 3, 3, 5, 3, 199,
    7, 2011, 3, 3, 3, 5, 3, 739,
    3, 5, 7, 103, 3, 3, 1399499, 71,
    7, 3, 3, 3, 223, 17, 3, 5119,
    61, 3, 3, 5, 3, 577, 11, 3,
    3, 5, 19753, 101, 3, 3, 19, 3,
    30109, 3, 449, 7, 3, 5, 3, 3,
    3, 5, 3, 3923, 3, 60497, 2371, 5,
    7, 3, 3, 3, 1913, 13, 3, 5,
    3, 11, 3, 5, 7, 3, 23, 419,
    3, 3, 13, 3, 3, 1493, 3, 3,
    50159, 3, 4846211, 5, 3, 7, 3, 3,
    3, 3, 3, 3, 17, 3, 3, 5,
    241, 3, 11, 3, 3, 5, 3, 31,
    3, 17, 5, 41, 11, 5, 3, 13,
    3, 2857, 11, 3, 3, 4957, 3, 127,
    3, 3, 7, 3, 17480951, 3, 31, 7,
    5, 3, 83, 3, 10099, 5, 3, 67,
    3, 3, 5, 3, 7, 3, 3, 3,
    19, 37, 3, 7, 3, 11, 3, 1709,
    3, 7333, 3, 3, 3, 17, 11, 3,
    587, 13, 3, 3, 5, 79, 3, 3,
    5, 3, 3, 4084909, 17, 5, 13, 2251,
    3, 5, 7, 487, 3, 3, 9910591, 3,
    3, 5, 3, 367, 19, 3, 3, 23,
    5, 3, 7549, 3, 5, 107, 3, 7,
    3, 19, 3, 3, 3, 29, 3, 43,
    7, 3, 5, 3, 3, 13, 3, 5,
    3, 61, 3, 19, 320063, 3, 3, 5,
    3, 347, 3, 11, 311, 3, 3, 5,
    37, 3, 2376047, 11, 7, 3, 47, 683,
    3, 3229, 13, 11, 3, 1021, 3, 5,
    3, 131, 3, 5, 3, 3, 3, 3,
    83, 14753, 3, 7, 3, 41, 3, 11,
    3, 3, 3, 5, 7, 29, 3, 5,
    3, 5, 3, 4712321, 3, 3, 11, 3,
    3, 3, 3, 37, 7, 3, 3, 19,
    109, 3, 5, 3, 1867, 3, 23, 7,
    3, 4057, 3, 5, 3, 43, 3, 5,
    3, 3, 3, 97, 3, 139, 7, 3,
    3, 29, 3, 3, 5, 3, 19949, 3,
    3, 1481, 7, 3, 3, 3, 1891187, 5,
    3, 2267, 3, 3, 5, 3, 496231, 3,
    3, 3, 5, 37, 3, 71, 3, 101,
    19, 5, 3, 7, 3, 5, 3, 59,
    3, 5, 3, 3, 5, 7, 3, 31,
    17, 3, 3, 137, 3, 37, 5, 3,
    830899, 109, 150203, 3, 3, 6469, 3, 3,
    631, 29, 5, 3, 3, 3, 7, 3,
    13, 67, 3, 11, 3, 3, 3, 5,
    59, 3, 1033, 3, 5, 3, 7, 19,
    3, 5, 3, 103, 11, 3, 3, 7,
    3, 10355101, 3, 3, 19, 5, 5441, 353,
    5, 3, 3, 3, 5, 10847, 7, 5,
    3, 211, 3, 3, 1777, 3, 13, 7,
    3, 3, 3, 61, 3, 3, 3, 3,
    4049, 3, 17, 23, 3, 3, 3, 7,
    13, 5, 1483, 5, 3, 3, 269, 5,
    3, 3, 23, 3, 67121, 7, 3, 3,
    11, 3, 3, 5, 37, 197, 3, 3,
    151471, 5, 3]

theorem prime_sub_4937 : Nat.Prime (1842054285136636 - 4937) := by
  show Nat.Prime 1842054285131699
  exact p1842054285131699

theorem check_4937 : allC 1842054285136636 4937 P10k ds_4937 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 1842054285136636 is 4937. -/
theorem minGB_S_4937 : minGB 1842054285136636 = 4937 :=
  minGB_eq_of P10k P10k_complete 1842054285136636 4937 (by norm_num) (by norm_num) prime_sub_4937 ds_4937 check_4937

def ds_5051 : List ℕ := [
    2, 5, 13, 3, 43, 3, 5419, 3,
    5, 19, 3, 3, 509, 3, 101, 5,
    750661, 3, 3, 10723, 3, 3, 5, 653,
    3, 23, 3, 7, 3, 5, 3, 29,
    181, 3, 7, 3, 3, 3, 227, 5,
    20201, 3, 7, 3, 17, 3, 3, 3,
    1283, 3, 5, 13, 3, 11, 19, 5,
    41, 3, 3, 11597, 3, 5, 3, 2609,
    3, 7, 3, 3, 37, 3, 5, 7,
    3, 3, 3, 5, 577, 3, 7, 3,
    2767, 3, 1163, 3, 3, 5, 11, 3,
    97, 3, 73, 29, 3, 5323, 3, 5,
    491, 61, 3, 3, 3, 63913, 5, 7,
    3, 3, 79, 5, 19, 3, 3, 3,
    2351, 3, 3, 4691, 3, 11, 5, 59,
    3, 3, 607, 5, 3, 8861, 3, 821,
    3, 3, 3, 5, 3, 3, 41, 3,
    5, 3, 83, 17, 3, 7, 3, 19,
    3, 197, 3, 251, 3, 5, 3, 52223,
    3, 61, 3, 11, 3, 23, 3, 13,
    7, 5, 3, 120863, 11, 5, 3, 3,
    3, 5, 13, 3, 7, 3, 3, 22817,
    3, 79, 3, 3, 3, 191, 3, 13,
    5, 11, 3, 3, 3, 1861, 3, 5,
    3, 75169, 163, 5, 3, 3, 17, 5,
    601, 3, 3, 3, 101, 179, 3, 5,
    109469, 3, 3, 43, 3, 11, 17, 3,
    3, 156253, 7, 5, 3, 3, 7, 3,
    107, 3, 5, 11, 3, 7, 3, 3,
    3, 23, 3, 13, 3, 5, 41, 19,
    5, 3, 3, 3, 5, 43, 3, 11,
    3, 5, 3, 4603, 47, 3, 5, 7,
    3, 3, 11, 3, 3, 1941931, 3, 3,
    29, 3, 53, 13, 3, 5, 3, 3,
    3, 3, 3, 3, 7, 3, 3, 30931,
    5, 3, 353, 3, 3, 7, 3, 13,
    3, 47, 11, 2029, 5, 17, 3, 2677,
    3, 5, 2699, 3, 3, 7, 3, 5,
    3, 3, 53, 3, 7, 3, 5, 107,
    7, 3, 1153, 3, 11, 13, 3, 2671,
    3, 3, 13249, 3, 5, 3, 3, 3,
    7, 5, 3, 17, 3, 5, 3, 13,
    3, 5, 3, 3, 3, 11, 19, 3,
    5, 17, 3, 3, 61, 469031, 3, 3,
    3298007, 3, 3, 5, 1213, 9029, 7, 5,
    3, 17, 23, 7, 3, 3, 167, 3,
    3, 235591, 3, 5, 638999, 3, 3, 13,
    43, 3, 31, 3, 26717, 5, 3, 13,
    3, 5, 3, 3, 3, 137, 3, 5,
    6341591, 3, 7, 3, 3, 41, 3, 29,
    3, 5, 3, 123323, 37, 3, 3, 1001947,
    3, 433, 3, 7, 5, 3, 3, 23,
    7, 3, 1093, 5, 151, 3, 42743, 67,
    3, 11, 5, 13, 3, 23, 3, 37,
    3, 5, 3, 1358689, 3, 3, 3, 3,
    5, 7, 3, 7961567, 3, 23, 3, 31,
    3, 3, 3, 823, 5, 3719, 3, 11,
    3, 1553, 3, 7, 3, 3, 7, 3,
    3, 3, 3, 5, 27143, 3, 3, 9221,
    13, 3, 97, 3, 242261, 3, 103651, 5,
    3, 19, 3, 17, 3, 7, 3, 59,
    3, 3, 3, 379, 3, 5, 31, 3,
    3, 103, 3, 3, 47, 3, 5, 3,
    3, 11, 5, 3, 3, 3, 43223, 13,
    3, 7, 3, 3, 13957087, 3, 7, 3,
    3, 3, 7, 17, 3, 313, 3, 2377,
    5, 241, 3, 5, 3, 577, 3, 5,
    3, 11, 3, 3, 31, 619, 3, 5,
    7, 3, 3, 11, 3, 10313, 782189, 3,
    653, 5, 19, 3, 3, 2659, 3, 3,
    5, 11, 5107, 3, 3, 3, 709, 3,
    5, 7, 3, 312343, 3, 3, 3, 11,
    13, 3, 4157, 3, 23, 3, 5, 4647683,
    3, 571, 3, 5, 101, 3, 3, 65963,
    3, 7, 3, 3, 5, 7, 43, 11,
    787, 3, 3, 3, 13, 199, 5, 17,
    3, 5, 3, 3, 7, 3, 5, 61,
    3, 3, 3, 5, 3, 3, 3, 3,
    107, 3, 5, 1201, 3, 3, 3, 5,
    331, 3223069, 5, 151, 3, 3, 5, 195401,
    3, 3, 17, 3, 5, 165463, 3, 3,
    19, 3, 3, 11, 263573, 17, 3, 3,
    13, 19, 3, 7, 5, 3, 3, 677321,
    3, 5, 3, 3, 3, 5, 37, 3,
    7, 3, 45883099]

theorem prime_sub_5051 : Nat.Prime (2303608290775108 - 5051) := by
  show Nat.Prime 2303608290770057
  exact p2303608290770057

theorem check_5051 : allC 2303608290775108 5051 P10k ds_5051 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 2303608290775108 is 5051. -/
theorem minGB_S_5051 : minGB 2303608290775108 = 5051 :=
  minGB_eq_of P10k P10k_complete 2303608290775108 5051 (by norm_num) (by norm_num) prime_sub_5051 ds_5051 check_5051

def ds_5087 : List ℕ := [
    2, 11, 271, 3, 5, 3, 23, 3,
    397, 31, 3, 3, 5, 3, 11, 7,
    17, 3, 3, 5, 3, 3, 263, 97,
    3, 5, 3, 24533, 3, 11, 3, 5,
    7, 3, 2549, 3, 3, 3, 61, 71,
    7, 3, 5, 3, 3023, 3, 3, 3,
    2663, 3, 43, 233, 3, 5, 6661, 7,
    89819, 3, 3, 5, 3, 23, 3, 5,
    3, 101, 3, 3, 7, 3, 281, 13,
    3, 3, 3, 4957, 7, 3, 5, 3,
    131, 3, 5, 3, 3, 11, 83, 3,
    5, 3, 17, 24251, 3, 5, 3, 769,
    11, 5, 3, 3, 3, 7, 821, 17,
    3, 3, 31, 13, 7, 3, 3, 3,
    9236341, 3, 3, 5, 3, 2027, 20897, 5437979,
    3, 3, 47, 7, 3, 5, 3, 991,
    3, 3, 3, 37, 3, 3, 5, 3,
    11, 3, 191, 7, 3, 5, 3, 13,
    3, 11, 3, 89, 3, 241, 3, 5,
    3, 29, 3, 5, 3, 13789, 3, 5,
    83, 223, 3, 5, 7, 13, 3, 3,
    3, 19, 7, 3, 5, 3, 3, 3401941,
    3, 5, 3, 3, 3, 5, 3, 293,
    7, 139, 3, 3, 3, 5, 3, 419,
    3, 5, 7, 17539, 3, 3, 13, 4363,
    7, 3, 3, 3, 23, 11239, 3, 17,
    73, 3, 3, 5, 3, 41, 563, 3,
    3, 5, 11, 13, 3, 3, 29, 3,
    67, 3, 11, 7, 3, 5, 3, 3,
    3, 5, 3, 17, 3, 41165807, 11, 5,
    7, 3, 3, 3, 41, 53, 3, 5,
    3, 19, 3, 5, 7, 3, 179, 1623533,
    3, 3, 233, 3, 3, 124951, 3, 3,
    11, 3, 17087309, 5, 3, 7, 3, 3,
    3, 3, 3, 3, 571, 3, 3, 5,
    33908057, 3, 417631, 3, 3, 5, 3, 53,
    3, 31, 5, 7691347, 79, 5, 3, 23,
    3, 331, 8230471, 3, 3, 13, 3, 13711,
    3, 3, 7, 3, 19, 3, 432721, 7,
    5, 3, 23, 3, 17, 5, 3, 1373,
    3, 3, 5, 3, 7, 3, 3, 3,
    431381, 3746167, 3, 7, 3, 789587, 3, 19,
    3, 21250429, 3, 3, 3, 37, 13, 3,
    617, 647, 3, 3, 5, 11, 3, 3,
    5, 3, 3, 383, 59, 5, 97, 11,
    3, 5, 7, 89, 3, 3, 2569927, 3,
    3, 5, 3, 13, 3529, 3, 3, 418031,
    5, 3, 17, 3, 5, 31, 3, 7,
    3, 199, 3, 3, 3, 11, 3, 27647,
    7, 3, 5, 3, 3, 61, 3, 5,
    3, 11, 3, 13, 311, 3, 3, 5,
    3, 11, 3, 19, 1481, 3, 3, 5,
    8263, 3, 691, 137, 7, 3, 433, 83,
    3, 6709867, 37, 2269, 3, 97, 3, 5,
    3, 1237, 3, 5, 3, 3, 3, 3,
    11, 13, 3, 7, 3, 151, 3, 13,
    3, 3, 3, 5, 7, 22091, 3, 5,
    3, 5, 3, 271, 3, 3, 48947, 3,
    3, 3, 3, 13, 7, 3, 3, 11,
    431, 3, 5, 3, 211, 3, 19, 7,
    3, 797, 3, 5, 3, 23, 3, 5,
    3, 3, 3, 17, 3, 21919979, 7, 3,
    3, 13, 3, 3, 5, 3, 44633, 3,
    3, 2161, 7, 3, 3, 3, 1213909, 5,
    3, 11, 3, 3, 5, 3, 107, 3,
    3, 3, 5, 41, 3, 47, 3, 467,
    109, 5, 3, 7, 3, 5, 3, 19,
    3, 5, 3, 3, 5, 7, 3, 1276397,
    20981, 3, 3, 13, 3, 163, 5, 3,
    11, 41, 23, 3, 3, 479, 3, 3,
    11, 971, 5, 3, 3, 3, 7, 3,
    197, 11, 3, 23, 3, 3, 3, 5,
    103, 3, 25738249, 3, 5, 3, 7, 13,
    3, 5, 3, 79, 269, 3, 3, 7,
    3, 131, 3, 3, 9941, 5, 53077, 1811,
    5, 3, 3, 3, 5, 109, 7, 5,
    3, 13, 3, 3, 37, 3, 59, 7,
    3, 3, 3, 1327, 3, 3, 3, 3,
    1013, 3, 67, 13, 3, 3, 3, 7,
    31, 5, 2098253, 5, 3, 3, 11, 5,
    3, 3, 181, 3, 73, 7, 3, 3,
    263, 3, 3, 5, 43, 19, 3, 3,
    9091391, 5, 3, 3533, 127, 3, 3, 7,
    3, 283, 3, 3, 3, 19, 7, 3,
    5, 3, 13, 5, 3, 3, 5]

theorem prime_sub_5087 : Nat.Prime (2748443296352086 - 5087) := by
  show Nat.Prime 2748443296346999
  exact p2748443296346999

theorem check_5087 : allC 2748443296352086 5087 P10k ds_5087 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 2748443296352086 is 5087. -/
theorem minGB_S_5087 : minGB 2748443296352086 = 5087 :=
  minGB_eq_of P10k P10k_complete 2748443296352086 5087 (by norm_num) (by norm_num) prime_sub_5087 ds_5087 check_5087

def ds_5227 : List ℕ := [
    2, 5, 3, 11, 3, 5, 3, 23,
    3, 3, 439, 6343, 3, 5, 3, 3,
    3, 1069, 29, 3, 5, 67, 3, 3,
    7, 3, 5, 3, 4204903, 3, 13, 3,
    3, 7, 3, 73, 23, 5, 3, 3,
    3, 7, 3, 5, 3, 5009, 43, 5,
    3, 239, 3, 3, 29, 3, 3, 3,
    3, 11, 223, 3, 5, 3, 7, 3,
    5, 3, 101, 11, 3, 7, 3, 3,
    31583, 5, 71, 3, 3, 7753, 3, 1049,
    3, 431, 3, 5, 13, 3, 3, 45563627,
    3, 5, 3, 3, 311, 3, 4018247, 3,
    3, 3, 5, 1553, 1429889, 3, 3, 3,
    23, 907, 3, 3, 3, 7, 331, 5,
    3, 643121, 2347, 3, 5, 3, 3, 3,
    2969, 5, 3, 3, 1723, 3, 23, 3,
    7, 5, 61, 3, 13, 19, 3, 7,
    3, 131, 3, 3, 7, 3, 5, 3,
    13, 3, 5, 3, 179, 3, 77743, 3,
    5, 3, 13, 3, 79, 3, 7, 3,
    3, 3, 3259, 3, 3, 3, 541, 11,
    2842991, 3, 3, 7, 3, 5, 13168847, 3,
    211, 3, 5, 269, 32875459, 3, 5, 3,
    3, 3, 47, 5, 11, 3, 5, 3,
    827, 3, 3, 3, 943777, 5, 3, 3,
    3, 7, 89, 3538673, 3, 3, 53, 3,
    3, 307, 13, 3, 5, 3, 3, 1860853,
    11, 3, 3, 3, 6883, 7, 3, 5,
    3, 373, 3, 3, 401, 3, 5, 11,
    61, 3, 5, 3, 45821, 3, 3, 3,
    3, 13, 5, 1993, 3, 3, 7, 3,
    56096279, 3, 53, 3, 3, 7, 3, 3,
    41, 127, 3, 11, 5, 3, 19, 5,
    3, 547, 3, 3, 5, 3, 31, 1759,
    5, 43, 7, 5, 3, 11, 14347, 3,
    3, 2081, 3, 7, 41, 3, 5, 3,
    2473, 3, 3, 3, 3, 3, 5, 3,
    23, 3, 3, 7, 5, 3, 13, 3,
    19, 43, 3, 7, 3, 5, 3, 3,
    3, 5, 3, 23, 3, 3, 5, 3,
    521137, 16567, 3, 5, 3, 147137, 6911, 5,
    3, 3, 9241, 3, 7, 3, 11, 3,
    157, 3, 7, 343243, 5, 3, 3, 13,
    3, 3, 73, 1249, 3, 3, 38921, 45322889,
    3, 5, 13, 3, 3, 3, 3, 3,
    66041, 3, 3, 3, 13, 5, 3, 5,
    112913, 3, 61879, 3, 3, 53, 24281, 3,
    3, 5, 3, 7, 3, 3, 11, 3,
    7, 3, 31, 29, 5, 3, 19780259, 3,
    3, 467, 3, 5, 14331881, 3, 30097, 3,
    37, 3, 6189607, 3, 3, 43, 3373, 3,
    5, 3, 5, 3, 3, 29, 13, 3,
    3, 2896903, 3, 3, 3, 23, 3, 3,
    5, 3, 3, 3, 37, 3, 683, 3,
    113, 3, 7, 3, 43, 17359, 347, 7,
    3, 3, 11, 3, 7, 3, 5, 3,
    13, 1223, 53, 3, 3, 3, 73, 3,
    31, 3, 5, 3, 277, 453367, 3, 61,
    11, 5, 227, 3, 3, 7, 5, 3,
    3, 71, 3, 5, 3, 59, 3, 3,
    5, 3, 7, 3, 5, 3, 23, 3,
    7, 6170387, 3588869, 3, 2903, 3, 3, 7,
    29, 3, 13, 11, 3, 5, 3, 19,
    5, 3, 3, 6323, 11, 5, 3, 3,
    5, 3, 739, 67, 3, 7, 3, 281,
    5, 17667523, 3, 3, 11, 3, 5, 3,
    3, 3, 5, 3, 971, 3, 5, 3,
    7, 3, 1171, 89, 3, 3, 7, 3,
    3, 131, 5, 3, 11, 3, 3, 5,
    3, 3, 3, 23, 13, 3, 1019, 137,
    3, 3, 3, 5, 11, 38039, 3, 7,
    3, 3, 5, 3, 23, 19, 937, 3,
    3, 47, 3, 11, 3, 5, 3, 3,
    13, 3, 5, 3, 3, 7, 41, 3,
    7, 3, 180907, 5, 3, 3, 3, 3,
    3, 5, 89, 843763, 3, 3, 3, 3,
    5, 3, 7, 5, 3, 19, 3, 3,
    7, 11, 2129, 3, 7, 43, 5, 557,
    3, 71, 3, 3, 13, 1663, 5, 3,
    3, 3, 3, 3, 5, 13, 3, 3,
    7, 5, 3, 151, 3, 3, 7, 5,
    3, 1759171, 19, 3, 3, 3, 5, 137321,
    3, 3, 5, 3, 3, 235877, 11, 3,
    7, 3, 23, 5, 97, 3, 3, 7,
    3, 5, 3, 3, 114659, 4099, 3, 3,
    3, 71699, 58278799, 5, 13, 3, 3, 271,
    3, 7, 3, 13, 1564183]

theorem prime_sub_5227 : Nat.Prime (3771671520132578 - 5227) := by
  show Nat.Prime 3771671520127351
  exact p3771671520127351

theorem check_5227 : allC 3771671520132578 5227 P10k ds_5227 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 3771671520132578 is 5227. -/
theorem minGB_S_5227 : minGB 3771671520132578 = 5227 :=
  minGB_eq_of P10k P10k_complete 3771671520132578 5227 (by norm_num) (by norm_num) prime_sub_5227 ds_5227 check_5227

def ds_5333 : List ℕ := [
    2, 11, 13, 3, 7, 3, 5, 3,
    31, 5471, 3, 3, 19, 3, 5, 7,
    2557, 3, 3, 54923291, 3, 3, 13, 17,
    3, 53, 3, 5, 3, 11, 3, 3633083,
    5, 3, 1015061, 3, 3, 3, 5, 157,
    7, 3, 17, 3, 5, 3, 3, 3,
    5, 3, 113, 13, 3, 69259, 5, 7,
    19, 3, 3, 23, 3, 17, 3, 11,
    3, 5, 3, 3, 5, 3, 198817, 67,
    3, 3, 3, 19, 7, 3, 3857983, 3,
    23, 3, 7, 3, 3, 11, 181, 3,
    1583, 3, 5, 211, 3, 43713877, 3, 29,
    11, 79, 3, 3, 3, 5, 37, 139,
    3, 3, 5, 43, 7, 3, 3, 3,
    5, 3, 3, 7, 3, 5, 167, 173,
    3, 3, 5, 7, 3, 17, 3, 3549701,
    3, 3, 3, 495109, 3, 3, 67, 3,
    11, 3, 5, 7, 3, 239, 3, 5,
    3, 11, 3, 5, 3, 13, 3, 6904613,
    3, 5, 3, 113, 3, 41, 3, 13,
    5, 19, 3, 11, 5, 941, 3, 3,
    3, 467, 7, 3, 271, 3, 3, 179,
    3, 7, 3, 3, 3, 7039, 3, 5,
    7, 17, 3, 3, 3, 733, 3, 67,
    3, 19, 5, 22229, 3, 3, 5, 18503,
    7, 3, 3, 3, 1571, 5, 3, 5101,
    443, 3, 3, 11, 3, 5, 23609, 3,
    3, 251, 5, 29, 3, 3, 13, 3,
    5, 3, 11, 7, 3, 37, 3, 3,
    3, 7, 3, 5, 3, 1247881, 11, 31,
    7, 3, 3, 3, 54180391, 4363, 3, 7518629,
    3, 28499, 3, 307, 5, 3, 18311, 17,
    3, 3, 5, 3, 3, 5, 3, 3,
    5, 3, 337, 13, 3, 7, 3, 3,
    3, 3, 3, 3, 5, 3, 3, 59,
    17, 3, 5, 3, 3, 73, 3, 5,
    3, 4310461, 7, 5, 41, 2791, 3, 1345033,
    3, 644669, 19, 3, 3, 5, 3, 723287,
    3, 3, 5, 3, 12510167, 3, 487, 7,
    1901, 3, 5, 3, 47, 7, 3, 17,
    3, 3, 43, 3, 7, 3, 3, 3,
    5, 23, 3, 5, 3, 29, 3, 5,
    3, 198223, 3, 3, 3, 5, 73, 3,
    17, 37, 3, 3, 23, 5, 3, 3,
    47, 3, 3, 314549, 43, 61, 5, 11,
    3, 31, 5, 46906753, 3, 3, 5, 3,
    3, 7, 3, 3767, 19, 3, 3, 13,
    29, 3, 1531, 3, 11, 26927, 3, 5,
    3, 19, 3, 3, 3, 5, 3, 158243,
    7, 3, 89, 3, 3, 2857, 3, 7,
    3, 11, 3, 5, 41128249, 3, 3, 191,
    3, 11, 3, 5, 17, 3, 3, 3221,
    131, 3, 5, 23, 7, 3, 5, 29,
    3, 5, 53, 13, 3, 31, 3, 211,
    3, 13691, 3, 23, 3, 3, 3, 3,
    11, 625529, 3, 7, 3, 5, 3, 5,
    3, 3, 3, 134293, 7, 373, 3, 5769791,
    3, 17, 3, 5, 3, 3, 41603, 3,
    3, 3, 3, 207551, 7, 3, 3, 5,
    13, 3, 7, 3, 41, 3, 5, 7,
    3, 37, 3, 19, 3, 5, 3, 1861,
    3, 3, 3, 5, 3, 19597, 7, 3,
    3, 5, 3, 3, 7, 3, 13, 3,
    3, 5, 7, 3, 3, 3, 17, 13,
    3, 5, 3, 3, 101, 3, 1193, 3,
    3, 3, 17, 5, 3, 89, 3, 5,
    19, 109, 3, 7, 3, 103, 3, 17,
    3, 41, 3, 3, 719, 5, 3, 11491,
    31, 3, 3, 5, 3, 10724387, 7, 3,
    5, 284593, 223, 3, 3, 691, 3, 3,
    11, 107, 223831, 3, 3, 3, 5, 3,
    24889, 11, 3, 5, 3, 3, 3, 7,
    5, 3, 2741, 3, 61, 3, 7, 19,
    3, 11, 3, 23, 59, 3, 3, 5,
    3, 257, 3, 3, 13, 419, 5, 3011,
    7, 3, 3, 3, 13, 5, 7, 4380287,
    3, 22133, 3, 3, 5, 3, 457, 5,
    3, 3, 3, 2687, 3, 3, 3, 3,
    5, 3, 59, 71, 3, 3, 3, 7,
    17, 421, 877, 43, 3, 3, 11, 1230347,
    3, 3, 5, 3, 181, 7, 3, 3,
    5, 3, 3, 53, 5, 29031143, 3, 3,
    13, 11, 3, 5, 19, 3, 3, 5,
    3, 23, 3, 3, 3, 37, 7, 3,
    937, 3, 4286803, 7, 3, 3, 34649, 5,
    12109, 3, 3, 3, 3, 5, 13, 3,
    19, 3, 17, 3, 3, 3, 13, 3,
    5, 7, 9664903, 313, 3, 5, 7, 13,
    3]

theorem prime_sub_5333 : Nat.Prime (4463039219937862 - 5333) := by
  show Nat.Prime 4463039219932529
  exact p4463039219932529

theorem check_5333 : allC 4463039219937862 5333 P10k ds_5333 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 4463039219937862 is 5333. -/
theorem minGB_S_5333 : minGB 4463039219937862 = 5333 :=
  minGB_eq_of P10k P10k_complete 4463039219937862 5333 (by norm_num) (by norm_num) prime_sub_5333 ds_5333 check_5333

def ds_5471 : List ℕ := [
    2, 5, 37, 3, 53, 3, 11, 3,
    5, 199, 3, 3, 13, 3, 67, 5,
    5639, 3, 3, 599, 3, 3, 5, 17,
    3, 1489, 3, 7, 3, 5, 3, 41,
    107, 3, 7, 3, 3, 3, 31379, 5,
    1097, 3, 7, 3, 13, 3, 3, 3,
    37, 3, 5, 103, 3, 2833, 43, 5,
    31, 3, 3, 11, 3, 5, 3, 167,
    3, 7, 3, 3, 11, 3, 5, 7,
    3, 3, 3, 5, 449, 3, 7, 3,
    83, 3, 13, 3, 3, 5, 37, 3,
    4483, 3, 211, 11, 3, 19, 3, 5,
    13, 137, 3, 3, 3, 3109, 5, 7,
    3, 3, 13, 5, 17, 3, 3, 3,
    3119, 3, 3, 31, 3, 29, 5, 63977,
    3, 3, 11, 5, 3, 17, 3, 19,
    3, 3, 3, 5, 3, 3, 463, 3,
    5, 3, 5875631, 11, 3, 7, 3, 31,
    3, 59, 3, 103, 3, 5, 3, 37397,
    3, 4848091, 3, 1367, 3, 8807, 3, 11,
    7, 5, 3, 349, 13, 5, 3, 3,
    3, 5, 33889, 3, 7, 3, 3, 269,
    3, 19, 3, 3, 3, 263, 3, 1831,
    5, 17, 3, 3, 3, 19333, 3, 5,
    3, 1867, 97, 5, 3, 3, 89, 5,
    3343, 3, 3, 3, 23, 601, 3, 5,
    13, 3, 3, 683, 3, 201037, 383, 3,
    3, 41, 7, 5, 3, 3, 7, 3,
    37117, 3, 5, 53183971, 3, 7, 3, 3,
    3, 503, 3, 71, 3, 5, 353, 1409,
    5, 3, 3, 3, 5, 37, 3, 31,
    3, 5, 3, 11, 41, 3, 5, 7,
    3, 3, 191, 3, 3, 11, 3, 3,
    34021297, 3, 487, 17, 3, 5, 3, 3,
    3, 3, 3, 3, 7, 3, 3, 23,
    5, 3, 307, 3, 3, 7, 3, 491,
    3, 439, 59, 178127, 5, 11, 3, 23,
    3, 5, 109, 3, 3, 7, 3, 5,
    3, 3, 17, 3, 7, 3, 5, 13,
    7, 3, 19, 3, 41, 173, 3, 11,
    3, 3, 17020117, 3, 5, 3, 3, 3,
    7, 5, 3, 53, 3, 5, 3, 1800301,
    3, 5, 3, 3, 3, 241, 479, 3,
    5, 71, 3, 3, 97, 919, 3, 3,
    13, 3, 3, 5, 73, 61, 7, 5,
    3, 2351, 37, 7, 3, 3, 1123, 3,
    3, 1609, 3, 5, 1634441, 3, 3, 43,
    11, 3, 59, 3, 1039, 5, 3, 11,
    3, 5, 3, 3, 3, 31, 3, 5,
    24133, 3, 7, 3, 3, 7081099, 3, 17,
    3, 5, 3, 23, 11, 3, 3, 1163,
    3, 89, 3, 7, 5, 3, 3, 67,
    7, 3, 1229, 5, 29, 3, 13, 1466293,
    3, 113, 5, 227, 3, 19, 3, 389,
    3, 5, 3, 15798791, 3, 3, 3, 3,
    5, 7, 3, 11, 3, 1201, 3, 23265103,
    3, 3, 3, 23, 5, 1019, 3, 157,
    3, 11, 3, 7, 3, 3, 7, 3,
    3, 3, 3, 5, 23, 3, 3, 107,
    27631, 3, 47, 3, 7257721, 3, 83, 5,
    3, 11, 3, 10627, 3, 7, 3, 7841863,
    3, 3, 3, 317, 3, 5, 463, 3,
    3, 17, 3, 3, 11, 3, 5, 3,
    3, 31, 5, 3, 3, 3, 17, 59,
    3, 7, 3, 3, 3566701, 3, 7, 3,
    3, 3, 7, 149, 3, 11, 3, 19,
    5, 41, 3, 5, 3, 197, 3, 5,
    3, 23, 3, 3, 11, 563, 3, 5,
    7, 3, 3, 103, 3, 31, 37, 3,
    7933, 5, 13, 3, 3, 397, 3, 3,
    5, 239, 1471, 3, 3, 3, 29, 3,
    5, 7, 3, 23, 3, 3, 3, 249881,
    47, 3, 23173, 3, 11, 3, 5, 117371,
    3, 17, 3, 5, 101, 3, 3, 73609,
    3, 7, 3, 3, 5, 7, 27011, 13,
    89, 3, 3, 3, 167173, 3791233, 5, 19,
    3, 5, 3, 3, 7, 3, 5, 31,
    3, 3, 3, 5, 3, 3, 3, 3,
    11, 3, 5, 29, 3, 3, 3, 5,
    17, 419, 5, 13, 3, 3, 5, 14087,
    3, 3, 541, 3, 5, 13, 3, 3,
    5897, 3, 3, 67, 13, 37, 3, 3,
    31, 773, 3, 7, 5, 3, 3, 11,
    3, 5, 3, 3, 3, 5, 1291, 3,
    7, 3, 685039, 19, 3, 3, 3061, 17,
    11, 3, 3, 3, 3, 7, 5, 3,
    29, 3, 7, 3, 3, 3, 7, 3,
    1049, 23, 5, 19, 3, 11, 5, 65719,
    3, 5, 3, 35353, 3851, 18013, 5, 7,
    3, 3, 43, 3, 3, 3, 7, 3,
    3]

theorem prime_sub_5471 : Nat.Prime (5122498676196358 - 5471) := by
  show Nat.Prime 5122498676190887
  exact p5122498676190887

theorem check_5471 : allC 5122498676196358 5471 P10k ds_5471 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 5122498676196358 is 5471. -/
theorem minGB_S_5471 : minGB 5122498676196358 = 5471 :=
  minGB_eq_of P10k P10k_complete 5122498676196358 5471 (by norm_num) (by norm_num) prime_sub_5471 ds_5471 check_5471

def ds_5483 : List ℕ := [
    2, 7, 31, 3, 5, 3, 7, 3,
    37907, 4243, 3, 3, 5, 3, 11, 171049,
    7, 3, 3, 5, 3, 3, 17, 56577791,
    3, 5, 3, 54377, 3, 11, 3, 5,
    29, 3, 23, 3, 3, 3, 1616597, 55469,
    11, 3, 5, 3, 193, 3, 3, 3,
    7, 3, 13, 37, 3, 5, 13033, 61,
    7, 3, 3, 5, 3, 487, 3, 5,
    3, 521, 3, 3, 79, 3, 7, 709,
    3, 3, 3, 19, 13, 3, 5, 3,
    1193, 3, 5, 3, 3, 11, 463, 3,
    5, 3, 13, 7, 3, 5, 3, 1733,
    11, 5, 3, 3, 3, 47, 7, 109,
    3, 3, 157, 17, 137, 3, 3, 3,
    4483, 3, 3, 5, 3, 7, 73, 29,
    3, 3, 30164461, 37, 3, 5, 3, 7155383,
    3, 3, 3, 77417, 3, 3, 5, 3,
    7, 3, 17, 631, 3, 5, 3, 59,
    3, 11, 3, 7, 3, 211, 3, 5,
    3, 6311, 3, 5, 3, 103, 3, 5,
    601, 19, 3, 5, 23, 7, 3, 3,
    3, 13, 41, 3, 5, 3, 3, 43,
    3, 5, 3, 3, 3, 5, 3, 95479,
    11, 7, 3, 3, 3, 5, 3, 149,
    3, 5, 1319, 7, 3, 3, 13009, 109,
    34919, 3, 3, 3, 941, 7, 3, 6121,
    5323, 3, 3, 5, 3, 17, 7, 3,
    3, 5, 11, 113, 3, 3, 17, 3,
    8117, 3, 11, 85703, 3, 5, 3, 3,
    3, 5, 3, 7, 3, 31, 11, 5,
    19, 3, 3, 3, 18263249, 13, 3, 5,
    3, 149543, 3, 5, 179, 3, 7, 197,
    3, 3, 13, 3, 3, 23, 3, 3,
    7, 3, 51864419, 5, 3, 10979, 3, 3,
    3, 3, 3, 3, 2174119, 3, 3, 5,
    7, 3, 4468171, 3, 3, 5, 3, 29,
    3, 59, 5, 7, 7883, 5, 3, 7,
    3, 337, 19, 3, 3, 379, 3, 41,
    3, 3, 11, 3, 38541523, 3, 6719, 49547,
    5, 3, 1851859, 3, 71, 5, 3, 211,
    3, 3, 5, 3, 8179, 3, 3, 3,
    19, 67, 3, 31, 3, 7, 3, 104579,
    3, 587, 3, 3, 3, 947, 107, 3,
    14327, 13, 3, 3, 5, 11, 3, 3,
    5, 3, 3, 2179, 29, 5, 13, 11,
    3, 5, 3593, 37, 3, 3, 62989, 3,
    3, 5, 3, 33117599, 19, 3, 3, 7,
    5, 3, 31, 3, 5, 17, 3, 2357,
    3, 7, 3, 3, 3, 11, 3, 150223,
    1884563, 3, 5, 3, 3, 13, 3, 5,
    3, 11, 3, 19, 7, 3, 3, 5,
    3, 11, 3, 17, 73, 3, 3, 5,
    1721, 3, 557, 37, 23, 3, 287239, 17,
    3, 7, 13, 89, 3, 7, 3, 5,
    3, 17239, 3, 5, 3, 3, 3, 3,
    7, 1451, 3, 13, 3, 25661773, 3, 7,
    3, 3, 3, 5, 142771, 7, 3, 5,
    3, 5, 3, 307, 3, 3, 979337, 3,
    3, 3, 3, 23, 2377, 3, 3, 11,
    18177541, 3, 5, 3, 4937, 3, 113, 11,
    3, 17, 3, 5, 3, 167, 3, 5,
    3, 3, 3, 2731, 3, 25874767, 31, 3,
    3, 61, 3, 3, 5, 3, 107, 3,
    3, 29, 239, 3, 3, 3, 47, 5,
    3, 11, 3, 3, 5, 3, 73, 3,
    3, 3, 5, 3191, 3, 97, 3, 7,
    19, 5, 3, 84163, 3, 5, 3, 659,
    3, 5, 3, 3, 5, 19, 3, 7,
    9629, 3, 3, 661, 3, 1031, 5, 3,
    7, 23, 103, 3, 3, 7, 3, 3,
    11, 199, 5, 3, 3, 3, 35731, 3,
    7, 11, 3, 73, 3, 3, 3, 5,
    7, 3, 71, 3, 5, 3, 1091, 7,
    3, 5, 3, 31, 13, 3, 3, 11,
    3, 53, 3, 3, 19, 5, 227, 3313,
    5, 3, 3, 3, 5, 37, 41, 5,
    3, 109, 3, 3, 623869, 3, 13, 11681,
    3, 3, 3, 467, 3, 3, 3, 3,
    7, 3, 20089, 457, 3, 3, 3, 17,
    7, 5, 23, 5, 3, 3, 11, 5,
    3, 3, 47, 3, 127, 11, 3, 3,
    236609, 3, 3, 5, 17, 7, 3, 3,
    43, 5, 3, 62552899, 19, 3, 3, 1151,
    3, 7, 3, 3, 3, 1494659, 29, 3,
    5, 3, 541, 5, 3, 3, 5, 79,
    7, 3, 3, 3, 3, 13, 571, 3,
    5, 3, 1693, 3, 3, 3, 5, 3,
    73613, 5, 199, 12413, 3, 157, 13, 7,
    3, 1749071, 3, 5, 5, 17, 7, 19,
    3, 3, 31547, 3, 3, 3, 5, 3,
    3, 5, 7, 3]

theorem prime_sub_5483 : Nat.Prime (6198478168628056 - 5483) := by
  show Nat.Prime 6198478168622573
  exact p6198478168622573

theorem check_5483 : allC 6198478168628056 5483 P10k ds_5483 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 6198478168628056 is 5483. -/
theorem minGB_S_5483 : minGB 6198478168628056 = 5483 :=
  minGB_eq_of P10k P10k_complete 6198478168628056 5483 (by norm_num) (by norm_num) prime_sub_5483 ds_5483 check_5483

def ds_5501 : List ℕ := [
    2, 13, 41617, 3, 29, 3, 117571, 3,
    7, 5, 3, 3, 73, 3, 16747, 977,
    5, 3, 3, 17, 3, 3, 31, 5,
    3, 11, 3, 7, 3, 251, 3, 241,
    71, 3, 5, 3, 3, 3, 11, 17,
    5, 3, 7, 3, 311, 3, 3, 3,
    691, 3, 7, 5, 3, 379, 11927, 13,
    5, 3, 3, 97, 3, 56983, 3, 23,
    3, 7, 3, 3, 41, 3, 43, 5,
    3, 3, 3, 17569, 5, 3, 7, 3,
    5, 3, 11, 3, 3, 7, 5, 3,
    765439, 3, 281, 5, 3, 971, 3, 211,
    5, 191, 3, 3, 3, 54679, 11, 5,
    3, 3, 23, 41, 5, 3, 3, 3,
    74449, 3, 3, 19, 3, 17011, 7, 5,
    3, 3, 147769, 17, 3, 57529, 3, 5,
    3, 3, 3, 410497, 3, 3, 11, 3,
    229, 3, 79, 5, 3, 7, 3, 11,
    3, 5, 3, 1259, 3, 7, 3, 29,
    3, 13, 3, 28297, 3, 5, 3, 181,
    7, 43067, 3, 9433, 829, 19, 3, 3,
    3, 31, 5, 3, 7, 3, 3, 5,
    3, 587, 3, 3, 3, 11, 3, 19,
    23486677, 5, 3, 3, 3, 823, 3, 127,
    3, 347, 606041, 17, 3, 3, 67, 11,
    5, 3, 3, 3, 5, 13, 3, 7,
    5, 3, 3, 3169, 3, 2213, 5, 3,
    3, 144583, 7, 467, 3, 3, 5, 3,
    349, 3, 13, 5, 3, 7, 3, 3,
    3, 47, 3, 11, 3, 7, 5, 13,
    1103, 3, 3, 3, 11, 5, 3, 31,
    3, 89, 3, 17, 1166969, 3, 269, 5,
    3, 3, 593, 3, 3, 13, 3, 3,
    61, 3, 5, 3487661, 3, 33617, 3, 3,
    3, 3, 3, 3, 7, 3, 3, 131,
    13, 3, 11503, 3, 3, 7, 3, 76603,
    3, 5, 13, 17, 7, 10513, 3, 5,
    3, 2549, 5, 3, 3, 7, 3, 5227219,
    3, 3, 97, 3, 5, 3, 61, 5,
    7, 3, 683083, 3, 5, 17, 3, 5,
    3, 3, 96737, 3, 281, 3, 3, 3,
    7, 11, 3, 19, 3, 23, 3, 71,
    3, 29, 3, 3, 3, 8447611, 5, 3,
    7, 5, 3, 3, 19, 43063, 3, 3,
    23, 3, 3, 4733, 5, 11, 7, 67,
    3, 193, 13, 5, 3, 3, 11, 3,
    3, 896879, 3, 7, 5, 3, 3, 5,
    137, 3, 5, 3, 17, 157, 3, 23,
    3, 8069, 3, 3, 3, 31, 3, 19,
    5, 3, 7, 3, 3, 5, 3, 11,
    3, 7, 3, 397, 5, 3, 3, 113,
    3, 5, 3, 7, 63866993, 3, 3, 673,
    5, 3, 313, 389, 5, 3, 17, 5,
    3, 20011, 7, 5, 3, 5, 3, 1373,
    3, 241, 3, 149, 3, 3, 3, 3,
    2921761, 5, 3, 5, 3, 11, 3, 79,
    3, 3, 3, 43, 11, 5, 3, 166867,
    3, 101769379, 3, 7, 3, 3, 5, 3,
    3, 3, 3, 619, 5, 3, 3, 23,
    5, 3, 101, 3, 5, 3, 1164817, 137,
    3, 5, 3, 13, 3, 7, 3, 19,
    3, 3, 3, 61, 3, 11, 5, 3,
    3, 223, 3, 3, 53, 3, 7, 3,
    3, 13, 23, 3, 3, 3, 5, 463207,
    3, 7, 3, 3, 1069, 3, 5, 3,
    3, 3, 7, 1135751, 3, 5, 3, 11,
    7, 617, 3, 19, 3, 13, 3, 11,
    3, 1381, 3, 3, 5711557, 569, 3, 683,
    5, 3, 3, 17, 3, 5, 23041, 3,
    13, 7, 5, 3, 3, 5, 3, 3,
    419561, 5, 8787001, 3, 3, 3, 11, 3,
    359, 5, 3, 113, 3, 3, 3, 127,
    53, 3, 5, 3, 13, 3, 17, 5,
    3, 353, 3, 41, 5, 3, 3, 8863,
    3, 5, 3, 3, 691, 7, 13, 5,
    73, 3, 3, 3, 23, 11, 59, 43,
    3, 107, 3, 3, 7, 3, 11, 31,
    3, 3, 3, 47, 3, 3, 3, 3,
    421, 3, 7, 5, 3, 3, 3, 4363,
    5, 207877, 821, 11, 3, 3, 31, 83,
    3, 3, 11, 3, 54631, 5, 3, 3,
    59, 3, 3, 24346313, 3010643, 5, 3, 3,
    5, 43909771, 3, 7, 13, 3, 3, 17,
    3, 19, 3, 3, 3, 23, 5, 3,
    7, 3, 5, 11, 3, 3, 151, 19,
    5, 3, 3, 3, 3, 7, 78511, 3,
    17, 3, 5, 3, 3, 3, 7, 3,
    67, 31081, 7, 5, 3, 73, 4013, 5,
    3, 13, 3, 16398491, 11, 2339, 3643, 5,
    3, 3, 23, 3, 3, 3, 7, 3,
    3, 1789, 17, 3, 7]

theorem prime_sub_5501 : Nat.Prime (14211744403075144 - 5501) := by
  show Nat.Prime 14211744403069643
  exact p14211744403069643

theorem check_5501 : allC 14211744403075144 5501 P10k ds_5501 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 14211744403075144 is 5501. -/
theorem minGB_S_5501 : minGB 14211744403075144 = 5501 :=
  minGB_eq_of P10k P10k_complete 14211744403075144 5501 (by norm_num) (by norm_num) prime_sub_5501 ds_5501 check_5501

def ds_5879 : List ℕ := [
    2, 283, 7, 3, 359, 3, 5, 3,
    11, 37, 3, 3, 33469, 3, 5, 31,
    251, 3, 3, 20483, 3, 3, 239, 7,
    3, 2003, 3, 5, 3, 13, 3, 7,
    5, 3, 21655883, 3, 3, 3, 5, 7,
    4889, 3, 13, 3, 5, 3, 3, 3,
    5, 3, 181, 31, 3, 37, 5, 124183,
    13, 3, 3, 5364559, 3, 109, 3, 61,
    3, 5, 3, 3, 5, 3, 11, 193,
    3, 3, 3, 7, 1523, 3, 17, 3,
    11, 3, 127, 3, 3, 62131, 5450437, 3,
    701, 3, 5, 53069, 3, 41, 3, 13,
    7, 149, 3, 3, 3, 5, 4297, 29,
    3, 3, 5, 7, 5557, 3, 3, 3,
    5, 3, 3, 1667, 3, 5, 751, 13,
    3, 3, 5, 11, 3, 52052509, 3, 7,
    3, 3, 3, 29, 3, 3, 7, 3,
    24007, 3, 5, 17, 3, 23, 3, 5,
    3, 44839, 3, 5, 3, 331, 3, 11,
    3, 5, 3, 17, 3, 7, 3, 53,
    5, 293, 3, 7, 5, 31, 3, 3,
    3, 7, 2087, 3, 77713, 3, 3, 13,
    3, 229, 3, 3, 3, 29, 3, 5,
    19, 1099619, 3, 3, 3, 1097, 3, 7365439,
    3, 7, 5, 127, 3, 3, 5, 7,
    41, 3, 3, 3, 53, 5, 3, 13,
    8923, 3, 3, 6481, 3, 5, 17, 3,
    3, 13, 5, 23, 3, 3, 11, 3,
    5, 3, 7, 13, 3, 463, 3, 3,
    3, 18131, 3, 5, 3, 59009, 21649, 23,
    17, 3, 3, 3, 409, 7, 3, 57571,
    3, 37, 3, 7, 5, 3, 29, 6607,
    3, 3, 5, 3, 3, 5, 3, 3,
    5, 3, 233, 41, 3, 604859, 3, 3,
    3, 3, 3, 3, 5, 3, 3, 7,
    1741, 3, 5, 3, 3, 11, 3, 5,
    3, 757, 19, 5, 31, 17, 3, 47,
    3, 1213481, 7, 3, 3, 5, 3, 11,
    3, 3, 5, 3, 4590667, 3, 7, 11,
    191, 3, 5, 3, 31, 919, 3, 19,
    3, 3, 13, 3, 113, 3, 3, 3,
    5, 41, 3, 5, 3, 19, 3, 5,
    3, 7, 3, 3, 3, 5, 29, 3,
    11, 17, 3, 3, 167, 5, 3, 3,
    593, 3, 3, 117043, 7, 125527, 5, 457,
    3, 7, 5, 41, 3, 3, 5, 3,
    3, 11, 3, 17, 2531, 3, 3, 18545069,
    2153, 3, 7, 3, 1201729, 5233, 3, 5,
    3, 11, 3, 3, 3, 5, 3, 7,
    19, 3, 103, 3, 3, 11, 3, 8867,
    3, 23, 3, 5, 211, 3, 3, 5469463,
    3, 7, 3, 5, 13, 3, 3, 7,
    137, 3, 5, 7, 109, 3, 5, 440227,
    3, 5, 607, 41953, 3, 13, 3, 73,
    3, 12301, 3, 19, 3, 3, 3, 3,
    787, 81173, 3, 1009, 3, 5, 3, 5,
    3, 3, 3, 11, 149, 199, 3, 379,
    3, 7561, 3, 5, 3, 3, 13399, 3,
    3, 3, 3, 7, 103, 3, 3, 5,
    17, 3, 169321, 3, 11, 3, 5, 101,
    3, 7, 3, 17, 3, 5, 3, 7,
    3, 3, 3, 5, 3, 7, 4759, 3,
    3, 5, 3, 3, 23, 3, 509, 3,
    3, 5, 13, 3, 3, 3, 7, 10867,
    3, 5, 3, 3, 7, 3, 11, 3,
    3, 3, 3229, 5, 3, 13, 3, 5,
    37, 691, 3, 193, 3, 11, 3, 1193,
    3, 71, 3, 3, 7, 5, 3, 47,
    11867, 3, 3, 5, 3, 997, 438983, 3,
    5, 13, 101, 3, 3, 11, 3, 3,
    17, 7, 13, 3, 3, 3, 5, 3,
    23, 179, 3, 5, 3, 3, 3, 7113839,
    5, 3, 463, 3, 127, 3, 227, 2129,
    3, 23, 3, 2957, 7, 3, 3, 5,
    3, 24169, 3, 3, 7, 83, 5, 19,
    22037, 3, 3, 3, 401, 5, 443, 13,
    3, 2851, 3, 3, 5, 3, 19, 5,
    3, 3, 3, 7, 3, 3, 3, 3,
    5, 3, 11, 541889, 3, 3, 3, 41,
    277, 37, 31, 2011, 3, 3, 71, 7,
    3, 3, 5, 3, 7, 107, 3, 3,
    5, 3, 3, 13, 5, 17, 3, 3,
    7, 3319, 3, 5, 223, 3, 3, 5,
    3, 11, 3, 3, 3, 7, 389, 3,
    759637, 3, 11, 47, 3, 3, 213193, 5,
    23, 3, 3, 3, 3, 5, 307, 3,
    7, 3, 4751, 3, 3, 3, 101, 3,
    5, 13, 353, 49193, 3, 5, 11, 96527,
    3, 47, 3, 260387, 7, 5, 53, 17,
    3, 3, 5, 3, 3, 3, 29, 3,
    3, 59, 5, 3, 11093, 11, 3, 5,
    131, 3, 3, 1049, 3, 3, 3, 13,
    3, 7, 3, 73, 3, 3, 13, 3,
    5, 3, 11743, 3, 3, 1297, 3, 53,
    5, 3, 760871, 3, 3, 3, 853, 3,
    7, 5, 139, 3, 3, 3, 7, 173,
    3, 3, 79, 5, 3]

theorem prime_sub_5879 : Nat.Prime (15812379959645512 - 5879) := by
  show Nat.Prime 15812379959639633
  exact p15812379959639633

theorem check_5879 : allC 15812379959645512 5879 P10k ds_5879 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 15812379959645512 is 5879. -/
theorem minGB_S_5879 : minGB 15812379959645512 = 5879 :=
  minGB_eq_of P10k P10k_complete 15812379959645512 5879 (by norm_num) (by norm_num) prime_sub_5879 ds_5879 check_5879

def ds_5903 : List ℕ := [
    2, 73, 11, 3, 97, 3, 13, 3,
    338197, 5, 3, 3, 7, 3, 26339, 19,
    5, 3, 3, 11, 3, 3, 7, 5,
    3, 1787, 3, 15739, 3, 107, 3, 1301,
    11, 3, 5, 3, 3, 3, 7, 13,
    5, 3, 79, 3, 4271, 3, 3, 3,
    12703, 3, 157, 5, 3, 7, 4952371, 6703,
    5, 3, 3, 19, 3, 7, 3, 227,
    3, 127, 3, 3, 61, 3, 23, 5,
    3, 3, 3, 151, 5, 3, 11, 3,
    5, 3, 45737, 3, 3, 17, 5, 3,
    7, 3, 11, 5, 3, 23, 3, 7,
    5, 211, 3, 3, 3, 229, 13, 5,
    3, 3, 7, 97, 5, 3, 3, 3,
    92987, 3, 3, 13, 3, 17, 479, 5,
    3, 3, 103, 359, 3, 29, 3, 5,
    3, 3, 3, 1453, 3, 3, 769, 3,
    1009, 3, 7, 5, 3, 149627, 3, 277,
    3, 5, 3, 449, 3, 11, 3, 7,
    3, 338027, 3, 263, 3, 5, 3, 41,
    91097, 13, 3, 53513567, 19507, 1049, 3, 3,
    3, 59, 5, 3, 13, 3, 3, 5,
    3, 11, 3, 3, 3, 7, 3, 2711,
    43, 5, 3, 3, 3, 131, 3, 2909,
    3, 23, 13, 11, 3, 3, 7, 29,
    5, 3, 3, 3, 5, 716447, 3, 383,
    5, 3, 3, 7, 3, 19, 5, 3,
    3, 17, 59, 29867, 3, 3, 5, 3,
    7, 3, 41, 5, 3, 173, 3, 3,
    3, 31, 3, 47, 3, 14081, 5, 7,
    11, 3, 3, 3, 7, 5, 3, 29,
    3, 83, 3, 641, 269, 3, 79, 5,
    3, 3, 7, 3, 3, 17, 3, 3,
    37, 3, 5, 7, 3, 13, 3, 3,
    3, 3, 3, 3, 11, 3, 3, 13,
    487, 3, 7, 3, 3, 17, 3, 19,
    3, 5, 73, 10111, 103, 7, 3, 5,
    3, 7, 5, 3, 3, 14341, 3, 3923,
    3, 3, 101, 3, 5, 3, 3221, 5,
    83, 3, 79, 3, 5, 9281, 3, 5,
    3, 3, 7, 3, 167, 3, 3, 3,
    1117, 53, 3, 509, 3, 583789, 3, 7,
    3, 293, 3, 3, 3, 4261, 5, 3,
    19, 5, 3, 3, 7, 13, 3, 3,
    11, 3, 3, 7, 5, 31, 41, 23,
    3, 29, 11, 5, 3, 3, 7, 3,
    3, 53, 3, 61, 5, 3, 3, 5,
    13, 3, 5, 3, 181, 67, 3, 6379,
    3, 41, 3, 3, 3, 7, 3, 25237,
    5, 3, 11, 3, 3, 5, 3, 3733,
    3, 139, 3, 11, 5, 3, 3, 81853,
    3, 5, 3, 23, 11, 3, 3, 3787351,
    5, 3, 7, 13, 5, 3, 179, 5,
    3, 199, 29, 5, 3, 5, 3, 89,
    3, 7, 3, 11, 3, 3, 3, 3,
    5801, 5, 3, 5, 3, 13, 3, 43,
    3, 3, 3, 7, 317599, 5, 3, 269,
    3, 23, 3, 3229, 3, 3, 5, 3,
    3, 3, 3, 107, 5, 3, 3, 719,
    5, 3, 11, 3, 5, 3, 132439, 52747,
    3, 5, 3, 47, 3, 2039, 3, 59,
    3, 3, 3, 7, 3, 36739, 5, 3,
    3, 615521, 3, 3, 137, 3, 1151, 3,
    3, 881, 45007, 3, 3, 3, 5, 673,
    3, 433, 3, 3, 11, 3, 5, 3,
    3, 3, 13, 11, 3, 5, 3, 569,
    23, 7, 3, 11, 3, 571, 3, 7,
    3, 27883, 3, 3, 17, 13, 3, 62355173,
    5, 3, 3, 7, 3, 5, 157, 3,
    29, 17, 5, 3, 3, 5, 3, 3,
    7, 5, 73, 3, 3, 3, 127, 3,
    929, 5, 3, 7, 3, 3, 3, 3741833,
    17, 3, 5, 3, 7, 3, 1526089, 5,
    3, 19, 3, 7, 5, 3, 3, 3691,
    3, 5, 3, 3, 61, 5519, 227, 5,
    17, 3, 3, 3, 7, 31, 13, 463,
    3, 7, 3, 3, 8893, 3, 17, 7691,
    3, 3, 3, 37, 3, 3, 3, 3,
    84729041, 3, 31, 5, 3, 3, 3, 22567,
    5, 11, 7, 251, 3, 3, 547, 10639,
    3, 3, 7, 3, 181, 5, 3, 3,
    643, 3, 3, 7, 29, 5, 3, 3,
    5, 13, 3, 14524777, 157, 3, 3, 73,
    3, 43, 3, 3, 3, 103, 5, 3,
    11, 3, 5, 29, 3, 3, 7, 11,
    5, 3, 3, 3, 3, 89, 11, 3,
    787, 3, 5, 3, 3, 3, 43, 3,
    17, 59, 18181, 5, 3, 19, 12792929, 5,
    3, 7, 3, 11, 99991, 31, 53, 5,
    3, 3, 7, 3, 3, 3, 17, 3,
    3, 37, 13, 3, 11, 7, 3, 4157,
    5, 3, 3, 4339, 3, 3, 3, 29,
    3, 71, 3, 5, 3, 3, 127, 3,
    18973, 3, 5, 3, 3, 37, 3, 7,
    47, 3, 1783, 3, 3, 3, 271, 3,
    17881999, 991, 11, 3, 3, 3, 73, 5,
    3, 3, 41, 13, 3, 5, 3, 311]

theorem prime_sub_5903 : Nat.Prime (20017986381370774 - 5903) := by
  show Nat.Prime 20017986381364871
  exact p20017986381364871

theorem check_5903 : allC 20017986381370774 5903 P10k ds_5903 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 20017986381370774 is 5903. -/
theorem minGB_S_5903 : minGB 20017986381370774 = 5903 :=
  minGB_eq_of P10k P10k_complete 20017986381370774 5903 (by norm_num) (by norm_num) prime_sub_5903 ds_5903 check_5903

def ds_5987 : List ℕ := [
    2, 277, 31, 3, 1231, 3, 215329, 3,
    4157, 5, 3, 3, 13, 3, 3061, 70948037,
    5, 3, 3, 7, 3, 3, 19, 5,
    3, 31267, 3, 29, 3, 7, 3, 11,
    163, 3, 5, 3, 3, 3, 16189, 5867,
    5, 3, 31, 3, 7, 3, 3, 3,
    167, 3, 97, 5, 3, 61, 47, 11,
    5, 3, 3, 7, 3, 21221, 3, 19,
    3, 887, 3, 3, 59, 3, 13, 5,
    3, 3, 3, 17, 5, 3, 1811, 3,
    5, 3, 13, 3, 3, 443, 5, 3,
    11, 3, 1165357, 5, 3, 7, 3, 43,
    5, 563, 3, 3, 3, 53, 31, 5,
    3, 3, 13, 11, 5, 3, 3, 3,
    7, 3, 3, 16007, 3, 479, 19, 5,
    3, 3, 142169, 619, 3, 7, 3, 5,
    3, 3, 3, 7, 3, 3, 43, 3,
    161329891, 3, 3050381, 5, 3, 13, 3, 7,
    3, 5, 3, 11, 3, 41, 3, 19,
    3, 4831, 3, 7, 3, 5, 3, 89,
    73, 7, 3, 149, 13, 61, 3, 3,
    3, 2041937, 5, 3, 23, 3, 3, 5,
    3, 108991, 3, 3, 3, 839, 3, 17,
    47, 5, 3, 3, 3, 29, 3, 7,
    3, 41890487, 11, 53, 3, 3, 3720407, 19,
    5, 3, 3, 3, 5, 43, 3, 4507,
    5, 3, 3, 17, 3, 23, 5, 3,
    3, 101, 13, 7, 3, 3, 5, 3,
    331501, 3, 1327, 5, 3, 11, 3, 3,
    3, 8053, 3, 200383, 3, 31, 5, 53,
    13, 3, 3, 3, 929, 5, 3, 1951,
    3, 7, 3, 13, 17, 3, 4967, 5,
    3, 3, 127, 3, 3, 7, 3, 3,
    2579, 3, 5, 23, 3, 5283059, 3, 3,
    3, 3, 3, 3, 173, 3, 3, 17,
    73, 3, 11, 3, 3, 985177, 3, 7,
    3, 5, 281, 19, 11, 15679, 3, 5,
    3, 1452413, 5, 3, 3, 23, 3, 7,
    3, 3, 2609, 3, 5, 3, 181, 5,
    61, 3, 7, 3, 5, 11, 3, 5,
    3, 3, 293, 3, 131, 3, 3, 3,
    43023143, 7, 3, 31, 3, 11, 3, 7129,
    3, 23, 3, 3, 3, 7, 5, 3,
    433241, 5, 3, 3, 67, 12763, 3, 3,
    7, 3, 3, 659, 5, 23, 609113, 7,
    3, 11, 61, 5, 3, 3, 19, 3,
    3, 109, 3, 29, 5, 3, 3, 5,
    7, 3, 5, 3, 457, 7, 3, 79,
    3, 89612687, 3, 3, 3, 23, 3, 13,
    5, 3, 199, 3, 3, 5, 3, 263,
    3, 67, 3, 239, 5, 3, 3, 7,
    3, 5, 3, 11, 7, 3, 3, 1187,
    5, 3, 130517, 11, 5, 3, 7, 5,
    3, 3359, 23, 5, 3, 5, 3, 7,
    3, 229, 3, 3631, 3, 3, 3, 3,
    13, 5, 3, 5, 3, 7, 3, 11,
    3, 3, 3, 108343, 113, 5, 3, 7,
    3, 1283, 3, 7498999, 3, 3, 5, 3,
    3, 3, 3, 41, 5, 3, 3, 7,
    5, 3, 971, 3, 5, 3, 271, 29,
    3, 5, 3, 8780159, 3, 641, 3, 37,
    3, 3, 3, 48239, 3, 59, 5, 3,
    3, 7, 3, 3, 636851, 3, 10896653, 3,
    3, 19, 7559, 3, 3, 3, 5, 2486287,
    3, 122743, 3, 3, 2393, 3, 5, 3,
    3, 3, 11, 7, 3, 5, 3, 103,
    71, 34511, 3, 50047, 3, 7, 3, 13,
    3, 113, 3, 3, 31, 269, 3, 47,
    5, 3, 3, 6389, 3, 5, 48311, 3,
    503, 73, 5, 3, 3, 5, 3, 3,
    19, 5, 11, 3, 3, 3, 541, 3,
    2287, 5, 3, 11, 3, 3, 3, 151,
    647, 3, 5, 3, 59, 3, 13, 5,
    3, 7, 3, 29, 5, 3, 3, 23827,
    3, 5, 3, 3, 43, 101, 7, 5,
    11, 3, 3, 3, 73, 29, 17, 7,
    3, 109, 3, 3, 819629, 3, 7, 149,
    3, 3, 3, 283, 3, 3, 3, 3,
    557, 3, 13, 5, 3, 3, 3, 58129,
    5, 7, 145007, 13, 3, 3, 7, 11,
    3, 3, 521, 3, 1429, 5, 3, 3,
    7, 3, 3, 17, 13, 5, 3, 3,
    5, 1597, 3, 72725357, 7, 3, 3, 587,
    3, 17, 3, 3, 3, 411583, 5, 3,
    473741, 3, 5, 47, 3, 3, 11, 2377,
    5, 3, 3, 3, 3, 11, 7, 3,
    23, 3, 5, 3, 3, 3, 179, 3,
    7, 18374101, 281, 5, 3, 131, 59, 5,
    3, 47, 3, 643, 17, 241, 1206353, 5,
    3, 3, 3919, 3, 3, 3, 19, 3,
    3, 97, 11, 3, 17, 13, 3, 71,
    5, 3, 3, 7, 3, 3, 3, 7,
    3, 138445793, 3, 5, 3, 3, 103, 3,
    7, 3, 5, 3, 3, 1627, 3, 37,
    431, 3, 7, 3, 3, 3, 7, 3,
    109, 11, 13, 3, 3, 3, 233, 5,
    3, 3, 23, 7, 3, 5, 3, 19,
    118493, 3, 3967, 5, 3, 23599]

theorem prime_sub_5987 : Nat.Prime (31821625829250454 - 5987) := by
  show Nat.Prime 31821625829244467
  exact p31821625829244467

theorem check_5987 : allC 31821625829250454 5987 P10k ds_5987 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 31821625829250454 is 5987. -/
theorem minGB_S_5987 : minGB 31821625829250454 = 5987 :=
  minGB_eq_of P10k P10k_complete 31821625829250454 5987 (by norm_num) (by norm_num) prime_sub_5987 ds_5987 check_5987

def ds_6131 : List ℕ := [
    2, 5, 104483537, 3, 37, 3, 7, 3,
    5, 11, 3, 3, 1429, 3, 47, 5,
    7, 3, 3, 19, 3, 3, 5, 449,
    3, 7, 3, 29, 3, 5, 3, 87623,
    593, 3, 53, 3, 3, 3, 167, 5,
    13, 3, 1376339, 3, 26981, 3, 3, 3,
    7, 3, 5, 71, 3, 127, 13, 5,
    7, 3, 3, 29, 3, 5, 3, 7,
    3, 18731, 3, 3, 2741, 3, 5, 11,
    3, 3, 3, 5, 17, 3, 23, 3,
    461, 3, 41, 3, 3, 5, 2269, 3,
    7879, 3, 31, 7, 3, 11, 3, 5,
    101, 7, 3, 3, 3, 11, 5, 13,
    3, 3, 536017, 5, 853, 3, 3, 3,
    89449, 3, 3, 19, 3, 7, 5, 929,
    3, 3, 23, 5, 3, 63853, 3, 32085019,
    3, 3, 3, 5, 3, 3, 1109, 3,
    5, 3, 17, 10343, 3, 11, 3, 67,
    3, 31, 3, 7, 3, 5, 3, 13,
    3, 11, 3, 59, 3, 271, 3, 7,
    281233, 5, 3, 107, 29, 5, 3, 3,
    3, 5, 11, 3, 61, 3, 3, 421,
    3, 109, 3, 3, 3, 23, 3, 19,
    5, 7, 3, 3, 3, 7, 3, 5,
    3, 124067, 6991, 5, 3, 3, 11, 5,
    23, 3, 3, 3, 128576447, 7, 3, 5,
    921013, 3, 3, 251, 3, 17, 7, 3,
    3, 7, 23, 5, 3, 3, 17, 3,
    13, 3, 5, 19, 3, 521, 3, 3,
    3, 11, 3, 7, 3, 5, 29, 17,
    5, 3, 3, 3, 5, 1117, 3, 7,
    3, 5, 3, 229, 2161, 3, 5, 59,
    3, 3, 197, 3, 3, 19, 3, 3,
    7, 3, 79601, 101, 3, 5, 3, 3,
    3, 3, 3, 3, 37, 3, 3, 11,
    5, 3, 29, 3, 3, 151, 3, 11,
    3, 79, 2579, 7, 5, 89, 3, 7,
    3, 5, 65929, 3, 3, 2011, 3, 5,
    3, 3, 1423, 3, 43, 3, 5, 457,
    6673, 3, 157, 3, 2467, 89107, 3, 13,
    3, 3, 11, 3, 5, 3, 3, 3,
    11, 5, 3, 19, 3, 5, 3, 859,
    3, 5, 3, 3, 3, 43, 1319, 3,
    5, 11, 3, 3, 19, 997, 3, 3,
    1297, 3, 3, 5, 41, 7, 173, 5,
    3, 13, 2441, 63463, 3, 3, 121039, 3,
    3, 17, 3, 5, 179, 3, 3, 7,
    117930271, 3, 23, 3, 7, 5, 3, 911,
    3, 5, 3, 3, 3, 97, 3, 5,
    31, 3, 13033, 3, 3, 73, 3, 148272463,
    3, 5, 3, 151, 7, 3, 3, 11,
    3, 197, 3, 17, 5, 3, 3, 61,
    181, 3, 37, 5, 13, 3, 15881, 17,
    3, 7, 5, 311, 3, 7, 3, 53,
    3, 5, 3, 7, 3, 3, 3, 3,
    5, 8209, 3, 37, 3, 41, 3, 7,
    3, 3, 3, 1051, 5, 7, 3, 13,
    3, 7, 3, 31, 3, 3, 13, 3,
    3, 3, 3, 5, 11, 3, 3, 17,
    263, 3, 1663, 3, 59, 3, 8803, 5,
    3, 17, 3, 7, 3, 6029, 3, 19,
    3, 3, 3, 11, 3, 5, 101, 3,
    3, 3553007, 3, 3, 653, 3, 5, 3,
    3, 3739, 5, 3, 3, 3, 11, 7,
    3, 109, 3, 3, 10164797, 3, 19, 3,
    3, 3, 29, 13, 3, 214391, 3, 7,
    5, 353, 3, 5, 3, 23, 3, 5,
    3, 7, 3, 3, 51521, 409, 3, 5,
    6473, 3, 3, 19, 3, 11, 13, 3,
    7, 5, 827, 3, 3, 7, 3, 3,
    5, 13, 7, 3, 3, 3, 23, 3,
    5, 60128639, 3, 13, 3, 3, 3, 292343,
    7, 3, 37, 3, 12186907, 3, 5, 7,
    3, 907, 3, 5, 19, 3, 3, 211,
    3, 229, 3, 3, 5, 13, 80086063, 98929,
    54293, 3, 3, 3, 11, 29, 5, 73,
    3, 5, 3, 3, 11, 3, 5, 13,
    3, 3, 3, 5, 3, 3, 3, 3,
    7, 3, 5, 11, 3, 3, 3, 5,
    7, 61, 5, 7, 3, 3, 5, 101,
    3, 3, 18413, 3, 5, 2749, 3, 3,
    23, 3, 3, 12503, 17, 7, 3, 3,
    53, 7, 3, 13, 5, 3, 3, 419,
    3, 5, 3, 3, 3, 5, 1009, 3,
    7243, 3, 14431, 181, 3, 3, 17, 19,
    7, 3, 3, 3, 3, 131, 5, 3,
    13, 3, 2671, 3, 3, 3, 23, 3,
    53, 317, 5, 1242757, 3, 162416413, 5, 7,
    3, 5, 3, 7, 193, 17, 5, 337,
    3, 3, 3631, 3, 3, 3, 11, 3,
    3, 29423, 7, 3, 5, 29, 3, 11,
    7, 3, 3, 173, 3, 3, 3, 5,
    3, 17, 3, 11, 3, 3, 43, 3,
    19, 3, 89, 3, 3, 5, 3, 191243933,
    13, 3, 18749, 3, 3, 3, 5, 3,
    1697, 271, 5, 3, 3, 3, 5, 29,
    3, 3, 31, 59, 3, 11083, 3, 7,
    5, 3, 587, 7, 3, 7, 199, 3,
    144158803, 13, 3, 3, 31, 5, 3, 3,
    3, 41, 3, 11, 5, 3]

theorem prime_sub_6131 : Nat.Prime (48033787978024768 - 6131) := by
  show Nat.Prime 48033787978018637
  exact p48033787978018637

theorem check_6131 : allC 48033787978024768 6131 P10k ds_6131 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 48033787978024768 is 6131. -/
theorem minGB_S_6131 : minGB 48033787978024768 = 6131 :=
  minGB_eq_of P10k P10k_complete 48033787978024768 6131 (by norm_num) (by norm_num) prime_sub_6131 ds_6131 check_6131

def ds_6263 : List ℕ := [
    2, 39883, 11, 3, 5, 3, 613, 3,
    1481, 7, 3, 3, 5, 3, 19, 37,
    43, 3, 3, 5, 3, 3, 23, 107,
    3, 5, 3, 17, 3, 7, 3, 5,
    11, 3, 5254313, 3, 3, 3, 31, 22457167,
    353, 3, 5, 3, 7, 3, 3, 3,
    15581, 3, 61, 7, 3, 5, 311, 53,
    11, 3, 3, 5, 3, 17551, 3, 5,
    3, 43, 3, 3, 4933, 3, 13, 23,
    3, 3, 3, 152423, 19, 3, 5, 3,
    188323, 3, 5, 3, 3, 211, 7, 3,
    5, 3, 11, 181, 3, 5, 3, 19,
    13, 5, 3, 3, 3, 149, 29, 281,
    3, 3, 13, 30727589, 11, 3, 3, 3,
    7, 3, 3, 5, 3, 41431991, 173189, 7,
    3, 3, 41, 509, 3, 5, 3, 17,
    3, 3, 3, 7, 3, 3, 5, 3,
    23, 3, 11, 83, 3, 5, 3, 7,
    3, 3779, 3, 431, 3, 11, 3, 5,
    3, 161033, 3, 5, 3, 11, 3, 5,
    1787, 7, 3, 5, 13, 66593, 3, 3,
    3, 4909, 113, 3, 5, 3, 3, 23,
    3, 5, 3, 3, 3, 5, 3, 31,
    3671, 6263, 3, 3, 3, 5, 3, 7,
    3, 5, 19, 11, 3, 3, 53, 251,
    17, 3, 3, 3, 11, 97, 3, 31,
    7, 3, 3, 5, 3, 83, 4720741, 3,
    3, 5, 13, 7, 3, 3, 821, 3,
    87025819, 3, 17, 439, 3, 5, 3, 3,
    3, 5, 3, 1201873, 3, 67, 7, 5,
    11, 3, 3, 3, 448451, 196523, 3, 5,
    3, 7, 3, 5, 29, 3, 137, 1171,
    3, 3, 17, 3, 3, 7, 3, 3,
    61, 3, 7, 5, 3, 857, 3, 3,
    3, 3, 3, 3, 11, 3, 3, 5,
    19207, 3, 42979, 3, 3, 5, 3, 7,
    3, 79, 5, 41, 13, 5, 3, 126307,
    3, 13915519, 89, 3, 3, 32321, 3, 7,
    3, 3, 31, 3, 2083, 3, 61, 13,
    5, 3, 7, 3, 19, 5, 3, 7,
    3, 3, 5, 3, 23, 3, 3, 3,
    3575987, 7, 3, 136043, 3, 27277, 3, 15422789,
    3, 37, 3, 3, 3, 7, 47, 3,
    829, 7, 3, 3, 5, 541, 3, 3,
    5, 3, 3, 78713, 31, 5, 367, 7,
    3, 5, 11, 13, 3, 3, 29, 3,
    3, 5, 3, 109614431, 7, 3, 3, 11,
    5, 3, 2687, 3, 5, 7, 3, 17,
    3, 109, 3, 3, 3, 9797783, 3, 13,
    67, 3, 5, 3, 3, 251, 3, 5,
    3, 1811, 3, 11, 2089, 3, 3, 5,
    3, 257, 3, 79, 7, 3, 3, 5,
    1153, 3, 19, 523, 11, 3, 7, 37,
    3, 31, 17, 7, 3, 29, 3, 5,
    3, 97, 3, 5, 3, 3, 3, 3,
    13, 71069, 3, 23, 3, 7, 3, 17,
    3, 3, 3, 5, 58263617, 62649101, 3, 5,
    3, 5, 3, 23, 3, 3, 71, 3,
    3, 3, 3, 196769, 31, 3, 3, 7,
    9780871, 3, 5, 3, 7, 3, 15139, 43,
    3, 2633, 3, 5, 3, 19, 3, 5,
    3, 3, 3, 61, 3, 23, 727, 3,
    3, 7, 3, 3, 5, 3, 2714573, 3,
    3, 80749181, 401, 3, 3, 3, 6761, 5,
    3, 17, 3, 3, 5, 3, 47, 3,
    3, 3, 5, 7, 3, 17, 3, 83,
    112429, 5, 3, 11, 3, 5, 3, 13,
    3, 5, 3, 3, 5, 5779, 3, 19,
    43, 3, 3, 23, 3, 311, 5, 3,
    2621, 379, 7, 3, 3, 37, 3, 3,
    31, 53, 5, 3, 3, 3, 1419749, 3,
    149, 87934783, 3, 17393, 3, 3, 3, 5,
    29, 3, 7, 3, 5, 3, 13, 31,
    3, 5, 3, 47, 17, 3, 3, 30347,
    3, 7552939, 3, 3, 3251, 5, 7, 13,
    5, 3, 3, 3, 5, 269, 73, 5,
    3, 11, 3, 3, 1289, 3, 7, 619,
    3, 3, 3, 107, 3, 3, 3, 3,
    23, 3, 13, 7, 3, 3, 3, 673,
    241, 5, 43, 5, 3, 3, 7, 5,
    3, 3, 617, 3, 83, 13, 3, 3,
    7, 3, 3, 5, 13, 11, 3, 3,
    641, 5, 3, 37, 7, 3, 3, 283,
    3, 479, 3, 3, 3, 17, 7555091, 3,
    5, 3, 443, 5, 3, 3, 5, 11,
    199, 3, 3, 3, 3, 313, 7, 3,
    5, 3, 13, 3, 3, 3, 5, 3,
    7, 5, 127, 7, 3, 1235369, 193, 17,
    3, 12391, 3, 5, 5, 8340637, 953, 82757,
    3, 3, 11, 3, 3, 3, 5, 3,
    3, 5, 43, 3, 11, 5, 3, 211,
    19, 3, 3, 5, 3, 3, 3, 7,
    3, 5, 3, 1063, 3, 3, 5, 3,
    7, 3, 53, 3, 3, 47, 3, 5,
    17, 3, 5, 3, 3, 3, 7, 3,
    5, 2843, 11, 3, 3, 3, 41, 10884883,
    3, 3, 5, 7, 3, 11, 3, 139,
    257, 3, 46663, 127609241, 3, 5, 53, 3,
    5, 233, 3, 3, 13, 1319, 3, 3,
    3, 19, 3, 5, 90197, 3, 5, 3,
    11, 3, 3, 359, 2936959, 3, 7, 3,
    3, 5, 3, 3, 47]

theorem prime_sub_6263 : Nat.Prime (55104008958365746 - 6263) := by
  show Nat.Prime 55104008958359483
  exact p55104008958359483

theorem check_6263 : allC 55104008958365746 6263 P10k ds_6263 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 55104008958365746 is 6263. -/
theorem minGB_S_6263 : minGB 55104008958365746 = 6263 :=
  minGB_eq_of P10k P10k_complete 55104008958365746 6263 (by norm_num) (by norm_num) prime_sub_6263 ds_6263 check_6263

def ds_6491 : List ℕ := [
    2, 5, 307, 3, 19, 3, 107, 3,
    5, 260413, 3, 3, 7, 3, 11, 5,
    13, 3, 3, 37, 3, 3, 5, 521,
    3, 953, 3, 73, 3, 5, 3, 127,
    13, 3, 53, 3, 3, 3, 7, 5,
    11, 3, 197, 3, 1367, 3, 3, 3,
    431, 3, 5, 19, 3, 7, 23, 5,
    367, 3, 3, 44398771, 3, 5, 3, 11,
    3, 223, 3, 3, 31, 3, 5, 101763043,
    3, 3, 3, 5, 17, 3, 94050809, 3,
    7, 3, 1039, 3, 3, 5, 13, 3,
    7, 3, 19, 101, 3, 17, 3, 5,
    11, 5851711, 3, 3, 3, 10739, 5, 103,
    3, 3, 7, 5, 313, 3, 3, 3,
    659, 3, 3, 11, 3, 36469, 5, 41,
    3, 3, 167, 5, 3, 109, 3, 31,
    3, 3, 3, 5, 3, 3, 13, 3,
    5, 3, 7, 19, 3, 43, 3, 145009,
    3, 7, 3, 181, 3, 5, 3, 7,
    3, 293, 3, 4967, 3, 739, 3, 91457,
    23, 5, 3, 11, 439, 5, 3, 3,
    3, 5, 599, 3, 5503, 3, 3, 7,
    3, 5441, 3, 3, 3, 7, 3, 15017,
    5, 29, 3, 3, 3, 13, 3, 5,
    3, 37, 103, 5, 3, 3, 7, 5,
    13, 3, 3, 3, 7, 31, 3, 5,
    563, 3, 3, 7, 3, 13, 4696177, 3,
    3, 23, 11, 5, 3, 3, 17, 3,
    7, 3, 5, 163, 3, 3585949, 3, 3,
    3, 131, 3, 593, 3, 5, 11, 7,
    5, 3, 3, 3, 5, 59, 3, 449,
    3, 5, 3, 6036067, 19, 3, 5, 13,
    3, 3, 7, 3, 3, 9017773, 3, 3,
    11, 3, 557, 7, 3, 5, 3, 3,
    3, 3, 3, 3, 61, 3, 3, 744811,
    5, 3, 7, 3, 3, 41897, 3, 2081,
    3, 7, 6997, 151, 5, 7, 3, 19,
    3, 5, 29, 3, 3, 641, 3, 5,
    3, 3, 11, 3, 1579, 3, 5, 37,
    79, 3, 13, 3, 7, 43, 3, 229,
    3, 3, 7, 3, 5, 3, 3, 3,
    31, 5, 3, 22447, 3, 5, 3, 7,
    3, 5, 3, 3, 3, 73, 7, 3,
    5, 2789, 3, 3, 7, 11, 3, 3,
    41, 3, 3, 5, 13, 97, 127, 5,
    3, 1123, 223729339, 47, 3, 3, 7, 3,
    3, 17, 3, 5, 4933, 3, 3, 31,
    446197, 3, 17015519, 3, 11, 5, 3, 971,
    3, 5, 3, 3, 3, 7, 3, 5,
    479, 3, 13, 3, 3, 7, 3, 23,
    3, 5, 3, 587, 13, 3, 3, 6607,
    3, 11, 3, 17, 5, 3, 3, 19,
    23, 3, 7, 5, 67, 3, 8971, 7,
    3, 37, 5, 523, 3, 1453, 3, 53,
    3, 5, 3, 17, 3, 3, 3, 3,
    5, 19, 3, 41, 3, 31, 3, 269,
    3, 3, 3, 7, 5, 28278139, 3, 16831,
    3, 61, 3, 13, 3, 3, 89, 3,
    3, 3, 3, 5, 53, 3, 3, 11,
    7, 3, 29, 3, 12049, 3, 9011, 5,
    3, 17, 3, 2131, 3, 461, 3, 13,
    3, 3, 3, 7, 3, 5, 7759, 3,
    3, 701, 3, 3, 69029, 3, 5, 3,
    3, 61, 5, 3, 3, 3, 19, 28409,
    3, 11, 3, 3, 1871, 3, 29, 3,
    3, 3, 65026373, 19183, 3, 7, 3, 7103,
    5, 7, 3, 5, 3, 29789, 3, 5,
    3, 13, 3, 3, 320907893, 43, 3, 5,
    35837, 3, 3, 7, 3, 7, 19, 3,
    11, 5, 1770001, 3, 3, 73, 3, 3,
    5, 6467767, 2447, 3, 3, 3, 607, 3,
    5, 11, 3, 7, 3, 3, 3, 1912969,
    3863, 3, 19, 3, 7, 3, 5, 23,
    3, 11, 3, 5, 37, 3, 3, 11,
    3, 13, 3, 3, 5, 59, 23, 7,
    2687, 3, 3, 3, 7, 19, 5, 14327,
    3, 5, 3, 3, 67, 3, 5, 91781,
    3, 3, 3, 5, 3, 3, 3, 3,
    301106903, 3, 5, 751, 3, 3, 3, 5,
    11273, 43, 5, 101, 3, 3, 5, 857,
    3, 3, 7, 3, 5, 11, 3, 3,
    13, 3, 3, 7, 17, 9473, 3, 3,
    53, 11, 3, 29, 5, 3, 3, 113,
    3, 5, 3, 3, 3, 5, 389, 3,
    457, 3, 7, 13, 3, 3, 7, 23,
    59, 3, 3, 3, 3, 14212463, 5, 3,
    14303, 3, 154043, 3, 3, 3, 317, 3,
    53, 11, 5, 47, 3, 2161, 5, 251,
    3, 5, 3, 163, 311, 17, 5, 37,
    3, 3, 7, 3, 3, 3, 13, 3,
    3, 5998417, 1559, 3, 5, 7, 3, 137653,
    13, 3, 3, 151, 3, 3, 3, 5,
    3, 11, 3, 23, 3, 3, 1789, 3,
    11, 3, 7, 3, 3, 5, 3, 7,
    211, 3, 31, 3, 3, 3, 5, 3,
    73, 29, 5, 3, 3, 3, 5, 1193,
    3, 3, 236017, 109777123, 3, 7, 3, 17,
    5, 3, 31, 19, 3, 29, 11, 3,
    1019, 4051, 3, 3, 7, 5, 3, 3,
    3, 7, 3, 17, 5, 3, 7, 3,
    5, 3, 3, 5, 131, 3, 5, 3,
    3, 13, 3, 3, 7, 5, 199, 3,
    3, 37, 7, 3, 2099, 11, 5, 23,
    3, 3, 5, 22463257, 3, 3, 3, 3,
    63391, 3, 3, 3, 11, 3, 3, 5,
    3]

theorem prime_sub_6491 : Nat.Prime (107157207101894788 - 6491) := by
  show Nat.Prime 107157207101888297
  exact p107157207101888297

theorem check_6491 : allC 107157207101894788 6491 P10k ds_6491 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 107157207101894788 is 6491. -/
theorem minGB_S_6491 : minGB 107157207101894788 = 6491 :=
  minGB_eq_of P10k P10k_complete 107157207101894788 6491 (by norm_num) (by norm_num) prime_sub_6491 ds_6491 check_6491

def ds_6761 : List ℕ := [
    2, 5, 23, 3, 19, 3, 7, 3,
    5, 13, 3, 3, 29, 3, 1423, 5,
    7, 3, 3, 17, 3, 3, 5, 59,
    3, 7, 3, 13, 3, 5, 3, 101,
    971, 3, 11, 3, 3, 3, 60901487, 5,
    1752263, 3, 2616023, 3, 5459677, 3, 3, 3,
    7, 3, 5, 19, 3, 33521, 239924771, 5,
    7, 3, 3, 11, 3, 5, 3, 7,
    3, 73, 3, 3, 11, 3, 5, 13757,
    3, 3, 3, 5, 29, 3, 6263, 3,
    13, 3, 30203, 3, 3, 5, 63134443, 3,
    643, 3, 19, 7, 3, 43575659, 3, 5,
    307, 7, 3, 3, 3, 23, 5, 1019,
    3, 3, 107, 5, 56673017, 3, 3, 3,
    397, 3, 3, 53, 3, 7, 5, 47,
    3, 3, 11, 5, 3, 43, 3, 142573,
    3, 3, 3, 5, 3, 3, 439, 3,
    5, 3, 41, 11, 3, 71, 3, 82744313,
    3, 18191, 3, 7, 3, 5, 3, 33191,
    3, 13, 3, 29, 3, 37, 3, 7,
    227, 5, 3, 23, 401, 5, 3, 3,
    3, 5, 95279897, 3, 67, 3, 3, 109,
    3, 1933, 3, 3, 3, 17, 3, 313,
    5, 7, 3, 3, 3, 7, 3, 5,
    3, 17749, 3911, 5, 3, 3, 43, 5,
    103, 3, 3, 3, 29, 7, 3, 5,
    41, 3, 3, 151, 3, 673, 7, 3,
    3, 7, 61, 5, 3, 3, 10937, 3,
    14554289, 3, 5, 38036291, 3, 31, 3, 3,
    3, 21767, 3, 7, 3, 5, 17, 13,
    5, 3, 3, 3, 5, 1914197, 3, 7,
    3, 5, 3, 11, 19, 3, 5, 139,
    3, 3, 31, 3, 3, 11, 3, 3,
    7, 3, 83, 19, 3, 5, 3, 3,
    3, 3, 3, 3, 47, 3, 3, 421,
    5, 3, 103, 3, 3, 107, 3, 331,
    3, 167, 13, 7, 5, 11, 3, 7,
    3, 5, 13, 3, 3, 11, 3, 5,
    3, 3, 41, 3, 37, 3, 5, 47,
    163, 3, 22511, 3, 61, 17, 3, 11,
    3, 3, 3345217, 3, 5, 3, 3, 3,
    83, 5, 3, 67, 3, 5, 3, 3558439,
    3, 5, 3, 3, 3, 1721, 227, 3,
    5, 878131, 3, 3, 23, 109, 3, 3,
    31, 3, 3, 5, 194933413, 7, 17, 5,
    3, 127, 13, 11, 3, 3, 29, 3,
    3, 291322583, 3, 5, 53, 3, 3, 7,
    11, 3, 669659, 3, 7, 5, 3, 11,
    3, 5, 3, 3, 3, 9689, 3, 5,
    730619, 3, 127843, 3, 3, 10459, 3, 653,
    3, 5, 3, 797, 7, 3, 3, 34147,
    3, 137, 3, 13, 5, 3, 3, 19,
    112291, 3, 241141, 5, 211, 3, 17, 31,
    3, 7, 5, 89, 3, 7, 3, 41,
    3, 5, 3, 7, 3, 3, 3, 3,
    5, 19, 3, 11, 3, 179, 3, 7,
    3, 3, 3, 334157, 5, 7, 3, 953,
    3, 7, 3, 41, 3, 3, 8821, 3,
    3, 3, 3, 5, 90583, 3, 3, 29,
    7406843, 3, 37, 3, 36073, 3, 48413, 5,
    3, 11, 3, 7, 3, 419, 3, 35159,
    3, 3, 3, 229, 3, 5, 13, 3,
    3, 389, 3, 3, 11, 3, 5, 3,
    3, 13, 5, 3, 3, 3, 19, 7,
    3, 1543, 3, 3, 83, 3, 2396683, 3,
    3, 3, 47, 101, 3, 11, 3, 7,
    5, 53, 3, 5, 3, 13, 3, 5,
    3, 7, 3, 3, 11, 1427, 3, 5,
    13, 3, 3, 17, 3, 941, 19, 3,
    7, 5, 151, 3, 3, 7, 3, 3,
    5, 5413, 7, 3, 3, 3, 1009, 3,
    5, 53, 3, 3041, 3, 3, 3, 179,
    7, 3, 19, 3, 11, 3, 5, 7,
    3, 25801, 3, 5, 157, 3, 3, 59,
    3, 823, 3, 3, 5, 29, 13, 149,
    23, 3, 3, 3, 10112477, 17, 5, 37,
    3, 5, 3, 3, 7963, 3, 5, 647,
    3, 3, 3, 5, 3, 3, 3, 3,
    7, 3, 5, 67, 3, 3, 3, 5,
    7, 59, 5, 7, 3, 3, 5, 97,
    3, 3, 13, 3, 5, 19, 3, 3,
    383, 3, 3, 23159, 1123, 7, 3, 3,
    160539319, 7, 3, 103, 5, 3, 3, 11,
    3, 5, 3, 3, 3, 5, 5479, 3,
    13, 3, 41651, 67, 3, 3, 71, 29,
    7, 3, 3, 3, 3, 37, 5, 3,
    17, 3, 66260351, 3, 3, 3, 11, 3,
    521, 29, 5, 4458667, 3, 11, 5, 7,
    3, 5, 3, 7, 397, 23, 5, 59,
    3, 3, 1033, 3, 3, 3, 211, 3,
    3, 41, 7, 3, 5, 1583039, 3, 71,
    7, 3, 3, 131, 3, 3, 3, 5,
    3, 37, 3, 89, 3, 3, 547, 3,
    8287, 3, 400069, 3, 3, 5, 3, 19,
    41, 3, 5431, 3, 3, 3, 5, 3,
    13, 7331, 5, 3, 3, 3, 5, 331,
    3, 3, 43, 6967, 3, 13, 3, 7,
    5, 3, 2819, 7, 3, 7, 17, 3,
    73, 439, 3, 3, 53, 5, 3, 3,
    3, 11, 3, 31, 5, 3, 29, 3,
    5, 3, 3, 5, 149, 3, 5, 3,
    3, 11, 3, 3, 37, 5, 13, 3,
    3, 11, 47, 3, 82457041, 7, 5, 152947,
    3, 3, 5, 7, 3, 3, 3, 3,
    43391, 3, 3, 3, 73, 3, 3, 5,
    3, 23, 6793, 3, 3, 11, 3, 5,
    7, 3, 3, 13, 17, 3, 3, 3,
    5, 13, 3, 3, 3, 83, 3, 17,
    3, 3, 199, 3, 7]

theorem prime_sub_6761 : Nat.Prime (182745307201020658 - 6761) := by
  show Nat.Prime 182745307201013897
  exact p182745307201013897

theorem check_6761 : allC 182745307201020658 6761 P10k ds_6761 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 182745307201020658 is 6761. -/
theorem minGB_S_6761 : minGB 182745307201020658 = 6761 :=
  minGB_eq_of P10k P10k_complete 182745307201020658 6761 (by norm_num) (by norm_num) prime_sub_6761 ds_6761 check_6761

def ds_6899 : List ℕ := [
    2, 34057, 13, 3, 5, 3, 23, 3,
    6203, 7, 3, 3, 5, 3, 17, 11,
    199, 3, 3, 5, 3, 3, 13, 445463717,
    3, 5, 3, 911, 3, 7, 3, 5,
    29, 3, 17, 3, 3, 3, 16197953, 31,
    547, 3, 5, 3, 7, 3, 3, 3,
    1741, 3, 1291, 7, 3, 5, 3673, 19,
    967, 3, 3, 5, 3, 23, 3, 5,
    3, 11, 3, 3, 37, 3, 17, 31,
    3, 3, 3, 11, 7695763, 3, 5, 3,
    6501749, 3, 5, 3, 3, 8087, 7, 3,
    5, 3, 223, 3049, 3, 5, 3, 3769,
    313, 5, 3, 3, 3, 17, 3727, 23,
    3, 3, 3911, 43, 191, 3, 3, 3,
    7, 3, 3, 5, 3, 11, 541, 7,
    3, 3, 89, 61, 3, 5, 3, 19,
    3, 3, 3, 7, 3, 3, 5, 3,
    79, 3, 241, 179, 3, 5, 3, 7,
    3, 113, 3, 439, 3, 13, 3, 5,
    3, 6553, 3, 5, 3, 3838259, 3, 5,
    19, 7, 3, 5, 11, 23, 3, 3,
    3, 37, 13, 3, 5, 3, 3, 61,
    3, 5, 3, 3, 3, 5, 3, 13,
    31, 11, 3, 3, 3, 5, 3, 7,
    3, 5, 353, 15679, 3, 3, 4078259, 23063,
    9174719, 3, 3, 3, 23, 41, 3, 401,
    7, 3, 3, 5, 3, 11, 85305709, 3,
    3, 5, 43, 7, 3, 3, 13, 3,
    33569, 3, 73, 11, 3, 5, 3, 3,
    3, 5, 3, 13, 3, 617, 7, 5,
    41, 3, 3, 3, 67, 2099, 3, 5,
    3, 7, 3, 5, 181, 3, 514309, 611551,
    3, 3, 11, 3, 3, 7, 3, 3,
    271, 3, 7, 5, 3, 83, 3, 3,
    3, 3, 3, 3, 136481, 3, 3, 5,
    661, 3, 31, 3, 3, 5, 3, 7,
    3, 309140411, 5, 53, 1429, 5, 3, 23,
    3, 19, 18979721, 3, 3, 18057503, 3, 7,
    3, 3, 193765301, 3, 1523, 3, 9973349, 519667,
    5, 3, 7, 3, 11, 5, 3, 7,
    3, 3, 5, 3, 1005883, 3, 3, 3,
    193, 7, 3, 2729, 3, 151, 3, 13,
    3, 233, 3, 3, 3, 7, 73, 3,
    1217, 7, 3, 3, 5, 67, 3, 3,
    5, 3, 3, 17, 29, 5, 104173, 7,
    3, 5, 199, 139, 3, 3, 97, 3,
    3, 5, 3, 19, 7, 3, 3, 13,
    5, 3, 674017, 3, 5, 7, 3, 13,
    3, 347, 3, 3, 3, 27299, 3, 11,
    17, 3, 5, 3, 3, 83, 3, 5,
    3, 41, 3, 23, 37, 3, 3, 5,
    3, 103, 3, 43783, 7, 3, 3, 5,
    61, 3, 79967, 17, 26591, 3, 7, 3931,
    3, 11, 31, 7, 3, 19, 3, 5,
    3, 11, 3, 5, 3, 3, 3, 3,
    73025671, 11, 3, 116697583, 3, 7, 3, 9227,
    3, 3, 3, 5, 13, 17, 3, 5,
    3, 5, 3, 163, 3, 3, 17940409, 3,
    3, 3, 3, 271, 23, 3, 3, 7,
    13, 3, 5, 3, 7, 3, 1231, 17,
    3, 551581, 3, 5, 3, 23, 3, 5,
    3, 3, 3, 9491, 3, 247369, 467, 3,
    3, 7, 3, 3, 5, 3, 13, 3,
    3, 11, 73, 3, 3, 3, 811, 5,
    3, 37, 3, 3, 5, 3, 17, 3,
    3, 3, 5, 7, 3, 181, 3, 19,
    683, 5, 3, 269, 3, 5, 3, 2243453,
    3, 5, 3, 3, 5, 132331, 3, 17,
    31151, 3, 3, 11, 3, 64171, 5, 3,
    727, 11, 7, 3, 3, 8579183, 3, 3,
    503, 11, 5, 3, 3, 3, 17, 3,
    53, 13, 3, 23, 3, 3, 3, 5,
    13, 3, 7, 3, 5, 3, 19, 7853,
    3, 5, 3, 6091, 2789, 3, 3, 1019,
    3, 109, 3, 3, 13, 5, 7, 11,
    5, 3, 3, 3, 5, 50924327, 43, 5,
    3, 641, 3, 3, 3299, 3, 7, 853,
    3, 3, 3, 180951149, 3, 3, 3, 3,
    17, 3, 4831, 7, 3, 3, 3, 11,
    107, 5, 995663, 5, 3, 3, 7, 5,
    3, 3, 37, 3, 137, 383, 3, 3,
    7, 3, 3, 5, 331, 127, 3, 3,
    13, 5, 3, 11, 7, 3, 3, 41,
    3, 4157, 3, 3, 3, 11, 29, 3,
    5, 3, 79, 5, 3, 3, 5, 53,
    8402683, 3, 3, 3, 3, 17, 7, 3,
    5, 3, 712571, 3, 3, 3, 5, 3,
    7, 5, 1481, 7, 3, 3581, 147377, 13,
    3, 11, 3, 5, 5, 13, 19, 11,
    3, 3, 311, 3, 3, 3, 5, 3,
    3, 5, 32533, 3, 89, 5, 3, 19,
    71, 3, 3, 5, 3, 3, 3, 7,
    3, 5, 3, 877, 3, 3, 5, 3,
    7, 3, 577, 3, 3, 6983, 3, 5,
    83, 3, 5, 3, 3, 3, 7, 3,
    5, 61, 23, 3, 3, 3, 4547, 19,
    3, 3, 5, 7, 3, 29, 3, 37,
    9001, 3, 11, 31, 3, 5, 79, 3,
    5, 199, 3, 3, 101, 29, 3, 3,
    3, 13, 3, 5, 197, 3, 5, 3,
    313, 3, 3, 61, 41, 3, 7, 3,
    3, 5, 3, 3, 11, 113, 17, 3,
    3, 7, 229, 3, 5, 84937663, 11, 7,
    3, 3, 1279, 53, 3, 3, 3, 3,
    11, 3, 3, 3, 599, 3, 3, 17,
    3, 5, 5, 3, 3, 5, 3, 37,
    1433, 3, 3, 5, 841307, 3, 3, 3,
    11, 47, 3, 3, 3, 41, 3, 5,
    3, 3, 11, 3, 308052659, 5, 3, 17,
    3, 5, 3, 911719, 3, 347, 3, 7,
    3, 389, 331, 13, 3, 3]

theorem prime_sub_6899 : Nat.Prime (237098616193722886 - 6899) := by
  show Nat.Prime 237098616193715987
  exact p237098616193715987

theorem check_6899 : allC 237098616193722886 6899 P10k ds_6899 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 237098616193722886 is 6899. -/
theorem minGB_S_6899 : minGB 237098616193722886 = 6899 :=
  minGB_eq_of P10k P10k_complete 237098616193722886 6899 (by norm_num) (by norm_num) prime_sub_6899 ds_6899 check_6899

end LeanLab.OeSHP2014
