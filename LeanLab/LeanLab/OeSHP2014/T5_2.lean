/-
P0005 Oliveira e Silva, Herzog, Pardi 2014, Math. Comp. 83, 2033 to 2060, Table 5 page 2044,
the rows not already in Sinisalo 1993 Table 2, part 2: minGB S(p) = p. Divisors and Pratt
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

theorem p11551849 : Nat.Prime 11551849 := by
  refine Pratt.pratt 11551849 29 [(2, 3), (3, 1), (7, 2), (11, 1), (19, 1), (47, 1)] (by norm_num)
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
theorem p12242267 : Nat.Prime 12242267 := by
  refine Pratt.pratt 12242267 2 [(2, 1), (1019, 1), (6007, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p12333283 : Nat.Prime 12333283 := by
  refine Pratt.pratt 12333283 2 [(2, 1), (3, 1), (13, 2), (12163, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p29148731 : Nat.Prime 29148731 := by
  refine Pratt.pratt 29148731 2 [(2, 1), (5, 1), (13, 1), (224221, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p30927997 : Nat.Prime 30927997 := by
  refine Pratt.pratt 30927997 2 [(2, 2), (3, 2), (11, 1), (78101, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p53398747 : Nat.Prime 53398747 := by
  refine Pratt.pratt 53398747 3 [(2, 1), (3, 2), (2966597, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p78539389 : Nat.Prime 78539389 := by
  refine Pratt.pratt 78539389 6 [(2, 2), (3, 1), (17, 1), (19, 1), (23, 1), (881, 1)] (by norm_num)
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
theorem p213594989 : Nat.Prime 213594989 := by
  refine Pratt.pratt 213594989 2 [(2, 2), (53398747, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p53398747
theorem p220360807 : Nat.Prime 220360807 := by
  refine Pratt.pratt 220360807 3 [(2, 1), (3, 2), (12242267, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p12242267
theorem p303973781 : Nat.Prime 303973781 := by
  refine Pratt.pratt 303973781 7 [(2, 2), (5, 1), (11, 3), (19, 1), (601, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p323451773 : Nat.Prime 323451773 := by
  refine Pratt.pratt 323451773 2 [(2, 2), (7, 1), (11551849, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p11551849
theorem p2276989199 : Nat.Prime 2276989199 := by
  refine Pratt.pratt 2276989199 7 [(2, 1), (11, 1), (211, 1), (490519, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p467773025911 : Nat.Prime 467773025911 := by
  refine Pratt.pratt 467773025911 3 [(2, 1), (3, 1), (5, 1), (73, 1), (213594989, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p213594989
theorem p6425663519579 : Nat.Prime 6425663519579 := by
  refine Pratt.pratt 6425663519579 2 [(2, 1), (17, 1), (83, 1), (2276989199, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p2276989199
theorem p60913048741229 : Nat.Prime 60913048741229 := by
  refine Pratt.pratt 60913048741229 2 [(2, 2), (283, 1), (4363, 1), (12333283, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p12333283
theorem p103252325574599 : Nat.Prime 103252325574599 := by
  refine Pratt.pratt 103252325574599 11 [(2, 1), (839, 1), (2111, 1), (29148731, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p29148731
theorem p107642944987841 : Nat.Prime 107642944987841 := by
  refine Pratt.pratt 107642944987841 3 [(2, 6), (5, 1), (4283, 1), (78539389, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p78539389
theorem p129987700021469 : Nat.Prime 129987700021469 := by
  refine Pratt.pratt 129987700021469 2 [(2, 2), (106907, 1), (303973781, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p303973781
theorem p143521252284989 : Nat.Prime 143521252284989 := by
  refine Pratt.pratt 143521252284989 2 [(2, 2), (61, 1), (163, 1), (20047, 1), (180007, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p194539179139181 : Nat.Prime 194539179139181 := by
  refine Pratt.pratt 194539179139181 2 [(2, 2), (5, 1), (19, 1), (71, 1), (173, 1), (1063, 1), (39209, 1)] (by norm_num)
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
theorem p215285889975683 : Nat.Prime 215285889975683 := by
  refine Pratt.pratt 215285889975683 2 [(2, 1), (107642944987841, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl
  · exact pB (by decide +kernel)
  · exact p107642944987841
theorem p280780621149101 : Nat.Prime 280780621149101 := by
  refine Pratt.pratt 280780621149101 2 [(2, 2), (5, 2), (19, 1), (1613, 1), (4283, 1), (21391, 1)] (by norm_num)
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
theorem p319245515533181 : Nat.Prime 319245515533181 := by
  refine Pratt.pratt 319245515533181 3 [(2, 2), (5, 1), (17, 1), (4261, 1), (220360807, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p220360807
theorem p332638450256747 : Nat.Prime 332638450256747 := by
  refine Pratt.pratt 332638450256747 2 [(2, 1), (514201, 1), (323451773, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p323451773
theorem p445685413496423 : Nat.Prime 445685413496423 := by
  refine Pratt.pratt 445685413496423 5 [(2, 1), (11, 1), (313, 1), (178537, 1), (362521, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p557249554744741 : Nat.Prime 557249554744741 := by
  refine Pratt.pratt 557249554744741 2 [(2, 2), (3, 2), (5, 1), (11, 1), (13, 3), (17, 1), (31, 1), (243077, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p650204506016291 : Nat.Prime 650204506016291 := by
  refine Pratt.pratt 650204506016291 2 [(2, 1), (5, 1), (139, 1), (467773025911, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p467773025911
theorem p666956025096593 : Nat.Prime 666956025096593 := by
  refine Pratt.pratt 666956025096593 3 [(2, 4), (7, 1), (11, 1), (115603, 1), (4682927, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
theorem p814410862533017 : Nat.Prime 814410862533017 := by
  refine Pratt.pratt 814410862533017 3 [(2, 3), (7, 1), (41, 1), (691, 1), (3877, 1), (132403, 1)] (by norm_num)
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
theorem p1025203842507749 : Nat.Prime 1025203842507749 := by
  refine Pratt.pratt 1025203842507749 3 [(2, 2), (19, 1), (79, 1), (5521, 1), (30927997, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p30927997
theorem p1246578722798327 : Nat.Prime 1246578722798327 := by
  refine Pratt.pratt 1246578722798327 5 [(2, 1), (97, 1), (6425663519579, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact p6425663519579

def ds_3863 : List ℕ := [
    2, 17, 7, 3, 13, 3, 5, 3,
    19, 199, 3, 3, 61, 3, 5, 22541,
    127, 3, 3, 11, 3, 3, 1181, 7,
    3, 439, 3, 5, 3, 43, 3, 7,
    5, 3, 263, 3, 3, 3, 5, 7,
    131, 3, 1453, 3, 5, 3, 3, 3,
    5, 3, 877699, 251, 3, 19, 5, 1097,
    11, 3, 3, 421, 3, 1759, 3, 71,
    3, 5, 3, 3, 5, 3, 887, 83,
    3, 3, 3, 7, 45497, 3, 11, 3,
    2937791, 3, 173, 3, 3, 31, 41, 3,
    2221, 3, 5, 13, 3, 5281, 3, 103,
    7, 23, 3, 3, 3, 5, 37, 5273,
    3, 3, 5, 7, 11, 3, 3, 3,
    5, 3, 3, 271, 3, 5, 4099, 23,
    3, 3, 5, 17, 3, 79, 3, 7,
    3, 3, 3, 2099, 3, 3, 7, 3,
    61, 3, 5, 187337, 3, 19, 3, 5,
    3, 151, 3, 5, 3, 11, 3, 7321,
    3, 5, 3, 11827, 3, 7, 3, 41,
    5, 653, 3, 7, 5, 39023, 3, 3,
    3, 7, 223, 3, 191, 3, 3, 19,
    3, 11, 3, 3, 3, 17, 3, 5,
    13, 233, 3, 3, 3, 435371, 3, 19,
    3, 7, 5, 11, 3, 3, 5, 7,
    37, 3, 3, 3, 11, 5, 3, 577,
    617, 3, 3, 167, 3, 5, 83093, 3,
    3, 837721, 5, 31, 3, 3, 67, 3,
    5, 3, 7, 2844223, 3, 37, 3, 3,
    3, 101, 3, 5, 3, 13, 17, 1871,
    11, 3, 3, 3, 2971, 7, 3, 13,
    3, 127, 3, 7, 5, 3, 8081, 19,
    3, 3, 5, 3, 3, 5, 3, 3,
    5, 3, 47, 11, 3, 19, 3, 3,
    3, 3, 3, 3, 5, 3, 3, 7,
    1123, 3, 5, 3, 3, 61, 3, 5,
    3, 37087, 23, 5, 787, 31, 3, 84319,
    3, 6301, 7, 3, 3, 5, 3, 1373,
    3, 3, 5, 3, 13, 3, 7, 115067,
    211, 3, 5, 3, 571, 17, 3, 53,
    3, 3, 1231, 3, 37021, 3, 3, 3,
    5, 17, 3, 5, 3, 36979, 3, 5,
    3, 7, 3, 3, 3, 5, 31469, 3,
    1672549, 37, 3, 3, 13, 5, 3, 3,
    11, 3, 3, 59, 7, 149, 5, 120943,
    3, 7, 5, 5879, 3, 3, 5, 3,
    3, 19, 3, 379, 4487843, 3, 3, 11,
    23, 3, 7, 3, 17, 6461839, 3, 5,
    3, 13, 3, 3, 3, 5, 3, 7,
    2467, 3, 11, 3, 3, 23, 3, 13,
    3, 243799, 3, 5, 3461, 3, 3, 3821,
    3, 7, 3, 5, 11, 3, 3, 7,
    97159, 3, 5, 7, 11, 3, 5, 105683,
    3, 5, 1423, 61, 3, 4263157, 3, 317,
    3, 349, 3, 11, 3, 3, 3, 3,
    29, 16963, 3, 47, 3, 5, 3, 5,
    3, 3, 3, 3299, 68891, 13, 3, 313,
    3, 107, 3, 5, 3, 3, 101, 3,
    3, 3, 3, 7, 19, 3, 3, 5,
    89, 3, 11, 3, 5903, 3, 5, 80789,
    3, 7, 3, 113, 3, 5, 3, 7,
    3, 3, 3, 5, 3, 7, 17, 3,
    3, 5, 3, 3, 283, 3, 103, 3,
    3, 5, 2435863, 3, 3, 3, 7, 19,
    3, 5, 3, 3, 7, 3, 53, 3,
    3, 3, 2503, 5, 3, 29, 3, 5,
    859, 67, 3, 11, 3, 7699, 3]

theorem prime_sub_3863 : Nat.Prime (60913048745092 - 3863) := by
  show Nat.Prime 60913048741229
  exact p60913048741229

theorem check_3863 : allC 60913048745092 3863 P10k ds_3863 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 60913048745092 is 3863. -/
theorem minGB_S_3863 : minGB 60913048745092 = 3863 :=
  minGB_eq_of P10k P10k_complete 60913048745092 3863 (by norm_num) (by norm_num) prime_sub_3863 ds_3863 check_3863

def ds_3923 : List ℕ := [
    2, 13, 17, 3, 53, 3, 5, 3,
    46451, 7, 3, 3, 31, 3, 5, 71,
    29, 3, 3, 7, 3, 3, 19, 593,
    3, 727, 3, 5, 3, 7, 3, 11,
    5, 3, 83, 3, 3, 3, 5, 193,
    79, 3, 1535351, 3, 5, 3, 3, 3,
    5, 3, 29, 7, 3, 3889, 5, 11,
    2539, 3, 3, 7, 3, 468623, 3, 17,
    3, 5, 3, 3, 5, 3, 47293, 367,
    3, 3, 3, 1601, 34457, 3, 107, 3,
    13, 3, 7331, 3, 3, 23, 7, 3,
    11, 3, 5, 59, 3, 7, 3, 276557,
    67, 43, 3, 3, 3, 5, 661, 3821,
    3, 3, 5, 11, 31, 3, 3, 3,
    5, 3, 3, 7161379, 3, 5, 13, 7,
    3, 3, 5, 647, 3, 7, 3, 17,
    3, 3, 3, 7, 3, 3, 69857, 3,
    6871, 3, 5, 13, 3, 17, 3, 5,
    3, 547, 3, 5, 3, 3019, 3, 19,
    3, 5, 3, 7, 3, 29, 3, 5479,
    5, 7, 3, 31, 5, 191, 3, 3,
    3, 4931, 311, 3, 139, 3, 3, 2951051,
    3, 131, 3, 3, 3, 5214119, 3, 5,
    29, 19, 3, 3, 3, 37, 3, 7,
    3, 101, 5, 47, 3, 3, 5, 19,
    17, 3, 3, 3, 15649, 5, 3, 53,
    7, 3, 3, 163, 3, 5, 11, 3,
    3, 41, 5, 7, 3, 3, 23, 3,
    5, 3, 13, 17359, 3, 11, 3, 3,
    3, 8186599, 3, 5, 3, 1230029, 7, 13,
    73, 3, 3, 3, 43, 67967, 3, 217409,
    3, 7, 3, 53, 5, 3, 527399, 313,
    3, 3, 5, 3, 3, 5, 3, 3,
    5, 3, 7, 109, 3, 202471, 3, 3,
    3, 3, 3, 3, 5, 3, 3, 43,
    13, 3, 5, 3, 3, 439, 3, 5,
    3, 239, 13, 5, 11, 211, 3, 859,
    3, 29, 11, 3, 3, 5, 3, 7,
    3, 3, 5, 3, 37, 3, 181, 43,
    125353, 3, 5, 3, 23, 11, 3, 7,
    3, 3, 83, 3, 241, 3, 3, 3,
    5, 7, 3, 5, 3, 11, 3, 5,
    3, 31, 3, 3, 3, 5, 11, 3,
    227, 7, 3, 3, 17, 5, 3, 3,
    7, 3, 3, 101, 73, 2492453, 5, 7,
    3, 11, 5, 31, 3, 3, 5, 3,
    3, 1597, 3, 19079, 7, 3, 3, 7591,
    7, 3, 71, 3, 113, 7, 3, 5,
    3, 157, 3, 3, 3, 5, 3, 9341,
    139, 3, 691, 3, 3, 61, 3, 293,
    3, 2341, 3, 5, 23, 3, 3, 7,
    3, 19, 3, 5, 7, 3, 3, 17,
    20431, 3, 5, 11, 9498197, 3, 5, 9844531,
    3, 5, 17, 7, 3, 101, 3, 7,
    3, 79, 3, 331, 3, 3, 3, 3,
    41, 7087723, 3, 27767, 3, 5, 3, 5,
    3, 3, 3, 29, 23, 811, 3, 7,
    3, 2190077, 3, 5, 3, 3, 11, 3,
    3, 3, 3, 67, 41, 3, 3, 5,
    43, 3, 17, 3, 7, 3, 5, 479,
    3, 47, 3, 13, 3, 5, 3, 1327,
    3, 3, 3, 5, 3, 139, 13, 3,
    3, 5, 3, 3, 18433, 3, 37, 3,
    3, 5, 89513, 3, 3, 3, 7489, 323581,
    3, 5, 3, 3, 463, 3, 22853, 3,
    3, 3, 11, 5, 3, 17, 3, 5,
    557, 41, 3, 1749431, 3, 7, 3, 2252693,
    3, 17, 3, 3, 4591, 5, 3]

theorem prime_sub_3923 : Nat.Prime (103252325578522 - 3923) := by
  show Nat.Prime 103252325574599
  exact p103252325574599

theorem check_3923 : allC 103252325578522 3923 P10k ds_3923 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 103252325578522 is 3923. -/
theorem minGB_S_3923 : minGB 103252325578522 = 3923 :=
  minGB_eq_of P10k P10k_complete 103252325578522 3923 (by norm_num) (by norm_num) prime_sub_3923 ds_3923 check_3923

def ds_4073 : List ℕ := [
    2, 19, 31, 3, 29, 3, 5, 3,
    7, 11, 3, 3, 19, 3, 5, 17,
    151, 3, 3, 5647, 3, 3, 199, 37,
    3, 991, 3, 5, 3, 337, 3, 53,
    5, 3, 7, 3, 3, 3, 5, 9056129,
    850337, 3, 7, 3, 5, 3, 3, 3,
    5, 3, 7, 3847549, 3, 1877, 5, 1811,
    19, 3, 3, 13, 3, 11, 3, 37,
    3, 5, 3, 3, 5, 3, 197, 7,
    3, 3, 3, 19, 21191, 3, 7, 3,
    184901, 3, 61, 3, 3, 7, 53, 3,
    17, 3, 5, 59, 3, 11, 3, 71,
    2131, 2729, 3, 3, 3, 5, 17, 7,
    3, 3, 5, 13, 120877, 3, 3, 3,
    5, 3, 3, 487, 3, 5, 7, 4056853,
    3, 3, 5, 173, 3, 69491, 3, 47,
    3, 3, 3, 23, 3, 3, 67, 3,
    6785279, 3, 5, 1402421, 3, 7, 3, 5,
    3, 19, 3, 5, 3, 7, 3, 23,
    3, 5, 3, 2903, 3, 71, 3, 569,
    5, 11, 3, 17, 5, 13, 3, 3,
    3, 401, 11, 3, 7, 3, 3, 6861157,
    3, 13, 3, 3, 3, 4793, 3, 5,
    347, 41, 3, 3, 3, 11, 3, 61,
    3, 19, 5, 3491, 3, 3, 5, 4751,
    29, 3, 3, 3, 7255883, 5, 3, 7,
    139, 3, 3, 167, 3, 5, 251387, 3,
    3, 107, 5, 13, 3, 3, 7, 3,
    5, 3, 23, 89, 3, 7, 3, 3,
    3, 11, 3, 5, 3, 7, 43, 101,
    19, 3, 3, 3, 1453, 158113, 3, 23,
    3, 17, 3, 41, 5, 3, 11, 7,
    3, 3, 5, 3, 3, 5, 3, 3,
    5, 3, 23, 53, 3, 2161, 3, 3,
    3, 3, 3, 3, 5, 3, 3, 11,
    9729067, 3, 5, 3, 3, 7, 3, 5,
    3, 17, 653743, 5, 7, 691, 3, 2579,
    3, 89, 19, 3, 3, 5, 3, 107,
    3, 3, 5, 3, 7, 3, 8737, 23581,
    7, 3, 5, 3, 29, 701, 3, 47,
    3, 3, 11, 3, 13, 3, 3, 3,
    5, 577, 3, 5, 3, 229, 3, 5,
    3, 11, 3, 3, 3, 5, 13, 3,
    7, 11, 3, 3, 127, 5, 3, 3,
    192053, 3, 3, 457, 17, 47, 5, 31,
    3, 787, 5, 7, 3, 3, 5, 3,
    3, 37, 3, 7, 19, 3, 3, 7499,
    599, 3, 31, 3, 13, 71, 3, 5,
    3, 19, 3, 3, 3, 5, 3, 47,
    13, 3, 7, 3, 3, 590609, 3, 9465317,
    3, 7, 3, 5, 43, 3, 3, 11,
    3, 1631821, 3, 5, 307, 3, 3, 80863,
    7, 3, 5, 827, 17, 3, 5, 6301,
    3, 5, 7, 29, 3, 11, 3, 13,
    3, 103, 3, 89, 3, 3, 3, 3,
    10377793, 7, 3, 19, 3, 5, 3, 5,
    3, 3, 3, 99667, 367, 937, 3, 2287,
    3, 795217, 3, 5, 3, 3, 7, 3,
    3, 3, 3, 13, 11, 3, 3, 5,
    61, 3, 83, 3, 73, 3, 5, 163,
    3, 1889, 3, 11, 3, 5, 3, 29,
    3, 3, 3, 5, 3, 4880747, 31, 3,
    3, 5, 3, 3, 6427, 3, 7, 3,
    3, 5, 17, 3, 3, 3, 11, 2879,
    3, 5, 3, 3, 3457, 3, 7, 3,
    3, 3, 7, 5, 3, 23, 3, 5,
    7, 43, 3, 389, 3, 6247, 3, 37,
    3, 227, 3, 3, 31, 5, 3, 11,
    7, 3, 3, 5, 3, 11, 1627, 3,
    5, 7, 59, 3, 3, 1613, 3, 3]

theorem prime_sub_4073 : Nat.Prime (129987700025542 - 4073) := by
  show Nat.Prime 129987700021469
  exact p129987700021469

theorem check_4073 : allC 129987700025542 4073 P10k ds_4073 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 129987700025542 is 4073. -/
theorem minGB_S_4073 : minGB 129987700025542 = 4073 :=
  minGB_eq_of P10k P10k_complete 129987700025542 4073 (by norm_num) (by norm_num) prime_sub_4073 ds_4073 check_4073

def ds_4079 : List ℕ := [
    2, 5, 11, 3, 107, 3, 7, 3,
    5, 853033, 3, 3, 23, 3, 59, 5,
    7, 3, 3, 11, 3, 3, 5, 37,
    3, 7, 3, 17, 3, 5, 3, 277,
    11, 3, 73, 3, 3, 3, 31, 5,
    23, 3, 367, 3, 131, 3, 3, 3,
    7, 3, 5, 53, 3, 13, 7079, 5,
    7, 3, 3, 41, 3, 5, 3, 7,
    3, 23, 3, 3, 19, 3, 5, 61,
    3, 3, 3, 5, 64871, 3, 11, 3,
    4463, 3, 109, 3, 3, 5, 153749, 3,
    19, 3, 11, 7, 3, 181, 3, 5,
    816217, 7, 3, 3, 3, 47, 5, 43,
    3, 3, 73, 5, 11, 3, 3, 3,
    17, 3, 3, 13, 3, 7, 5, 116243,
    3, 3, 89, 5, 3, 313, 3, 13,
    3, 3, 3, 5, 3, 3, 2028413, 3,
    5, 3, 11, 173, 3, 17, 3, 43,
    3, 47, 3, 7, 3, 5, 3, 2174999,
    3, 139, 3, 31, 3, 11, 3, 7,
    227, 5, 3, 3089, 37, 5, 3, 3,
    3, 5, 41, 3, 13, 3, 3, 373,
    3, 11, 3, 3, 3, 61, 3, 31,
    5, 7, 3, 3, 3, 7, 3, 5,
    3, 8429, 13, 5, 3, 3, 104087, 5,
    17, 3, 3, 3, 11, 7, 3, 5,
    1237, 3, 3, 67, 3, 587, 7, 3,
    3, 7, 35911, 5, 3, 3, 337, 3,
    863, 3, 5, 251, 3, 29, 3, 3,
    3, 92809, 3, 7, 3, 5, 13, 41,
    5, 3, 3, 3, 5, 23, 3, 7,
    3, 5, 3, 19, 4391, 3, 5, 103,
    3, 3, 17, 3, 3, 421, 3, 3,
    7, 3, 9976247, 11, 3, 5, 3, 3,
    3, 3, 3, 3, 11, 3, 3, 13,
    5, 3, 173, 3, 3, 1831, 3, 5557,
    3, 13, 73, 7, 5, 5821, 3, 7,
    3, 5, 853, 3, 3, 443, 3, 5,
    3, 3, 31, 3, 149, 3, 5, 1321,
    10891, 3, 37, 3, 27431, 23, 3, 643,
    3, 3, 409, 3, 5, 3, 3, 3,
    179549, 5, 3, 103, 3, 5, 3, 190669,
    3, 5, 3, 3, 3, 1087, 37, 3,
    5, 73, 3, 3, 17, 13, 3, 3,
    11, 3, 3, 5, 19, 7, 83, 5,
    3, 701, 11, 167, 3, 3, 2239, 3,
    3, 37, 3, 5, 91493, 3, 3, 7,
    13, 3, 487, 3, 7, 5, 3, 17,
    3, 5, 3, 3, 3, 1515841, 3, 5,
    1684259, 3, 11, 3, 3, 19141, 3, 19,
    3, 5, 3, 11, 7, 3, 3, 23,
    3, 823, 3, 1867, 5, 3, 3, 17,
    59, 3, 2927, 5, 11, 3, 5297, 23,
    3, 7, 5, 19, 3, 7, 3, 827,
    3, 5, 3, 7, 3, 3, 3, 3,
    5, 127, 3, 431, 3, 13, 3, 7,
    3, 3, 3, 29, 5, 7, 3, 107,
    3, 7, 3, 2053, 3, 3, 5009, 3,
    3, 3, 3, 5, 31, 3, 3, 89,
    1010473, 3, 11, 3, 139, 3, 43, 5,
    3, 13, 3, 7, 3, 1407877, 3, 23,
    3, 3, 3, 13, 3, 5, 19, 3,
    3, 613, 3, 3, 557, 3, 5, 3,
    3, 709861, 5, 3, 3, 3, 47, 7,
    3, 17, 3, 3, 11, 3, 347, 3,
    3, 3, 13, 11, 3, 17, 3, 7,
    5, 11701, 3, 5, 3, 127, 3, 5,
    3, 7, 3, 3, 83, 13, 3, 5,
    157, 3, 3, 197063, 3, 40529, 2749277, 3,
    7, 5, 61, 3, 3, 7, 3, 3,
    5]

theorem prime_sub_4079 : Nat.Prime (143521252289068 - 4079) := by
  show Nat.Prime 143521252284989
  exact p143521252284989

theorem check_4079 : allC 143521252289068 4079 P10k ds_4079 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 143521252289068 is 4079. -/
theorem minGB_S_4079 : minGB 143521252289068 = 4079 :=
  minGB_eq_of P10k P10k_complete 143521252289068 4079 (by norm_num) (by norm_num) prime_sub_4079 ds_4079 check_4079

def ds_4127 : List ℕ := [
    2, 5, 19, 3, 832841, 3, 2649091, 3,
    5, 3931, 3, 3, 7, 3, 61, 5,
    14741, 3, 3, 365851, 3, 3, 5, 7621,
    3, 17, 3, 33049, 3, 5, 3, 11,
    3395477, 3, 173, 3, 3, 3, 7, 5,
    37, 3, 12324679, 3, 11, 3, 3, 3,
    2715617, 3, 5, 24943, 3, 7, 16691, 5,
    41, 3, 3, 107, 3, 5, 3, 13,
    3, 137, 3, 3, 19, 3, 5, 3964507,
    3, 3, 3, 5, 13, 3, 37, 3,
    7, 3, 443, 3, 3, 5, 251, 3,
    7, 3, 13, 23, 3, 647, 3, 5,
    17, 43, 3, 3, 3, 503, 5, 53,
    3, 3, 7, 5, 79, 3, 3, 3,
    23, 3, 3, 103, 3, 101, 5, 11,
    3, 3, 1579, 5, 3, 13, 3, 29,
    3, 3, 3, 5, 3, 3, 41, 3,
    5, 3, 7, 47, 3, 3530609, 3, 131,
    3, 7, 3, 11, 3, 5, 3, 7,
    3, 31, 3, 1987, 3, 142589, 3, 587,
    2063, 5, 3, 11897, 7963, 5, 3, 3,
    3, 5, 17, 3, 19, 3, 3, 7,
    3, 525493, 3, 3, 3, 7, 3, 190607,
    5, 481939, 3, 3, 3, 409, 3, 5,
    3, 38167, 11, 5, 3, 3, 7, 5,
    3719519, 3, 3, 3, 7, 643, 3, 5,
    37, 3, 3, 7, 3, 23, 11, 3,
    3, 881, 167, 5, 3, 3, 113, 3,
    7, 3, 5, 1523, 3, 11, 3, 3,
    3, 13, 3, 19, 3, 5, 41, 7,
    5, 3, 3, 3, 5, 13, 3, 677,
    3, 5, 3, 19, 5437, 3, 5, 373,
    3, 3, 7, 3, 3, 83, 3, 3,
    12793411, 3, 379, 7, 3, 5, 3, 3,
    3, 3, 3, 3, 563, 3, 3, 43,
    5, 3, 7, 3, 3, 13, 3, 61,
    3, 7, 3659, 109, 5, 7, 3, 13,
    3, 5, 11, 3, 3, 23, 3, 5,
    3, 3, 13, 3, 17, 3, 5, 43,
    23581, 3, 113, 3, 7, 11, 3, 1609,
    3, 3, 7, 3, 5, 3, 3, 3,
    107, 5, 3, 41, 3, 5, 3, 7,
    3, 5, 3, 3, 3, 59, 7, 3,
    5, 13, 3, 3, 7, 18049, 3, 3,
    724433, 3, 3, 5, 19, 23, 13, 5,
    3, 11, 17, 29, 3, 3, 7, 3,
    3, 431, 3, 5, 17, 3, 3, 197,
    6703, 3, 61, 3, 37, 5, 3, 449,
    3, 5, 3, 3, 3, 7, 3, 5,
    599, 3, 2411, 3, 3, 7, 3, 19,
    3, 5, 3, 4933, 181, 3, 3, 25411,
    3, 3203, 3, 11, 5, 3, 3, 127,
    193, 3, 7, 5, 8117, 3, 73, 7,
    3, 17, 5, 11, 3, 5235539, 3, 3331,
    3, 5, 3, 13, 3, 3, 3, 3,
    5, 443, 3, 13, 3, 67, 3, 11,
    3, 3, 3, 7, 5, 457, 3, 41,
    3, 159407, 3, 1258109, 3, 3, 11, 3,
    3, 3, 3, 5, 29, 3, 3, 47,
    7, 3, 167, 3, 337, 3, 797, 5,
    3, 3511, 3, 251, 3, 17, 3, 31,
    3, 3, 3, 7, 3, 5, 19, 3,
    3, 2437, 3, 3, 2531, 3, 5, 3,
    3, 43, 5, 3, 3, 3, 83, 17,
    3, 29, 3, 3, 97, 3, 523, 3,
    3, 3, 11, 19, 3, 7, 3, 311,
    5, 7, 3, 5, 3, 29, 3, 5,
    3, 19, 3, 3, 47, 79, 3, 5,
    23, 3, 3, 7, 3, 7, 12161711, 3,
    3511913, 5, 139, 3, 3, 31, 3, 3,
    5, 17, 11, 3, 3, 3]

theorem prime_sub_4127 : Nat.Prime (194539179143308 - 4127) := by
  show Nat.Prime 194539179139181
  exact p194539179139181

theorem check_4127 : allC 194539179143308 4127 P10k ds_4127 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 194539179143308 is 4127. -/
theorem minGB_S_4127 : minGB 194539179143308 = 4127 :=
  minGB_eq_of P10k P10k_complete 194539179143308 4127 (by norm_num) (by norm_num) prime_sub_4127 ds_4127 check_4127

def ds_4133 : List ℕ := [
    2, 19, 7, 3, 5, 3, 203549, 3,
    83, 11, 3, 3, 5, 3, 7, 257,
    2534941, 3, 3, 5, 3, 3, 59, 7,
    3, 5, 3, 983, 3, 17, 3, 5,
    23, 3, 13, 3, 3, 3, 89, 7,
    41, 3, 5, 3, 1093, 3, 3, 3,
    11, 3, 2800859, 181, 3, 5, 7, 7933,
    19, 3, 3, 5, 3, 11, 3, 5,
    3, 17, 3, 3, 47, 3, 271, 11,
    3, 3, 3, 7, 255733, 3, 5, 3,
    17, 3, 5, 3, 3, 1120001, 53, 3,
    5, 3, 7, 18959, 3, 5, 3, 29,
    7, 5, 3, 3, 3, 11, 31, 1009,
    3, 3, 103, 7, 2129, 3, 3, 3,
    13, 3, 3, 5, 3, 131, 14303, 503911,
    3, 3, 7, 834607, 3, 5, 3, 7,
    3, 3, 3, 661, 3, 3, 5, 3,
    13, 3, 227, 2971, 3, 5, 3, 17,
    3, 19, 3, 379, 3, 293, 3, 5,
    3, 7, 3, 5, 3, 7, 3, 5,
    193, 11, 3, 5, 61, 96323, 3, 3,
    3, 7, 11, 3, 5, 3, 3, 4969,
    3, 5, 3, 3, 3, 5, 3, 7,
    23, 839, 3, 3, 3, 5, 3, 13,
    3, 5, 67, 47, 3, 3, 11, 7,
    1987, 3, 3, 3, 107, 281, 3, 11,
    83761, 3, 3, 5, 3, 7, 13, 3,
    3, 5, 3334307, 29, 3, 3, 19, 3,
    419, 3, 7, 17, 3, 5, 3, 3,
    3, 5, 3, 149, 3, 31, 59, 5,
    19, 3, 3, 3, 13, 7, 3, 5,
    3, 4807813, 3, 5, 13285981, 3, 11, 5573,
    3, 3, 19, 3, 3, 37, 3, 3,
    113, 3, 13, 5, 3, 248587, 3, 3,
    3, 3, 3, 3, 13, 3, 3, 5,
    103, 3, 17, 3, 3, 5, 3, 11,
    3, 37, 5, 1321, 14064023, 5, 3, 17,
    3, 133711, 7, 3, 3, 1612561, 3, 628267,
    3, 3, 197, 3, 47, 3, 7, 23,
    5, 3, 693323, 3, 13, 5, 3, 487507,
    3, 3, 5, 3, 17, 3, 3, 3,
    11, 6781, 3, 31, 3, 29, 3, 97,
    3, 7, 3, 3, 3, 691, 2273, 3,
    13, 11, 3, 3, 5, 7, 3, 3,
    5, 3, 3, 41, 7, 5, 29, 31,
    3, 5, 12271541, 17, 3, 3, 87797, 3,
    3, 5, 3, 107, 19, 3, 3, 1361,
    5, 3, 7, 3, 5, 277, 3, 1693,
    3, 17, 3, 3, 3, 3931, 3, 7,
    43, 3, 5, 3, 3, 122929, 3, 5,
    3, 1409977, 3, 7, 3373, 3, 3, 5,
    3, 7, 3, 89, 593, 3, 3, 5,
    13, 3, 23, 7, 25111, 3, 127, 29,
    3, 13, 281, 17, 3, 11, 3, 5,
    3, 191, 3, 5, 3, 3, 3, 3,
    223, 503, 3, 19, 3, 257, 3, 31,
    3, 3, 3, 5, 5399941, 197, 3, 5,
    3, 5, 3, 1583, 3, 3, 269, 3,
    3, 3, 3, 7, 11, 3, 3, 13,
    69847, 3, 5, 3, 73, 3, 7, 8951,
    3, 7, 3, 5, 3, 307, 3, 5,
    3, 3, 3, 11, 3, 7, 31, 3,
    3, 211, 3, 3, 5, 3, 11, 3,
    3, 7, 41, 3, 3, 3, 7, 5,
    3, 103, 3, 3, 5, 3, 1451, 3,
    3, 3, 5, 433, 3, 10488271, 3, 13297,
    19, 5, 3, 163, 3, 5, 3, 23,
    3, 5, 3, 3, 5, 19, 3, 11,
    805111, 3, 3, 53, 3, 11, 5, 3,
    83, 47, 6101, 3, 3, 13, 3, 3,
    439, 7, 5, 3, 3, 3, 13, 3]

theorem prime_sub_4133 : Nat.Prime (215285889979816 - 4133) := by
  show Nat.Prime 215285889975683
  exact p215285889975683

theorem check_4133 : allC 215285889979816 4133 P10k ds_4133 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 215285889979816 is 4133. -/
theorem minGB_S_4133 : minGB 215285889979816 = 4133 :=
  minGB_eq_of P10k P10k_complete 215285889979816 4133 (by norm_num) (by norm_num) prime_sub_4133 ds_4133 check_4133

def ds_4241 : List ℕ := [
    2, 17, 19, 3, 13, 3, 5, 3,
    7, 29, 3, 3, 6029, 3, 5, 35729,
    23, 3, 3, 17, 3, 3, 2671, 13,
    3, 11, 3, 5, 3, 8069, 3, 349,
    5, 3, 7, 3, 3, 3, 5, 17,
    197, 3, 7, 3, 5, 3, 3, 3,
    5, 3, 7, 461, 3, 8689, 5, 156119,
    79, 3, 3, 5261, 3, 61, 3, 207293,
    3, 5, 3, 3, 5, 3, 3191, 7,
    3, 3, 3, 41, 443, 3, 7, 3,
    2937421, 3, 11, 3, 3, 7, 1864361, 3,
    19, 3, 5, 13, 3, 26557, 3, 1973,
    239, 1045409, 3, 3, 3, 5, 11, 7,
    3, 3, 5, 167, 157, 3, 3, 3,
    5, 3, 3, 241, 3, 5, 7, 37,
    3, 3, 5, 17, 3, 881369, 3, 61547,
    3, 3, 3, 79, 3, 3, 11, 3,
    293, 3, 5, 439, 3, 7, 3, 5,
    3, 331, 3, 5, 3, 7, 3, 37,
    3, 5, 3, 271, 3, 977, 3, 333539,
    5, 53, 3, 1637, 5, 1061, 3, 3,
    3, 67, 101, 3, 7, 3, 3, 433,
    3, 4889, 3, 3, 3, 11, 3, 5,
    13, 97, 3, 3, 3, 1697, 3, 23,
    3, 13, 5, 17, 3, 3, 5, 11,
    269, 3, 3, 3, 13, 5, 3, 7,
    11, 3, 3, 23, 3, 5, 696653, 3,
    3, 197, 5, 19, 3, 3, 7, 3,
    5, 3, 83, 23, 3, 7, 3, 3,
    3, 253531, 3, 5, 3, 7, 17, 913571,
    1373, 3, 3, 3, 11, 31, 3, 13,
    3, 229, 3, 17, 5, 3, 41, 7,
    3, 3, 5, 3, 3, 5, 3, 3,
    5, 3, 31699, 43, 3, 739, 3, 3,
    3, 3, 3, 3, 5, 3, 3, 827,
    103, 3, 5, 3, 3, 7, 3, 5,
    3, 401, 14713, 5, 7, 31, 3, 11,
    3, 907, 43, 3, 3, 5, 3, 743,
    3, 3, 5, 3, 7, 3, 3557, 29363,
    7, 3, 5, 3, 71, 17, 3, 23,
    3, 3, 12998959, 3, 89, 3, 3, 3,
    5, 11, 3, 5, 3, 5927, 3, 5,
    3, 13, 3, 3, 3, 5, 1129, 3,
    7, 4226333, 3, 3, 13, 5, 3, 3,
    14869, 3, 3, 113, 19, 11, 5, 2551933,
    3, 103, 5, 7, 3, 3, 5, 3,
    3, 293, 3, 7, 59, 3, 3, 379,
    557, 3, 11, 3, 17, 179, 3, 5,
    3, 13, 3, 3, 3, 5, 3, 173,
    24407, 3, 7, 3, 3, 7582747, 3, 11,
    3, 7, 3, 5, 149, 3, 3, 4007,
    3, 13, 3, 5, 41, 3, 3, 31,
    7, 3, 5, 59, 367, 3, 5, 11,
    3, 5, 7, 19, 3, 137, 3, 43,
    3, 67, 3, 521, 3, 3, 3, 3,
    19, 7, 3, 20983, 3, 5, 3, 5,
    3, 3, 3, 431, 11, 13, 3, 61,
    3, 11833, 3, 5, 3, 3, 7, 3,
    3, 3, 3, 37, 163411, 3, 3, 5,
    337, 3, 23, 3, 1352873, 3, 5, 1283,
    3, 35099, 3, 1187, 3, 5, 3, 457,
    3, 3, 3, 5, 3, 11, 17, 3,
    3, 5, 3, 3, 41, 3, 7, 3,
    3, 5, 58979, 3, 3, 3, 389, 11605403,
    3, 5, 3, 3, 85751, 3, 7, 3,
    3, 3, 7, 5, 3, 2250337, 3, 5,
    7, 137, 3, 13, 3, 32401, 3, 11,
    3, 19, 3, 3, 13, 5, 3, 23,
    7, 3, 3, 5, 3, 13, 2747351, 3,
    5, 7, 97, 3, 3, 17, 3, 3,
    41, 5023, 47, 3, 3, 3, 5, 3,
    53, 7, 3, 5, 3, 3, 3, 37,
    5, 3, 67, 3]

theorem prime_sub_4241 : Nat.Prime (280780621153342 - 4241) := by
  show Nat.Prime 280780621149101
  exact p280780621149101

theorem check_4241 : allC 280780621153342 4241 P10k ds_4241 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 280780621153342 is 4241. -/
theorem minGB_S_4241 : minGB 280780621153342 = 4241 :=
  minGB_eq_of P10k P10k_complete 280780621153342 4241 (by norm_num) (by norm_num) prime_sub_4241 ds_4241 check_4241

def ds_4373 : List ℕ := [
    2, 29, 17, 3, 7, 3, 127, 3,
    11, 5, 3, 3, 3049, 3, 13, 7,
    5, 3, 3, 31, 3, 3, 23, 5,
    3, 616387, 3, 17, 3, 3307, 3, 827,
    7, 3, 5, 3, 3, 3, 2293, 19,
    5, 3, 137, 3, 443, 3, 3, 3,
    1012703, 3, 53, 5, 3, 43, 31, 7,
    5, 3, 3, 13, 3, 29, 3, 17,
    3, 309121, 3, 3, 7, 3, 11, 5,
    3, 3, 3, 223, 5, 3, 19, 3,
    5, 3, 7, 3, 3, 31, 5, 3,
    191, 3, 29, 5, 3, 109, 3, 61,
    5, 1153, 3, 3, 3, 7, 3557, 5,
    3, 3, 4229, 13, 5, 3, 3, 3,
    11, 3, 3, 7, 3, 47, 37, 5,
    3, 3, 59, 7, 3, 910199, 3, 5,
    3, 3, 3, 19, 3, 3, 163, 3,
    23, 3, 919, 5, 3, 17, 3, 13,
    3, 5, 3, 19, 3, 1223, 3, 11,
    3, 6263, 3, 23, 3, 5, 3, 79,
    11, 587, 3, 19, 7, 13, 3, 3,
    3, 11, 5, 3, 59, 3, 3, 5,
    3, 7, 3, 3, 3, 8557181, 3, 37,
    7, 5, 3, 3, 3, 14713, 3, 29,
    3, 8017, 7, 809, 3, 3, 13, 41,
    5, 3, 3, 3, 5, 11, 3, 43,
    5, 3, 3, 454141, 3, 2819, 5, 3,
    3, 181, 5725927, 13, 3, 3, 5, 3,
    19, 3, 17, 5, 3, 13, 3, 3,
    3, 7, 3, 479, 3, 47, 5, 29,
    7, 3, 3, 3, 122599, 5, 3, 139,
    3, 1319, 3, 23, 7, 3, 313, 5,
    3, 3, 17, 3, 3, 213589, 3, 3,
    601, 3, 5, 223, 3, 7, 3, 3,
    3, 3, 3, 3, 522383, 3, 3, 337,
    53, 3, 151, 3, 3, 11, 3, 23,
    3, 5, 7, 1222253, 131, 31, 3, 5,
    3, 39119, 5, 3, 3, 13, 3, 11,
    3, 3, 7, 3, 5, 3, 229, 5,
    97, 3, 1429, 3, 5, 7, 3, 5,
    3, 3, 53, 3, 7, 3, 3, 3,
    29, 13219, 3, 7, 3, 8999, 3, 11,
    3, 1409, 3, 3, 3, 73, 5, 3,
    11, 5, 3, 3, 17, 421, 3, 3,
    29, 3, 3, 4637, 5, 193, 263, 308437,
    3, 173, 7, 5, 3, 3, 7182047, 3,
    3, 7, 3, 13, 5, 3, 3, 5,
    9679, 3, 5, 3, 13, 563, 3, 7,
    3, 11, 3, 3, 3, 149, 3, 20011,
    5, 3, 6199, 3, 3, 5, 3, 7,
    3, 151, 3, 13, 5, 3, 3, 59,
    3, 5, 3, 79, 23, 3, 3, 11,
    5, 3, 311, 29, 5, 3, 11, 5,
    3, 4021, 17, 5, 3, 5, 3, 13,
    3, 19, 3, 124819, 3, 3, 3, 3,
    67, 5, 3, 5, 3, 19, 3, 13,
    3, 3, 3, 11, 7, 5, 3, 107,
    3, 19, 3, 11, 3, 3, 5, 3,
    3, 3, 3, 11, 5, 3, 3, 43,
    5, 3, 7, 3, 5, 3, 133153, 7,
    3, 5, 3, 257, 3, 47, 3, 313,
    3, 3, 3, 3259, 3, 23, 5, 3,
    3, 13, 3, 3, 7, 3, 19, 3,
    3, 466573, 7, 3, 3, 3, 5, 23,
    3, 17, 3, 3, 6481, 3, 5, 3,
    3, 3, 37, 271, 3, 5, 3, 61,
    181273, 19, 3, 7, 3, 11, 3, 43,
    3, 17, 3, 3, 804847, 7, 3, 269,
    5, 3, 3, 13, 3, 5, 7, 3,
    331, 249583, 5, 3, 3, 5, 3, 3,
    139, 5, 569, 3, 3, 3, 7, 3,
    1601, 5, 3, 1021, 3, 3, 3, 7,
    59, 3, 5, 3, 1427, 3, 7, 5,
    3, 131, 3, 659419, 5, 3, 3, 7,
    3, 5, 3, 3]

theorem prime_sub_4373 : Nat.Prime (319245515537554 - 4373) := by
  show Nat.Prime 319245515533181
  exact p319245515533181

theorem check_4373 : allC 319245515537554 4373 P10k ds_4373 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 319245515537554 is 4373. -/
theorem minGB_S_4373 : minGB 319245515537554 = 4373 :=
  minGB_eq_of P10k P10k_complete 319245515537554 4373 (by norm_num) (by norm_num) prime_sub_4373 ds_4373 check_4373

def ds_4457 : List ℕ := [
    2, 7, 947, 3, 29, 3, 7, 3,
    15187, 5, 3, 3, 239, 3, 17, 11023121,
    5, 3, 3, 509, 3, 3, 47, 5,
    3, 7, 3, 379, 3, 13, 3, 11,
    1193, 3, 5, 3, 3, 3, 601, 23,
    5, 3, 13, 3, 11, 3, 3, 3,
    7, 3, 1439, 5, 3, 17, 37, 11,
    5, 3, 3, 67, 3, 6113, 3, 7,
    3, 1619, 3, 3, 13, 3, 7, 5,
    3, 3, 3, 13933, 5, 3, 139, 3,
    5, 3, 299419, 3, 3, 151, 5, 3,
    11, 3, 499, 5, 3, 19, 3, 13,
    5, 7, 3, 3, 3, 17, 7, 5,
    3, 3, 23, 11, 5, 3, 3, 3,
    353, 3, 3, 113, 3, 7, 128983, 5,
    3, 3, 74531, 67, 3, 37, 3, 5,
    3, 3, 3, 3863, 3, 3, 17, 3,
    7, 3, 71, 5, 3, 347, 3, 127,
    3, 5, 3, 7, 3, 17, 3, 29,
    3, 10631, 3, 173, 3, 5, 3, 7,
    19, 401, 3, 13, 211, 7, 3, 3,
    3, 1762771, 5, 3, 11738729, 3, 3, 5,
    3, 19, 3, 3, 3, 375841, 3, 53,
    1991389, 5, 3, 3, 3, 7, 3, 599,
    3, 31, 11, 7, 3, 3, 1129, 71,
    5, 3, 3, 3, 5, 7, 3, 13,
    5, 3, 3, 43, 3, 349, 5, 3,
    3, 7, 31, 17, 3, 3, 5, 3,
    73, 3, 7499, 5, 3, 11, 3, 3,
    3, 71419, 3, 7, 3, 47, 5, 2803,
    167, 3, 3, 3, 23, 5, 3, 7,
    3, 11, 3, 227, 571, 3, 7, 5,
    3, 3, 163, 3, 3, 61, 3, 3,
    7, 3, 5, 83, 3, 53, 3, 3,
    3, 3, 3, 3, 79, 3, 3, 37,
    7, 3, 11, 3, 3, 1861, 3, 11321,
    3, 5, 67843, 7, 11, 41, 3, 5,
    3, 19, 5, 3, 3, 113, 3, 1811,
    3, 3, 3980549, 3, 5, 3, 13, 5,
    652039, 3, 17, 3, 5, 11, 3, 5,
    3, 3, 13, 3, 3847, 3, 3, 3,
    1309127, 191, 3, 2351, 3, 7, 3, 1960639,
    3, 29, 3, 3, 3, 13, 5, 3,
    43, 5, 3, 3, 127, 244429, 3, 3,
    23, 3, 3, 17, 5, 7, 919, 41,
    3, 11, 29, 5, 3, 3, 37, 3,
    3, 13, 3, 19, 5, 3, 3, 5,
    43, 3, 5, 3, 7, 13697, 3, 19,
    3, 7, 3, 3, 3, 13, 3, 67,
    5, 3, 569, 3, 3, 5, 3, 73,
    3, 59, 3, 15629, 5, 3, 3, 17,
    3, 5, 3, 11, 13, 3, 3, 179999,
    5, 3, 229, 11, 5, 3, 71, 5,
    3, 7, 227, 5, 3, 5, 3, 886021,
    3, 4933, 3, 7, 3, 3, 3, 3,
    7, 5, 3, 5, 3, 6666791, 3, 7,
    3, 3, 3, 107, 4333507, 5, 3, 17189,
    3, 7, 3, 137623, 3, 3, 5, 3,
    3, 3, 3, 53, 5, 3, 3, 23,
    5, 3, 11119, 3, 5, 3, 41, 17,
    3, 5, 3, 7, 3, 13, 3, 29,
    3, 3, 3, 167, 3, 53051, 5, 3,
    3, 6299, 3, 3, 1103, 3, 163, 3,
    3, 17, 13, 3, 3, 3, 5, 7,
    3, 220807, 3, 3, 13, 3, 5, 3,
    3, 3, 11, 1027987, 3, 5, 3, 7,
    3967, 17, 3, 107, 3, 371873, 3, 61,
    3, 7, 3, 3, 19, 109, 3, 7,
    5, 3, 3, 2288243, 3, 5, 5197, 3,
    7, 13, 5, 3, 3, 5, 3, 3,
    677, 5, 7, 3, 3, 3, 17, 3,
    7, 5, 3, 11, 3, 3, 3, 83,
    7, 3, 5, 3, 7680479, 3, 19, 5,
    3, 229, 3, 761, 5, 3, 3, 9151,
    3, 5, 3, 3, 16903, 41, 43, 5,
    11, 3, 3, 3, 23]

theorem prime_sub_4457 : Nat.Prime (332638450261204 - 4457) := by
  show Nat.Prime 332638450256747
  exact p332638450256747

theorem check_4457 : allC 332638450261204 4457 P10k ds_4457 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 332638450261204 is 4457. -/
theorem minGB_S_4457 : minGB 332638450261204 = 4457 :=
  minGB_eq_of P10k P10k_complete 332638450261204 4457 (by norm_num) (by norm_num) prime_sub_4457 ds_4457 check_4457

def ds_4523 : List ℕ := [
    2, 7, 31, 3, 5, 3, 7, 3,
    43, 37, 3, 3, 5, 3, 11, 61,
    7, 3, 3, 5, 3, 3, 251, 151,
    3, 5, 3, 139, 3, 11, 3, 5,
    67, 3, 19391, 3, 3, 3, 47, 181,
    11, 3, 5, 3, 605789, 3, 3, 3,
    7, 3, 617, 19, 3, 5, 23, 211,
    7, 3, 3, 5, 3, 877, 3, 5,
    3, 7177, 3, 3, 17, 3, 7, 13,
    3, 3, 3, 197, 173, 3, 5, 3,
    61, 3, 5, 3, 3, 11, 17, 3,
    5, 3, 19, 7, 3, 5, 3, 2034161,
    11, 5, 3, 3, 3, 1987, 7, 79,
    3, 3, 113, 13, 107, 3, 3, 3,
    4146547, 3, 3, 5, 3, 7, 17, 179,
    3, 3, 317, 127, 3, 5, 3, 467261,
    3, 3, 3, 389, 3, 3, 5, 3,
    7, 3, 43, 19, 3, 5, 3, 13,
    3, 11, 3, 7, 3, 24953, 3, 5,
    3, 2939, 3, 5, 3, 881963, 3, 5,
    23, 593, 3, 5, 3361, 7, 3, 3,
    3, 47, 659, 3, 5, 3, 3, 392599,
    3, 5, 3, 3, 3, 5, 3, 479,
    11, 7, 3, 3, 3, 5, 3, 17,
    3, 5, 73, 7, 3, 3, 13, 23,
    29, 3, 3, 3, 181, 7, 3, 22037,
    2221, 3, 3, 5, 3, 31, 7, 3,
    3, 5, 11, 13, 3, 3, 2753, 3,
    173, 3, 11, 97, 3, 5, 3, 3,
    3, 5, 3, 7, 3, 19, 11, 5,
    2063, 3, 3, 3, 131, 347, 3, 5,
    3, 37, 3, 5, 13, 3, 7, 233621,
    3, 3, 23, 3, 3, 379, 3, 3,
    7, 3, 2699, 5, 3, 179, 3, 3,
    3, 3, 3, 3, 4357, 3, 3, 5,
    7, 3, 124193, 3, 3, 5, 3, 17,
    3, 743, 5, 7, 23, 5, 3, 7,
    3, 40487, 17, 3, 3, 13, 3, 63617,
    3, 3, 11, 3, 22571, 3, 19, 41,
    5, 3, 43, 3, 29, 5, 3, 191,
    3, 3, 5, 3, 13, 3, 3, 3,
    127, 709, 3, 31, 3, 7, 3, 857,
    3, 29, 3, 3, 3, 2423, 13, 3,
    313, 131, 3, 3, 5, 11, 3, 3,
    5, 3, 3, 83, 967, 5, 49003, 11,
    3, 5, 29, 7207, 3, 3, 10859, 3,
    3, 5, 3, 13, 67, 3, 3, 7,
    5, 3, 31, 3, 5, 19, 3, 3407,
    3, 7, 3, 3, 3, 11, 3, 17,
    13, 3, 5, 3, 3, 718453, 3, 5,
    3, 11, 3, 13, 7, 3, 3, 5,
    3, 11, 3, 18255829, 2341, 3, 3, 5,
    23, 3, 17, 2610451, 263, 3, 881, 73,
    3, 7, 257, 29, 3, 7, 3, 5,
    3, 1597, 3, 5, 3, 3, 3, 3,
    7, 13, 3, 43, 3, 37, 3, 7,
    3, 3, 3, 5, 17, 7, 3, 5,
    3, 5, 3, 4271, 3, 3, 41, 3,
    3, 3, 3, 13, 3847, 3, 3, 11,
    37, 3, 5, 3, 83, 3, 17, 11,
    3, 17483, 3, 5, 3, 6581, 3, 5,
    3, 3, 3, 34273, 3, 1453, 31, 3,
    3, 13, 3, 3, 5, 3, 2633, 3,
    3, 227, 27409, 3, 3, 3, 19, 5,
    3, 11, 3, 3, 5, 3, 239, 3,
    3, 3, 5, 97, 3, 12201143, 3, 7,
    37, 5, 3, 47, 3, 5, 3, 5431,
    3, 5, 3, 3, 5, 17, 3, 7,
    197, 3, 3, 13, 3, 6737, 5, 3,
    7, 29, 17, 3, 3, 7, 3, 3,
    11, 61, 5, 3, 3, 3, 53, 3,
    7, 11, 3, 67, 3, 3, 3, 5,
    7, 3, 19, 3, 5, 3, 73, 7,
    3, 5, 3, 31, 5042867, 3, 3, 11,
    3, 97, 3, 3, 3028073, 5, 23, 43,
    5, 3, 3, 3, 5, 19, 157, 5,
    3, 13, 3, 3, 181, 3]

theorem prime_sub_4523 : Nat.Prime (445685413500946 - 4523) := by
  show Nat.Prime 445685413496423
  exact p445685413496423

theorem check_4523 : allC 445685413500946 4523 P10k ds_4523 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 445685413500946 is 4523. -/
theorem minGB_S_4523 : minGB 445685413500946 = 4523 :=
  minGB_eq_of P10k P10k_complete 445685413500946 4523 (by norm_num) (by norm_num) prime_sub_4523 ds_4523 check_4523

def ds_4621 : List ℕ := [
    2, 31, 3, 5, 3, 7, 3, 23,
    3, 3, 857, 5, 3, 229, 3, 3,
    3, 41, 5, 3, 71, 11, 3, 3,
    5, 3, 37, 3, 1759, 3, 5, 3,
    3, 7, 3, 17, 5, 13, 3, 3,
    3, 7, 3, 4300573, 3, 509, 11, 7,
    3, 197, 3, 3, 13, 3, 3, 3,
    3, 2151203, 5, 3, 2596513, 3, 5, 3,
    31, 3, 5009, 5, 3, 7, 3, 3,
    5, 67, 19, 3, 3, 5, 3, 11,
    3, 65167, 3, 7, 331, 3, 3, 5,
    3, 647, 3, 3, 5, 3, 31, 3,
    3, 3, 29, 11, 5, 3, 3, 3,
    23, 5, 3, 3, 3, 7, 5, 107,
    3, 43, 13, 3, 7, 3, 3, 3,
    17, 11, 3, 3, 6689, 3, 13, 3,
    5, 42307, 11, 3, 641, 5, 3, 7,
    3, 5, 3, 3, 7, 3, 4673, 3,
    937, 3, 7, 3, 22133, 3, 5, 3,
    257, 3, 5, 3, 1789, 3, 5, 3,
    3, 3, 5, 3, 3, 3, 37, 5,
    4049, 3, 3, 7, 3, 1950643, 89809, 3,
    1571777, 3, 7, 11, 5, 3, 1223, 3,
    3, 3, 5, 23, 39631, 3, 167, 3,
    17, 3, 3, 3, 11, 37, 3, 3,
    3, 7, 5, 47, 3, 3, 13921, 3,
    3, 19, 5, 3, 1567, 3, 3, 179,
    5, 3, 3, 3, 229693, 7, 3, 1481,
    3, 31, 3, 3, 5, 3, 97, 16212853,
    599, 3, 7, 3, 13, 3, 3, 3,
    3, 11, 1055303, 8263, 3, 3, 5, 3,
    17, 3, 5, 3, 3, 7, 3, 3,
    5507, 5, 3, 5, 11, 3, 211, 7,
    3, 263, 3, 3, 13, 3, 29, 5,
    4297, 1877, 5, 17, 3, 563, 13, 3,
    3, 86533, 3, 7, 5, 3, 131, 3,
    13, 3, 3, 3, 3, 3, 181, 3,
    23, 3, 3, 5, 11, 3, 30059, 3,
    83, 5, 3, 7, 3, 6577, 3, 3,
    3, 59, 3, 17, 3, 3, 7, 3,
    190613, 5, 3, 1303, 3, 127, 971, 19,
    3, 3, 415937, 3, 7, 3, 2467, 3,
    13, 3, 7, 5, 17, 3, 3, 3049,
    3, 3, 6473, 5, 3, 3, 397, 5,
    3, 67, 11, 3, 3, 3, 3, 3,
    5, 3, 3, 3, 5, 534649, 3, 13,
    11, 3, 107, 3, 3, 66797, 5, 3,
    3, 157, 3, 5, 3, 3, 5, 3,
    7, 3, 2029, 5, 43, 3, 6698207, 3,
    3, 5, 3, 821, 11, 3, 31, 3,
    1907, 3, 5, 3, 3, 59, 5, 3,
    17, 3, 73, 3, 3, 11, 5, 3,
    3, 5, 3, 3, 3, 5, 3, 3,
    7, 3, 3, 3, 13, 3, 19, 3,
    181, 3, 5, 3, 11, 1636363, 5, 7,
    3, 3, 17, 3, 7, 3, 7, 3,
    53, 11, 5, 3, 3, 3, 5, 3,
    19, 3, 509, 3, 41, 73, 3, 1087,
    5, 11, 3197063, 3, 3, 7, 19, 3,
    3, 13, 3, 7, 3, 139, 3, 3,
    37, 3, 5, 3, 20695453, 3, 23, 3,
    7, 11, 5, 3, 929, 3, 3, 7,
    5, 3, 103, 19, 3, 7, 3, 5,
    1447, 3, 3, 80051, 5, 11, 3, 3,
    13, 3, 1601, 5, 3, 7, 3, 5,
    487, 1409843, 3, 3, 461, 3, 7, 3,
    3, 3, 17, 3, 5, 3, 59, 3,
    5, 3, 109, 5, 3, 3, 7, 3,
    3, 24907, 589607, 3, 5, 3, 3, 7,
    3, 3, 3, 23, 5, 3, 101, 5,
    3, 3, 3, 3568417, 37, 739, 3, 7,
    3, 3, 12370961, 3, 23, 5, 211, 3,
    3, 13, 3, 17, 3, 41, 3, 3,
    29473, 3, 311, 3, 3, 5, 5, 3,
    7, 3, 5, 89, 3, 3, 3, 3,
    3, 7, 53, 5, 3, 3, 3, 3,
    19, 3, 5, 9227, 3, 19609, 3, 3,
    7, 59, 5, 3, 7, 5, 5309]

theorem prime_sub_4621 : Nat.Prime (557249554749362 - 4621) := by
  show Nat.Prime 557249554744741
  exact p557249554744741

theorem check_4621 : allC 557249554749362 4621 P10k ds_4621 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 557249554749362 is 4621. -/
theorem minGB_S_4621 : minGB 557249554749362 = 4621 :=
  minGB_eq_of P10k P10k_complete 557249554749362 4621 (by norm_num) (by norm_num) prime_sub_4621 ds_4621 check_4621

def ds_4643 : List ℕ := [
    2, 31, 1547537, 3, 7, 3, 837157, 3,
    17, 5, 3, 3, 1523, 3, 19, 7,
    5, 3, 3, 43, 3, 3, 137, 5,
    3, 41, 3, 803717, 3, 293, 3, 37,
    7, 3, 5, 3, 3, 3, 79, 131,
    5, 3, 101, 3, 191, 3, 3, 3,
    11, 3, 569, 5, 3, 31, 14334701, 7,
    5, 3, 3, 8584679, 3, 11, 3, 14033,
    3, 8269, 3, 3, 7, 3, 37, 5,
    3, 3, 3, 661, 5, 3, 7103, 3,
    5, 3, 7, 3, 3, 61, 5, 3,
    22613, 3, 45641, 5, 3, 11, 3, 19,
    5, 107, 3, 3, 3, 7, 443, 5,
    3, 3, 43, 41, 5, 3, 3, 3,
    19, 3, 3, 7, 3, 491837, 233, 5,
    3, 3, 111119, 7, 3, 657557, 3, 5,
    3, 3, 3, 29, 3, 3, 13, 3,
    373, 3, 37, 5, 3, 11, 3, 23,
    3, 5, 3, 173, 3, 70999, 3, 211,
    3, 11, 3, 229, 3, 5, 3, 17,
    977567, 11, 3, 24395339, 7, 8221, 3, 3,
    3, 804161, 5, 3, 8731, 3, 3, 5,
    3, 7, 3, 3, 3, 29, 3, 6229,
    7, 5, 3, 3, 3, 11, 3, 107,
    3, 31, 7, 151, 3, 3, 11, 1117,
    5, 3, 3, 3, 5, 2161, 3, 11,
    5, 3, 3, 19, 3, 13, 5, 3,
    3, 43, 31, 353, 3, 3, 5, 3,
    277, 3, 23801807, 5, 3, 17, 3, 3,
    3, 7, 3, 149, 3, 2753, 5, 4973,
    7, 3, 3, 3, 17, 5, 3, 409,
    3, 89, 3, 1031, 7, 3, 11, 5,
    3, 3, 24365491, 3, 3, 223, 3, 3,
    13, 3, 5, 37633, 3, 7, 3, 3,
    3, 3, 3, 3, 29, 3, 3, 11,
    41, 3, 7498703, 3, 3, 19, 3, 11,
    3, 5, 7, 37, 12911, 13, 3, 5,
    3, 449353, 5, 3, 3, 823, 3, 53,
    3, 3, 7, 3, 5, 3, 17, 5,
    281, 3, 13, 3, 5, 7, 3, 5,
    3, 3, 11, 3, 7, 3, 3, 3,
    11, 19, 3, 7, 3, 13, 3, 17,
    3, 11, 3, 3, 3, 31, 5, 3,
    577, 5, 3, 3, 37, 509, 3, 3,
    149, 3, 3, 43, 5, 460211, 307, 1723,
    3, 19, 7, 5, 3, 3, 13, 3,
    3, 7, 3, 71, 5, 3, 3, 5,
    1619, 3, 5, 3, 23, 13, 3, 7,
    3, 397633, 3, 3, 3, 383, 3, 3181,
    5, 3, 13, 3, 3, 5, 3, 7,
    3, 67, 3, 17, 5, 3, 3, 11,
    3, 5, 3, 139, 15569, 3, 3, 367,
    5, 3, 19, 991, 5, 3, 347, 5,
    3, 53, 619753, 5, 3, 5, 3, 19,
    3, 13, 3, 31, 3, 3, 3, 3,
    17, 5, 3, 5, 3, 11875417, 3, 43,
    3, 3, 3, 2657, 7, 5, 3, 101,
    3, 11897, 3, 13, 3, 3, 5, 3,
    3, 3, 3, 113, 5, 3, 3, 11008457,
    5, 3, 7, 3, 5, 3, 3769589, 7,
    3, 5, 3, 11, 3, 19, 3, 13,
    3, 3, 3, 11, 3, 929, 5, 3,
    3, 67, 3, 3, 7, 3, 11, 3,
    3, 2549863, 7, 3, 3, 3, 5, 139,
    3, 166783, 3, 3, 29, 3, 5, 3,
    3, 3, 12058843, 281, 3, 5, 3, 17,
    13, 71, 3, 7, 3, 1975751, 3, 23,
    3, 13, 3, 3, 53, 7, 3, 11,
    5, 3, 3, 317, 3, 5, 7, 3,
    113081, 59, 5, 3, 3, 5, 3, 3,
    151871, 5, 983, 3, 3, 3, 7, 3,
    2251, 5, 3, 31, 3, 3, 3, 7,
    631, 3, 5, 3, 10709, 3, 7, 5,
    3, 13, 3, 41, 5, 3, 3, 7,
    3, 5, 3, 3, 107, 26489, 29, 5,
    7, 3, 3, 3, 11, 43, 7, 2099,
    3, 19, 3, 3, 11, 3, 109, 7,
    3, 3, 3, 11, 3, 3, 3, 3,
    1980019, 3]

theorem prime_sub_4643 : Nat.Prime (650204506020934 - 4643) := by
  show Nat.Prime 650204506016291
  exact p650204506016291

theorem check_4643 : allC 650204506020934 4643 P10k ds_4643 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 650204506020934 is 4643. -/
theorem minGB_S_4643 : minGB 650204506020934 = 4643 :=
  minGB_eq_of P10k P10k_complete 650204506020934 4643 (by norm_num) (by norm_num) prime_sub_4643 ds_4643 check_4643

def ds_4679 : List ℕ := [
    2, 61, 11, 3, 7, 3, 5, 3,
    13, 4409, 3, 3, 2689807, 3, 5, 7,
    37, 3, 3, 11, 3, 3, 5042837, 8599,
    3, 13, 3, 5, 3, 25307, 3, 67,
    5, 3, 31, 3, 3, 3, 5, 6529,
    7, 3, 4733, 3, 5, 3, 3, 3,
    5, 3, 71, 23, 3, 197, 5, 7,
    11, 3, 3, 37, 3, 521, 3, 139,
    3, 5, 3, 3, 5, 3, 419, 68581,
    3, 3, 3, 79, 7, 3, 11, 3,
    467, 3, 7, 3, 3, 43, 19, 3,
    347, 3, 5, 2306191, 3, 13, 3, 37,
    5517409, 31, 3, 3, 3, 5, 19, 13,
    3, 3, 5, 12301, 7, 3, 3, 3,
    5, 3, 3, 7, 3, 5, 23, 71,
    3, 3, 5, 7, 3, 43, 3, 29,
    3, 3, 3, 53, 3, 3, 28163, 3,
    24977, 3, 5, 7, 3, 719, 3, 5,
    3, 17, 3, 5, 3, 11, 3, 13,
    3, 5, 3, 97, 3, 11, 3, 17,
    5, 212801, 3, 2389, 5, 491, 3, 3,
    3, 73, 7, 3, 2143, 3, 3, 827,
    3, 7, 3, 3, 3, 743, 3, 5,
    7, 113, 3, 3, 3, 6133, 3, 506339,
    3, 101, 5, 11, 3, 3, 5, 61,
    7, 3, 3, 3, 11, 5, 3, 103,
    76471, 3, 3, 5407, 3, 5, 769, 3,
    3, 19, 5, 157, 3, 3, 47, 3,
    5, 3, 197, 7, 3, 17, 3, 3,
    3, 7, 3, 5, 3, 97, 5043691, 71,
    7, 3, 3, 3, 17, 9689, 3, 6451,
    3, 13, 3, 59, 5, 3, 37, 23,
    3, 3, 5, 3, 3, 5, 3, 3,
    5, 3, 89, 11, 3, 7, 3, 3,
    3, 3, 3, 3, 5, 3, 3, 3301147,
    31, 3, 5, 3, 3, 131, 3, 5,
    3, 73, 7, 5, 174679, 19, 3, 11306507,
    3, 13, 41, 3, 3, 5, 3, 53089,
    3, 3, 5, 3, 137, 3, 17, 7,
    401, 3, 5, 3, 83, 7, 3, 13,
    3, 3, 67, 3, 7, 3, 3, 3,
    5, 563, 3, 5, 3, 89, 3, 5,
    3, 19, 3, 3, 3, 5, 23, 3,
    53, 1009, 3, 3, 2251, 5, 3, 3,
    11, 3, 3, 101, 18301, 499, 5, 49139,
    3, 13, 5, 29, 3, 3, 5, 3,
    3, 7, 3, 67, 1549, 3, 3, 11,
    92399, 3, 18055099, 3, 673, 29, 3, 5,
    3, 59, 3, 3, 3, 5, 3, 4369279,
    7, 3, 11, 3, 3, 19, 3, 7,
    3, 13, 3, 5, 71, 3, 3, 58967,
    3, 47, 3, 5, 11, 3, 3, 23,
    17, 3, 5, 337277, 7, 3, 5, 31,
    3, 5, 41, 53, 3, 23, 3, 107,
    3, 43, 3, 11, 3, 3, 3, 3,
    17, 331, 3, 7, 3, 5, 3, 5,
    3, 3, 3, 607, 7, 41, 3, 13,
    3, 4079, 3, 5, 3, 3, 13, 3,
    3, 3, 3, 5131571, 7, 3, 3, 5,
    757, 3, 7, 3, 17, 3, 5, 7,
    3, 1879, 3, 283, 3, 5, 3, 17,
    3, 3, 3, 5, 3, 13, 7, 3,
    3, 5, 3, 3, 7, 3, 17, 3,
    3, 5, 7, 3, 3, 3, 5918909, 127,
    3, 5, 3, 3, 11, 3, 2161, 3,
    3, 3, 813157, 5, 3, 22963, 3, 5,
    671369, 97, 3, 7, 3, 29, 3, 3075313,
    3, 576041, 3, 3, 4127, 5, 3, 13,
    173, 3, 3, 5, 3, 12725591, 7, 3,
    5, 167, 2113, 3, 3, 43577, 3, 3,
    15727, 13, 83, 3, 3, 3, 5, 3,
    1693, 41189, 3, 5, 3, 3, 3, 7,
    5, 3, 11, 3, 23, 3, 7, 149,
    3, 223547, 3, 179, 3637, 3, 3, 5,
    3, 1201, 3, 3, 29, 13, 5, 17,
    7, 3, 3, 3, 853, 5, 7, 139,
    3, 11, 3, 3, 5, 3, 2713, 5,
    3, 3, 3, 1097, 3, 3, 3, 3,
    5, 3, 281, 79, 3, 3, 3, 7]

theorem prime_sub_4679 : Nat.Prime (666956025101272 - 4679) := by
  show Nat.Prime 666956025096593
  exact p666956025096593

theorem check_4679 : allC 666956025101272 4679 P10k ds_4679 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 666956025101272 is 4679. -/
theorem minGB_S_4679 : minGB 666956025101272 = 4679 :=
  minGB_eq_of P10k P10k_complete 666956025101272 4679 (by norm_num) (by norm_num) prime_sub_4679 ds_4679 check_4679

def ds_4721 : List ℕ := [
    2, 5, 17, 3, 7, 3, 479, 3,
    5, 79, 3, 3, 911, 3, 32089, 5,
    11, 3, 3, 11411, 3, 3, 5, 13,
    3, 23, 3, 17, 3, 5, 3, 673,
    7, 3, 7793, 3, 3, 3, 13, 5,
    7, 3, 11, 3, 19, 3, 3, 3,
    53, 3, 5, 23, 3, 71, 11, 5,
    295199, 3, 3, 163, 3, 5, 3, 17,
    3, 347, 3, 3, 7, 3, 5, 12589,
    3, 3, 3, 5, 7, 3, 13, 3,
    11589749, 3, 7, 3, 3, 5, 29, 3,
    107, 3, 983, 13, 3, 847703, 3, 5,
    1483, 11, 3, 3, 3, 7, 5, 9931,
    3, 3, 11, 5, 7, 3, 3, 3,
    17, 3, 3, 7, 3, 1831, 5, 109,
    3, 3, 71, 5, 3, 373, 3, 11,
    3, 3, 3, 5, 3, 3, 277, 3,
    5, 3, 29, 7, 3, 17, 3, 41,
    3, 1779931, 3, 31, 3, 5, 3, 19,
    3, 43, 3, 257, 3, 23, 3, 4663,
    13, 5, 3, 29, 7, 5, 3, 3,
    3, 5, 7, 3, 263, 3, 3, 11,
    3, 7, 3, 3, 3, 7321, 3, 59,
    5, 19, 3, 3, 3, 127, 3, 5,
    3, 11, 7, 5, 3, 3, 137, 5,
    7, 3, 3, 3, 13, 887, 3, 5,
    37, 3, 3, 56531, 3, 2617, 29, 3,
    3, 3673, 263843, 5, 3, 3, 1529419, 3,
    4493, 3, 5, 7, 3, 19, 3, 3,
    3, 7, 3, 2671, 3, 5, 53, 11,
    5, 3, 3, 3, 5, 612809, 3, 13,
    3, 5, 3, 31, 7, 3, 5, 23,
    3, 3, 17, 3, 3, 29, 3, 3,
    701, 3, 11, 83, 3, 5, 3, 3,
    3, 3, 3, 3, 31, 3, 3, 41,
    5, 3, 47, 3, 3, 2753, 3, 643,
    3, 569, 7, 11, 5, 1823, 3, 113,
    3, 5, 1951, 3, 3, 7547, 3, 5,
    3, 3, 7, 3, 11, 3, 5, 7,
    11769013, 3, 325537, 3, 647, 7, 3, 47,
    3, 3, 236983, 3, 5, 3, 3, 3,
    67, 5, 3, 7, 3, 5, 3, 907,
    3, 5, 3, 3, 3, 73, 23, 3,
    5, 281, 3, 3, 13, 7063723, 3, 3,
    71, 3, 3, 5, 37, 47, 332513, 5,
    3, 34403, 7, 89, 3, 3, 19, 3,
    3, 7, 3, 5, 41, 3, 3, 17135431,
    19, 3, 67, 3, 37, 5, 3, 7,
    3, 5, 3, 3, 3, 173, 3, 5,
    7, 3, 29, 3, 3, 211, 3, 7,
    3, 5, 3, 5521, 6829, 3, 3, 7621,
    3, 13, 3, 11429227, 5, 3, 3, 17,
    63367, 3, 11, 5, 7, 3, 4073, 373,
    3, 197381, 5, 953881, 3, 23, 3, 67,
    3, 5, 3, 41, 3, 3, 3, 3,
    5, 31, 3, 7, 3, 23, 3, 17,
    3, 3, 3, 1097, 5, 13, 3, 59,
    3, 61, 3, 47, 3, 3, 179, 3,
    3, 3, 3, 5, 7, 3, 3, 79,
    11, 3, 7, 3, 19, 3, 29, 5,
    3, 1761467, 3, 31, 3, 43, 3, 11,
    3, 3, 3, 89, 3, 5, 7, 3,
    3, 11, 3, 3, 7, 3, 5, 3,
    3, 19, 5, 3, 3, 3, 71, 107,
    3, 13, 3, 3, 1327, 3, 11231111, 3,
    3, 3, 337, 4339, 3, 17, 3, 3347,
    5, 11, 3, 5, 3, 461, 3, 5,
    3, 17, 3, 3, 13, 7, 3, 5,
    29, 3, 3, 181, 3, 13, 7, 3,
    5081, 5, 11, 3, 3, 73, 3, 3,
    5, 149, 10570081, 3, 3, 3, 7, 3,
    5, 3163, 3, 139, 3, 3, 3, 7,
    11, 3, 307, 3, 23, 3, 5, 401,
    3, 41, 3, 5, 17, 3, 3, 7,
    3, 11, 3, 3, 5, 17, 37, 683,
    7, 3, 3, 3, 29, 13, 5, 11,
    3, 5, 3, 3, 23, 3, 5, 7,
    3, 3, 3, 5, 3, 3, 3, 3,
    59, 3, 5, 97, 3, 3, 3, 5,
    11, 13, 5]

theorem prime_sub_4721 : Nat.Prime (814410862537738 - 4721) := by
  show Nat.Prime 814410862533017
  exact p814410862533017

theorem check_4721 : allC 814410862537738 4721 P10k ds_4721 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 814410862537738 is 4721. -/
theorem minGB_S_4721 : minGB 814410862537738 = 4721 :=
  minGB_eq_of P10k P10k_complete 814410862537738 4721 (by norm_num) (by norm_num) prime_sub_4721 ds_4721 check_4721

def ds_4733 : List ℕ := [
    2, 7, 41, 3, 1988933, 3, 5, 3,
    251, 43, 3, 3, 19, 3, 5, 277,
    7, 3, 3, 17, 3, 3, 11, 907,
    3, 7, 3, 5, 3, 13, 3, 2676683,
    5, 3, 11, 3, 3, 3, 5, 17,
    47521, 3, 13, 3, 5, 3, 3, 3,
    5, 3, 1901, 1021, 3, 41, 5, 601,
    7, 3, 3, 11, 3, 1333691, 3, 7,
    3, 5, 3, 3, 5, 3, 7, 5939447,
    3, 3, 3, 19, 79, 3, 47, 3,
    29, 3, 12241, 3, 3, 499, 557, 3,
    16339, 3, 5, 7, 3, 23, 3, 13,
    53, 7, 3, 3, 3, 5, 7, 165527,
    3, 3, 5, 29, 433, 3, 3, 3,
    5, 3, 3, 4273, 3, 5, 2046631, 13,
    3, 3, 5, 17, 3, 59, 3, 15497,
    3, 3, 3, 11, 3, 3, 757, 3,
    7, 3, 5, 11, 3, 257, 3, 5,
    3, 19, 3, 5, 3, 79, 3, 37,
    3, 5, 3, 23003, 3, 14281187, 3, 7,
    5, 19, 3, 13, 5, 7, 3, 3,
    3, 5252081, 152981, 3, 1823, 3, 3, 13,
    3, 43, 3, 3, 3, 17, 3, 5,
    37, 7, 3, 3, 3, 7, 3, 5573,
    3, 19, 5, 7, 3, 3, 5, 9203,
    6715691, 3, 3, 3, 347, 5, 3, 13,
    29, 3, 3, 4261, 3, 5, 7, 3,
    3, 7, 5, 229, 3, 3, 19, 3,
    5, 3, 281, 13, 3, 107, 3, 3,
    3, 41, 3, 5, 3, 1697, 17, 349,
    19, 3, 3, 3, 1856347, 9383071, 3, 7,
    3, 1274759, 3, 11, 5, 3, 7, 19949,
    3, 3, 5, 3, 3, 5, 3, 3,
    5, 3, 13697, 10259, 3, 11, 3, 3,
    3, 3, 3, 3, 5, 3, 3, 29,
    7, 3, 5, 3, 3, 23, 3, 5,
    3, 3347, 241, 5, 857, 11, 3, 7,
    3, 41, 19, 3, 3, 5, 3, 4007,
    3, 3, 5, 3, 769, 3, 11, 233,
    2663, 3, 5, 3, 53, 17, 3, 11,
    3, 3, 13, 3, 97, 3, 3, 3,
    5, 17, 3, 5, 3, 7, 3, 5,
    3, 2519981, 3, 3, 3, 5, 411001, 3,
    29, 13921, 3, 3, 43, 5, 3, 3,
    197, 3, 3, 11, 157, 7, 5, 23,
    3, 131, 5, 11, 3, 3, 5, 3,
    3, 13, 3, 31, 19, 3, 3, 7,
    11, 3, 13, 3, 7, 211, 3, 5,
    3, 7, 3, 3, 3, 5, 3, 132607,
    23, 3, 41, 3, 3, 31, 3, 75431,
    3, 227, 3, 5, 7, 3, 3, 647,
    3, 414763, 3, 5, 13, 3, 3, 3361,
    37, 3, 5, 1009, 2221, 3, 5, 47,
    3, 5, 373, 83, 3, 7, 3, 977,
    3, 5113, 3, 7, 3, 3, 3, 3,
    7, 307, 3, 11, 3, 5, 3, 5,
    3, 3, 3, 1223, 29, 7, 3, 47,
    3, 7, 3, 5, 3, 3, 61, 3,
    3, 3, 3, 37, 1327889, 3, 3, 5,
    1913969, 3, 53, 3, 13, 3, 5, 179497,
    3, 11, 3, 7, 3, 5, 3, 137,
    3, 3, 3, 5, 3, 59, 17, 3,
    3, 5, 3, 3, 11, 3, 839, 3,
    3, 5, 13, 3, 3, 3, 31, 7,
    3, 5, 3, 3, 13, 3, 1022443, 3,
    3, 3, 1567, 5, 3, 11, 3, 5,
    19, 109, 3, 823, 3, 108709, 3, 1291,
    3, 7, 3, 3, 11, 5, 3, 7,
    317, 3, 3, 5, 3, 37, 23509, 3,
    5, 13, 107, 3, 3, 7, 3, 3,
    29, 23, 7, 3, 3, 3, 5, 3,
    7, 199, 3, 5, 3, 3, 3, 37,
    5, 3, 4057, 3, 11, 3, 17, 7,
    3, 7012193, 3, 157, 4170251, 3, 3, 5,
    3, 47, 3, 3, 11, 389, 5, 167,
    29, 3, 3, 3, 26539, 5, 83, 13,
    3, 23, 3, 3, 5, 3, 26251, 5,
    3, 3, 3, 4379017, 3, 3, 3, 3,
    5, 3, 53, 521, 3, 3, 3, 43,
    7, 223, 11, 7, 3, 3]

theorem prime_sub_4733 : Nat.Prime (1025203842512482 - 4733) := by
  show Nat.Prime 1025203842507749
  exact p1025203842507749

theorem check_4733 : allC 1025203842512482 4733 P10k ds_4733 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 1025203842512482 is 4733. -/
theorem minGB_S_4733 : minGB 1025203842512482 = 4733 :=
  minGB_eq_of P10k P10k_complete 1025203842512482 4733 (by norm_num) (by norm_num) prime_sub_4733 ds_4733 check_4733

def ds_4817 : List ℕ := [
    2, 7, 11, 3, 3037, 3, 7, 3,
    577, 5, 3, 3, 29, 3, 313, 1693,
    5, 3, 3, 11, 3, 3, 19, 5,
    3, 7, 3, 13, 3, 12343, 3, 113,
    11, 3, 5, 3, 3, 3, 17, 23,
    5, 3, 47, 3, 19, 3, 3, 3,
    7, 3, 71, 5, 3, 6173, 169607, 13,
    5, 3, 3, 83, 3, 211, 3, 7,
    3, 227, 3, 3, 43, 3, 7, 5,
    3, 3, 3, 14629, 5, 3, 11, 3,
    5, 3, 467, 3, 3, 281, 5, 3,
    3243323, 3, 11, 5, 3, 3154441, 3, 10429,
    5, 7, 3, 3, 3, 3389, 7, 5,
    3, 3, 23, 33099569, 5, 3, 3, 3,
    809, 3, 3, 263, 3, 7, 13, 5,
    3, 3, 17, 10343, 3, 2677, 3, 5,
    3, 3, 3, 311, 3, 3, 31, 3,
    7, 3, 11, 5, 3, 667081, 3, 15410753,
    3, 5, 3, 7, 3, 11, 3, 17,
    3, 13, 3, 29, 3, 5, 3, 7,
    31, 179, 3, 2429363, 37, 7, 3, 3,
    3, 13638059, 5, 3, 27749, 3, 3, 5,
    3, 11, 3, 3, 3, 41, 3, 3257,
    1499, 5, 3, 3, 3, 7, 3, 274627,
    3, 103, 17, 7, 3, 3, 9623891, 19,
    5, 3, 3, 3, 5, 7, 3, 4049,
    5, 3, 3, 124793, 3, 24901291, 5, 3,
    3, 7, 67, 228713, 3, 3, 5, 3,
    857, 3, 13, 5, 3, 19, 3, 3,
    3, 271, 3, 7, 3, 17, 5, 13,
    11, 3, 3, 3, 23, 5, 3, 7,
    3, 41, 3, 47, 29, 3, 7, 5,
    3, 3, 43, 3, 3, 13, 3, 3,
    7, 3, 5, 11, 3, 653, 3, 3,
    3, 3, 3, 3, 11, 3, 3, 97,
    7, 3, 131, 3, 3, 185369, 3, 31,
    3, 5, 13, 7, 229, 61, 3, 5,
    3, 367, 5, 3, 3, 53, 3, 17,
    3, 3, 179, 3, 5, 3, 31, 5,
    10103, 3, 37, 3, 5, 24229, 3, 5,
    3, 3, 191, 3, 43, 3, 3, 3,
    17, 13, 3, 4660501, 3, 7, 3, 223,
    3, 83, 3, 3, 3, 61, 5, 3,
    283, 5, 3, 3, 59, 101, 3, 3,
    11, 3, 3, 97, 5, 7, 103, 557,
    3, 52541, 11, 5, 3, 3, 19, 3,
    3, 37, 3, 167, 5, 3, 3, 5,
    19, 3, 5, 3, 7, 53, 3, 23,
    3, 7, 3, 3, 3, 139, 3, 347,
    5, 3, 11, 3, 3, 5, 3, 401,
    3, 37, 3, 11, 5, 3, 3, 876233,
    3, 5, 3, 13, 11, 3, 3, 1041329,
    5, 3, 2160787, 3491, 5, 3, 43, 5,
    3, 7, 101, 5, 3, 5, 3, 47,
    3, 17, 3, 7, 3, 3, 3, 3,
    7, 5, 3, 5, 3, 3751229, 3, 7,
    3, 3, 3, 171043, 6993551, 5, 3, 23518813,
    3, 7, 3, 55529, 3, 3, 5, 3,
    3, 3, 3, 12413, 5, 3, 3, 23,
    5, 3, 11, 3, 5, 3, 436279, 59,
    3, 5, 3, 7, 3, 117223, 3, 2953,
    3, 3, 3, 947987, 3, 17, 5, 3,
    3, 97, 3, 3, 1291, 3, 1637, 3,
    3, 13, 23, 3, 3, 3, 5, 7,
    3, 349, 3, 3, 11, 3, 5, 3,
    3, 3, 23, 11, 3, 5, 3, 7,
    127, 20269, 3, 11, 3, 13, 3, 37,
    3, 7, 3, 3, 173, 929, 3, 7,
    5, 3, 3, 30785437, 3, 5, 4463, 3,
    7, 383, 5, 3, 3, 5, 3, 3,
    19, 5, 7, 3, 3, 3, 61, 3,
    7, 5, 3, 523, 3, 3, 3, 7129,
    7, 3, 5, 3, 13, 3, 18077, 5,
    3, 103, 3, 67187, 5, 3, 3, 569,
    3, 5, 3, 3, 193, 29, 13, 5,
    47, 3, 3, 3, 17, 1163, 98939, 31,
    3, 11, 3, 3, 3907, 3, 37537, 167,
    3, 3, 3, 67, 3, 3, 3, 3,
    7, 3, 19, 5, 3, 3, 3, 43237,
    5, 11, 47, 7, 3, 3, 43, 37,
    3, 3, 13, 3, 1737433, 5, 3, 3]

theorem prime_sub_4817 : Nat.Prime (1246578722803144 - 4817) := by
  show Nat.Prime 1246578722798327
  exact p1246578722798327

theorem check_4817 : allC 1246578722803144 4817 P10k ds_4817 = true := by decide +kernel

/-- Table 5 row: the least Goldbach prime of 1246578722803144 is 4817. -/
theorem minGB_S_4817 : minGB 1246578722803144 = 4817 :=
  minGB_eq_of P10k P10k_complete 1246578722803144 4817 (by norm_num) (by norm_num) prime_sub_4817 ds_4817 check_4817

end LeanLab.OeSHP2014
