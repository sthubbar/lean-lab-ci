/-
U-1454, P0005 Oliveira e Silva, Herzog, Pardi 2014, Math. Comp. 83, 2033 to 2060.
Reduction lemmas and elementary facts of the paper, zero sorry.
* `evenGoldbach_of_intervals`: p. 2041, Goldbach on the intervals max(4, 10^12 k) < n at most
  10^12 k + 10^12 for k < 4·10^6 gives every even n from 4 to 4·10^18. PROVED.
* `isGoldbachSum_iff_half`, `minGB_spec`, `minGB_eq_of`, `minGB_eq_zero_iff`: the facts behind
  Algorithm 1.3, p. 2039: step 2 may stop at 2p > n, and the first hit is p(n). PROVED.
* `evenGoldbachUpTo_of_cert`: a table n to p with p and n - p certified prime gives
  EvenGoldbachUpTo N. PROVED; vacuity instance at N = 1000.
* Theorem 2.1, p. 2060: `pr3999999999999999791`, `pr3999999999999999691` the two printed primes
  N0 - 209 and N0 - 309, Lucas certificates; `minGB_N0_add_2`, `minGB_N0_add_4`: 211 and 313 are
  the MINIMAL partitions, PROVED; `ternary_of_even_gap`, the paper's argument, PROVED;
  `gapIntervals_of_RS`, Ramare Saouter Theorem 3 with Table 1 rows 59 and 60 give a prime in every
  (x, x + N0] up to N0 Δ; `theorem2_1_of`, odd Goldbach below 209267308 · 4·10^18,
  CONDITIONAL ON EvenGoldbachUpTo (4·10^18), RS Theorem 3, RS row 59, RS row 60.
AI-written Lean code, Claude, 2026-10-22, run 20261022T0003Z-15508. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.Verifications.Pratt

namespace LeanLab.OeSHP2014.U1454

open LeanLab LeanLab.Verifications LeanLab.Verifications.Pratt

/-! ### The interval covering of p. 2041 -/

/-- p. 2041: the runs covered max(4, 10^12 k) < n ≤ 10^12 k + 10^12 for 0 ≤ k < 4·10^6. -/
theorem evenGoldbach_of_intervals
    (hI : ∀ k, k < 4 * 10 ^ 6 → ∀ n, Even n → max 4 (10 ^ 12 * k) < n →
      n ≤ 10 ^ 12 * k + 10 ^ 12 → IsGoldbachSum n) :
    EvenGoldbachUpTo (4 * 10 ^ 18) := by
  intro n hev h4 hn
  rcases Nat.eq_or_lt_of_le h4 with h | h
  · subst h; exact ⟨2, 2, Nat.prime_two, Nat.prime_two, rfl⟩
  · refine hI ((n - 1) / 10 ^ 12) ?_ n hev ?_ ?_
    · norm_num at hn ⊢; omega
    · rw [max_lt_iff]; norm_num; omega
    · norm_num; omega

/-! ### Minimal Goldbach partitions, Algorithm 1.3 -/

/-- A Goldbach partition can be taken with 2p ≤ n: step 2 of Algorithm 1.3 is sound. -/
theorem isGoldbachSum_iff_half (n : ℕ) :
    IsGoldbachSum n ↔ ∃ p, p.Prime ∧ (n - p).Prime ∧ 2 * p ≤ n := by
  constructor
  · rintro ⟨p, q, hp, hq, rfl⟩
    rcases le_total p q with h | h
    · exact ⟨p, hp, by rwa [Nat.add_sub_cancel_left], by omega⟩
    · exact ⟨q, hq, by rwa [Nat.add_sub_cancel], by omega⟩
  · rintro ⟨p, hp, hq, h2⟩
    exact ⟨p, n - p, hp, hq, by omega⟩

theorem exists_of_isGoldbachSum {n : ℕ} (h : IsGoldbachSum n) :
    ∃ p, p.Prime ∧ (n - p).Prime := by
  obtain ⟨p, hp, hq, -⟩ := (isGoldbachSum_iff_half n).mp h
  exact ⟨p, hp, hq⟩

/-- p(n) is a prime, n - p(n) is a prime, and no smaller prime works. -/
theorem minGB_spec {n : ℕ} (h : IsGoldbachSum n) :
    (minGB n).Prime ∧ (n - minGB n).Prime ∧
      ∀ p, p < minGB n → ¬ (p.Prime ∧ (n - p).Prime) := by
  classical
  have hex := exists_of_isGoldbachSum h
  have e : minGB n = Nat.find hex := by unfold minGB; rw [dif_pos hex]
  rw [e]
  exact ⟨(Nat.find_spec hex).1, (Nat.find_spec hex).2, fun p hp => Nat.find_min hex hp⟩

/-- The first hit of Algorithm 1.3 is p(n). -/
theorem minGB_eq_of {n P : ℕ} (hP : P.Prime) (hQ : (n - P).Prime)
    (hmin : ∀ p, p < P → ¬ (p.Prime ∧ (n - p).Prime)) : minGB n = P := by
  classical
  have hex : ∃ p, p.Prime ∧ (n - p).Prime := ⟨P, hP, hQ⟩
  unfold minGB
  rw [dif_pos hex, Nat.find_eq_iff]
  exact ⟨⟨hP, hQ⟩, hmin⟩

/-- p(n) ≤ n / 2 whenever n has a partition. -/
theorem two_mul_minGB_le {n : ℕ} (h : IsGoldbachSum n) : 2 * minGB n ≤ n := by
  obtain ⟨p, hp, hq, h2⟩ := (isGoldbachSum_iff_half n).mp h
  have := minGB_spec h
  by_contra hc
  exact this.2.2 p (by omega) ⟨hp, hq⟩

/-- `minGB` is 0 exactly when there is no partition, so a bound minGB n ≤ c alone does not
say that n is a sum of two primes. -/
theorem minGB_eq_zero_iff (n : ℕ) : minGB n = 0 ↔ ¬ IsGoldbachSum n := by
  constructor
  · intro h0 hG
    have := (minGB_spec hG).1
    rw [h0] at this; exact Nat.not_prime_zero this
  · intro hn
    classical
    have hex : ¬ ∃ p, p.Prime ∧ (n - p).Prime := by
      rintro ⟨p, hp, hq⟩
      exact hn ⟨p, n - p, hp, hq, by
        have := hq.two_le; omega⟩
    unfold minGB; rw [dif_neg hex]

/-! ### Certificates: a table of partitions gives EvenGoldbachUpTo -/

/-- Every even n with 4 ≤ n ≤ N has f n and n - f n passing the kernel primality test. -/
def certOK (f : ℕ → ℕ) (N : ℕ) : Bool :=
  (List.range (N + 1)).all fun n => n % 2 == 1 || n < 4 || (primeB (f n) && primeB (n - f n))

theorem evenGoldbachUpTo_of_cert (f : ℕ → ℕ) (N : ℕ) (h : certOK f N = true) :
    EvenGoldbachUpTo N := by
  intro n hev h4 hn
  have := List.all_eq_true.mp h n (List.mem_range.mpr (by omega))
  have hodd : n % 2 = 0 := Nat.even_iff.mp hev
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.and_eq_true] at this
  rcases this with (h1 | h1) | ⟨hp, hq⟩
  · omega
  · omega
  · exact ⟨f n, n - f n, primeB_sound hp, primeB_sound hq, by
      have := (primeB_sound hq).two_le; omega⟩

/-- The search of Algorithm 1.3 as a function: least p with both primality tests passing. -/
def firstP (n : ℕ) : ℕ :=
  ((List.range (n + 1)).find? fun p => primeB p && primeB (n - p)).getD 0

/-- Vacuity instance: the certificate hypothesis holds for a real table. -/
theorem evenGoldbachUpTo_1000 : EvenGoldbachUpTo 1000 :=
  evenGoldbachUpTo_of_cert firstP 1000 (by decide +kernel)

/-! ### Theorem 2.1, p. 2060 -/

/-- N0 = 4·10^18. -/
abbrev N0 : ℕ := 4 * 10 ^ 18

theorem pr399999999999999979 : Nat.Prime 399999999999999979 := by
  refine pratt 399999999999999979 2 [(2, 1), (3, 3), (23, 1), (211, 1), (239851, 1), (6363769, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Nat.prime_two
  · exact Nat.prime_three
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem pr3999999999999999791 : Nat.Prime 3999999999999999791 := by
  refine pratt 3999999999999999791 11 [(2, 1), (5, 1), (399999999999999979, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact Nat.prime_two
  · exact pB (by decide +kernel)
  · exact pr399999999999999979

theorem pr37379684141669 : Nat.Prime 37379684141669 := by
  refine pratt 37379684141669 2 [(2, 2), (11, 1), (389, 1), (18913, 1), (115471, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact Nat.prime_two
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)

theorem pr3999999999999999691 : Nat.Prime 3999999999999999691 := by
  refine pratt 3999999999999999691 3 [(2, 1), (3, 2), (5, 1), (29, 1), (41, 1), (37379684141669, 1)] (by norm_num)
    (by decide +kernel) ?_ (by decide +kernel) (by decide +kernel)
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Nat.prime_two
  · exact Nat.prime_three
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pB (by decide +kernel)
  · exact pr37379684141669

/-- Divisor certificate below 211 for 4000000000000000002: a proper divisor of p or of 4000000000000000002 - p. -/
def cert2 : List (ℕ × ℕ) := [(2, 2), (3, 3), (4, 2), (5, 421), (6, 2), (7, 5), (8, 2), (9, 3), (10, 2), (11, 17), (12, 2), (13, 7), (14, 2), (15, 3), (16, 2), (17, 5), (18, 2), (19, 13), (20, 2), (21, 3), (22, 2), (23, 383), (24, 2), (25, 5), (26, 2), (27, 3), (28, 2), (29, 263), (30, 2), (31, 21319), (32, 2), (33, 3), (34, 2), (35, 5), (36, 2), (37, 5), (38, 2), (39, 3), (40, 2), (41, 7), (42, 2), (43, 37), (44, 2), (45, 3), (46, 2), (47, 5), (48, 2), (49, 7), (50, 2), (51, 3), (52, 2), (53, 42667), (54, 2), (55, 5), (56, 2), (57, 3), (58, 2), (59, 74959), (60, 2), (61, 11), (62, 2), (63, 3), (64, 2), (65, 5), (66, 2), (67, 5), (68, 2), (69, 3), (70, 2), (71, 13), (72, 2), (73, 25771), (74, 2), (75, 3), (76, 2), (77, 7), (78, 2), (79, 17), (80, 2), (81, 3), (82, 2), (83, 7), (84, 2), (85, 5), (86, 2), (87, 3), (88, 2), (89, 239), (90, 2), (91, 7), (92, 2), (93, 3), (94, 2), (95, 5), (96, 2), (97, 5), (98, 2), (99, 3), (100, 2), (101, 19), (102, 2), (103, 107), (104, 2), (105, 3), (106, 2), (107, 5), (108, 2), (109, 29), (110, 2), (111, 3), (112, 2), (113, 17), (114, 2), (115, 5), (116, 2), (117, 3), (118, 2), (119, 7), (120, 2), (121, 11), (122, 2), (123, 3), (124, 2), (125, 5), (126, 2), (127, 5), (128, 2), (129, 3), (130, 2), (131, 870264299), (132, 2), (133, 7), (134, 2), (135, 3), (136, 2), (137, 5), (138, 2), (139, 7), (140, 2), (141, 3), (142, 2), (143, 11), (144, 2), (145, 5), (146, 2), (147, 3), (148, 2), (149, 11), (150, 2), (151, 467), (152, 2), (153, 3), (154, 2), (155, 5), (156, 2), (157, 5), (158, 2), (159, 3), (160, 2), (161, 7), (162, 2), (163, 491), (164, 2), (165, 3), (166, 2), (167, 5), (168, 2), (169, 13), (170, 2), (171, 3), (172, 2), (173, 11312221), (174, 2), (175, 5), (176, 2), (177, 3), (178, 2), (179, 7369), (180, 2), (181, 7), (182, 2), (183, 3), (184, 2), (185, 5), (186, 2), (187, 11), (188, 2), (189, 3), (190, 2), (191, 37), (192, 2), (193, 11), (194, 2), (195, 3), (196, 2), (197, 5), (198, 2), (199, 23), (200, 2), (201, 3), (202, 2), (203, 7), (204, 2), (205, 5), (206, 2), (207, 3), (208, 2), (209, 11), (210, 2)]

/-- Divisor certificate below 313 for 4000000000000000004: a proper divisor of p or of 4000000000000000004 - p. -/
def cert4 : List (ℕ × ℕ) := [(2, 2), (3, 12056437), (4, 2), (5, 3), (6, 2), (7, 421), (8, 2), (9, 3), (10, 2), (11, 3), (12, 2), (13, 17), (14, 2), (15, 3), (16, 2), (17, 3), (18, 2), (19, 5), (20, 2), (21, 3), (22, 2), (23, 3), (24, 2), (25, 5), (26, 2), (27, 3), (28, 2), (29, 3), (30, 2), (31, 263), (32, 2), (33, 3), (34, 2), (35, 5), (36, 2), (37, 83), (38, 2), (39, 3), (40, 2), (41, 3), (42, 2), (43, 7), (44, 2), (45, 3), (46, 2), (47, 3), (48, 2), (49, 7), (50, 2), (51, 3), (52, 2), (53, 3), (54, 2), (55, 5), (56, 2), (57, 3), (58, 2), (59, 3), (60, 2), (61, 74959), (62, 2), (63, 3), (64, 2), (65, 5), (66, 2), (67, 31), (68, 2), (69, 3), (70, 2), (71, 3), (72, 2), (73, 13), (74, 2), (75, 3), (76, 2), (77, 7), (78, 2), (79, 5), (80, 2), (81, 3), (82, 2), (83, 3), (84, 2), (85, 5), (86, 2), (87, 3), (88, 2), (89, 3), (90, 2), (91, 7), (92, 2), (93, 3), (94, 2), (95, 5), (96, 2), (97, 14521697), (98, 2), (99, 3), (100, 2), (101, 3), (102, 2), (103, 19), (104, 2), (105, 3), (106, 2), (107, 3), (108, 2), (109, 5), (110, 2), (111, 3), (112, 2), (113, 3), (114, 2), (115, 5), (116, 2), (117, 3), (118, 2), (119, 7), (120, 2), (121, 11), (122, 2), (123, 3), (124, 2), (125, 5), (126, 2), (127, 7), (128, 2), (129, 3), (130, 2), (131, 3), (132, 2), (133, 7), (134, 2), (135, 3), (136, 2), (137, 3), (138, 2), (139, 5), (140, 2), (141, 3), (142, 2), (143, 11), (144, 2), (145, 5), (146, 2), (147, 3), (148, 2), (149, 3), (150, 2), (151, 11), (152, 2), (153, 3), (154, 2), (155, 5), (156, 2), (157, 47), (158, 2), (159, 3), (160, 2), (161, 7), (162, 2), (163, 127), (164, 2), (165, 3), (166, 2), (167, 3), (168, 2), (169, 13), (170, 2), (171, 3), (172, 2), (173, 3), (174, 2), (175, 5), (176, 2), (177, 3), (178, 2), (179, 3), (180, 2), (181, 7369), (182, 2), (183, 3), (184, 2), (185, 5), (186, 2), (187, 11), (188, 2), (189, 3), (190, 2), (191, 3), (192, 2), (193, 37), (194, 2), (195, 3), (196, 2), (197, 3), (198, 2), (199, 5), (200, 2), (201, 3), (202, 2), (203, 7), (204, 2), (205, 5), (206, 2), (207, 3), (208, 2), (209, 11), (210, 2), (211, 7), (212, 2), (213, 3), (214, 2), (215, 5), (216, 2), (217, 7), (218, 2), (219, 3), (220, 2), (221, 13), (222, 2), (223, 1259), (224, 2), (225, 3), (226, 2), (227, 3), (228, 2), (229, 5), (230, 2), (231, 3), (232, 2), (233, 3), (234, 2), (235, 5), (236, 2), (237, 3), (238, 2), (239, 3), (240, 2), (241, 16783651), (242, 2), (243, 3), (244, 2), (245, 5), (246, 2), (247, 13), (248, 2), (249, 3), (250, 2), (251, 3), (252, 2), (253, 11), (254, 2), (255, 3), (256, 2), (257, 3), (258, 2), (259, 7), (260, 2), (261, 3), (262, 2), (263, 3), (264, 2), (265, 5), (266, 2), (267, 3), (268, 2), (269, 3), (270, 2), (271, 557), (272, 2), (273, 3), (274, 2), (275, 5), (276, 2), (277, 22343), (278, 2), (279, 3), (280, 2), (281, 3), (282, 2), (283, 11), (284, 2), (285, 3), (286, 2), (287, 7), (288, 2), (289, 17), (290, 2), (291, 3), (292, 2), (293, 3), (294, 2), (295, 5), (296, 2), (297, 3), (298, 2), (299, 13), (300, 2), (301, 7), (302, 2), (303, 3), (304, 2), (305, 5), (306, 2), (307, 13), (308, 2), (309, 3), (310, 2), (311, 3), (312, 2)]

/-- The divisor certificate check: each p from 2 to P - 1 has a proper divisor d of p or of
m - p. -/
def divOK (m P : ℕ) (L : List (ℕ × ℕ)) : Bool :=
  (List.range P).all fun p => p < 2 ||
    (let d := (L.lookup p).getD 0
     1 < d && ((d < p && p % d == 0) || (d < m - p && (m - p) % d == 0)))

theorem divOK_sound {m P : ℕ} {L : List (ℕ × ℕ)} (h : divOK m P L = true) :
    ∀ p, p < P → ¬ (p.Prime ∧ (m - p).Prime) := by
  intro p hp ⟨hpp, hq⟩
  have := List.all_eq_true.mp h p (List.mem_range.mpr hp)
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at this
  rcases this with h2 | ⟨h1, ⟨hlt, hmod⟩ | ⟨hlt, hmod⟩⟩
  · exact absurd hpp.two_le (by omega)
  · exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hmod) h1 hlt hpp
  · exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hmod) h1 hlt hq

/-- p(N0 + 2) = 211, the partition printed in the proof of Theorem 2.1. -/
theorem minGB_N0_add_2 : minGB (N0 + 2) = 211 := by
  refine minGB_eq_of (by norm_num) ?_ (divOK_sound (m := N0 + 2) (P := 211) (L := cert2)
    (by decide +kernel))
  rw [show N0 + 2 - 211 = 3999999999999999791 by norm_num]; exact pr3999999999999999791

/-- p(N0 + 4) = 313, the partition printed in the proof of Theorem 2.1. -/
theorem minGB_N0_add_4 : minGB (N0 + 4) = 313 := by
  refine minGB_eq_of (by norm_num) ?_ (divOK_sound (m := N0 + 4) (P := 313) (L := cert4)
    (by decide +kernel))
  rw [show N0 + 4 - 313 = 3999999999999999691 by norm_num]; exact pr3999999999999999691

/-- The two extra partitions extend the even range by 4. -/
theorem even_N0_add_4 (h : EvenGoldbachUpTo N0) : EvenGoldbachUpTo (N0 + 4) := by
  intro n hev h4 hn
  obtain ⟨k, hk⟩ := hev
  have hN : N0 = 4000000000000000000 := by norm_num [N0]
  rcases Nat.lt_or_ge N0 n with hbig | hle
  · rcases (show n = N0 + 2 ∨ n = N0 + 4 by omega) with rfl | rfl
    · exact ⟨211, 3999999999999999791, by norm_num, pr3999999999999999791, by norm_num⟩
    · exact ⟨313, 3999999999999999691, by norm_num, pr3999999999999999691, by norm_num⟩
  · exact h n ⟨k, hk⟩ h4 hle

/-- The argument of Theorem 2.1 for any B: even Goldbach to B + 4 and a prime in every
(x, x + B] up to X give odd Goldbach to X + 5. -/
theorem ternary_of_even_gap (B X : ℕ) (hB : 4 ≤ B) (hE : EvenGoldbachUpTo (B + 4))
    (hG : ∀ x, 2 ≤ x → x + B ≤ X → ∃ p, p.Prime ∧ x < p ∧ p ≤ x + B) :
    TernaryGoldbachUpTo (X + 5) := by
  intro n ho h7 hn
  rcases le_or_gt n (B + 7) with hs | hl
  · have hev : Even (n - 3) := Nat.Odd.sub_odd ho (by decide)
    obtain ⟨q, r, hq, hr, hqr⟩ := hE (n - 3) hev (by omega) (by omega)
    exact ⟨3, q, r, Nat.prime_three, hq, hr, by omega⟩
  · obtain ⟨r, hr, hxr, hrx⟩ := hG (n - B - 5) (by omega) (by omega)
    have hr2 : r ≠ 2 := by omega
    have hev : Even (n - r) := Nat.Odd.sub_odd ho (hr.eq_two_or_odd'.resolve_left hr2)
    obtain ⟨q, s, hq, hs, hqs⟩ := hE (n - r) hev (by omega) (by omega)
    exact ⟨r, q, s, hr, hq, hs, by omega⟩

/-- Ramaré, Saouter 2003, Theorem 3, as the lab states it in RamareSaouter2003.theorem3. -/
def RS3 : Prop := ∀ x : ℝ, 10726905041 < x →
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28314000) < p ∧ (p : ℝ) ≤ x

/-- Ramaré, Saouter 2003, Theorem 2 with Table 1 row log x0 = 59, as the lab states it. -/
def RS59 : Prop := ∀ x : ℝ, Real.exp 59 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 209257759) < p ∧ (p : ℝ) ≤ x

/-- Ramaré, Saouter 2003, Theorem 2 with Table 1 row log x0 = 60, Δ = 209 267 308. -/
def RS60 : Prop := ∀ x : ℝ, Real.exp 60 ≤ x →
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 209267308) < p ∧ (p : ℝ) ≤ x

/-- From a prime in (y (1 - 1/D), y] with y = x + G ≤ D G, a prime in (x, x + G]. -/
theorem prime_in_of_ratio (D : ℝ) (hD : 0 < D) (x G : ℕ)
    (hy : ((x + G : ℕ) : ℝ) ≤ D * G)
    (h : ∃ p : ℕ, p.Prime ∧ ((x + G : ℕ) : ℝ) * (1 - 1 / D) < p ∧ (p : ℝ) ≤ ((x + G : ℕ) : ℝ)) :
    ∃ p, p.Prime ∧ x < p ∧ p ≤ x + G := by
  obtain ⟨p, hp, hl, hu⟩ := h
  refine ⟨p, hp, ?_, by exact_mod_cast hu⟩
  have hdiv : ((x + G : ℕ) : ℝ) / D ≤ G := by rw [div_le_iff₀ hD]; linarith
  have e : ((x + G : ℕ) : ℝ) * (1 - 1 / D) = ((x + G : ℕ) : ℝ) - ((x + G : ℕ) : ℝ) / D := by
    field_simp
  have : (x : ℝ) < p := by
    rw [e] at hl; push_cast at hl hdiv; linarith
  exact_mod_cast this

theorem exp59_le : Real.exp 59 ≤ 28314000 * (N0 : ℝ) := by
  have h1 := Real.exp_one_lt_d9
  have e : Real.exp 59 = Real.exp 1 ^ 59 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : Real.exp 1 ^ 59 ≤ (2.72 : ℝ) ^ 59 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 59
  refine this.trans ?_
  norm_num [N0]

theorem exp60_le : Real.exp 60 ≤ 209257759 * (N0 : ℝ) := by
  have h1 := Real.exp_one_lt_d9
  have e : Real.exp 60 = Real.exp 1 ^ 60 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : Real.exp 1 ^ 60 ≤ (2.72 : ℝ) ^ 60 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 60
  refine this.trans ?_
  norm_num [N0]

/-- The covering argument for a general block length G. -/
theorem gapIntervals_gen (G : ℕ) (hG : (10726905041 : ℝ) < G)
    (e59 : Real.exp 59 ≤ 28314000 * (G : ℝ)) (e60 : Real.exp 60 ≤ 209257759 * (G : ℝ))
    (h3 : RS3) (h59 : RS59) (h60 : RS60) :
    ∀ x, 2 ≤ x → x + G ≤ 209267308 * G → ∃ p, p.Prime ∧ x < p ∧ p ≤ x + G := by
  intro x hx hX
  have hyR : ((x + G : ℕ) : ℝ) ≤ 209267308 * (G : ℝ) := by exact_mod_cast hX
  have hxG : (G : ℝ) ≤ ((x + G : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg x : (0 : ℝ) ≤ x)]
  rcases le_or_gt (x + G) (28314000 * G) with c1 | c1
  · exact prime_in_of_ratio 28314000 (by norm_num) x G (by exact_mod_cast c1)
      (h3 _ (by linarith))
  rcases le_or_gt (x + G) (209257759 * G) with c2 | c2
  · refine prime_in_of_ratio 209257759 (by norm_num) x G (by exact_mod_cast c2) (h59 _ ?_)
    have : (28314000 * G : ℝ) ≤ ((x + G : ℕ) : ℝ) := by exact_mod_cast c1.le
    exact e59.trans this
  · refine prime_in_of_ratio 209267308 (by norm_num) x G hyR (h60 _ ?_)
    have : (209257759 * G : ℝ) ≤ ((x + G : ℕ) : ℝ) := by exact_mod_cast c2.le
    exact e60.trans this

/-- Up to N0 Δ every interval (x, x + N0] holds a prime, from RS Theorem 3, rows 59 and 60. -/
theorem gapIntervals_of_RS (h3 : RS3) (h59 : RS59) (h60 : RS60) :
    ∀ x, 2 ≤ x → x + N0 ≤ 209267308 * N0 → ∃ p, p.Prime ∧ x < p ∧ p ≤ x + N0 :=
  gapIntervals_gen N0 (by norm_num [N0]) exp59_le exp60_le h3 h59 h60

/-- Theorem 2.1, p. 2060: every odd n with 5 < n < 209267308 · 4·10^18 is a sum of three
primes. CONDITIONAL ON the even range and the three Ramaré, Saouter inputs. -/
theorem theorem2_1_of (hE : EvenGoldbachUpTo N0) (h3 : RS3) (h59 : RS59) (h60 : RS60) :
    TernaryGoldbachUpTo (209267308 * N0 - 1) := by
  have := ternary_of_even_gap N0 (209267308 * N0 - 6) (by norm_num [N0]) (even_N0_add_4 hE)
    (fun x hx hX => gapIntervals_of_RS h3 h59 h60 x hx (by omega))
  rwa [show 209267308 * N0 - 6 + 5 = 209267308 * N0 - 1 by norm_num [N0]] at this

/-- The printed value: 209267308 · 4·10^18 = 8.37069232 · 10^26. -/
theorem theorem2_1_value : 209267308 * N0 = 837069232 * 10 ^ 18 := by norm_num [N0]

end LeanLab.OeSHP2014.U1454

open LeanLab.OeSHP2014.U1454 in
#print axioms evenGoldbach_of_intervals
open LeanLab.OeSHP2014.U1454 in
#print axioms isGoldbachSum_iff_half
open LeanLab.OeSHP2014.U1454 in
#print axioms minGB_spec
open LeanLab.OeSHP2014.U1454 in
#print axioms minGB_eq_of
open LeanLab.OeSHP2014.U1454 in
#print axioms two_mul_minGB_le
open LeanLab.OeSHP2014.U1454 in
#print axioms minGB_eq_zero_iff
open LeanLab.OeSHP2014.U1454 in
#print axioms evenGoldbachUpTo_of_cert
open LeanLab.OeSHP2014.U1454 in
#print axioms evenGoldbachUpTo_1000
open LeanLab.OeSHP2014.U1454 in
#print axioms pr3999999999999999791
open LeanLab.OeSHP2014.U1454 in
#print axioms pr3999999999999999691
open LeanLab.OeSHP2014.U1454 in
#print axioms minGB_N0_add_2
open LeanLab.OeSHP2014.U1454 in
#print axioms minGB_N0_add_4
open LeanLab.OeSHP2014.U1454 in
#print axioms even_N0_add_4
open LeanLab.OeSHP2014.U1454 in
#print axioms ternary_of_even_gap
open LeanLab.OeSHP2014.U1454 in
#print axioms gapIntervals_of_RS
open LeanLab.OeSHP2014.U1454 in
#print axioms theorem2_1_of
open LeanLab.OeSHP2014.U1454 in
#print axioms theorem2_1_value
