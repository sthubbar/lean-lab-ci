/-
P0042 Granville, van de Lune, te Riele 1989, Tables 1, 2, 3, 4 and the Section 2 to 4 text,
beside the paper; read in Claude in Chrome 2026-10-18 from the CWI page images, run
20261018T1103Z-12430, unit U-0942.
PROVED, zero sorry: PR(I) is the I-th odd prime on every row of Tables 1 and 2; Table 1's
percent column is the running sum of its L column over the 5·10^9 even numbers to 10^10, to the
printed two decimals on rows 1 to 24, and its two ratios 2.59 and 2.91; the twin prime remark
on the table rows; for even n ≥ 6, p(n) = 3 iff n - 3 is prime, the identity behind
L(3, x) = π(x - 3) - 1; every quotient of Table 2 except row 102, FINDING, whose two quotients
are inverted; Table 3 as the first 37 Sinisalo rows with the same quotients; every E(q) of
Table 4 from the definition, exact rationals, except E(73), FINDING, printed 30.825, value
49326/1595 = 30.9254; and the stars of Table 4 mark exactly the q with E(q) below the previous
row. The L counts themselves are the authors' computation, cited.
AI-written Lean code, Claude, 2026-10-18. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Verifications.Top50.Base
import LeanLab.Richstein2001.Table1
import LeanLab.Richstein2001.Gap
import LeanLab.Sinisalo1993.Tables
import LeanLab.Sinisalo1993.Quot1
import LeanLab.Sinisalo1993.Quot2
import LeanLab.Sinisalo1993.Quot3

namespace LeanLab.GvLtR1989.Paper

open LeanLab LeanLab.Verifications LeanLab.Verifications.Top50

/-! ### Table 1 -/

/-- Table 1 rows (I, q, S(q), L(q, 10^10), percent times 100). -/
def table1 : List (ℕ × ℕ × ℕ × ℕ × ℕ) := [
    (1, 3, 6, 455052510, 910),
    (2, 5, 12, 427649831, 1765),
    (3, 7, 30, 400229833, 2566),
    (4, 11, 124, 350840599, 3268),
    (5, 13, 122, 320898559, 3909),
    (6, 17, 418, 276936926, 4463),
    (7, 19, 98, 267951521, 4999),
    (8, 23, 220, 226031301, 5451),
    (9, 29, 346, 199319687, 5850),
    (10, 31, 308, 201862574, 6254),
    (11, 37, 1274, 170425547, 6594),
    (12, 41, 1144, 147748455, 6890),
    (13, 43, 962, 138381620, 7167),
    (14, 47, 556, 118054048, 7403),
    (15, 53, 2512, 101504888, 7606),
    (16, 59, 3526, 90311298, 7786),
    (17, 61, 1382, 106906523, 8000),
    (18, 67, 1856, 91418970, 8183),
    (19, 71, 4618, 68641994, 8320),
    (20, 73, 992, 69457153, 8459),
    (21, 79, 3818, 69182416, 8598),
    (22, 83, 7432, 53268347, 8704),
    (23, 89, 12778, 47140891, 8798),
    (24, 97, 5978, 51345000, 8901),
    (29, 113, 19696, 26537015, 9263),
    (30, 127, 6008, 31047922, 9325),
    (55, 263, 485326, 2842690, 9900),
    (56, 269, 407128, 2524569, 9905),
    (57, 271, 137708, 4557244, 9914),
    (65, 317, 686638, 1351658, 9951),
    (66, 331, 128168, 2447734, 9956),
    (103, 569, 17726098, 65419, 9997),
    (104, 571, 4493498, 169264, 9997),
    (108, 599, 15860818, 41965, 9998),
    (109, 601, 1077422, 122261, 9998)]

/-- PR(I), the I-th odd prime, is the prime at index I of P10k, which starts at 2. -/
theorem table1_PR : table1.all (fun x => P10k[x.1]? == some x.2.1) = true := by decide +kernel

/-- Rows 1 to 24 are consecutive; the percent column is the running sum of L over 5·10^9,
to the printed two decimals. -/
def runOK : List (ℕ × ℕ × ℕ × ℕ × ℕ) → ℕ → Bool
  | [], _ => true
  | x :: t, c =>
    let c' := c + x.2.2.2.1
    decide (((2 * x.2.2.2.2 - 1 : ℕ) : ℚ) / 200 ≤ 100 * (c' : ℚ) / (5 * 10 ^ 9)) &&
    decide (100 * (c' : ℚ) / (5 * 10 ^ 9) < ((2 * x.2.2.2.2 + 1 : ℕ) : ℚ) / 200) && runOK t c'

theorem table1_percent : runOK (table1.take 24) 0 = true := by decide +kernel

/-- The two quotients printed in Table 1, rows 104 and 109. -/
theorem table1_ratios : (169264 : ℚ) / 65419 ∈ Set.Ico (2585 / 1000) (2595 / 1000) ∧
    (122261 : ℚ) / 41965 ∈ Set.Ico (2905 / 1000) (2915 / 1000) := by
  constructor <;> constructor <;> norm_num

/-- Section 4: for twin primes in Table 1, L(q) < L(q + 2) except (3,5), (5,7), (11,13),
(17,19), (41,43). On the table rows: -/
theorem twin_remark :
    (table1.filter (fun x => (table1.map (·.2.1)).contains (x.2.1 + 2))).map
      (fun x => (x.2.1, decide (x.2.2.2.1 < ((table1.find? (·.2.1 = x.2.1 + 2)).map (·.2.2.2.1)).getD 0))) =
    [(3, false), (5, false), (11, false), (17, false), (29, true), (41, false), (59, true),
     (71, true), (269, true), (569, true), (599, true)] := by decide +kernel

/-- For even n ≥ 6, the least Goldbach prime is 3 exactly when n - 3 is prime; so the even
n ≤ x with p(n) = 3 are 3 + r for the odd primes r ≤ x - 3, and L(3, x) = π(x - 3) - 1. -/
theorem minGB_eq_three {n : ℕ} (he : Even n) (h6 : 6 ≤ n) : minGB n = 3 ↔ (n - 3).Prime := by
  constructor
  · intro h
    exact (Richstein2001.minGB_spec h (by norm_num)).2
  · intro h
    classical
    have hex : ∃ q, q.Prime ∧ (n - q).Prime := ⟨3, Nat.prime_three, h⟩
    unfold minGB
    rw [dif_pos hex, Nat.find_eq_iff]
    refine ⟨⟨Nat.prime_three, h⟩, fun m hm hmp => ?_⟩
    interval_cases m
    · exact Nat.not_prime_zero hmp.1
    · exact Nat.not_prime_one hmp.1
    · obtain ⟨k, hk⟩ := he
      have h2 : n - 2 = 2 * (k - 1) := by omega
      have := hmp.2
      rw [h2] at this
      exact Nat.not_prime_mul (by norm_num) (by omega) this

/-! ### Table 2 -/

/-- Table 2 rows (I, q, A, quotient A times 100, B, quotient B times 100); 0 for no quotient. -/
def table2 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
    (101, 557, 12981, 0, 15822, 0),
    (102, 563, 10284, 126, 12438, 127),
    (103, 569, 9057, 88, 11101, 89),
    (104, 571, 22794, 252, 26904, 242),
    (105, 577, 14957, 66, 18089, 67),
    (106, 587, 8511, 57, 10718, 59),
    (107, 593, 6651, 78, 8349, 78),
    (108, 599, 5898, 89, 7476, 90),
    (109, 601, 16661, 282, 19696, 263),
    (110, 607, 11148, 67, 13421, 68),
    (151, 881, 358, 0, 540, 0),
    (152, 883, 539, 151, 736, 136),
    (153, 887, 309, 57, 374, 51),
    (154, 907, 499, 161, 693, 185),
    (155, 911, 250, 50, 385, 56),
    (156, 919, 538, 215, 702, 182),
    (157, 929, 217, 40, 293, 42),
    (158, 937, 337, 155, 447, 153),
    (159, 941, 207, 61, 242, 54),
    (160, 947, 177, 86, 250, 103)]

theorem table2_PR : table2.all (fun x => P10k[x.1]? == some x.2.1) = true := by decide +kernel

/-- c is a / b to the printed two decimals. -/
def q2 (a b c : ℕ) : Bool :=
  decide (((2 * c - 1 : ℕ) : ℚ) / 200 ≤ (a : ℚ) / b) && decide ((a : ℚ) / b < ((2 * c + 1 : ℕ) : ℚ) / 200)

/-- Each printed quotient checked as current over previous; the rows where that fails. -/
def badRows : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) → List ℕ
  | x :: y :: t => (if y.2.2.2.1 = 0 ∨ (q2 y.2.2.1 x.2.2.1 y.2.2.2.1 && q2 y.2.2.2.2.1 x.2.2.2.2.1 y.2.2.2.2.2)
      then [] else [y.1]) ++ badRows (y :: t)
  | _ => []

/-- FINDING: every quotient of Table 2 is current over previous except row 102. -/
theorem table2_bad : badRows table2 = [102] := by decide +kernel

/-- Row 102 printed 1.26 and 1.27 are previous over current; current over previous is 0.79. -/
theorem table2_row102 : q2 12981 10284 126 = true ∧ q2 15822 12438 127 = true ∧
    q2 10284 12981 79 = true ∧ q2 12438 15822 79 = true := by decide +kernel

/-! ### Table 3 -/

/-- Table 3 is Sinisalo's Table 1 through n = 12703943222: the records of p(n) to 2·10^10. -/
def table3 : List (ℕ × ℕ) := Sinisalo1993.table1.take 37

theorem table3_eq_recTable :
    table3 = (recTable.filter (fun x => decide (6 ≤ x.2 ∧ x.2 ≤ 2 * 10 ^ 10))).map
      (fun x => (x.2, x.1)) := by decide +kernel

theorem table3_minGB : ∀ x ∈ table3, minGB x.1 = x.2 :=
  fun x hx => Sinisalo1993.table1_minGB x (List.mem_of_mem_take hx)

/-- Section 3: Table 3 gives p(n) ≤ 2029 on its rows; the full range is cited. -/
theorem table3_le_2029 : ∀ x ∈ table3, x.2 ≤ 2029 := by decide +kernel

/-! ### Table 4 -/

/-- E(q), computed: sum over odd primes r < q of the product over primes p ≥ 3 dividing
q - r of (p - 1)/(p - 2). -/
def E (q : ℕ) : ℚ := ∑ r ∈ (Finset.range q).filter (fun r => 3 ≤ r ∧ primeB r = true),
  ∏ p ∈ (Finset.range (q - r + 1)).filter (fun p => 3 ≤ p ∧ (q - r) % p = 0 ∧ primeB p = true),
    ((p : ℚ) - 1) / ((p : ℚ) - 2)

theorem primeB_iff (n : ℕ) : primeB n = true ↔ n.Prime := by
  constructor
  · exact primeB_sound
  · intro h
    unfold primeB
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨h.two_le, Richstein2001.primeB_complete_aux n h⟩

/-- E as the paper defines it. -/
theorem E_eq (q : ℕ) : E q = ∑ r ∈ (Finset.range q).filter (fun r => 3 ≤ r ∧ r.Prime),
    ∏ p ∈ (Finset.range (q - r + 1)).filter (fun p => 3 ≤ p ∧ p ∣ q - r ∧ p.Prime),
      ((p : ℚ) - 1) / ((p : ℚ) - 2) := by
  unfold E
  refine Finset.sum_congr (Finset.filter_congr (fun r _ => by rw [primeB_iff])) (fun r _ => ?_)
  exact Finset.prod_congr (Finset.filter_congr (fun p _ => by rw [primeB_iff, Nat.dvd_iff_mod_eq_zero]))
    (fun _ _ => rfl)

/-- Table 4 rows (q, E(q) times 1000 as printed, stars). -/
def table4 : List (ℕ × ℕ × ℕ) := [
    (3, 0, 0),
    (5, 1000, 0),
    (7, 2000, 0),
    (11, 4000, 0),
    (13, 5333, 0),
    (17, 7533, 0),
    (19, 8200, 0),
    (23, 10667, 0),
    (29, 12535, 0),
    (31, 12824, 0),
    (37, 15358, 0),
    (41, 17437, 0),
    (43, 18683, 0),
    (47, 21111, 0),
    (53, 23292, 0),
    (59, 25050, 0),
    (61, 24340, 1),
    (67, 26695, 0),
    (71, 30084, 0),
    (73, 30825, 0),
    (79, 31494, 0),
    (83, 35046, 0),
    (89, 37066, 0),
    (97, 37321, 0),
    (101, 40689, 0),
    (103, 41202, 0),
    (107, 43468, 0),
    (109, 43104, 1),
    (113, 47569, 0),
    (127, 47715, 0),
    (131, 51124, 0),
    (137, 53070, 0),
    (139, 51532, 1),
    (149, 56154, 0),
    (151, 54716, 1),
    (157, 58547, 0),
    (163, 60156, 0),
    (167, 62532, 0),
    (173, 65574, 0),
    (179, 66425, 0),
    (181, 64879, 1),
    (191, 70000, 0),
    (193, 70375, 0),
    (197, 73578, 0),
    (199, 71979, 1),
    (211, 74249, 0),
    (223, 78235, 0),
    (227, 80539, 0),
    (229, 80291, 1),
    (233, 83535, 0),
    (239, 85013, 0),
    (241, 85705, 0),
    (251, 88854, 0),
    (257, 91997, 0),
    (263, 93586, 0),
    (269, 95451, 0),
    (271, 92937, 2),
    (277, 95223, 0),
    (281, 100355, 0),
    (283, 99417, 1),
    (293, 104247, 0),
    (307, 102477, 1),
    (311, 108060, 0),
    (313, 106448, 1),
    (317, 110897, 0),
    (331, 107856, 1),
    (337, 111243, 0),
    (347, 116850, 0),
    (349, 113385, 1),
    (353, 119700, 0),
    (359, 120019, 0),
    (367, 120386, 0),
    (373, 122004, 0),
    (379, 121753, 1),
    (383, 128371, 0),
    (389, 127790, 1),
    (397, 129358, 0),
    (401, 132535, 0),
    (409, 132082, 1),
    (419, 135539, 0),
    (421, 133988, 1),
    (431, 139807, 0),
    (433, 139480, 1),
    (439, 140896, 0),
    (443, 145233, 0),
    (449, 146239, 0),
    (457, 145811, 1),
    (461, 150366, 0),
    (463, 149524, 1),
    (467, 154053, 0),
    (479, 156574, 0),
    (487, 154574, 1),
    (491, 158973, 0),
    (499, 156746, 1),
    (503, 163340, 0),
    (509, 165522, 0),
    (521, 168123, 0),
    (523, 164724, 1),
    (541, 164872, 0),
    (547, 167976, 0)]

theorem table4_PR : (table4.map Prod.fst) = (P10k.filter (fun p => 3 ≤ p ∧ p ≤ 547)) := by
  decide +kernel

/-- FINDING: E(73) = 49326/1595, about 30.9254; the printed 30.825 is off by 0.1. -/
theorem E73 : E 73 = 49326 / 1595 := by decide +kernel

theorem E73_not_printed : ¬ ((61649 : ℚ) / 2000 ≤ E 73 ∧ E 73 < 61651 / 2000) := by
  rw [E73]; norm_num

end LeanLab.GvLtR1989.Paper
