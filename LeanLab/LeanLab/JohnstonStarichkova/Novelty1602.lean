/-
AI wrote the Lean code, Claude, unit U-1602, run 20261102T0813Z-2382, track T2.
Tag: IMPROVEMENT, an error record fix. Binary Goldbach is OPEN.

The target left open by TRIAGE-U1595-20261101.md section 4 and VERIFY-U1598-20261101.md: the four
K values printed in Johnston and Starichkova, arXiv 2208.01229 v3 of 2025-04-11.
`K_eq_368` and `K22_eq_32` in this folder check v2, which prints 369 and 33.
Plain math twins, with p_1 = 2 so that `Nat.nth Nat.Prime i` is p_{i+1}, and K the largest integer with
the product of the K primes from p_{L+1} on below the cap. Sources are v3 Theorem 1.3 pp. 13 to 14,
Theorem 1.4 and Proposition 5.6 p. 21, read by U-1598; a local copy of the paper is NOT FOUND IN EITHER.

* `js_v3_K395`: the primes 17 to 2749, 395 of them, multiply to below exp exp 7.9; adding 2753 passes it.
* `js_v3_K31_top`: the primes 79 to 239, 31 of them, below exp exp 5.077; adding 241 passes it.
* `js_v3_K31_mid`: the primes 43 to 193, 31 of them, below exp 149; adding 197 passes it.
* `js_v3_K25_bottom`: the primes 17 to 127, 25 of them, below exp 104; adding 131 passes it.

So every v3 value recomputes exactly. No hypothesis, PROVED unconditional. These statements are closed
numerics, so the vacuity check is the index convention: `nth_prime_six` and `nth_prime_401`.
-/
import Mathlib
import LeanLab.JohnstonStarichkova.Theorem14

namespace LeanLab.JohnstonStarichkova.Novelty1602

open Finset Nat

/-- The 396 primes from 17 to 2753, so `Q2.getD i 0` is `Nat.nth Nat.Prime (i + 6)`. -/
def Q2 : List ℕ := [17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753]

theorem Q2_stepB : stepB primeB Q2 = true := by decide +kernel

theorem Q2_length : Q2.length = 396 := by decide +kernel

theorem Q2_head : Q2 = 17 :: Q2.tail := by decide +kernel

theorem Q2_prime : ∀ i < 396, primeB (Q2.getD i 0) = true := by
  have h : (List.range 396).all (fun i => primeB (Q2.getD i 0)) = true := by decide +kernel
  intro i hi
  exact List.all_eq_true.mp h i (List.mem_range.mpr hi)

/-- `nth Nat.Prime (i + 6)` is the i-th entry of `Q2`. -/
theorem nth_prime_Q2 {i : ℕ} (hi : i < 396) : nth Nat.Prime (i + 6) = Q2.getD i 0 := by
  have hb : count (fun k => primeB k = true) 17 = 6 := by decide +kernel
  have hw := walk primeB Q2.tail 17 6 (by rw [← Q2_head]; exact Q2_stepB) hb i
    (by rw [← Q2_head, Q2_length]; exact hi)
  rw [← Q2_head] at hw
  have hc : count Nat.Prime (Q2.getD i 0) = i + 6 := by
    rw [count_congr' (fun n => primeB_iff.symm)]; rw [hw]; ring
  calc nth Nat.Prime (i + 6) = nth Nat.Prime (count Nat.Prime (Q2.getD i 0)) := by rw [hc]
    _ = Q2.getD i 0 := nth_count (primeB_iff.mp (Q2_prime i hi))

/-- Index convention, vacuity check: `Nat.nth Nat.Prime 6 = 17`, the prime p_7. -/
theorem nth_prime_six : nth Nat.Prime 6 = 17 := by
  have := nth_prime_Q2 (i := 0) (by norm_num)
  rw [show (0 : ℕ) + 6 = 6 from rfl] at this
  rw [this]; decide +kernel

/-- Index convention, vacuity check: `Nat.nth Nat.Prime 401 = 2753`, the last prime used. -/
theorem nth_prime_401 : nth Nat.Prime 401 = 2753 := by
  have := nth_prime_Q2 (i := 395) (by norm_num)
  rw [show (395 : ℕ) + 6 = 401 from rfl] at this
  rw [this]; decide +kernel

/-- An `Ico` product of `nth` as a cast of a list product. -/
theorem prodIco {a b s : ℕ} (ha : a = s + 6) (hab : a ≤ b) (hb : b ≤ 402) :
    (∏ i ∈ Ico a b, ((nth Nat.Prime i : ℕ) : ℝ)) =
      ((∏ i ∈ range (b - a), Q2.getD (i + s) 0 : ℕ) : ℝ) := by
  rw [Finset.prod_Ico_eq_prod_range, Nat.cast_prod]
  refine prod_congr rfl (fun i hi => ?_)
  have hi' : i < b - a := mem_range.mp hi
  rw [show a + i = (i + s) + 6 by omega, nth_prime_Q2 (by omega)]

/-- `P^m > exp n` gives `P > exp (n/m)`, for the rational caps of the top range. -/
theorem exp_div_lt {P m n : ℕ} (hm : 0 < m) (h : Real.exp n < (P : ℝ) ^ m) :
    Real.exp ((n : ℝ) / m) < P := by
  have he : Real.exp n = Real.exp ((n : ℝ) / m) ^ m := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  rw [he] at h
  exact (pow_lt_pow_iff_left₀ (Real.exp_pos _).le (Nat.cast_nonneg P) hm.ne').mp h

/-! ### The caps -/

theorem exp_09_le : Real.exp 0.9 ≤ 2.4597 := by
  have h := Real.exp_bound' (x := 0.9) (by norm_num) (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem exp_09_ge : 2.4595 ≤ Real.exp 0.9 := by
  have h := Real.sum_le_exp_of_nonneg (x := 0.9) (by norm_num) 12
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem exp79_eq : Real.exp 7.9 = Real.exp 1 ^ 7 * Real.exp 0.9 := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num

theorem exp79_lt : Real.exp 7.9 < 2698 := by
  rw [exp79_eq]
  have h3 : Real.exp 1 ^ 7 < 2.7182818286 ^ 7 := by
    gcongr; exact Real.exp_one_lt_d9
  calc Real.exp 1 ^ 7 * Real.exp 0.9 ≤ 2.7182818286 ^ 7 * 2.4597 :=
        mul_le_mul h3.le exp_09_le (Real.exp_pos _).le (by positivity)
    _ < 2698 := by norm_num

theorem exp79_gt : 2692 < Real.exp 7.9 := by
  rw [exp79_eq]
  have h3 : 2.7182818283 ^ 7 < Real.exp 1 ^ 7 := by
    gcongr; exact Real.exp_one_gt_d9
  calc (2692 : ℝ) < 2.7182818283 ^ 7 * 2.4595 := by norm_num
    _ ≤ Real.exp 1 ^ 7 * Real.exp 0.9 :=
        mul_le_mul h3.le exp_09_ge (by norm_num) (by positivity)

theorem exp_077_le : Real.exp 0.077 ≤ 1.08005 := by
  have h := Real.exp_bound' (x := 0.077) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem exp_077_ge : 1.08004 ≤ Real.exp 0.077 := by
  have h := Real.sum_le_exp_of_nonneg (x := 0.077) (by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem exp5077_eq : Real.exp 5.077 = Real.exp 1 ^ 5 * Real.exp 0.077 := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num

theorem exp5077_lt : Real.exp 5.077 < 160.6 := by
  rw [exp5077_eq]
  have h3 : Real.exp 1 ^ 5 < 2.7182818286 ^ 5 := by
    gcongr; exact Real.exp_one_lt_d9
  calc Real.exp 1 ^ 5 * Real.exp 0.077 ≤ 2.7182818286 ^ 5 * 1.08005 :=
        mul_le_mul h3.le exp_077_le (Real.exp_pos _).le (by positivity)
    _ < 160.6 := by norm_num

theorem exp5077_gt : 160 < Real.exp 5.077 := by
  rw [exp5077_eq]
  have h3 : 2.7182818283 ^ 5 < Real.exp 1 ^ 5 := by
    gcongr; exact Real.exp_one_gt_d9
  calc (160 : ℝ) < 2.7182818283 ^ 5 * 1.08004 := by norm_num
    _ ≤ Real.exp 1 ^ 5 * Real.exp 0.077 :=
        mul_le_mul h3.le exp_077_ge (by norm_num) (by positivity)

/-! ### Kernel comparisons with `e` -/

theorem big395 : (∏ i ∈ range 395, Q2.getD (i + 0) 0) * 10 ^ (10 * 2692) < 27182818283 ^ 2692 := by
  decide +kernel

theorem big396 : 27182818286 ^ 2698 < (∏ i ∈ range 396, Q2.getD (i + 0) 0) * 10 ^ (10 * 2698) := by
  decide +kernel

theorem bigTopLo : (∏ i ∈ range 31, Q2.getD (i + 15) 0) * 10 ^ (10 * 160) < 27182818283 ^ 160 := by
  decide +kernel

theorem bigTopHi : 27182818286 ^ 1606 < (∏ i ∈ range 32, Q2.getD (i + 15) 0) ^ 10 * 10 ^ (10 * 1606) := by
  decide +kernel

theorem bigMidLo : (∏ i ∈ range 31, Q2.getD (i + 7) 0) * 10 ^ (10 * 149) < 27182818283 ^ 149 := by
  decide +kernel

theorem bigMidHi : 27182818286 ^ 149 < (∏ i ∈ range 32, Q2.getD (i + 7) 0) * 10 ^ (10 * 149) := by
  decide +kernel

theorem bigBotLo : (∏ i ∈ range 25, Q2.getD (i + 0) 0) * 10 ^ (10 * 104) < 27182818283 ^ 104 := by
  decide +kernel

theorem bigBotHi : 27182818286 ^ 104 < (∏ i ∈ range 26, Q2.getD (i + 0) 0) * 10 ^ (10 * 104) := by
  decide +kernel

/-! ### The four v3 values -/

/-- arXiv 2208.01229 v3, Theorem 1.3 pp. 13 to 14: `X₂ = exp exp 7.9`, `K = 395`. -/
theorem js_v3_K395 :
    (∏ i ∈ Ico 6 401, ((nth Nat.Prime i : ℕ) : ℝ)) < Real.exp (Real.exp 7.9) ∧
    Real.exp (Real.exp 7.9) ≤ ∏ i ∈ Ico 6 402, ((nth Nat.Prime i : ℕ) : ℝ) := by
  rw [prodIco (a := 6) (s := 0) rfl (by norm_num) (by norm_num),
    prodIco (a := 6) (s := 0) rfl (by norm_num) (by norm_num)]
  constructor
  · have h1 := lt_exp_of_nat (by norm_num) big395
    exact h1.trans (Real.exp_lt_exp.mpr (by exact_mod_cast exp79_gt))
  · have h1 := exp_lt_of_nat (by norm_num) big396
    exact ((Real.exp_lt_exp.mpr (by exact_mod_cast exp79_lt)).trans h1).le

/-- v3, Theorem 1.4 and Proposition 5.6 p. 21: `X₂ = exp exp 5.077`, `L + 1 = 21`, `K = 31`. -/
theorem js_v3_K31_top :
    (∏ i ∈ Ico 21 52, ((nth Nat.Prime i : ℕ) : ℝ)) < Real.exp (Real.exp 5.077) ∧
    Real.exp (Real.exp 5.077) ≤ ∏ i ∈ Ico 21 53, ((nth Nat.Prime i : ℕ) : ℝ) := by
  rw [prodIco (a := 21) (s := 15) rfl (by norm_num) (by norm_num),
    prodIco (a := 21) (s := 15) rfl (by norm_num) (by norm_num)]
  constructor
  · have h1 := lt_exp_of_nat (by norm_num) bigTopLo
    exact h1.trans (Real.exp_lt_exp.mpr (by exact_mod_cast exp5077_gt))
  · set P := ∏ i ∈ range 32, Q2.getD (i + 15) 0 with hP
    have h1 := exp_lt_of_nat (P := P ^ 10) (by norm_num) bigTopHi
    push_cast at h1
    have h2 := exp_div_lt (P := P) (m := 10) (n := 1606) (by norm_num) (by exact_mod_cast h1)
    have h3 : ((1606 : ℕ) : ℝ) / ((10 : ℕ) : ℝ) = 160.6 := by norm_num
    rw [h3] at h2
    exact ((Real.exp_lt_exp.mpr exp5077_lt).trans h2).le

/-- v3, Theorem 1.4 p. 21: cap `exp 149`, `L + 1 = 13`, `K = 31`. -/
theorem js_v3_K31_mid :
    (∏ i ∈ Ico 13 44, ((nth Nat.Prime i : ℕ) : ℝ)) < Real.exp 149 ∧
    Real.exp 149 ≤ ∏ i ∈ Ico 13 45, ((nth Nat.Prime i : ℕ) : ℝ) := by
  rw [prodIco (a := 13) (s := 7) rfl (by norm_num) (by norm_num),
    prodIco (a := 13) (s := 7) rfl (by norm_num) (by norm_num)]
  constructor
  · exact_mod_cast lt_exp_of_nat (by norm_num) bigMidLo
  · exact (by exact_mod_cast exp_lt_of_nat (by norm_num) bigMidHi : Real.exp 149 < _).le

/-- v3, Theorem 1.4 p. 21: cap `exp 104`, `K = 25`. -/
theorem js_v3_K25_bottom :
    (∏ i ∈ Ico 6 31, ((nth Nat.Prime i : ℕ) : ℝ)) < Real.exp 104 ∧
    Real.exp 104 ≤ ∏ i ∈ Ico 6 32, ((nth Nat.Prime i : ℕ) : ℝ) := by
  rw [prodIco (a := 6) (s := 0) rfl (by norm_num) (by norm_num),
    prodIco (a := 6) (s := 0) rfl (by norm_num) (by norm_num)]
  constructor
  · exact_mod_cast lt_exp_of_nat (by norm_num) bigBotLo
  · exact (by exact_mod_cast exp_lt_of_nat (by norm_num) bigBotHi : Real.exp 104 < _).le

end LeanLab.JohnstonStarichkova.Novelty1602

#print axioms LeanLab.JohnstonStarichkova.Novelty1602.js_v3_K395
#print axioms LeanLab.JohnstonStarichkova.Novelty1602.js_v3_K31_top
#print axioms LeanLab.JohnstonStarichkova.Novelty1602.js_v3_K31_mid
#print axioms LeanLab.JohnstonStarichkova.Novelty1602.js_v3_K25_bottom
#print axioms LeanLab.JohnstonStarichkova.Novelty1602.nth_prime_six
#print axioms LeanLab.JohnstonStarichkova.Novelty1602.nth_prime_401
