/-
Rosser-Schoenfeld 1962 (3.3), `π(n) > n/(log n - 1/2)` for `n ≥ 67`, cited in the lab as
`RieselVaughan1983.RS33` and `ChenExplicit.Yamada.RS62`, with the same statement.
Unit U-1391, PC run 20261021T1003Z-20044, track T1, ladder rung 5b shared inputs.
AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel. KNOWN mathematics.

* `rs33_small`, PROVED, no cited input: the inequality for every `67 ≤ n < 3300000`. A finite
  check closing the named gap below `N0 = 3300000` of the analytic step: the prime bitmap
  `pm 3300001` of Verifications/Top50/BitSieve, one kernel evaluation of `chk` over 195
  checkpoints, each block counted by the certified SWAR popcount of U1391Popc. At a checkpoint
  `pos` with `c ≤ π(pos)`, `256^j ≤ pos · 255^j` gives `log n ≥ j/256` for `n ≥ pos`, and
  `256 · nx ≤ c (j - 128)` then gives the inequality on all of `[pos, nx)`.
* `rs33_large`, CONDITIONAL ON `RS1975Cor2Thm7`, Rosser-Schoenfeld 1975, the lab's cited
  `θ(t) ≥ t - t/(40 log t)` for `t ≥ 678407`: the inequality for `n ≥ 3300000`, by Abel
  summation split at `e^13.5`, the head dropped as nonnegative and the tail bounded below by the
  primitive `t/log² t + 1.975 t/log³ t`, RieselVaughan1983/Lemma6Theta.
* `rs33_of_rs1975`: (3.3) for every `n ≥ 67`, CONDITIONAL ON `RS1975Cor2Thm7` only.
Goldbach is open.
-/
import LeanLab.Common.U1391Popc
import LeanLab.Verifications.Top50.BitSieve
import LeanLab.RieselVaughan1983.Lemma6Theta

namespace LeanLab.Common.U1391

open Finset Real Chebyshev
open LeanLab.Verifications.Top50.Bits
open LeanLab.RieselVaughan1983.Lemma6Theta

/-- Rosser-Schoenfeld 1962 (3.3), p. 69, as the lab cites it in two folders. -/
def RS33Body : Prop :=
  ∀ n : ℕ, 67 ≤ n → (n : ℝ) / (Real.log n - 1 / 2) < (Nat.primeCounting n : ℝ)

/-- The inequality at one `n`. -/
def RSIneq (n : ℕ) : Prop := (n : ℝ) / (Real.log n - 1 / 2) < (Nat.primeCounting n : ℝ)

/-- The checkpoint checker. `x` is the bitmap shifted so that bit `0` is `pos + 1`, `c` a lower
bound for `π(pos)`; an entry `(nx, j, K)` asks `log pos ≥ j/256`, `c (j/256 - 1/2) ≥ nx` and
counts the primes in `(pos, nx]` with `popc K`. -/
def chk (x pos c : ℕ) : List (ℕ × ℕ × ℕ) → Bool
  | [] => true
  | (nx, j, K) :: rest =>
      Nat.blt pos nx && Nat.blt 128 j && Nat.ble (256 ^ j) (pos * 255 ^ j) &&
      Nat.ble (256 * nx) (c * (j - 128)) && Nat.ble (nx - pos) (2 ^ K) &&
      chk (x >>> (nx - pos)) nx (c + popc K (x % 2 ^ (nx - pos))) rest

/-- The end of the range a checkpoint list covers. -/
def endOf : ℕ → List (ℕ × ℕ × ℕ) → ℕ
  | pos, [] => pos
  | _, (nx, _, _) :: rest => endOf nx rest

/-- A block count of the bitmap is at most the number of primes in the block. -/
theorem block_le {L : ℕ} (hL : L ≤ 10 ^ 8) (s len K : ℕ) :
    popc K ((pm L >>> s) % 2 ^ len) ≤ Nat.count (fun k => (s + k).Prime) len := by
  rw [popc_eq, Nat.count_eq_card_filter_range]
  apply card_le_card
  intro i hi
  simp only [mem_filter, mem_range, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
    Bool.and_eq_true, decide_eq_true_eq] at hi ⊢
  exact ⟨hi.2.1, prime_of_pm hL hi.2.2⟩

lemma pi_add (a b : ℕ) :
    Nat.primeCounting (a + b) = Nat.primeCounting a + Nat.count (fun k => (a + 1 + k).Prime) b := by
  simp only [Nat.primeCounting, Nat.primeCounting']
  rw [show a + b + 1 = (a + 1) + b by ring, Nat.count_add]

/-- One checkpoint: `c ≤ π(n)`, `log pos ≥ j/256` and `256 nx ≤ c (j - 128)` give the inequality
for `pos ≤ n < nx`. -/
theorem ineq_of {pos nx j c n : ℕ} (hj : 128 < j) (he : 256 ^ j ≤ pos * 255 ^ j)
    (hc : 256 * nx ≤ c * (j - 128)) (hcn : c ≤ Nat.primeCounting n) (hpn : pos ≤ n)
    (hnx : n < nx) : RSIneq n := by
  have hpos : 1 ≤ pos := by
    rcases Nat.eq_zero_or_pos pos with h | h
    · subst h; simp at he
    · exact h
  have hposR : (1 : ℝ) ≤ pos := by exact_mod_cast hpos
  have hnR : (pos : ℝ) ≤ n := by exact_mod_cast hpn
  have heR : (256 : ℝ) ^ j ≤ pos * 255 ^ j := by exact_mod_cast he
  have hlog : (j : ℝ) * (Real.log 256 - Real.log 255) ≤ Real.log pos := by
    have := Real.log_le_log (by positivity) heR
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at this
    linarith
  have h256 : (1 : ℝ) / 256 ≤ Real.log 256 - Real.log 255 := by
    have := Real.one_sub_inv_le_log_of_pos (x := (256 : ℝ) / 255) (by norm_num)
    rw [Real.log_div (by norm_num) (by norm_num)] at this
    norm_num at this ⊢; linarith
  have hjR : (128 : ℝ) < j := by exact_mod_cast hj
  have hln : (j : ℝ) / 256 ≤ Real.log n := by
    have := Real.log_le_log (by linarith) hnR
    have : (j : ℝ) / 256 ≤ j * (Real.log 256 - Real.log 255) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left h256 (by linarith)
    linarith
  have hcR : (256 : ℝ) * nx ≤ c * ((j : ℝ) - 128) := by
    have := hc; rw [← Nat.cast_le (α := ℝ)] at this
    push_cast [Nat.cast_sub hj.le] at this; linarith
  have hcnR : (c : ℝ) ≤ Nat.primeCounting n := by exact_mod_cast hcn
  have hnxR : (n : ℝ) + 1 ≤ nx := by exact_mod_cast hnx
  have hpos' : 0 < Real.log n - 1 / 2 := by linarith
  unfold RSIneq
  rw [div_lt_iff₀ hpos']
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have : (c : ℝ) * ((j : ℝ) / 256 - 1 / 2) ≤ Nat.primeCounting n * (Real.log n - 1 / 2) :=
    mul_le_mul hcnR (by linarith) (by linarith) (by linarith)
  linarith

/-- **Soundness of the checker.** -/
theorem chk_sound {L : ℕ} (hL : L ≤ 10 ^ 8) : ∀ (l : List (ℕ × ℕ × ℕ)) (x pos c : ℕ),
    chk x pos c l = true → x = pm L >>> (pos + 1) → c ≤ Nat.primeCounting pos →
    ∀ n, pos ≤ n → n < endOf pos l → RSIneq n
  | [], _, pos, _, _, _, _, n, h1, h2 => by simp [endOf] at h2; omega
  | (nx, j, K) :: rest, x, pos, c, h, hx, hc, n, h1, h2 => by
    simp only [chk, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at h
    obtain ⟨⟨⟨⟨⟨hpn, hj⟩, he⟩, hcc⟩, hK⟩, hr⟩ := h
    by_cases hn : n < nx
    · exact ineq_of hj he hcc (hc.trans (Nat.monotone_primeCounting h1)) h1 hn
    · push Not at hn
      refine chk_sound hL rest _ nx _ hr ?_ ?_ n hn (by simpa [endOf] using h2)
      · rw [hx, ← Nat.shiftRight_add]; congr 1; omega
      · have hb := block_le hL (pos + 1) (nx - pos) K
        rw [← hx] at hb
        have := pi_add pos (nx - pos)
        rw [show pos + (nx - pos) = nx by omega] at this
        omega

/-- The 195 checkpoints from `67` to `3300000`, made by an untrusted Python script,
/home/claude/ctx/u1391/plan.py, and checked here by the kernel. -/
def cps : List (ℕ × ℕ × ℕ) := [(70, 1074, 2), (71, 1085, 1), (75, 1089, 2), (79, 1103, 2), (84, 1116, 3), (90, 1132, 3), (95, 1149, 3), (97, 1163, 1), (101, 1168, 2), (106, 1179, 3), (112, 1191, 3), (122, 1205, 4), (128, 1227, 3), (134, 1239, 3), (140, 1251, 3), (150, 1262, 4), (157, 1280, 3), (168, 1291, 4), (179, 1309, 4), (191, 1325, 4), (203, 1341, 4), (220, 1357, 5), (229, 1378, 4), (246, 1388, 5), (264, 1406, 5), (283, 1424, 5), (313, 1442, 5), (340, 1468, 5), (361, 1489, 5), (387, 1504, 5), (413, 1522, 5), (440, 1538, 5), (473, 1555, 6), (513, 1573, 6), (555, 1594, 6), (586, 1614, 5), (621, 1628, 6), (674, 1643, 6), (732, 1664, 6), (784, 1685, 6), (842, 1702, 6), (907, 1720, 7), (975, 1739, 7), (1044, 1758, 7), (1125, 1775, 7), (1224, 1795, 7), (1318, 1816, 7), (1426, 1835, 7), (1511, 1855, 7), (1633, 1870, 7), (1775, 1890, 8), (1908, 1911, 8), (2054, 1929, 8), (2203, 1948, 8), (2354, 1966, 8), (2528, 1983, 8), (2699, 2001, 8), (2901, 2018, 8), (3124, 2037, 8), (3349, 2055, 8), (3586, 2073, 8), (3849, 2091, 9), (4124, 2109, 9), (4417, 2126, 9), (4725, 2144, 9), (5058, 2161, 9), (5415, 2179, 9), (5767, 2196, 9), (6162, 2212, 9), (6582, 2229, 9), (7048, 2246, 9), (7555, 2263, 9), (8056, 2281, 9), (8578, 2298, 10), (9119, 2314, 10), (9715, 2329, 10), (10366, 2345, 10), (11091, 2362, 10), (11817, 2379, 10), (12539, 2395, 10), (13350, 2411, 10), (14234, 2427, 10), (15119, 2443, 10), (16064, 2458, 10), (17118, 2474, 11), (18204, 2490, 11), (19367, 2506, 11), (20489, 2522, 11), (21756, 2536, 11), (23094, 2551, 11), (24571, 2567, 11), (26121, 2582, 11), (27710, 2598, 11), (29334, 2613, 11), (31123, 2628, 11), (32930, 2643, 11), (34852, 2657, 11), (36977, 2672, 12), (39194, 2687, 12), (41485, 2702, 12), (43854, 2716, 12), (46398, 2730, 12), (49017, 2745, 12), (51766, 2759, 12), (54708, 2773, 12), (57802, 2787, 12), (61144, 2801, 12), (64624, 2815, 12), (68214, 2830, 12), (72011, 2843, 12), (75985, 2857, 12), (80157, 2871, 13), (84519, 2885, 13), (89148, 2898, 13), (93916, 2912, 13), (98998, 2925, 13), (104321, 2938, 13), (109893, 2952, 13), (115751, 2965, 13), (121726, 2978, 13), (128119, 2991, 13), (134756, 3004, 13), (141718, 3017, 13), (149180, 3030, 13), (156874, 3043, 13), (164974, 3056, 13), (173369, 3069, 14), (182121, 3082, 14), (191225, 3094, 14), (200873, 3107, 14), (210888, 3119, 14), (221568, 3132, 14), (232573, 3144, 14), (244236, 3157, 14), (256144, 3169, 14), (268771, 3181, 14), (281916, 3194, 14), (295716, 3206, 14), (309772, 3218, 14), (324558, 3230, 14), (340192, 3242, 14), (356559, 3254, 14), (373765, 3266, 15), (391362, 3278, 15), (409787, 3290, 15), (428764, 3301, 15), (448624, 3313, 15), (469509, 3325, 15), (491049, 3336, 15), (513778, 3348, 15), (537393, 3359, 15), (562293, 3371, 15), (587715, 3382, 15), (614735, 3394, 15), (642752, 3405, 15), (671329, 3416, 15), (701378, 3428, 15), (732584, 3439, 15), (765305, 3450, 15), (799177, 3461, 16), (834576, 3472, 16), (871526, 3483, 16), (909885, 3494, 16), (950005, 3505, 16), (991347, 3516, 16), (1033959, 3527, 16), (1078692, 3538, 16), (1124720, 3549, 16), (1172718, 3559, 16), (1222999, 3570, 16), (1275384, 3581, 16), (1329837, 3592, 16), (1386031, 3602, 16), (1444505, 3613, 16), (1504966, 3623, 16), (1568428, 3634, 16), (1633758, 3644, 16), (1701763, 3655, 17), (1772230, 3665, 17), (1844932, 3676, 17), (1920583, 3686, 17), (1999390, 3696, 17), (2081040, 3706, 17), (2166241, 3717, 17), (2254703, 3727, 17), (2345737, 3737, 17), (2439983, 3747, 17), (2537195, 3757, 17), (2638360, 3767, 17), (2743249, 3777, 17), (2852261, 3787, 17), (2965856, 3797, 17), (3082858, 3807, 17), (3204026, 3817, 17), (3300000, 3827, 17)]

set_option maxRecDepth 100000 in
/-- **The kernel check**, one evaluation. -/
theorem chk_ok : chk (pm 3300001 >>> (67 + 1)) 67 (popc 7 (pm 3300001 % 2 ^ 68)) cps = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem endOf_cps : endOf 67 cps = 3300000 := by decide +kernel

/-- **(3.3) for `67 ≤ n < 3300000`, PROVED, no cited input.** -/
theorem rs33_small (n : ℕ) (h1 : 67 ≤ n) (h2 : n < 3300000) : RSIneq n := by
  have hL : (3300001 : ℕ) ≤ 10 ^ 8 := by norm_num
  have hc : popc 7 (pm 3300001 % 2 ^ 68) ≤ Nat.primeCounting 67 := by
    have h1 := block_le hL 0 68 7
    simp only [zero_add, Nat.shiftRight_zero] at h1
    exact h1
  exact chk_sound hL cps _ 67 _ chk_ok rfl hc n h1 (by rw [endOf_cps]; exact h2)

/-! ### The analytic range `n ≥ 3300000`, CONDITIONAL ON `RS1975Cor2Thm7` -/

lemma exp_half_le : exp (0.5 : ℝ) ≤ 1.6488 := by
  have h := Real.exp_one_lt_d9
  have e : exp (0.5 : ℝ) ^ 2 = exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  nlinarith [exp_pos (0.5 : ℝ)]

lemma exp_13_5_le : exp (13.5 : ℝ) ≤ 729452 := by
  have h := Real.exp_one_lt_d9
  have e : exp (13.5 : ℝ) = exp 1 ^ 13 * exp 0.5 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h13 : exp 1 ^ 13 ≤ (2.7182818286 : ℝ) ^ 13 := pow_le_pow_left₀ (exp_pos 1).le h.le 13
  rw [e]
  calc exp 1 ^ 13 * exp 0.5 ≤ (2.7182818286 : ℝ) ^ 13 * 1.6488 :=
        mul_le_mul h13 exp_half_le (exp_pos _).le (by positivity)
    _ ≤ 729452 := by norm_num

lemma exp_15_le : exp (15 : ℝ) ≤ 3270000 := by
  have h := Real.exp_one_lt_d9
  have e : exp (15 : ℝ) = exp 1 ^ 15 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  calc exp 1 ^ 15 ≤ (2.7182818286 : ℝ) ^ 15 := pow_le_pow_left₀ (exp_pos 1).le h.le 15
    _ ≤ 3270000 := by norm_num

lemma Gprim_y_le : Gprim 1.975 (exp 13.5) ≤ 4600 := by
  unfold Gprim
  rw [Real.log_exp]
  have := exp_13_5_le
  have h0 := exp_pos (13.5 : ℝ)
  have e : exp (13.5 : ℝ) / 13.5 ^ 2 + 1.975 * exp 13.5 / 13.5 ^ 3 =
      exp 13.5 * (1 / 13.5 ^ 2 + 1.975 / 13.5 ^ 3) := by ring
  rw [e]
  nlinarith

/-- **(3.3) for `n ≥ 3300000`, CONDITIONAL ON `RS1975Cor2Thm7`.** -/
theorem rs33_large (hRS : RS1975Cor2Thm7) (n : ℕ) (hn : 3300000 ≤ n) : RSIneq n := by
  set x : ℝ := (n : ℝ) with hxdef
  have hx : (3300000 : ℝ) ≤ x := by rw [hxdef]; exact_mod_cast hn
  have hx0 : 0 < x := by linarith
  have hy := exp_13_5
  have hyx : exp 13.5 ≤ x := by linarith [exp_13_5_le]
  have hsplit := pi_split (x := x) (y := exp 13.5) (by linarith) hyx
  have hfl : ⌊x⌋₊ = n := by rw [hxdef]; exact Nat.floor_natCast n
  rw [hfl] at hsplit
  have hhead := head_nonneg (y := exp 13.5) (by linarith)
  have htail := tail_lower hRS hy hyx
  have hth := hRS x (by linarith)
  set L := Real.log x with hLdef
  have hL15 : 15 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hx0]; linarith [exp_15_le]
  have hL0 : 0 < L := by linarith
  have hGx : x / L ^ 2 ≤ Gprim 1.975 x := by
    unfold Gprim; rw [← hLdef]
    have : 0 ≤ 1.975 * x / L ^ 3 := by positivity
    linarith
  have hGy := Gprim_y_le
  -- `A = x / L²` is large
  set A := x / L ^ 2 with hAdef
  have hxA : x = A * L ^ 2 := by rw [hAdef]; field_simp
  have hA : 14528 ≤ A := by
    have h1 := sq_mul_exp_le (L0 := 15) (L := L) (by norm_num) hL15
    rw [hLdef, Real.exp_log hx0, ← hLdef] at h1
    have h2 := exp_nat_ge 15
    have h3 : (3269017 : ℝ) ≤ exp 15 := by norm_num at h2 ⊢; linarith
    rw [hAdef, le_div_iff₀ (by positivity)]
    nlinarith
  have hθL : (x - x / (40 * L)) / L ≤ θ x / L := div_le_div_of_nonneg_right hth hL0.le
  have hT : (x - x / (40 * L)) / L = A * L - A / 40 := by
    rw [hxA]; field_simp
  have hpi : A * L - A / 40 + A - 4600 ≤ (Nat.primeCounting n : ℝ) := by
    rw [hsplit]; linarith
  unfold RSIneq
  rw [← hxdef, ← hLdef, div_lt_iff₀ (by linarith)]
  have key : x < (A * L - A / 40 + A - 4600) * (L - 1 / 2) := by
    rw [hxA]
    nlinarith [mul_le_mul_of_nonneg_right (sub_nonneg.2 hA) (show (0 : ℝ) ≤ 0.475 * L - 0.4875 by linarith),
      mul_nonneg (sub_nonneg.2 hA) (sub_nonneg.2 hL15)]
  calc x < (A * L - A / 40 + A - 4600) * (L - 1 / 2) := key
    _ ≤ (Nat.primeCounting n : ℝ) * (L - 1 / 2) :=
        mul_le_mul_of_nonneg_right hpi (by linarith)

/-- **Rosser-Schoenfeld (3.3) for every `n ≥ 67`, CONDITIONAL ON `RS1975Cor2Thm7` only.** -/
theorem rs33_of_rs1975 (hRS : RS1975Cor2Thm7) : RS33Body := by
  intro n hn
  by_cases h : n < 3300000
  · exact rs33_small n hn h
  · exact rs33_large hRS n (by omega)

/-- Vacuity: the hypotheses of `rs33_small` hold at `n = 67`, and the conclusion is the
statement `67 / (log 67 - 1/2) < π(67) = 19`. -/
theorem rs33_at_67 : RSIneq 67 := rs33_small 67 le_rfl (by norm_num)

end LeanLab.Common.U1391
