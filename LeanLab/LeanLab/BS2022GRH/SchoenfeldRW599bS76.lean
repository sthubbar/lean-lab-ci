/-
Rosser-Schoenfeld 1962 Theorem 19, display (4.6), cited as [10, Theorem 19] in Schoenfeld 1976
after (6.16): the finite part 0 < x ≤ 1420.9 of x - 2√x < θ(x). Only this finite part is
proved here; the range 1423 ≤ x ≤ 10⁸ stays with the existing leaf rs62_thm19.
Method: 103 closed blocks [a, b], on each x - 2√x ≤ b - 2√b < log of the product of the
listed primes ≤ a ≤ θ(x), the log bounded below through 2^i e^j ≤ product, decided by the kernel.

AI wrote this Lean code, Claude, ROUTE BURST S76 burst-20261122, unit rosser_walker_599.
Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.BS2022GRH.SchoenfeldRW599bS76
open Real

/-- Chunk 0 of the listed primes. -/
def L0 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53]

lemma L0_prime : ∀ p ∈ L0, p.Prime := by
  simp only [L0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

/-- Chunk 1 of the listed primes. -/
def L1 : List ℕ := [59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131]

lemma L1_prime : ∀ p ∈ L1, p.Prime := by
  simp only [L1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

/-- Chunk 2 of the listed primes. -/
def L2 : List ℕ := [137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223]

lemma L2_prime : ∀ p ∈ L2, p.Prime := by
  simp only [L2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

/-- Chunk 3 of the listed primes. -/
def L3 : List ℕ := [227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311]

lemma L3_prime : ∀ p ∈ L3, p.Prime := by
  simp only [L3, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

/-- Chunk 4 of the listed primes. -/
def L4 : List ℕ := [313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409]

lemma L4_prime : ∀ p ∈ L4, p.Prime := by
  simp only [L4, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

/-- Chunk 5 of the listed primes. -/
def L5 : List ℕ := [419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503]

lemma L5_prime : ∀ p ∈ L5, p.Prime := by
  simp only [L5, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

/-- Chunk 6 of the listed primes. -/
def L6 : List ℕ := [509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613]

lemma L6_prime : ∀ p ∈ L6, p.Prime := by
  simp only [L6, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

/-- Chunk 7 of the listed primes. -/
def L7 : List ℕ := [617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719]

lemma L7_prime : ∀ p ∈ L7, p.Prime := by
  simp only [L7, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

/-- Chunk 8 of the listed primes. -/
def L8 : List ℕ := [727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827]

lemma L8_prime : ∀ p ∈ L8, p.Prime := by
  simp only [L8, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

/-- Chunk 9 of the listed primes. -/
def L9 : List ℕ := [829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941]

lemma L9_prime : ∀ p ∈ L9, p.Prime := by
  simp only [L9, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

/-- Chunk 10 of the listed primes. -/
def L10 : List ℕ := [947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049]

lemma L10_prime : ∀ p ∈ L10, p.Prime := by
  simp only [L10, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

/-- Chunk 11 of the listed primes. -/
def L11 : List ℕ := [1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163]

lemma L11_prime : ∀ p ∈ L11, p.Prime := by
  simp only [L11, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

/-- Chunk 12 of the listed primes. -/
def L12 : List ℕ := [1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283]

lemma L12_prime : ∀ p ∈ L12, p.Prime := by
  simp only [L12, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

/-- Chunk 13 of the listed primes. -/
def L13 : List ℕ := [1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423]

lemma L13_prime : ∀ p ∈ L13, p.Prime := by
  simp only [L13, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

/-- Chunk 14 of the listed primes. -/
def L14 : List ℕ := [1427, 1429]

lemma L14_prime : ∀ p ∈ L14, p.Prime := by
  simp only [L14, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

/-- The listed primes. -/
def L : List ℕ := L0 ++ L1 ++ L2 ++ L3 ++ L4 ++ L5 ++ L6 ++ L7 ++ L8 ++ L9 ++ L10 ++ L11 ++ L12 ++ L13 ++ L14

lemma L_prime : ∀ p ∈ L, p.Prime := by
  simp only [L, List.forall_mem_append, and_assoc]
  exact ⟨L0_prime, L1_prime, L2_prime, L3_prime, L4_prime, L5_prime, L6_prime, L7_prime, L8_prime, L9_prime, L10_prime, L11_prime, L12_prime, L13_prime, L14_prime⟩

/-- Product of the listed primes up to `n`. -/
def P (n : ℕ) : ℕ := ∏ p ∈ (L.filter (· ≤ n)).toFinset, p

lemma P_pos (n : ℕ) : 0 < P n := by
  unfold P
  apply Finset.prod_pos
  intro p hp
  simp only [List.mem_toFinset, List.mem_filter] at hp
  exact (L_prime p hp.1).pos

lemma log_P_le_theta (n : ℕ) : Real.log (P n) ≤ Chebyshev.theta n := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  unfold P
  push_cast
  rw [Real.log_prod]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hp
      exact Nat.mem_primesLE.2 ⟨hp.2, L_prime p hp.1⟩
    · intro p _ _; exact Real.log_natCast_nonneg p
  · intro p hp
    simp only [List.mem_toFinset, List.mem_filter] at hp
    exact_mod_cast (L_prime p hp.1).ne_zero

lemma log_lb {M : ℝ} (_hM : 0 < M) (m i j : ℕ) (hm : 0 < m)
    (h : (2:ℝ) ^ i * 2.7182818286 ^ j ≤ M ^ m) :
    ((i:ℝ) * 0.6931471803 + j) / m ≤ log M := by
  rw [div_le_iff₀ (by exact_mod_cast hm)]
  have h1 : (i:ℝ) * 0.6931471803 ≤ i * log 2 :=
    mul_le_mul_of_nonneg_left log_two_gt_d9.le (by positivity)
  have h2 : exp ((i:ℝ) * log 2 + j) ≤ M ^ m := by
    calc exp ((i:ℝ) * log 2 + j) = 2 ^ i * exp 1 ^ j := by
          rw [exp_add, exp_nat_mul, exp_log (by norm_num), exp_one_pow]
      _ ≤ 2 ^ i * 2.7182818286 ^ j := by gcongr; exact exp_one_lt_d9.le
      _ ≤ M ^ m := h
  have h3 : (i:ℝ) * log 2 + j ≤ m * log M := by
    have := log_le_log (exp_pos _) h2
    rw [log_exp, log_pow] at this
    exact this
  nlinarith

lemma cast_ineq (i j N : ℕ) (h : 2 ^ i * 27182818286 ^ j ≤ N * 10000000000 ^ j) :
    (2:ℝ) ^ i * 2.7182818286 ^ j ≤ N := by
  have : (2.7182818286:ℝ) = 27182818286 / 10000000000 := by norm_num
  rw [this, div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
  exact_mod_cast h

lemma block19 (a ti tj : ℕ) (b s x : ℝ) (hax : (a:ℝ) ≤ x) (hxb : x ≤ b) (ha : 1 ≤ a)
    (hT : 2 ^ ti * 27182818286 ^ tj ≤ P a * 10000000000 ^ tj)
    (hs : 0 < s) (hs2 : s ^ 2 ≤ b)
    (key : b - 2 * s < ti * 0.6931471803 + tj) :
    x - 2 * √x < Chebyshev.theta x := by
  have ha' : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hPpos : (0:ℝ) < P a := by exact_mod_cast P_pos a
  have hT' := log_lb hPpos 1 ti tj one_pos (by rw [pow_one]; exact cast_ineq ti tj (P a) hT)
  rw [Nat.cast_one, div_one] at hT'
  have hT'' := hT'.trans (log_P_le_theta a)
  have hmono : Chebyshev.theta a ≤ Chebyshev.theta x := Chebyshev.theta_mono hax
  have hx1 : 1 ≤ x := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hsb : s ≤ √b := by
    have h1 := Real.sqrt_le_sqrt hs2
    rwa [Real.sqrt_sq hs.le] at h1
  have hu1 : 1 ≤ √x := by rw [show (1:ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hx1
  have huv : √x ≤ √b := Real.sqrt_le_sqrt hxb
  have hxx := Real.sq_sqrt (show (0:ℝ) ≤ x by linarith)
  have hbb := Real.sq_sqrt (show (0:ℝ) ≤ b by linarith)
  have hinc : x - 2 * √x ≤ b - 2 * √b := by
    nlinarith [mul_nonneg (sub_nonneg.2 huv) (show (0:ℝ) ≤ √x + √b - 2 by linarith)]
  linarith

lemma blk0 (x : ℝ) (hax : (2:ℝ) ≤ x) (hxb : x ≤ (5 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 2 1 0 (5 : ℝ) (559/250 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk1 (x : ℝ) (hax : (5:ℝ) ≤ x) (hxb : x ≤ (9 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 5 2 2 (9 : ℝ) (3 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk2 (x : ℝ) (hax : (9:ℝ) ≤ x) (hxb : x ≤ (12 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 9 6 1 (12 : ℝ) (34641/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk3 (x : ℝ) (hax : (12:ℝ) ≤ x) (hxb : x ≤ (15 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 12 1 7 (15 : ℝ) (38729/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk4 (x : ℝ) (hax : (15:ℝ) ≤ x) (hxb : x ≤ (18 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 15 9 4 (18 : ℝ) (21213/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk5 (x : ℝ) (hax : (18:ℝ) ≤ x) (hxb : x ≤ (22 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 18 16 2 (22 : ℝ) (5863/1250 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk6 (x : ℝ) (hax : (22:ℝ) ≤ x) (hxb : x ≤ (26 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 22 3 14 (26 : ℝ) (5099/1000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk7 (x : ℝ) (hax : (26:ℝ) ≤ x) (hxb : x ≤ (30 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 26 19 6 (30 : ℝ) (13693/2500 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk8 (x : ℝ) (hax : (30:ℝ) ≤ x) (hxb : x ≤ (34 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 30 21 8 (34 : ℝ) (58309/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk9 (x : ℝ) (hax : (34:ℝ) ≤ x) (hxb : x ≤ (38 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 34 26 8 (38 : ℝ) (15411/2500 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk10 (x : ℝ) (hax : (38:ℝ) ≤ x) (hxb : x ≤ (42 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 38 11 22 (42 : ℝ) (64807/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk11 (x : ℝ) (hax : (42:ℝ) ≤ x) (hxb : x ≤ (47 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 42 38 7 (47 : ℝ) (17139/2500 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk12 (x : ℝ) (hax : (47:ℝ) ≤ x) (hxb : x ≤ (55 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 47 36 16 (55 : ℝ) (74161/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk13 (x : ℝ) (hax : (55:ℝ) ≤ x) (hxb : x ≤ (60 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 55 59 4 (60 : ℝ) (77459/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk14 (x : ℝ) (hax : (60:ℝ) ≤ x) (hxb : x ≤ (65 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 60 0 49 (65 : ℝ) (40311/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk15 (x : ℝ) (hax : (65:ℝ) ≤ x) (hxb : x ≤ (69 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 65 42 24 (69 : ℝ) (41533/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk16 (x : ℝ) (hax : (69:ℝ) ≤ x) (hxb : x ≤ (74 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 69 12 49 (74 : ℝ) (86023/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk17 (x : ℝ) (hax : (74:ℝ) ≤ x) (hxb : x ≤ (84 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 74 33 43 (84 : ℝ) (91651/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk18 (x : ℝ) (hax : (84:ℝ) ≤ x) (hxb : x ≤ (94 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 84 50 40 (94 : ℝ) (96953/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk19 (x : ℝ) (hax : (94:ℝ) ≤ x) (hxb : x ≤ (99 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 94 81 23 (99 : ℝ) (49749/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk20 (x : ℝ) (hax : (99:ℝ) ≤ x) (hxb : x ≤ (104 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 99 40 56 (104 : ℝ) (5099/500 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk21 (x : ℝ) (hax : (104:ℝ) ≤ x) (hxb : x ≤ (114 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 104 62 50 (114 : ℝ) (10677/1000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk22 (x : ℝ) (hax : (114:ℝ) ≤ x) (hxb : x ≤ (129 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 114 78 53 (129 : ℝ) (56789/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk23 (x : ℝ) (hax : (129:ℝ) ≤ x) (hxb : x ≤ (135 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 129 72 62 (135 : ℝ) (116189/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk24 (x : ℝ) (hax : (135:ℝ) ≤ x) (hxb : x ≤ (140 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 135 17 105 (140 : ℝ) (118321/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk25 (x : ℝ) (hax : (140:ℝ) ≤ x) (hxb : x ≤ (151 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 140 125 40 (151 : ℝ) (61441/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk26 (x : ℝ) (hax : (151:ℝ) ≤ x) (hxb : x ≤ (162 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 151 50 102 (162 : ℝ) (127279/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk27 (x : ℝ) (hax : (162:ℝ) ≤ x) (hxb : x ≤ (167 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 162 27 123 (167 : ℝ) (32307/2500 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk28 (x : ℝ) (hax : (167:ℝ) ≤ x) (hxb : x ≤ (178 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 167 10 145 (178 : ℝ) (16677/1250 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk29 (x : ℝ) (hax : (178:ℝ) ≤ x) (hxb : x ≤ (184 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 178 192 24 (184 : ℝ) (67823/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk30 (x : ℝ) (hax : (184:ℝ) ≤ x) (hxb : x ≤ (195 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 184 194 33 (195 : ℝ) (69821/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk31 (x : ℝ) (hax : (195:ℝ) ≤ x) (hxb : x ≤ (206 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 195 75 126 (206 : ℝ) (143527/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk32 (x : ℝ) (hax : (206:ℝ) ≤ x) (hxb : x ≤ (218 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 206 210 43 (218 : ℝ) (9228/625 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk33 (x : ℝ) (hax : (218:ℝ) ≤ x) (hxb : x ≤ (223 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 218 173 74 (223 : ℝ) (149331/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk34 (x : ℝ) (hax : (223:ℝ) ≤ x) (hxb : x ≤ (229 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 223 12 191 (229 : ℝ) (151327/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk35 (x : ℝ) (hax : (229:ℝ) ≤ x) (hxb : x ≤ (241 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 229 32 188 (241 : ℝ) (155241/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk36 (x : ℝ) (hax : (241:ℝ) ≤ x) (hxb : x ≤ (258 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 241 60 185 (258 : ℝ) (160623/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk37 (x : ℝ) (hax : (258:ℝ) ≤ x) (hxb : x ≤ (270 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 258 151 133 (270 : ℝ) (41079/2500 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk38 (x : ℝ) (hax : (270:ℝ) ≤ x) (hxb : x ≤ (282 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 270 258 70 (282 : ℝ) (20991/1250 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk39 (x : ℝ) (hax : (282:ℝ) ≤ x) (hxb : x ≤ (300 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 282 190 134 (300 : ℝ) (34641/2000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk40 (x : ℝ) (hax : (300:ℝ) ≤ x) (hxb : x ≤ (312 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 300 303 67 (312 : ℝ) (35327/2000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk41 (x : ℝ) (hax : (312:ℝ) ≤ x) (hxb : x ≤ (324 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 312 308 75 (324 : ℝ) (18 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk42 (x : ℝ) (hax : (324:ℝ) ≤ x) (hxb : x ≤ (336 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 324 176 178 (336 : ℝ) (183303/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk43 (x : ℝ) (hax : (336:ℝ) ≤ x) (hxb : x ≤ (342 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 336 307 93 (342 : ℝ) (46233/2500 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk44 (x : ℝ) (hax : (342:ℝ) ≤ x) (hxb : x ≤ (348 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 342 187 182 (348 : ℝ) (186547/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk45 (x : ℝ) (hax : (348:ℝ) ≤ x) (hxb : x ≤ (355 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 348 282 122 (355 : ℝ) (94207/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk46 (x : ℝ) (hax : (355:ℝ) ≤ x) (hxb : x ≤ (367 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 355 133 237 (367 : ℝ) (47893/2500 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk47 (x : ℝ) (hax : (367:ℝ) ≤ x) (hxb : x ≤ (379 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 367 339 106 (379 : ℝ) (194679/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk48 (x : ℝ) (hax : (379:ℝ) ≤ x) (hxb : x ≤ (392 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 379 447 43 (392 : ℝ) (197989/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk49 (x : ℝ) (hax : (392:ℝ) ≤ x) (hxb : x ≤ (404 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 392 66 319 (404 : ℝ) (200997/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk50 (x : ℝ) (hax : (404:ℝ) ≤ x) (hxb : x ≤ (417 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 404 40 349 (417 : ℝ) (40841/2000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk51 (x : ℝ) (hax : (417:ℝ) ≤ x) (hxb : x ≤ (423 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 417 330 154 (423 : ℝ) (205669/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk52 (x : ℝ) (hax : (423:ℝ) ≤ x) (hxb : x ≤ (436 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 423 245 225 (436 : ℝ) (104403/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk53 (x : ℝ) (hax : (436:ℝ) ≤ x) (hxb : x ≤ (449 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 436 225 251 (449 : ℝ) (26487/1250 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk54 (x : ℝ) (hax : (449:ℝ) ≤ x) (hxb : x ≤ (468 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 449 198 288 (468 : ℝ) (216333/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk55 (x : ℝ) (hax : (468:ℝ) ≤ x) (hxb : x ≤ (494 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 468 294 246 (494 : ℝ) (222261/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk56 (x : ℝ) (hax : (494:ℝ) ≤ x) (hxb : x ≤ (513 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 494 315 250 (513 : ℝ) (45299/2000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk57 (x : ℝ) (hax : (513:ℝ) ≤ x) (hxb : x ≤ (533 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 513 466 164 (533 : ℝ) (230867/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk58 (x : ℝ) (hax : (533:ℝ) ≤ x) (hxb : x ≤ (546 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 533 347 259 (546 : ℝ) (116833/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk59 (x : ℝ) (hax : (546:ℝ) ≤ x) (hxb : x ≤ (552 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 546 421 214 (552 : ℝ) (117473/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk60 (x : ℝ) (hax : (552:ℝ) ≤ x) (hxb : x ≤ (559 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 552 143 413 (559 : ℝ) (236431/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk61 (x : ℝ) (hax : (559:ℝ) ≤ x) (hxb : x ≤ (566 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 559 344 280 (566 : ℝ) (237907/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk62 (x : ℝ) (hax : (566:ℝ) ≤ x) (hxb : x ≤ (572 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 566 558 138 (572 : ℝ) (47833/2000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk63 (x : ℝ) (hax : (572:ℝ) ≤ x) (hxb : x ≤ (585 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 572 282 342 (585 : ℝ) (241867/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk64 (x : ℝ) (hax : (585:ℝ) ≤ x) (hxb : x ≤ (592 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 585 157 435 (592 : ℝ) (24331/1000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk65 (x : ℝ) (hax : (592:ℝ) ≤ x) (hxb : x ≤ (599 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 592 788 4 (599 : ℝ) (30593/1250 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk66 (x : ℝ) (hax : (599:ℝ) ≤ x) (hxb : x ≤ (612 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 599 251 389 (612 : ℝ) (123693/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk67 (x : ℝ) (hax : (612:ℝ) ≤ x) (hxb : x ≤ (625 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 612 571 180 (625 : ℝ) (25 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk68 (x : ℝ) (hax : (625:ℝ) ≤ x) (hxb : x ≤ (645 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 625 254 419 (645 : ℝ) (15873/625 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk69 (x : ℝ) (hax : (645:ℝ) ≤ x) (hxb : x ≤ (666 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 645 885 1 (666 : ℝ) (258069/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk70 (x : ℝ) (hax : (666:ℝ) ≤ x) (hxb : x ≤ (693 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 666 354 395 (693 : ℝ) (16453/625 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk71 (x : ℝ) (hax : (693:ℝ) ≤ x) (hxb : x ≤ (720 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 693 924 26 (720 : ℝ) (33541/1250 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk72 (x : ℝ) (hax : (720:ℝ) ≤ x) (hxb : x ≤ (740 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 720 560 298 (740 : ℝ) (272029/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk73 (x : ℝ) (hax : (740:ℝ) ≤ x) (hxb : x ≤ (761 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 740 678 236 (761 : ℝ) (137931/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk74 (x : ℝ) (hax : (761:ℝ) ≤ x) (hxb : x ≤ (788 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 761 810 171 (788 : ℝ) (280713/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk75 (x : ℝ) (hax : (788:ℝ) ≤ x) (hxb : x ≤ (809 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 788 859 157 (809 : ℝ) (284429/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk76 (x : ℝ) (hax : (809:ℝ) ≤ x) (hxb : x ≤ (823 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 809 483 431 (823 : ℝ) (286879/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk77 (x : ℝ) (hax : (823:ℝ) ≤ x) (hxb : x ≤ (844 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 823 903 160 (844 : ℝ) (72629/2500 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk78 (x : ℝ) (hax : (844:ℝ) ≤ x) (hxb : x ≤ (864 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 844 922 167 (864 : ℝ) (146969/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk79 (x : ℝ) (hax : (864:ℝ) ≤ x) (hxb : x ≤ (892 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 864 1036 115 (892 : ℝ) (298663/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk80 (x : ℝ) (hax : (892:ℝ) ≤ x) (hxb : x ≤ (920 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 892 273 671 (920 : ℝ) (60663/2000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk81 (x : ℝ) (hax : (920:ℝ) ≤ x) (hxb : x ≤ (942 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 920 806 322 (942 : ℝ) (7673/250 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk82 (x : ℝ) (hax : (942:ℝ) ≤ x) (hxb : x ≤ (963 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 942 423 608 (963 : ℝ) (155161/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk83 (x : ℝ) (hax : (963:ℝ) ≤ x) (hxb : x ≤ (977 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 963 1180 97 (977 : ℝ) (312569/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk84 (x : ℝ) (hax : (977:ℝ) ≤ x) (hxb : x ≤ (998 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 977 839 354 (998 : ℝ) (315911/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk85 (x : ℝ) (hax : (998:ℝ) ≤ x) (hxb : x ≤ (1020 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 998 475 627 (1020 : ℝ) (159687/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk86 (x : ℝ) (hax : (1020:ℝ) ≤ x) (hxb : x ≤ (1041 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 1020 1385 17 (1041 : ℝ) (64529/2000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk87 (x : ℝ) (hax : (1041:ℝ) ≤ x) (hxb : x ≤ (1070 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 1041 633 566 (1070 : ℝ) (81777/2500 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk88 (x : ℝ) (hax : (1070:ℝ) ≤ x) (hxb : x ≤ (1106 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 1070 1155 239 (1106 : ℝ) (66513/2000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk89 (x : ℝ) (hax : (1106:ℝ) ≤ x) (hxb : x ≤ (1142 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 1106 1142 283 (1142 : ℝ) (168967/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk90 (x : ℝ) (hax : (1142:ℝ) ≤ x) (hxb : x ≤ (1171 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 1142 1057 370 (1171 : ℝ) (171099/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk91 (x : ℝ) (hax : (1171:ℝ) ≤ x) (hxb : x ≤ (1200 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 1171 1506 87 (1200 : ℝ) (34641/1000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk92 (x : ℝ) (hax : (1200:ℝ) ≤ x) (hxb : x ≤ (1222 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 1200 1238 294 (1222 : ℝ) (349571/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk93 (x : ℝ) (hax : (1222:ℝ) ≤ x) (hxb : x ≤ (1243 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 1222 1224 325 (1243 : ℝ) (176281/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk94 (x : ℝ) (hax : (1243:ℝ) ≤ x) (hxb : x ≤ (1273 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 1243 1405 228 (1273 : ℝ) (356791/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk95 (x : ℝ) (hax : (1273:ℝ) ≤ x) (hxb : x ≤ (1287 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 1273 1541 148 (1287 : ℝ) (358747/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk96 (x : ℝ) (hax : (1287:ℝ) ≤ x) (hxb : x ≤ (1309 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 1287 1634 105 (1309 : ℝ) (361801/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk97 (x : ℝ) (hax : (1309:ℝ) ≤ x) (hxb : x ≤ (1354 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 1309 1282 392 (1354 : ℝ) (367967/10000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk98 (x : ℝ) (hax : (1354:ℝ) ≤ x) (hxb : x ≤ (1376 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 1354 1492 268 (1376 : ℝ) (23184/625 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk99 (x : ℝ) (hax : (1376:ℝ) ≤ x) (hxb : x ≤ (1398 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 1376 1089 569 (1398 : ℝ) (186949/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk100 (x : ℝ) (hax : (1398:ℝ) ≤ x) (hxb : x ≤ (1406 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 1398 997 640 (1406 : ℝ) (187483/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk101 (x : ℝ) (hax : (1406:ℝ) ≤ x) (hxb : x ≤ (1413 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 1406 1837 65 (1413 : ℝ) (187949/5000 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

lemma blk102 (x : ℝ) (hax : (1413:ℝ) ≤ x) (hxb : x ≤ (14209/10 : ℝ)) : x - 2 * √x < Chebyshev.theta x :=
  block19 1413 1494 310 (14209/10 : ℝ) (94237/2500 : ℝ) x (by exact_mod_cast hax) hxb (by norm_num) (by decide +kernel)
    (by norm_num) (by norm_num) (by norm_num)

/-- PROVED: the finite part 0 < x ≤ 1420.9 of Rosser-Schoenfeld 1962 Theorem 19, display (4.6). -/
theorem rs62_thm19_small_S76 : ∀ x : ℝ, 0 < x → x ≤ 1420.9 → x - 2 * √x < Chebyshev.theta x := by
  intro x hx0 hxe
  rcases lt_or_ge x 2 with hlt | h2
  · have hs := Real.sq_sqrt hx0.le
    have hpos := Real.sqrt_pos.2 hx0
    have hlt2 : √x < 2 := by nlinarith
    have := Chebyshev.theta_nonneg x
    nlinarith
  rcases le_or_gt x (5 : ℝ) with hb0 | hb0
  · exact blk0 x (by exact_mod_cast h2) hb0
  rcases le_or_gt x (9 : ℝ) with hb1 | hb1
  · exact blk1 x (by exact_mod_cast hb0.le) hb1
  rcases le_or_gt x (12 : ℝ) with hb2 | hb2
  · exact blk2 x (by exact_mod_cast hb1.le) hb2
  rcases le_or_gt x (15 : ℝ) with hb3 | hb3
  · exact blk3 x (by exact_mod_cast hb2.le) hb3
  rcases le_or_gt x (18 : ℝ) with hb4 | hb4
  · exact blk4 x (by exact_mod_cast hb3.le) hb4
  rcases le_or_gt x (22 : ℝ) with hb5 | hb5
  · exact blk5 x (by exact_mod_cast hb4.le) hb5
  rcases le_or_gt x (26 : ℝ) with hb6 | hb6
  · exact blk6 x (by exact_mod_cast hb5.le) hb6
  rcases le_or_gt x (30 : ℝ) with hb7 | hb7
  · exact blk7 x (by exact_mod_cast hb6.le) hb7
  rcases le_or_gt x (34 : ℝ) with hb8 | hb8
  · exact blk8 x (by exact_mod_cast hb7.le) hb8
  rcases le_or_gt x (38 : ℝ) with hb9 | hb9
  · exact blk9 x (by exact_mod_cast hb8.le) hb9
  rcases le_or_gt x (42 : ℝ) with hb10 | hb10
  · exact blk10 x (by exact_mod_cast hb9.le) hb10
  rcases le_or_gt x (47 : ℝ) with hb11 | hb11
  · exact blk11 x (by exact_mod_cast hb10.le) hb11
  rcases le_or_gt x (55 : ℝ) with hb12 | hb12
  · exact blk12 x (by exact_mod_cast hb11.le) hb12
  rcases le_or_gt x (60 : ℝ) with hb13 | hb13
  · exact blk13 x (by exact_mod_cast hb12.le) hb13
  rcases le_or_gt x (65 : ℝ) with hb14 | hb14
  · exact blk14 x (by exact_mod_cast hb13.le) hb14
  rcases le_or_gt x (69 : ℝ) with hb15 | hb15
  · exact blk15 x (by exact_mod_cast hb14.le) hb15
  rcases le_or_gt x (74 : ℝ) with hb16 | hb16
  · exact blk16 x (by exact_mod_cast hb15.le) hb16
  rcases le_or_gt x (84 : ℝ) with hb17 | hb17
  · exact blk17 x (by exact_mod_cast hb16.le) hb17
  rcases le_or_gt x (94 : ℝ) with hb18 | hb18
  · exact blk18 x (by exact_mod_cast hb17.le) hb18
  rcases le_or_gt x (99 : ℝ) with hb19 | hb19
  · exact blk19 x (by exact_mod_cast hb18.le) hb19
  rcases le_or_gt x (104 : ℝ) with hb20 | hb20
  · exact blk20 x (by exact_mod_cast hb19.le) hb20
  rcases le_or_gt x (114 : ℝ) with hb21 | hb21
  · exact blk21 x (by exact_mod_cast hb20.le) hb21
  rcases le_or_gt x (129 : ℝ) with hb22 | hb22
  · exact blk22 x (by exact_mod_cast hb21.le) hb22
  rcases le_or_gt x (135 : ℝ) with hb23 | hb23
  · exact blk23 x (by exact_mod_cast hb22.le) hb23
  rcases le_or_gt x (140 : ℝ) with hb24 | hb24
  · exact blk24 x (by exact_mod_cast hb23.le) hb24
  rcases le_or_gt x (151 : ℝ) with hb25 | hb25
  · exact blk25 x (by exact_mod_cast hb24.le) hb25
  rcases le_or_gt x (162 : ℝ) with hb26 | hb26
  · exact blk26 x (by exact_mod_cast hb25.le) hb26
  rcases le_or_gt x (167 : ℝ) with hb27 | hb27
  · exact blk27 x (by exact_mod_cast hb26.le) hb27
  rcases le_or_gt x (178 : ℝ) with hb28 | hb28
  · exact blk28 x (by exact_mod_cast hb27.le) hb28
  rcases le_or_gt x (184 : ℝ) with hb29 | hb29
  · exact blk29 x (by exact_mod_cast hb28.le) hb29
  rcases le_or_gt x (195 : ℝ) with hb30 | hb30
  · exact blk30 x (by exact_mod_cast hb29.le) hb30
  rcases le_or_gt x (206 : ℝ) with hb31 | hb31
  · exact blk31 x (by exact_mod_cast hb30.le) hb31
  rcases le_or_gt x (218 : ℝ) with hb32 | hb32
  · exact blk32 x (by exact_mod_cast hb31.le) hb32
  rcases le_or_gt x (223 : ℝ) with hb33 | hb33
  · exact blk33 x (by exact_mod_cast hb32.le) hb33
  rcases le_or_gt x (229 : ℝ) with hb34 | hb34
  · exact blk34 x (by exact_mod_cast hb33.le) hb34
  rcases le_or_gt x (241 : ℝ) with hb35 | hb35
  · exact blk35 x (by exact_mod_cast hb34.le) hb35
  rcases le_or_gt x (258 : ℝ) with hb36 | hb36
  · exact blk36 x (by exact_mod_cast hb35.le) hb36
  rcases le_or_gt x (270 : ℝ) with hb37 | hb37
  · exact blk37 x (by exact_mod_cast hb36.le) hb37
  rcases le_or_gt x (282 : ℝ) with hb38 | hb38
  · exact blk38 x (by exact_mod_cast hb37.le) hb38
  rcases le_or_gt x (300 : ℝ) with hb39 | hb39
  · exact blk39 x (by exact_mod_cast hb38.le) hb39
  rcases le_or_gt x (312 : ℝ) with hb40 | hb40
  · exact blk40 x (by exact_mod_cast hb39.le) hb40
  rcases le_or_gt x (324 : ℝ) with hb41 | hb41
  · exact blk41 x (by exact_mod_cast hb40.le) hb41
  rcases le_or_gt x (336 : ℝ) with hb42 | hb42
  · exact blk42 x (by exact_mod_cast hb41.le) hb42
  rcases le_or_gt x (342 : ℝ) with hb43 | hb43
  · exact blk43 x (by exact_mod_cast hb42.le) hb43
  rcases le_or_gt x (348 : ℝ) with hb44 | hb44
  · exact blk44 x (by exact_mod_cast hb43.le) hb44
  rcases le_or_gt x (355 : ℝ) with hb45 | hb45
  · exact blk45 x (by exact_mod_cast hb44.le) hb45
  rcases le_or_gt x (367 : ℝ) with hb46 | hb46
  · exact blk46 x (by exact_mod_cast hb45.le) hb46
  rcases le_or_gt x (379 : ℝ) with hb47 | hb47
  · exact blk47 x (by exact_mod_cast hb46.le) hb47
  rcases le_or_gt x (392 : ℝ) with hb48 | hb48
  · exact blk48 x (by exact_mod_cast hb47.le) hb48
  rcases le_or_gt x (404 : ℝ) with hb49 | hb49
  · exact blk49 x (by exact_mod_cast hb48.le) hb49
  rcases le_or_gt x (417 : ℝ) with hb50 | hb50
  · exact blk50 x (by exact_mod_cast hb49.le) hb50
  rcases le_or_gt x (423 : ℝ) with hb51 | hb51
  · exact blk51 x (by exact_mod_cast hb50.le) hb51
  rcases le_or_gt x (436 : ℝ) with hb52 | hb52
  · exact blk52 x (by exact_mod_cast hb51.le) hb52
  rcases le_or_gt x (449 : ℝ) with hb53 | hb53
  · exact blk53 x (by exact_mod_cast hb52.le) hb53
  rcases le_or_gt x (468 : ℝ) with hb54 | hb54
  · exact blk54 x (by exact_mod_cast hb53.le) hb54
  rcases le_or_gt x (494 : ℝ) with hb55 | hb55
  · exact blk55 x (by exact_mod_cast hb54.le) hb55
  rcases le_or_gt x (513 : ℝ) with hb56 | hb56
  · exact blk56 x (by exact_mod_cast hb55.le) hb56
  rcases le_or_gt x (533 : ℝ) with hb57 | hb57
  · exact blk57 x (by exact_mod_cast hb56.le) hb57
  rcases le_or_gt x (546 : ℝ) with hb58 | hb58
  · exact blk58 x (by exact_mod_cast hb57.le) hb58
  rcases le_or_gt x (552 : ℝ) with hb59 | hb59
  · exact blk59 x (by exact_mod_cast hb58.le) hb59
  rcases le_or_gt x (559 : ℝ) with hb60 | hb60
  · exact blk60 x (by exact_mod_cast hb59.le) hb60
  rcases le_or_gt x (566 : ℝ) with hb61 | hb61
  · exact blk61 x (by exact_mod_cast hb60.le) hb61
  rcases le_or_gt x (572 : ℝ) with hb62 | hb62
  · exact blk62 x (by exact_mod_cast hb61.le) hb62
  rcases le_or_gt x (585 : ℝ) with hb63 | hb63
  · exact blk63 x (by exact_mod_cast hb62.le) hb63
  rcases le_or_gt x (592 : ℝ) with hb64 | hb64
  · exact blk64 x (by exact_mod_cast hb63.le) hb64
  rcases le_or_gt x (599 : ℝ) with hb65 | hb65
  · exact blk65 x (by exact_mod_cast hb64.le) hb65
  rcases le_or_gt x (612 : ℝ) with hb66 | hb66
  · exact blk66 x (by exact_mod_cast hb65.le) hb66
  rcases le_or_gt x (625 : ℝ) with hb67 | hb67
  · exact blk67 x (by exact_mod_cast hb66.le) hb67
  rcases le_or_gt x (645 : ℝ) with hb68 | hb68
  · exact blk68 x (by exact_mod_cast hb67.le) hb68
  rcases le_or_gt x (666 : ℝ) with hb69 | hb69
  · exact blk69 x (by exact_mod_cast hb68.le) hb69
  rcases le_or_gt x (693 : ℝ) with hb70 | hb70
  · exact blk70 x (by exact_mod_cast hb69.le) hb70
  rcases le_or_gt x (720 : ℝ) with hb71 | hb71
  · exact blk71 x (by exact_mod_cast hb70.le) hb71
  rcases le_or_gt x (740 : ℝ) with hb72 | hb72
  · exact blk72 x (by exact_mod_cast hb71.le) hb72
  rcases le_or_gt x (761 : ℝ) with hb73 | hb73
  · exact blk73 x (by exact_mod_cast hb72.le) hb73
  rcases le_or_gt x (788 : ℝ) with hb74 | hb74
  · exact blk74 x (by exact_mod_cast hb73.le) hb74
  rcases le_or_gt x (809 : ℝ) with hb75 | hb75
  · exact blk75 x (by exact_mod_cast hb74.le) hb75
  rcases le_or_gt x (823 : ℝ) with hb76 | hb76
  · exact blk76 x (by exact_mod_cast hb75.le) hb76
  rcases le_or_gt x (844 : ℝ) with hb77 | hb77
  · exact blk77 x (by exact_mod_cast hb76.le) hb77
  rcases le_or_gt x (864 : ℝ) with hb78 | hb78
  · exact blk78 x (by exact_mod_cast hb77.le) hb78
  rcases le_or_gt x (892 : ℝ) with hb79 | hb79
  · exact blk79 x (by exact_mod_cast hb78.le) hb79
  rcases le_or_gt x (920 : ℝ) with hb80 | hb80
  · exact blk80 x (by exact_mod_cast hb79.le) hb80
  rcases le_or_gt x (942 : ℝ) with hb81 | hb81
  · exact blk81 x (by exact_mod_cast hb80.le) hb81
  rcases le_or_gt x (963 : ℝ) with hb82 | hb82
  · exact blk82 x (by exact_mod_cast hb81.le) hb82
  rcases le_or_gt x (977 : ℝ) with hb83 | hb83
  · exact blk83 x (by exact_mod_cast hb82.le) hb83
  rcases le_or_gt x (998 : ℝ) with hb84 | hb84
  · exact blk84 x (by exact_mod_cast hb83.le) hb84
  rcases le_or_gt x (1020 : ℝ) with hb85 | hb85
  · exact blk85 x (by exact_mod_cast hb84.le) hb85
  rcases le_or_gt x (1041 : ℝ) with hb86 | hb86
  · exact blk86 x (by exact_mod_cast hb85.le) hb86
  rcases le_or_gt x (1070 : ℝ) with hb87 | hb87
  · exact blk87 x (by exact_mod_cast hb86.le) hb87
  rcases le_or_gt x (1106 : ℝ) with hb88 | hb88
  · exact blk88 x (by exact_mod_cast hb87.le) hb88
  rcases le_or_gt x (1142 : ℝ) with hb89 | hb89
  · exact blk89 x (by exact_mod_cast hb88.le) hb89
  rcases le_or_gt x (1171 : ℝ) with hb90 | hb90
  · exact blk90 x (by exact_mod_cast hb89.le) hb90
  rcases le_or_gt x (1200 : ℝ) with hb91 | hb91
  · exact blk91 x (by exact_mod_cast hb90.le) hb91
  rcases le_or_gt x (1222 : ℝ) with hb92 | hb92
  · exact blk92 x (by exact_mod_cast hb91.le) hb92
  rcases le_or_gt x (1243 : ℝ) with hb93 | hb93
  · exact blk93 x (by exact_mod_cast hb92.le) hb93
  rcases le_or_gt x (1273 : ℝ) with hb94 | hb94
  · exact blk94 x (by exact_mod_cast hb93.le) hb94
  rcases le_or_gt x (1287 : ℝ) with hb95 | hb95
  · exact blk95 x (by exact_mod_cast hb94.le) hb95
  rcases le_or_gt x (1309 : ℝ) with hb96 | hb96
  · exact blk96 x (by exact_mod_cast hb95.le) hb96
  rcases le_or_gt x (1354 : ℝ) with hb97 | hb97
  · exact blk97 x (by exact_mod_cast hb96.le) hb97
  rcases le_or_gt x (1376 : ℝ) with hb98 | hb98
  · exact blk98 x (by exact_mod_cast hb97.le) hb98
  rcases le_or_gt x (1398 : ℝ) with hb99 | hb99
  · exact blk99 x (by exact_mod_cast hb98.le) hb99
  rcases le_or_gt x (1406 : ℝ) with hb100 | hb100
  · exact blk100 x (by exact_mod_cast hb99.le) hb100
  rcases le_or_gt x (1413 : ℝ) with hb101 | hb101
  · exact blk101 x (by exact_mod_cast hb100.le) hb101
  exact blk102 x (by exact_mod_cast hb101.le) (by linarith)

end LeanLab.BS2022GRH.SchoenfeldRW599bS76

#print axioms LeanLab.BS2022GRH.SchoenfeldRW599bS76.rs62_thm19_small_S76
