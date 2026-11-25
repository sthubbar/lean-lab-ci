/-
Schoenfeld 1976 p. 339, after (6.16): for 599 ≤ x < 1200, θ(x) - x > -(√x log² x)/(8π).
The paper cites the Rosser-Walker tables; here it is checked directly. The interval is cut into
44 blocks [a, b). On each block θ(x) ≥ θ(a) ≥ log of the product of the listed primes ≤ a,
bounded below through 2^i e^j ≤ product with log 2 > 0.6931471803 and e < 2.7182818286, both
power comparisons decided by the kernel; log a and √a are bounded below the same way, π < 3.1416.

AI wrote this Lean code, Claude, ROUTE BURST S76 burst-20261122, unit rosser_walker_599.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.BS2022GRH.SchoenfeldThm10S70

namespace LeanLab.BS2022GRH.SchoenfeldRW599S76
open Real

/-- The primes below 1200. -/
def L : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193]

set_option maxRecDepth 20000 in
lemma L_prime : ∀ p ∈ L, p.Prime := by
  simp only [L, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

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

lemma log_lb {M : ℝ} (hM : 0 < M) (m i j : ℕ) (hm : 0 < m)
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

lemma block (a b ti tj li lj : ℕ) (s x : ℝ) (hax : (a:ℝ) ≤ x) (hxb : x < b) (ha : 599 ≤ a)
    (hT : 2 ^ ti * 27182818286 ^ tj ≤ P a * 10000000000 ^ tj)
    (hL : 2 ^ li * 27182818286 ^ lj ≤ a ^ 10 * 10000000000 ^ lj)
    (hs : 0 < s) (hs2 : s ^ 2 ≤ a)
    (key : (b:ℝ) - (ti * 0.6931471803 + tj) <
      s * ((li * 0.6931471803 + lj) / 10) ^ 2 / (8 * 3.1416)) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x := by
  have ha' : (599:ℝ) ≤ a := by exact_mod_cast ha
  have hPpos : (0:ℝ) < P a := by exact_mod_cast P_pos a
  have hT' := log_lb hPpos 1 ti tj one_pos (by rw [pow_one]; exact cast_ineq ti tj (P a) hT)
  rw [Nat.cast_one, div_one] at hT'
  have hT'' := hT'.trans (log_P_le_theta a)
  have hLg := log_lb (M := (a:ℝ)) (by linarith) 10 li lj (by norm_num)
    (by have := cast_ineq li lj (a ^ 10) hL; push_cast at this; exact this)
  push_cast at hLg
  have hmono : Chebyshev.theta a ≤ Chebyshev.theta x := Chebyshev.theta_mono hax
  have hlog : log a ≤ log x := log_le_log (by linarith) hax
  have hsq : s ≤ √x := by
    have h1 := Real.sqrt_le_sqrt hs2
    rw [Real.sqrt_sq hs.le] at h1
    exact h1.trans (Real.sqrt_le_sqrt hax)
  have hLg0 : (0:ℝ) ≤ ((li:ℝ) * 0.6931471803 + lj) / 10 := by positivity
  have hprod : s * (((li:ℝ) * 0.6931471803 + lj) / 10) ^ 2 ≤ √x * log x ^ 2 :=
    mul_le_mul hsq (pow_le_pow_left₀ hLg0 (hLg.trans hlog) 2) (by positivity) (sqrt_nonneg _)
  have hpi := pi_lt_d4
  have hdiv : s * (((li:ℝ) * 0.6931471803 + lj) / 10) ^ 2 / (8 * 3.1416) ≤
      √x * log x ^ 2 / (8 * π) :=
    div_le_div₀ (by positivity) hprod (by positivity) (by linarith)
  linarith



lemma blk0 (x : ℝ) (hax : (599:ℝ) ≤ x) (hxb : x < 602) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 599 602 251 389 23 48 (12237/500 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk1 (x : ℝ) (hax : (602:ℝ) ≤ x) (hxb : x < 609) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 602 609 543 193 0 64 (4907/200 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk2 (x : ℝ) (hax : (609:ℝ) ≤ x) (hxb : x < 616) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 609 616 571 180 42 35 (24677/1000 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk3 (x : ℝ) (hax : (616:ℝ) ≤ x) (hxb : x < 622) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 616 622 612 158 84 6 (24819/1000 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk4 (x : ℝ) (hax : (622:ℝ) ≤ x) (hxb : x < 636) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 622 636 254 419 25 47 (24939/1000 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk5 (x : ℝ) (hax : (636:ℝ) ≤ x) (hxb : x < 643) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 636 643 787 56 8 59 (25219/1000 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk6 (x : ℝ) (hax : (643:ℝ) ≤ x) (hxb : x < 656) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 643 656 885 1 50 30 (25357/1000 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk7 (x : ℝ) (hax : (656:ℝ) ≤ x) (hxb : x < 670) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 656 670 556 242 7 60 (6403/250 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk8 (x : ℝ) (hax : (670:ℝ) ≤ x) (hxb : x < 683) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 670 683 354 395 78 11 (6471/250 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk9 (x : ℝ) (hax : (683:ℝ) ≤ x) (hxb : x < 704) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 683 704 375 400 35 41 (13067/500 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk10 (x : ℝ) (hax : (704:ℝ) ≤ x) (hxb : x < 718) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 704 718 391 402 34 42 (6633/250 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk11 (x : ℝ) (hax : (718:ℝ) ≤ x) (hxb : x < 725) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 718 725 513 324 79 11 (5359/200 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk12 (x : ℝ) (hax : (725:ℝ) ≤ x) (hxb : x < 732) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 725 732 560 298 7 61 (1077/40 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk13 (x : ℝ) (hax : (732:ℝ) ≤ x) (hxb : x < 739) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 732 739 620 263 36 41 (5411/200 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk14 (x : ℝ) (hax : (739:ℝ) ≤ x) (hxb : x < 753) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 739 753 678 236 52 30 (3398/125 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk15 (x : ℝ) (hax : (753:ℝ) ≤ x) (hxb : x < 767) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 753 767 863 121 9 60 (686/25 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk16 (x : ℝ) (hax : (767:ℝ) ≤ x) (hxb : x < 781) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 767 781 810 171 41 38 (13847/500 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk17 (x : ℝ) (hax : (781:ℝ) ≤ x) (hxb : x < 795) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 781 795 796 194 73 16 (13973/500 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk18 (x : ℝ) (hax : (795:ℝ) ≤ x) (hxb : x < 802) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 795 802 859 157 4 64 (5639/200 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk19 (x : ℝ) (hax : (802:ℝ) ≤ x) (hxb : x < 809) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 802 809 570 364 20 53 (28319/1000 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk20 (x : ℝ) (hax : (809:ℝ) ≤ x) (hxb : x < 816) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 809 816 483 431 36 42 (14221/500 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk21 (x : ℝ) (hax : (816:ℝ) ≤ x) (hxb : x < 823) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 816 823 673 306 52 31 (5713/200 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk22 (x : ℝ) (hax : (823:ℝ) ≤ x) (hxb : x < 837) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 823 837 903 160 55 29 (28687/1000 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk23 (x : ℝ) (hax : (837:ℝ) ≤ x) (hxb : x < 851) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 837 851 1058 66 74 16 (2893/100 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk24 (x : ℝ) (hax : (851:ℝ) ≤ x) (hxb : x < 858) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 851 858 922 167 93 3 (29171/1000 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk25 (x : ℝ) (hax : (858:ℝ) ≤ x) (hxb : x < 872) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 858 872 513 464 8 62 (29291/1000 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk26 (x : ℝ) (hax : (872:ℝ) ≤ x) (hxb : x < 886) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 872 886 1036 115 14 58 (29529/1000 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk27 (x : ℝ) (hax : (886:ℝ) ≤ x) (hxb : x < 907) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 886 907 709 362 20 54 (5953/200 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk28 (x : ℝ) (hax : (907:ℝ) ≤ x) (hxb : x < 922) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 907 922 505 517 29 48 (7529/250 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk29 (x : ℝ) (hax : (922:ℝ) ≤ x) (hxb : x < 936) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 922 936 806 322 35 44 (7591/250 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk30 (x : ℝ) (hax : (936:ℝ) ≤ x) (hxb : x < 944) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 936 944 334 656 28 49 (15297/500 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk31 (x : ℝ) (hax : (944:ℝ) ≤ x) (hxb : x < 958) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 944 958 423 608 44 38 (7681/250 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk32 (x : ℝ) (hax : (958:ℝ) ≤ x) (hxb : x < 972) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 958 972 1180 97 37 43 (30951/1000 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk33 (x : ℝ) (hax : (972:ℝ) ≤ x) (hxb : x < 987) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 972 987 793 379 17 57 (3897/125 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk34 (x : ℝ) (hax : (987:ℝ) ≤ x) (hxb : x < 1001) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 987 1001 709 451 23 53 (3927/125 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk35 (x : ℝ) (hax : (1001:ℝ) ≤ x) (hxb : x < 1016) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 1001 1016 475 627 91 6 (15819/500 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk36 (x : ℝ) (hax : (1016:ℝ) ≤ x) (hxb : x < 1030) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 1016 1030 922 331 97 2 (15937/500 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk37 (x : ℝ) (hax : (1030:ℝ) ≤ x) (hxb : x < 1045) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 1030 1045 841 401 77 16 (32093/1000 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk38 (x : ℝ) (hax : (1045:ℝ) ≤ x) (hxb : x < 1066) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 1045 1066 633 566 57 30 (16163/500 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk39 (x : ℝ) (hax : (1066:ℝ) ≤ x) (hxb : x < 1095) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 1066 1095 728 528 27 51 (32649/1000 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk40 (x : ℝ) (hax : (1095:ℝ) ≤ x) (hxb : x < 1125) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 1095 1125 1318 147 62 27 (3309/100 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk41 (x : ℝ) (hax : (1125:ℝ) ≤ x) (hxb : x < 1161) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 1125 1161 1572 6 22 55 (33541/1000 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk42 (x : ℝ) (hax : (1161:ℝ) ≤ x) (hxb : x < 1184) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 1161 1184 1174 303 34 47 (34073/1000 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

lemma blk43 (x : ℝ) (hax : (1184:ℝ) ≤ x) (hxb : x < 1200) :
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x :=
  block 1184 1200 678 668 79 16 (34409/1000 : ℝ) x (by exact_mod_cast hax) (by exact_mod_cast hxb)
    (by norm_num) (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num)

/-- PROVED: Schoenfeld 1976 p. 339 after (6.16), the Rosser-Walker range 599 ≤ x < 1200. -/
theorem rosser_walker_599_S76 : ∀ x : ℝ, 599 ≤ x → x < 1200 →
    -(√x * log x ^ 2 / (8 * π)) < Chebyshev.theta x - x := by
  intro x h0 h1200
  rcases lt_or_ge x 602 with hb0 | hb0
  · exact blk0 x h0 hb0
  rcases lt_or_ge x 609 with hb1 | hb1
  · exact blk1 x hb0 hb1
  rcases lt_or_ge x 616 with hb2 | hb2
  · exact blk2 x hb1 hb2
  rcases lt_or_ge x 622 with hb3 | hb3
  · exact blk3 x hb2 hb3
  rcases lt_or_ge x 636 with hb4 | hb4
  · exact blk4 x hb3 hb4
  rcases lt_or_ge x 643 with hb5 | hb5
  · exact blk5 x hb4 hb5
  rcases lt_or_ge x 656 with hb6 | hb6
  · exact blk6 x hb5 hb6
  rcases lt_or_ge x 670 with hb7 | hb7
  · exact blk7 x hb6 hb7
  rcases lt_or_ge x 683 with hb8 | hb8
  · exact blk8 x hb7 hb8
  rcases lt_or_ge x 704 with hb9 | hb9
  · exact blk9 x hb8 hb9
  rcases lt_or_ge x 718 with hb10 | hb10
  · exact blk10 x hb9 hb10
  rcases lt_or_ge x 725 with hb11 | hb11
  · exact blk11 x hb10 hb11
  rcases lt_or_ge x 732 with hb12 | hb12
  · exact blk12 x hb11 hb12
  rcases lt_or_ge x 739 with hb13 | hb13
  · exact blk13 x hb12 hb13
  rcases lt_or_ge x 753 with hb14 | hb14
  · exact blk14 x hb13 hb14
  rcases lt_or_ge x 767 with hb15 | hb15
  · exact blk15 x hb14 hb15
  rcases lt_or_ge x 781 with hb16 | hb16
  · exact blk16 x hb15 hb16
  rcases lt_or_ge x 795 with hb17 | hb17
  · exact blk17 x hb16 hb17
  rcases lt_or_ge x 802 with hb18 | hb18
  · exact blk18 x hb17 hb18
  rcases lt_or_ge x 809 with hb19 | hb19
  · exact blk19 x hb18 hb19
  rcases lt_or_ge x 816 with hb20 | hb20
  · exact blk20 x hb19 hb20
  rcases lt_or_ge x 823 with hb21 | hb21
  · exact blk21 x hb20 hb21
  rcases lt_or_ge x 837 with hb22 | hb22
  · exact blk22 x hb21 hb22
  rcases lt_or_ge x 851 with hb23 | hb23
  · exact blk23 x hb22 hb23
  rcases lt_or_ge x 858 with hb24 | hb24
  · exact blk24 x hb23 hb24
  rcases lt_or_ge x 872 with hb25 | hb25
  · exact blk25 x hb24 hb25
  rcases lt_or_ge x 886 with hb26 | hb26
  · exact blk26 x hb25 hb26
  rcases lt_or_ge x 907 with hb27 | hb27
  · exact blk27 x hb26 hb27
  rcases lt_or_ge x 922 with hb28 | hb28
  · exact blk28 x hb27 hb28
  rcases lt_or_ge x 936 with hb29 | hb29
  · exact blk29 x hb28 hb29
  rcases lt_or_ge x 944 with hb30 | hb30
  · exact blk30 x hb29 hb30
  rcases lt_or_ge x 958 with hb31 | hb31
  · exact blk31 x hb30 hb31
  rcases lt_or_ge x 972 with hb32 | hb32
  · exact blk32 x hb31 hb32
  rcases lt_or_ge x 987 with hb33 | hb33
  · exact blk33 x hb32 hb33
  rcases lt_or_ge x 1001 with hb34 | hb34
  · exact blk34 x hb33 hb34
  rcases lt_or_ge x 1016 with hb35 | hb35
  · exact blk35 x hb34 hb35
  rcases lt_or_ge x 1030 with hb36 | hb36
  · exact blk36 x hb35 hb36
  rcases lt_or_ge x 1045 with hb37 | hb37
  · exact blk37 x hb36 hb37
  rcases lt_or_ge x 1066 with hb38 | hb38
  · exact blk38 x hb37 hb38
  rcases lt_or_ge x 1095 with hb39 | hb39
  · exact blk39 x hb38 hb39
  rcases lt_or_ge x 1125 with hb40 | hb40
  · exact blk40 x hb39 hb40
  rcases lt_or_ge x 1161 with hb41 | hb41
  · exact blk41 x hb40 hb41
  rcases lt_or_ge x 1184 with hb42 | hb42
  · exact blk42 x hb41 hb42
  exact blk43 x hb42 h1200

end LeanLab.BS2022GRH.SchoenfeldRW599S76

#print axioms LeanLab.BS2022GRH.SchoenfeldRW599S76.rosser_walker_599_S76
