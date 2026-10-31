/-
P0022, Kaniecki 1995, the input `DiagLam2` of Lemma5Near21.lean, PROVED here.
PC run 20261021T0604Z-1697, unit U-1372, T1.

`DiagLam2`: `Σ Λ(n)²/n² ≤ 0.886`, true value about 0.80521.
Proof. Head `n ≤ 300`: each term is bounded by a certified rational, using `Λ(p^j) = log p` and
`log p ≤ k log 2 / 128` whenever `p^128 ≤ 2^k`, with Mathlib's `log 2 < 0.6931471808`; the
composite terms vanish since two distinct primes divide them. The head total is at most
0.7847167. Tail `n > 300`: `Λ(n)² ≤ Λ(n) log n`, then summation by parts against
`g(x) = log x / x²` with `ψ(N) ≤ 1.9 N` for `N ≥ 300`, from the lab's `psi_le_11062` and
`log N ≤ (4/e) N^{1/4}`; the tail is at most `1.9 (300 g(300) + G(300))`, `G(x) = (log x + 1)/x`,
which is at most 0.07863. Total at most 0.86335.
AI wrote this Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Kaniecki1995.Lemma5Near21
import LeanLab.ChebyshevExplicit.Psi30Upper

set_option exponentiation.threshold 2000

namespace LeanLab.Kaniecki1995.L5Lam

open Real Chebyshev
open scoped ArithmeticFunction.vonMangoldt

/-- the summand of `DiagLam2` -/
noncomputable def f (n : ℕ) : ℝ := Λ n ^ 2 * (n : ℝ) ^ (-(2 : ℝ))

/-- the partial sums -/
noncomputable def S (k : ℕ) : ℝ := ∑ n ∈ Finset.range k, f n

theorem S_zero : S 0 = 0 := by simp [S]

theorem S_succ (k : ℕ) : S (k + 1) = S k + f k := Finset.sum_range_succ _ _

theorem f_nonneg (n : ℕ) : 0 ≤ f n := by unfold f; positivity

theorem log_le_pow (p k : ℕ) (h : p ^ 128 ≤ 2 ^ k) :
    Real.log (p : ℝ) ≤ (k : ℝ) * 0.6931471808 / 128 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp; positivity
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h' : ((p : ℝ)) ^ 128 ≤ (2 : ℝ) ^ k := by exact_mod_cast h
  have := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at this
  have h2 := Real.log_two_lt_d9
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  push_cast at this
  nlinarith

theorem lam_zero_of (n p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hpn : p ∣ n)
    (hqn : q ∣ n) : Λ n = 0 := by
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff, isPrimePow_iff_unique_prime_dvd]
  rintro ⟨r, _, hu⟩
  exact hpq ((hu p ⟨hp, hpn⟩).trans (hu q ⟨hq, hqn⟩).symm)

theorem term_le {n : ℕ} {L a : ℝ} (hn : 0 < n) (hΛ : Λ n ≤ L) (h : L ^ 2 ≤ a * (n : ℝ) ^ 2) :
    f n ≤ a := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  unfold f
  rw [Real.rpow_neg hn'.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [mul_inv_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul hΛ hΛ h0 (h0.trans hΛ)]

theorem t0 : f 0 ≤ 0 / 10000000 := by simp [f]

theorem t1 : f 1 ≤ 0 / 10000000 := by simp [f]

theorem t2 : f 2 ≤ 1201133 / 10000000 :=
  term_le (n := 2) (L := 128 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 2 128 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t3 : f 3 ≤ 1342705 / 10000000 :=
  term_le (n := 3) (L := 203 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 3 203 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t4 : f 4 ≤ 300284 / 10000000 :=
  term_le (n := 4) (L := 128 * 0.6931471808 / 128) (by norm_num) (by
    rw [show (4:ℕ) = 2 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 2 128 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t5 : f 5 ≤ 1041655 / 10000000 :=
  term_le (n := 5) (L := 298 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 5 298 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t6 : f 6 ≤ 0 / 10000000 := by
  show Λ 6 ^ 2 * _ ≤ _
  rw [lam_zero_of 6 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t7 : f 7 ≤ 775604 / 10000000 :=
  term_le (n := 7) (L := 360 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 7 360 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t8 : f 8 ≤ 75071 / 10000000 :=
  term_le (n := 8) (L := 128 * 0.6931471808 / 128) (by norm_num) (by
    rw [show (8:ℕ) = 2 ^ 3 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 2 128 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t9 : f 9 ≤ 149190 / 10000000 :=
  term_le (n := 9) (L := 203 * 0.6931471808 / 128) (by norm_num) (by
    rw [show (9:ℕ) = 3 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 3 203 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t10 : f 10 ≤ 0 / 10000000 := by
  show Λ 10 ^ 2 * _ ≤ _
  rw [lam_zero_of 10 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t11 : f 11 ≤ 475613 / 10000000 :=
  term_le (n := 11) (L := 443 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 11 443 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t12 : f 12 ≤ 0 / 10000000 := by
  show Λ 12 ^ 2 * _ ≤ _
  rw [lam_zero_of 12 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t13 : f 13 ≤ 389854 / 10000000 :=
  term_le (n := 13) (L := 474 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 13 474 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t14 : f 14 ≤ 0 / 10000000 := by
  show Λ 14 ^ 2 * _ ≤ _
  rw [lam_zero_of 14 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t15 : f 15 ≤ 0 / 10000000 := by
  show Λ 15 ^ 2 * _ ≤ _
  rw [lam_zero_of 15 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t16 : f 16 ≤ 18768 / 10000000 :=
  term_le (n := 16) (L := 128 * 0.6931471808 / 128) (by norm_num) (by
    rw [show (16:ℕ) = 2 ^ 4 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 2 128 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t17 : f 17 ≤ 278610 / 10000000 :=
  term_le (n := 17) (L := 524 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 17 524 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t18 : f 18 ≤ 0 / 10000000 := by
  show Λ 18 ^ 2 * _ ≤ _
  rw [lam_zero_of 18 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t19 : f 19 ≤ 240393 / 10000000 :=
  term_le (n := 19) (L := 544 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 19 544 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t20 : f 20 ≤ 0 / 10000000 := by
  show Λ 20 ^ 2 * _ ≤ _
  rw [lam_zero_of 20 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t21 : f 21 ≤ 0 / 10000000 := by
  show Λ 21 ^ 2 * _ ≤ _
  rw [lam_zero_of 21 3 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t22 : f 22 ≤ 0 / 10000000 := by
  show Λ 22 ^ 2 * _ ≤ _
  rw [lam_zero_of 22 2 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t23 : f 23 ≤ 186480 / 10000000 :=
  term_le (n := 23) (L := 580 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 23 580 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t24 : f 24 ≤ 0 / 10000000 := by
  show Λ 24 ^ 2 * _ ≤ _
  rw [lam_zero_of 24 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t25 : f 25 ≤ 41667 / 10000000 :=
  term_le (n := 25) (L := 298 * 0.6931471808 / 128) (by norm_num) (by
    rw [show (25:ℕ) = 5 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 5 298 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t26 : f 26 ≤ 0 / 10000000 := by
  show Λ 26 ^ 2 * _ ≤ _
  rw [lam_zero_of 26 2 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t27 : f 27 ≤ 16577 / 10000000 :=
  term_le (n := 27) (L := 203 * 0.6931471808 / 128) (by norm_num) (by
    rw [show (27:ℕ) = 3 ^ 3 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 3 203 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t28 : f 28 ≤ 0 / 10000000 := by
  show Λ 28 ^ 2 * _ ≤ _
  rw [lam_zero_of 28 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t29 : f 29 ≤ 134902 / 10000000 :=
  term_le (n := 29) (L := 622 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 29 622 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t30 : f 30 ≤ 0 / 10000000 := by
  show Λ 30 ^ 2 * _ ≤ _
  rw [lam_zero_of 30 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t31 : f 31 ≤ 123043 / 10000000 :=
  term_le (n := 31) (L := 635 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 31 635 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t32 : f 32 ≤ 4692 / 10000000 :=
  term_le (n := 32) (L := 128 * 0.6931471808 / 128) (by norm_num) (by
    rw [show (32:ℕ) = 2 ^ 5 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 2 128 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t33 : f 33 ≤ 0 / 10000000 := by
  show Λ 33 ^ 2 * _ ≤ _
  rw [lam_zero_of 33 3 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t34 : f 34 ≤ 0 / 10000000 := by
  show Λ 34 ^ 2 * _ ≤ _
  rw [lam_zero_of 34 2 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t35 : f 35 ≤ 0 / 10000000 := by
  show Λ 35 ^ 2 * _ ≤ _
  rw [lam_zero_of 35 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t36 : f 36 ≤ 0 / 10000000 := by
  show Λ 36 ^ 2 * _ ≤ _
  rw [lam_zero_of 36 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t37 : f 37 ≤ 95297 / 10000000 :=
  term_le (n := 37) (L := 667 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 37 667 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t38 : f 38 ≤ 0 / 10000000 := by
  show Λ 38 ^ 2 * _ ≤ _
  rw [lam_zero_of 38 2 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t39 : f 39 ≤ 0 / 10000000 := by
  show Λ 39 ^ 2 * _ ≤ _
  rw [lam_zero_of 39 3 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t40 : f 40 ≤ 0 / 10000000 := by
  show Λ 40 ^ 2 * _ ≤ _
  rw [lam_zero_of 40 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t41 : f 41 ≤ 82095 / 10000000 :=
  term_le (n := 41) (L := 686 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 41 686 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t42 : f 42 ≤ 0 / 10000000 := by
  show Λ 42 ^ 2 * _ ≤ _
  rw [lam_zero_of 42 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t43 : f 43 ≤ 76607 / 10000000 :=
  term_le (n := 43) (L := 695 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 43 695 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t44 : f 44 ≤ 0 / 10000000 := by
  show Λ 44 ^ 2 * _ ≤ _
  rw [lam_zero_of 44 2 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t45 : f 45 ≤ 0 / 10000000 := by
  show Λ 45 ^ 2 * _ ≤ _
  rw [lam_zero_of 45 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t46 : f 46 ≤ 0 / 10000000 := by
  show Λ 46 ^ 2 * _ ≤ _
  rw [lam_zero_of 46 2 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t47 : f 47 ≤ 67109 / 10000000 :=
  term_le (n := 47) (L := 711 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 47 711 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t48 : f 48 ≤ 0 / 10000000 := by
  show Λ 48 ^ 2 * _ ≤ _
  rw [lam_zero_of 48 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t49 : f 49 ≤ 15829 / 10000000 :=
  term_le (n := 49) (L := 360 * 0.6931471808 / 128) (by norm_num) (by
    rw [show (49:ℕ) = 7 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 7 360 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t50 : f 50 ≤ 0 / 10000000 := by
  show Λ 50 ^ 2 * _ ≤ _
  rw [lam_zero_of 50 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t51 : f 51 ≤ 0 / 10000000 := by
  show Λ 51 ^ 2 * _ ≤ _
  rw [lam_zero_of 51 3 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t52 : f 52 ≤ 0 / 10000000 := by
  show Λ 52 ^ 2 * _ ≤ _
  rw [lam_zero_of 52 2 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t53 : f 53 ≤ 56244 / 10000000 :=
  term_le (n := 53) (L := 734 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 53 734 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t54 : f 54 ≤ 0 / 10000000 := by
  show Λ 54 ^ 2 * _ ≤ _
  rw [lam_zero_of 54 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t55 : f 55 ≤ 0 / 10000000 := by
  show Λ 55 ^ 2 * _ ≤ _
  rw [lam_zero_of 55 5 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t56 : f 56 ≤ 0 / 10000000 := by
  show Λ 56 ^ 2 * _ ≤ _
  rw [lam_zero_of 56 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t57 : f 57 ≤ 0 / 10000000 := by
  show Λ 57 ^ 2 * _ ≤ _
  rw [lam_zero_of 57 3 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t58 : f 58 ≤ 0 / 10000000 := by
  show Λ 58 ^ 2 * _ ≤ _
  rw [lam_zero_of 58 2 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t59 : f 59 ≤ 47766 / 10000000 :=
  term_le (n := 59) (L := 753 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 59 753 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t60 : f 60 ≤ 0 / 10000000 := by
  show Λ 60 ^ 2 * _ ≤ _
  rw [lam_zero_of 60 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t61 : f 61 ≤ 45520 / 10000000 :=
  term_le (n := 61) (L := 760 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 61 760 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t62 : f 62 ≤ 0 / 10000000 := by
  show Λ 62 ^ 2 * _ ≤ _
  rw [lam_zero_of 62 2 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t63 : f 63 ≤ 0 / 10000000 := by
  show Λ 63 ^ 2 * _ ≤ _
  rw [lam_zero_of 63 3 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t64 : f 64 ≤ 1173 / 10000000 :=
  term_le (n := 64) (L := 128 * 0.6931471808 / 128) (by norm_num) (by
    rw [show (64:ℕ) = 2 ^ 6 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 2 128 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t65 : f 65 ≤ 0 / 10000000 := by
  show Λ 65 ^ 2 * _ ≤ _
  rw [lam_zero_of 65 5 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t66 : f 66 ≤ 0 / 10000000 := by
  show Λ 66 ^ 2 * _ ≤ _
  rw [lam_zero_of 66 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t67 : f 67 ≤ 39439 / 10000000 :=
  term_le (n := 67) (L := 777 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 67 777 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t68 : f 68 ≤ 0 / 10000000 := by
  show Λ 68 ^ 2 * _ ≤ _
  rw [lam_zero_of 68 2 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t69 : f 69 ≤ 0 / 10000000 := by
  show Λ 69 ^ 2 * _ ≤ _
  rw [lam_zero_of 69 3 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t70 : f 70 ≤ 0 / 10000000 := by
  show Λ 70 ^ 2 * _ ≤ _
  rw [lam_zero_of 70 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t71 : f 71 ≤ 36122 / 10000000 :=
  term_le (n := 71) (L := 788 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 71 788 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t72 : f 72 ≤ 0 / 10000000 := by
  show Λ 72 ^ 2 * _ ≤ _
  rw [lam_zero_of 72 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t73 : f 73 ≤ 34605 / 10000000 :=
  term_le (n := 73) (L := 793 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 73 793 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t74 : f 74 ≤ 0 / 10000000 := by
  show Λ 74 ^ 2 * _ ≤ _
  rw [lam_zero_of 74 2 37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t75 : f 75 ≤ 0 / 10000000 := by
  show Λ 75 ^ 2 * _ ≤ _
  rw [lam_zero_of 75 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t76 : f 76 ≤ 0 / 10000000 := by
  show Λ 76 ^ 2 * _ ≤ _
  rw [lam_zero_of 76 2 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t77 : f 77 ≤ 0 / 10000000 := by
  show Λ 77 ^ 2 * _ ≤ _
  rw [lam_zero_of 77 7 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t78 : f 78 ≤ 0 / 10000000 := by
  show Λ 78 ^ 2 * _ ≤ _
  rw [lam_zero_of 78 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t79 : f 79 ≤ 30601 / 10000000 :=
  term_le (n := 79) (L := 807 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 79 807 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t80 : f 80 ≤ 0 / 10000000 := by
  show Λ 80 ^ 2 * _ ≤ _
  rw [lam_zero_of 80 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t81 : f 81 ≤ 1842 / 10000000 :=
  term_le (n := 81) (L := 203 * 0.6931471808 / 128) (by norm_num) (by
    rw [show (81:ℕ) = 3 ^ 4 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 3 203 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t82 : f 82 ≤ 0 / 10000000 := by
  show Λ 82 ^ 2 * _ ≤ _
  rw [lam_zero_of 82 2 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t83 : f 83 ≤ 28414 / 10000000 :=
  term_le (n := 83) (L := 817 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 83 817 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t84 : f 84 ≤ 0 / 10000000 := by
  show Λ 84 ^ 2 * _ ≤ _
  rw [lam_zero_of 84 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t85 : f 85 ≤ 0 / 10000000 := by
  show Λ 85 ^ 2 * _ ≤ _
  rw [lam_zero_of 85 5 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t86 : f 86 ≤ 0 / 10000000 := by
  show Λ 86 ^ 2 * _ ≤ _
  rw [lam_zero_of 86 2 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t87 : f 87 ≤ 0 / 10000000 := by
  show Λ 87 ^ 2 * _ ≤ _
  rw [lam_zero_of 87 3 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t88 : f 88 ≤ 0 / 10000000 := by
  show Λ 88 ^ 2 * _ ≤ _
  rw [lam_zero_of 88 2 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t89 : f 89 ≤ 25443 / 10000000 :=
  term_le (n := 89) (L := 829 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 89 829 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t90 : f 90 ≤ 0 / 10000000 := by
  show Λ 90 ^ 2 * _ ≤ _
  rw [lam_zero_of 90 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t91 : f 91 ≤ 0 / 10000000 := by
  show Λ 91 ^ 2 * _ ≤ _
  rw [lam_zero_of 91 7 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t92 : f 92 ≤ 0 / 10000000 := by
  show Λ 92 ^ 2 * _ ≤ _
  rw [lam_zero_of 92 2 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t93 : f 93 ≤ 0 / 10000000 := by
  show Λ 93 ^ 2 * _ ≤ _
  rw [lam_zero_of 93 3 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t94 : f 94 ≤ 0 / 10000000 := by
  show Λ 94 ^ 2 * _ ≤ _
  rw [lam_zero_of 94 2 47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t95 : f 95 ≤ 0 / 10000000 := by
  show Λ 95 ^ 2 * _ ≤ _
  rw [lam_zero_of 95 5 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t96 : f 96 ≤ 0 / 10000000 := by
  show Λ 96 ^ 2 * _ ≤ _
  rw [lam_zero_of 96 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t97 : f 97 ≤ 22254 / 10000000 :=
  term_le (n := 97) (L := 845 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 97 845 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t98 : f 98 ≤ 0 / 10000000 := by
  show Λ 98 ^ 2 * _ ≤ _
  rw [lam_zero_of 98 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t99 : f 99 ≤ 0 / 10000000 := by
  show Λ 99 ^ 2 * _ ≤ _
  rw [lam_zero_of 99 3 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t100 : f 100 ≤ 0 / 10000000 := by
  show Λ 100 ^ 2 * _ ≤ _
  rw [lam_zero_of 100 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t101 : f 101 ≤ 20917 / 10000000 :=
  term_le (n := 101) (L := 853 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 101 853 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t102 : f 102 ≤ 0 / 10000000 := by
  show Λ 102 ^ 2 * _ ≤ _
  rw [lam_zero_of 102 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t103 : f 103 ≤ 20254 / 10000000 :=
  term_le (n := 103) (L := 856 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 103 856 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t104 : f 104 ≤ 0 / 10000000 := by
  show Λ 104 ^ 2 * _ ≤ _
  rw [lam_zero_of 104 2 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t105 : f 105 ≤ 0 / 10000000 := by
  show Λ 105 ^ 2 * _ ≤ _
  rw [lam_zero_of 105 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t106 : f 106 ≤ 0 / 10000000 := by
  show Λ 106 ^ 2 * _ ≤ _
  rw [lam_zero_of 106 2 53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t107 : f 107 ≤ 19076 / 10000000 :=
  term_le (n := 107) (L := 863 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 107 863 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t108 : f 108 ≤ 0 / 10000000 := by
  show Λ 108 ^ 2 * _ ≤ _
  rw [lam_zero_of 108 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t109 : f 109 ≤ 18554 / 10000000 :=
  term_le (n := 109) (L := 867 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 109 867 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t110 : f 110 ≤ 0 / 10000000 := by
  show Λ 110 ^ 2 * _ ≤ _
  rw [lam_zero_of 110 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t111 : f 111 ≤ 0 / 10000000 := by
  show Λ 111 ^ 2 * _ ≤ _
  rw [lam_zero_of 111 3 37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t112 : f 112 ≤ 0 / 10000000 := by
  show Λ 112 ^ 2 * _ ≤ _
  rw [lam_zero_of 112 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t113 : f 113 ≤ 17503 / 10000000 :=
  term_le (n := 113) (L := 873 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 113 873 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t114 : f 114 ≤ 0 / 10000000 := by
  show Λ 114 ^ 2 * _ ≤ _
  rw [lam_zero_of 114 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t115 : f 115 ≤ 0 / 10000000 := by
  show Λ 115 ^ 2 * _ ≤ _
  rw [lam_zero_of 115 5 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t116 : f 116 ≤ 0 / 10000000 := by
  show Λ 116 ^ 2 * _ ≤ _
  rw [lam_zero_of 116 2 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t117 : f 117 ≤ 0 / 10000000 := by
  show Λ 117 ^ 2 * _ ≤ _
  rw [lam_zero_of 117 3 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t118 : f 118 ≤ 0 / 10000000 := by
  show Λ 118 ^ 2 * _ ≤ _
  rw [lam_zero_of 118 2 59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t119 : f 119 ≤ 0 / 10000000 := by
  show Λ 119 ^ 2 * _ ≤ _
  rw [lam_zero_of 119 7 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t120 : f 120 ≤ 0 / 10000000 := by
  show Λ 120 ^ 2 * _ ≤ _
  rw [lam_zero_of 120 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t121 : f 121 ≤ 3931 / 10000000 :=
  term_le (n := 121) (L := 443 * 0.6931471808 / 128) (by norm_num) (by
    rw [show (121:ℕ) = 11 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 11 443 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t122 : f 122 ≤ 0 / 10000000 := by
  show Λ 122 ^ 2 * _ ≤ _
  rw [lam_zero_of 122 2 61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t123 : f 123 ≤ 0 / 10000000 := by
  show Λ 123 ^ 2 * _ ≤ _
  rw [lam_zero_of 123 3 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t124 : f 124 ≤ 0 / 10000000 := by
  show Λ 124 ^ 2 * _ ≤ _
  rw [lam_zero_of 124 2 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t125 : f 125 ≤ 1667 / 10000000 :=
  term_le (n := 125) (L := 298 * 0.6931471808 / 128) (by norm_num) (by
    rw [show (125:ℕ) = 5 ^ 3 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 5 298 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t126 : f 126 ≤ 0 / 10000000 := by
  show Λ 126 ^ 2 * _ ≤ _
  rw [lam_zero_of 126 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t127 : f 127 ≤ 14564 / 10000000 :=
  term_le (n := 127) (L := 895 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 127 895 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t128 : f 128 ≤ 294 / 10000000 :=
  term_le (n := 128) (L := 128 * 0.6931471808 / 128) (by norm_num) (by
    rw [show (128:ℕ) = 2 ^ 7 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 2 128 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t129 : f 129 ≤ 0 / 10000000 := by
  show Λ 129 ^ 2 * _ ≤ _
  rw [lam_zero_of 129 3 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t130 : f 130 ≤ 0 / 10000000 := by
  show Λ 130 ^ 2 * _ ≤ _
  rw [lam_zero_of 130 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t131 : f 131 ≤ 13872 / 10000000 :=
  term_le (n := 131) (L := 901 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 131 901 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t132 : f 132 ≤ 0 / 10000000 := by
  show Λ 132 ^ 2 * _ ≤ _
  rw [lam_zero_of 132 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t133 : f 133 ≤ 0 / 10000000 := by
  show Λ 133 ^ 2 * _ ≤ _
  rw [lam_zero_of 133 7 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t134 : f 134 ≤ 0 / 10000000 := by
  show Λ 134 ^ 2 * _ ≤ _
  rw [lam_zero_of 134 2 67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t135 : f 135 ≤ 0 / 10000000 := by
  show Λ 135 ^ 2 * _ ≤ _
  rw [lam_zero_of 135 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t136 : f 136 ≤ 0 / 10000000 := by
  show Λ 136 ^ 2 * _ ≤ _
  rw [lam_zero_of 136 2 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t137 : f 137 ≤ 12910 / 10000000 :=
  term_le (n := 137) (L := 909 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 137 909 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t138 : f 138 ≤ 0 / 10000000 := by
  show Λ 138 ^ 2 * _ ≤ _
  rw [lam_zero_of 138 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t139 : f 139 ≤ 12624 / 10000000 :=
  term_le (n := 139) (L := 912 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 139 912 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t140 : f 140 ≤ 0 / 10000000 := by
  show Λ 140 ^ 2 * _ ≤ _
  rw [lam_zero_of 140 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t141 : f 141 ≤ 0 / 10000000 := by
  show Λ 141 ^ 2 * _ ≤ _
  rw [lam_zero_of 141 3 47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t142 : f 142 ≤ 0 / 10000000 := by
  show Λ 142 ^ 2 * _ ≤ _
  rw [lam_zero_of 142 2 71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t143 : f 143 ≤ 0 / 10000000 := by
  show Λ 143 ^ 2 * _ ≤ _
  rw [lam_zero_of 143 11 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t144 : f 144 ≤ 0 / 10000000 := by
  show Λ 144 ^ 2 * _ ≤ _
  rw [lam_zero_of 144 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t145 : f 145 ≤ 0 / 10000000 := by
  show Λ 145 ^ 2 * _ ≤ _
  rw [lam_zero_of 145 5 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t146 : f 146 ≤ 0 / 10000000 := by
  show Λ 146 ^ 2 * _ ≤ _
  rw [lam_zero_of 146 2 73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t147 : f 147 ≤ 0 / 10000000 := by
  show Λ 147 ^ 2 * _ ≤ _
  rw [lam_zero_of 147 3 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t148 : f 148 ≤ 0 / 10000000 := by
  show Λ 148 ^ 2 * _ ≤ _
  rw [lam_zero_of 148 2 37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t149 : f 149 ≤ 11302 / 10000000 :=
  term_le (n := 149) (L := 925 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 149 925 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t150 : f 150 ≤ 0 / 10000000 := by
  show Λ 150 ^ 2 * _ ≤ _
  rw [lam_zero_of 150 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t151 : f 151 ≤ 11052 / 10000000 :=
  term_le (n := 151) (L := 927 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 151 927 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t152 : f 152 ≤ 0 / 10000000 := by
  show Λ 152 ^ 2 * _ ≤ _
  rw [lam_zero_of 152 2 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t153 : f 153 ≤ 0 / 10000000 := by
  show Λ 153 ^ 2 * _ ≤ _
  rw [lam_zero_of 153 3 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t154 : f 154 ≤ 0 / 10000000 := by
  show Λ 154 ^ 2 * _ ≤ _
  rw [lam_zero_of 154 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t155 : f 155 ≤ 0 / 10000000 := by
  show Λ 155 ^ 2 * _ ≤ _
  rw [lam_zero_of 155 5 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t156 : f 156 ≤ 0 / 10000000 := by
  show Λ 156 ^ 2 * _ ≤ _
  rw [lam_zero_of 156 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t157 : f 157 ≤ 10379 / 10000000 :=
  term_le (n := 157) (L := 934 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 157 934 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t158 : f 158 ≤ 0 / 10000000 := by
  show Λ 158 ^ 2 * _ ≤ _
  rw [lam_zero_of 158 2 79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t159 : f 159 ≤ 0 / 10000000 := by
  show Λ 159 ^ 2 * _ ≤ _
  rw [lam_zero_of 159 3 53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t160 : f 160 ≤ 0 / 10000000 := by
  show Λ 160 ^ 2 * _ ≤ _
  rw [lam_zero_of 160 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t161 : f 161 ≤ 0 / 10000000 := by
  show Λ 161 ^ 2 * _ ≤ _
  rw [lam_zero_of 161 7 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t162 : f 162 ≤ 0 / 10000000 := by
  show Λ 162 ^ 2 * _ ≤ _
  rw [lam_zero_of 162 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t163 : f 163 ≤ 9774 / 10000000 :=
  term_le (n := 163) (L := 941 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 163 941 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t164 : f 164 ≤ 0 / 10000000 := by
  show Λ 164 ^ 2 * _ ≤ _
  rw [lam_zero_of 164 2 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t165 : f 165 ≤ 0 / 10000000 := by
  show Λ 165 ^ 2 * _ ≤ _
  rw [lam_zero_of 165 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t166 : f 166 ≤ 0 / 10000000 := by
  show Λ 166 ^ 2 * _ ≤ _
  rw [lam_zero_of 166 2 83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t167 : f 167 ≤ 9410 / 10000000 :=
  term_le (n := 167) (L := 946 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 167 946 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t168 : f 168 ≤ 0 / 10000000 := by
  show Λ 168 ^ 2 * _ ≤ _
  rw [lam_zero_of 168 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t169 : f 169 ≤ 2307 / 10000000 :=
  term_le (n := 169) (L := 474 * 0.6931471808 / 128) (by norm_num) (by
    rw [show (169:ℕ) = 13 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 13 474 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t170 : f 170 ≤ 0 / 10000000 := by
  show Λ 170 ^ 2 * _ ≤ _
  rw [lam_zero_of 170 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t171 : f 171 ≤ 0 / 10000000 := by
  show Λ 171 ^ 2 * _ ≤ _
  rw [lam_zero_of 171 3 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t172 : f 172 ≤ 0 / 10000000 := by
  show Λ 172 ^ 2 * _ ≤ _
  rw [lam_zero_of 172 2 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t173 : f 173 ≤ 8880 / 10000000 :=
  term_le (n := 173) (L := 952 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 173 952 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t174 : f 174 ≤ 0 / 10000000 := by
  show Λ 174 ^ 2 * _ ≤ _
  rw [lam_zero_of 174 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t175 : f 175 ≤ 0 / 10000000 := by
  show Λ 175 ^ 2 * _ ≤ _
  rw [lam_zero_of 175 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t176 : f 176 ≤ 0 / 10000000 := by
  show Λ 176 ^ 2 * _ ≤ _
  rw [lam_zero_of 176 2 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t177 : f 177 ≤ 0 / 10000000 := by
  show Λ 177 ^ 2 * _ ≤ _
  rw [lam_zero_of 177 3 59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t178 : f 178 ≤ 0 / 10000000 := by
  show Λ 178 ^ 2 * _ ≤ _
  rw [lam_zero_of 178 2 89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t179 : f 179 ≤ 8400 / 10000000 :=
  term_le (n := 179) (L := 958 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 179 958 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t180 : f 180 ≤ 0 / 10000000 := by
  show Λ 180 ^ 2 * _ ≤ _
  rw [lam_zero_of 180 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t181 : f 181 ≤ 8250 / 10000000 :=
  term_le (n := 181) (L := 960 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 181 960 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t182 : f 182 ≤ 0 / 10000000 := by
  show Λ 182 ^ 2 * _ ≤ _
  rw [lam_zero_of 182 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t183 : f 183 ≤ 0 / 10000000 := by
  show Λ 183 ^ 2 * _ ≤ _
  rw [lam_zero_of 183 3 61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t184 : f 184 ≤ 0 / 10000000 := by
  show Λ 184 ^ 2 * _ ≤ _
  rw [lam_zero_of 184 2 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t185 : f 185 ≤ 0 / 10000000 := by
  show Λ 185 ^ 2 * _ ≤ _
  rw [lam_zero_of 185 5 37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t186 : f 186 ≤ 0 / 10000000 := by
  show Λ 186 ^ 2 * _ ≤ _
  rw [lam_zero_of 186 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t187 : f 187 ≤ 0 / 10000000 := by
  show Λ 187 ^ 2 * _ ≤ _
  rw [lam_zero_of 187 11 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t188 : f 188 ≤ 0 / 10000000 := by
  show Λ 188 ^ 2 * _ ≤ _
  rw [lam_zero_of 188 2 47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t189 : f 189 ≤ 0 / 10000000 := by
  show Λ 189 ^ 2 * _ ≤ _
  rw [lam_zero_of 189 3 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t190 : f 190 ≤ 0 / 10000000 := by
  show Λ 190 ^ 2 * _ ≤ _
  rw [lam_zero_of 190 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t191 : f 191 ≤ 7564 / 10000000 :=
  term_le (n := 191) (L := 970 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 191 970 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t192 : f 192 ≤ 0 / 10000000 := by
  show Λ 192 ^ 2 * _ ≤ _
  rw [lam_zero_of 192 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t193 : f 193 ≤ 7438 / 10000000 :=
  term_le (n := 193) (L := 972 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 193 972 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t194 : f 194 ≤ 0 / 10000000 := by
  show Λ 194 ^ 2 * _ ≤ _
  rw [lam_zero_of 194 2 97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t195 : f 195 ≤ 0 / 10000000 := by
  show Λ 195 ^ 2 * _ ≤ _
  rw [lam_zero_of 195 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t196 : f 196 ≤ 0 / 10000000 := by
  show Λ 196 ^ 2 * _ ≤ _
  rw [lam_zero_of 196 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t197 : f 197 ≤ 7198 / 10000000 :=
  term_le (n := 197) (L := 976 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 197 976 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t198 : f 198 ≤ 0 / 10000000 := by
  show Λ 198 ^ 2 * _ ≤ _
  rw [lam_zero_of 198 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t199 : f 199 ≤ 7083 / 10000000 :=
  term_le (n := 199) (L := 978 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 199 978 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t200 : f 200 ≤ 0 / 10000000 := by
  show Λ 200 ^ 2 * _ ≤ _
  rw [lam_zero_of 200 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t201 : f 201 ≤ 0 / 10000000 := by
  show Λ 201 ^ 2 * _ ≤ _
  rw [lam_zero_of 201 3 67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t202 : f 202 ≤ 0 / 10000000 := by
  show Λ 202 ^ 2 * _ ≤ _
  rw [lam_zero_of 202 2 101 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t203 : f 203 ≤ 0 / 10000000 := by
  show Λ 203 ^ 2 * _ ≤ _
  rw [lam_zero_of 203 7 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t204 : f 204 ≤ 0 / 10000000 := by
  show Λ 204 ^ 2 * _ ≤ _
  rw [lam_zero_of 204 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t205 : f 205 ≤ 0 / 10000000 := by
  show Λ 205 ^ 2 * _ ≤ _
  rw [lam_zero_of 205 5 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t206 : f 206 ≤ 0 / 10000000 := by
  show Λ 206 ^ 2 * _ ≤ _
  rw [lam_zero_of 206 2 103 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t207 : f 207 ≤ 0 / 10000000 := by
  show Λ 207 ^ 2 * _ ≤ _
  rw [lam_zero_of 207 3 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t208 : f 208 ≤ 0 / 10000000 := by
  show Λ 208 ^ 2 * _ ≤ _
  rw [lam_zero_of 208 2 13 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t209 : f 209 ≤ 0 / 10000000 := by
  show Λ 209 ^ 2 * _ ≤ _
  rw [lam_zero_of 209 11 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t210 : f 210 ≤ 0 / 10000000 := by
  show Λ 210 ^ 2 * _ ≤ _
  rw [lam_zero_of 210 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t211 : f 211 ≤ 6443 / 10000000 :=
  term_le (n := 211) (L := 989 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 211 989 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t212 : f 212 ≤ 0 / 10000000 := by
  show Λ 212 ^ 2 * _ ≤ _
  rw [lam_zero_of 212 2 53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t213 : f 213 ≤ 0 / 10000000 := by
  show Λ 213 ^ 2 * _ ≤ _
  rw [lam_zero_of 213 3 71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t214 : f 214 ≤ 0 / 10000000 := by
  show Λ 214 ^ 2 * _ ≤ _
  rw [lam_zero_of 214 2 107 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t215 : f 215 ≤ 0 / 10000000 := by
  show Λ 215 ^ 2 * _ ≤ _
  rw [lam_zero_of 215 5 43 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t216 : f 216 ≤ 0 / 10000000 := by
  show Λ 216 ^ 2 * _ ≤ _
  rw [lam_zero_of 216 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t217 : f 217 ≤ 0 / 10000000 := by
  show Λ 217 ^ 2 * _ ≤ _
  rw [lam_zero_of 217 7 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t218 : f 218 ≤ 0 / 10000000 := by
  show Λ 218 ^ 2 * _ ≤ _
  rw [lam_zero_of 218 2 109 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t219 : f 219 ≤ 0 / 10000000 := by
  show Λ 219 ^ 2 * _ ≤ _
  rw [lam_zero_of 219 3 73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t220 : f 220 ≤ 0 / 10000000 := by
  show Λ 220 ^ 2 * _ ≤ _
  rw [lam_zero_of 220 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t221 : f 221 ≤ 0 / 10000000 := by
  show Λ 221 ^ 2 * _ ≤ _
  rw [lam_zero_of 221 13 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t222 : f 222 ≤ 0 / 10000000 := by
  show Λ 222 ^ 2 * _ ≤ _
  rw [lam_zero_of 222 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t223 : f 223 ≤ 5886 / 10000000 :=
  term_le (n := 223) (L := 999 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 223 999 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t224 : f 224 ≤ 0 / 10000000 := by
  show Λ 224 ^ 2 * _ ≤ _
  rw [lam_zero_of 224 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t225 : f 225 ≤ 0 / 10000000 := by
  show Λ 225 ^ 2 * _ ≤ _
  rw [lam_zero_of 225 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t226 : f 226 ≤ 0 / 10000000 := by
  show Λ 226 ^ 2 * _ ≤ _
  rw [lam_zero_of 226 2 113 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t227 : f 227 ≤ 5714 / 10000000 :=
  term_le (n := 227) (L := 1002 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 227 1002 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t228 : f 228 ≤ 0 / 10000000 := by
  show Λ 228 ^ 2 * _ ≤ _
  rw [lam_zero_of 228 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t229 : f 229 ≤ 5637 / 10000000 :=
  term_le (n := 229) (L := 1004 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 229 1004 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t230 : f 230 ≤ 0 / 10000000 := by
  show Λ 230 ^ 2 * _ ≤ _
  rw [lam_zero_of 230 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t231 : f 231 ≤ 0 / 10000000 := by
  show Λ 231 ^ 2 * _ ≤ _
  rw [lam_zero_of 231 3 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t232 : f 232 ≤ 0 / 10000000 := by
  show Λ 232 ^ 2 * _ ≤ _
  rw [lam_zero_of 232 2 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t233 : f 233 ≤ 5478 / 10000000 :=
  term_le (n := 233) (L := 1007 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 233 1007 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t234 : f 234 ≤ 0 / 10000000 := by
  show Λ 234 ^ 2 * _ ≤ _
  rw [lam_zero_of 234 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t235 : f 235 ≤ 0 / 10000000 := by
  show Λ 235 ^ 2 * _ ≤ _
  rw [lam_zero_of 235 5 47 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t236 : f 236 ≤ 0 / 10000000 := by
  show Λ 236 ^ 2 * _ ≤ _
  rw [lam_zero_of 236 2 59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t237 : f 237 ≤ 0 / 10000000 := by
  show Λ 237 ^ 2 * _ ≤ _
  rw [lam_zero_of 237 3 79 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t238 : f 238 ≤ 0 / 10000000 := by
  show Λ 238 ^ 2 * _ ≤ _
  rw [lam_zero_of 238 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t239 : f 239 ≤ 5258 / 10000000 :=
  term_le (n := 239) (L := 1012 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 239 1012 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t240 : f 240 ≤ 0 / 10000000 := by
  show Λ 240 ^ 2 * _ ≤ _
  rw [lam_zero_of 240 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t241 : f 241 ≤ 5182 / 10000000 :=
  term_le (n := 241) (L := 1013 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 241 1013 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t242 : f 242 ≤ 0 / 10000000 := by
  show Λ 242 ^ 2 * _ ≤ _
  rw [lam_zero_of 242 2 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t243 : f 243 ≤ 205 / 10000000 :=
  term_le (n := 243) (L := 203 * 0.6931471808 / 128) (by norm_num) (by
    rw [show (243:ℕ) = 3 ^ 5 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 3 203 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t244 : f 244 ≤ 0 / 10000000 := by
  show Λ 244 ^ 2 * _ ≤ _
  rw [lam_zero_of 244 2 61 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t245 : f 245 ≤ 0 / 10000000 := by
  show Λ 245 ^ 2 * _ ≤ _
  rw [lam_zero_of 245 5 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t246 : f 246 ≤ 0 / 10000000 := by
  show Λ 246 ^ 2 * _ ≤ _
  rw [lam_zero_of 246 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t247 : f 247 ≤ 0 / 10000000 := by
  show Λ 247 ^ 2 * _ ≤ _
  rw [lam_zero_of 247 13 19 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t248 : f 248 ≤ 0 / 10000000 := by
  show Λ 248 ^ 2 * _ ≤ _
  rw [lam_zero_of 248 2 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t249 : f 249 ≤ 0 / 10000000 := by
  show Λ 249 ^ 2 * _ ≤ _
  rw [lam_zero_of 249 3 83 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t250 : f 250 ≤ 0 / 10000000 := by
  show Λ 250 ^ 2 * _ ≤ _
  rw [lam_zero_of 250 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t251 : f 251 ≤ 4853 / 10000000 :=
  term_le (n := 251) (L := 1021 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 251 1021 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t252 : f 252 ≤ 0 / 10000000 := by
  show Λ 252 ^ 2 * _ ≤ _
  rw [lam_zero_of 252 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t253 : f 253 ≤ 0 / 10000000 := by
  show Λ 253 ^ 2 * _ ≤ _
  rw [lam_zero_of 253 11 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t254 : f 254 ≤ 0 / 10000000 := by
  show Λ 254 ^ 2 * _ ≤ _
  rw [lam_zero_of 254 2 127 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t255 : f 255 ≤ 0 / 10000000 := by
  show Λ 255 ^ 2 * _ ≤ _
  rw [lam_zero_of 255 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t256 : f 256 ≤ 74 / 10000000 :=
  term_le (n := 256) (L := 128 * 0.6931471808 / 128) (by norm_num) (by
    rw [show (256:ℕ) = 2 ^ 8 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 2 128 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t257 : f 257 ≤ 4665 / 10000000 :=
  term_le (n := 257) (L := 1025 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 257 1025 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t258 : f 258 ≤ 0 / 10000000 := by
  show Λ 258 ^ 2 * _ ≤ _
  rw [lam_zero_of 258 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t259 : f 259 ≤ 0 / 10000000 := by
  show Λ 259 ^ 2 * _ ≤ _
  rw [lam_zero_of 259 7 37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t260 : f 260 ≤ 0 / 10000000 := by
  show Λ 260 ^ 2 * _ ≤ _
  rw [lam_zero_of 260 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t261 : f 261 ≤ 0 / 10000000 := by
  show Λ 261 ^ 2 * _ ≤ _
  rw [lam_zero_of 261 3 29 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t262 : f 262 ≤ 0 / 10000000 := by
  show Λ 262 ^ 2 * _ ≤ _
  rw [lam_zero_of 262 2 131 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t263 : f 263 ≤ 4490 / 10000000 :=
  term_le (n := 263) (L := 1029 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 263 1029 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t264 : f 264 ≤ 0 / 10000000 := by
  show Λ 264 ^ 2 * _ ≤ _
  rw [lam_zero_of 264 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t265 : f 265 ≤ 0 / 10000000 := by
  show Λ 265 ^ 2 * _ ≤ _
  rw [lam_zero_of 265 5 53 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t266 : f 266 ≤ 0 / 10000000 := by
  show Λ 266 ^ 2 * _ ≤ _
  rw [lam_zero_of 266 2 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t267 : f 267 ≤ 0 / 10000000 := by
  show Λ 267 ^ 2 * _ ≤ _
  rw [lam_zero_of 267 3 89 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t268 : f 268 ≤ 0 / 10000000 := by
  show Λ 268 ^ 2 * _ ≤ _
  rw [lam_zero_of 268 2 67 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t269 : f 269 ≤ 4333 / 10000000 :=
  term_le (n := 269) (L := 1034 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 269 1034 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t270 : f 270 ≤ 0 / 10000000 := by
  show Λ 270 ^ 2 * _ ≤ _
  rw [lam_zero_of 270 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t271 : f 271 ≤ 4278 / 10000000 :=
  term_le (n := 271) (L := 1035 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 271 1035 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t272 : f 272 ≤ 0 / 10000000 := by
  show Λ 272 ^ 2 * _ ≤ _
  rw [lam_zero_of 272 2 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t273 : f 273 ≤ 0 / 10000000 := by
  show Λ 273 ^ 2 * _ ≤ _
  rw [lam_zero_of 273 3 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t274 : f 274 ≤ 0 / 10000000 := by
  show Λ 274 ^ 2 * _ ≤ _
  rw [lam_zero_of 274 2 137 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t275 : f 275 ≤ 0 / 10000000 := by
  show Λ 275 ^ 2 * _ ≤ _
  rw [lam_zero_of 275 5 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t276 : f 276 ≤ 0 / 10000000 := by
  show Λ 276 ^ 2 * _ ≤ _
  rw [lam_zero_of 276 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t277 : f 277 ≤ 4126 / 10000000 :=
  term_le (n := 277) (L := 1039 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 277 1039 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t278 : f 278 ≤ 0 / 10000000 := by
  show Λ 278 ^ 2 * _ ≤ _
  rw [lam_zero_of 278 2 139 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t279 : f 279 ≤ 0 / 10000000 := by
  show Λ 279 ^ 2 * _ ≤ _
  rw [lam_zero_of 279 3 31 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t280 : f 280 ≤ 0 / 10000000 := by
  show Λ 280 ^ 2 * _ ≤ _
  rw [lam_zero_of 280 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t281 : f 281 ≤ 4033 / 10000000 :=
  term_le (n := 281) (L := 1042 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 281 1042 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t282 : f 282 ≤ 0 / 10000000 := by
  show Λ 282 ^ 2 * _ ≤ _
  rw [lam_zero_of 282 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t283 : f 283 ≤ 3984 / 10000000 :=
  term_le (n := 283) (L := 1043 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 283 1043 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t284 : f 284 ≤ 0 / 10000000 := by
  show Λ 284 ^ 2 * _ ≤ _
  rw [lam_zero_of 284 2 71 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t285 : f 285 ≤ 0 / 10000000 := by
  show Λ 285 ^ 2 * _ ≤ _
  rw [lam_zero_of 285 3 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t286 : f 286 ≤ 0 / 10000000 := by
  show Λ 286 ^ 2 * _ ≤ _
  rw [lam_zero_of 286 2 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t287 : f 287 ≤ 0 / 10000000 := by
  show Λ 287 ^ 2 * _ ≤ _
  rw [lam_zero_of 287 7 41 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t288 : f 288 ≤ 0 / 10000000 := by
  show Λ 288 ^ 2 * _ ≤ _
  rw [lam_zero_of 288 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t289 : f 289 ≤ 965 / 10000000 :=
  term_le (n := 289) (L := 524 * 0.6931471808 / 128) (by norm_num) (by
    rw [show (289:ℕ) = 17 ^ 2 by norm_num, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 17 524 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t290 : f 290 ≤ 0 / 10000000 := by
  show Λ 290 ^ 2 * _ ≤ _
  rw [lam_zero_of 290 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t291 : f 291 ≤ 0 / 10000000 := by
  show Λ 291 ^ 2 * _ ≤ _
  rw [lam_zero_of 291 3 97 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t292 : f 292 ≤ 0 / 10000000 := by
  show Λ 292 ^ 2 * _ ≤ _
  rw [lam_zero_of 292 2 73 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t293 : f 293 ≤ 3759 / 10000000 :=
  term_le (n := 293) (L := 1049 * 0.6931471808 / 128) (by norm_num) (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime (by norm_num)]
    exact (log_le_pow 293 1049 (by norm_num)).trans_eq (by norm_num)) (by norm_num)

theorem t294 : f 294 ≤ 0 / 10000000 := by
  show Λ 294 ^ 2 * _ ≤ _
  rw [lam_zero_of 294 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t295 : f 295 ≤ 0 / 10000000 := by
  show Λ 295 ^ 2 * _ ≤ _
  rw [lam_zero_of 295 5 59 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t296 : f 296 ≤ 0 / 10000000 := by
  show Λ 296 ^ 2 * _ ≤ _
  rw [lam_zero_of 296 2 37 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t297 : f 297 ≤ 0 / 10000000 := by
  show Λ 297 ^ 2 * _ ≤ _
  rw [lam_zero_of 297 3 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t298 : f 298 ≤ 0 / 10000000 := by
  show Λ 298 ^ 2 * _ ≤ _
  rw [lam_zero_of 298 2 149 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t299 : f 299 ≤ 0 / 10000000 := by
  show Λ 299 ^ 2 * _ ≤ _
  rw [lam_zero_of 299 13 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem t300 : f 300 ≤ 0 / 10000000 := by
  show Λ 300 ^ 2 * _ ≤ _
  rw [lam_zero_of 300 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; simp

theorem s1 : S 1 ≤ 0 / 10000000 := by
  have h : S 1 = S 0 + f 0 := S_succ 0
  linarith [t0, S_zero]

theorem s2 : S 2 ≤ 0 / 10000000 := by
  have h : S 2 = S 1 + f 1 := S_succ 1
  linarith [s1, t1]

theorem s3 : S 3 ≤ 1201133 / 10000000 := by
  have h : S 3 = S 2 + f 2 := S_succ 2
  linarith [s2, t2]

theorem s4 : S 4 ≤ 2543838 / 10000000 := by
  have h : S 4 = S 3 + f 3 := S_succ 3
  linarith [s3, t3]

theorem s5 : S 5 ≤ 2844122 / 10000000 := by
  have h : S 5 = S 4 + f 4 := S_succ 4
  linarith [s4, t4]

theorem s6 : S 6 ≤ 3885777 / 10000000 := by
  have h : S 6 = S 5 + f 5 := S_succ 5
  linarith [s5, t5]

theorem s7 : S 7 ≤ 3885777 / 10000000 := by
  have h : S 7 = S 6 + f 6 := S_succ 6
  linarith [s6, t6]

theorem s8 : S 8 ≤ 4661381 / 10000000 := by
  have h : S 8 = S 7 + f 7 := S_succ 7
  linarith [s7, t7]

theorem s9 : S 9 ≤ 4736452 / 10000000 := by
  have h : S 9 = S 8 + f 8 := S_succ 8
  linarith [s8, t8]

theorem s10 : S 10 ≤ 4885642 / 10000000 := by
  have h : S 10 = S 9 + f 9 := S_succ 9
  linarith [s9, t9]

theorem s11 : S 11 ≤ 4885642 / 10000000 := by
  have h : S 11 = S 10 + f 10 := S_succ 10
  linarith [s10, t10]

theorem s12 : S 12 ≤ 5361255 / 10000000 := by
  have h : S 12 = S 11 + f 11 := S_succ 11
  linarith [s11, t11]

theorem s13 : S 13 ≤ 5361255 / 10000000 := by
  have h : S 13 = S 12 + f 12 := S_succ 12
  linarith [s12, t12]

theorem s14 : S 14 ≤ 5751109 / 10000000 := by
  have h : S 14 = S 13 + f 13 := S_succ 13
  linarith [s13, t13]

theorem s15 : S 15 ≤ 5751109 / 10000000 := by
  have h : S 15 = S 14 + f 14 := S_succ 14
  linarith [s14, t14]

theorem s16 : S 16 ≤ 5751109 / 10000000 := by
  have h : S 16 = S 15 + f 15 := S_succ 15
  linarith [s15, t15]

theorem s17 : S 17 ≤ 5769877 / 10000000 := by
  have h : S 17 = S 16 + f 16 := S_succ 16
  linarith [s16, t16]

theorem s18 : S 18 ≤ 6048487 / 10000000 := by
  have h : S 18 = S 17 + f 17 := S_succ 17
  linarith [s17, t17]

theorem s19 : S 19 ≤ 6048487 / 10000000 := by
  have h : S 19 = S 18 + f 18 := S_succ 18
  linarith [s18, t18]

theorem s20 : S 20 ≤ 6288880 / 10000000 := by
  have h : S 20 = S 19 + f 19 := S_succ 19
  linarith [s19, t19]

theorem s21 : S 21 ≤ 6288880 / 10000000 := by
  have h : S 21 = S 20 + f 20 := S_succ 20
  linarith [s20, t20]

theorem s22 : S 22 ≤ 6288880 / 10000000 := by
  have h : S 22 = S 21 + f 21 := S_succ 21
  linarith [s21, t21]

theorem s23 : S 23 ≤ 6288880 / 10000000 := by
  have h : S 23 = S 22 + f 22 := S_succ 22
  linarith [s22, t22]

theorem s24 : S 24 ≤ 6475360 / 10000000 := by
  have h : S 24 = S 23 + f 23 := S_succ 23
  linarith [s23, t23]

theorem s25 : S 25 ≤ 6475360 / 10000000 := by
  have h : S 25 = S 24 + f 24 := S_succ 24
  linarith [s24, t24]

theorem s26 : S 26 ≤ 6517027 / 10000000 := by
  have h : S 26 = S 25 + f 25 := S_succ 25
  linarith [s25, t25]

theorem s27 : S 27 ≤ 6517027 / 10000000 := by
  have h : S 27 = S 26 + f 26 := S_succ 26
  linarith [s26, t26]

theorem s28 : S 28 ≤ 6533604 / 10000000 := by
  have h : S 28 = S 27 + f 27 := S_succ 27
  linarith [s27, t27]

theorem s29 : S 29 ≤ 6533604 / 10000000 := by
  have h : S 29 = S 28 + f 28 := S_succ 28
  linarith [s28, t28]

theorem s30 : S 30 ≤ 6668506 / 10000000 := by
  have h : S 30 = S 29 + f 29 := S_succ 29
  linarith [s29, t29]

theorem s31 : S 31 ≤ 6668506 / 10000000 := by
  have h : S 31 = S 30 + f 30 := S_succ 30
  linarith [s30, t30]

theorem s32 : S 32 ≤ 6791549 / 10000000 := by
  have h : S 32 = S 31 + f 31 := S_succ 31
  linarith [s31, t31]

theorem s33 : S 33 ≤ 6796241 / 10000000 := by
  have h : S 33 = S 32 + f 32 := S_succ 32
  linarith [s32, t32]

theorem s34 : S 34 ≤ 6796241 / 10000000 := by
  have h : S 34 = S 33 + f 33 := S_succ 33
  linarith [s33, t33]

theorem s35 : S 35 ≤ 6796241 / 10000000 := by
  have h : S 35 = S 34 + f 34 := S_succ 34
  linarith [s34, t34]

theorem s36 : S 36 ≤ 6796241 / 10000000 := by
  have h : S 36 = S 35 + f 35 := S_succ 35
  linarith [s35, t35]

theorem s37 : S 37 ≤ 6796241 / 10000000 := by
  have h : S 37 = S 36 + f 36 := S_succ 36
  linarith [s36, t36]

theorem s38 : S 38 ≤ 6891538 / 10000000 := by
  have h : S 38 = S 37 + f 37 := S_succ 37
  linarith [s37, t37]

theorem s39 : S 39 ≤ 6891538 / 10000000 := by
  have h : S 39 = S 38 + f 38 := S_succ 38
  linarith [s38, t38]

theorem s40 : S 40 ≤ 6891538 / 10000000 := by
  have h : S 40 = S 39 + f 39 := S_succ 39
  linarith [s39, t39]

theorem s41 : S 41 ≤ 6891538 / 10000000 := by
  have h : S 41 = S 40 + f 40 := S_succ 40
  linarith [s40, t40]

theorem s42 : S 42 ≤ 6973633 / 10000000 := by
  have h : S 42 = S 41 + f 41 := S_succ 41
  linarith [s41, t41]

theorem s43 : S 43 ≤ 6973633 / 10000000 := by
  have h : S 43 = S 42 + f 42 := S_succ 42
  linarith [s42, t42]

theorem s44 : S 44 ≤ 7050240 / 10000000 := by
  have h : S 44 = S 43 + f 43 := S_succ 43
  linarith [s43, t43]

theorem s45 : S 45 ≤ 7050240 / 10000000 := by
  have h : S 45 = S 44 + f 44 := S_succ 44
  linarith [s44, t44]

theorem s46 : S 46 ≤ 7050240 / 10000000 := by
  have h : S 46 = S 45 + f 45 := S_succ 45
  linarith [s45, t45]

theorem s47 : S 47 ≤ 7050240 / 10000000 := by
  have h : S 47 = S 46 + f 46 := S_succ 46
  linarith [s46, t46]

theorem s48 : S 48 ≤ 7117349 / 10000000 := by
  have h : S 48 = S 47 + f 47 := S_succ 47
  linarith [s47, t47]

theorem s49 : S 49 ≤ 7117349 / 10000000 := by
  have h : S 49 = S 48 + f 48 := S_succ 48
  linarith [s48, t48]

theorem s50 : S 50 ≤ 7133178 / 10000000 := by
  have h : S 50 = S 49 + f 49 := S_succ 49
  linarith [s49, t49]

theorem s51 : S 51 ≤ 7133178 / 10000000 := by
  have h : S 51 = S 50 + f 50 := S_succ 50
  linarith [s50, t50]

theorem s52 : S 52 ≤ 7133178 / 10000000 := by
  have h : S 52 = S 51 + f 51 := S_succ 51
  linarith [s51, t51]

theorem s53 : S 53 ≤ 7133178 / 10000000 := by
  have h : S 53 = S 52 + f 52 := S_succ 52
  linarith [s52, t52]

theorem s54 : S 54 ≤ 7189422 / 10000000 := by
  have h : S 54 = S 53 + f 53 := S_succ 53
  linarith [s53, t53]

theorem s55 : S 55 ≤ 7189422 / 10000000 := by
  have h : S 55 = S 54 + f 54 := S_succ 54
  linarith [s54, t54]

theorem s56 : S 56 ≤ 7189422 / 10000000 := by
  have h : S 56 = S 55 + f 55 := S_succ 55
  linarith [s55, t55]

theorem s57 : S 57 ≤ 7189422 / 10000000 := by
  have h : S 57 = S 56 + f 56 := S_succ 56
  linarith [s56, t56]

theorem s58 : S 58 ≤ 7189422 / 10000000 := by
  have h : S 58 = S 57 + f 57 := S_succ 57
  linarith [s57, t57]

theorem s59 : S 59 ≤ 7189422 / 10000000 := by
  have h : S 59 = S 58 + f 58 := S_succ 58
  linarith [s58, t58]

theorem s60 : S 60 ≤ 7237188 / 10000000 := by
  have h : S 60 = S 59 + f 59 := S_succ 59
  linarith [s59, t59]

theorem s61 : S 61 ≤ 7237188 / 10000000 := by
  have h : S 61 = S 60 + f 60 := S_succ 60
  linarith [s60, t60]

theorem s62 : S 62 ≤ 7282708 / 10000000 := by
  have h : S 62 = S 61 + f 61 := S_succ 61
  linarith [s61, t61]

theorem s63 : S 63 ≤ 7282708 / 10000000 := by
  have h : S 63 = S 62 + f 62 := S_succ 62
  linarith [s62, t62]

theorem s64 : S 64 ≤ 7282708 / 10000000 := by
  have h : S 64 = S 63 + f 63 := S_succ 63
  linarith [s63, t63]

theorem s65 : S 65 ≤ 7283881 / 10000000 := by
  have h : S 65 = S 64 + f 64 := S_succ 64
  linarith [s64, t64]

theorem s66 : S 66 ≤ 7283881 / 10000000 := by
  have h : S 66 = S 65 + f 65 := S_succ 65
  linarith [s65, t65]

theorem s67 : S 67 ≤ 7283881 / 10000000 := by
  have h : S 67 = S 66 + f 66 := S_succ 66
  linarith [s66, t66]

theorem s68 : S 68 ≤ 7323320 / 10000000 := by
  have h : S 68 = S 67 + f 67 := S_succ 67
  linarith [s67, t67]

theorem s69 : S 69 ≤ 7323320 / 10000000 := by
  have h : S 69 = S 68 + f 68 := S_succ 68
  linarith [s68, t68]

theorem s70 : S 70 ≤ 7323320 / 10000000 := by
  have h : S 70 = S 69 + f 69 := S_succ 69
  linarith [s69, t69]

theorem s71 : S 71 ≤ 7323320 / 10000000 := by
  have h : S 71 = S 70 + f 70 := S_succ 70
  linarith [s70, t70]

theorem s72 : S 72 ≤ 7359442 / 10000000 := by
  have h : S 72 = S 71 + f 71 := S_succ 71
  linarith [s71, t71]

theorem s73 : S 73 ≤ 7359442 / 10000000 := by
  have h : S 73 = S 72 + f 72 := S_succ 72
  linarith [s72, t72]

theorem s74 : S 74 ≤ 7394047 / 10000000 := by
  have h : S 74 = S 73 + f 73 := S_succ 73
  linarith [s73, t73]

theorem s75 : S 75 ≤ 7394047 / 10000000 := by
  have h : S 75 = S 74 + f 74 := S_succ 74
  linarith [s74, t74]

theorem s76 : S 76 ≤ 7394047 / 10000000 := by
  have h : S 76 = S 75 + f 75 := S_succ 75
  linarith [s75, t75]

theorem s77 : S 77 ≤ 7394047 / 10000000 := by
  have h : S 77 = S 76 + f 76 := S_succ 76
  linarith [s76, t76]

theorem s78 : S 78 ≤ 7394047 / 10000000 := by
  have h : S 78 = S 77 + f 77 := S_succ 77
  linarith [s77, t77]

theorem s79 : S 79 ≤ 7394047 / 10000000 := by
  have h : S 79 = S 78 + f 78 := S_succ 78
  linarith [s78, t78]

theorem s80 : S 80 ≤ 7424648 / 10000000 := by
  have h : S 80 = S 79 + f 79 := S_succ 79
  linarith [s79, t79]

theorem s81 : S 81 ≤ 7424648 / 10000000 := by
  have h : S 81 = S 80 + f 80 := S_succ 80
  linarith [s80, t80]

theorem s82 : S 82 ≤ 7426490 / 10000000 := by
  have h : S 82 = S 81 + f 81 := S_succ 81
  linarith [s81, t81]

theorem s83 : S 83 ≤ 7426490 / 10000000 := by
  have h : S 83 = S 82 + f 82 := S_succ 82
  linarith [s82, t82]

theorem s84 : S 84 ≤ 7454904 / 10000000 := by
  have h : S 84 = S 83 + f 83 := S_succ 83
  linarith [s83, t83]

theorem s85 : S 85 ≤ 7454904 / 10000000 := by
  have h : S 85 = S 84 + f 84 := S_succ 84
  linarith [s84, t84]

theorem s86 : S 86 ≤ 7454904 / 10000000 := by
  have h : S 86 = S 85 + f 85 := S_succ 85
  linarith [s85, t85]

theorem s87 : S 87 ≤ 7454904 / 10000000 := by
  have h : S 87 = S 86 + f 86 := S_succ 86
  linarith [s86, t86]

theorem s88 : S 88 ≤ 7454904 / 10000000 := by
  have h : S 88 = S 87 + f 87 := S_succ 87
  linarith [s87, t87]

theorem s89 : S 89 ≤ 7454904 / 10000000 := by
  have h : S 89 = S 88 + f 88 := S_succ 88
  linarith [s88, t88]

theorem s90 : S 90 ≤ 7480347 / 10000000 := by
  have h : S 90 = S 89 + f 89 := S_succ 89
  linarith [s89, t89]

theorem s91 : S 91 ≤ 7480347 / 10000000 := by
  have h : S 91 = S 90 + f 90 := S_succ 90
  linarith [s90, t90]

theorem s92 : S 92 ≤ 7480347 / 10000000 := by
  have h : S 92 = S 91 + f 91 := S_succ 91
  linarith [s91, t91]

theorem s93 : S 93 ≤ 7480347 / 10000000 := by
  have h : S 93 = S 92 + f 92 := S_succ 92
  linarith [s92, t92]

theorem s94 : S 94 ≤ 7480347 / 10000000 := by
  have h : S 94 = S 93 + f 93 := S_succ 93
  linarith [s93, t93]

theorem s95 : S 95 ≤ 7480347 / 10000000 := by
  have h : S 95 = S 94 + f 94 := S_succ 94
  linarith [s94, t94]

theorem s96 : S 96 ≤ 7480347 / 10000000 := by
  have h : S 96 = S 95 + f 95 := S_succ 95
  linarith [s95, t95]

theorem s97 : S 97 ≤ 7480347 / 10000000 := by
  have h : S 97 = S 96 + f 96 := S_succ 96
  linarith [s96, t96]

theorem s98 : S 98 ≤ 7502601 / 10000000 := by
  have h : S 98 = S 97 + f 97 := S_succ 97
  linarith [s97, t97]

theorem s99 : S 99 ≤ 7502601 / 10000000 := by
  have h : S 99 = S 98 + f 98 := S_succ 98
  linarith [s98, t98]

theorem s100 : S 100 ≤ 7502601 / 10000000 := by
  have h : S 100 = S 99 + f 99 := S_succ 99
  linarith [s99, t99]

theorem s101 : S 101 ≤ 7502601 / 10000000 := by
  have h : S 101 = S 100 + f 100 := S_succ 100
  linarith [s100, t100]

theorem s102 : S 102 ≤ 7523518 / 10000000 := by
  have h : S 102 = S 101 + f 101 := S_succ 101
  linarith [s101, t101]

theorem s103 : S 103 ≤ 7523518 / 10000000 := by
  have h : S 103 = S 102 + f 102 := S_succ 102
  linarith [s102, t102]

theorem s104 : S 104 ≤ 7543772 / 10000000 := by
  have h : S 104 = S 103 + f 103 := S_succ 103
  linarith [s103, t103]

theorem s105 : S 105 ≤ 7543772 / 10000000 := by
  have h : S 105 = S 104 + f 104 := S_succ 104
  linarith [s104, t104]

theorem s106 : S 106 ≤ 7543772 / 10000000 := by
  have h : S 106 = S 105 + f 105 := S_succ 105
  linarith [s105, t105]

theorem s107 : S 107 ≤ 7543772 / 10000000 := by
  have h : S 107 = S 106 + f 106 := S_succ 106
  linarith [s106, t106]

theorem s108 : S 108 ≤ 7562848 / 10000000 := by
  have h : S 108 = S 107 + f 107 := S_succ 107
  linarith [s107, t107]

theorem s109 : S 109 ≤ 7562848 / 10000000 := by
  have h : S 109 = S 108 + f 108 := S_succ 108
  linarith [s108, t108]

theorem s110 : S 110 ≤ 7581402 / 10000000 := by
  have h : S 110 = S 109 + f 109 := S_succ 109
  linarith [s109, t109]

theorem s111 : S 111 ≤ 7581402 / 10000000 := by
  have h : S 111 = S 110 + f 110 := S_succ 110
  linarith [s110, t110]

theorem s112 : S 112 ≤ 7581402 / 10000000 := by
  have h : S 112 = S 111 + f 111 := S_succ 111
  linarith [s111, t111]

theorem s113 : S 113 ≤ 7581402 / 10000000 := by
  have h : S 113 = S 112 + f 112 := S_succ 112
  linarith [s112, t112]

theorem s114 : S 114 ≤ 7598905 / 10000000 := by
  have h : S 114 = S 113 + f 113 := S_succ 113
  linarith [s113, t113]

theorem s115 : S 115 ≤ 7598905 / 10000000 := by
  have h : S 115 = S 114 + f 114 := S_succ 114
  linarith [s114, t114]

theorem s116 : S 116 ≤ 7598905 / 10000000 := by
  have h : S 116 = S 115 + f 115 := S_succ 115
  linarith [s115, t115]

theorem s117 : S 117 ≤ 7598905 / 10000000 := by
  have h : S 117 = S 116 + f 116 := S_succ 116
  linarith [s116, t116]

theorem s118 : S 118 ≤ 7598905 / 10000000 := by
  have h : S 118 = S 117 + f 117 := S_succ 117
  linarith [s117, t117]

theorem s119 : S 119 ≤ 7598905 / 10000000 := by
  have h : S 119 = S 118 + f 118 := S_succ 118
  linarith [s118, t118]

theorem s120 : S 120 ≤ 7598905 / 10000000 := by
  have h : S 120 = S 119 + f 119 := S_succ 119
  linarith [s119, t119]

theorem s121 : S 121 ≤ 7598905 / 10000000 := by
  have h : S 121 = S 120 + f 120 := S_succ 120
  linarith [s120, t120]

theorem s122 : S 122 ≤ 7602836 / 10000000 := by
  have h : S 122 = S 121 + f 121 := S_succ 121
  linarith [s121, t121]

theorem s123 : S 123 ≤ 7602836 / 10000000 := by
  have h : S 123 = S 122 + f 122 := S_succ 122
  linarith [s122, t122]

theorem s124 : S 124 ≤ 7602836 / 10000000 := by
  have h : S 124 = S 123 + f 123 := S_succ 123
  linarith [s123, t123]

theorem s125 : S 125 ≤ 7602836 / 10000000 := by
  have h : S 125 = S 124 + f 124 := S_succ 124
  linarith [s124, t124]

theorem s126 : S 126 ≤ 7604503 / 10000000 := by
  have h : S 126 = S 125 + f 125 := S_succ 125
  linarith [s125, t125]

theorem s127 : S 127 ≤ 7604503 / 10000000 := by
  have h : S 127 = S 126 + f 126 := S_succ 126
  linarith [s126, t126]

theorem s128 : S 128 ≤ 7619067 / 10000000 := by
  have h : S 128 = S 127 + f 127 := S_succ 127
  linarith [s127, t127]

theorem s129 : S 129 ≤ 7619361 / 10000000 := by
  have h : S 129 = S 128 + f 128 := S_succ 128
  linarith [s128, t128]

theorem s130 : S 130 ≤ 7619361 / 10000000 := by
  have h : S 130 = S 129 + f 129 := S_succ 129
  linarith [s129, t129]

theorem s131 : S 131 ≤ 7619361 / 10000000 := by
  have h : S 131 = S 130 + f 130 := S_succ 130
  linarith [s130, t130]

theorem s132 : S 132 ≤ 7633233 / 10000000 := by
  have h : S 132 = S 131 + f 131 := S_succ 131
  linarith [s131, t131]

theorem s133 : S 133 ≤ 7633233 / 10000000 := by
  have h : S 133 = S 132 + f 132 := S_succ 132
  linarith [s132, t132]

theorem s134 : S 134 ≤ 7633233 / 10000000 := by
  have h : S 134 = S 133 + f 133 := S_succ 133
  linarith [s133, t133]

theorem s135 : S 135 ≤ 7633233 / 10000000 := by
  have h : S 135 = S 134 + f 134 := S_succ 134
  linarith [s134, t134]

theorem s136 : S 136 ≤ 7633233 / 10000000 := by
  have h : S 136 = S 135 + f 135 := S_succ 135
  linarith [s135, t135]

theorem s137 : S 137 ≤ 7633233 / 10000000 := by
  have h : S 137 = S 136 + f 136 := S_succ 136
  linarith [s136, t136]

theorem s138 : S 138 ≤ 7646143 / 10000000 := by
  have h : S 138 = S 137 + f 137 := S_succ 137
  linarith [s137, t137]

theorem s139 : S 139 ≤ 7646143 / 10000000 := by
  have h : S 139 = S 138 + f 138 := S_succ 138
  linarith [s138, t138]

theorem s140 : S 140 ≤ 7658767 / 10000000 := by
  have h : S 140 = S 139 + f 139 := S_succ 139
  linarith [s139, t139]

theorem s141 : S 141 ≤ 7658767 / 10000000 := by
  have h : S 141 = S 140 + f 140 := S_succ 140
  linarith [s140, t140]

theorem s142 : S 142 ≤ 7658767 / 10000000 := by
  have h : S 142 = S 141 + f 141 := S_succ 141
  linarith [s141, t141]

theorem s143 : S 143 ≤ 7658767 / 10000000 := by
  have h : S 143 = S 142 + f 142 := S_succ 142
  linarith [s142, t142]

theorem s144 : S 144 ≤ 7658767 / 10000000 := by
  have h : S 144 = S 143 + f 143 := S_succ 143
  linarith [s143, t143]

theorem s145 : S 145 ≤ 7658767 / 10000000 := by
  have h : S 145 = S 144 + f 144 := S_succ 144
  linarith [s144, t144]

theorem s146 : S 146 ≤ 7658767 / 10000000 := by
  have h : S 146 = S 145 + f 145 := S_succ 145
  linarith [s145, t145]

theorem s147 : S 147 ≤ 7658767 / 10000000 := by
  have h : S 147 = S 146 + f 146 := S_succ 146
  linarith [s146, t146]

theorem s148 : S 148 ≤ 7658767 / 10000000 := by
  have h : S 148 = S 147 + f 147 := S_succ 147
  linarith [s147, t147]

theorem s149 : S 149 ≤ 7658767 / 10000000 := by
  have h : S 149 = S 148 + f 148 := S_succ 148
  linarith [s148, t148]

theorem s150 : S 150 ≤ 7670069 / 10000000 := by
  have h : S 150 = S 149 + f 149 := S_succ 149
  linarith [s149, t149]

theorem s151 : S 151 ≤ 7670069 / 10000000 := by
  have h : S 151 = S 150 + f 150 := S_succ 150
  linarith [s150, t150]

theorem s152 : S 152 ≤ 7681121 / 10000000 := by
  have h : S 152 = S 151 + f 151 := S_succ 151
  linarith [s151, t151]

theorem s153 : S 153 ≤ 7681121 / 10000000 := by
  have h : S 153 = S 152 + f 152 := S_succ 152
  linarith [s152, t152]

theorem s154 : S 154 ≤ 7681121 / 10000000 := by
  have h : S 154 = S 153 + f 153 := S_succ 153
  linarith [s153, t153]

theorem s155 : S 155 ≤ 7681121 / 10000000 := by
  have h : S 155 = S 154 + f 154 := S_succ 154
  linarith [s154, t154]

theorem s156 : S 156 ≤ 7681121 / 10000000 := by
  have h : S 156 = S 155 + f 155 := S_succ 155
  linarith [s155, t155]

theorem s157 : S 157 ≤ 7681121 / 10000000 := by
  have h : S 157 = S 156 + f 156 := S_succ 156
  linarith [s156, t156]

theorem s158 : S 158 ≤ 7691500 / 10000000 := by
  have h : S 158 = S 157 + f 157 := S_succ 157
  linarith [s157, t157]

theorem s159 : S 159 ≤ 7691500 / 10000000 := by
  have h : S 159 = S 158 + f 158 := S_succ 158
  linarith [s158, t158]

theorem s160 : S 160 ≤ 7691500 / 10000000 := by
  have h : S 160 = S 159 + f 159 := S_succ 159
  linarith [s159, t159]

theorem s161 : S 161 ≤ 7691500 / 10000000 := by
  have h : S 161 = S 160 + f 160 := S_succ 160
  linarith [s160, t160]

theorem s162 : S 162 ≤ 7691500 / 10000000 := by
  have h : S 162 = S 161 + f 161 := S_succ 161
  linarith [s161, t161]

theorem s163 : S 163 ≤ 7691500 / 10000000 := by
  have h : S 163 = S 162 + f 162 := S_succ 162
  linarith [s162, t162]

theorem s164 : S 164 ≤ 7701274 / 10000000 := by
  have h : S 164 = S 163 + f 163 := S_succ 163
  linarith [s163, t163]

theorem s165 : S 165 ≤ 7701274 / 10000000 := by
  have h : S 165 = S 164 + f 164 := S_succ 164
  linarith [s164, t164]

theorem s166 : S 166 ≤ 7701274 / 10000000 := by
  have h : S 166 = S 165 + f 165 := S_succ 165
  linarith [s165, t165]

theorem s167 : S 167 ≤ 7701274 / 10000000 := by
  have h : S 167 = S 166 + f 166 := S_succ 166
  linarith [s166, t166]

theorem s168 : S 168 ≤ 7710684 / 10000000 := by
  have h : S 168 = S 167 + f 167 := S_succ 167
  linarith [s167, t167]

theorem s169 : S 169 ≤ 7710684 / 10000000 := by
  have h : S 169 = S 168 + f 168 := S_succ 168
  linarith [s168, t168]

theorem s170 : S 170 ≤ 7712991 / 10000000 := by
  have h : S 170 = S 169 + f 169 := S_succ 169
  linarith [s169, t169]

theorem s171 : S 171 ≤ 7712991 / 10000000 := by
  have h : S 171 = S 170 + f 170 := S_succ 170
  linarith [s170, t170]

theorem s172 : S 172 ≤ 7712991 / 10000000 := by
  have h : S 172 = S 171 + f 171 := S_succ 171
  linarith [s171, t171]

theorem s173 : S 173 ≤ 7712991 / 10000000 := by
  have h : S 173 = S 172 + f 172 := S_succ 172
  linarith [s172, t172]

theorem s174 : S 174 ≤ 7721871 / 10000000 := by
  have h : S 174 = S 173 + f 173 := S_succ 173
  linarith [s173, t173]

theorem s175 : S 175 ≤ 7721871 / 10000000 := by
  have h : S 175 = S 174 + f 174 := S_succ 174
  linarith [s174, t174]

theorem s176 : S 176 ≤ 7721871 / 10000000 := by
  have h : S 176 = S 175 + f 175 := S_succ 175
  linarith [s175, t175]

theorem s177 : S 177 ≤ 7721871 / 10000000 := by
  have h : S 177 = S 176 + f 176 := S_succ 176
  linarith [s176, t176]

theorem s178 : S 178 ≤ 7721871 / 10000000 := by
  have h : S 178 = S 177 + f 177 := S_succ 177
  linarith [s177, t177]

theorem s179 : S 179 ≤ 7721871 / 10000000 := by
  have h : S 179 = S 178 + f 178 := S_succ 178
  linarith [s178, t178]

theorem s180 : S 180 ≤ 7730271 / 10000000 := by
  have h : S 180 = S 179 + f 179 := S_succ 179
  linarith [s179, t179]

theorem s181 : S 181 ≤ 7730271 / 10000000 := by
  have h : S 181 = S 180 + f 180 := S_succ 180
  linarith [s180, t180]

theorem s182 : S 182 ≤ 7738521 / 10000000 := by
  have h : S 182 = S 181 + f 181 := S_succ 181
  linarith [s181, t181]

theorem s183 : S 183 ≤ 7738521 / 10000000 := by
  have h : S 183 = S 182 + f 182 := S_succ 182
  linarith [s182, t182]

theorem s184 : S 184 ≤ 7738521 / 10000000 := by
  have h : S 184 = S 183 + f 183 := S_succ 183
  linarith [s183, t183]

theorem s185 : S 185 ≤ 7738521 / 10000000 := by
  have h : S 185 = S 184 + f 184 := S_succ 184
  linarith [s184, t184]

theorem s186 : S 186 ≤ 7738521 / 10000000 := by
  have h : S 186 = S 185 + f 185 := S_succ 185
  linarith [s185, t185]

theorem s187 : S 187 ≤ 7738521 / 10000000 := by
  have h : S 187 = S 186 + f 186 := S_succ 186
  linarith [s186, t186]

theorem s188 : S 188 ≤ 7738521 / 10000000 := by
  have h : S 188 = S 187 + f 187 := S_succ 187
  linarith [s187, t187]

theorem s189 : S 189 ≤ 7738521 / 10000000 := by
  have h : S 189 = S 188 + f 188 := S_succ 188
  linarith [s188, t188]

theorem s190 : S 190 ≤ 7738521 / 10000000 := by
  have h : S 190 = S 189 + f 189 := S_succ 189
  linarith [s189, t189]

theorem s191 : S 191 ≤ 7738521 / 10000000 := by
  have h : S 191 = S 190 + f 190 := S_succ 190
  linarith [s190, t190]

theorem s192 : S 192 ≤ 7746085 / 10000000 := by
  have h : S 192 = S 191 + f 191 := S_succ 191
  linarith [s191, t191]

theorem s193 : S 193 ≤ 7746085 / 10000000 := by
  have h : S 193 = S 192 + f 192 := S_succ 192
  linarith [s192, t192]

theorem s194 : S 194 ≤ 7753523 / 10000000 := by
  have h : S 194 = S 193 + f 193 := S_succ 193
  linarith [s193, t193]

theorem s195 : S 195 ≤ 7753523 / 10000000 := by
  have h : S 195 = S 194 + f 194 := S_succ 194
  linarith [s194, t194]

theorem s196 : S 196 ≤ 7753523 / 10000000 := by
  have h : S 196 = S 195 + f 195 := S_succ 195
  linarith [s195, t195]

theorem s197 : S 197 ≤ 7753523 / 10000000 := by
  have h : S 197 = S 196 + f 196 := S_succ 196
  linarith [s196, t196]

theorem s198 : S 198 ≤ 7760721 / 10000000 := by
  have h : S 198 = S 197 + f 197 := S_succ 197
  linarith [s197, t197]

theorem s199 : S 199 ≤ 7760721 / 10000000 := by
  have h : S 199 = S 198 + f 198 := S_succ 198
  linarith [s198, t198]

theorem s200 : S 200 ≤ 7767804 / 10000000 := by
  have h : S 200 = S 199 + f 199 := S_succ 199
  linarith [s199, t199]

theorem s201 : S 201 ≤ 7767804 / 10000000 := by
  have h : S 201 = S 200 + f 200 := S_succ 200
  linarith [s200, t200]

theorem s202 : S 202 ≤ 7767804 / 10000000 := by
  have h : S 202 = S 201 + f 201 := S_succ 201
  linarith [s201, t201]

theorem s203 : S 203 ≤ 7767804 / 10000000 := by
  have h : S 203 = S 202 + f 202 := S_succ 202
  linarith [s202, t202]

theorem s204 : S 204 ≤ 7767804 / 10000000 := by
  have h : S 204 = S 203 + f 203 := S_succ 203
  linarith [s203, t203]

theorem s205 : S 205 ≤ 7767804 / 10000000 := by
  have h : S 205 = S 204 + f 204 := S_succ 204
  linarith [s204, t204]

theorem s206 : S 206 ≤ 7767804 / 10000000 := by
  have h : S 206 = S 205 + f 205 := S_succ 205
  linarith [s205, t205]

theorem s207 : S 207 ≤ 7767804 / 10000000 := by
  have h : S 207 = S 206 + f 206 := S_succ 206
  linarith [s206, t206]

theorem s208 : S 208 ≤ 7767804 / 10000000 := by
  have h : S 208 = S 207 + f 207 := S_succ 207
  linarith [s207, t207]

theorem s209 : S 209 ≤ 7767804 / 10000000 := by
  have h : S 209 = S 208 + f 208 := S_succ 208
  linarith [s208, t208]

theorem s210 : S 210 ≤ 7767804 / 10000000 := by
  have h : S 210 = S 209 + f 209 := S_succ 209
  linarith [s209, t209]

theorem s211 : S 211 ≤ 7767804 / 10000000 := by
  have h : S 211 = S 210 + f 210 := S_succ 210
  linarith [s210, t210]

theorem s212 : S 212 ≤ 7774247 / 10000000 := by
  have h : S 212 = S 211 + f 211 := S_succ 211
  linarith [s211, t211]

theorem s213 : S 213 ≤ 7774247 / 10000000 := by
  have h : S 213 = S 212 + f 212 := S_succ 212
  linarith [s212, t212]

theorem s214 : S 214 ≤ 7774247 / 10000000 := by
  have h : S 214 = S 213 + f 213 := S_succ 213
  linarith [s213, t213]

theorem s215 : S 215 ≤ 7774247 / 10000000 := by
  have h : S 215 = S 214 + f 214 := S_succ 214
  linarith [s214, t214]

theorem s216 : S 216 ≤ 7774247 / 10000000 := by
  have h : S 216 = S 215 + f 215 := S_succ 215
  linarith [s215, t215]

theorem s217 : S 217 ≤ 7774247 / 10000000 := by
  have h : S 217 = S 216 + f 216 := S_succ 216
  linarith [s216, t216]

theorem s218 : S 218 ≤ 7774247 / 10000000 := by
  have h : S 218 = S 217 + f 217 := S_succ 217
  linarith [s217, t217]

theorem s219 : S 219 ≤ 7774247 / 10000000 := by
  have h : S 219 = S 218 + f 218 := S_succ 218
  linarith [s218, t218]

theorem s220 : S 220 ≤ 7774247 / 10000000 := by
  have h : S 220 = S 219 + f 219 := S_succ 219
  linarith [s219, t219]

theorem s221 : S 221 ≤ 7774247 / 10000000 := by
  have h : S 221 = S 220 + f 220 := S_succ 220
  linarith [s220, t220]

theorem s222 : S 222 ≤ 7774247 / 10000000 := by
  have h : S 222 = S 221 + f 221 := S_succ 221
  linarith [s221, t221]

theorem s223 : S 223 ≤ 7774247 / 10000000 := by
  have h : S 223 = S 222 + f 222 := S_succ 222
  linarith [s222, t222]

theorem s224 : S 224 ≤ 7780133 / 10000000 := by
  have h : S 224 = S 223 + f 223 := S_succ 223
  linarith [s223, t223]

theorem s225 : S 225 ≤ 7780133 / 10000000 := by
  have h : S 225 = S 224 + f 224 := S_succ 224
  linarith [s224, t224]

theorem s226 : S 226 ≤ 7780133 / 10000000 := by
  have h : S 226 = S 225 + f 225 := S_succ 225
  linarith [s225, t225]

theorem s227 : S 227 ≤ 7780133 / 10000000 := by
  have h : S 227 = S 226 + f 226 := S_succ 226
  linarith [s226, t226]

theorem s228 : S 228 ≤ 7785847 / 10000000 := by
  have h : S 228 = S 227 + f 227 := S_succ 227
  linarith [s227, t227]

theorem s229 : S 229 ≤ 7785847 / 10000000 := by
  have h : S 229 = S 228 + f 228 := S_succ 228
  linarith [s228, t228]

theorem s230 : S 230 ≤ 7791484 / 10000000 := by
  have h : S 230 = S 229 + f 229 := S_succ 229
  linarith [s229, t229]

theorem s231 : S 231 ≤ 7791484 / 10000000 := by
  have h : S 231 = S 230 + f 230 := S_succ 230
  linarith [s230, t230]

theorem s232 : S 232 ≤ 7791484 / 10000000 := by
  have h : S 232 = S 231 + f 231 := S_succ 231
  linarith [s231, t231]

theorem s233 : S 233 ≤ 7791484 / 10000000 := by
  have h : S 233 = S 232 + f 232 := S_succ 232
  linarith [s232, t232]

theorem s234 : S 234 ≤ 7796962 / 10000000 := by
  have h : S 234 = S 233 + f 233 := S_succ 233
  linarith [s233, t233]

theorem s235 : S 235 ≤ 7796962 / 10000000 := by
  have h : S 235 = S 234 + f 234 := S_succ 234
  linarith [s234, t234]

theorem s236 : S 236 ≤ 7796962 / 10000000 := by
  have h : S 236 = S 235 + f 235 := S_succ 235
  linarith [s235, t235]

theorem s237 : S 237 ≤ 7796962 / 10000000 := by
  have h : S 237 = S 236 + f 236 := S_succ 236
  linarith [s236, t236]

theorem s238 : S 238 ≤ 7796962 / 10000000 := by
  have h : S 238 = S 237 + f 237 := S_succ 237
  linarith [s237, t237]

theorem s239 : S 239 ≤ 7796962 / 10000000 := by
  have h : S 239 = S 238 + f 238 := S_succ 238
  linarith [s238, t238]

theorem s240 : S 240 ≤ 7802220 / 10000000 := by
  have h : S 240 = S 239 + f 239 := S_succ 239
  linarith [s239, t239]

theorem s241 : S 241 ≤ 7802220 / 10000000 := by
  have h : S 241 = S 240 + f 240 := S_succ 240
  linarith [s240, t240]

theorem s242 : S 242 ≤ 7807402 / 10000000 := by
  have h : S 242 = S 241 + f 241 := S_succ 241
  linarith [s241, t241]

theorem s243 : S 243 ≤ 7807402 / 10000000 := by
  have h : S 243 = S 242 + f 242 := S_succ 242
  linarith [s242, t242]

theorem s244 : S 244 ≤ 7807607 / 10000000 := by
  have h : S 244 = S 243 + f 243 := S_succ 243
  linarith [s243, t243]

theorem s245 : S 245 ≤ 7807607 / 10000000 := by
  have h : S 245 = S 244 + f 244 := S_succ 244
  linarith [s244, t244]

theorem s246 : S 246 ≤ 7807607 / 10000000 := by
  have h : S 246 = S 245 + f 245 := S_succ 245
  linarith [s245, t245]

theorem s247 : S 247 ≤ 7807607 / 10000000 := by
  have h : S 247 = S 246 + f 246 := S_succ 246
  linarith [s246, t246]

theorem s248 : S 248 ≤ 7807607 / 10000000 := by
  have h : S 248 = S 247 + f 247 := S_succ 247
  linarith [s247, t247]

theorem s249 : S 249 ≤ 7807607 / 10000000 := by
  have h : S 249 = S 248 + f 248 := S_succ 248
  linarith [s248, t248]

theorem s250 : S 250 ≤ 7807607 / 10000000 := by
  have h : S 250 = S 249 + f 249 := S_succ 249
  linarith [s249, t249]

theorem s251 : S 251 ≤ 7807607 / 10000000 := by
  have h : S 251 = S 250 + f 250 := S_succ 250
  linarith [s250, t250]

theorem s252 : S 252 ≤ 7812460 / 10000000 := by
  have h : S 252 = S 251 + f 251 := S_succ 251
  linarith [s251, t251]

theorem s253 : S 253 ≤ 7812460 / 10000000 := by
  have h : S 253 = S 252 + f 252 := S_succ 252
  linarith [s252, t252]

theorem s254 : S 254 ≤ 7812460 / 10000000 := by
  have h : S 254 = S 253 + f 253 := S_succ 253
  linarith [s253, t253]

theorem s255 : S 255 ≤ 7812460 / 10000000 := by
  have h : S 255 = S 254 + f 254 := S_succ 254
  linarith [s254, t254]

theorem s256 : S 256 ≤ 7812460 / 10000000 := by
  have h : S 256 = S 255 + f 255 := S_succ 255
  linarith [s255, t255]

theorem s257 : S 257 ≤ 7812534 / 10000000 := by
  have h : S 257 = S 256 + f 256 := S_succ 256
  linarith [s256, t256]

theorem s258 : S 258 ≤ 7817199 / 10000000 := by
  have h : S 258 = S 257 + f 257 := S_succ 257
  linarith [s257, t257]

theorem s259 : S 259 ≤ 7817199 / 10000000 := by
  have h : S 259 = S 258 + f 258 := S_succ 258
  linarith [s258, t258]

theorem s260 : S 260 ≤ 7817199 / 10000000 := by
  have h : S 260 = S 259 + f 259 := S_succ 259
  linarith [s259, t259]

theorem s261 : S 261 ≤ 7817199 / 10000000 := by
  have h : S 261 = S 260 + f 260 := S_succ 260
  linarith [s260, t260]

theorem s262 : S 262 ≤ 7817199 / 10000000 := by
  have h : S 262 = S 261 + f 261 := S_succ 261
  linarith [s261, t261]

theorem s263 : S 263 ≤ 7817199 / 10000000 := by
  have h : S 263 = S 262 + f 262 := S_succ 262
  linarith [s262, t262]

theorem s264 : S 264 ≤ 7821689 / 10000000 := by
  have h : S 264 = S 263 + f 263 := S_succ 263
  linarith [s263, t263]

theorem s265 : S 265 ≤ 7821689 / 10000000 := by
  have h : S 265 = S 264 + f 264 := S_succ 264
  linarith [s264, t264]

theorem s266 : S 266 ≤ 7821689 / 10000000 := by
  have h : S 266 = S 265 + f 265 := S_succ 265
  linarith [s265, t265]

theorem s267 : S 267 ≤ 7821689 / 10000000 := by
  have h : S 267 = S 266 + f 266 := S_succ 266
  linarith [s266, t266]

theorem s268 : S 268 ≤ 7821689 / 10000000 := by
  have h : S 268 = S 267 + f 267 := S_succ 267
  linarith [s267, t267]

theorem s269 : S 269 ≤ 7821689 / 10000000 := by
  have h : S 269 = S 268 + f 268 := S_succ 268
  linarith [s268, t268]

theorem s270 : S 270 ≤ 7826022 / 10000000 := by
  have h : S 270 = S 269 + f 269 := S_succ 269
  linarith [s269, t269]

theorem s271 : S 271 ≤ 7826022 / 10000000 := by
  have h : S 271 = S 270 + f 270 := S_succ 270
  linarith [s270, t270]

theorem s272 : S 272 ≤ 7830300 / 10000000 := by
  have h : S 272 = S 271 + f 271 := S_succ 271
  linarith [s271, t271]

theorem s273 : S 273 ≤ 7830300 / 10000000 := by
  have h : S 273 = S 272 + f 272 := S_succ 272
  linarith [s272, t272]

theorem s274 : S 274 ≤ 7830300 / 10000000 := by
  have h : S 274 = S 273 + f 273 := S_succ 273
  linarith [s273, t273]

theorem s275 : S 275 ≤ 7830300 / 10000000 := by
  have h : S 275 = S 274 + f 274 := S_succ 274
  linarith [s274, t274]

theorem s276 : S 276 ≤ 7830300 / 10000000 := by
  have h : S 276 = S 275 + f 275 := S_succ 275
  linarith [s275, t275]

theorem s277 : S 277 ≤ 7830300 / 10000000 := by
  have h : S 277 = S 276 + f 276 := S_succ 276
  linarith [s276, t276]

theorem s278 : S 278 ≤ 7834426 / 10000000 := by
  have h : S 278 = S 277 + f 277 := S_succ 277
  linarith [s277, t277]

theorem s279 : S 279 ≤ 7834426 / 10000000 := by
  have h : S 279 = S 278 + f 278 := S_succ 278
  linarith [s278, t278]

theorem s280 : S 280 ≤ 7834426 / 10000000 := by
  have h : S 280 = S 279 + f 279 := S_succ 279
  linarith [s279, t279]

theorem s281 : S 281 ≤ 7834426 / 10000000 := by
  have h : S 281 = S 280 + f 280 := S_succ 280
  linarith [s280, t280]

theorem s282 : S 282 ≤ 7838459 / 10000000 := by
  have h : S 282 = S 281 + f 281 := S_succ 281
  linarith [s281, t281]

theorem s283 : S 283 ≤ 7838459 / 10000000 := by
  have h : S 283 = S 282 + f 282 := S_succ 282
  linarith [s282, t282]

theorem s284 : S 284 ≤ 7842443 / 10000000 := by
  have h : S 284 = S 283 + f 283 := S_succ 283
  linarith [s283, t283]

theorem s285 : S 285 ≤ 7842443 / 10000000 := by
  have h : S 285 = S 284 + f 284 := S_succ 284
  linarith [s284, t284]

theorem s286 : S 286 ≤ 7842443 / 10000000 := by
  have h : S 286 = S 285 + f 285 := S_succ 285
  linarith [s285, t285]

theorem s287 : S 287 ≤ 7842443 / 10000000 := by
  have h : S 287 = S 286 + f 286 := S_succ 286
  linarith [s286, t286]

theorem s288 : S 288 ≤ 7842443 / 10000000 := by
  have h : S 288 = S 287 + f 287 := S_succ 287
  linarith [s287, t287]

theorem s289 : S 289 ≤ 7842443 / 10000000 := by
  have h : S 289 = S 288 + f 288 := S_succ 288
  linarith [s288, t288]

theorem s290 : S 290 ≤ 7843408 / 10000000 := by
  have h : S 290 = S 289 + f 289 := S_succ 289
  linarith [s289, t289]

theorem s291 : S 291 ≤ 7843408 / 10000000 := by
  have h : S 291 = S 290 + f 290 := S_succ 290
  linarith [s290, t290]

theorem s292 : S 292 ≤ 7843408 / 10000000 := by
  have h : S 292 = S 291 + f 291 := S_succ 291
  linarith [s291, t291]

theorem s293 : S 293 ≤ 7843408 / 10000000 := by
  have h : S 293 = S 292 + f 292 := S_succ 292
  linarith [s292, t292]

theorem s294 : S 294 ≤ 7847167 / 10000000 := by
  have h : S 294 = S 293 + f 293 := S_succ 293
  linarith [s293, t293]

theorem s295 : S 295 ≤ 7847167 / 10000000 := by
  have h : S 295 = S 294 + f 294 := S_succ 294
  linarith [s294, t294]

theorem s296 : S 296 ≤ 7847167 / 10000000 := by
  have h : S 296 = S 295 + f 295 := S_succ 295
  linarith [s295, t295]

theorem s297 : S 297 ≤ 7847167 / 10000000 := by
  have h : S 297 = S 296 + f 296 := S_succ 296
  linarith [s296, t296]

theorem s298 : S 298 ≤ 7847167 / 10000000 := by
  have h : S 298 = S 297 + f 297 := S_succ 297
  linarith [s297, t297]

theorem s299 : S 299 ≤ 7847167 / 10000000 := by
  have h : S 299 = S 298 + f 298 := S_succ 298
  linarith [s298, t298]

theorem s300 : S 300 ≤ 7847167 / 10000000 := by
  have h : S 300 = S 299 + f 299 := S_succ 299
  linarith [s299, t299]

theorem s301 : S 301 ≤ 7847167 / 10000000 := by
  have h : S 301 = S 300 + f 300 := S_succ 300
  linarith [s300, t300]

/-! ### The tail `n > 300` by summation by parts -/

/-- `g(x) = log x / x²` -/
noncomputable def g (x : ℝ) : ℝ := Real.log x / x ^ 2

/-- `G(x) = (log x + 1)/x`, so `g(x+1) ≤ G(x) - G(x+1)` -/
noncomputable def G (x : ℝ) : ℝ := (Real.log x + 1) / x

theorem log_le_quarter {x : ℝ} (hx : 0 < x) : Real.log x ≤ 1.4716 * √(√x) := by
  set y := √(√x)
  have hy : 0 < y := by positivity
  have hly : Real.log y = Real.log x / 4 := by
    simp only [y]; rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hx.le]; ring
  have he := Real.exp_one_gt_d9
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have h1 := Real.log_le_sub_one_of_pos (div_pos hy he0)
  rw [Real.log_div hy.ne' he0.ne', Real.log_exp] at h1
  have h2 : y / Real.exp 1 ≤ 0.3679 * y := by
    rw [div_le_iff₀ he0]; nlinarith
  linarith

theorem psi_le_19 (N : ℕ) (hN : 300 ≤ N) : ψ (N : ℝ) ≤ 1.9 * N := by
  have h := LeanLab.ChebyshevExplicit.psi_le_11062 N
  have hN' : (300 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : (0 : ℝ) < N := by linarith
  have hl := log_le_quarter hx
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  set s := √(N : ℝ)
  have hs2 : s ^ 2 = N := Real.sq_sqrt hx.le
  have hs : 17.32 ≤ s := Real.le_sqrt_of_sq_le (by nlinarith)
  have hy2 : √s ^ 2 = s := Real.sq_sqrt (by positivity)
  have hy0 : 0 ≤ √s := Real.sqrt_nonneg _
  have hlog2 : Real.log N ^ 2 ≤ 1.4716 ^ 2 * s := by
    have := mul_le_mul hl hl hl0 (by positivity)
    nlinarith
  nlinarith

theorem g_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ g x := by
  unfold g; have := Real.log_nonneg hx; positivity

theorem log_succ_le {x : ℝ} (hx : 0 < x) : Real.log (x + 1) ≤ Real.log x + 1 / x := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
  rw [Real.log_div (by positivity) hx.ne'] at h
  have : (x + 1) / x - 1 = 1 / x := by field_simp; ring
  linarith

theorem g_anti {x : ℝ} (hx : 3 ≤ x) : g (x + 1) ≤ g x := by
  have hx0 : 0 < x := by linarith
  have hl1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; have := Real.exp_one_lt_d9; linarith
  have h := log_succ_le hx0
  unfold g
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : Real.log (x + 1) * x ^ 2 ≤ (Real.log x + 1 / x) * x ^ 2 :=
    mul_le_mul_of_nonneg_right h (by positivity)
  have h2 : (Real.log x + 1 / x) * x ^ 2 = Real.log x * x ^ 2 + x := by field_simp
  nlinarith

theorem g_tel {x : ℝ} (hx : 8 ≤ x) : g (x + 1) ≤ G x - G (x + 1) := by
  have hx0 : 0 < x := by linarith
  set L := Real.log (x + 1)
  have hL : 2 ≤ L := by
    simp only [L]; rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [e]; nlinarith [Real.exp_pos 1]
  have h := log_succ_le hx0
  have key : G x - G (x + 1) - g (x + 1) =
      (Real.log x - (L - 1 / x)) / x + (L * x - (x + 1)) / (x ^ 2 * (x + 1) ^ 2) := by
    simp only [G, g, L]; field_simp; ring
  have h1 : 0 ≤ (Real.log x - (L - 1 / x)) / x := div_nonneg (by linarith) hx0.le
  have h2 : 0 ≤ (L * x - (x + 1)) / (x ^ 2 * (x + 1) ^ 2) :=
    div_nonneg (by nlinarith) (by positivity)
  linarith

theorem psi_succ (N : ℕ) : ψ ((N + 1 : ℕ) : ℝ) = ψ (N : ℝ) + Λ (N + 1) := by
  unfold Chebyshev.psi
  rw [Nat.floor_natCast, Nat.floor_natCast, Finset.sum_Ioc_succ_top (by omega)]

/-- the weighted tail -/
noncomputable def Tl (N : ℕ) : ℝ := ∑ n ∈ Finset.Ico 301 (N + 1), Λ n * g n

theorem tail_ind (N : ℕ) (hN : 300 ≤ N) :
    Tl N + (1.9 * N - ψ (N : ℝ)) * g N ≤ 1.9 * (300 * g 300 + G 300 - G N) := by
  induction N, hN using Nat.le_induction with
  | base =>
    have : Tl 300 = 0 := by simp [Tl]
    rw [this]
    have := psi_nonneg ((300 : ℕ) : ℝ)
    have := g_nonneg (show (1 : ℝ) ≤ 300 by norm_num)
    push_cast at *
    nlinarith
  | succ N hN ih =>
    have hT : Tl (N + 1) = Tl N + Λ (N + 1) * g ((N + 1 : ℕ) : ℝ) := by
      unfold Tl; rw [Finset.sum_Ico_succ_top (by omega)]
    have hN' : (300 : ℝ) ≤ N := by exact_mod_cast hN
    have hpsi := psi_succ N
    have hb := psi_le_19 N hN
    have ha := g_anti (x := (N : ℝ)) (by linarith)
    have ht := g_tel (x := (N : ℝ)) (by linarith)
    rw [hT, hpsi]
    push_cast at *
    nlinarith [mul_le_mul_of_nonneg_left (sub_nonneg.2 ha) (sub_nonneg.2 hb)]

theorem G_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ G x := by
  have h0 : 0 < x := by linarith
  unfold G; have := Real.log_nonneg hx; positivity

theorem tail_le (N : ℕ) (hN : 300 ≤ N) : Tl N ≤ 0.07864 := by
  have h := tail_ind N hN
  have hN' : (300 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : 0 ≤ (1.9 * N - ψ (N : ℝ)) * g N :=
    mul_nonneg (by linarith [psi_le_19 N hN]) (g_nonneg (by linarith))
  have h2 := G_nonneg (show (1 : ℝ) ≤ N by linarith)
  have h3 := (log_le_pow 300 1054 (by norm_num))
  have h4 : 1.9 * (300 * g 300 + G 300) ≤ 0.07864 := by
    unfold g G; push_cast at h3; norm_num; linarith
  linarith

theorem f_le_lam_g {n : ℕ} (hn : 0 < n) : f n ≤ Λ n * g n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 : 0 ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
  have h1 : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  unfold f g
  rw [Real.rpow_neg hn'.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [mul_div_assoc', div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)

/-- **`DiagLam2`**, PROVED: `Σ Λ(n)²/n² ≤ 0.886`. -/
theorem diagLam2 : L5.DiagLam2 := by
  show ∑' n : ℕ, f n ≤ 0.886
  refine Real.tsum_le_of_sum_range_le f_nonneg fun N => ?_
  have h301 := s301
  change S N ≤ 0.886
  rcases le_or_gt N 301 with hN | hN
  · have : S N ≤ S 301 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hN)
        (fun i _ _ => f_nonneg i)
    linarith
  · obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
    have hK : 300 ≤ K := by omega
    have hsplit : S (K + 1) = S 301 + ∑ n ∈ Finset.Ico 301 (K + 1), f n :=
      (Finset.sum_range_add_sum_Ico _ (by omega)).symm
    have htl : ∑ n ∈ Finset.Ico 301 (K + 1), f n ≤ Tl K :=
      Finset.sum_le_sum fun n hn => f_le_lam_g (by simp at hn; omega)
    have := tail_le K hK
    linarith

/-- Plain-math twin and vacuity: the bound is not trivial, the head alone is positive. -/
theorem diagLam2_head_pos : 0 < S 3 := by
  have h : S 3 = S 2 + f 2 := S_succ 2
  have h2 : 0 ≤ S 2 := Finset.sum_nonneg fun i _ => f_nonneg i
  have h3 : 0 < f 2 := by
    unfold f; rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  linarith

/-- **(21), p. 370**, CONDITIONAL ON `LamSq2` only. -/
theorem bound21_of_lamSq (hL : L5.LamSq2) : L5.Bound21 := L5.bound21_proved diagLam2 hL

/-- **Lemma 5, p. 368**, CONDITIONAL ON Lemma 4, `Parseval1920`, `LamSq2`, `Const4`. -/
theorem lemma5_of_lamSq (h4 : Lemma4) (hP : L5.Parseval1920) (hL : L5.LamSq2) (hC : L5.Const4) :
    Lemma5 := L5.lemma5_of_lam h4 hP diagLam2 hL hC

end LeanLab.Kaniecki1995.L5Lam

#print axioms LeanLab.Kaniecki1995.L5Lam.log_le_pow
#print axioms LeanLab.Kaniecki1995.L5Lam.lam_zero_of
#print axioms LeanLab.Kaniecki1995.L5Lam.term_le
#print axioms LeanLab.Kaniecki1995.L5Lam.s301
#print axioms LeanLab.Kaniecki1995.L5Lam.log_le_quarter
#print axioms LeanLab.Kaniecki1995.L5Lam.psi_le_19
#print axioms LeanLab.Kaniecki1995.L5Lam.g_anti
#print axioms LeanLab.Kaniecki1995.L5Lam.g_tel
#print axioms LeanLab.Kaniecki1995.L5Lam.psi_succ
#print axioms LeanLab.Kaniecki1995.L5Lam.tail_ind
#print axioms LeanLab.Kaniecki1995.L5Lam.tail_le
#print axioms LeanLab.Kaniecki1995.L5Lam.f_le_lam_g
#print axioms LeanLab.Kaniecki1995.L5Lam.diagLam2
#print axioms LeanLab.Kaniecki1995.L5Lam.diagLam2_head_pos
#print axioms LeanLab.Kaniecki1995.L5Lam.bound21_of_lamSq
#print axioms LeanLab.Kaniecki1995.L5Lam.lemma5_of_lamSq
