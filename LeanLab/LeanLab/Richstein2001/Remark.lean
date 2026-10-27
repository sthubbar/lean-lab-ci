/-
P0017 Richstein 2001, Section 7 Remark, page 1748: an exception to the ternary Goldbach
conjecture would now need a prime gap of 4·10^14 below 10^43000, the Chen-Wang 1989 bound from
which ternary Goldbach is known.
The reduction is stated and PROVED here: if even Goldbach holds up to M and some odd prime p
has N - M ≤ p ≤ N - 4, then the odd number N is a sum of three primes. So an odd N that is not
a sum of three primes has no odd prime in [N - M, N - 4], a prime gap of more than M - 4.
Also PROVED: e^(e^11.503) > 10^43000, so 10^43000 sits below the Chen-Wang bound as the remark
needs. Run 20261018T1103Z-12430, unit U-0937.
AI-written Lean code, Claude, 2026-10-18. Ternary Goldbach is a theorem of Helfgott; binary
Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Common.Goldbach

namespace LeanLab.Richstein2001

open LeanLab

/-- The reduction in Richstein's remark. -/
theorem ternary_of_prime_near {M N p : ℕ} (hE : EvenGoldbachUpTo M) (hN : Odd N)
    (hp : p.Prime) (hp2 : p ≠ 2) (h4 : p + 4 ≤ N) (hM : N ≤ p + M) : IsTernarySum N := by
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hev : Even (N - p) := by
    obtain ⟨a, ha⟩ := hN
    obtain ⟨b, hb⟩ := hpo
    exact ⟨a - b, by omega⟩
  obtain ⟨q, r, hq, hr, hqr⟩ := hE (N - p) hev (by omega) (by omega)
  exact ⟨p, q, r, hp, hq, hr, by omega⟩

/-- The contrapositive: an odd exception N leaves no odd prime in [N - M, N - 4]. -/
theorem gap_of_exception {M N : ℕ} (hE : EvenGoldbachUpTo M) (hN : Odd N)
    (hX : ¬ IsTernarySum N) :
    ∀ p, p.Prime → p ≠ 2 → N - M ≤ p → p + 4 ≤ N → False := by
  intro p hp hp2 h1 h2
  exact hX (ternary_of_prime_near hE hN hp hp2 h2 (by omega))

/-- 10^43000 is below the Chen-Wang 1989 bound e^(e^11.503). The margin is small:
43000 log 10 is about 99011.17 and e^11.503 about 99012.36. -/
theorem chenWang_gt : (10 : ℝ) ^ (43000 : ℕ) < Real.exp (Real.exp 11.503) := by
  have he := Real.exp_one_gt_d9
  have h5 : Real.log 5 < 1.609438 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have hs : Real.exp 1.609438 = Real.exp 1 * Real.exp 0.609438 := by
      rw [← Real.exp_add]; norm_num
    have h06' : (1.83939736 : ℝ) < Real.exp 0.609438 := by
      have := Real.sum_le_exp_of_nonneg (x := (0.609438 : ℝ)) (by norm_num) 13
      norm_num [Finset.sum_range_succ, Nat.factorial] at this
      linarith
    rw [hs]
    nlinarith
  have hl : Real.log 10 < 2.3025851808 := by
    have h2 := Real.log_two_lt_d9
    have : Real.log 10 = Real.log 2 + Real.log 5 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    linarith
  have he1 : (99011.5 : ℝ) < Real.exp 11.503 := by
    have h11 : Real.exp 11.503 = Real.exp 1 ^ 11 * Real.exp 0.503 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have h05 : (1.65367 : ℝ) < Real.exp 0.503 := by
      have := Real.sum_le_exp_of_nonneg (x := (0.503 : ℝ)) (by norm_num) 13
      norm_num [Finset.sum_range_succ, Nat.factorial] at this
      linarith
    have hpow : (2.7182818283 : ℝ) ^ 11 < Real.exp 1 ^ 11 :=
      pow_lt_pow_left₀ he (by norm_num) (by norm_num)
    have h59 : (59874.14 : ℝ) < Real.exp 1 ^ 11 := by
      have : (59874.14 : ℝ) < 2.7182818283 ^ 11 := by norm_num
      linarith
    rw [h11]
    nlinarith [Real.exp_pos 0.503]
  rw [← Real.exp_log (by positivity : (0 : ℝ) < 10 ^ (43000 : ℕ)), Real.exp_lt_exp,
    Real.log_pow]
  push_cast
  linarith

end LeanLab.Richstein2001
