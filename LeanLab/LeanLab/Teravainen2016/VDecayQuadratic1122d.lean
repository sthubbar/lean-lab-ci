/-
P0076, Section 4, Proposition 4.1 v, page 16, display 4.5.
Split of the HARD leaf `vdecay_quadratic_bound` of VDecay1122b.lean into the exact Selberg
diagonalization of the twisted quadratic form at q, a proved truncated mass bound by G_1,
and a local factor bound at the primes of q. The assembly is proved.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.VDecay1122b

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- LEAF: Proposition 4.1 v, page 16, display 4.5 with w_q sharp from reference 18 formulas
4.1.14 and 4.1.15, class HARD. The Selberg diagonalization with y variables y_m equal to
h of m over G 1 of z for m dividing P of z with m at most z, so that rho_d is mu of d over
g of d times the sum of y_m over the multiples m of d. Writing g of lcm d1 d2 as g d1 g d2
over g of gcd d1 d2 and one over g of a square free k as the sum over e dividing k of one
over h of e, the twisted form at q collapses to the diagonal sum over n coprime to q of
h of n times a kernel over pairs a, b of divisors of q with lcm a b equal to q. Checked with
exact rationals for w equal 5, 6, 10, integer z up to 31 and every q dividing P of z. -/
theorem vdq_selberg_diagonal {w : ℕ} (hw : 5 ≤ w) {z : ℝ} (hz : 1 ≤ z) {q : ℕ}
    (hq : q ∣ envelopingPrimeProduct w z) :
    envelopingG w 1 z *
        ∑ d1 ∈ (envelopingPrimeProduct w z).divisors,
          ∑ d2 ∈ (envelopingPrimeProduct w z).divisors,
            (if q ∣ Nat.lcm d1 d2 then
              envelopingRho w d1 z * envelopingRho w d2 z *
                envelopingDensity w (Nat.lcm d1 d2 / q)
            else 0) =
      (-1 : ℝ) ^ q.primeFactors.card / (envelopingDensity w q * envelopingG w 1 z) *
        ∑ n ∈ (envelopingPrimeProduct w z).divisors.filter (fun n => Nat.Coprime n q),
          envelopingH w n *
            ∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
              (if Nat.lcm a b = q ∧ ((n * a : ℕ) : ℝ) ≤ z ∧ ((n * b : ℕ) : ℝ) ≤ z then
                envelopingH w a * envelopingH w b *
                  ∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)
              else 0) := by
  sorry

/-- LEAF: Proposition 4.1 v, page 16, the local factor of w_q sharp at the primes of q, as
in reference 18 formula 4.1.18, class MEDIUM. The kernel of the diagonalization in absolute
value, summed over pairs a, b of divisors of q with lcm a b equal to q, is multiplicative in
q with local factor 2 h of p plus h of p times the absolute value of h of p minus 1 at each
prime p of q. Since h of p is at most 2 over 5 and g of p is h of p times 1 minus g of p,
this local factor over g of p is at most 3 over 1 minus g of p, at most 21 over 5. -/
theorem vdq_local_factor {w : ℕ} (hw : 5 ≤ w) {z : ℝ} {q : ℕ}
    (hq : q ∣ envelopingPrimeProduct w z) :
    ∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
        (if Nat.lcm a b = q then
          envelopingH w a * envelopingH w b *
            |∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)|
        else 0) ≤
      (21 / 5 : ℝ) ^ q.primeFactors.card * envelopingDensity w q := by
  sorry

/-- Page 15: the diagonal mass of h over n dividing P of z with n at most z is at most G 1
of z, since each such n is one of the delta in the sum defining G 1 of z. -/
theorem vdq_truncated_mass (w : ℕ) {z : ℝ} (q : ℕ) :
    ∑ n ∈ ((envelopingPrimeProduct w z).divisors.filter (fun n => Nat.Coprime n q)).filter
        (fun n : ℕ => (n : ℝ) ≤ z), envelopingH w n ≤ envelopingG w 1 z := by
  unfold envelopingG
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [mem_filter, Nat.mem_divisors] at hn
    obtain ⟨⟨⟨hdvd, hP⟩, -⟩, hnz⟩ := hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hP (zero_dvd_iff.mp hdvd)
    simp only [mem_filter, mem_Icc, Nat.lcm_one_left]
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr hn0, ?_⟩, hnz⟩
    have hz0 : (0 : ℝ) ≤ z := le_trans (Nat.cast_nonneg n) hnz
    exact Nat.le_floor hnz
  · intro n _ _
    exact envelopingH_nonneg w n

/-- Page 16: the local density g of q is positive for q dividing P of z, since every prime
of q lies above w and so omega of p is 1 or 2. -/
theorem vdq_density_pos {w : ℕ} {z : ℝ} {q : ℕ} (hq : q ∣ envelopingPrimeProduct w z) :
    0 < envelopingDensity w q := by
  unfold envelopingDensity
  apply prod_pos
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpq := Nat.dvd_of_mem_primeFactors hp
  have hgt := efs_prime_gt hpp (dvd_trans hpq hq)
  have hom : 1 ≤ envelopingOmega w p := by
    unfold envelopingOmega
    split_ifs <;> omega
  have : (0 : ℝ) < envelopingOmega w p := by exact_mod_cast hom
  have : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  positivity

/-- The kernel at n vanishes unless n is at most z, and is bounded by the absolute kernel. -/
theorem vdq_kernel_abs_le {w : ℕ} {z : ℝ} {q n : ℕ} :
    |∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
        (if Nat.lcm a b = q ∧ ((n * a : ℕ) : ℝ) ≤ z ∧ ((n * b : ℕ) : ℝ) ≤ z then
          envelopingH w a * envelopingH w b *
            ∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)
        else 0)| ≤
      if (n : ℝ) ≤ z then
        ∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
          (if Nat.lcm a b = q then
            envelopingH w a * envelopingH w b *
              |∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)|
          else 0)
      else 0 := by
  split_ifs with hnz
  · refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => ?_)
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b _ => ?_)
    split_ifs with h1 h2
    · rw [abs_mul, abs_mul, abs_of_nonneg (envelopingH_nonneg w a),
        abs_of_nonneg (envelopingH_nonneg w b)]
    · exact absurd h1.1 h2
    · rw [abs_zero]
      have := envelopingH_nonneg w a
      have := envelopingH_nonneg w b
      positivity
    · rw [abs_zero]
  · rw [abs_nonpos_iff]
    apply sum_eq_zero
    intro a ha
    apply sum_eq_zero
    intro b _
    rw [ite_eq_right_iff]
    rintro ⟨-, h2, -⟩
    exfalso
    apply hnz
    have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pos_of_mem_divisors ha))
    have : n ≤ n * a := Nat.le_mul_of_pos_right n ha1
    have : (n : ℝ) ≤ ((n * a : ℕ) : ℝ) := by exact_mod_cast this
    linarith

/-- Assembly: the exact statement of `vdecay_quadratic_bound` with K equal to 21 over 5,
from the diagonalization leaf, the local factor leaf and the proved truncated mass bound. -/
theorem vdecay_quadratic_bound_of_leaves :
    type_of% @LeanLab.Teravainen2016.vdecay_quadratic_bound := by
  refine ⟨21 / 5, by norm_num, ?_⟩
  intro w hw z hz q hq
  have hwBig : (5 : ℝ) ≤ wBig := by
    calc (5 : ℝ) ≤ 10 := by norm_num
      _ = (10 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ wBig := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (Real.one_le_rpow (by norm_num) (by positivity))
  have hw5 : 5 ≤ w := by exact_mod_cast (hwBig.trans hw)
  rw [vdq_selberg_diagonal hw5 hz hq]
  set U := ∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
        (if Nat.lcm a b = q then
          envelopingH w a * envelopingH w b *
            |∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)|
        else 0) with hU
  have hg := vdq_density_pos hq
  have hG := envelopingG_one_le w hz
  have hG0 : 0 < envelopingG w 1 z := by linarith
  have hU0 : 0 ≤ U := by
    apply sum_nonneg; intro a _; apply sum_nonneg; intro b _
    split_ifs
    · have := envelopingH_nonneg w a
      have := envelopingH_nonneg w b
      positivity
    · exact le_refl 0
  have hloc := vdq_local_factor hw5 (z := z) hq
  rw [← hU] at hloc
  set S := (envelopingPrimeProduct w z).divisors.filter (fun n => Nat.Coprime n q) with hS
  have hsum : |∑ n ∈ S, envelopingH w n *
      ∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
        (if Nat.lcm a b = q ∧ ((n * a : ℕ) : ℝ) ≤ z ∧ ((n * b : ℕ) : ℝ) ≤ z then
          envelopingH w a * envelopingH w b *
            ∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)
        else 0)| ≤ envelopingG w 1 z * U := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ n ∈ S, (if (n : ℝ) ≤ z then envelopingH w n * U else 0) := by
          apply sum_le_sum
          intro n _
          rw [abs_mul, abs_of_nonneg (envelopingH_nonneg w n)]
          have hk := vdq_kernel_abs_le (w := w) (z := z) (q := q) (n := n)
          rw [← hU] at hk
          have hh := envelopingH_nonneg w n
          split_ifs at hk ⊢
          · exact mul_le_mul_of_nonneg_left hk hh
          · have : |∑ a ∈ q.divisors, ∑ b ∈ q.divisors,
                (if Nat.lcm a b = q ∧ ((n * a : ℕ) : ℝ) ≤ z ∧ ((n * b : ℕ) : ℝ) ≤ z then
                  envelopingH w a * envelopingH w b *
                    ∏ p ∈ (Nat.gcd a b).primeFactors, (1 - 1 / envelopingH w p)
                else 0)| = 0 := le_antisymm hk (abs_nonneg _)
            rw [this, mul_zero]
      _ = (∑ n ∈ S.filter (fun n : ℕ => (n : ℝ) ≤ z), envelopingH w n) * U := by
          rw [← sum_filter, sum_mul]
      _ ≤ envelopingG w 1 z * U :=
          mul_le_mul_of_nonneg_right (vdq_truncated_mass w q) hU0
  rw [abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (mul_pos hg hG0)]
  calc 1 / (envelopingDensity w q * envelopingG w 1 z) * |_|
      ≤ 1 / (envelopingDensity w q * envelopingG w 1 z) * (envelopingG w 1 z * U) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = U / envelopingDensity w q := by field_simp
    _ ≤ (21 / 5 : ℝ) ^ q.primeFactors.card := by
        rw [div_le_iff₀ hg]; exact hloc

#print axioms vdq_truncated_mass
#print axioms vdq_density_pos
#print axioms vdq_kernel_abs_le
#print axioms vdecay_quadratic_bound_of_leaves

end LeanLab.Teravainen2016
