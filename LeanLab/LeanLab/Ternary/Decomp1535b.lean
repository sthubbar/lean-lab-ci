/-
Unit U-1535, run 20261026T0004Z-24325. Second decomposition file for the weighted ternary
statement of State1535: the arc geometry from Dirichlet's theorem, the local factors of the
singular series, the singular integral count, the prime power excess, and the size of the
thresholds exp(exp(9.715)) for 1996 and exp(exp(11.503)) for 1989. Page references are to
Liu-Wang 2002, Acta Arith. 105, pp. 133-175, and to the 1996 abstract. The leaves have
`sorry` proofs; the assemblies have real proofs and are CONDITIONAL ON the leaves.
AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Ternary.State1535

namespace LeanLab.Ternary.U1535

open LeanLab.Ternary

/-! ### Leaves -/

/-- LEAF. Unit U-1535. Dirichlet's approximation: for `Q ≥ 1` every real `α` has
`1 ≤ q ≤ Q` and an integer `a` with `|α - a/q| ≤ 1/(q(Q+1))`; Liu-Wang 2002 p. 144,
eq. 3.2. -/
theorem dirichlet_cover (α : ℝ) (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ∧ ∃ a : ℤ, |α - a / q| ≤ 1 / (q * ((Q : ℝ) + 1)) := by sorry

/-- LEAF. Unit U-1535. Disjoint arcs: if `q, q' ≤ P`, `2P < Q` and `a/q ≠ a'/q'`, then
the arcs of radius `1/(qQ)` and `1/(q'Q)` around them are disjoint, since the centres are
more than the sum of the radii apart; Liu-Wang 2002 p. 144, below eq. 3.2. -/
theorem arcs_disjoint {P Q q q' : ℕ} {a a' : ℤ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hqP : q ≤ P) (hq'P : q' ≤ P) (hPQ : 2 * P < Q) (hne : (a : ℝ) / q ≠ a' / q') :
    1 / ((q : ℝ) * Q) + 1 / ((q' : ℝ) * Q) < |(a : ℝ) / q - a' / q'| := by sorry

/-- LEAF. Unit U-1535. Ramanujan's sum at a prime: the sum of `e(aN/p)` over
`1 ≤ a ≤ p - 1` is `p - 1` if `p` divides `N` and `-1` otherwise; the local factor of the
singular series, Liu-Wang 2002 p. 145, eq. 3.14 with principal character. -/
theorem ramanujan_prime (p : ℕ) (hp : p.Prime) (N : ℕ) :
    ∑ a ∈ Finset.Ico 1 p, Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * N / p : ℝ) : ℂ)) =
      if p ∣ N then ((p : ℂ) - 1) else -1 := by sorry

/-- LEAF. Unit U-1535. The singular integral count: the number of ordered triples of
positive integers with sum `N` is `(N - 1)(N - 2)/2`; the main term of the major arc
integral, Liu-Wang 2002 p. 156, Lemma 4.3. -/
theorem triple_count (N : ℕ) :
    ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
      (fun x : ℕ × ℕ × ℕ => x.1 + x.2.1 + x.2.2 = N)).card = (N - 1) * (N - 2) / 2 := by
  sorry

/-- LEAF. Unit U-1535. Singular series, dividing primes: the product of
`1 - 1/(p - 1)^2` over primes `3 ≤ p ≤ X` dividing `N` is at least `0.6`, since the full
product over odd primes is the twin prime constant `0.6601...`; Liu-Wang 2002 p. 156,
Lemma 4.3. -/
theorem singular_partial (N X : ℕ) :
    (0.6 : ℝ) ≤ ∏ p ∈ (Finset.Icc 3 X).filter (fun p => p.Prime ∧ p ∣ N),
      (1 - 1 / ((p : ℝ) - 1) ^ 2) := by sorry

/-- LEAF. Unit U-1535. Singular series, coprime primes: the product of `1 + 1/(p - 1)^3`
over primes `p ≤ X` not dividing `N` is at least `1`; Liu-Wang 2002 p. 156, Lemma 4.3. -/
theorem singular_coprime_factor (N X : ℕ) :
    (1 : ℝ) ≤ ∏ p ∈ (Finset.range (X + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ N),
      (1 + 1 / ((p : ℝ) - 1) ^ 3) := by sorry

/-- LEAF. Unit U-1535. Prime powers: `ψ(N) - θ(N) ≤ 2 √N log N`, the cost of passing
from von Mangoldt weights to prime weights; Liu-Wang 2002 p. 145, below eq. 3.10. -/
theorem primePower_excess (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n - theta N ≤
      2 * Real.sqrt N * Real.log N := by sorry

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000

/-- LEAF. Unit U-1535. Size of the 1996 threshold, upper side: `exp(exp(9.715)) ≤ 10^7194`;
the abstract gives `exp(exp(9.715)) ≈ 10^7194`, and `exp(9.715)/log 10 ≈ 7193.75`. -/
theorem exp_exp_upper : Real.exp (Real.exp 9.715) ≤ (10 : ℝ) ^ (7194 : ℕ) := by
  have h1 : Real.exp (9.715 : ℝ) ≤ (33129 / 2 : ℝ) := by
    have he_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have ht1 : Real.exp 9.715 = (Real.exp 1) ^ (9.715 : ℝ) := by
      rw [← Real.exp_mul, one_mul]
    have ht2 : (Real.exp 1) ^ (9.715 : ℝ) ≤ (2.7182818286 : ℝ) ^ (9.715 : ℝ) := by
      apply Real.rpow_le_rpow (by positivity) he_lt.le (by positivity)
    have ht3 : (2.7182818286 : ℝ) ^ (9.715 : ℝ) ≤ 33129 / 2 := by
      have h_rpow : (2.7182818286 : ℝ) ^ (9.715 : ℝ) = ((2.7182818286 : ℝ) ^ (1943 : ℕ)) ^ ((200 : ℕ)⁻¹ : ℝ) := by
        have : (9.715 : ℝ) = (1943 : ℝ) * (200 : ℝ)⁻¹ := by norm_num
        rw [this, Real.rpow_mul (by positivity)]
        congr 1
        exact Real.rpow_natCast _ _
      rw [h_rpow]
      have h_num : (13591409143 : ℕ) ^ 1943 * 2 ^ 200 ≤ (33129 : ℕ) ^ 200 * (5000000000 : ℕ) ^ 1943 := by
        decide
      have h1 : (13591409143 : ℝ) ^ 1943 * 2 ^ 200 ≤ (33129 : ℝ) ^ 200 * (5000000000 : ℝ) ^ 1943 := by
        exact_mod_cast h_num
      have h2 : (2.7182818286 : ℝ) ^ (1943 : ℕ) = (13591409143 : ℝ) ^ (1943 : ℕ) / (5000000000 : ℝ) ^ (1943 : ℕ) := by
        rw [← div_pow]
        norm_num
      have h3 : (13591409143 : ℝ) ^ (1943 : ℕ) / (5000000000 : ℝ) ^ (1943 : ℕ) ≤ (33129 / 2 : ℝ) ^ (200 : ℕ) := by
        rw [div_le_iff₀ (by positivity)]
        have h2' : (33129 / 2 : ℝ) ^ (200 : ℕ) = (33129 : ℝ) ^ (200 : ℕ) / (2 : ℝ) ^ 200 := by
          exact div_pow (33129 : ℝ) 2 200
        rw [h2']
        have ht : (33129 : ℝ) ^ 200 / 2 ^ 200 * 5000000000 ^ 1943 = (33129 : ℝ) ^ 200 * 5000000000 ^ 1943 / 2 ^ 200 := by ring
        rw [ht]
        have h1' : (13591409143 : ℝ) ^ (1943 : ℕ) * (2 : ℝ) ^ 200 ≤ (33129 : ℝ) ^ (200 : ℕ) * (5000000000 : ℝ) ^ (1943 : ℕ) := by exact h1
        exact (le_div_iff₀ (by positivity)).mpr h1'
      have h4 : (2.7182818286 : ℝ) ^ (1943 : ℕ) ≤ (33129 / 2 : ℝ) ^ (200 : ℕ) := by
        exact h2.le.trans h3
      have h5 : ((2.7182818286 : ℝ) ^ (1943 : ℕ)) ^ ((200 : ℕ)⁻¹ : ℝ) ≤ ((33129 / 2 : ℝ) ^ (200 : ℕ)) ^ ((200 : ℕ)⁻¹ : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) h4 (by positivity)
      have h6 : ((33129 / 2 : ℝ) ^ (200 : ℕ)) ^ ((200 : ℕ)⁻¹ : ℝ) = (33129 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_inv_cancel₀ (by norm_num), Real.rpow_one]
      exact h5.trans h6.le
    calc
      Real.exp 9.715 = (Real.exp 1) ^ (9.715 : ℝ) := ht1
      _ ≤ (2.7182818286 : ℝ) ^ (9.715 : ℝ) := ht2
      _ ≤ 33129 / 2 := ht3
  have h2 : (33129 / 2 : ℝ) ≤ 7194 * Real.log 10 := by
    have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hl5 : (1.6094379123 : ℝ) < Real.log 5 := Real.log_five_gt_d9
    have ht : Real.log 10 = Real.log 2 + Real.log 5 := by
      have : (10 : ℝ) = 2 * 5 := by norm_num
      rw [this, Real.log_mul (by positivity) (by positivity)]
    rw [ht]
    calc (33129 / 2 : ℝ) ≤ 7194 * (0.6931471803 + 1.6094379123) := by norm_num
      _ ≤ 7194 * (Real.log 2 + Real.log 5) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
  calc
    Real.exp (Real.exp 9.715) ≤ Real.exp (33129 / 2) := Real.exp_le_exp.mpr h1
    _ ≤ Real.exp (7194 * Real.log 10) := Real.exp_le_exp.mpr h2
    _ = Real.exp (Real.log ((10 : ℝ) ^ (7194 : ℕ))) := by
      rw [Real.log_pow]; push_cast; ring
    _ = (10 : ℝ) ^ (7194 : ℕ) := Real.exp_log (by positivity)

/-- LEAF. Unit U-1535. Size of the 1996 threshold, lower side: `10^7193 ≤ exp(exp(9.715))`;
abstract, `exp(9.715)/log 10 ≈ 7193.75`. -/
theorem exp_exp_lower : (10 : ℝ) ^ (7193 : ℕ) ≤ Real.exp (Real.exp 9.715) := by
  have h1 : (16562.5 : ℝ) ≤ Real.exp (9.715 : ℝ) := by
    have he_gt : 2.7182818283 ≤ Real.exp 1 := by
      exact Real.exp_one_gt_d9.le
    have ht1 : Real.exp 9.715 = (Real.exp 1) ^ (9.715 : ℝ) := by
      rw [← Real.exp_mul, one_mul]
    have ht2 : (2.7182818283 : ℝ) ^ (9.715 : ℝ) ≤ (Real.exp 1) ^ (9.715 : ℝ) := by
      apply Real.rpow_le_rpow (by positivity) he_gt (by positivity)
    have ht3 : 16562.5 ≤ (2.7182818283 : ℝ) ^ (9.715 : ℝ) := by
      have h_rpow : (2.7182818283 : ℝ) ^ (9.715 : ℝ) = ((2.7182818283 : ℝ) ^ (1943 : ℕ)) ^ ((200 : ℕ)⁻¹ : ℝ) := by
        have : (9.715 : ℝ) = (1943 : ℝ) * (200 : ℝ)⁻¹ := by norm_num
        rw [this, Real.rpow_mul (by positivity)]
        congr 1
        exact Real.rpow_natCast _ _
      rw [h_rpow]
      have h_num : (33125 : ℕ) ^ 200 * (10000000000 : ℕ) ^ 1943 ≤ (27182818283 : ℕ) ^ 1943 * 2 ^ 200 := by
        decide
      have h1 : (33125 : ℝ) ^ 200 * (10000000000 : ℝ) ^ 1943 ≤ (27182818283 : ℝ) ^ 1943 * 2 ^ 200 := by
        exact_mod_cast h_num
      have h2 : (2.7182818283 : ℝ) ^ (1943 : ℕ) = (27182818283 : ℝ) ^ (1943 : ℕ) / (10000000000 : ℝ) ^ (1943 : ℕ) := by
        rw [← div_pow]
        norm_num
      have h3 : (33125 / 2 : ℝ) ^ (200 : ℕ) ≤ (27182818283 : ℝ) ^ (1943 : ℕ) / (10000000000 : ℝ) ^ (1943 : ℕ) := by
        have h2' : (33125 / 2 : ℝ) ^ (200 : ℕ) = (33125 : ℝ) ^ (200 : ℕ) / (2 : ℝ) ^ 200 := by
          exact div_pow (33125 : ℝ) 2 200
        rw [h2']
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        exact h1
      have h4 : (33125 / 2 : ℝ) ^ (200 : ℕ) ≤ (2.7182818283 : ℝ) ^ (1943 : ℕ) := by
        exact h3.trans h2.symm.le
      have h5 : ((33125 / 2 : ℝ) ^ (200 : ℕ)) ^ ((200 : ℕ)⁻¹ : ℝ) ≤ ((2.7182818283 : ℝ) ^ (1943 : ℕ)) ^ ((200 : ℕ)⁻¹ : ℝ) := by
        apply Real.rpow_le_rpow (by positivity) h4 (by positivity)
      have h6 : ((33125 / 2 : ℝ) ^ (200 : ℕ)) ^ ((200 : ℕ)⁻¹ : ℝ) = (33125 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_inv_cancel₀ (by norm_num), Real.rpow_one]
      have ht : (16562.5 : ℝ) = 33125 / 2 := by norm_num
      rw [ht]
      exact h6.symm.le.trans h5
    calc
      16562.5 ≤ (2.7182818283 : ℝ) ^ (9.715 : ℝ) := ht3
      _ ≤ (Real.exp 1) ^ (9.715 : ℝ) := ht2
      _ = Real.exp 9.715 := ht1.symm
  have h2 : 7193 * Real.log 10 ≤ 16562.5 := by
    have hl2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hl5 : Real.log 5 < 1.6094379126 := Real.log_five_lt_d9
    have ht : Real.log 10 = Real.log 2 + Real.log 5 := by
      have : (10 : ℝ) = 2 * 5 := by norm_num
      rw [this, Real.log_mul (by positivity) (by positivity)]
    rw [ht]
    calc 7193 * (Real.log 2 + Real.log 5) ≤ 7193 * (0.6931471808 + 1.6094379126) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ ≤ 16562.5 := by norm_num
  calc
    (10 : ℝ) ^ (7193 : ℕ) = Real.exp (Real.log ((10 : ℝ) ^ (7193 : ℕ))) := (Real.exp_log (by positivity)).symm
    _ = Real.exp (7193 * Real.log 10) := by
      rw [Real.log_pow]; push_cast; ring
    _ ≤ Real.exp 16562.5 := Real.exp_le_exp.mpr h2
    _ ≤ Real.exp (Real.exp 9.715) := Real.exp_le_exp.mpr h1

/-- LEAF. Unit U-1535. Size of the 1989 threshold: `10^43000 ≤ exp(exp(11.503))`;
Liu-Wang 2002 p. 134 gives `exp(exp(11.503)) = 10^43000.5...`. -/
theorem exp_exp_1989 : (10 : ℝ) ^ (43000 : ℕ) ≤ Real.exp (Real.exp 11.503) := by sorry

/-! ### Assemblies, zero sorry of their own -/

/-- Off the major arcs with `q ≤ P` the Dirichlet denominator exceeds `P`: the minor arc
dichotomy. CONDITIONAL ON `dirichlet_cover`. -/
theorem minor_q_large {α : ℝ} {P Q : ℕ} (hQ : 1 ≤ Q)
    (hα : ∀ q : ℕ, 1 ≤ q → q ≤ P → ∀ a : ℤ, 1 / (q * ((Q : ℝ) + 1)) < |α - a / q|) :
    ∃ q : ℕ, P < q ∧ q ≤ Q ∧ ∃ a : ℤ, |α - a / q| ≤ 1 / (q * ((Q : ℝ) + 1)) := by
  obtain ⟨q, h1, h2, a, ha⟩ := dirichlet_cover α Q hQ
  refine ⟨q, ?_, h2, a, ha⟩
  by_contra hle
  exact absurd ha (not_le.mpr (hα q h1 (not_lt.mp hle) a))

/-- The 1996 threshold lies between `10^7193` and `10^7194`.
CONDITIONAL ON `exp_exp_lower`, `exp_exp_upper`. -/
theorem chenWang_size :
    (10 : ℝ) ^ (7193 : ℕ) ≤ Real.exp (Real.exp 9.715) ∧
      Real.exp (Real.exp 9.715) ≤ (10 : ℝ) ^ (7194 : ℕ) :=
  ⟨exp_exp_lower, exp_exp_upper⟩

/-- Chen-Wang's bound in powers of ten: every odd `N ≥ 10^7194` is a sum of three primes.
CONDITIONAL ON `exp_exp_upper` and on the hypothesis. -/
theorem ternaryAbove_10pow_of_chenWang (h : TernaryAbove (Real.exp (Real.exp 9.715))) :
    TernaryAbove ((10 : ℝ) ^ (7194 : ℕ)) :=
  ternaryAbove_mono exp_exp_upper h

/-- The 1996 threshold improves the 1989 one by a factor of at least `10^35806`:
`exp(exp(9.715)) · 10^35806 ≤ exp(exp(11.503))`. CONDITIONAL ON `exp_exp_upper`,
`exp_exp_1989`. -/
theorem threshold_gap :
    Real.exp (Real.exp 9.715) * (10 : ℝ) ^ (35806 : ℕ) ≤ Real.exp (Real.exp 11.503) := by
  have h1 := mul_le_mul_of_nonneg_right exp_exp_upper
    (show (0 : ℝ) ≤ (10 : ℝ) ^ (35806 : ℕ) by positivity)
  rw [← pow_add] at h1
  exact h1.trans exp_exp_1989

end LeanLab.Ternary.U1535
