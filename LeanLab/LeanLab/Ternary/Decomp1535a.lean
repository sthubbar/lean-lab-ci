/-
Unit U-1535, run 20261026T0004Z-24325. Decomposition of the weighted ternary statement
`ChenWangWeighted` of State1535 along the standard circle method route: the circle identity,
the split into major and minor arcs, the trivial minor arc bound through Parseval, and the
Chebyshev bound. Page references are to Liu-Wang 2002, Acta Arith. 105, pp. 133-175, which
uses this route. The leaves have `sorry` proofs; the assemblies have real proofs and are
CONDITIONAL ON the leaves.
AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Ternary.State1535

namespace LeanLab.Ternary.U1535

open MeasureTheory LeanLab.Ternary

/-! ### Leaves -/

/-- LEAF. Unit U-1535. Orthogonality: for an integer `k`, the integral of `e(kα)` over
`[0, 1]` is `1` if `k = 0` and `0` otherwise; Liu-Wang 2002 p. 145, behind eq. 3.10. -/
theorem orth_int (k : ℤ) :
    ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * k) =
      if k = 0 then 1 else 0 := by sorry

/-- LEAF. Unit U-1535. The circle identity: given orthogonality, `R3 N` equals the integral
of `S(α)^3 e(-Nα)` over `[0, 1]`; Liu-Wang 2002 p. 145, eq. 3.10, with weights on primes. -/
theorem circle_identity_of_orth
    (horth : ∀ k : ℤ, ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * k) =
      if k = 0 then 1 else 0) (N : ℕ) :
    (R3 N : ℂ) = ∫ α in (0 : ℝ)..1, F N α := by sorry

/-- LEAF. Unit U-1535. If the weighted count `R3 N` is positive then `N` is a sum of three
primes; Liu-Wang 2002 p. 145, eq. 3.9. -/
theorem isTernarySum_of_r3_pos {N : ℕ} (h : 0 < R3 N) : IsTernarySum N := by
  unfold R3 at h
  unfold IsTernarySum
  have hne : ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N + 1),
    (if Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = N then Real.log ↑p * Real.log ↑q * Real.log ↑r else (0 : ℝ)) ≠ 0 := ne_of_gt h
  have h1 := Finset.exists_ne_zero_of_sum_ne_zero hne
  rcases h1 with ⟨p, _, hp_ne⟩
  have h2 := Finset.exists_ne_zero_of_sum_ne_zero hp_ne
  rcases h2 with ⟨q, _, hq_ne⟩
  have h3 := Finset.exists_ne_zero_of_sum_ne_zero hq_ne
  rcases h3 with ⟨r, _, hr_ne⟩
  use p, q, r
  split_ifs at hr_ne with h_if
  · exact h_if
  · contradiction

/-- LEAF. Unit U-1535. Parseval: given orthogonality, the integral of `|S(α)|^2` over
`[0, 1]` is the sum of `(log p)^2` over primes `p ≤ N`; Liu-Wang 2002 p. 174, proof of
Theorem 1. -/
theorem parseval_of_orth
    (horth : ∀ k : ℤ, ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * k) =
      if k = 0 then 1 else 0) (N : ℕ) :
    ∫ α in (0 : ℝ)..1, ‖S N α‖ ^ 2 =
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p ^ 2 := by sorry

/-- LEAF. Unit U-1535. The exponential sum `S(α)` is continuous in `α`, a finite sum of
continuous terms; Liu-Wang 2002 p. 144, eq. 3.8. -/
theorem continuous_S (N : ℕ) : Continuous (S N) := by
  unfold S
  fun_prop

/-- LEAF. Unit U-1535. Splitting the circle: for a measurable set `M`, the integral of
`F` over `(0, 1]` is the integral over the part in `M` plus the part outside `M`;
Liu-Wang 2002 p. 145, eqs. 3.11 and 3.12. -/
theorem split_arcs (N : ℕ) {M : Set ℝ} (hM : MeasurableSet M) :
    ∫ α in Set.Ioc (0 : ℝ) 1, F N α =
      (∫ α in Set.Ioc (0 : ℝ) 1 ∩ M, F N α) + ∫ α in Set.Ioc (0 : ℝ) 1 \ M, F N α := by
  sorry

/-- LEAF. Unit U-1535. Trivial minor arc bound: if `|S(α)| ≤ B` with `B ≥ 0` off `M`,
then the integral of `F` off `M` has norm at most `B` times the integral of `|S|^2` over
`[0, 1]`; Liu-Wang 2002 p. 174, proof of Theorem 1. -/
theorem minor_bound (N : ℕ) {M : Set ℝ} (hM : MeasurableSet M) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ M, ‖S N α‖ ≤ B) :
    ‖∫ α in Set.Ioc (0 : ℝ) 1 \ M, F N α‖ ≤ B * ∫ α in (0 : ℝ)..1, ‖S N α‖ ^ 2 := by
  sorry

/-- LEAF. Unit U-1535. The sum of `(log p)^2` over primes `p ≤ N` is at most
`log N · θ(N)`; Liu-Wang 2002 p. 174, proof of Theorem 1. -/
theorem sum_log_sq_le (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p ^ 2 ≤
      Real.log N * theta N := by sorry

/-- LEAF. Unit U-1535. Chebyshev's bound `θ(N) ≤ N log 4`, from the primorial bound
`∏_{p ≤ N} p ≤ 4^N`; a weaker form of the bound on Liu-Wang 2002 p. 174. -/
theorem theta_le (N : ℕ) : theta N ≤ Real.log 4 * N := by sorry

/-- LEAF. Unit U-1535. The trivial bound `|S(α)| ≤ θ(N)` by the triangle inequality;
Liu-Wang 2002 p. 168, below eq. 6.2. -/
theorem norm_S_le (N : ℕ) (α : ℝ) : ‖S N α‖ ≤ theta N := by sorry

/-! ### Assemblies, zero sorry of their own -/

/-- `R3 N` is the real part of the circle integral over `(0, 1]`.
CONDITIONAL ON `orth_int` and `circle_identity_of_orth`. -/
theorem r3_eq_re_integral (N : ℕ) : R3 N = (∫ α in Set.Ioc (0 : ℝ) 1, F N α).re := by
  have h := circle_identity_of_orth orth_int N
  rw [intervalIntegral.integral_of_le zero_le_one] at h
  rw [← h, Complex.ofReal_re]

/-- Major arcs against minor arcs: a lower bound `A` for the real part of the major arc
integral and a pointwise bound `B` for `|S|` off the major arcs with `B Σ (log p)^2 < A`
give `R3 N > 0`. CONDITIONAL ON `orth_int`, `circle_identity_of_orth`, `split_arcs`,
`minor_bound`, `parseval_of_orth`. -/
theorem r3_pos_of_arcs (N : ℕ) {M : Set ℝ} (hM : MeasurableSet M) {A B : ℝ} (hB0 : 0 ≤ B)
    (hmaj : A ≤ (∫ α in Set.Ioc (0 : ℝ) 1 ∩ M, F N α).re)
    (hmin : ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ M, ‖S N α‖ ≤ B)
    (hAB : B * ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p ^ 2 < A) :
    0 < R3 N := by
  rw [r3_eq_re_integral, split_arcs N hM, Complex.add_re]
  have h1 := minor_bound N hM hB0 hmin
  rw [parseval_of_orth orth_int N] at h1
  have h2 := (abs_le.mp (Complex.abs_re_le_norm (∫ α in Set.Ioc (0 : ℝ) 1 \ M, F N α))).1
  linarith

/-- The same with the explicit right side `B · log N · N log 4`.
CONDITIONAL ON the leaves of `r3_pos_of_arcs` and `sum_log_sq_le`, `theta_le`. -/
theorem r3_pos_of_arcs_log4 (N : ℕ) {M : Set ℝ} (hM : MeasurableSet M) {A B : ℝ}
    (hB0 : 0 ≤ B)
    (hmaj : A ≤ (∫ α in Set.Ioc (0 : ℝ) 1 ∩ M, F N α).re)
    (hmin : ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ M, ‖S N α‖ ≤ B)
    (hAB : B * (Real.log N * (Real.log 4 * N)) < A) :
    0 < R3 N := by
  refine r3_pos_of_arcs N hM hB0 hmaj hmin (lt_of_le_of_lt ?_ hAB)
  have hl : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have h1 := sum_log_sq_le N
  have h2 := mul_le_mul_of_nonneg_left (theta_le N) hl
  exact mul_le_mul_of_nonneg_left (h1.trans h2) hB0

/-- The circle method frame for a threshold `C`: major and minor arc bounds for every odd
`N ≥ C` give every odd `N ≥ C` as a sum of three primes. CONDITIONAL ON the leaves of
`r3_pos_of_arcs_log4` and `isTernarySum_of_r3_pos`. -/
theorem ternaryAbove_of_arcs {C : ℝ}
    (h : ∀ N : ℕ, Odd N → C ≤ N → ∃ M : Set ℝ, MeasurableSet M ∧ ∃ A B : ℝ, 0 ≤ B ∧
      A ≤ (∫ α in Set.Ioc (0 : ℝ) 1 ∩ M, F N α).re ∧
      (∀ α ∈ Set.Ioc (0 : ℝ) 1 \ M, ‖S N α‖ ≤ B) ∧
      B * (Real.log N * (Real.log 4 * N)) < A) :
    TernaryAbove C := by
  intro N ho hN
  obtain ⟨M, hM, A, B, hB0, hmaj, hmin, hAB⟩ := h N ho hN
  exact isTernarySum_of_r3_pos (r3_pos_of_arcs_log4 N hM hB0 hmaj hmin hAB)

/-- The weighted form gives the plain form. CONDITIONAL ON `isTernarySum_of_r3_pos`. -/
theorem ternaryAbove_of_weighted {C : ℝ} (h : ChenWangWeighted C) : TernaryAbove C :=
  fun N ho hN => isTernarySum_of_r3_pos (h N ho hN)

/-- The weighted form is equivalent to the plain form. CONDITIONAL ON
`isTernarySum_of_r3_pos`. -/
theorem weighted_iff_ternaryAbove (C : ℝ) : ChenWangWeighted C ↔ TernaryAbove C :=
  ⟨ternaryAbove_of_weighted, chenWangWeighted_of_ternaryAbove⟩

end LeanLab.Ternary.U1535
