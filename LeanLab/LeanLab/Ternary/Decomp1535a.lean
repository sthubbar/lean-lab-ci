/-
Unit U-1535, run 20261026T0004Z-24325. Decomposition of the weighted ternary statement
`ChenWangWeighted` of State1535 along the standard circle method route: the circle identity,
the split into major and minor arcs, the trivial minor arc bound through Parseval, and the
Chebyshev bound. Page references are to Liu-Wang 2002, Acta Arith. 105, pp. 133-175, which
uses this route. All elementary leaves and assemblies below have proofs.
The quantitative major and minor arc estimates remain explicit hypotheses.
AI-written Lean code, Claude, 2026-10-26, and Codex task200, 2026-10-31.
Checked by module builds and the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Ternary.State1535
import LeanLab.Ternary.MMSOrthogonality
import LeanLab.Ternary.Decomp1535b

namespace LeanLab.Ternary.U1535

open MeasureTheory LeanLab.Ternary
open scoped ComplexConjugate

/-! ### Leaves -/

/-- LEAF. Unit U-1535. Orthogonality: for an integer `k`, the integral of `e(kα)` over
`[0, 1]` is `1` if `k = 0` and `0` otherwise; Liu-Wang 2002 p. 145, behind eq. 3.10. -/
theorem orth_int (k : ℤ) :
    ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * k) =
      if k = 0 then 1 else 0 := by
  convert LeanLab.Ternary.MMS.integral_e_int k using 1
  congr 1
  ext α
  unfold LeanLab.Ternary.MMS.e
  push_cast
  congr 1
  ring

/-- LEAF. Unit U-1535. The circle identity: given orthogonality, `R3 N` equals the integral
of `S(α)^3 e(-Nα)` over `[0, 1]`; Liu-Wang 2002 p. 145, eq. 3.10, with weights on primes. -/
theorem circle_identity_of_orth
    (horth : ∀ k : ℤ, ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * k) =
      if k = 0 then 1 else 0) (N : ℕ) :
    (R3 N : ℂ) = ∫ α in (0 : ℝ)..1, F N α := by
  let P := (Finset.range (N + 1)).filter Nat.Prime
  have hF (α : ℝ) : F N α =
      ∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P,
        ((Real.log p * Real.log q * Real.log r : ℝ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * α * ((p : ℤ) + q + r - N : ℤ)) := by
    unfold F S
    change (∑ p ∈ P, _) ^ 3 * _ = _
    rw [pow_succ, pow_two]
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Complex.ofReal_mul, Int.cast_add, Int.cast_sub, Int.cast_natCast]
    calc
      _ = ((Real.log p : ℂ) * Real.log q * Real.log r) *
          (Complex.exp (2 * Real.pi * Complex.I * α * p) *
            Complex.exp (2 * Real.pi * Complex.I * α * q) *
            Complex.exp (2 * Real.pi * Complex.I * α * r) *
            Complex.exp (-(2 * Real.pi * Complex.I * α * N))) := by ring
      _ = _ := by
        rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
        congr 2
        ring
  have hc (p q r : ℕ) : Continuous (fun α : ℝ =>
      ((Real.log p * Real.log q * Real.log r : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * α * ((p : ℤ) + q + r - N : ℤ))) := by fun_prop
  have hint : (∫ α in (0 : ℝ)..1, F N α) =
      ∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P,
        if p + q + r = N then ((Real.log p * Real.log q * Real.log r : ℝ) : ℂ) else 0 := by
    simp_rw [hF]
    rw [intervalIntegral.integral_finsetSum (fun p hp =>
      (continuous_finsetSum _ fun q hq => continuous_finsetSum _ fun r hr => hc p q r).intervalIntegrable 0 1)]
    simp_rw [intervalIntegral.integral_finsetSum (fun q hq =>
      (continuous_finsetSum _ fun r hr => hc _ q r).intervalIntegrable 0 1)]
    simp_rw [intervalIntegral.integral_finsetSum (fun r hr => (hc _ _ r).intervalIntegrable 0 1),
      intervalIntegral.integral_const_mul, horth]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    have heq : (p : ℤ) + q + r - N = 0 ↔ p + q + r = N := by omega
    simp only [heq]
    split_ifs <;> simp
  rw [hint]
  unfold R3
  simp only [Complex.ofReal_sum]
  dsimp [P]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpp : p.Prime
  · simp only [hpp, ite_true]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hqp : q.Prime
    · simp only [hqp, ite_true, true_and]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hrp : r.Prime <;>
        simp only [hrp, true_and, false_and, ite_true, ite_false] <;>
        (try split_ifs) <;> simp only [Complex.ofReal_mul, Complex.ofReal_zero]
    · simp [hqp]
  · simp [hpp]

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
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p ^ 2 := by
  let P := (Finset.range (N + 1)).filter Nat.Prime
  have hconj (α : ℝ) : conj (S N α) =
      ∑ q ∈ P, (Real.log q : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * α * q)) := by
    unfold S
    simp only [map_sum, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    apply Finset.sum_congr rfl
    intro q hq
    congr 2
    simp only [Complex.conj_I, map_ofNat, map_natCast]
    ring
  have hsq (α : ℝ) : ((‖S N α‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ P, ∑ q ∈ P, ((Real.log p * Real.log q : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * α * ((p : ℤ) - q : ℤ)) := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj', hconj]
    unfold S
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    simp only [Complex.ofReal_mul, Int.cast_sub, Int.cast_natCast]
    calc
      _ = ((Real.log p : ℂ) * Real.log q) *
          (Complex.exp (2 * Real.pi * Complex.I * α * p) *
            Complex.exp (-(2 * Real.pi * Complex.I * α * q))) := by ring
      _ = _ := by
        rw [← Complex.exp_add]
        congr 2
        ring
  have hc (p q : ℕ) : Continuous (fun α : ℝ =>
      ((Real.log p * Real.log q : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * α * ((p : ℤ) - q : ℤ))) := by fun_prop
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hsq]
  rw [intervalIntegral.integral_finsetSum (fun p hp =>
    (continuous_finsetSum _ fun q hq => hc p q).intervalIntegrable 0 1)]
  simp_rw [intervalIntegral.integral_finsetSum (fun q hq => (hc _ q).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, horth]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow]
  simp [P, mul_ite, sub_eq_zero, eq_comm, pow_two]
  apply Finset.sum_congr rfl
  intro p hp
  have hpp := (Finset.mem_filter.mp hp).2
  have hpN : p ≤ N := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    omega
  simp only [hpp, hpN, and_self, ite_true]

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
  have hc : Continuous (F N) := by
    unfold F S
    fun_prop
  exact (integral_inter_add_sdiff hM
    (hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)).symm

/-- LEAF. Unit U-1535. Trivial minor arc bound: if `|S(α)| ≤ B` with `B ≥ 0` off `M`,
then the integral of `F` off `M` has norm at most `B` times the integral of `|S|^2` over
`[0, 1]`; Liu-Wang 2002 p. 174, proof of Theorem 1. -/
theorem minor_bound (N : ℕ) {M : Set ℝ} (hM : MeasurableSet M) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ M, ‖S N α‖ ≤ B) :
    ‖∫ α in Set.Ioc (0 : ℝ) 1 \ M, F N α‖ ≤ B * ∫ α in (0 : ℝ)..1, ‖S N α‖ ^ 2 := by
  have hc : Continuous (fun α : ℝ => ‖S N α‖ ^ 2) := (continuous_S N).norm.pow 2
  have hi : IntegrableOn (fun α : ℝ => ‖S N α‖ ^ 2) (Set.Ioc (0 : ℝ) 1) :=
    hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hsub : Set.Ioc (0 : ℝ) 1 \ M ⊆ Set.Ioc (0 : ℝ) 1 := Set.sdiff_subset
  calc
    ‖∫ α in Set.Ioc (0 : ℝ) 1 \ M, F N α‖ ≤
        ∫ α in Set.Ioc (0 : ℝ) 1 \ M, B * ‖S N α‖ ^ 2 := by
      apply norm_integral_le_of_norm_le ((hi.mono_set hsub).const_mul B)
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.diff hM)] with α hα
      have he : ‖Complex.exp (-(2 * Real.pi * Complex.I * α * N))‖ = 1 := by
        simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
      rw [F, norm_mul, norm_pow, he, mul_one]
      calc ‖S N α‖ ^ 3 = ‖S N α‖ * ‖S N α‖ ^ 2 := by ring
           _ ≤ B * ‖S N α‖ ^ 2 := mul_le_mul_of_nonneg_right (hB α hα) (sq_nonneg _)
    _ = B * ∫ α in Set.Ioc (0 : ℝ) 1 \ M, ‖S N α‖ ^ 2 := integral_const_mul _ _
    _ ≤ B * ∫ α in Set.Ioc (0 : ℝ) 1, ‖S N α‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hB0
      exact setIntegral_mono_set hi (Filter.Eventually.of_forall fun α => sq_nonneg _)
        (Filter.Eventually.of_forall fun α hα => hsub hα)
    _ = _ := by rw [intervalIntegral.integral_of_le zero_le_one]

/-- LEAF. Unit U-1535. The sum of `(log p)^2` over primes `p ≤ N` is at most
`log N · θ(N)`; Liu-Wang 2002 p. 174, proof of Theorem 1. -/
theorem sum_log_sq_le (N : ℕ) :
    ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p ^ 2 ≤
      Real.log N * theta N := by
  unfold theta
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (Finset.mem_filter.mp hp).2
  have hpN : p ≤ N := by
    have := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    omega
  have hlog := Real.log_le_log (show (0 : ℝ) < p by exact_mod_cast hprime.pos)
    (show (p : ℝ) ≤ N by exact_mod_cast hpN)
  simpa only [pow_two] using mul_le_mul_of_nonneg_right hlog (Real.log_natCast_nonneg p)

/-- LEAF. Unit U-1535. Chebyshev's bound `θ(N) ≤ N log 4`, from the primorial bound
`∏_{p ≤ N} p ≤ 4^N`; a weaker form of the bound on Liu-Wang 2002 p. 174. -/
theorem theta_le (N : ℕ) : theta N ≤ Real.log 4 * N := by
  simpa only [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range,
    theta] using (Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity))

/-- LEAF. Unit U-1535. The trivial bound `|S(α)| ≤ θ(N)` by the triangle inequality;
Liu-Wang 2002 p. 168, below eq. 6.2. -/
theorem norm_S_le (N : ℕ) (α : ℝ) : ‖S N α‖ ≤ theta N := by
  unfold S theta
  apply norm_sum_le_of_le
  intro p hp
  have he : ‖Complex.exp (2 * Real.pi * Complex.I * α * p)‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_natCast_nonneg p)]

/-! ### Assemblies, zero sorry of their own -/

/-- `R3 N` is the real part of the circle integral over `(0, 1]`.
The orthogonality and finite circle identity inputs are proved above. -/
theorem r3_eq_re_integral (N : ℕ) : R3 N = (∫ α in Set.Ioc (0 : ℝ) 1, F N α).re := by
  have h := circle_identity_of_orth orth_int N
  rw [intervalIntegral.integral_of_le zero_le_one] at h
  rw [← h, Complex.ofReal_re]

/-- Major arcs against minor arcs: a lower bound `A` for the real part of the major arc
integral and a pointwise bound `B` for `|S|` off the major arcs with `B Σ (log p)^2 < A`
give `R3 N > 0`. The major and minor arc estimates remain explicit hypotheses. -/
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
The major and minor arc estimates remain explicit hypotheses. -/
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
`N ≥ C` give every odd `N ≥ C` as a sum of three primes.
The quantitative major and minor arc estimates are hypotheses. -/
theorem ternaryAbove_of_arcs {C : ℝ}
    (h : ∀ N : ℕ, Odd N → C ≤ N → ∃ M : Set ℝ, MeasurableSet M ∧ ∃ A B : ℝ, 0 ≤ B ∧
      A ≤ (∫ α in Set.Ioc (0 : ℝ) 1 ∩ M, F N α).re ∧
      (∀ α ∈ Set.Ioc (0 : ℝ) 1 \ M, ‖S N α‖ ≤ B) ∧
      B * (Real.log N * (Real.log 4 * N)) < A) :
    TernaryAbove C := by
  intro N ho hN
  obtain ⟨M, hM, A, B, hB0, hmaj, hmin, hAB⟩ := h N ho hN
  exact isTernarySum_of_r3_pos (r3_pos_of_arcs_log4 N hM hB0 hmaj hmin hAB)

/-- The weighted form gives the plain form. -/
theorem ternaryAbove_of_weighted {C : ℝ} (h : ChenWangWeighted C) : TernaryAbove C :=
  fun N ho hN => isTernarySum_of_r3_pos (h N ho hN)

/-- The weighted form is equivalent to the plain form. -/
theorem weighted_iff_ternaryAbove (C : ℝ) : ChenWangWeighted C ↔ TernaryAbove C :=
  ⟨ternaryAbove_of_weighted, chenWangWeighted_of_ternaryAbove⟩

/-- The prime sum has period one. Derived from Liu and Wang page 145 equation 3.10. -/
theorem periodic_S (N : ℕ) : Function.Periodic (S N) 1 := by
  intro α
  unfold S
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  have he : Complex.exp (2 * Real.pi * Complex.I * (p : ℂ)) = 1 := by
    rw [show 2 * Real.pi * Complex.I * (p : ℂ) =
      (p : ℂ) * (2 * Real.pi * Complex.I) by ring, Complex.exp_nat_mul,
      Complex.exp_two_pi_mul_I]
    simp
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((α + 1 : ℝ) : ℂ) * p =
    2 * Real.pi * Complex.I * α * p + 2 * Real.pi * Complex.I * p by push_cast; ring,
    Complex.exp_add, he, mul_one]


/-- The circle integrand has period one. Derived from Liu and Wang page 145 equation 3.10. -/
theorem periodic_F (N : ℕ) : Function.Periodic (F N) 1 := by
  intro α
  unfold F
  rw [periodic_S N α]
  congr 1
  have he : Complex.exp (-(2 * Real.pi * Complex.I * (N : ℂ))) = 1 := by
    rw [Complex.exp_neg, show 2 * Real.pi * Complex.I * (N : ℂ) =
      (N : ℂ) * (2 * Real.pi * Complex.I) by ring, Complex.exp_nat_mul,
      Complex.exp_two_pi_mul_I]
    simp
  rw [show -(2 * (Real.pi : ℂ) * Complex.I * ((α + 1 : ℝ) : ℂ) * N) =
    -(2 * Real.pi * Complex.I * α * N) + -(2 * Real.pi * Complex.I * N) by push_cast; ring,
    Complex.exp_add, he, mul_one]


/-- The prime weighted circle identity holds on every interval of length one.
Derived version of Liu and Wang page 145 equation 3.10 for the sealed prime sum. -/
theorem circle_identity_shifted (N : ℕ) (a : ℝ) :
    (R3 N : ℂ) = ∫ α in a..a + 1, F N α := by
  rw [(periodic_F N).intervalIntegral_add_eq a 0]
  simpa using circle_identity_of_orth orth_int N

/-- The prime power error in the exponential sum is at most twice square root N times log N.
Derived prime sum version of Liu and Wang page 145 below equation 3.10. -/
theorem norm_vonMangoldt_sum_sub_S_le (N : ℕ) (α : ℝ) :
    ‖(∑ n ∈ Finset.range (N + 1),
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * α * n)) - S N α‖ ≤
      2 * Real.sqrt N * Real.log N := by
  let w : ℕ → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n - if n.Prime then Real.log n else 0
  have hw (n : ℕ) : 0 ≤ w n := by
    dsimp [w]
    by_cases hp : n.Prime
    · rw [ite_eq_left hp, ArithmeticFunction.vonMangoldt_apply_prime hp, sub_self]
    · simpa only [hp, ite_false, sub_zero] using (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  have heq : (∑ n ∈ Finset.range (N + 1),
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * α * n)) - S N α =
      ∑ n ∈ Finset.range (N + 1), (w n : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * α * n) := by
    unfold S
    rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [w]
    split_ifs <;> push_cast <;> ring
  rw [heq]
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1), w n := by
      apply norm_sum_le_of_le
      intro n hn
      simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw n)]
    _ = ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n - theta N := by
      simp only [w, Finset.sum_sub_distrib, theta, Finset.sum_filter]
    _ ≤ _ := primePower_excess N

/-- Parseval on an arbitrary interval of length one. Derived prime sum version of
Liu and Wang page 174 and the periodic integration in page 145 equation 3.10. -/
theorem parseval_shifted (N : ℕ) (a : ℝ) :
    ∫ α in a..a + 1, ‖S N α‖ ^ 2 =
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p ^ 2 := by
  have hp : Function.Periodic (fun α : ℝ => ‖S N α‖ ^ 2) 1 := by
    intro α
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (periodic_S N α)
  rw [hp.intervalIntegral_add_eq a 0]
  simpa using parseval_of_orth orth_int N


/-- The explicit elementary minor arc budget. Derived weaker Chebyshev version of
Liu and Wang page 174. The pointwise minor arc estimate is an explicit hypothesis. -/
theorem minor_bound_log4 (N : ℕ) {M : Set ℝ} (hM : MeasurableSet M) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ M, ‖S N α‖ ≤ B) :
    ‖∫ α in Set.Ioc (0 : ℝ) 1 \ M, F N α‖ ≤
      B * (Real.log N * (Real.log 4 * N)) := by
  have h := minor_bound N hM hB0 hB
  rw [parseval_of_orth orth_int N] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hB0
  exact (sum_log_sq_le N).trans
    (mul_le_mul_of_nonneg_left (theta_le N) (Real.log_natCast_nonneg N))

/-- A trivial finite upper bound for the weighted prime triple count. Derived from
Liu and Wang page 145 equation 3.9 using the lab positive triple count.
This elementary upper bound is derived here and is not printed in the paper. -/
theorem r3_le_positive_triples_mul_log_cube (N : ℕ) :
    R3 N ≤ (((N - 1) * (N - 2) / 2 : ℕ) : ℝ) * Real.log N ^ 3 := by
  let T := ((Finset.range (N + 1) ×ˢ Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
    (fun x : ℕ × ℕ × ℕ => x.1.Prime ∧ x.2.1.Prime ∧ x.2.2.Prime ∧
      x.1 + x.2.1 + x.2.2 = N))
  let U := ((Finset.Icc 1 N ×ˢ Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
    (fun x : ℕ × ℕ × ℕ => x.1 + x.2.1 + x.2.2 = N))
  have hR : R3 N = ∑ x ∈ T, Real.log x.1 * Real.log x.2.1 * Real.log x.2.2 := by
    simp only [R3, T, Finset.sum_filter, Finset.sum_product]
  have hsub : T ⊆ U := by
    rintro ⟨p, q, r⟩ hx
    simp only [T, U, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_Icc] at hx ⊢
    rcases hx with ⟨⟨hpN, hqN, hrN⟩, hp, hq, hr, hs⟩
    exact ⟨⟨⟨hp.one_le, by omega⟩, ⟨hq.one_le, by omega⟩, ⟨hr.one_le, by omega⟩⟩, hs⟩
  have hL : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hb : ∀ x ∈ T, Real.log x.1 * Real.log x.2.1 * Real.log x.2.2 ≤ Real.log N ^ 3 := by
    rintro ⟨p, q, r⟩ hx
    simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
    rcases hx with ⟨⟨hpN, hqN, hrN⟩, hp, hq, hr, hs⟩
    have hl (p : ℕ) (hp : p.Prime) (hpN : p < N + 1) : Real.log p ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast (show p ≤ N by omega))
    calc
      Real.log p * Real.log q * Real.log r ≤ Real.log N * Real.log N * Real.log N :=
        mul_le_mul (mul_le_mul (hl p hp hpN) (hl q hq hqN)
          (Real.log_natCast_nonneg q) hL) (hl r hr hrN)
          (Real.log_natCast_nonneg r) (mul_nonneg hL hL)
      _ = _ := by ring
  calc
    R3 N = ∑ x ∈ T, Real.log x.1 * Real.log x.2.1 * Real.log x.2.2 := hR
    _ ≤ ∑ _x ∈ T, Real.log N ^ 3 := Finset.sum_le_sum hb
    _ = (T.card : ℝ) * Real.log N ^ 3 := by simp
    _ ≤ (U.card : ℝ) * Real.log N ^ 3 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (pow_nonneg hL 3)
    _ = _ := by rw [show U.card = (N - 1) * (N - 2) / 2 from triple_count N]

/-- Zero frequency is the total prime weight. Derived from Liu and Wang page 144
and the prime sum convention of State1535. -/
theorem S_zero (N : ℕ) : S N 0 = (theta N : ℂ) := by
  simp only [S, theta, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one,
    Complex.ofReal_sum]


/-- The triangle bound is attained at zero frequency. Derived from Liu and Wang page 168. -/
theorem norm_S_zero (N : ℕ) : ‖S N 0‖ = theta N := by
  have ht : 0 ≤ theta N := Finset.sum_nonneg fun p hp => Real.log_natCast_nonneg p
  rw [S_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]


/-- A global bound cannot improve theta. The minor arc restriction matters.
Derived from Liu and Wang pages 168 and 174 for the sealed prime sum. -/
theorem global_norm_bound_iff (N : ℕ) (B : ℝ) :
    (∀ α : ℝ, ‖S N α‖ ≤ B) ↔ theta N ≤ B := by
  constructor
  · intro h
    simpa only [norm_S_zero] using h 0
  · intro h α
    exact (norm_S_le N α).trans h


/-- A strict improvement over the global triangle bound forces the arc set to
contain the unit endpoint. Derived from Liu and Wang page 144 major arcs and page 174. -/
theorem one_mem_arcs_of_minor_lt_theta (N : ℕ) {M : Set ℝ} {B : ℝ}
    (hB : ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ M, ‖S N α‖ ≤ B) (hlt : B < theta N) : 1 ∈ M := by
  by_contra hM
  have h := hB 1 ⟨by norm_num, hM⟩
  have hp : S N 1 = S N 0 := by simpa using periodic_S N 0
  rw [hp, norm_S_zero] at h
  exact (not_le_of_gt hlt) h

/-- The prime power error bound survives every real lower cutoff. Derived from
Liu and Wang page 144 equation 3.8 and page 145 below equation 3.10. -/
theorem norm_truncated_vonMangoldt_sub_prime_le (N : ℕ) (c α : ℝ) :
    ‖(∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ => c * N ≤ n),
      (ArithmeticFunction.vonMangoldt n : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * α * n)) -
      ∑ p ∈ ((Finset.range (N + 1)).filter Nat.Prime).filter (fun p : ℕ => c * N ≤ p),
        (Real.log p : ℂ) * Complex.exp (2 * Real.pi * Complex.I * α * p)‖ ≤
      2 * Real.sqrt N * Real.log N := by
  let P := (Finset.range (N + 1)).filter (fun n : ℕ => c * N ≤ n)
  have hP : ((Finset.range (N + 1)).filter Nat.Prime).filter (fun p : ℕ => c * N ≤ p) =
      P.filter Nat.Prime := by
    ext n
    simp only [P, Finset.mem_filter]
    tauto
  rw [hP]
  let w : ℕ → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n - if n.Prime then Real.log n else 0
  have hw (n : ℕ) : 0 ≤ w n := by
    dsimp [w]
    by_cases hp : n.Prime
    · rw [ite_eq_left hp, ArithmeticFunction.vonMangoldt_apply_prime hp, sub_self]
    · simpa only [hp, ite_false, sub_zero] using (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  have heq : (∑ n ∈ P,
      (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * α * n)) -
      ∑ p ∈ P.filter Nat.Prime,
        (Real.log p : ℂ) * Complex.exp (2 * Real.pi * Complex.I * α * p) =
      ∑ n ∈ P, (w n : ℂ) * Complex.exp (2 * Real.pi * Complex.I * α * n) := by
    rw [Finset.sum_filter (s := P), ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [w]
    split_ifs <;> push_cast <;> ring
  change ‖(∑ n ∈ P, _) - ∑ p ∈ P.filter Nat.Prime, _‖ ≤ _
  rw [heq]
  calc
    _ ≤ ∑ n ∈ P, w n := by
      apply norm_sum_le_of_le
      intro n hn
      simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw n)]
    _ ≤ ∑ n ∈ Finset.range (N + 1), w n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n hn hnot => hw n)
    _ = ∑ n ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt n - theta N := by
      simp only [w, Finset.sum_sub_distrib, theta, Finset.sum_filter]
    _ ≤ _ := primePower_excess N

end LeanLab.Ternary.U1535
