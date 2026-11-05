/-
Elementary inputs to the periodic prime second moment in P0079 page 10.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.CountBounds293

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 4, definition of e. Every integer phase has character one. -/
theorem character_int353 (n : ℤ) : character293 n = 1 := by
  unfold character293
  convert Complex.exp_int_mul_two_pi_mul_I n using 1 <;> push_cast <;> ring

/-- P0079 page 4, definition of e. Negating the phase conjugates the character. -/
theorem character_neg353 (u : ℝ) :
    character293 (-u) = starRingEnd ℂ (character293 u) := by
  unfold character293
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- P0079 page 10, Section 5, the periodicity used in the tail estimate. -/
theorem primeSum_periodic353 (ε X : ℝ) : Function.Periodic (primeSum293 ε X) 1 := by
  intro α
  unfold primeSum293
  apply sum_congr rfl
  intro p hp
  rw [show (p : ℝ) * (α + 1) = (p : ℝ) * α + (p : ℝ) by ring, character_add293]
  have hp' : character293 (p : ℝ) = 1 := by exact_mod_cast character_int353 (p : ℤ)
  rw [hp', mul_one]

/-- P0079 page 4, display 11, and page 10, Section 5.
Integer characters are orthogonal on the centered interval of length one. -/
theorem character_orthogonality353 (n : ℤ) :
    (∫ α in -(1 / 2 : ℝ)..(1 / 2 : ℝ), character293 (α * n)) =
      if n = 0 then 1 else 0 := by
  rw [character_interval293]
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [if_neg hn]
    simp only [mul_one, one_mul]
    rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hn')]
    simp [mul_comm Real.pi, Real.sin_int_mul_pi]

/-- P0079 page 10, Section 5. Expanding the squared prime sum gives the
finite double sum of logarithmic weights and difference characters. -/
theorem prime_square_expansion353 (ε X α : ℝ) :
    (‖primeSum293 ε X α‖ ^ 2 : ℝ) =
      (∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)),
        ∑ q ∈ (range (⌊X⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧ ε * X ≤ (q : ℝ)),
          ((log p * log q : ℝ) : ℂ) * character293 (((p : ℝ) - q) * α)).re := by
  have heq : ((‖primeSum293 ε X α‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)),
        ∑ q ∈ (range (⌊X⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧ ε * X ≤ (q : ℝ)),
          ((log p * log q : ℝ) : ℂ) * character293 (((p : ℝ) - q) * α) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    unfold primeSum293
    simp only [map_sum, map_mul, Complex.conj_ofReal]
    rw [Finset.sum_mul_sum]
    apply sum_congr rfl
    intro p hp
    apply sum_congr rfl
    intro q hq
    rw [← character_neg353, sub_mul, sub_eq_add_neg, character_add293]
    push_cast
    ring
  exact congrArg Complex.re heq

/-- P0079 page 10, Section 5. Termwise orthogonality removes every off-diagonal
term in the integral of a finite weighted difference-character sum. -/
theorem weighted_difference_integral353 (T : Finset ℕ) (w : ℕ → ℝ) :
    (∫ α in -(1 / 2 : ℝ)..(1 / 2 : ℝ), ∑ p ∈ T, ∑ q ∈ T,
      ((w p * w q : ℝ) : ℂ) * character293 (((p : ℝ) - q) * α)) =
        ((∑ p ∈ T, (w p) ^ 2 : ℝ) : ℂ) := by
  have hterm (p q : ℕ) :
      (∫ α in -(1 / 2 : ℝ)..(1 / 2 : ℝ),
        ((w p * w q : ℝ) : ℂ) * character293 (((p : ℝ) - q) * α)) =
          if p = q then (((w p) ^ 2 : ℝ) : ℂ) else 0 := by
    rw [intervalIntegral.integral_const_mul]
    have hphase : (fun α : ℝ => character293 (((p : ℝ) - q) * α)) =
        (fun α : ℝ => character293 (α * (((p : ℤ) - (q : ℤ) : ℤ) : ℝ))) := by
      funext α
      congr 1
      push_cast
      ring
    rw [hphase, character_orthogonality353]
    by_cases hpq : p = q
    · subst q
      simp [pow_two]
    · have hne : (p : ℤ) - q ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hpq)
      simp [hpq, hne]
  have hc (p q : ℕ) : Continuous (fun α : ℝ =>
      ((w p * w q : ℝ) : ℂ) * character293 (((p : ℝ) - q) * α)) := by
    unfold character293
    fun_prop
  have hcs (p : ℕ) : Continuous (fun α : ℝ => ∑ q ∈ T,
      ((w p * w q : ℝ) : ℂ) * character293 (((p : ℝ) - q) * α)) :=
    continuous_finset_sum _ (fun q hq => hc p q)
  rw [intervalIntegral.integral_finsetSum (fun p hp => (hcs p).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_finsetSum (fun q hq => (hc _ q).intervalIntegrable _ _)]
  simp_rw [hterm]
  simp

/-- P0079 page 10, Section 5. The unweighted unit-interval prime second
moment equals the sum of squared logarithmic weights over the primes in the box. -/
theorem prime_second_moment353 (ε X : ℝ) :
    (∫ α in -(1 / 2 : ℝ)..(1 / 2 : ℝ), ‖primeSum293 ε X α‖ ^ 2) =
      ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)),
        (log p) ^ 2 := by
  simp_rw [prime_square_expansion353]
  have hc : Continuous (fun α : ℝ =>
      ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)),
        ∑ q ∈ (range (⌊X⌋₊ + 1)).filter (fun q : ℕ => q.Prime ∧ ε * X ≤ (q : ℝ)),
          ((log p * log q : ℝ) : ℂ) * character293 (((p : ℝ) - q) * α)) := by
    unfold character293
    fun_prop
  have hr := Complex.reCLM.intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) (-(1 / 2 : ℝ)) (1 / 2 : ℝ))
  simp only [Complex.reCLM_apply] at hr
  rw [hr]
  rw [weighted_difference_integral353]
  rfl

/-- P0079 page 10, Section 5. Chebyshev's bound suffices for the prime
second moment bound of order X log X, without a prime number theorem input. -/
theorem prime_second_moment_le353 (ε X : ℝ) (hX : 2 ≤ X) :
    (∫ α in -(1 / 2 : ℝ)..(1 / 2 : ℝ), ‖primeSum293 ε X α‖ ^ 2) ≤
      log 4 * X * log X := by
  let P := (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ))
  let Q := (Ioc 0 ⌊X⌋₊).filter (fun p : ℕ => p.Prime)
  have hsub : P ⊆ Q := by
    intro p hp
    have hp' := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp'.2.1.pos, Nat.le_of_lt_succ (mem_range.mp hp'.1)⟩,
      hp'.2.1⟩
  have hlogX : 0 ≤ log X := log_nonneg (by linarith)
  rw [prime_second_moment353]
  change ∑ p ∈ P, log p ^ 2 ≤ _
  calc
    _ ≤ log X * ∑ p ∈ P, log p := by
      rw [mul_sum]
      apply sum_le_sum
      intro p hp
      have hp' := (mem_filter.mp hp).2.1
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp'.one_lt.le
      have hpX : (p : ℝ) ≤ X :=
        (by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hp).1) :
          (p : ℝ) ≤ ⌊X⌋₊).trans (Nat.floor_le (by linarith))
      have hlogp := log_nonneg hp1
      have hlogpX := log_le_log (by linarith : (0 : ℝ) < p) hpX
      nlinarith
    _ ≤ log X * Chebyshev.theta X := by
      apply mul_le_mul_of_nonneg_left _ hlogX
      change ∑ p ∈ P, log p ≤ ∑ p ∈ Q, log p
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro p hp hp'
      exact log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_lt.le)
    _ ≤ log X * (log 4 * X) := mul_le_mul_of_nonneg_left
      (Chebyshev.theta_le_log4_mul_x (by linarith)) hlogX
    _ = _ := by ring

/-- P0079 page 10, Section 5. Periodicity makes the exact prime second
moment the same on every translated unit interval. -/
theorem prime_second_moment_unit353 (ε X t : ℝ) :
    (∫ α in t..t + 1, ‖primeSum293 ε X α‖ ^ 2) =
      ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)),
        (log p) ^ 2 := by
  have hp : Function.Periodic (fun α : ℝ => ‖primeSum293 ε X α‖ ^ 2) 1 := by
    intro α
    change ‖primeSum293 ε X (α + 1)‖ ^ 2 = ‖primeSum293 ε X α‖ ^ 2
    rw [(primeSum_periodic353 ε X) α]
  have H := hp.intervalIntegral_add_eq t (-(1 / 2 : ℝ))
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at H
  exact H.trans (prime_second_moment353 ε X)

/-- P0079 page 10, Section 5, the estimate on each positive unit interval.
The kernel decay and the exact periodic moment give an explicit inverse-square bound. -/
theorem primeMoment_unit_le353 (ε X η a : ℝ) (hX : 2 ≤ X) (ha : 0 < a) :
    (∫ α in a..a + 1, ‖primeSum293 ε X α‖ ^ 2 * kernel293 η α) ≤
      ((1 / Real.pi ^ 2) / a ^ 2) * (log 4 * X * log X) := by
  have hk : ∀ α ∈ Set.Icc a (a + 1), kernel293 η α ≤ (1 / Real.pi ^ 2) / a ^ 2 := by
    intro α hα
    apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
    have hsq : a ^ 2 ≤ α ^ 2 := by nlinarith [hα.1]
    have hkn := kernel_nonneg293 η α
    have hdec := kernel_mul_sq_le293 η α
    nlinarith
  have hs : Continuous (fun α : ℝ => ‖primeSum293 ε X α‖ ^ 2) := by
    unfold primeSum293 character293
    fun_prop
  have hker : Continuous (kernel293 η) := by unfold kernel293; fun_prop
  calc
    _ ≤ ∫ α in a..a + 1, ((1 / Real.pi ^ 2) / a ^ 2) * ‖primeSum293 ε X α‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((hs.mul hker).intervalIntegrable _ _)
        ((hs.const_mul _).intervalIntegrable _ _)
      intro α hα
      change ‖primeSum293 ε X α‖ ^ 2 * kernel293 η α ≤
        ((1 / Real.pi ^ 2) / a ^ 2) * ‖primeSum293 ε X α‖ ^ 2
      calc
        _ ≤ ‖primeSum293 ε X α‖ ^ 2 * ((1 / Real.pi ^ 2) / a ^ 2) :=
          mul_le_mul_of_nonneg_left (hk α hα) (sq_nonneg _)
        _ = _ := mul_comm _ _
    _ = ((1 / Real.pi ^ 2) / a ^ 2) *
        (∫ α in -(1 / 2 : ℝ)..(1 / 2 : ℝ), ‖primeSum293 ε X α‖ ^ 2) := by
      rw [intervalIntegral.integral_const_mul, prime_second_moment_unit353,
        prime_second_moment353]
    _ ≤ _ := mul_le_mul_of_nonneg_left (prime_second_moment_le353 ε X hX) (by positivity)

end LeanLab.LZPowersOfTwo
