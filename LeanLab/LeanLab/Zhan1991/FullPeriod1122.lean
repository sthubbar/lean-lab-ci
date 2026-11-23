import LeanLab.Zhan1991.SingIntegral1122

/-!
P0068 Zhan 1991, page 271, the full period identity of the singular integral, PROVED: the
integral of `v(λ)³ e(-Nλ)` over `[-1/2, 1/2]` is the weighted count of window triples with
`n₁ + n₂ + n₃ = N`. It closes the LEAF `fullPeriodIdentity_leaf` of SingIntegral1122 by a
separate proof, without editing that file. burst-20261122, session S80.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991
open Real MeasureTheory

/-- `∫_{-1/2}^{1/2} e(kλ) dλ` is `1` for `k = 0` and `0` for every other integer `k`. PROVED. -/
theorem ee_integral_half (k : ℤ) :
    (∫ lam in (-(1 / 2 : ℝ))..(1 / 2), ee ((k : ℝ) * lam)) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp [ee]; norm_num
  · have hz : (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hk)
    have he : ∀ α : ℝ, ee ((k : ℝ) * α) =
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) * (α : ℂ)) := by
      intro α; simp only [ee, Complex.ofReal_mul, Complex.ofReal_intCast]; congr 1; ring
    simp_rw [he]
    rw [integral_exp_mul_complex hz]
    have h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((1 / 2 : ℝ) : ℂ)) =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((-(1 / 2 : ℝ)) : ℂ)) := by
      rw [Complex.exp_eq_exp_iff_exists_int]
      exact ⟨k, by push_cast; ring⟩
    rw [h1]; push_cast; simp

/-- `v(λ)³ e(-Nλ)` expanded over window triples. PROVED. -/
theorem singIntegrand_expand (N : ℕ) (U lam : ℝ) :
    singIntegrand N U lam =
      ∑ n₁ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
        ∑ n₂ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
          ∑ n₃ ∈ Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊,
            ((1 / (Real.log n₁ * Real.log n₂ * Real.log n₃) : ℝ) : ℂ) *
              ee ((((n₁ + n₂ + n₃ : ℤ) - N : ℤ) : ℝ) * lam) := by
  unfold singIntegrand vSum
  simp only [pow_three, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro n₁ _
  apply Finset.sum_congr rfl; intro n₂ _
  apply Finset.sum_congr rfl; intro n₃ _
  have hE : ee ((((n₁ + n₂ + n₃ : ℤ) - N : ℤ) : ℝ) * lam) =
      ee ((n₁ : ℝ) * lam) * ee ((n₂ : ℝ) * lam) * ee ((n₃ : ℝ) * lam) * ee (-(N : ℝ) * lam) := by
    rw [← ee_add110, ← ee_add110, ← ee_add110]; congr 1; push_cast; ring
  rw [hE]
  push_cast
  ring

/-- Page 271, orthogonality over one period: `FullPeriodIdentity`. PROVED. -/
theorem fullPeriodIdentity_proof : FullPeriodIdentity := by
  intro N U
  set W := Finset.Icc ⌈(N : ℝ) / 3 - U⌉₊ ⌊(N : ℝ) / 3 + U⌋₊
  have hc : ∀ (k : ℤ) (c : ℝ), IntervalIntegrable (fun lam : ℝ => (c : ℂ) * ee ((k : ℝ) * lam))
      volume (-(1 / 2 : ℝ)) (1 / 2) := by
    intro k c
    apply Continuous.intervalIntegrable
    unfold ee; fun_prop
  have hterm : ∀ n₁ n₂ n₃ : ℕ,
      (∫ lam in (-(1 / 2 : ℝ))..(1 / 2),
        ((1 / (Real.log n₁ * Real.log n₂ * Real.log n₃) : ℝ) : ℂ) *
          ee ((((n₁ + n₂ + n₃ : ℤ) - N : ℤ) : ℝ) * lam)).re =
      if n₁ + n₂ + n₃ = N then 1 / (Real.log n₁ * Real.log n₂ * Real.log n₃) else 0 := by
    intro n₁ n₂ n₃
    rw [intervalIntegral.integral_const_mul, ee_integral_half]
    by_cases h : n₁ + n₂ + n₃ = N
    · have h0 : ((n₁ + n₂ + n₃ : ℤ) - N : ℤ) = 0 := by omega
      rw [if_pos h0, if_pos h, mul_one, Complex.ofReal_re]
    · have h0 : ((n₁ + n₂ + n₃ : ℤ) - N : ℤ) ≠ 0 := by omega
      rw [if_neg h0, if_neg h, mul_zero, Complex.zero_re]
  simp_rw [singIntegrand_expand]
  rw [intervalIntegral.integral_finsetSum (fun n₁ _ => ?_)]
  · rw [Complex.re_sum]
    unfold weightedTriples
    apply Finset.sum_congr rfl; intro n₁ _
    rw [intervalIntegral.integral_finsetSum (fun n₂ _ => ?_), Complex.re_sum]
    · apply Finset.sum_congr rfl; intro n₂ _
      rw [intervalIntegral.integral_finsetSum (fun n₃ _ => hc _ _), Complex.re_sum]
      apply Finset.sum_congr rfl; intro n₃ _
      exact hterm n₁ n₂ n₃
    · apply Continuous.intervalIntegrable; unfold ee; fun_prop
  · apply Continuous.intervalIntegrable; unfold ee; fun_prop

/-- Step 3 of the major arc split with the full period identity PROVED. -/
theorem singIntEval_split_p6 : SingIntEval :=
  singIntEval_of_parts fullPeriodIdentity_proof weightedTriplesEval_leaf singIntTail_leaf

end LeanLab.Zhan1991
