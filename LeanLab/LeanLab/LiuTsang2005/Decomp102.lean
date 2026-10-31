/-
Liu and Tsang 2005, P0081. Section 2, p. 82, equation 2.7.
This file proves the missing minor arc term, the mean-value and Schwarz estimates,
and the exact weighted prime circle identity.
AI wrote the Lean code. Binary Goldbach stays open.
-/
import LeanLab.LiuTsang2005.Decomp1533b
import LeanLab.LiuTsang2005.Decomp1533c

namespace LeanLab.LiuTsang2005.Decomp102
open Real Complex intervalIntegral MeasureTheory Decomp1533c

/-- LEAF. P0081 p. 82, equation 2.7. The middle term is bounded by the common
minor arc factor. The assumptions A and a at least 1 follow from the paper's
integer coefficients and the definition of A. -/
theorem eq27_second (N A a : ℝ) (hN : 0 < N) (hA : 1 ≤ A) (ha : 1 ≤ a) :
    (N / a) ^ (4 / 5 : ℝ) ≤ N / Real.sqrt (a * (N / A) ^ (2 / 5 : ℝ)) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hp : 0 < (N / A) ^ (2 / 5 : ℝ) := by positivity
  have hroot : Real.sqrt ((N / A) ^ (2 / 5 : ℝ)) ≤ N ^ (1 / 5 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (div_pos hN hA0).le]
    norm_num
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    exact div_le_self hN.le hA
  have hfactor : (N / a) ^ (4 / 5 : ℝ) ≤ N ^ (4 / 5 : ℝ) / Real.sqrt a := by
    rw [Real.div_rpow hN.le ha0.le, Real.sqrt_eq_rpow]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le ha (by norm_num)
  rw [le_div_iff₀ (Real.sqrt_pos.mpr (mul_pos ha0 hp)), Real.sqrt_mul ha0.le]
  calc
    _ ≤ (N ^ (4 / 5 : ℝ) / Real.sqrt a) * (Real.sqrt a * Real.sqrt ((N / A) ^ (2 / 5 : ℝ))) :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ = N ^ (4 / 5 : ℝ) * Real.sqrt ((N / A) ^ (2 / 5 : ℝ)) := by
      field_simp
    _ ≤ N ^ (4 / 5 : ℝ) * N ^ (1 / 5 : ℝ) := by gcongr
    _ = N := by rw [← Real.rpow_add hN]; norm_num

/-- P0081 p. 82, equation 2.7. All three terms are at most the common factor,
so their sum has explicit constant 3. -/
theorem eq27_three_terms (N A a L : ℝ) (hN : 0 < N) (hA : 1 ≤ A)
    (ha : 1 ≤ a) (hL : 1 ≤ L) :
    L ^ 4 * (N / a * ((N / A) ^ (2 / 5 : ℝ)) ^ (-(1 / 2) : ℝ) * a ^ (1 / 2 : ℝ) +
      (N / a) ^ (4 / 5 : ℝ) + Real.sqrt (N / a) *
        Real.sqrt (N / (((N / A) ^ (2 / 5 : ℝ)) * L ^ 2))) ≤
      3 * (N * L ^ 4 / Real.sqrt (a * (N / A) ^ (2 / 5 : ℝ))) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hP : 0 < (N / A) ^ (2 / 5 : ℝ) := by positivity
  rw [Decomp1533b.eq27_first N a _ ha0 hP]
  have h2 := eq27_second N A a hN hA ha
  have h3 := Decomp1533b.eq27_third N a _ L hN ha0 hP hL
  calc
    _ ≤ L ^ 4 * (N / Real.sqrt (a * (N / A) ^ (2 / 5 : ℝ)) +
      N / Real.sqrt (a * (N / A) ^ (2 / 5 : ℝ)) + N / Real.sqrt (a * (N / A) ^ (2 / 5 : ℝ))) := by
      gcongr
    _ = _ := by ring

/-- P0081 p. 82, mean-value step before equation 2.8. Orthogonality gives
an exact identity for real weights. The paper uses w p = log p on a prime index set. -/
theorem weighted_mean_square (a : ℕ) (ha : 0 < a) (s : Finset ℕ) (w : ℕ → ℝ) :
    (∫ lam in (-(1 / 2 : ℝ))..(1 / 2),
      ‖∑ m ∈ s, (w m : ℂ) * eF ((a : ℝ) * m * lam)‖ ^ 2) = ∑ m ∈ s, w m ^ 2 := by
  classical
  have hx (lam : ℝ) :
      ((‖∑ m ∈ s, (w m : ℂ) * eF ((a : ℝ) * m * lam)‖ ^ 2 : ℝ) : ℂ) =
        ∑ m ∈ s, ∑ m' ∈ s, ((w m * w m' : ℝ) : ℂ) *
          eF (((a : ℝ) * m - a * m') * lam) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m' hm'
    simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    rw [mul_mul_mul_comm]
    congr 1
    unfold eF
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    push_cast
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast]
    ring
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hx]
  rw [intervalIntegral.integral_finsetSum (fun m hm =>
    Continuous.intervalIntegrable (by unfold eF; fun_prop) _ _)]
  calc
    _ = ∑ m ∈ s, ∑ m' ∈ s, ((w m * w m' : ℝ) : ℂ) *
        (if m = m' then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [intervalIntegral.integral_finsetSum (fun m' hm' =>
        Continuous.intervalIntegrable (by unfold eF; fun_prop) _ _)]
      apply Finset.sum_congr rfl
      intro m' hm'
      rw [intervalIntegral.integral_const_mul, orth_long a ha]
    _ = _ := by simp [mul_ite, Finset.sum_ite_eq, pow_two]

/-- P0081 p. 82, mean-value step before equation 2.8. A finite prime log-square
sum is bounded using Mathlib's proved Chebyshev theta upper bound. -/
theorem prime_log_sq_sum_le (s : Finset ℕ) (N x : ℝ) (hN : 1 ≤ N) (hx : 0 ≤ x) (hxN : x ≤ N)
    (hs : ∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ x) :
    ∑ p ∈ s, (Real.log p) ^ 2 ≤ Real.log 4 * x * Real.log N := by
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hsub : s ⊆ Nat.primesLE ⌊x⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hx).mpr (hs p hp).2, (hs p hp).1⟩
  have hsum : ∑ p ∈ s, Real.log p ≤ Chebyshev.theta x := by
    rw [Chebyshev.theta_eq_sum_primesLE]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ =>
      Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le))
  calc
    ∑ p ∈ s, Real.log p ^ 2 ≤ (Real.log N) * ∑ p ∈ s, Real.log p := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hs p hp).1.pos
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hs p hp).1.one_le
      have hpN : Real.log p ≤ Real.log N := Real.log_le_log hp0 (le_trans (hs p hp).2 hxN)
      simpa [pow_two] using (mul_le_mul_of_nonneg_right hpN (Real.log_nonneg hp1))
    _ ≤ Real.log N * Chebyshev.theta x := mul_le_mul_of_nonneg_left hsum hlog
    _ ≤ Real.log N * (Real.log 4 * x) :=
      mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x hx) hlog
    _ = _ := by ring

/-- P0081 p. 82, mean-value estimate before equation 2.8, on the centered
unit interval. The explicit absolute constant is log 4. -/
theorem prime_mean_value (a : ℕ) (ha : 0 < a) (M N : ℝ) (hN : 1 ≤ N) :
    (∫ lam in (-(1 / 2 : ℝ))..(1 / 2),
      ‖∑ p ∈ (idx a M N).filter Nat.Prime,
        (Real.log p : ℂ) * eF ((a : ℝ) * p * lam)‖ ^ 2) ≤
      Real.log 4 * (N / a) * Real.log N := by
  rw [weighted_mean_square a ha]
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  apply prime_log_sq_sum_le _ N (N / a) hN (by positivity)
    (div_le_self (by linarith) ha1)
  intro p hp
  have hpidx := Finset.mem_filter.mp hp
  refine ⟨hpidx.2, ?_⟩
  rw [le_div_iff₀ ha0]
  simpa [mul_comm] using (Finset.mem_filter.mp hpidx.1).2.2

/-- P0081 p. 82, mean-value step before equation 2.8. The exact weighted
identity holds on every translated unit interval by periodicity. -/
theorem weighted_mean_square_unit (a : ℕ) (ha : 0 < a) (s : Finset ℕ) (w : ℕ → ℝ) (u : ℝ) :
    (∫ lam in u..u + 1,
      ‖∑ m ∈ s, (w m : ℂ) * eF ((a : ℝ) * m * lam)‖ ^ 2) = ∑ m ∈ s, w m ^ 2 := by
  have hp : Function.Periodic (fun lam : ℝ => ∑ m ∈ s, (w m : ℂ) * eF ((a : ℝ) * m * lam)) 1 := by
    intro lam
    apply Finset.sum_congr rfl
    intro m hm
    congr 1
    unfold eF
    apply Complex.exp_eq_exp_iff_exists_int.mpr
    refine ⟨(a : ℤ) * m, ?_⟩
    push_cast
    ring
  have hnorm : Function.Periodic (fun lam : ℝ => ‖∑ m ∈ s, (w m : ℂ) * eF ((a : ℝ) * m * lam)‖ ^ 2) 1 := by
    intro lam
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) (hp lam)
  rw [hnorm.intervalIntegral_add_eq u (-(1 / 2 : ℝ)), show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]
  exact weighted_mean_square a ha s w

/-- P0081 p. 82, mean-value estimate before equation 2.8. Set u = 1/Q
to recover the paper's interval. The constant is log 4. -/
theorem prime_mean_value_unit (a : ℕ) (ha : 0 < a) (M N u : ℝ) (hN : 1 ≤ N) :
    (∫ lam in u..u + 1,
      ‖∑ p ∈ (idx a M N).filter Nat.Prime,
        (Real.log p : ℂ) * eF ((a : ℝ) * p * lam)‖ ^ 2) ≤
      Real.log 4 * (N / a) * Real.log N := by
  rw [weighted_mean_square_unit a ha]
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  apply prime_log_sq_sum_le _ N (N / a) hN (by positivity)
    (div_le_self (by linarith) ha1)
  intro p hp
  have hpidx := Finset.mem_filter.mp hp
  refine ⟨hpidx.2, ?_⟩
  rw [le_div_iff₀ ha0]
  simpa [mul_comm] using (Finset.mem_filter.mp hpidx.1).2.2

/-- P0081 p. 82, equation 2.8. The product of the two prime exponential
sums has unit-interval L1 norm at most log 4 times L N divided by sqrt a1 a2.
The mean-square inputs and Holder inequality are proved in the library. -/
theorem eq28_prime_schwarz (a₁ a₂ : ℕ) (h1 : 0 < a₁) (h2 : 0 < a₂) (M N u : ℝ) (hN : 1 ≤ N) :
    (∫ lam in u..u + 1,
      ‖(∑ p ∈ (idx a₁ M N).filter Nat.Prime, (Real.log p : ℂ) * eF ((a₁ : ℝ) * p * lam)) *
        (∑ p ∈ (idx a₂ M N).filter Nat.Prime, (Real.log p : ℂ) * eF ((a₂ : ℝ) * p * lam))‖) ≤
      Real.log 4 * (Real.log N * N / Real.sqrt ((a₁ : ℝ) * a₂)) := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hN0 : 0 ≤ N := by linarith
  let f := fun lam : ℝ => ∑ p ∈ (idx a₁ M N).filter Nat.Prime,
    (Real.log p : ℂ) * eF ((a₁ : ℝ) * p * lam)
  let g := fun lam : ℝ => ∑ p ∈ (idx a₂ M N).filter Nat.Prime,
    (Real.log p : ℂ) * eF ((a₂ : ℝ) * p * lam)
  have hf : Continuous f := by unfold f eF; fun_prop
  have hg : Continuous g := by unfold g eF; fun_prop
  let μ := volume.restrict (Set.Ioc u (u + 1))
  have hfMem : MemLp f 2 μ := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
    ((hf.norm.pow 2).intervalIntegrable u (u + 1)).1
  have hgMem : MemLp g 2 μ := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mpr
    ((hg.norm.pow 2).intervalIntegrable u (u + 1)).1
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (p := 2) (q := 2)
    (by norm_num [Real.holderConjugate_iff]) (by simpa using hfMem) (by simpa using hgMem)
  have hcs : (∫ lam in u..u + 1, ‖f lam * g lam‖) ≤
      Real.sqrt (∫ lam in u..u + 1, ‖f lam‖ ^ 2) * Real.sqrt (∫ lam in u..u + 1, ‖g lam‖ ^ 2) := by
    simpa only [μ, intervalIntegral.integral_of_le (by linarith : u ≤ u + 1),
      norm_mul, Real.rpow_two, ← Real.sqrt_eq_rpow] using hholder
  have hb1 : (∫ lam in u..u + 1, ‖f lam‖ ^ 2) ≤ Real.log 4 * (N / a₁) * Real.log N :=
    prime_mean_value_unit a₁ h1 M N u hN
  have hb2 : (∫ lam in u..u + 1, ‖g lam‖ ^ 2) ≤ Real.log 4 * (N / a₂) * Real.log N :=
    prime_mean_value_unit a₂ h2 M N u hN
  calc
    _ ≤ Real.sqrt (Real.log 4 * (N / a₁) * Real.log N) *
        Real.sqrt (Real.log 4 * (N / a₂) * Real.log N) := by
      exact hcs.trans (mul_le_mul (Real.sqrt_le_sqrt hb1) (Real.sqrt_le_sqrt hb2)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = _ := by
      rw [← Real.sqrt_mul (by positivity)]
      have he : Real.log 4 * (N / a₁) * Real.log N *
          (Real.log 4 * (N / a₂) * Real.log N) =
          (Real.log 4 * Real.log N * N) ^ 2 / ((a₁ : ℝ) * a₂) := by ring
      rw [he, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (by positivity)]
      ring

/-- P0081 p. 81, definition of the signed prime exponential sum Sj. -/
noncomputable def Sprime (a : ℤ) (M N lam : ℝ) : ℂ :=
  ∑ p ∈ (idx a.natAbs M N).filter Nat.Prime, (Real.log p : ℂ) * eF ((a : ℝ) * p * lam)
/-- P0081 pp. 81 and 82. Negating a coefficient conjugates its prime sum. -/
theorem Sprime_neg (a : ℤ) (M N lam : ℝ) : Sprime (-a) M N lam = (starRingEnd ℂ) (Sprime a M N lam) := by
  unfold Sprime
  simp only [Int.natAbs_neg, map_sum, map_mul, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  unfold eF
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_intCast]
  ring

/-- P0081 pp. 81 and 82. The norm of the signed prime sum depends only
on the absolute value of its integer coefficient. -/
theorem norm_Sprime_eq_natAbs (a : ℤ) (M N lam : ℝ) : ‖Sprime a M N lam‖ = ‖Sprime (a.natAbs : ℤ) M N lam‖ := by
  have habs := Int.natCast_natAbs a
  by_cases h : 0 ≤ a
  · have he : (a.natAbs : ℤ) = a := by simpa [abs_of_nonneg h] using habs
    rw [he]
  · have he : (a.natAbs : ℤ) = -a := by simpa [abs_of_neg (lt_of_not_ge h)] using habs
    rw [he, Sprime_neg, Complex.norm_conj]

/-- P0081 p. 82, mean-value estimate before equation 2.8 for every nonzero
integer coefficient, on the exact translated unit interval of the paper. -/
theorem signed_prime_mean_value (a : ℤ) (ha : a ≠ 0) (M N u : ℝ) (hN : 1 ≤ N) :
    (∫ lam in u..u + 1, ‖Sprime a M N lam‖ ^ 2) ≤
      Real.log 4 * (N / a.natAbs) * Real.log N := by
  simp_rw [norm_Sprime_eq_natAbs a]
  simpa only [Sprime, Int.natAbs_natCast, Int.cast_natCast] using
    prime_mean_value_unit a.natAbs (Int.natAbs_pos.mpr ha) M N u hN

/-- P0081 p. 82, equation 2.8, for arbitrary nonzero integer coefficients.
The explicit constant is log 4. -/
theorem eq28_signed_schwarz (a₁ a₂ : ℤ) (h1 : a₁ ≠ 0) (h2 : a₂ ≠ 0) (M N u : ℝ) (hN : 1 ≤ N) :
    (∫ lam in u..u + 1, ‖Sprime a₁ M N lam * Sprime a₂ M N lam‖) ≤
      Real.log 4 * (Real.log N * N / Real.sqrt ((a₁.natAbs : ℝ) * a₂.natAbs)) := by
  simp_rw [norm_mul, norm_Sprime_eq_natAbs a₁, norm_Sprime_eq_natAbs a₂]
  simpa only [Sprime, Int.natAbs_natCast, Int.cast_natCast, norm_mul] using
    eq28_prime_schwarz a₁.natAbs a₂.natAbs (Int.natAbs_pos.mpr h1) (Int.natAbs_pos.mpr h2) M N u hN

/-- P0081 p. 81, orthogonality used in equation 2.3. An integer frequency
integrates to zero on a unit interval unless the frequency is zero. -/
theorem integral_eF_int_unit (k : ℤ) (u : ℝ) :
    (∫ lam in u..u + 1, eF ((k : ℝ) * lam)) = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [eF]
  · rw [if_neg hk]
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hc : 2 * (π : ℂ) * I * k ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) hkC
    simp only [eF, Complex.ofReal_mul, Complex.ofReal_intCast]
    simp_rw [← mul_assoc]
    rw [integral_exp_mul_complex hc]
    have he : Complex.exp (2 * (π : ℂ) * I * k * (u + 1 : ℝ)) =
        Complex.exp (2 * (π : ℂ) * I * k * u) := by
      apply Complex.exp_eq_exp_iff_exists_int.mpr
      refine ⟨k, ?_⟩
      push_cast
      ring
    rw [he, sub_self, zero_div]

/-- P0081 p. 81, equation 2.3. The full unit-interval circle integral equals
the weighted number of prime solutions. The equation is written in complex numbers. -/
theorem eq23_circle_identity (a₁ a₂ a₃ n : ℤ) (h1 : a₁ ≠ 0) (h2 : a₂ ≠ 0) (h3 : a₃ ≠ 0) (M N u : ℝ) :
    (∫ lam in u..u + 1, Sprime a₁ M N lam * Sprime a₂ M N lam * Sprime a₃ M N lam *
      eF (-(n : ℝ) * lam)) =
    ∑ p₁ ∈ (idx a₁.natAbs M N).filter Nat.Prime,
      ∑ p₂ ∈ (idx a₂.natAbs M N).filter Nat.Prime,
        ∑ p₃ ∈ (idx a₃.natAbs M N).filter Nat.Prime,
          if a₁ * p₁ + a₂ * p₂ + a₃ * p₃ = n then
            ((Real.log p₁ * Real.log p₂ * Real.log p₃ : ℝ) : ℂ) else 0 := by
  have he (x y : ℝ) : eF x * eF y = eF (x + y) := by
    unfold eF
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hx (lam : ℝ) :
      Sprime a₁ M N lam * Sprime a₂ M N lam * Sprime a₃ M N lam * eF (-(n : ℝ) * lam) =
        ∑ p₁ ∈ (idx a₁.natAbs M N).filter Nat.Prime,
          ∑ p₂ ∈ (idx a₂.natAbs M N).filter Nat.Prime,
            ∑ p₃ ∈ (idx a₃.natAbs M N).filter Nat.Prime,
              ((Real.log p₁ * Real.log p₂ * Real.log p₃ : ℝ) : ℂ) *
                eF (((a₁ * p₁ + a₂ * p₂ + a₃ * p₃ - n : ℤ) : ℝ) * lam) := by
    unfold Sprime
    simp_rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p₁ hp₁
    conv_lhs => arg 1; arg 1; rw [Finset.mul_sum]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p₂ hp₂
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p₃ hp₃
    calc
      _ = ((Real.log p₁ * Real.log p₂ * Real.log p₃ : ℝ) : ℂ) *
          (eF ((a₁ : ℝ) * p₁ * lam) * eF ((a₂ : ℝ) * p₂ * lam) *
            eF ((a₃ : ℝ) * p₃ * lam) * eF (-(n : ℝ) * lam)) := by push_cast; ring
      _ = _ := by
        rw [he, he, he]
        congr 1
        congr 1
        push_cast
        ring
  simp_rw [hx]
  rw [intervalIntegral.integral_finsetSum (fun p₁ hp₁ =>
    Continuous.intervalIntegrable (by unfold eF; fun_prop) _ _)]
  apply Finset.sum_congr rfl
  intro p₁ hp₁
  rw [intervalIntegral.integral_finsetSum (fun p₂ hp₂ =>
    Continuous.intervalIntegrable (by unfold eF; fun_prop) _ _)]
  apply Finset.sum_congr rfl
  intro p₂ hp₂
  rw [intervalIntegral.integral_finsetSum (fun p₃ hp₃ =>
    Continuous.intervalIntegrable (by unfold eF; fun_prop) _ _)]
  apply Finset.sum_congr rfl
  intro p₃ hp₃
  rw [intervalIntegral.integral_const_mul, integral_eF_int_unit]
  simp [sub_eq_zero, mul_ite]

end LeanLab.LiuTsang2005.Decomp102
