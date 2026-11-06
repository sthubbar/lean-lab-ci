/-
Split of LeanLab/Linnik1951/Decomp357d, theorem count_circle_coefficient357.

The circle coefficient is an integral over the unit interval of a product of
three absolutely convergent Fourier series, one copy of the damped prime
series taken twice and k copies of the damped power-of-two series, times one
exponential of frequency N.  The split is the five steps of its evaluation:
the orthogonal integral at an integral frequency, the pointwise product of the
series, the exchange of the integral of that series with its sum, the value of
every termwise integral, and the count of the tuples whose frequency is N.
The leaves are the hard steps; the assembly is only their combination.
-/
import LeanLab.Linnik1951.Decomp357d

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. Step 1 of the proof, the orthogonal integral: the integral over the
unit interval of a complex exponential of an integral frequency is one at
frequency zero and zero at every other integral frequency. -/
theorem integral_exp_two_pi_mul_int357 (m : ℤ) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      Complex.exp (((2 * Real.pi * α * (m : ℝ)) : ℝ) * Complex.I)) =
      if m = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  by_cases hm : m = 0
  · subst m
    simp
  · simp only [hm, ↓reduceIte]
    let c : ℂ := 2 * Real.pi * (m : ℂ) * Complex.I
    have hc : c ≠ 0 := by
      dsimp [c]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        (Int.cast_ne_zero.mpr hm)) Complex.I_ne_zero
    have heq : (fun α : ℝ => Complex.exp (((2 * Real.pi * α * (m : ℝ)) : ℝ) * Complex.I)) =
        fun α : ℝ => Complex.exp (c * (α : ℂ)) := by
      funext α
      congr 1
      dsimp [c]
      push_cast
      ring
    rw [heq, integral_exp_mul_complex hc]
    have he : Complex.exp c = 1 := by
      have he' : Complex.exp (c * ((1 : ℝ) : ℂ)) = 1 := by
        dsimp [c]
        convert Complex.exp_int_mul_two_pi_mul_I m using 1 <;> ring
      simpa using he'
    simp [he, hc]

private theorem tsum_fintype_pi_pow357 (f : ℕ → ℂ)
    (hf : Summable (fun n => ‖f n‖)) (k : ℕ) :
    Summable (fun ν : Fin k → ℕ => ∏ i, f (ν i)) ∧
      (∑' n, f n) ^ k = ∑' ν : Fin k → ℕ, ∏ i, f (ν i) := by
  induction k with
  | zero =>
      constructor
      · exact (hasSum_fintype _).summable
      · simp [tsum_fintype]
  | succ k ih =>
      have hνnorm : Summable (fun ν : Fin k → ℕ => ‖∏ i, f (ν i)‖) := by
        simpa only [norm_prod] using ih.1.norm
      have hprod : Summable (fun z : (Fin k → ℕ) × ℕ =>
          (∏ i, f (z.1 i)) * f z.2) :=
        (hνnorm.mul_norm hf).of_norm
      let e : ((Fin k → ℕ) × ℕ) ≃ (Fin (k + 1) → ℕ) :=
        (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ : Fin (k + 1) => ℕ))
      constructor
      · have hc := Summable.comp_injective
          (f := fun z : (Fin k → ℕ) × ℕ => (∏ i, f (z.1 i)) * f z.2)
          (i := fun x => e.symm x) hprod (fun _ _ h => e.symm.injective h)
        convert hc using 1
        ext ν
        simp [e, Fin.prod_univ_succ, Fin.tail, mul_comm]
      · rw [pow_succ, ih.2]
        calc
          (∑' ν : Fin k → ℕ, ∏ i, f (ν i)) * ∑' n, f n =
              ∑' z : (Fin k → ℕ) × ℕ, (∏ i, f (z.1 i)) * f z.2 :=
            tsum_mul_tsum_of_summable_norm hνnorm hf
          _ = ∑' ν : Fin (k + 1) → ℕ, ∏ i, f (ν i) := by
            simpa [e, Fin.prod_univ_succ, Fin.tail, mul_comm] using
              e.tsum_eq (fun ν : Fin (k + 1) → ℕ => ∏ i, f (ν i))

/-- LEAF. Step 2 of the proof, the pointwise product: at a fixed point of the
unit interval, one copy of the damped prime series squared times k copies of
the damped power-of-two series times the exponential of frequency N is the
absolutely convergent series over prime pairs and exponent tuples whose
frequencies add up. -/
theorem integrand_eq_tsum357 (k N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    primeFourier111 N α ^ 2 * powerFourier111 N α ^ k *
        Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) =
      ∑' t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
        (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) * Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I) := by
  let P : Nat.Primes → ℂ := fun p =>
    (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)
  let Q : ℕ → ℂ := fun m =>
    (Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)
  have hP : Summable (fun p => ‖P p‖) := by
    simpa only [P] using (prime_fourier_summable111 N hN α).norm
  have hQ : Summable (fun m => ‖Q m‖) := by
    simpa only [Q] using (power_fourier_summable111 N hN α).norm
  have hpow := tsum_fintype_pi_pow357 Q hQ k
  have hpairnorm : Summable (fun z : Nat.Primes × Nat.Primes => ‖P z.1 * P z.2‖) :=
    hP.mul_norm hP
  have hpnorm : Summable (fun ν : Fin k → ℕ => ‖∏ i, Q (ν i)‖) := by
    simpa only [norm_prod] using hpow.1.norm
  change (∑' p, P p) ^ 2 * (∑' m, Q m) ^ k *
    Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) = _
  calc
    (∑' p, P p) ^ 2 * (∑' m, Q m) ^ k *
        Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) =
        ((∑' z : Nat.Primes × Nat.Primes, P z.1 * P z.2) *
          (∑' ν : Fin k → ℕ, ∏ i, Q (ν i))) *
            Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) := by
              rw [pow_two, tsum_mul_tsum_of_summable_norm hP hP, hpow.2]
    _ = (∑' z : (Nat.Primes × Nat.Primes) × (Fin k → ℕ),
          (P z.1.1 * P z.1.2) * ∏ i, Q (z.2 i)) *
            Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) := by
              rw [tsum_mul_tsum_of_summable_norm hpairnorm hpnorm]
    _ = ∑' z : (Nat.Primes × Nat.Primes) × (Fin k → ℕ),
          ((P z.1.1 * P z.1.2) * ∏ i, Q (z.2 i)) *
            Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) := by
              rw [tsum_mul_right]
    _ = ∑' t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
          ((P t.1 * P t.2.1) * ∏ i, Q (t.2.2 i)) *
            Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) := by
              simpa using (Equiv.prodAssoc Nat.Primes Nat.Primes (Fin k → ℕ)).tsum_eq
                (fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) =>
                  ((P t.1 * P t.2.1) * ∏ i, Q (t.2.2 i)) *
                    Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I))
    _ = _ := by
      apply tsum_congr
      intro t
      have hdamp :
          ((Real.exp (-((t.1 : ℕ) : ℝ) / N) * Real.exp (-((t.2.1 : ℕ) : ℝ) / N)) *
            ∏ i, Real.exp (-((2 ^ (t.2.2 i + 1) : ℕ) : ℝ) / N)) =
            Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
              ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) := by
        rw [← Real.exp_add, ← Real.exp_sum, ← Real.exp_add]
        congr 1
        push_cast
        simp only [neg_div, Finset.sum_neg_distrib, Finset.mul_sum]
        rw [← Finset.sum_div]
        ring
      have hphase :
          ((Complex.exp ((-(2 * Real.pi * α * (t.1 : ℕ)) : ℝ) * Complex.I) *
            Complex.exp ((-(2 * Real.pi * α * (t.2.1 : ℕ)) : ℝ) * Complex.I)) *
            ∏ i, Complex.exp ((-(2 * Real.pi * α * (2 ^ (t.2.2 i + 1) : ℕ)) : ℝ) * Complex.I)) *
            Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) =
            Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) +
              ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I) := by
        rw [← Complex.exp_add, ← Complex.exp_sum, ← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        simp only [neg_div, neg_mul, Finset.sum_neg_distrib, Finset.mul_sum]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        ring
      dsimp only [P, Q]
      rw [Finset.prod_mul_distrib]
      have hdampC := congrArg (fun x : ℝ => (x : ℂ)) hdamp
      simp only [Complex.ofReal_mul, Complex.ofReal_prod] at hdampC
      calc
        _ = (((Real.exp (-((t.1 : ℕ) : ℝ) / N) : ℂ) *
                (Real.exp (-((t.2.1 : ℕ) : ℝ) / N) : ℂ) *
                ∏ i, (Real.exp (-((2 ^ (t.2.2 i + 1) : ℕ) : ℝ) / N) : ℂ)) *
              (((Complex.exp ((-(2 * Real.pi * α * (t.1 : ℕ)) : ℝ) * Complex.I) *
                  Complex.exp ((-(2 * Real.pi * α * (t.2.1 : ℕ)) : ℝ) * Complex.I)) *
                  ∏ i, Complex.exp ((-(2 * Real.pi * α * (2 ^ (t.2.2 i + 1) : ℕ)) : ℝ) * Complex.I)) *
                Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I))) := by ring
        _ = _ := by rw [hdampC, hphase]

private theorem expanded_fourier_summable357 (k N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    Summable (fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) =>
      (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
        ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) *
      Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) +
        ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I)) := by
  let P : Nat.Primes → ℂ := fun p =>
    (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (p : ℕ)) : ℝ) * Complex.I)
  let Q : ℕ → ℂ := fun m =>
    (Real.exp (-((2 ^ (m + 1) : ℕ) : ℝ) / N) : ℂ) *
      Complex.exp ((-(2 * Real.pi * α * (2 ^ (m + 1) : ℕ)) : ℝ) * Complex.I)
  have hP : Summable (fun p => ‖P p‖) := by
    simpa only [P] using (prime_fourier_summable111 N hN α).norm
  have hQ : Summable (fun m => ‖Q m‖) := by
    simpa only [Q] using (power_fourier_summable111 N hN α).norm
  have hpow := tsum_fintype_pi_pow357 Q hQ k
  have hpairnorm : Summable (fun z : Nat.Primes × Nat.Primes => ‖P z.1 * P z.2‖) :=
    hP.mul_norm hP
  have hpnorm : Summable (fun ν : Fin k → ℕ => ‖∏ i, Q (ν i)‖) := by
    simpa only [norm_prod] using hpow.1.norm
  have hfull : Summable (fun z : (Nat.Primes × Nat.Primes) × (Fin k → ℕ) =>
      (P z.1.1 * P z.1.2) * ∏ i, Q (z.2 i)) :=
    (hpairnorm.mul_norm hpnorm).of_norm
  have hright : Summable (fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) =>
      (P t.1 * P t.2.1) * ∏ i, Q (t.2.2 i)) := by
    have hc := Summable.comp_injective
      (f := fun z : (Nat.Primes × Nat.Primes) × (Fin k → ℕ) =>
        (P z.1.1 * P z.1.2) * ∏ i, Q (z.2 i))
      (i := fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) =>
        (Equiv.prodAssoc Nat.Primes Nat.Primes (Fin k → ℕ)).symm t)
      hfull (fun _ _ h => (Equiv.prodAssoc Nat.Primes Nat.Primes (Fin k → ℕ)).symm.injective h)
    exact hc
  refine (hright.mul_right (Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I))).congr ?_
  intro t
  have hdamp :
      ((Real.exp (-((t.1 : ℕ) : ℝ) / N) * Real.exp (-((t.2.1 : ℕ) : ℝ) / N)) *
        ∏ i, Real.exp (-((2 ^ (t.2.2 i + 1) : ℕ) : ℝ) / N)) =
        Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
          ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) := by
    rw [← Real.exp_add, ← Real.exp_sum, ← Real.exp_add]
    congr 1
    push_cast
    simp only [neg_div, Finset.sum_neg_distrib]
    rw [← Finset.sum_div]
    ring
  have hphase :
      ((Complex.exp ((-(2 * Real.pi * α * (t.1 : ℕ)) : ℝ) * Complex.I) *
        Complex.exp ((-(2 * Real.pi * α * (t.2.1 : ℕ)) : ℝ) * Complex.I)) *
        ∏ i, Complex.exp ((-(2 * Real.pi * α * (2 ^ (t.2.2 i + 1) : ℕ)) : ℝ) * Complex.I)) *
        Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I) =
        Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) +
          ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I) := by
    rw [← Complex.exp_add, ← Complex.exp_sum, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    simp only [neg_mul, Finset.sum_neg_distrib]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  dsimp only [P, Q]
  rw [Finset.prod_mul_distrib]
  have hdampC := congrArg (fun x : ℝ => (x : ℂ)) hdamp
  simp only [Complex.ofReal_mul, Complex.ofReal_prod] at hdampC
  calc
    _ = (((Real.exp (-((t.1 : ℕ) : ℝ) / N) : ℂ) *
            (Real.exp (-((t.2.1 : ℕ) : ℝ) / N) : ℂ) *
            ∏ i, (Real.exp (-((2 ^ (t.2.2 i + 1) : ℕ) : ℝ) / N) : ℂ)) *
          (((Complex.exp ((-(2 * Real.pi * α * (t.1 : ℕ)) : ℝ) * Complex.I) *
              Complex.exp ((-(2 * Real.pi * α * (t.2.1 : ℕ)) : ℝ) * Complex.I)) *
              ∏ i, Complex.exp ((-(2 * Real.pi * α * (2 ^ (t.2.2 i + 1) : ℕ)) : ℝ) * Complex.I)) *
            Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I))) := by ring
    _ = _ := by rw [hdampC, hphase]

/-- LEAF. Step 3 of the proof, the exchange of the integral with the sum: the
integral over the unit interval of the expanded series of step 2 is the sum
over the same index set of the termwise integrals, each taken by step 1, so
each term survives exactly when its frequency is N. -/
theorem integral_tsum_swap357 (k N : ℕ) (hN : 1 ≤ N) :
    (∫ α in Set.Icc (0 : ℝ) 1,
      ∑' t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
        (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) * Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I)) =
      ∑' t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
        (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) * (if ((t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1)) = N then (1 : ℂ) else 0) := by
  have hnorm (t : Nat.Primes × Nat.Primes × (Fin k → ℕ)) (α : ℝ) :
      ‖(Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
        ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) *
        Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) +
          ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I)‖ =
        Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
          ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) := by
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hweight : Summable (fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) =>
      Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
        ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N))) := by
    have h := (expanded_fourier_summable357 k N hN 0).norm
    exact h.congr (fun t => hnorm t 0)
  have hF_int : ∀ t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
      IntegrableOn (fun α : ℝ =>
        (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
          ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) *
        Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) +
          ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I))
        (Set.Icc (0 : ℝ) 1) := by
    intro t
    apply Continuous.integrableOn_Icc
    fun_prop
  have hint (t : Nat.Primes × Nat.Primes × (Fin k → ℕ)) :
      (∫ α in Set.Icc (0 : ℝ) 1,
        ‖(Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
          ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) *
          Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) +
            ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I)‖) =
        Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
          ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) := by
    rw [setIntegral_congr_fun measurableSet_Icc (fun α _ => hnorm t α)]
    simp
  have hF_sum : Summable (fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) =>
      ∫ α in Set.Icc (0 : ℝ) 1,
        ‖(Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
          ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) *
          Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) +
            ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I)‖) := by
    simpa only [hint] using hweight
  rw [← integral_tsum_of_summable_integral_norm hF_int hF_sum]
  apply tsum_congr
  intro t
  rw [integral_const_mul]
  let M : ℤ := (N : ℤ) - ((t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1))
  have hfun : (fun α : ℝ =>
      Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) +
        ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I)) =
      fun α : ℝ => Complex.exp (((2 * Real.pi * α * (M : ℝ)) : ℝ) * Complex.I) := by
    funext α
    congr 2
    dsimp [M]
    push_cast
    ring
  rw [hfun, integral_exp_two_pi_mul_int357 M]
  by_cases ht : (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) = N
  · have ht' : (N : ℤ) = (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) := by
      exact_mod_cast ht.symm
    have hM : M = 0 := by dsimp [M]; omega
    simp [ht, hM]
  · have ht' : (N : ℤ) ≠ (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) := by
      intro hn
      apply ht
      exact_mod_cast hn.symm
    have hM : M ≠ 0 := by dsimp [M]; omega
    simp [ht, hM]

/-- LEAF. Step 4 of the proof, the count: at frequency N the damping weight of
every surviving tuple is exp of minus one, and the surviving tuples are in
bijection with the ordered representations counted by
representationCount111, so the sum over them is exp of minus one times that
count. -/
theorem tsum_indicator_eq_count357 (k N : ℕ) (hN : 1 ≤ N) :
    (∑' t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
        (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) * (if ((t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1)) = N then (1 : ℂ) else 0)) =
      (Real.exp (-1) : ℂ) * (representationCount111 k N : ℂ) := by
  classical
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hterm (t : Nat.Primes × Nat.Primes × (Fin k → ℕ)) :
      (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
        ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) *
        (if (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) = N then (1 : ℂ) else 0) =
        if (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) = N then
          (Real.exp (-1) : ℂ) else 0 := by
    by_cases ht : (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) = N
    · have ht' : ((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) +
          ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast ht
      simp only [ht, if_true, mul_one]
      rw [ht', div_self hNr]
    · simp [ht]
  rw [tsum_congr hterm]
  let R : Finset (Fin (N + 1) × Fin (N + 1) × (Fin k → Fin (N + 1))) :=
    Finset.univ.filter fun t : Fin (N + 1) × Fin (N + 1) × (Fin k → Fin (N + 1)) =>
      (t.1.val).Prime ∧ (t.2.1.val).Prime ∧ (∀ i, 1 ≤ (t.2.2 i).val) ∧
        N = t.1.val + t.2.1.val + ∑ i, 2 ^ (t.2.2 i).val
  let e : {t // t ∈ R} → Nat.Primes × Nat.Primes × (Fin k → ℕ) := fun t =>
    (⟨t.1.1.val, (Finset.mem_filter.mp t.2).2.1⟩,
      (⟨t.1.2.1.val, (Finset.mem_filter.mp t.2).2.2.1⟩,
        fun i => (t.1.2.2 i).val - 1))
  let S : Finset (Nat.Primes × Nat.Primes × (Fin k → ℕ)) := Finset.univ.image e
  have he_inj : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    have hp : a.1.1 = b.1.1 := by
      apply Fin.ext
      exact congrArg (fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) => (t.1 : ℕ)) hab
    have hq : a.1.2.1 = b.1.2.1 := by
      apply Fin.ext
      exact congrArg (fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) => (t.2.1 : ℕ)) hab
    have hν : a.1.2.2 = b.1.2.2 := by
      funext i
      apply Fin.ext
      have ha := (Finset.mem_filter.mp a.2).2.2.2.1 i
      have hb := (Finset.mem_filter.mp b.2).2.2.2.1 i
      have he := congrArg (fun t : Nat.Primes × Nat.Primes × (Fin k → ℕ) => t.2.2 i) hab
      dsimp [e] at he
      omega
    exact Prod.ext hp (Prod.ext hq hν)
  have hS (t : Nat.Primes × Nat.Primes × (Fin k → ℕ)) (ht : t ∈ S) :
      (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) = N := by
    rcases Finset.mem_image.mp ht with ⟨r, _, rfl⟩
    have hr := Finset.mem_filter.mp r.2
    dsimp [e]
    convert hr.2.2.2.2.symm using 1
    have hsum : (∑ i, 2 ^ ((r.1.2.2 i).val - 1 + 1)) =
        ∑ i, 2 ^ (r.1.2.2 i).val := by
      apply Finset.sum_congr rfl
      intro i _
      have hi := hr.2.2.2.1 i
      congr 1
      omega
    exact congrArg (fun x : ℕ => (r.1.1 : ℕ) + (r.1.2.1 : ℕ) + x) hsum
  have hout (t : Nat.Primes × Nat.Primes × (Fin k → ℕ)) (ht : t ∉ S) :
      (if (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) = N then
        (Real.exp (-1) : ℂ) else 0) = 0 := by
    have hnc : ¬((t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) = N) := by
      intro htotal
      apply ht
      have hpN : (t.1 : ℕ) < N + 1 := by omega
      have hqN : (t.2.1 : ℕ) < N + 1 := by omega
      have hνN : ∀ i, t.2.2 i + 1 < N + 1 := by
        intro i
        have hle : 2 ^ (t.2.2 i + 1) ≤ ∑ j, 2 ^ (t.2.2 j + 1) :=
          Finset.single_le_sum (f := fun j : Fin k => 2 ^ (t.2.2 j + 1))
            (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        have hpow : t.2.2 i + 1 < 2 ^ (t.2.2 i + 1) := Nat.lt_two_pow_self
        omega
      let r : Fin (N + 1) × Fin (N + 1) × (Fin k → Fin (N + 1)) :=
        (⟨(t.1 : ℕ), hpN⟩, ⟨(t.2.1 : ℕ), hqN⟩, fun i => ⟨t.2.2 i + 1, hνN i⟩)
      have hr : r ∈ R := by
        simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨t.1.property, t.2.1.property, fun i => by dsimp [r]; omega, htotal.symm⟩
      apply Finset.mem_image.mpr
      refine ⟨⟨r, hr⟩, Finset.mem_univ _, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply Prod.ext
        · apply Subtype.ext
          rfl
        · funext i
          rfl
    simp [hnc]
  rw [tsum_eq_sum (s := S) hout]
  have hcard : S.card = R.card := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ he_inj, Finset.card_attach]
  have hrep : representationCount111 k N = R.card := by
    rfl
  calc
    (∑ t ∈ S, if (t.1 : ℕ) + (t.2.1 : ℕ) + ∑ i, 2 ^ (t.2.2 i + 1) = N then
        (Real.exp (-1) : ℂ) else 0) = ∑ _t ∈ S, (Real.exp (-1) : ℂ) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [if_pos (hS t ht)]
    _ = (S.card : ℂ) * (Real.exp (-1) : ℂ) := by simp
    _ = (Real.exp (-1) : ℂ) * (representationCount111 k N : ℂ) := by
      rw [hcard, ← hrep]
      ring

/-- The circle coefficient, assembled from the four leaves of this file: integrate
the expanded product, swap the integral with the sum, evaluate every termwise
integral, and count the surviving tuples. -/
theorem count_circle_coefficient357_split (k N : ℕ) (hN : 1 ≤ N) :
    (∫ α in Set.Icc (0 : ℝ) 1, primeFourier111 N α ^ 2 * powerFourier111 N α ^ k * Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) = (Real.exp (-1) : ℂ) * (representationCount111 k N : ℂ) := by
  have hexp : (∫ α in Set.Icc (0 : ℝ) 1, primeFourier111 N α ^ 2 * powerFourier111 N α ^ k *
      Complex.exp (((2 * Real.pi * α * N) : ℝ) * Complex.I)) =
      ∫ α in Set.Icc (0 : ℝ) 1,
        ∑' t : Nat.Primes × Nat.Primes × (Fin k → ℕ),
          (Real.exp (-((((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)) / N)) : ℂ) * Complex.exp (((2 * Real.pi * α * ((N : ℝ) - (((t.1 : ℕ) : ℝ) + ((t.2.1 : ℕ) : ℝ) + ∑ i, ((2 ^ (t.2.2 i + 1) : ℕ) : ℝ)))) : ℝ) * Complex.I) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro α _
    exact integrand_eq_tsum357 k N hN α
  rw [hexp, integral_tsum_swap357 k N hN, tsum_indicator_eq_count357 k N hN]

end LeanLab.Linnik1951
