/-
The three character term decomposition of the local major arc integral at an
integer residual, cut into two steps: the finite character square expansion of
the local arc at each fixed residual, and the exact separation of that square
into the principal, the mixed and the nonprincipal character blocks.

The square is the double sum of the ordered character pair contribution over all
pairs of characters of the modulus. Expanding the square of the prime Fourier
series against the characters of the modulus is exact for the primes coprime to
the modulus, so the expansion differs from the local arc only through the primes
dividing the modulus and through the finite integral rearrangement. The residual
is carried separately for nonnegative and for negative residuals, since the two
regions use conjugate reduced residue phases. The separation of the square into
the three named blocks is a finite rearrangement with no error term.
-/
import LeanLab.Linnik1951.Decomp491b

namespace LeanLab.Linnik1951

open Finset MeasureTheory

set_option maxHeartbeats 4000000

/-- LEAF. The exponential damping summed over the primes is summable. -/
private lemma summable_prime_damp491 (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun p : Nat.Primes => Real.exp (-((p : ℕ) : ℝ) / N)) :=
  (damping_summable111 N hN).comp_injective Nat.Primes.coe_nat_injective

/-- LEAF. The modulus of one damped prime exponential is its damping weight. -/
private lemma norm_prime_exp491 (N : ℕ) (p : Nat.Primes) (z : ℝ) :
    ‖(Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)‖ =
      Real.exp (-((p : ℕ) : ℝ) / N) := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le]

/-- LEAF. One twisted summand has modulus at most its damping weight. -/
private lemma norm_twist_le491 (N : ℕ) (c : Nat.Primes → ℂ) (hc : ∀ p, ‖c p‖ ≤ 1)
    (p : Nat.Primes) (z : ℝ) :
    ‖c p * ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))‖ ≤ Real.exp (-((p : ℕ) : ℝ) / N) := by
  rw [norm_mul, norm_prime_exp491 N p z]
  calc ‖c p‖ * Real.exp (-((p : ℕ) : ℝ) / N)
      ≤ 1 * Real.exp (-((p : ℕ) : ℝ) / N) := by
        have h1 := hc p
        have h2 : (0:ℝ) ≤ Real.exp (-((p : ℕ) : ℝ) / N) := (Real.exp_pos _).le
        nlinarith
    _ = Real.exp (-((p : ℕ) : ℝ) / N) := one_mul _

/-- LEAF. The twisted damped prime series is absolutely summable at every real point. -/
private lemma summable_twist491 (N : ℕ) (hN : 1 ≤ N) (c : Nat.Primes → ℂ)
    (hc : ∀ p, ‖c p‖ ≤ 1) (z : ℝ) :
    Summable (fun p : Nat.Primes => ‖c p * ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))‖) := by
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
    (summable_prime_damp491 N hN)
  exact norm_twist_le491 N c hc p z

/-- LEAF. The product of two twisted damped prime series at one point is the sum over
ordered prime pairs. -/
private lemma prod_twist491 (N : ℕ) (hN : 1 ≤ N) (c₁ c₂ : Nat.Primes → ℂ)
    (h₁ : ∀ p, ‖c₁ p‖ ≤ 1) (h₂ : ∀ p, ‖c₂ p‖ ≤ 1) (z : ℝ) :
    (∑' p : Nat.Primes, c₁ p * ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) *
        (∑' p : Nat.Primes, c₂ p * ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) =
      ∑' k : Nat.Primes × Nat.Primes,
        (c₁ k.1 * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (c₂ k.2 * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) :=
  tsum_mul_tsum_of_summable_norm (summable_twist491 N hN c₁ h₁ z)
    (summable_twist491 N hN c₂ h₂ z)

/-- LEAF. The pair weight is summable. -/
private lemma summable_pair_damp491 (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun k : Nat.Primes × Nat.Primes =>
      Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N)) := by
  have hnorm : Summable (fun p : Nat.Primes => ‖Real.exp (-((p : ℕ) : ℝ) / N)‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using
      summable_prime_damp491 N hN
  have h := hnorm.mul_norm hnorm
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) h
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- LEAF. The exchange of one interval integral against the product of two
character-twisted damped prime series. -/
private theorem hasSum_prime_square491 (N : ℕ) (hN : 1 ≤ N) (n : ℤ)
    (c₁ c₂ : Nat.Primes → ℂ) (h₁ : ∀ p, ‖c₁ p‖ ≤ 1) (h₂ : ∀ p, ‖c₂ p‖ ≤ 1)
    {a b : ℝ} (hab : a ≤ b) :
    HasSum (fun k : Nat.Primes × Nat.Primes =>
        ∫ z in a..b, (c₁ k.1 * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (c₂ k.2 * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))
      (∫ z in a..b,
        (∑' p : Nat.Primes, c₁ p * ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) *
        (∑' p : Nat.Primes, c₂ p * ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
  have hmain := hasSum_integral_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc a b))
    (F := fun k : Nat.Primes × Nat.Primes => fun z : ℝ =>
      (c₁ k.1 * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (c₂ k.2 * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))
    (by
      intro k
      have hcont : Continuous (fun z : ℝ =>
          (c₁ k.1 * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (c₂ k.2 * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
        fun_prop
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hcont.intervalIntegrable a b))
    (by
      refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
        (Summable.mul_left (b - a) (summable_pair_damp491 N hN))
      · exact integral_nonneg (fun z => norm_nonneg _)
      · have hb1 : IntervalIntegrable (fun z : ℝ =>
            ‖(c₁ k.1 * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (c₂ k.2 * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖) volume a b := by
          have hcont : Continuous (fun z : ℝ =>
              (c₁ k.1 * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (c₂ k.2 * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
            fun_prop
          exact hcont.norm.intervalIntegrable a b
        have hb2 : IntervalIntegrable
            (fun _ : ℝ => Real.exp (-((k.1 : ℕ) : ℝ) / N) *
              Real.exp (-((k.2 : ℕ) : ℝ) / N)) volume a b := intervalIntegrable_const
        have hle : ∀ z : ℝ,
            ‖(c₁ k.1 * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (c₂ k.2 * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
            Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) := by
          intro z
          rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
          exact mul_le_mul (norm_twist_le491 N c₁ h₁ k.1 z) (norm_twist_le491 N c₂ h₂ k.2 z)
            (norm_nonneg _) (Real.exp_pos _).le
        rw [← intervalIntegral.integral_of_le hab]
        have hmono := intervalIntegral.integral_mono hab hb1 hb2 hle
        calc _ ≤ ∫ z in a..b, Real.exp (-((k.1 : ℕ) : ℝ) / N) *
              Real.exp (-((k.2 : ℕ) : ℝ) / N) := hmono
          _ = (b - a) * (Real.exp (-((k.1 : ℕ) : ℝ) / N) *
              Real.exp (-((k.2 : ℕ) : ℝ) / N)) := by
            rw [intervalIntegral.integral_const]
            ring)
  have hfun : (fun z : ℝ => ∑' k : Nat.Primes × Nat.Primes,
      (c₁ k.1 * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (c₂ k.2 * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
      fun z : ℝ => (∑' p : Nat.Primes, c₁ p * ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) *
        (∑' p : Nat.Primes, c₂ p * ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    funext z
    rw [prod_twist491 N hN c₁ c₂ h₁ h₂ z, tsum_mul_right]
  rw [hfun] at hmain
  have hsummand : (fun k : Nat.Primes × Nat.Primes =>
      ∫ x in Set.Ioc a b, (c₁ k.1 * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * x * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (c₂ k.2 * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * x * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * x * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
      fun k : Nat.Primes × Nat.Primes => ∫ z in a..b, (c₁ k.1 * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (c₂ k.2 * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    funext k
    exact (intervalIntegral.integral_of_le hab).symm
  rw [hsummand] at hmain
  rw [← intervalIntegral.integral_of_le hab] at hmain
  exact hmain

/-- LEAF. Complex conjugation inverts character values. -/
private lemma star_char_apply491 (q : ℕ) (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    star (χ a) = χ⁻¹ a := by
  rw [MulChar.inv_apply_eq_inv, Ring.inverse_eq_inv]
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    change starRingEnd ℂ (χ ↑u) = (χ ↑u)⁻¹
    rw [← Complex.inv_eq_conj (DirichletCharacter.unit_norm_eq_one χ u)]
  · rw [χ.map_nonunit ha, star_zero, inv_zero]

/-- LEAF. Conjugation of one character value at a reduced residue. -/
private lemma star_gauss_term491 (q : ℕ) (χ : DirichletCharacter ℂ q) (b : ℕ) :
    star (χ ((b : ℕ) : ZMod q) * Complex.exp (((2 * Real.pi * ((b : ℝ) / q) : ℝ) : ℂ) * Complex.I))
      = χ⁻¹ ((b : ℕ) : ZMod q) *
        Complex.exp (((-(2 * Real.pi * ((b : ℝ) / q)) : ℝ) : ℂ) * Complex.I) := by
  have hw : star (Complex.exp (((2 * Real.pi * ((b : ℝ) / q) : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((-(2 * Real.pi * ((b : ℝ) / q)) : ℝ) : ℂ) * Complex.I) := by
    change starRingEnd ℂ (Complex.exp (((2 * Real.pi * ((b : ℝ) / q) : ℝ) : ℂ) * Complex.I)) = _
    rw [← Complex.exp_conj]
    congr 1
    change (starRingEnd ℂ) (((2 * Real.pi * ((b : ℝ) / q) : ℝ) : ℂ) * Complex.I) = _
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
    ring
  rw [star_mul, star_char_apply491, hw, mul_comm]

/-- LEAF. The reduced residue phase has period one in the numerator. -/
private lemma phase_period491 (q b k : ℕ) (hq : (q : ℝ) ≠ 0) :
    Complex.exp (((-(2 * Real.pi * (((b : ℝ) + (q : ℝ) * (k : ℝ)) / (q : ℝ))) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-(2 * Real.pi * ((b : ℝ) / (q : ℝ))) : ℝ) : ℂ) * Complex.I) := by
  have hreal : -(2 * Real.pi * (((b : ℝ) + (q : ℝ) * (k : ℝ)) / (q : ℝ))) =
      -(2 * Real.pi * ((b : ℝ) / (q : ℝ))) + (k : ℝ) * (-(2 * Real.pi)) := by
    field_simp
    ring
  have harg : (((-(2 * Real.pi * (((b : ℝ) + (q : ℝ) * (k : ℝ)) / (q : ℝ))) : ℝ)) : ℂ) * Complex.I =
      (((-(2 * Real.pi * ((b : ℝ) / (q : ℝ))) : ℝ)) : ℂ) * Complex.I +
        ((k : ℕ) : ℂ) * (-(2 * Real.pi) * Complex.I) := by
    rw [hreal]
    push_cast
    ring
  rw [harg, Complex.exp_add]
  have hone : Complex.exp (((k : ℕ) : ℂ) * (-(2 * Real.pi) * Complex.I)) = 1 := by
    have h := Complex.exp_int_mul_two_pi_mul_I (-(k : ℤ))
    convert h using 2
    push_cast
    ring
  rw [hone, mul_one]

/-- LEAF. The character coefficient of one natural number at one modulus. -/
private lemma charCoeff_one491 (q : ℕ) [NeZero q] (m : ℕ) :
    ∑ χ : DirichletCharacter ℂ q, conjugateGauss491 q χ * χ ((m : ℕ) : ZMod q) =
      if Nat.Coprime m q then
        (q.totient : ℂ) *
          Complex.exp (((-(2 * Real.pi * ((m : ℝ) / (q : ℝ))) : ℝ) : ℂ) * Complex.I)
      else 0 := by
  classical
  have hqpos : 0 < q := NeZero.pos q
  have hqne : ((q : ℝ)) ≠ 0 := by positivity
  have hexp (χ : DirichletCharacter ℂ q) :
      conjugateGauss491 q χ = ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
        χ⁻¹ ((b : ℕ) : ZMod q) *
          Complex.exp (((-(2 * Real.pi * ((b : ℝ) / q)) : ℝ) : ℂ) * Complex.I) := by
    unfold conjugateGauss491
    rw [star_sum]
    exact Finset.sum_congr rfl (fun b _ => star_gauss_term491 q χ b)
  have hkey (b : ℕ) (hb : b ∈ (range q).filter (fun b => Nat.Coprime b q)) :
      ∑ χ : DirichletCharacter ℂ q,
          χ⁻¹ ((b : ℕ) : ZMod q) * χ ((m : ℕ) : ZMod q) =
        if (((b : ℕ) : ZMod q) = ((m : ℕ) : ZMod q)) then (q.totient : ℂ) else 0 := by
    have hunit : IsUnit (((b : ℕ) : ZMod q)) :=
      (ZMod.isUnit_iff_coprime b q).mpr (Finset.mem_filter.mp hb).2
    have hconv : ∑ χ : DirichletCharacter ℂ q,
        χ (((b : ℕ) : ZMod q)⁻¹) * χ ((m : ℕ) : ZMod q) =
        ∑ χ : DirichletCharacter ℂ q,
          χ⁻¹ ((b : ℕ) : ZMod q) * χ ((m : ℕ) : ZMod q) := by
      apply Finset.sum_congr rfl
      intro χ _
      have harg : ((b : ℕ) : ZMod q)⁻¹ = Ring.inverse (((b : ℕ) : ZMod q)) := by
        rw [← hunit.unit_spec, ZMod.inv_coe_unit, Ring.inverse_unit]
      rw [MulChar.inv_apply, ← harg]
    rw [← hconv]
    exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ hunit ((m : ℕ) : ZMod q)
  have hstep1 : (∑ χ : DirichletCharacter ℂ q, conjugateGauss491 q χ * χ ((m : ℕ) : ZMod q))
      = ∑ χ : DirichletCharacter ℂ q, ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
          (χ⁻¹ ((b : ℕ) : ZMod q) *
            Complex.exp (((-(2 * Real.pi * ((b : ℝ) / q)) : ℝ) : ℂ) * Complex.I)) *
            χ ((m : ℕ) : ZMod q) := by
    apply Finset.sum_congr rfl
    intro χ _
    rw [hexp χ, Finset.sum_mul]
  rw [hstep1, Finset.sum_comm]
  have hstep2 : ∀ b ∈ (range q).filter (fun b => Nat.Coprime b q),
      (∑ χ : DirichletCharacter ℂ q,
          (χ⁻¹ ((b : ℕ) : ZMod q) *
            Complex.exp (((-(2 * Real.pi * ((b : ℝ) / q)) : ℝ) : ℂ) * Complex.I)) *
            χ ((m : ℕ) : ZMod q)) =
        (if (((b : ℕ) : ZMod q) = ((m : ℕ) : ZMod q)) then (q.totient : ℂ) else 0) *
          Complex.exp (((-(2 * Real.pi * ((b : ℝ) / q)) : ℝ) : ℂ) * Complex.I) := by
    intro b hb
    calc (∑ χ : DirichletCharacter ℂ q,
          (χ⁻¹ ((b : ℕ) : ZMod q) *
            Complex.exp (((-(2 * Real.pi * ((b : ℝ) / q)) : ℝ) : ℂ) * Complex.I)) *
            χ ((m : ℕ) : ZMod q))
        = ∑ χ : DirichletCharacter ℂ q,
            (χ⁻¹ ((b : ℕ) : ZMod q) * χ ((m : ℕ) : ZMod q)) *
              Complex.exp (((-(2 * Real.pi * ((b : ℝ) / q)) : ℝ) : ℂ) * Complex.I) := by
          apply Finset.sum_congr rfl
          intro χ _
          ring
      _ = (∑ χ : DirichletCharacter ℂ q,
            χ⁻¹ ((b : ℕ) : ZMod q) * χ ((m : ℕ) : ZMod q)) *
              Complex.exp (((-(2 * Real.pi * ((b : ℝ) / q)) : ℝ) : ℂ) * Complex.I) :=
          (Finset.sum_mul ..).symm
      _ = _ := by rw [hkey b hb]
  rw [Finset.sum_congr rfl hstep2]
  by_cases hcop : Nat.Coprime m q
  · set b0 := m % q with hb0
    have hb0lt : b0 < q := Nat.mod_lt m hqpos
    have hb0eqm : ((b0 : ℕ) : ZMod q) = ((m : ℕ) : ZMod q) := by
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hb0lt]
    have hb0S : b0 ∈ (range q).filter (fun b => Nat.Coprime b q) := by
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨hb0lt, ?_⟩
      have hunit : IsUnit (((m : ℕ) : ZMod q)) := (ZMod.isUnit_iff_coprime m q).mpr hcop
      exact (ZMod.isUnit_iff_coprime b0 q).mp (by simpa only [← hb0eqm] using hunit)
    have hphase : Complex.exp (((-(2 * Real.pi * ((b0 : ℝ) / q)) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((-(2 * Real.pi * ((m : ℝ) / (q : ℝ))) : ℝ) : ℂ) * Complex.I) := by
      have hsplit : ((m : ℝ)) = (b0 : ℝ) + (q : ℝ) * ((m / q : ℕ) : ℝ) := by
        have h := Nat.div_add_mod m q
        have h2 : ((m : ℕ) : ℝ) = ((q * (m / q) + m % q : ℕ) : ℝ) := by rw [h]
        rw [h2, hb0]
        push_cast
        ring
      rw [hsplit, phase_period491 q b0 (m / q) hqne]
    have hsingle : ∀ b ∈ (range q).filter (fun b => Nat.Coprime b q), b ≠ b0 →
        (if (((b : ℕ) : ZMod q) = ((m : ℕ) : ZMod q)) then (q.totient : ℂ) else 0) *
          Complex.exp (((-(2 * Real.pi * ((b : ℝ) / q)) : ℝ) : ℂ) * Complex.I) = 0 := by
      intro b hb hne
      have hbq : b < q := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      have hneq : ((b : ℕ) : ZMod q) ≠ ((m : ℕ) : ZMod q) := by
        intro heq
        rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hbq, ← hb0] at heq
        exact hne heq
      rw [if_neg hneq, zero_mul]
    rw [Finset.sum_eq_single b0 hsingle (by intro h; exact absurd hb0S h)]
    rw [if_pos hb0eqm, if_pos hcop, hphase]
  · have hzero : ∀ b ∈ (range q).filter (fun b => Nat.Coprime b q),
        (if (((b : ℕ) : ZMod q) = ((m : ℕ) : ZMod q)) then (q.totient : ℂ) else 0) *
          Complex.exp (((-(2 * Real.pi * ((b : ℝ) / q)) : ℝ) : ℂ) * Complex.I) = 0 := by
      intro b hb
      have hbq : b < q := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      have hbcop : Nat.Coprime b q := (Finset.mem_filter.mp hb).2
      have hneq : ((b : ℕ) : ZMod q) ≠ ((m : ℕ) : ZMod q) := by
        intro heq
        have hunit : IsUnit (((m : ℕ) : ZMod q)) :=
          heq ▸ ((ZMod.isUnit_iff_coprime b q).mpr hbcop)
        exact hcop ((ZMod.isUnit_iff_coprime m q).mp hunit)
      rw [if_neg hneq, zero_mul]
    rw [Finset.sum_eq_zero hzero, if_neg hcop]

/-- LEAF. The character twist of the damped prime series at a shifted argument. -/
private lemma primeFourier_shift491 (N q a : ℕ) (z : ℝ) :
    primeFourier111 N ((a : ℝ) / q + z) =
      ∑' p : Nat.Primes, (Complex.exp (((-(2 * Real.pi * ((p : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I)) * ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) := by
  unfold primeFourier111
  apply tsum_congr
  intro p
  have harg : ((-(2 * Real.pi * ((a : ℝ) / (q : ℝ) + z) * ((p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I =
      ((-(2 * Real.pi * ((p : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I +
        ((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_add]
  ring

/-- LEAF. The twist has modulus one. -/
private lemma norm_twist_phase491 (q a : ℕ) (p : Nat.Primes) :
    ‖(Complex.exp (((-(2 * Real.pi * ((p : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I))‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- LEAF. The local arc expands into the sum over reduced residues of the phase times
the ordered prime pair sum of the pair integrals. -/
private lemma localArc_expand491 (N q : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) (n : ℤ) :
    localArc1622 N q n =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
          ∑' k : Nat.Primes × Nat.Primes,
            ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
              ((Complex.exp (((-(2 * Real.pi * ((k.1 : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I)) * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) *
              ((Complex.exp (((-(2 * Real.pi * ((k.2 : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I)) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have htau : (0 : ℝ) ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
  have hab : (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by linarith
  unfold localArc1622
  apply Finset.sum_congr rfl
  intro a ha
  have hphase : ∀ z : ℝ, Complex.exp (((2 * Real.pi * (n : ℝ) * (((a : ℝ) / q + z)) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    intro z
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have htw : ∀ p : Nat.Primes, ‖(Complex.exp (((-(2 * Real.pi * ((p : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I))‖ ≤ 1 := fun p => le_of_eq (norm_twist_phase491 q a p)
  have hhs := hasSum_prime_square491 N hN n
    (fun p : Nat.Primes => (Complex.exp (((-(2 * Real.pi * ((p : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I))) (fun p : Nat.Primes => (Complex.exp (((-(2 * Real.pi * ((p : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I)))
    htw htw hab
  rw [show (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
        primeFourier111 N ((a : ℝ) / q + z) ^ 2 *
          Complex.exp (((2 * Real.pi * (n : ℝ) * (((a : ℝ) / q + z)) : ℝ) : ℂ) * Complex.I)) =
      ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
          ((∑' p : Nat.Primes, (Complex.exp (((-(2 * Real.pi * ((p : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I)) * ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) *
            (∑' p : Nat.Primes, (Complex.exp (((-(2 * Real.pi * ((p : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I)) * ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) from by
    apply intervalIntegral.integral_congr
    intro z _
    simp only []
    rw [pow_two, primeFourier_shift491, hphase z]
    ring]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [← hhs.tsum_eq]

/-- LEAF. A finite sum of summable families is summable. -/
private lemma finset_summable491 {ι σ : Type*} [Countable ι] (s : Finset σ) (f : σ → ι → ℂ)
    (h : ∀ σ' ∈ s, Summable (f σ')) : Summable (fun i => ∑ σ' ∈ s, f σ' i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact Summable.add (h a (Finset.mem_insert_self a s))
        (ih (fun σ' hσ' => h σ' (Finset.mem_insert_of_mem hσ')))

/-- LEAF. A finite sum of infinite sums is the infinite sum of the finite sums. -/
private lemma finset_tsum_swap491 {ι σ : Type*} [Countable ι] [DecidableEq σ] (s : Finset σ)
    (f : σ → ι → ℂ) (h : ∀ σ' ∈ s, Summable (f σ')) :
    (∑ σ' ∈ s, ∑' i, f σ' i) = ∑' i, ∑ σ' ∈ s, f σ' i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have hs : Summable (fun i => ∑ σ' ∈ s, f σ' i) :=
        finset_summable491 s f (fun σ' hσ' => h σ' (Finset.mem_insert_of_mem hσ'))
      rw [Summable.tsum_add (h a (Finset.mem_insert_self a s)) hs]
      rw [ih (fun σ' hσ' => h σ' (Finset.mem_insert_of_mem hσ'))]

/-- LEAF. The character prime series is the sum of the damped prime exponentials
weighted by the character. -/
private lemma characterPrime_eq_tsum491 (N q : ℕ) (χ : DirichletCharacter ℂ q) (z : ℝ) :
    characterPrime280 χ N z =
      ∑' p : Nat.Primes, χ ((p : ℕ) : ZMod q) * ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) := by
  unfold characterPrime280
  apply tsum_congr
  intro p
  ring

/-- LEAF. The ordered pair coefficient over all character pairs. -/
private lemma charPair_coeff491 (q : ℕ) [NeZero q] {a : ℕ} (ha : Nat.Coprime a q) (p1 p2 : ℕ) :
    (∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
        (conjugateGauss491 q χ * χ (((a * p1 : ℕ)) : ZMod q)) *
          (conjugateGauss491 q ψ * ψ (((a * p2 : ℕ)) : ZMod q))) =
      if Nat.Coprime p1 q ∧ Nat.Coprime p2 q then
        (q.totient : ℂ) ^ 2 *
          Complex.exp (((-(2 * Real.pi * (((a : ℝ) * ((p1 : ℝ) + (p2 : ℝ))) / (q : ℝ))) : ℝ) : ℂ) * Complex.I)
      else 0 := by
  rw [← Finset.sum_mul_sum (s := (univ : Finset (DirichletCharacter ℂ q)))
    (t := (univ : Finset (DirichletCharacter ℂ q)))
    (f := fun χ : DirichletCharacter ℂ q => conjugateGauss491 q χ * χ (((a * p1 : ℕ)) : ZMod q))
    (g := fun ψ : DirichletCharacter ℂ q => conjugateGauss491 q ψ * ψ (((a * p2 : ℕ)) : ZMod q))]
  have h1 := charCoeff_one491 q (a * p1)
  have h2 := charCoeff_one491 q (a * p2)
  rw [h1, h2]
  have hcop1 : Nat.Coprime (a * p1) q ↔ Nat.Coprime p1 q := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
  have hcop2 : Nat.Coprime (a * p2) q ↔ Nat.Coprime p2 q := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩
  have hphase : Complex.exp (((-(2 * Real.pi * (((a * p1 : ℕ) : ℝ) / (q : ℝ))) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((-(2 * Real.pi * (((a * p2 : ℕ) : ℝ) / (q : ℝ))) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((-(2 * Real.pi * (((a : ℝ) * ((p1 : ℝ) + (p2 : ℝ))) / (q : ℝ))) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    have hqne : ((q : ℝ)) ≠ 0 := by
      have := NeZero.pos q
      positivity
    push_cast
    field_simp
    ring
  by_cases hp1 : Nat.Coprime p1 q
  · by_cases hp2 : Nat.Coprime p2 q
    · rw [if_pos (hcop1.mpr hp1), if_pos (hcop2.mpr hp2), if_pos (show Nat.Coprime p1 q ∧ Nat.Coprime p2 q from ⟨hp1, hp2⟩), ← hphase]
      ring
    · rw [if_pos (hcop1.mpr hp1), if_neg (fun h => hp2 (hcop2.mp h)),
        if_neg (fun h : Nat.Coprime p1 q ∧ Nat.Coprime p2 q => hp2 h.2)]
      ring
  · rw [if_neg (fun h => hp1 (hcop1.mp h)),
      if_neg (fun h : Nat.Coprime p1 q ∧ Nat.Coprime p2 q => hp1 h.1)]
    ring

/-- LEAF. One ordered character pair expands into the ordered prime pair sum of its
pair integrals. -/
private lemma characterPair_expand491 (N q : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) (n : ℤ)
    (χ ψ : DirichletCharacter ℂ q) :
    characterPair491 N q n χ ψ =
      (1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q χ * conjugateGauss491 q ψ *
        (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          χ ((a : ℕ) : ZMod q) * ψ ((a : ℕ) : ZMod q) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) *
        (∑' k : Nat.Primes × Nat.Primes,
          ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
            (χ ((k.1 : ℕ) : ZMod q) * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) *
              (ψ ((k.2 : ℕ) : ZMod q) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have htau : (0 : ℝ) ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
  have hab : (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by linarith
  have hχ : ∀ p : Nat.Primes, ‖χ ((p : ℕ) : ZMod q)‖ ≤ 1 := fun p =>
    DirichletCharacter.norm_le_one χ _
  have hψ : ∀ p : Nat.Primes, ‖ψ ((p : ℕ) : ZMod q)‖ ≤ 1 := fun p =>
    DirichletCharacter.norm_le_one ψ _
  have hIzn : (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
        characterPrime280 χ N z * characterPrime280 ψ N z *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
      ∑' k : Nat.Primes × Nat.Primes,
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
          (χ ((k.1 : ℕ) : ZMod q) * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) *
            (ψ ((k.2 : ℕ) : ZMod q) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    have hχt : ∀ z : ℝ, characterPrime280 χ N z =
        ∑' p : Nat.Primes, χ ((p : ℕ) : ZMod q) *
          ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
            Complex.exp (((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) :=
      fun z => characterPrime_eq_tsum491 N q χ z
    have hψt : ∀ z : ℝ, characterPrime280 ψ N z =
        ∑' p : Nat.Primes, ψ ((p : ℕ) : ZMod q) *
          ((Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
            Complex.exp (((-(2 * Real.pi * z * ((p : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) :=
      fun z => characterPrime_eq_tsum491 N q ψ z
    simp only [hχt, hψt]
    exact (hasSum_prime_square491 N hN n (fun p : Nat.Primes => χ ((p : ℕ) : ZMod q))
      (fun p : Nat.Primes => ψ ((p : ℕ) : ZMod q)) hχ hψ hab).tsum_eq.symm
  have hI : (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
        characterPrime280 χ N z * characterPrime280 ψ N z *
          Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
      ∑' k : Nat.Primes × Nat.Primes,
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
          (χ ((k.1 : ℕ) : ZMod q) * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) *
            (ψ ((k.2 : ℕ) : ZMod q) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    rw [show (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
        characterPrime280 χ N z * characterPrime280 ψ N z *
          Complex.exp (((2 * Real.pi * (n : ℝ) * z : ℝ) : ℂ) * Complex.I)) =
      (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
        characterPrime280 χ N z * characterPrime280 ψ N z *
          Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) from by
      apply intervalIntegral.integral_congr
      intro z _
      simp only []
      ring]
    exact hIzn
  unfold characterPair491
  exact congrArg (fun t => (1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q χ *
    conjugateGauss491 q ψ *
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        χ ((a : ℕ) : ZMod q) * ψ ((a : ℕ) : ZMod q) *
          Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) * t) hI

/-- LEAF. One ordered pair integral is bounded by the interval length times the pair
weight. -/
private lemma norm_pair_integral491 (N : ℕ) (n : ℤ) (c₁ c₂ : Nat.Primes → ℂ)
    (h₁ : ∀ p, ‖c₁ p‖ ≤ 1) (h₂ : ∀ p, ‖c₂ p‖ ≤ 1) {a b : ℝ} (hab : a ≤ b)
    (k : Nat.Primes × Nat.Primes) :
    ‖∫ z in a..b, (c₁ k.1 * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (c₂ k.2 * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      (b - a) * (Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N)) := by
  have hle : ∀ z ∈ Set.uIoc a b,
      ‖(c₁ k.1 * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (c₂ k.2 * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
        Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) := by
    intro z _
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact mul_le_mul (norm_twist_le491 N c₁ h₁ k.1 z) (norm_twist_le491 N c₂ h₂ k.2 z)
      (norm_nonneg _) (Real.exp_pos _).le
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hle
  simpa only [abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a), mul_comm] using h

/-- LEAF. The norms of the ordered pair integrals are summable. -/
private lemma pair_integral_summable491 (N : ℕ) (hN : 1 ≤ N) (n : ℤ)
    (c₁ c₂ : Nat.Primes → ℂ) (h₁ : ∀ p, ‖c₁ p‖ ≤ 1) (h₂ : ∀ p, ‖c₂ p‖ ≤ 1)
    {a b : ℝ} (hab : a ≤ b) :
    Summable (fun k : Nat.Primes × Nat.Primes =>
      ‖∫ z in a..b, (c₁ k.1 * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (c₂ k.2 * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (fun k => norm_pair_integral491 N n c₁ c₂ h₁ h₂ hab k) ?_
  exact Summable.mul_left _ (summable_pair_damp491 N hN)

/-- LEAF. One reduced residue of the character square: the finite character sum at
that residue is the single ordered prime pair coefficient. -/
private lemma rhs_residue_coeff491 (q : ℕ) [NeZero q] {a : ℕ} (ha : Nat.Coprime a q)
    (k : Nat.Primes × Nat.Primes) :
    (∑ p ∈ (univ : Finset (DirichletCharacter ℂ q)) ×ˢ
        (univ : Finset (DirichletCharacter ℂ q)),
      (1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q p.1 * conjugateGauss491 q p.2 *
        (p.1 ((a : ℕ) : ZMod q) * p.2 ((a : ℕ) : ZMod q)) *
        (p.1 ((k.1 : ℕ) : ZMod q) * p.2 ((k.2 : ℕ) : ZMod q))) =
      if Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q then
        Complex.exp (((-(2 * Real.pi * (((a : ℝ) * (((k.1 : ℕ) : ℝ) + ((k.2 : ℕ) : ℝ))) / (q : ℝ))) : ℝ) : ℂ) * Complex.I)
      else 0 := by
  classical
  have hqpos : 0 < q := NeZero.pos q
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hqpos
  have hφ2 : ((q.totient : ℂ)) ^ 2 ≠ 0 := by
    have h1 : ((q.totient : ℂ)) ≠ 0 := by
      simpa using (Complex.ofReal_ne_zero.mpr hφpos.ne')
    exact pow_ne_zero 2 h1
  rw [Finset.sum_product]
  have hkey := charPair_coeff491 q ha (k.1 : ℕ) (k.2 : ℕ)
  have hregroup : (∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
      (1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q χ * conjugateGauss491 q ψ *
        (χ ((a : ℕ) : ZMod q) * ψ ((a : ℕ) : ZMod q)) *
        (χ ((k.1 : ℕ) : ZMod q) * ψ ((k.2 : ℕ) : ZMod q))) =
      (1 / ((q.totient : ℂ)) ^ 2) * (∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
        (conjugateGauss491 q χ * χ (((a * (k.1 : ℕ) : ℕ)) : ZMod q)) *
          (conjugateGauss491 q ψ * ψ (((a * (k.2 : ℕ) : ℕ)) : ZMod q))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ψ _
    rw [Nat.cast_mul, Nat.cast_mul, map_mul χ, map_mul ψ]
    ring
  rw [hregroup, hkey]
  by_cases hg : Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q
  · rw [if_pos hg, if_pos hg]
    have hne : ((q.totient : ℂ)) ≠ 0 := by
      simpa using (Complex.ofReal_ne_zero.mpr hφpos.ne')
    field_simp
  · rw [if_neg hg, if_neg hg, mul_zero]

/-- LEAF. At one reduced residue, the finite character square against the ordered pair
integrals collapses to the pair coefficient times the plain pair integral. -/
private lemma rhs_per_a491 (N q : ℕ) [NeZero q] (hN : 1 ≤ N) (hq : 1 ≤ q) (n : ℤ)
    {a : ℕ} (ha : Nat.Coprime a q) :
    (∑ p ∈ (univ : Finset (DirichletCharacter ℂ q)) ×ˢ
        (univ : Finset (DirichletCharacter ℂ q)),
        (1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q p.1 * conjugateGauss491 q p.2 * (p.1 ((a : ℕ) : ZMod q) * p.2 ((a : ℕ) : ZMod q)) *
          (∑' k : Nat.Primes × Nat.Primes,
            ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)), (p.1 ((k.1 : ℕ) : ZMod q) * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (p.2 ((k.2 : ℕ) : ZMod q) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))) =
      ∑' k : Nat.Primes × Nat.Primes,
        (if Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q then
            Complex.exp (((-(2 * Real.pi * (((a : ℝ) * (((k.1 : ℕ) : ℝ) + ((k.2 : ℕ) : ℝ))) / (q : ℝ))) : ℝ) : ℂ) * Complex.I)
          else 0) *
          ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)), ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  classical
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have htau : (0 : ℝ) ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
  have hab : (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by linarith
  have hsumm : ∀ p ∈ (univ : Finset (DirichletCharacter ℂ q)) ×ˢ
      (univ : Finset (DirichletCharacter ℂ q)),
      Summable (fun k : Nat.Primes × Nat.Primes =>
        (1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q p.1 * conjugateGauss491 q p.2 * (p.1 ((a : ℕ) : ZMod q) * p.2 ((a : ℕ) : ZMod q)) * ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)), (p.1 ((k.1 : ℕ) : ZMod q) * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (p.2 ((k.2 : ℕ) : ZMod q) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
    intro p _
    refine Summable.of_norm_bounded (g := fun k : Nat.Primes × Nat.Primes =>
      ‖(1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q p.1 * conjugateGauss491 q p.2 * (p.1 ((a : ℕ) : ZMod q) * p.2 ((a : ℕ) : ZMod q))‖ *
        ((1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) - -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) *
          (Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N)))) ?_ ?_
    · exact Summable.mul_left _ (Summable.mul_left _ (summable_pair_damp491 N hN))
    · intro k
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_pair_integral491 N n (fun r : Nat.Primes => p.1 ((r : ℕ) : ZMod q))
          (fun r : Nat.Primes => p.2 ((r : ℕ) : ZMod q))
          (fun r => DirichletCharacter.norm_le_one p.1 _)
          (fun r => DirichletCharacter.norm_le_one p.2 _) hab k) (norm_nonneg _)
  simp only [← tsum_mul_left]
  rw [finset_tsum_swap491 _ _ hsumm]
  apply tsum_congr
  intro k
  have hstep : (∑ p ∈ (univ : Finset (DirichletCharacter ℂ q)) ×ˢ
        (univ : Finset (DirichletCharacter ℂ q)),
        (1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q p.1 * conjugateGauss491 q p.2 * (p.1 ((a : ℕ) : ZMod q) * p.2 ((a : ℕ) : ZMod q)) * ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)), (p.1 ((k.1 : ℕ) : ZMod q) * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (p.2 ((k.2 : ℕ) : ZMod q) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
      (∑ p ∈ (univ : Finset (DirichletCharacter ℂ q)) ×ˢ
        (univ : Finset (DirichletCharacter ℂ q)),
        (1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q p.1 * conjugateGauss491 q p.2 * (p.1 ((a : ℕ) : ZMod q) * p.2 ((a : ℕ) : ZMod q)) * (p.1 ((k.1 : ℕ) : ZMod q) * p.2 ((k.2 : ℕ) : ZMod q))) *
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)), ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    have h1 : (∑ p ∈ (univ : Finset (DirichletCharacter ℂ q)) ×ˢ
          (univ : Finset (DirichletCharacter ℂ q)),
          (1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q p.1 * conjugateGauss491 q p.2 * (p.1 ((a : ℕ) : ZMod q) * p.2 ((a : ℕ) : ZMod q)) * ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)), (p.1 ((k.1 : ℕ) : ZMod q) * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (p.2 ((k.2 : ℕ) : ZMod q) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
        ∑ p ∈ (univ : Finset (DirichletCharacter ℂ q)) ×ˢ
          (univ : Finset (DirichletCharacter ℂ q)),
          ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)), (1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q p.1 * conjugateGauss491 q p.2 * (p.1 ((a : ℕ) : ZMod q) * p.2 ((a : ℕ) : ZMod q)) * ((p.1 ((k.1 : ℕ) : ZMod q) * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (p.2 ((k.2 : ℕ) : ZMod q) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
      apply Finset.sum_congr rfl
      intro p _
      exact (intervalIntegral.integral_const_mul _ _).symm
    rw [h1]
    have h2 : (∑ p ∈ (univ : Finset (DirichletCharacter ℂ q)) ×ˢ
          (univ : Finset (DirichletCharacter ℂ q)),
          ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)), (1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q p.1 * conjugateGauss491 q p.2 * (p.1 ((a : ℕ) : ZMod q) * p.2 ((a : ℕ) : ZMod q)) * ((p.1 ((k.1 : ℕ) : ZMod q) * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (p.2 ((k.2 : ℕ) : ZMod q) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))) =
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)), ∑ p ∈ (univ : Finset (DirichletCharacter ℂ q)) ×ˢ
          (univ : Finset (DirichletCharacter ℂ q)),
          (1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q p.1 * conjugateGauss491 q p.2 * (p.1 ((a : ℕ) : ZMod q) * p.2 ((a : ℕ) : ZMod q)) * ((p.1 ((k.1 : ℕ) : ZMod q) * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (p.2 ((k.2 : ℕ) : ZMod q) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) :=
      (intervalIntegral.integral_finsetSum
        (fun p _ => Continuous.intervalIntegrable (by fun_prop) _ _)).symm
    rw [h2]
    have h3 : ∀ z : ℝ, (∑ p ∈ (univ : Finset (DirichletCharacter ℂ q)) ×ˢ
          (univ : Finset (DirichletCharacter ℂ q)),
          (1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q p.1 * conjugateGauss491 q p.2 * (p.1 ((a : ℕ) : ZMod q) * p.2 ((a : ℕ) : ZMod q)) * ((p.1 ((k.1 : ℕ) : ZMod q) * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (p.2 ((k.2 : ℕ) : ZMod q) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))) =
        (∑ p ∈ (univ : Finset (DirichletCharacter ℂ q)) ×ˢ
          (univ : Finset (DirichletCharacter ℂ q)),
          (1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q p.1 * conjugateGauss491 q p.2 * (p.1 ((a : ℕ) : ZMod q) * p.2 ((a : ℕ) : ZMod q)) * (p.1 ((k.1 : ℕ) : ZMod q) * p.2 ((k.2 : ℕ) : ZMod q))) * (((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
      intro z
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      ring
    simp only [h3]
    exact intervalIntegral.integral_const_mul _ _
  rw [hstep, rhs_residue_coeff491 q ha k]

/-- LEAF. The two twist constants of one ordered pair factor out of its integral. -/
private lemma pair_integral_const491 (N : ℕ) (n : ℤ) {l u : ℝ} (hlu : l ≤ u)
    (k : Nat.Primes × Nat.Primes) (c₁ c₂ : ℂ) :
    (∫ z in l..u, (c₁ * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (c₂ * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))
      = c₁ * c₂ * ∫ z in l..u, ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  simp only [show ∀ z : ℝ, (c₁ * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * (c₂ * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)
      = c₁ * c₂ * (((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) from fun z => by ring]
  exact intervalIntegral.integral_const_mul (c₁ * c₂) (fun z : ℝ =>
    (((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)))

/-- LEAF. At one reduced residue the ordered pair sum of the twisted pair integrals is
the ordered pair sum of the twist coefficients times the plain pair integrals. -/
private lemma pair_integral_const_tsum491 (N q : ℕ) (n : ℤ) {l u : ℝ} (hlu : l ≤ u)
    (a : ℕ) :
    (∑' k : Nat.Primes × Nat.Primes,
        ∫ z in l..u, ((Complex.exp (((-(2 * Real.pi * ((k.1 : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I)) * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) *
          ((Complex.exp (((-(2 * Real.pi * ((k.2 : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I)) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) =
      ∑' k : Nat.Primes × Nat.Primes,
        (Complex.exp (((-(2 * Real.pi * ((k.1 : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I)) * (Complex.exp (((-(2 * Real.pi * ((k.2 : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I)) *
          ∫ z in l..u, ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) * Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  apply tsum_congr
  intro k
  exact pair_integral_const491 N n hlu k _ _

/-- LEAF. The damped prime series is at most twice the scale. -/
private lemma tsum_prime_damp_le491 (N : ℕ) (hN : 1 ≤ N) :
    (∑' p : Nat.Primes, Real.exp (-((p : ℕ) : ℝ) / N)) ≤ 2 * (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hwpos (n : ℕ) : (0 : ℝ) < Real.exp (-(n : ℝ) / N) := Real.exp_pos _
  have hsum : Summable (fun n : ℕ => Real.exp (-(n : ℝ) / N)) :=
    damping_summable111 N hN
  have hsub : (∑' p : Nat.Primes, Real.exp (-((p : ℕ) : ℝ) / N)) =
      ∑' n : ℕ, Set.indicator {n : ℕ | n.Prime} (fun n => Real.exp (-(n : ℝ) / N)) n := by
    change (∑' p : {n : ℕ // n.Prime}, Real.exp (-((p : ℕ) : ℝ) / N)) = _
    exact tsum_subtype {n : ℕ | n.Prime} (fun n : ℕ => Real.exp (-(n : ℝ) / N))
  rw [hsub]
  have hle : (∑' n : ℕ, Set.indicator {n : ℕ | n.Prime}
        (fun n => Real.exp (-(n : ℝ) / N)) n) ≤
      ∑' n : ℕ, Real.exp (-(n : ℝ) / N) := by
    refine Summable.tsum_le_tsum (fun n => ?_) ?_ hsum
    · by_cases hp : n.Prime
      · rw [Set.indicator_of_mem (show n ∈ {n : ℕ | n.Prime} from hp)]
      · rw [Set.indicator_of_notMem (show n ∉ {n : ℕ | n.Prime} from hp)]
        exact (hwpos n).le
    · refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsum
      · by_cases hp : n.Prime
        · rw [Set.indicator_of_mem (show n ∈ {n : ℕ | n.Prime} from hp)]
          exact (hwpos n).le
        · rw [Set.indicator_of_notMem (show n ∉ {n : ℕ | n.Prime} from hp)]
      · by_cases hp : n.Prime
        · rw [Set.indicator_of_mem (show n ∈ {n : ℕ | n.Prime} from hp)]
        · rw [Set.indicator_of_notMem (show n ∉ {n : ℕ | n.Prime} from hp)]
          exact (hwpos n).le
  refine hle.trans ?_
  have hr0 : (0 : ℝ) ≤ Real.exp (-(1 / (N : ℝ))) := (Real.exp_pos _).le
  have hr1 : Real.exp (-(1 / (N : ℝ))) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : (0:ℝ) < 1 / (N:ℝ) := by positivity
    linarith
  have hgeom : (∑' n : ℕ, Real.exp (-(1 / (N : ℝ))) ^ n) = (1 - Real.exp (-(1 / (N : ℝ))))⁻¹ :=
    tsum_geometric_of_lt_one hr0 hr1
  have hrewrite : (∑' n : ℕ, Real.exp (-(n : ℝ) / N)) =
      ∑' n : ℕ, Real.exp (-(1 / (N : ℝ))) ^ n := by
    apply tsum_congr
    intro n
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hrewrite, hgeom]
  have h1 : 1 + 1 / (N:ℝ) ≤ Real.exp (1 / (N:ℝ)) := by
    have h := Real.add_one_le_exp (1 / (N:ℝ))
    linarith
  have hdenpos : (0:ℝ) < 1 + 1 / (N:ℝ) := by positivity
  have hrle : Real.exp (-(1 / (N : ℝ))) ≤ (1 + 1 / (N:ℝ))⁻¹ := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le hdenpos h1
  have hden : (1 + 1 / (N:ℝ)) ≤ 2 := by
    have h2 : (1:ℝ) ≤ N := by exact_mod_cast hN
    have h3 : 1 / (N:ℝ) ≤ 1 := by
      rw [div_le_one hNpos]
      exact h2
    linarith
  have hA : (1:ℝ) - (1 + 1 / (N:ℝ))⁻¹ = (1 / (N:ℝ)) / (1 + 1 / (N:ℝ)) := by
    field_simp
    ring
  have hmono : (1 / (N:ℝ)) / 2 ≤ (1 / (N:ℝ)) / (1 + 1 / (N:ℝ)) :=
    div_le_div_of_nonneg_left (by positivity) hdenpos hden
  have hgap : 1 / (2 * (N:ℝ)) ≤ 1 - Real.exp (-(1 / (N : ℝ))) := by
    calc 1 / (2 * (N:ℝ)) = (1 / (N:ℝ)) / 2 := by
          field_simp
      _ ≤ (1 / (N:ℝ)) / (1 + 1 / (N:ℝ)) := hmono
      _ = 1 - (1 + 1 / (N:ℝ))⁻¹ := hA.symm
      _ ≤ 1 - Real.exp (-(1 / (N : ℝ))) := by linarith
  have hgap2 : (0:ℝ) < 1 - Real.exp (-(1 / (N : ℝ))) := by
    have hpos2 : (0:ℝ) < 1 / (2 * (N:ℝ)) := by positivity
    linarith
  calc (1 - Real.exp (-(1 / (N : ℝ))))⁻¹ = 1 / (1 - Real.exp (-(1 / (N : ℝ)))) :=
        (one_div _).symm
    _ ≤ 1 / (1 / (2 * (N:ℝ))) :=
        one_div_le_one_div_of_le (by positivity : (0:ℝ) < 1 / (2 * (N:ℝ))) hgap
    _ = 2 * (N : ℝ) := by
        field_simp

/-- LEAF. The primes dividing the modulus are at most the divisor count of that set:
the indicator sum over the bad primes is bounded by the number of prime factors. -/
private lemma tsum_bad_prime_le491 (q : ℕ) (hq : 1 ≤ q) :
    (∑' p : Nat.Primes, if ¬ Nat.Coprime (p : ℕ) q then (1 : ℝ) else 0) ≤
      (q.primeFactors.card : ℝ) := by
  have h1 : (∑' p : Nat.Primes, if ¬ Nat.Coprime (p : ℕ) q then (1 : ℝ) else 0) =
      ∑' n : ℕ, Set.indicator {n : ℕ | n.Prime}
        (fun n : ℕ => if ¬ Nat.Coprime n q then (1 : ℝ) else 0) n := by
    change (∑' p : {n : ℕ // n.Prime}, if ¬ Nat.Coprime (p : ℕ) q then (1 : ℝ) else 0) = _
    exact tsum_subtype {n : ℕ | n.Prime}
      (fun n : ℕ => if ¬ Nat.Coprime n q then (1 : ℝ) else 0)
  rw [h1, tsum_eq_sum (s := q.primeFactors)]
  · have hcard : (∑ _n ∈ q.primeFactors, (1 : ℝ)) = (q.primeFactors.card : ℝ) := by simp
    rw [← hcard]
    refine Finset.sum_le_sum (fun n _ => ?_)
    rw [Set.indicator_apply]
    split_ifs <;> norm_num
  · intro n hn
    by_cases hp : n.Prime
    · have hcop : Nat.Coprime n q := by
        by_contra hc
        exact hn (Nat.mem_primeFactors.mpr ⟨hp, hp.dvd_iff_not_coprime.mpr hc, by omega⟩)
      rw [Set.indicator_of_mem (show n ∈ {n : ℕ | n.Prime} from hp), if_neg (by simp [hcop])]
    · rw [Set.indicator_of_notMem (show n ∉ {n : ℕ | n.Prime} from hp)]

/-- LEAF. The number of distinct prime divisors of a modulus at least two is at most
twice the logarithm of the modulus. -/
private lemma card_primeFactors_le_log491 (q : ℕ) (hq : 2 ≤ q) :
    (q.primeFactors.card : ℝ) ≤ 2 * Real.log q := by
  have h2q : (2:ℕ)^q.primeFactors.card ≤ q := by
    refine (Finset.pow_card_le_prod q.primeFactors (fun p => p) 2
      (fun p hp => (Nat.mem_primeFactors.mp hp).1.two_le)).trans ?_
    exact Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
  have hcast : (((2:ℕ)^q.primeFactors.card : ℕ) : ℝ) ≤ (q:ℝ) := by exact_mod_cast h2q
  have hlog : (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log q := by
    have h := Real.log_le_log
      (show (0:ℝ) < (((2:ℕ)^q.primeFactors.card : ℕ) : ℝ) by positivity) hcast
    rwa [show Real.log ((((2:ℕ)^q.primeFactors.card : ℕ)) : ℝ) =
        (q.primeFactors.card : ℝ) * Real.log 2 from by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]] at h
  have hlog2pos : (0:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hcard : (q.primeFactors.card : ℝ) ≤ Real.log q / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]
    exact hlog
  have hqlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have h2 : Real.log q / Real.log 2 ≤ Real.log q / (1/2) :=
    div_le_div_of_nonneg_left hqlog (by norm_num) (by linarith [Real.log_two_gt_d9])
  have hfin : Real.log q / (1/2) = 2 * Real.log q := by
    field_simp
  linarith


/-- LEAF. Generic pull-out: the residue sum inside the character pair coefficient can be
moved outside the character sums, producing the phase factor at every reduced residue. -/
private lemma pull_out_residue_sum491 (q : ℕ) (n : ℤ)
    (c J : DirichletCharacter ℂ q → DirichletCharacter ℂ q → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q, c χ ψ *
        (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          (χ ((a : ℕ) : ZMod q) * ψ ((a : ℕ) : ZMod q) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I))) *
        J χ ψ) =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
          ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
            c χ ψ * (χ ((a : ℕ) : ZMod q) * ψ ((a : ℕ) : ZMod q)) * J χ ψ := by
  classical
  have hterm : ∀ χ ψ : DirichletCharacter ℂ q, c χ ψ *
        (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          (χ ((a : ℕ) : ZMod q) * ψ ((a : ℕ) : ZMod q) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I))) *
        J χ ψ =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
          (c χ ψ * (χ ((a : ℕ) : ZMod q) * ψ ((a : ℕ) : ZMod q)) * J χ ψ) := by
    intro χ ψ
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  simp only [hterm]
  have hinner : ∀ χ : DirichletCharacter ℂ q,
      (∑ ψ : DirichletCharacter ℂ q,
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
            (c χ ψ * (χ ((a : ℕ) : ZMod q) * ψ ((a : ℕ) : ZMod q)) * J χ ψ)) =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∑ ψ : DirichletCharacter ℂ q,
          Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
            (c χ ψ * (χ ((a : ℕ) : ZMod q) * ψ ((a : ℕ) : ZMod q)) * J χ ψ) :=
    fun χ => Finset.sum_comm
  simp only [hinner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  rw [Finset.mul_sum]

/-- LEAF. The local arc as an ordered prime pair sum with the residue phases factored
out of the pair integrals. -/
private lemma localArc_pair_form491 (N q : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) (n : ℤ) :
    localArc1622 N q n =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
          ∑' k : Nat.Primes × Nat.Primes,
            (Complex.exp (((-(2 * Real.pi * ((k.1 : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I)) *
            (Complex.exp (((-(2 * Real.pi * ((k.2 : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I)) *
            ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
              ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) *
              ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) *
              Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlu : (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) ≤
      1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    have hpos : (0 : ℝ) < 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
    linarith
  rw [localArc_expand491 N q hN hq n]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  exact pair_integral_const_tsum491 N q n hlu a

/-- LEAF. The character square sum with the residue sum pulled out, every reduced residue
carrying the ordered pair coefficient of the Gauss orthogonality. -/
private lemma pairSum_form491 (N q : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) (n : ℤ) :
    (∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q, characterPair491 N q n χ ψ) =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
          ∑' k : Nat.Primes × Nat.Primes,
            (if Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q then
              Complex.exp (((-(2 * Real.pi * (((a : ℝ) * (((k.1 : ℕ) : ℝ) + ((k.2 : ℕ) : ℝ))) / (q : ℝ))) : ℝ) : ℂ) * Complex.I)
              else 0) *
            ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
              ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) *
              ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) *
              Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  classical
  letI : NeZero q := ⟨by omega⟩
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlu : (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) ≤
      1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    have hpos : (0 : ℝ) < 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
    linarith
  have hexp : ∀ χ ψ : DirichletCharacter ℂ q, characterPair491 N q n χ ψ =
      (1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q χ * conjugateGauss491 q ψ *
        (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          χ ((a : ℕ) : ZMod q) * ψ ((a : ℕ) : ZMod q) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) *
        (∑' k : Nat.Primes × Nat.Primes,
          ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
            (χ ((k.1 : ℕ) : ZMod q) * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) *
            (ψ ((k.2 : ℕ) : ZMod q) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) *
            Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) :=
    fun χ ψ => characterPair_expand491 N q hN hq n χ ψ
  simp only [hexp]
  rw [pull_out_residue_sum491 q n
    (fun χ ψ => (1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q χ * conjugateGauss491 q ψ)
    (fun χ ψ => ∑' k : Nat.Primes × Nat.Primes,
      ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
        (χ ((k.1 : ℕ) : ZMod q) * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) *
        (ψ ((k.2 : ℕ) : ZMod q) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) *
        Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  have hrhs := rhs_per_a491 N q hN hq n (a := a) (Finset.mem_filter.mp ha).2
  have hbridge : (∑ p ∈ (univ : Finset (DirichletCharacter ℂ q)) ×ˢ
        (univ : Finset (DirichletCharacter ℂ q)),
        (1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q p.1 * conjugateGauss491 q p.2 *
          (p.1 ((a : ℕ) : ZMod q) * p.2 ((a : ℕ) : ZMod q)) *
          (∑' k : Nat.Primes × Nat.Primes,
            ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
              (p.1 ((k.1 : ℕ) : ZMod q) * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) *
              (p.2 ((k.2 : ℕ) : ZMod q) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) *
              Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))) =
      ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
        ((1 / ((q.totient : ℂ)) ^ 2) * conjugateGauss491 q χ * conjugateGauss491 q ψ *
          (χ ((a : ℕ) : ZMod q) * ψ ((a : ℕ) : ZMod q))) *
          (∑' k : Nat.Primes × Nat.Primes,
            ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
              (χ ((k.1 : ℕ) : ZMod q) * ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) *
              (ψ ((k.2 : ℕ) : ZMod q) * ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) *
              Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) := by
    rw [Finset.sum_product]
  rw [← hbridge]
  exact hrhs

/-- LEAF. The ordered prime pairs with a bad slot carry at most twice the divisor count
of the modulus times the damped prime mass of the other slot. -/
private lemma pair_weight_factor491 (f g : Nat.Primes → ℝ) (hf : Summable f) (hg : Summable g) :
    (∑' k : Nat.Primes × Nat.Primes, f k.1 * g k.2) = (∑' p, f p) * (∑' p, g p) :=
  (tsum_mul_tsum_of_summable_norm hf.norm hg.norm).symm

/-- LEAF. The bad ordered prime pairs are bounded by twice the prime divisor count times
the damped prime mass. -/
private lemma bad_pair_weight_le491 (N q : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) :
    (∑' k : Nat.Primes × Nat.Primes,
      (if ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q) then
        Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0))
      ≤ 4 * (q.primeFactors.card : ℝ) * (N : ℝ) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  -- the pointwise majorant splits the bad condition over the two slots
  have hpt : ∀ k : Nat.Primes × Nat.Primes,
      (if ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q) then
        Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0)
      ≤ (if ¬ Nat.Coprime (k.1 : ℕ) q then
            Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0)
        + (if ¬ Nat.Coprime (k.2 : ℕ) q then
            Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0) := by
    intro k
    have hw : (0 : ℝ) ≤ Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) := by
      positivity
    by_cases h1 : Nat.Coprime (k.1 : ℕ) q
    · by_cases h2 : Nat.Coprime (k.2 : ℕ) q
      · rw [if_neg (by simp [h1, h2]), if_neg (by simp [h1]), if_neg (by simp [h2])]
        linarith
      · rw [if_pos (by simp [h1, h2]), if_neg (by simp [h1]), if_pos (by simp [h2])]
        linarith
    · rw [if_pos (by simp [h1]), if_pos (by simp [h1])]
      by_cases h2 : Nat.Coprime (k.2 : ℕ) q
      · rw [if_neg (by simp [h2])]
        linarith
      · rw [if_pos (by simp [h2])]
        linarith
  have hmaj : Summable (fun k : Nat.Primes × Nat.Primes =>
      (if ¬ Nat.Coprime (k.1 : ℕ) q then
          Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0)
        + (if ¬ Nat.Coprime (k.2 : ℕ) q then
            Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0)) := by
    refine Summable.add ?_ ?_
    · refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
        (summable_pair_damp491 N hN)
      by_cases h : Nat.Coprime (k.1 : ℕ) q
      · rw [if_neg (by simp [h])]; positivity
      · rw [if_pos (by simp [h])]
    · refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
        (summable_pair_damp491 N hN)
      by_cases h : Nat.Coprime (k.2 : ℕ) q
      · rw [if_neg (by simp [h])]; positivity
      · rw [if_pos (by simp [h])]
  have hmin : Summable (fun k : Nat.Primes × Nat.Primes =>
      (if ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q) then
        Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0)) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hpt hmaj
  refine (Summable.tsum_le_tsum hpt hmin hmaj).trans ?_
  -- evaluate the majorant
  have hfb : Summable (fun p : Nat.Primes => Real.exp (-((p : ℕ) : ℝ) / N)) :=
    (damping_summable111 N hN).comp_injective Nat.Primes.coe_nat_injective
  have hfa : Summable (fun p : Nat.Primes =>
      if ¬ Nat.Coprime (p : ℕ) q then Real.exp (-((p : ℕ) : ℝ) / N) else 0) :=
    Summable.of_nonneg_of_le (fun p => by positivity) (fun p => by
      by_cases h : Nat.Coprime (p : ℕ) q
      · rw [if_neg (by simp [h])]
        positivity
      · rw [if_pos (by simp [h])]) hfb
  have h1 : (∑' k : Nat.Primes × Nat.Primes,
      (if ¬ Nat.Coprime (k.1 : ℕ) q then
        Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0))
      = (∑' p : Nat.Primes, if ¬ Nat.Coprime (p : ℕ) q then Real.exp (-((p : ℕ) : ℝ) / N) else 0)
        * (∑' p : Nat.Primes, Real.exp (-((p : ℕ) : ℝ) / N)) := by
    rw [← pair_weight_factor491
      (fun p => if ¬ Nat.Coprime (p : ℕ) q then Real.exp (-((p : ℕ) : ℝ) / N) else 0)
      (fun p => Real.exp (-((p : ℕ) : ℝ) / N)) hfa hfb]
    apply tsum_congr
    intro k
    by_cases h : Nat.Coprime (k.1 : ℕ) q
    · rw [if_neg (by simp [h]), if_neg (by simp [h]), zero_mul]
    · rw [if_pos (by simp [h]), if_pos (by simp [h])]
  have h2 : (∑' k : Nat.Primes × Nat.Primes,
      (if ¬ Nat.Coprime (k.2 : ℕ) q then
        Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0))
      = (∑' p : Nat.Primes, Real.exp (-((p : ℕ) : ℝ) / N))
        * (∑' p : Nat.Primes, if ¬ Nat.Coprime (p : ℕ) q then Real.exp (-((p : ℕ) : ℝ) / N) else 0) := by
    rw [← pair_weight_factor491
      (fun p => Real.exp (-((p : ℕ) : ℝ) / N))
      (fun p => if ¬ Nat.Coprime (p : ℕ) q then Real.exp (-((p : ℕ) : ℝ) / N) else 0) hfb hfa]
    apply tsum_congr
    intro k
    by_cases h : Nat.Coprime (k.2 : ℕ) q
    · rw [if_neg (by simp [h]), if_neg (by simp [h]), mul_zero]
    · rw [if_pos (by simp [h]), if_pos (by simp [h])]
  have hf1 : Summable (fun k : Nat.Primes × Nat.Primes =>
      (if ¬ Nat.Coprime (k.1 : ℕ) q then
        Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0)) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (summable_pair_damp491 N hN)
    by_cases h : Nat.Coprime (k.1 : ℕ) q
    · rw [if_neg (by simp [h])]
      positivity
    · rw [if_pos (by simp [h])]
  have hf2 : Summable (fun k : Nat.Primes × Nat.Primes =>
      (if ¬ Nat.Coprime (k.2 : ℕ) q then
        Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0)) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (summable_pair_damp491 N hN)
    by_cases h : Nat.Coprime (k.2 : ℕ) q
    · rw [if_neg (by simp [h])]
      positivity
    · rw [if_pos (by simp [h])]
  rw [Summable.tsum_add hf1 hf2, h1, h2]
  -- bound each factor
  have hB : (∑' p : Nat.Primes, if ¬ Nat.Coprime (p : ℕ) q then Real.exp (-((p : ℕ) : ℝ) / N) else 0)
      ≤ (q.primeFactors.card : ℝ) := by
    have h1 : (∑' p : Nat.Primes,
        if ¬ Nat.Coprime (p : ℕ) q then Real.exp (-((p : ℕ) : ℝ) / N) else 0) =
        ∑' n : ℕ, Set.indicator {n : ℕ | n.Prime}
          (fun n : ℕ => if ¬ Nat.Coprime n q then Real.exp (-(n : ℝ) / N) else 0) n := by
      change (∑' p : {n : ℕ // n.Prime},
        if ¬ Nat.Coprime (p : ℕ) q then Real.exp (-((p : ℕ) : ℝ) / N) else 0) = _
      exact tsum_subtype {n : ℕ | n.Prime}
        (fun n : ℕ => if ¬ Nat.Coprime n q then Real.exp (-(n : ℝ) / N) else 0)
    rw [h1, tsum_eq_sum (s := q.primeFactors)]
    · have hc : (∑ _n ∈ q.primeFactors, (1 : ℝ)) = (q.primeFactors.card : ℝ) := by simp
      rw [← hc]
      refine Finset.sum_le_sum (fun n _ => ?_)
      rw [Set.indicator_apply]
      by_cases hp : n.Prime
      · rw [if_pos (show n ∈ {n : ℕ | Nat.Prime n} from hp)]
        by_cases hnc : Nat.Coprime n q
        · rw [if_neg (by simp [hnc])]
          norm_num
        · rw [if_pos (by simp [hnc])]
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by
            have h1 : (-(n : ℝ)) ≤ 0 := neg_nonpos.mpr (by positivity)
            have h2 : (0 : ℝ) ≤ (N : ℝ) := by positivity
            exact div_nonpos_of_nonpos_of_nonneg h1 h2)
      · rw [if_neg (show n ∉ {n : ℕ | Nat.Prime n} from hp)]
        norm_num
    · intro n hn
      by_cases hp : n.Prime
      · have hcop : Nat.Coprime n q := by
          by_contra hc
          exact hn (Nat.mem_primeFactors.mpr ⟨hp, hp.dvd_iff_not_coprime.mpr hc, by omega⟩)
        rw [Set.indicator_of_mem (show n ∈ {n : ℕ | n.Prime} from hp), if_neg (by simp [hcop])]
      · rw [Set.indicator_of_notMem (show n ∉ {n : ℕ | n.Prime} from hp)]
  have hS : (∑' p : Nat.Primes, Real.exp (-((p : ℕ) : ℝ) / N)) ≤ 2 * (N : ℝ) :=
    tsum_prime_damp_le491 N hN
  have hB0 : (0 : ℝ) ≤ (q.primeFactors.card : ℝ) := by positivity
  have hS0 : (0 : ℝ) ≤ (∑' p : Nat.Primes, Real.exp (-((p : ℕ) : ℝ) / N)) := by positivity
  have hBs : (0 : ℝ) ≤ (∑' p : Nat.Primes, if ¬ Nat.Coprime (p : ℕ) q then Real.exp (-((p : ℕ) : ℝ) / N) else 0) := by
    positivity
  have hstep1 : (∑' p : Nat.Primes, if ¬ Nat.Coprime (p : ℕ) q then Real.exp (-((p : ℕ) : ℝ) / N) else 0)
      * (∑' p : Nat.Primes, Real.exp (-((p : ℕ) : ℝ) / N))
      ≤ (q.primeFactors.card : ℝ) * (2 * (N : ℝ)) := by
    apply mul_le_mul hB hS hS0 hB0
  have hstep2 : (∑' p : Nat.Primes, Real.exp (-((p : ℕ) : ℝ) / N))
      * (∑' p : Nat.Primes, if ¬ Nat.Coprime (p : ℕ) q then Real.exp (-((p : ℕ) : ℝ) / N) else 0)
      ≤ 2 * (N : ℝ) * (q.primeFactors.card : ℝ) := by
    apply mul_le_mul hS hB hBs (by positivity)
  linarith

/-- LEAF. Per residue, the ordered pair sums of the local arc and of the character square
agree except on the ordered pairs with a prime dividing the modulus. -/
private lemma pair_diff_bound491 (N q : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) (n : ℤ) (a : ℕ) :
    ‖Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
        (∑' k : Nat.Primes × Nat.Primes,
          (Complex.exp (((-(2 * Real.pi * ((k.1 : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I)) *
          (Complex.exp (((-(2 * Real.pi * ((k.2 : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I)) *
          ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
            ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) *
            ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) *
            Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) -
      Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
        (∑' k : Nat.Primes × Nat.Primes,
          (if Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q then
            Complex.exp (((-(2 * Real.pi * (((a : ℝ) * (((k.1 : ℕ) : ℝ) + ((k.2 : ℕ) : ℝ))) / (q : ℝ))) : ℝ) : ℂ) * Complex.I)
            else 0) *
          ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
            ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) *
            ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) *
            Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I))‖ ≤
      (2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) *
        (∑' k : Nat.Primes × Nat.Primes,
          if ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q) then
            Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0) := by
  classical
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlu : (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) ≤
      1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    have hp : (0 : ℝ) < 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by positivity
    linarith
  let I : Nat.Primes × Nat.Primes → ℂ := fun k =>
    ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
      ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) *
      ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) *
      Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)
  let e : ℂ := Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)
  let ph : Nat.Primes → ℂ := fun p =>
    Complex.exp (((-(2 * Real.pi * ((p : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I)
  let P : Nat.Primes × Nat.Primes → ℂ := fun k =>
    Complex.exp (((-(2 * Real.pi * (((a : ℝ) * (((k.1 : ℕ) : ℝ) + ((k.2 : ℕ) : ℝ))) / (q : ℝ))) : ℝ) : ℂ) * Complex.I)
  have hIeq : I = fun k =>
      ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
        ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) *
        ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) *
        Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I) := rfl
  have heq : e = Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) := rfl
  have hpheq : ph = fun p : Nat.Primes =>
      Complex.exp (((-(2 * Real.pi * (((p : ℕ) : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I) := rfl
  have hPeq : P = fun k =>
      Complex.exp (((-(2 * Real.pi * (((a : ℝ) * (((k.1 : ℕ) : ℝ) + ((k.2 : ℕ) : ℝ))) / (q : ℝ))) : ℝ) : ℂ) * Complex.I) := rfl
  change ‖e * (∑' k : Nat.Primes × Nat.Primes, ph k.1 * ph k.2 * I k) -
      e * (∑' k : Nat.Primes × Nat.Primes,
        (if Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q then P k else 0) * I k)‖ ≤
    (2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) *
      (∑' k : Nat.Primes × Nat.Primes,
        if ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q) then
          Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0)
  have hen : ‖e‖ = 1 := by
    rw [heq]
    exact Complex.norm_exp_ofReal_mul_I _
  have hcoef : ∀ k : Nat.Primes × Nat.Primes, ph k.1 * ph k.2 = P k := by
    intro k
    rw [hpheq, hPeq]
    simp only []
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hnormI : ∀ k : Nat.Primes × Nat.Primes, ‖I k‖ ≤
      (2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) *
        (Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N)) := by
    intro k
    have h := norm_pair_integral491 N n (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ))
      (fun _ => by simp) (fun _ => by simp) hlu k
    rw [hIeq]
    simp only []
    have hb : (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) -
        (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) =
        2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by ring
    rw [hb] at h
    simpa only [one_mul] using h
  have hbound : ∀ k : Nat.Primes × Nat.Primes, 0 ≤
      Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) := by
    intro k
    positivity
  have hsumm : Summable (fun k : Nat.Primes × Nat.Primes =>
      (Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N))) :=
    summable_pair_damp491 N hN
  have hs1 : Summable (fun k : Nat.Primes × Nat.Primes => ph k.1 * ph k.2 * I k) := by
    refine Summable.of_norm_bounded (g := fun k : Nat.Primes × Nat.Primes =>
      (2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) *
        (Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N)))
      (Summable.mul_left _ hsumm) ?_
    intro k
    have hp1 : ‖ph k.1‖ = 1 := by
      rw [hpheq]
      exact Complex.norm_exp_ofReal_mul_I _
    have hp2 : ‖ph k.2‖ = 1 := by
      rw [hpheq]
      exact Complex.norm_exp_ofReal_mul_I _
    calc ‖ph k.1 * ph k.2 * I k‖ = ‖ph k.1‖ * ‖ph k.2‖ * ‖I k‖ := by rw [norm_mul, norm_mul]
      _ = ‖I k‖ := by rw [hp1, hp2]; ring
      _ ≤ _ := hnormI k
  have hs2 : Summable (fun k : Nat.Primes × Nat.Primes =>
      (if Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q then P k else 0) * I k) := by
    refine Summable.of_norm_bounded (g := fun k : Nat.Primes × Nat.Primes =>
      (2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) *
        (Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N)))
      (Summable.mul_left _ hsumm) ?_
    intro k
    by_cases hc : Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q
    · rw [if_pos hc]
      have hp : ‖P k‖ = 1 := by
        rw [hPeq]
        exact Complex.norm_exp_ofReal_mul_I _
      calc ‖P k * I k‖ = ‖P k‖ * ‖I k‖ := norm_mul _ _
        _ = ‖I k‖ := by rw [hp, one_mul]
        _ ≤ _ := hnormI k
    · rw [if_neg hc, zero_mul, norm_zero]
      positivity
  have hdiff : (∑' k : Nat.Primes × Nat.Primes, ph k.1 * ph k.2 * I k) -
      (∑' k : Nat.Primes × Nat.Primes,
        (if Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q then P k else 0) * I k) =
      ∑' k : Nat.Primes × Nat.Primes,
        (if ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q) then ph k.1 * ph k.2 * I k else 0) := by
    rw [← Summable.tsum_sub hs1 hs2]
    apply tsum_congr
    intro k
    by_cases hc : Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q
    · rw [if_pos hc, if_neg (by simp [hc]), hcoef k, sub_self]
    · rw [if_neg hc, if_pos (by simp [hc]), zero_mul, sub_zero]
  have hmaj2 : Summable (fun k : Nat.Primes × Nat.Primes =>
      (if ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q) then ph k.1 * ph k.2 * I k else 0)) := by
    refine Summable.of_norm_bounded (g := fun k : Nat.Primes × Nat.Primes =>
      (2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) *
        (Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N)))
      (Summable.mul_left _ hsumm) ?_
    intro k
    by_cases hc : Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q
    · rw [if_neg (by simp [hc]), norm_zero]
      positivity
    · rw [if_pos (by simp [hc])]
      have hp1 : ‖ph k.1‖ = 1 := by
        rw [hpheq]
        exact Complex.norm_exp_ofReal_mul_I _
      have hp2 : ‖ph k.2‖ = 1 := by
        rw [hpheq]
        exact Complex.norm_exp_ofReal_mul_I _
      calc ‖ph k.1 * ph k.2 * I k‖ = ‖ph k.1‖ * ‖ph k.2‖ * ‖I k‖ := by rw [norm_mul, norm_mul]
        _ = ‖I k‖ := by rw [hp1, hp2]; ring
        _ ≤ _ := hnormI k
  have hsumm2 : Summable (fun k : Nat.Primes × Nat.Primes =>
      ‖(if ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q) then ph k.1 * ph k.2 * I k else 0)‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      (Summable.mul_left (2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) hsumm)
    by_cases hc : Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q
    · rw [if_neg (by simp [hc]), norm_zero]
      positivity
    · rw [if_pos (by simp [hc])]
      have hp1 : ‖ph k.1‖ = 1 := by
        rw [hpheq]
        exact Complex.norm_exp_ofReal_mul_I _
      have hp2 : ‖ph k.2‖ = 1 := by
        rw [hpheq]
        exact Complex.norm_exp_ofReal_mul_I _
      calc ‖ph k.1 * ph k.2 * I k‖ = ‖ph k.1‖ * ‖ph k.2‖ * ‖I k‖ := by rw [norm_mul, norm_mul]
        _ = ‖I k‖ := by rw [hp1, hp2]; ring
        _ ≤ _ := hnormI k
  have hkey : ‖e * (∑' k : Nat.Primes × Nat.Primes, ph k.1 * ph k.2 * I k) -
      e * (∑' k : Nat.Primes × Nat.Primes,
        (if Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q then P k else 0) * I k)‖
      ≤ (∑' k : Nat.Primes × Nat.Primes,
          (if ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q) then
            (2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) *
              (Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N)) else 0)) := by
    have h1 : e * (∑' k : Nat.Primes × Nat.Primes, ph k.1 * ph k.2 * I k) -
        e * (∑' k : Nat.Primes × Nat.Primes,
          (if Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q then P k else 0) * I k)
        = e * ((∑' k : Nat.Primes × Nat.Primes, ph k.1 * ph k.2 * I k) -
          (∑' k : Nat.Primes × Nat.Primes,
            (if Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q then P k else 0) * I k)) := by
      ring
    rw [h1, norm_mul, hen, one_mul, hdiff]
    have hpt3 : ∀ k : Nat.Primes × Nat.Primes,
        ‖(if ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q) then
            ph k.1 * ph k.2 * I k else 0)‖
          ≤ (if ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q) then
              (2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) *
                (Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N)) else 0) := by
      intro k
      by_cases hc : Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q
      · rw [if_neg (by simp [hc]), if_neg (by simp [hc])]
        simp
      · rw [if_pos (by simp [hc]), if_pos (by simp [hc])]
        have hp1 : ‖ph k.1‖ = 1 := by
          rw [hpheq]
          exact Complex.norm_exp_ofReal_mul_I _
        have hp2 : ‖ph k.2‖ = 1 := by
          rw [hpheq]
          exact Complex.norm_exp_ofReal_mul_I _
        calc ‖ph k.1 * ph k.2 * I k‖ = ‖ph k.1‖ * ‖ph k.2‖ * ‖I k‖ := by rw [norm_mul, norm_mul]
          _ = ‖I k‖ := by rw [hp1, hp2]; ring
          _ ≤ _ := hnormI k
    have hmin3 : Summable (fun k : Nat.Primes × Nat.Primes =>
        (if ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q) then
          Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0)) := by
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hsumm
      by_cases hc : Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q
      · rw [if_neg (by simp [hc])]
        positivity
      · rw [if_pos (by simp [hc])]
    have hmaj3 : Summable (fun k : Nat.Primes × Nat.Primes =>
        (if ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q) then
          (2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) *
            (Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N)) else 0)) := by
      have h := Summable.mul_left (2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) hmin3
      simpa only [mul_ite, mul_zero] using h
    refine (norm_tsum_le_tsum_norm hsumm2).trans ?_
    exact Summable.tsum_le_tsum hpt3 hsumm2 hmaj3
  refine hkey.trans ?_
  rw [← tsum_mul_left]
  apply le_of_eq
  apply tsum_congr
  intro k
  by_cases hc : ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q)
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc, mul_zero]

/-- LEAF. The finite character square expansion: the local arc and the double character
pair sum differ only through the ordered prime pairs with a prime dividing the modulus. -/
private lemma expansion_general491 (N q : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) (n : ℤ) :
    ‖localArc1622 N q n -
        (∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
          characterPair491 N q n χ ψ)‖ ≤
      8 * (q.primeFactors.card : ℝ) * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have h7pos : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hBAD := bad_pair_weight_le491 N q hN hq
  rw [localArc_pair_form491 N q hN hq n, pairSum_form491 N q hN hq n,
    ← Finset.sum_sub_distrib]
  have hcard : ((range q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    ext x
    simp [Nat.coprime_comm]
  calc ‖∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        (Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
          (∑' k : Nat.Primes × Nat.Primes,
            (Complex.exp (((-(2 * Real.pi * ((k.1 : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I)) *
            (Complex.exp (((-(2 * Real.pi * ((k.2 : ℝ) * ((a : ℝ) / (q : ℝ)))) : ℝ) : ℂ) * Complex.I)) *
            ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
              ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) *
              ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) *
              Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)) -
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) *
          (∑' k : Nat.Primes × Nat.Primes,
            (if Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q then
              Complex.exp (((-(2 * Real.pi * (((a : ℝ) * (((k.1 : ℕ) : ℝ) + ((k.2 : ℕ) : ℝ))) / (q : ℝ))) : ℝ) : ℂ) * Complex.I)
              else 0) *
            ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)),
              ((Real.exp (-((k.1 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) *
              ((Real.exp (-((k.2 : ℕ) : ℝ) / N) : ℂ) * Complex.exp (((-(2 * Real.pi * z * ((k.2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) *
              Complex.exp (((2 * Real.pi * z * (n : ℝ) : ℝ) : ℂ) * Complex.I)))‖
      ≤ ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          (2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) *
            (∑' k : Nat.Primes × Nat.Primes,
              if ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q) then
                Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0) := by
        refine (norm_sum_le _ _).trans ?_
        exact Finset.sum_le_sum (fun a ha => pair_diff_bound491 N q hN hq n a)
    _ = (q.totient : ℝ) * ((2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) *
          (∑' k : Nat.Primes × Nat.Primes,
            if ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q) then
              Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0)) := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ ≤ (q : ℝ) * ((2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) *
          (∑' k : Nat.Primes × Nat.Primes,
            if ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q) then
              Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0)) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast Nat.totient_le q
    _ = 2 * (∑' k : Nat.Primes × Nat.Primes,
          if ¬ (Nat.Coprime (k.1 : ℕ) q ∧ Nat.Coprime (k.2 : ℕ) q) then
            Real.exp (-((k.1 : ℕ) : ℝ) / N) * Real.exp (-((k.2 : ℕ) : ℝ) / N) else 0) /
          (N : ℝ) ^ (1 / 7 : ℝ) := by
      have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
      have hqne : (q : ℝ) ≠ 0 := hqpos.ne'
      have h7ne : (N : ℝ) ^ (1 / 7 : ℝ) ≠ 0 := h7pos.ne'
      field_simp
    _ ≤ 2 * (4 * (q.primeFactors.card : ℝ) * (N : ℝ)) / (N : ℝ) ^ (1 / 7 : ℝ) := by
      apply div_le_div_of_nonneg_right ?_ h7pos.le
      linarith
    _ = 8 * (q.primeFactors.card : ℝ) * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) := by ring

/-- LEAF. The conjugate Gauss coefficient of the principal character is the
Moebius value at the modulus. -/
private lemma conjGauss_one491 (q : ℕ) (hq : 1 ≤ q) :
    conjugateGauss491 q (1 : DirichletCharacter ℂ q) = (ArithmeticFunction.moebius q : ℂ) := by
  have hone : conjugateGauss491 q (1 : DirichletCharacter ℂ q) =
      star (signedRamanujan491 q 1) := by
    unfold conjugateGauss491 signedRamanujan491
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
    have hunit : IsUnit ((a : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr hcop
    rw [MulChar.one_apply hunit, one_mul]
    congr 1
    push_cast
    ring
  rw [hone, signedRamanujan_toNat491 q 1 (by norm_num)]
  have hto : (Int.toNat 1 : ℕ) = 1 := rfl
  rw [hto, LeanLab.Perelli1996.Ramanujan103.ramanujanSum_coprime q 1 (by omega)
      (Nat.coprime_one_right q)]
  simp

/-- LEAF. The ordered pair of two principal characters is the principal term. -/
private lemma pair_one_one491 (N q : ℕ) (hq : 1 ≤ q) (n : ℤ) :
    characterPair491 N q n 1 1 = principalTerm491 N q n := by
  have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (show 0 < q by omega)
  have hτ : conjugateGauss491 q (1 : DirichletCharacter ℂ q) =
      (ArithmeticFunction.moebius q : ℂ) := conjGauss_one491 q hq
  have hone (a : ℕ) (ha : a ∈ (range q).filter (fun a => Nat.Coprime a q)) :
      (1 : DirichletCharacter ℂ q) a = 1 := by
    have hcop : Nat.Coprime a q := (Finset.mem_filter.mp ha).2
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime a q).mpr hcop)
  unfold characterPair491 principalTerm491 principalIntegral491 signedRamanujan491
  rw [hτ]
  have hsum : (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      (1 : DirichletCharacter ℂ q) a * (1 : DirichletCharacter ℂ q) a *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) =
      ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q) : ℝ) : ℂ) * Complex.I) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [hone a ha]
    ring
  rw [hsum]
  have hcoef : (1 / ((q.totient : ℂ)) ^ 2) * ((ArithmeticFunction.moebius q : ℂ)) *
      ((ArithmeticFunction.moebius q : ℂ)) =
      (((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 : ℝ) : ℂ) := by
    have hne : ((q.totient : ℂ)) ≠ 0 := by
      simpa using (Complex.ofReal_ne_zero.mpr hφpos.ne')
    push_cast
    field_simp
  rw [hcoef]
  simp only [sq]

/-- LEAF. Finite character square expansion at a nonnegative residual. For a
modulus inside the admissible range, the local arc at a residual that is at
least zero differs from the double sum of the ordered character pair
contribution by no more than the stated logarithm of the modulus, the residual
coming only from the primes dividing the modulus and the finite integral
rearrangement. -/
theorem character_square_expansion_nonneg491 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        ∀ n : ℤ, 0 ≤ n →
          ‖localArc1622 N q n -
              (∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
                characterPair491 N q n χ ψ)‖ ≤
            C * (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) := by
  refine ⟨16, by norm_num, 1, ?_⟩
  intro N hN q hq hqN n hn
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have hN0 : 0 < N := by omega
    exact_mod_cast hN0
  have h7pos : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNpos (1 / 7)
  have hN1 : 1 ≤ N := le_of_lt hN
  have hkey := expansion_general491 N q hN1 hq n
  rcases eq_or_lt_of_le hq with hq1 | hq2
  · have hqone : q = 1 := hq1.symm
    subst hqone
    refine hkey.trans ?_
    simp
  · have hcard : (q.primeFactors.card : ℝ) ≤ 2 * Real.log q :=
      card_primeFactors_le_log491 q hq2
    have hfac : (0 : ℝ) ≤ (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) :=
      div_nonneg hNpos.le h7pos.le
    refine hkey.trans ?_
    have hineq : 8 * (q.primeFactors.card : ℝ) ≤ 16 * Real.log q := by linarith
    calc 8 * (q.primeFactors.card : ℝ) * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ)
        = (8 * (q.primeFactors.card : ℝ)) * ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ)) := by ring
      _ ≤ (16 * Real.log q) * ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ)) :=
          mul_le_mul_of_nonneg_right hineq hfac
      _ = 16 * (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) := by ring

/-- LEAF. Finite character square expansion at a negative residual. The same
expansion as at a nonnegative residual, with the reduced residue phase replaced
by its conjugate, which changes no norm; the primes dividing the modulus and the
finite integral rearrangement are again the whole residual. -/
theorem character_square_expansion_neg491 :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        ∀ n : ℤ, n < 0 →
          ‖localArc1622 N q n -
              (∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
                characterPair491 N q n χ ψ)‖ ≤
            C * (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) := by
  refine ⟨16, by norm_num, 1, ?_⟩
  intro N hN q hq hqN n hn
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have hN0 : 0 < N := by omega
    exact_mod_cast hN0
  have h7pos : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNpos (1 / 7)
  have hN1 : 1 ≤ N := le_of_lt hN
  have hkey := expansion_general491 N q hN1 hq n
  rcases eq_or_lt_of_le hq with hq1 | hq2
  · have hqone : q = 1 := hq1.symm
    subst hqone
    refine hkey.trans ?_
    simp
  · have hcard : (q.primeFactors.card : ℝ) ≤ 2 * Real.log q :=
      card_primeFactors_le_log491 q hq2
    have hfac : (0 : ℝ) ≤ (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) :=
      div_nonneg hNpos.le h7pos.le
    refine hkey.trans ?_
    have hineq : 8 * (q.primeFactors.card : ℝ) ≤ 16 * Real.log q := by linarith
    calc 8 * (q.primeFactors.card : ℝ) * (N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ)
        = (8 * (q.primeFactors.card : ℝ)) * ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ)) := by ring
      _ ≤ (16 * Real.log q) * ((N : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ)) :=
          mul_le_mul_of_nonneg_right hineq hfac
      _ = 16 * (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) := by ring

/-- LEAF. Exact separation of the finite character square. The double sum over
all ordered character pairs is the principal pair, that is the reduced residue
phase against the square of the principal prime series, plus the two mixed
blocks with exactly one principal character plus the block with both characters
nonprincipal. This is a finite rearrangement of the same sum with no error. -/
theorem character_square_matching491 (N q : ℕ) [NeZero q] (n : ℤ) :
    (∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
        characterPair491 N q n χ ψ) =
      principalTerm491 N q n + mixedTerm491 N q n + nonprincipalTerm491 N q n := by
  classical
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set S := univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1) with hS
  have hsingle : (univ.filter (fun χ : DirichletCharacter ℂ q => χ = 1)) = {1} := by
    ext x
    simp
  have hsplit (f : DirichletCharacter ℂ q → ℂ) :
      (∑ χ : DirichletCharacter ℂ q, f χ) = f 1 + ∑ χ ∈ S, f χ := by
    have h := Finset.sum_filter_add_sum_filter_not
      (s := (univ : Finset (DirichletCharacter ℂ q)))
      (p := fun χ : DirichletCharacter ℂ q => χ = 1) (f := f)
    rw [hsingle, Finset.sum_singleton] at h
    rw [← h]
  rw [hsplit (fun χ => ∑ ψ : DirichletCharacter ℂ q, characterPair491 N q n χ ψ)]
  rw [hsplit (fun ψ => characterPair491 N q n 1 ψ)]
  rw [Finset.sum_congr rfl (fun χ (_ : χ ∈ S) => hsplit (fun ψ => characterPair491 N q n χ ψ))]
  rw [pair_one_one491 N q hq n]
  unfold mixedTerm491 nonprincipalTerm491
  simp only [hS, Finset.sum_add_distrib]
  abel

/-- The three character term decomposition, assembled from the finite character
square expansion at each residual sign and from the exact separation of that
square. -/
theorem character_decomposition491_split :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, ∀ hq : 1 ≤ q, (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        letI : NeZero q := ⟨by omega⟩
        ∀ n : ℤ, ‖localArc1622 N q n -
          (principalTerm491 N q n + mixedTerm491 N q n + nonprincipalTerm491 N q n)‖ ≤
          C * (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) := by
  obtain ⟨C1, hC1, N1, h1⟩ := character_square_expansion_nonneg491
  obtain ⟨C2, hC2, N2, h2⟩ := character_square_expansion_neg491
  refine ⟨max C1 C2, lt_of_lt_of_le hC1 (le_max_left _ _), max N1 N2, ?_⟩
  intro N hN q hq hqQ
  have hN1 : N1 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : N2 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have h : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) hN
    exact_mod_cast h
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hx : 0 ≤ (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) :=
    div_nonneg (mul_nonneg (by positivity) hlogq) (Real.rpow_pos_of_pos hNpos _).le
  letI : NeZero q := ⟨by omega⟩
  intro n
  rcases lt_or_ge n 0 with hn | hn
  · have h := h2 N hN2 q hq hqQ n hn
    calc ‖localArc1622 N q n -
          (principalTerm491 N q n + mixedTerm491 N q n + nonprincipalTerm491 N q n)‖
        = ‖localArc1622 N q n -
            (∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
              characterPair491 N q n χ ψ)‖ := by
          rw [character_square_matching491 N q n]
      _ ≤ C2 * (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) := h
      _ = C2 * ((N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ)) := by ring
      _ ≤ max C1 C2 * ((N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hx
      _ = max C1 C2 * (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) := by ring
  · have h := h1 N hN1 q hq hqQ n hn
    calc ‖localArc1622 N q n -
          (principalTerm491 N q n + mixedTerm491 N q n + nonprincipalTerm491 N q n)‖
        = ‖localArc1622 N q n -
            (∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
              characterPair491 N q n χ ψ)‖ := by
          rw [character_square_matching491 N q n]
      _ ≤ C1 * (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) := h
      _ = C1 * ((N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ)) := by ring
      _ ≤ max C1 C2 * ((N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hx
      _ = max C1 C2 * (N : ℝ) * Real.log q / (N : ℝ) ^ (1 / 7 : ℝ) := by ring

end LeanLab.Linnik1951
