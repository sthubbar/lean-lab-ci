/-
Split of the saving estimate for the mixed local contribution of the rational
major arcs in this folder.

The estimate bounds the reduced residue sum, over one centred local arc of
radius one over q times N to the one seventh, of the principal prime series
against one translated prime series weighted by the central phase.

The principal prime series is the full prime series minus the prime divisors of
the modulus that the principal character removes. The file cuts the estimate
along exactly that difference:

* the step bounding the full prime series against one translated prime series;
* the step bounding the removed prime divisor correction against the same
  translated series;
* the assembly that writes the principal series back as the difference, splits
  the sum and the arc integral accordingly, and adds the two saving estimates,
  with the constant doubled and the two cutoffs taken to be the larger.

Each leaf is left open for a later pass; the assembly below is complete.
-/
import LeanLab.Linnik1951.SPLIT_mixed_bound520

namespace LeanLab.Linnik1951
open Finset MeasureTheory

/-! Private helpers: the sup-norm bound on the damped prime Fourier series and
the elementary counting bound on the number of distinct prime divisors. -/

/-- The reciprocal of one minus the damped factor is at most twice the scale. -/
private lemma one_sub_exp_neg_inv_le520 (N : ℕ) (hN : 1 ≤ N) :
    (1 - Real.exp (-(1 / (N : ℝ))))⁻¹ ≤ 2 * (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set t : ℝ := 1 / (N : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one hNpos]; exact hN1
  have hpos : (0 : ℝ) < 1 + t := by linarith
  have hexp_le : Real.exp (-t) ≤ 1 / (1 + t) := by
    have h1 : 1 + t ≤ Real.exp t := by
      rw [← Real.log_le_iff_le_exp hpos]
      have h := Real.log_le_sub_one_of_pos hpos
      linarith
    have h2 : (Real.exp t)⁻¹ ≤ ((1 : ℝ) + t)⁻¹ := inv_anti₀ hpos h1
    calc Real.exp (-t) = (Real.exp t)⁻¹ := by rw [Real.exp_neg]
      _ ≤ ((1 : ℝ) + t)⁻¹ := h2
      _ = 1 / (1 + t) := by rw [one_div]
  have hlow : 1 / (2 * (N : ℝ)) ≤ 1 - Real.exp (-t) := by
    have h4 : t / 2 ≤ t / (1 + t) :=
      div_le_div_of_nonneg_left (le_of_lt ht0) hpos (by linarith)
    have h5 : (1 : ℝ) - 1 / (1 + t) = t / (1 + t) := by
      field_simp
      ring
    have h6 : t / 2 = 1 / (2 * (N : ℝ)) := by
      rw [ht]
      field_simp
    rw [h6] at h4
    linarith [hexp_le]
  have h2N : (0 : ℝ) < 2 * (N : ℝ) := by positivity
  have hone : (0 : ℝ) < 1 - Real.exp (-t) := by
    have hlt : Real.exp (-t) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hprod : 1 ≤ (1 - Real.exp (-t)) * (2 * (N : ℝ)) := by
    have := (div_le_iff₀ h2N).mp hlow
    linarith
  rw [show (1 - Real.exp (-t))⁻¹ = 1 / (1 - Real.exp (-t)) by rw [one_div],
    div_le_iff₀ hone]
  linarith

/-- The damped prime Fourier series is bounded by twice the scale. -/
private lemma norm_prime_fourier_le520 (N : ℕ) (hN : 1 ≤ N) (α : ℝ) :
    ‖primeFourier111_up111 N α‖ ≤ 2 * (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set r : ℝ := Real.exp (-(1 / (N : ℝ))) with hr
  have hr0 : 0 ≤ r := le_of_lt (Real.exp_pos _)
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    have : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    linarith
  have hgeom : Summable (fun m : ℕ => r ^ m) := summable_geometric_of_lt_one hr0 hr1
  have hgeom_tsum : (∑' m : ℕ, r ^ m) = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
  have hpow : ∀ m : ℕ, r ^ m = Real.exp (-((m : ℝ)) / N) := by
    intro m
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hterm : ∀ p : Nat.Primes,
      Real.exp (-(((p : ℕ) : ℝ)) / N) = r ^ ((p : ℕ)) := by
    intro p
    rw [hpow]
  have key : ∀ s : Finset Nat.Primes,
      ∑ p ∈ s, Real.exp (-(((p : ℕ) : ℝ)) / N) ≤ 2 * (N : ℝ) := by
    intro s
    have hmap : ∑ m ∈ s.image (fun p : Nat.Primes => (p : ℕ)),
        Real.exp (-((m : ℝ)) / N)
        = ∑ p ∈ s, Real.exp (-(((p : ℕ) : ℝ)) / N) := by
      rw [Finset.sum_image]
      intro x _ y _ hxy
      exact Subtype.coe_injective hxy
    rw [← hmap]
    have hstep : ∑ m ∈ s.image (fun p : Nat.Primes => (p : ℕ)), Real.exp (-((m : ℝ)) / N)
        = ∑ m ∈ s.image (fun p : Nat.Primes => (p : ℕ)), r ^ m := by
      refine Finset.sum_congr rfl ?_
      intro m _
      exact (hpow m).symm
    rw [hstep]
    calc ∑ m ∈ s.image (fun p : Nat.Primes => (p : ℕ)), r ^ m
        ≤ ∑' m : ℕ, r ^ m := hgeom.sum_le_tsum _ (fun i _ => pow_nonneg hr0 i)
      _ = (1 - r)⁻¹ := hgeom_tsum
      _ ≤ 2 * (N : ℝ) := by rw [hr]; exact one_sub_exp_neg_inv_le520 N hN
  have hnorm_eq : ∀ p : Nat.Primes,
      ‖(Real.exp (-(((p : ℕ) : ℝ)) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * α * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)‖
        = Real.exp (-(((p : ℕ) : ℝ)) / N) := by
    intro p
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hsummR : Summable (fun p : Nat.Primes => Real.exp (-(((p : ℕ) : ℝ)) / N)) :=
    summable_of_sum_le (fun p => (Real.exp_pos _).le) key
  have hsumm_norm : Summable (fun p : Nat.Primes =>
      ‖(Real.exp (-(((p : ℕ) : ℝ)) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * α * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)‖) := by
    simpa only [hnorm_eq] using hsummR
  calc ‖primeFourier111_up111 N α‖
      = ‖∑' p : Nat.Primes, (Real.exp (-(((p : ℕ) : ℝ)) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * α * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)‖ := by
        rw [primeFourier111_up111]
    _ ≤ ∑' p : Nat.Primes, ‖(Real.exp (-(((p : ℕ) : ℝ)) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * α * ((p : ℕ) : ℝ)) : ℝ) * Complex.I)‖ :=
        norm_tsum_le_tsum_norm hsumm_norm
    _ = ∑' p : Nat.Primes, Real.exp (-(((p : ℕ) : ℝ)) / N) := tsum_congr hnorm_eq
    _ ≤ 2 * (N : ℝ) := Real.tsum_le_of_sum_le (fun p => (Real.exp_pos _).le) key

/-- The sum over the distinct prime divisors of the modulus is at most their
number, the terms carrying norm at most one. -/
private lemma norm_prime_factors_sum_le520 (N q : ℕ) (hN : 1 ≤ N) (z : ℝ) :
    ‖∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * z * (p : ℝ)) : ℝ) * Complex.I)‖
      ≤ (q.primeFactors.card : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ q.primeFactors,
      ‖(Real.exp (-(p : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * z * (p : ℝ)) : ℝ) * Complex.I)‖ ≤ 1 := by
    intro p _
    have h1 : ‖(Real.exp (-(p : ℝ) / N) : ℂ)‖ = Real.exp (-(p : ℝ) / N) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, h1, Real.exp_le_one_iff]
    have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hNpos.le
  calc ∑ p ∈ q.primeFactors, ‖(Real.exp (-(p : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * z * (p : ℝ)) : ℝ) * Complex.I)‖
      ≤ ∑ p ∈ q.primeFactors, (1 : ℝ) := Finset.sum_le_sum hterm
    _ = (q.primeFactors.card : ℝ) := by simp

/-- The number of distinct prime divisors of a positive modulus is at most the
logarithm of the modulus over the logarithm of two. -/
private lemma card_primeFactors_le_log520 (q : ℕ) (hq : 1 ≤ q) :
    (q.primeFactors.card : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 := by
  have hq0 : q ≠ 0 := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hdvd : ∏ p ∈ q.primeFactors, p ∣ q := Nat.prod_primeFactors_dvd q
  have hle : ∏ p ∈ q.primeFactors, p ≤ q := Nat.le_of_dvd (by omega) hdvd
  have h2prod : ∏ p ∈ q.primeFactors, (2 : ℕ) ≤ ∏ p ∈ q.primeFactors, p := by
    refine Finset.prod_le_prod ?_
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).two_le
  have hpow : (2 : ℕ) ^ q.primeFactors.card ≤ q := by
    rw [Finset.prod_const] at h2prod
    exact le_trans h2prod hle
  have hcast : ((2 : ℝ) ^ q.primeFactors.card) ≤ (q : ℝ) := by
    exact_mod_cast hpow
  have hlog : (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log (q : ℝ) := by
    have h1 : Real.log ((2 : ℝ) ^ q.primeFactors.card) ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by positivity) hcast
    rwa [Real.log_pow] at h1
  have hpos2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hpos2]
  linarith

/-- LEAF. Full prime series step. Over one centred local arc of radius one over
q times N to the one seventh, the reduced residue sum of one full prime series
against one translated prime series, weighted by the central phase, is at most
the scale N times the sixth power of the logarithm of N divided by the square
root of q times N to the one seventh. -/
theorem mixed_shifted_prime_part520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          primeFourier111_up111 N z * primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (N : ℝ) * Real.log N ^ 6 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  sorry

/-- LEAF. Removed prime divisor step. The same sum and the same arc, with the
prime divisors of the modulus that the principal character removes in place of
the first prime series. That correction has one exponentially damped term per
prime divisor of the modulus, so it carries the same saving. -/
theorem mixed_shifted_divisor_part520 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          (∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I)) *
            primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (N : ℝ) * Real.log N ^ 6 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  refine ⟨1, one_pos, 2 ^ 70, ?_⟩
  intro N hN q hq hqQ n hn
  have hNbig : 2 ^ 70 ≤ N := le_of_lt hN
  have hN1 : 1 ≤ N := by
    have : 0 < 2 ^ 70 := by norm_num
    omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hNbigR : (2 : ℝ) ^ 70 ≤ (N : ℝ) := by exact_mod_cast hNbig
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  set r : ℝ := 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) with hr
  have hp7 : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hrpos : 0 < r := by rw [hr]; positivity
  have hlogtwo : (0.693 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 : (1 : ℝ) ≤ Real.log N := by
    have h1 : Real.log ((2 : ℝ) ^ 70) ≤ Real.log N :=
      Real.log_le_log (by positivity) hNbigR
    rw [Real.log_pow] at h1
    push_cast at h1
    nlinarith
  have hL0 : (0 : ℝ) ≤ Real.log N := le_trans (by norm_num) hL1
  -- the pointwise bound on the integrand
  have hpt : ∀ (a : ℕ) (z : ℝ),
      ‖(∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * z * (p : ℝ)) : ℝ) * Complex.I)) *
        primeFourier111_up111 N ((a : ℝ) / q + z) *
        Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖
      ≤ (q.primeFactors.card : ℝ) * (2 * (N : ℝ)) := by
    intro a z
    simp only [norm_mul]
    have hE : ‖Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) *
        Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    rw [hE, mul_one]
    exact mul_le_mul (norm_prime_factors_sum_le520 N q hN1 z)
      (norm_prime_fourier_le520 N hN1 ((a : ℝ) / q + z))
      (norm_nonneg _) (by positivity)
  -- the bound on one arc integral
  have hint : ∀ a : ℕ,
      ‖∫ z in -(r)..r,
        (∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * (p : ℝ)) : ℝ) * Complex.I)) *
          primeFourier111_up111 N ((a : ℝ) / q + z) *
          Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖
      ≤ ((q.primeFactors.card : ℝ) * (2 * (N : ℝ))) * (2 * r) := by
    intro a
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -r) (b := r)
      (C := (q.primeFactors.card : ℝ) * (2 * (N : ℝ)))
      (f := fun z : ℝ =>
        (∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * (p : ℝ)) : ℝ) * Complex.I)) *
          primeFourier111_up111 N ((a : ℝ) / q + z) *
          Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))
      (fun z _ => hpt a z)
    have hlen : |r - -r| = 2 * r := by
      rw [show r - -r = 2 * r by ring, abs_of_nonneg (by linarith [hrpos.le])]
    rwa [hlen] at h
  -- the cardinality of the reduced residues
  have hcard : ((range q).filter (fun a => Nat.Coprime a q)).card ≤ q := by
    calc ((range q).filter (fun a => Nat.Coprime a q)).card ≤ (range q).card :=
          Finset.card_filter_le _ _
      _ = q := Finset.card_range q
  have hQtenth : Real.log (q : ℝ) ≤ Real.log N / 10 := by
    have h1 : Real.log (q : ℝ) ≤ Real.log ((N : ℝ) ^ (1 / 10 : ℝ)) :=
      Real.log_le_log hqpos hqQ
    rw [Real.log_rpow hNpos] at h1
    linarith
  have homega : (q.primeFactors.card : ℝ) ≤ Real.log N / (10 * Real.log 2) := by
    have h1 := card_primeFactors_le_log520 q hq
    have h2 : Real.log (q : ℝ) / Real.log 2 ≤ (Real.log N / 10) / Real.log 2 :=
      div_le_div_of_nonneg_right hQtenth hlog2pos.le
    have h3 : (Real.log N / 10) / Real.log 2 = Real.log N / (10 * Real.log 2) := by
      field_simp
    linarith
  have homega4 : 4 * (q.primeFactors.card : ℝ) ≤ Real.log N := by
    have h1 : Real.log N / (10 * Real.log 2) ≤ Real.log N / 4 := by
      apply div_le_div_of_nonneg_left hL0 (by norm_num : (0 : ℝ) < 4) _
      nlinarith
    have h2 : 4 * (Real.log N / (10 * Real.log 2)) ≤ Real.log N := by
      calc 4 * (Real.log N / (10 * Real.log 2)) ≤ 4 * (Real.log N / 4) := by linarith
        _ = Real.log N := by ring
    nlinarith [homega]
  -- the square root comparison
  have hqle : (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 10 := by
    have h1 : (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) := by
      refine le_trans hqQ (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) ?_)
      norm_num
    have h2 : (1 : ℝ) ≤ Real.log N ^ 10 := by
      have h3 : (1 : ℝ) ^ 10 ≤ Real.log N ^ 10 := pow_le_pow_left₀ (by norm_num) hL1 10
      simpa using h3
    have h4 : (N : ℝ) ^ (1 / 7 : ℝ) * 1 ≤ (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 10 :=
      mul_le_mul_of_nonneg_left h2 hp7.le
    linarith
  have hsqle : Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≤
      (N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 5 := by
    rw [Real.sqrt_le_left (by positivity)]
    have h1 : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤
        ((N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 10) * (N : ℝ) ^ (1 / 7 : ℝ) :=
      mul_le_mul_of_nonneg_right hqle hp7.le
    have h2 : ((N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 10) * (N : ℝ) ^ (1 / 7 : ℝ) =
        ((N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 5) ^ 2 := by ring
    linarith
  have hspos : (0 : ℝ) < Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) :=
    Real.sqrt_pos.2 (by positivity)
  -- assembly
  have hbound : ‖∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(r)..r,
          (∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * (p : ℝ)) : ℝ) * Complex.I)) *
            primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖
      ≤ (((range q).filter (fun a => Nat.Coprime a q)).card : ℝ) *
          (((q.primeFactors.card : ℝ) * (2 * (N : ℝ))) * (2 * r)) := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun a _ => hint a)) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcardle : (((range q).filter (fun a => Nat.Coprime a q)).card : ℝ) *
        (((q.primeFactors.card : ℝ) * (2 * (N : ℝ))) * (2 * r))
      ≤ 4 * (N : ℝ) * (q.primeFactors.card : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) := by
    have h1 : (((range q).filter (fun a => Nat.Coprime a q)).card : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast hcard
    have h2 : (0 : ℝ) ≤ ((q.primeFactors.card : ℝ) * (2 * (N : ℝ))) * (2 * r) := by
      rw [hr]; positivity
    refine le_trans (mul_le_mul_of_nonneg_right h1 h2) (le_of_eq ?_)
    rw [hr]
    have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqpos
    have hp0 : (N : ℝ) ^ (1 / 7 : ℝ) ≠ 0 := ne_of_gt hp7
    have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    field_simp
    ring
  have hfinal : 4 * (N : ℝ) * (q.primeFactors.card : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) ≤
      1 * (N : ℝ) * Real.log N ^ 6 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    rw [one_mul, le_div_iff₀ hspos]
    have hp0 : (N : ℝ) ^ (1 / 7 : ℝ) ≠ 0 := ne_of_gt hp7
    have hstep3 : 4 * (N : ℝ) * (q.primeFactors.card : ℝ) * Real.log N ^ 5 ≤
        (N : ℝ) * Real.log N ^ 6 := by
      have h5 : (0 : ℝ) ≤ Real.log N ^ 5 := pow_nonneg hL0 5
      calc 4 * (N : ℝ) * (q.primeFactors.card : ℝ) * Real.log N ^ 5
          = ((N : ℝ) * Real.log N ^ 5) * (4 * (q.primeFactors.card : ℝ)) := by ring
        _ ≤ ((N : ℝ) * Real.log N ^ 5) * Real.log N :=
            mul_le_mul_of_nonneg_left homega4 (by positivity)
        _ = (N : ℝ) * Real.log N ^ 6 := by ring
    calc 4 * (N : ℝ) * (q.primeFactors.card : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) *
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))
        ≤ 4 * (N : ℝ) * (q.primeFactors.card : ℝ) / (N : ℝ) ^ (1 / 7 : ℝ) *
            ((N : ℝ) ^ (1 / 7 : ℝ) * Real.log N ^ 5) := by
          apply mul_le_mul_of_nonneg_left hsqle
          positivity
      _ = 4 * (N : ℝ) * (q.primeFactors.card : ℝ) * Real.log N ^ 5 := by
          field_simp
      _ ≤ (N : ℝ) * Real.log N ^ 6 := hstep3
  exact le_trans (le_trans hbound hcardle) hfinal

/-- The saving estimate for the mixed local contribution: the principal prime
series is the full prime series minus the removed prime divisor correction, so
the reduced residue sum of the arc integrals splits into the two bounded pieces,
and the triangle inequality plus the doubling of the constant gives the
displayed scale. -/
theorem mixed_shifted_bound520_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) → ∀ n : ℤ, n ≤ N →
      ‖∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          principalPrime520 N q z * primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (N : ℝ) * Real.log N ^ 6 /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  obtain ⟨A, hA, NA, hSA⟩ := mixed_shifted_prime_part520 hG
  obtain ⟨B, hB, NB, hSB⟩ := mixed_shifted_divisor_part520 hG
  refine ⟨2 * A + 2 * B, by linarith, max NA NB, ?_⟩
  intro N hN q hq hqQ n hn
  have hNA : NA < N := lt_of_le_of_lt (le_max_left NA NB) hN
  have hNB : NB < N := lt_of_le_of_lt (le_max_right NA NB) hN
  have hN1 : 1 ≤ N :=
    Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le NA) hNA))
  have h1 := hSA N hNA q hq hqQ n hn
  have h2 := hSB N hNB q hq hqQ n hn
  have hsplit :
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          principalPrime520 N q z * primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) =
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          primeFourier111_up111 N z * primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) -
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          (∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I)) *
            primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have hFz : Continuous (fun z : ℝ => primeFourier111_up111 N z) :=
      continuous_prime_fourier111_up111 N hN1
    have hFz' : Continuous (fun z : ℝ => primeFourier111_up111 N ((a : ℝ) / q + z)) :=
      (continuous_prime_fourier111_up111 N hN1).comp (by fun_prop)
    have hE : Continuous (fun z : ℝ => Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    have hDz : Continuous (fun z : ℝ =>
        (∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
          Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I))) := by
      fun_prop
    have hi1 : IntervalIntegrable (fun z : ℝ => primeFourier111_up111 N z *
        primeFourier111_up111 N ((a : ℝ) / q + z) *
          Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))
        volume (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := ((hFz.mul hFz').mul hE).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun z : ℝ =>
        (∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
            Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I)) *
          primeFourier111_up111 N ((a : ℝ) / q + z) *
          Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))
        volume (-(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := ((hDz.mul hFz').mul hE).intervalIntegrable _ _
    have heq : (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        (primeFourier111_up111 N z * primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I) -
          (∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I)) *
            primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I))) =
      (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        primeFourier111_up111 N z * primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) -
      (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        (∑ p ∈ q.primeFactors, (Real.exp (-(p : ℝ) / N) : ℂ) *
              Complex.exp ((-(2 * Real.pi * z * p) : ℝ) * Complex.I)) *
            primeFourier111_up111 N ((a : ℝ) / q + z) *
            Complex.exp (((2 * Real.pi * (n : ℝ) * ((a : ℝ) / q + z) : ℝ) : ℂ) * Complex.I)) :=
      intervalIntegral.integral_sub hi1 hi2
    rw [← heq]
    apply intervalIntegral.integral_congr
    intro z hz
    simp only [principalPrime520]
    ring
  rw [hsplit]
  have hsN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hsq : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hrp : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hsN _
  have hs : (0 : ℝ) < Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) :=
    Real.sqrt_pos.2 (mul_pos hsq hrp)
  have hNN : (0 : ℝ) ≤ (N : ℝ) := le_of_lt hsN
  have hL : (0 : ℝ) ≤ Real.log N ^ 6 := by
    have hsq6 : Real.log N ^ 6 = (Real.log N ^ 3) ^ 2 := by ring
    rw [hsq6]
    exact sq_nonneg _
  have hkey :
      (A * (N : ℝ) * Real.log N ^ 6) / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) +
        (B * (N : ℝ) * Real.log N ^ 6) / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≤
      (2 * A + 2 * B) * (N : ℝ) * Real.log N ^ 6 /
        Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (le_of_lt hs)
    have hAB : A + B ≤ 2 * A + 2 * B := by linarith
    have hNL : (0 : ℝ) ≤ (N : ℝ) * Real.log N ^ 6 := mul_nonneg hNN hL
    nlinarith [mul_le_mul_of_nonneg_right hAB hNL]
  exact le_trans (norm_sub_le _ _) (le_trans (add_le_add h1 h2) hkey)

end LeanLab.Linnik1951
