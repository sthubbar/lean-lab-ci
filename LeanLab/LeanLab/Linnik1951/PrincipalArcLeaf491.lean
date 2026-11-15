/-
P0093 page 155 equation 2.3 and pages 159 through 161. The principal character form
of the mean square estimate on the short arc, equations 6.1 and 6.3. It is derived
here from the theorem prime_arc_mean_square491 for the full prime series by removing
the primes dividing q, which contribute at most the number of prime divisors of q.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Base491b
import LeanLab.Linnik1951.PrimeArcLeaf491

namespace LeanLab.Linnik1951

open Finset MeasureTheory

/-- The model series S one is continuous. -/
private lemma continuous_logFourier_leaf491 (N : ℕ) (hN : 1 ≤ N) :
    Continuous (logFourier520 N) := by
  unfold logFourier520
  refine continuous_tsum (u := fun m : ℕ => ‖logCoefficient520 N m‖)
    (fun m => by fun_prop) (logCoefficient_summable520 N hN).norm (fun m z => ?_)
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The primes dividing the modulus have finite support. -/
private lemma bad_prime_summable_leaf491 (q : ℕ) (hq : 1 ≤ q) :
    Summable (fun p : Nat.Primes => if ¬ Nat.Coprime (p : ℕ) q then (1 : ℝ) else 0) := by
  have hfin : Set.Finite ((fun p : Nat.Primes => (p : ℕ)) ⁻¹' (q.primeFactors : Set ℕ)) :=
    Set.Finite.preimage (Nat.Primes.coe_nat_injective.injOn) (q.primeFactors.finite_toSet)
  refine summable_of_ne_finset_zero (s := hfin.toFinset) (fun p hp => ?_)
  by_contra hne
  apply hp
  rw [Set.Finite.mem_toFinset]
  have hc : ¬ Nat.Coprime (p : ℕ) q := by
    by_contra hc
    exact hne (by simp [hc])
  exact Finset.mem_coe.mpr
    (Nat.mem_primeFactors.mpr ⟨p.2, p.2.dvd_iff_not_coprime.mpr hc, by omega⟩)

/-- The indicator sum over the primes dividing the modulus is at most the number
of prime factors. -/
private lemma tsum_bad_prime_le_leaf491 (q : ℕ) (hq : 1 ≤ q) :
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

/-- P0093 page 155 equation 2.3. The principal character prime series differs from
the full prime series by at most the number of primes dividing the modulus. -/
private lemma principal_sub_prime_norm_leaf491 (N q : ℕ) (hN : 1 ≤ N) (hq : 1 ≤ q) (z : ℝ) :
    ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z - primeFourier111 N z‖ ≤
      (q.primeFactors.card : ℝ) := by
  have hdamp : Summable (fun p : Nat.Primes => Real.exp (-((p : ℕ) : ℝ) / N)) :=
    (damping_summable111 N hN).comp_injective Nat.Primes.coe_nat_injective
  have hs1 : Summable (fun p : Nat.Primes =>
      (1 : DirichletCharacter ℂ q) (p : ℕ) * (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * z * (p : ℕ)) : ℝ) * Complex.I)) := by
    refine Summable.of_norm_bounded hdamp (fun p => ?_)
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (DirichletCharacter.norm_le_one _ _)
  have hs2 : Summable (fun p : Nat.Primes =>
      (Real.exp (-((p : ℕ) : ℝ) / N) : ℂ) *
        Complex.exp ((-(2 * Real.pi * z * (p : ℕ)) : ℝ) * Complex.I)) := by
    refine Summable.of_norm_bounded hdamp (fun p => ?_)
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact le_refl _
  unfold characterPrime280 primeFourier111
  rw [← Summable.tsum_sub hs1 hs2]
  refine (tsum_of_norm_bounded (bad_prime_summable_leaf491 q hq).hasSum (fun p => ?_)).trans
    (tsum_bad_prime_le_leaf491 q hq)
  by_cases hc : Nat.Coprime (p : ℕ) q
  · have hu : IsUnit (((p : ℕ) : ZMod q)) := (ZMod.isUnit_iff_coprime _ _).mpr hc
    rw [MulChar.one_apply hu]
    simp [hc]
  · have hu : ¬ IsUnit (((p : ℕ) : ZMod q)) := fun h => hc ((ZMod.isUnit_iff_coprime _ _).mp h)
    rw [MulChar.map_nonunit _ hu, if_pos hc]
    simp only [zero_mul, zero_sub, norm_neg, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Real.exp_le_one_iff]
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hp0 : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hN0.le

/-- P0093 page 155 equation 2.3 and page 160 equation 6.1.
Derived from the theorem prime_arc_mean_square491 for the full prime series by
removing the primes dividing q. The term B ln q of equation 2.3 has the same origin. Under the extended Riemann hypothesis the principal
character prime series differs from the model series S one, with weights one over
ln m, by a function whose square integral over the arc of radius one over q tau is
at most a constant times N ln to the 13 of N over q tau. The primes dividing q
change the series by at most the number of prime divisors of q, which is at most
two ln N, so they change the square integral by at most 16 ln squared of N over
q tau. -/
theorem principal_arc_mean_square491 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) →
        (∫ z in -(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..
            (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z - logFourier520 N z‖ ^ 2) ≤
          C * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 := by
  obtain ⟨C0, hC0, N0, h0⟩ := prime_arc_mean_square491 hG
  refine ⟨2 * C0 + 16, by positivity, max N0 3, fun N hN q hq hqN => ?_⟩
  have hN0 : N0 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN3 : 3 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hN1 : 1 ≤ N := by omega
  have hNr : (3 : ℝ) < (N : ℝ) := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  set L : ℝ := Real.log N with hL
  set D : ℝ := (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) with hD
  have hDpos : 0 < D := mul_pos hqpos (Real.rpow_pos_of_pos hNpos _)
  have hL1 : 1 ≤ L := by
    have h1 : Real.log (Real.exp 1) ≤ Real.log N :=
      Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    rwa [Real.log_exp] at h1
  have hqN' : (q : ℝ) ≤ (N : ℝ) := by
    refine hqN.trans ?_
    calc (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (N : ℝ) := Real.rpow_one _
  have hcard : (q.primeFactors.card : ℝ) ≤ 2 * L := by
    have h1 := prime_factor_card_log442 q hq
    have h2 : Real.log q ≤ L := Real.log_le_log hqpos hqN'
    have h3 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h4 : (0 : ℝ) ≤ (q.primeFactors.card : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hpc : Continuous (characterPrime280 (1 : DirichletCharacter ℂ q) N) :=
    continuous_character_prime357 _ N hN1
  have hsc : Continuous (primeFourier111 N) := continuous_prime_fourier111 N hN1
  have hfc : Continuous (logFourier520 N) := continuous_logFourier_leaf491 N hN1
  have hrr : -(1 / D) ≤ 1 / D := by
    have : 0 < 1 / D := by positivity
    linarith
  have hpt : ∀ z : ℝ,
      ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z - logFourier520 N z‖ ^ 2 ≤
        2 * ‖primeFourier111 N z - logFourier520 N z‖ ^ 2 + 8 * L ^ 2 := by
    intro z
    have hb := principal_sub_prime_norm_leaf491 N q hN1 hq z
    have hb0 := norm_nonneg
      (characterPrime280 (1 : DirichletCharacter ℂ q) N z - primeFourier111 N z)
    have ha0 := norm_nonneg (primeFourier111 N z - logFourier520 N z)
    have htri : ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z - logFourier520 N z‖ ≤
        ‖primeFourier111 N z - logFourier520 N z‖ +
          ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z - primeFourier111 N z‖ := by
      have := norm_add_le (primeFourier111 N z - logFourier520 N z)
        (characterPrime280 (1 : DirichletCharacter ℂ q) N z - primeFourier111 N z)
      rwa [show primeFourier111 N z - logFourier520 N z +
          (characterPrime280 (1 : DirichletCharacter ℂ q) N z - primeFourier111 N z) =
          characterPrime280 (1 : DirichletCharacter ℂ q) N z - logFourier520 N z by ring] at this
    have hc0 := norm_nonneg
      (characterPrime280 (1 : DirichletCharacter ℂ q) N z - logFourier520 N z)
    have hb2 : ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z - primeFourier111 N z‖ ≤
        2 * L := hb.trans hcard
    nlinarith [sq_nonneg (‖primeFourier111 N z - logFourier520 N z‖ -
      ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z - primeFourier111 N z‖)]
  have hi1 : IntervalIntegrable (fun z : ℝ =>
      ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z - logFourier520 N z‖ ^ 2)
      volume (-(1 / D)) (1 / D) :=
    (((hpc.sub hfc).norm).pow 2).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun z : ℝ =>
      ‖primeFourier111 N z - logFourier520 N z‖ ^ 2) volume (-(1 / D)) (1 / D) :=
    (((hsc.sub hfc).norm).pow 2).intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun z : ℝ =>
      2 * ‖primeFourier111 N z - logFourier520 N z‖ ^ 2 + 8 * L ^ 2) volume (-(1 / D)) (1 / D) :=
    (hi2.const_mul 2).add intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hrr hi1 hi3 (fun z _ => hpt z)
  have hsplit : (∫ z in -(1 / D)..(1 / D),
      (2 * ‖primeFourier111 N z - logFourier520 N z‖ ^ 2 + 8 * L ^ 2)) =
      2 * (∫ z in -(1 / D)..(1 / D), ‖primeFourier111 N z - logFourier520 N z‖ ^ 2) +
        (1 / D - -(1 / D)) * (8 * L ^ 2) := by
    rw [intervalIntegral.integral_add (hi2.const_mul 2) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
  have hleaf := h0 N hN0 q hq hqN
  rw [← hD, ← hL] at hleaf
  refine hmono.trans ?_
  rw [hsplit]
  have hL13 : L ^ 2 ≤ L ^ 13 := pow_le_pow_right₀ hL1 (by norm_num)
  have hL2 : 0 ≤ L ^ 2 := by positivity
  have hN1r : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hk : L ^ 2 ≤ (N : ℝ) * L ^ 13 := by nlinarith
  have e1 : (1 / D - -(1 / D)) * (8 * L ^ 2) = 16 * (L ^ 2 / D) := by ring
  have e2 : (2 * C0 + 16) * (N : ℝ) / D * L ^ 13 =
      2 * (C0 * (N : ℝ) / D * L ^ 13) + 16 * ((N : ℝ) * L ^ 13 / D) := by ring
  rw [e1, e2]
  have hdiv : L ^ 2 / D ≤ (N : ℝ) * L ^ 13 / D := div_le_div_of_nonneg_right hk hDpos.le
  linarith

end LeanLab.Linnik1951
