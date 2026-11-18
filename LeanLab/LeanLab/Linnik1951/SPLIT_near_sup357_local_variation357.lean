/-
Split of the local variation bound `near_sup357_local_variation357` into three
smaller steps. Nothing here changes the statement: the assembly
`near_sup357_local_variation357_split` below states it character for character and
proves it from the three OPEN leaves, which record, in order, (1) the identity that
writes the change of the damped character prime sum between phase zero and phase
alpha as the integral of its derivative in the phase, (2) the plain
Cauchy-Schwarz inequality for an interval integral of a complex valued function, and
(3) the mean square estimate for that derivative over the permitted phase range.
The proof of the assembly does not use `near_sup357_local_variation357`.
-/
import LeanLab.Linnik1951.SPLIT_near_positive_sup357

namespace LeanLab.Linnik1951

/-- For `N` at least one the weights `exp (-p / N)` are summable over the primes, being
dominated by the geometric series with ratio `exp (-1 / N)`. -/
private lemma summable_primes_exp_neg (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun p : Nat.Primes => Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ))) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set r : ℝ := Real.exp (-(1 : ℝ) / (N : ℝ)) with hr
  have hr1 : ‖r‖ < 1 := by
    rw [hr, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    have h : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    have h2 : (-(1 : ℝ)) / (N : ℝ) = -(1 / (N : ℝ)) := by ring
    rw [h2]
    linarith
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ 0 * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 0 hr1
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := fun a b h => Subtype.ext h
  refine (hbase.comp_injective hinj).congr fun p => ?_
  have hpow : r ^ (p : ℕ) = Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) := by
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  simp [hpow]

/-- The same summability with an extra factor of `p`, for `N` at least one. -/
private lemma summable_primes_exp_neg_mul (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) * Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ))) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set r : ℝ := Real.exp (-(1 : ℝ) / (N : ℝ)) with hr
  have hr1 : ‖r‖ < 1 := by
    rw [hr, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    have h : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    have h2 : (-(1 : ℝ)) / (N : ℝ) = -(1 / (N : ℝ)) := by ring
    rw [h2]
    linarith
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ 1 * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr1
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := fun a b h => Subtype.ext h
  refine (hbase.comp_injective hinj).congr fun p => ?_
  have hpow : r ^ (p : ℕ) = Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) := by
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  simp [hpow]

/-- A Dirichlet character takes the value of norm one on a unit: the value is a root of unity
because the order of the unit is finite. -/
private lemma norm_dirichletCharacter_apply_eq_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    {a : ZMod q} (ha : IsUnit a) : ‖χ a‖ = 1 := by
  have hpow' : (χ.toUnitHom ha.unit) ^ orderOf ha.unit = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hpow : χ ((ha.unit : ZMod q)) ^ orderOf ha.unit = 1 := by
    have hv := congrArg (fun u : ℂˣ => (u : ℂ)) hpow'
    simpa [MulChar.coe_toUnitHom] using hv
  have hnorm : ‖χ ((ha.unit : ZMod q))‖ ^ orderOf ha.unit = 1 := by
    rw [← norm_pow, hpow, norm_one]
  have heq : ‖χ ((ha.unit : ZMod q))‖ = 1 :=
    (pow_left_inj₀ (norm_nonneg _) zero_le_one (orderOf_pos ha.unit).ne').mp
      (by rw [hnorm, one_pow])
  simpa [IsUnit.unit_spec ha] using heq

/-- A Dirichlet character takes values of norm at most one. -/
private lemma norm_dirichletCharacter_apply_le_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ZMod q) : ‖χ a‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · rw [norm_dirichletCharacter_apply_eq_one χ ha]
  · rw [MulChar.apply_eq_zero_iff.mpr ha, norm_zero]
    norm_num

/-- At level zero the weight `exp (-p / 0)` is one, so the summand is a character value times a
phase factor and a coefficient `c p` of norm at least one half. If the level is zero every
character value at a prime vanishes, and otherwise the terms do not tend to zero; in both cases
the sum vanishes. -/
private lemma tsum_char_mul_exp_phase_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (β : ℝ)
    (c : Nat.Primes → ℂ) (hc : ∀ p : Nat.Primes, (1 / 2 : ℝ) ≤ ‖c p‖) :
    (∑' p : Nat.Primes,
      χ ((p : ℕ)) * c p * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)) = 0 := by
  by_cases hq : q = 0
  · subst hq
    have hzero : ∀ p : Nat.Primes, χ ((p : ℕ)) = 0 := by
      intro p
      refine MulChar.map_nonunit χ ?_
      rw [ZMod.isUnit_prime_iff_not_dvd p.2]
      exact fun h => absurd h (by simp)
    simp [hzero]
  · refine tsum_eq_zero_of_not_summable ?_
    intro hs
    have hsmall : ∀ᶠ p : Nat.Primes in Filter.cofinite,
        ‖χ ((p : ℕ)) * c p *
          Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ < 1 / 2 := by
      have h2 := (Metric.tendsto_nhds.mp hs.tendsto_cofinite_zero) (1 / 2) (by norm_num)
      simpa [dist_eq_norm] using h2
    have hfin : {p : Nat.Primes |
        ¬ ‖χ ((p : ℕ)) * c p *
          Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ < 1 / 2}.Finite :=
      Filter.eventually_cofinite.mp hsmall
    set M : ℕ := hfin.toFinset.sup (fun p : Nat.Primes => (p : ℕ)) with hM
    have hMle : ∀ p : Nat.Primes,
        ¬ ‖χ ((p : ℕ)) * c p *
          Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ < 1 / 2 →
          (p : ℕ) ≤ M := by
      intro p hp
      exact Finset.le_sup (f := fun p : Nat.Primes => (p : ℕ)) (hfin.mem_toFinset.mpr hp)
    obtain ⟨p, hpq, hpprime⟩ := Nat.exists_infinite_primes (max (q + 1) (M + 1))
    have hpq' : q < p := Nat.lt_of_succ_le (le_trans (le_max_left (q + 1) (M + 1)) hpq)
    have hunit : IsUnit ((p : ℕ) : ZMod q) := by
      rw [ZMod.isUnit_prime_iff_not_dvd hpprime]
      intro hdvd
      have hle : p ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hdvd
      omega
    have hnorm : ‖χ ((p : ℕ))‖ = 1 := norm_dirichletCharacter_apply_eq_one χ hunit
    have hterm : ¬ ‖χ ((p : ℕ)) * c ⟨p, hpprime⟩ *
        Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ < 1 / 2 := by
      rw [norm_mul, norm_mul, hnorm, Complex.norm_exp_ofReal_mul_I, mul_one, one_mul]
      have := hc ⟨p, hpprime⟩
      linarith
    have hple : p ≤ M := hMle ⟨p, hpprime⟩ hterm
    have hMle' : M + 1 ≤ p := le_trans (le_max_right (q + 1) (M + 1)) hpq
    omega


/-- LEAF: Step 1 of 3: the change of the damped character prime sum over the phase is
the integral of its derivative. The derivative in the phase of the exponential factor
of the summand at prime p carries the factor minus two pi p, so the differentiated
series is the one displayed. This is an identity in the complex numbers and it uses
no estimate at all: the two sides are equal for every nonnegative phase, and both
sides vanish at phase zero. -/
theorem near_sup357_difference_integral357 {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ)
    (α : ℝ) (hα : 0 ≤ α) :
    characterPrime280 χ N α - characterPrime280 χ N 0 =
      ∫ β in (0 : ℝ)..α, ∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) := by
  set φ : Nat.Primes → ℝ → ℂ := fun p β => χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) with hφ
  set ψ : Nat.Primes → ℝ → ℂ := fun p β => χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) with hψ
  by_cases hN0 : N = 0
  · -- N = 0: the weight `exp (-p / 0)` is one and both sums vanish
    subst hN0
    have hfam1 : ∀ β : ℝ, (∑' p : Nat.Primes,
        χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / ((0 : ℕ) : ℝ)) : ℂ) *
          Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)) = 0 := by
      intro β
      have h := tsum_char_mul_exp_phase_zero χ β (fun _ => (1 : ℂ)) (fun p => by norm_num)
      simpa [Nat.cast_zero, div_zero, neg_zero, Real.exp_zero, Complex.ofReal_one] using h
    have hfam2 : ∀ β : ℝ, (∑' p : Nat.Primes,
        χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / ((0 : ℕ) : ℝ)) : ℂ) *
          ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) *
          Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)) = 0 := by
      intro β
      have hc : ∀ p : Nat.Primes,
          (1 / 2 : ℝ) ≤ ‖(((-(2 * Real.pi * (((p : ℕ) : ℝ)))) : ℝ) : ℂ) * Complex.I‖ := by
        intro p
        have hpi : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
        have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
        rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_neg,
          abs_of_pos (by positivity)]
        have h1 : (2 : ℝ) * 2 ≤ 2 * Real.pi := by nlinarith
        have h8 : (8 : ℝ) ≤ 2 * Real.pi * ((p : ℕ) : ℝ) := by
          have h := mul_le_mul h1 hp2 (show (0 : ℝ) ≤ 2 by norm_num) (by positivity)
          have h' : (2 : ℝ) * 2 * 2 = 8 := by norm_num
          rw [h'] at h
          exact h
        linarith
      have h := tsum_char_mul_exp_phase_zero χ β
        (fun p : Nat.Primes => (((-(2 * Real.pi * (((p : ℕ) : ℝ)))) : ℝ) : ℂ) * Complex.I) hc
      simpa [Nat.cast_zero, div_zero, neg_zero, Real.exp_zero, Complex.ofReal_one] using h
    have hL : characterPrime280 χ 0 α - characterPrime280 χ 0 0 = 0 := by
      have h1 : characterPrime280 χ 0 α = 0 := by
        rw [characterPrime280]
        exact hfam1 α
      have h2 : characterPrime280 χ 0 0 = 0 := by
        rw [characterPrime280]
        exact hfam1 0
      rw [h1, h2, sub_self]
    rw [hL]
    have hzero : (∫ β in (0 : ℝ)..α, ∑' p : Nat.Primes,
        χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / ((0 : ℕ) : ℝ)) : ℂ) *
          ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) *
          Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)) = 0 := by
      rw [show (fun β : ℝ => ∑' p : Nat.Primes,
          χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / ((0 : ℕ) : ℝ)) : ℂ) *
            ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) *
            Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I))
          = fun _ => (0 : ℂ) from funext hfam2]
      simp
    rw [hzero]
  · have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
    have hderiv : ∀ (p : Nat.Primes) (β : ℝ), HasDerivAt (φ p) (ψ p β) β := by
      intro p β
      set cc : ℂ := χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) with hcc
      set d : ℂ := ((-(2 * Real.pi * (((p : ℕ) : ℝ)))) : ℂ) * Complex.I with hddef
      have harg : ∀ γ : ℝ, ((-(2 * Real.pi * γ * (((p : ℕ) : ℝ))) : ℝ) : ℂ) * Complex.I
          = (γ : ℂ) * d := by
        intro γ
        rw [hddef]
        push_cast
        ring
      have h1 : HasDerivAt (fun γ : ℝ => (γ : ℂ) * d) d β := by
        have h := (Complex.ofRealCLM.hasDerivAt (x := β)).mul_const d
        simpa using h
      have h2 : HasDerivAt (fun γ : ℝ => Complex.exp ((γ : ℂ) * d))
          (Complex.exp ((β : ℂ) * d) * d) β := by
        simpa using h1.cexp
      have h3 := (hasDerivAt_const (x := β) (c := cc)).mul h2
      have hfun : (fun γ : ℝ => cc * Complex.exp ((γ : ℂ) * d))
          = fun γ : ℝ => χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) *
              Complex.exp ((-(2 * Real.pi * γ * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) := by
        funext γ
        rw [hcc, harg γ]
      have hval : ψ p β = cc * (Complex.exp ((β : ℂ) * d) * d) := by
        simp only [hψ]
        rw [harg β, hcc, hddef]
        push_cast
        ring
      rw [hval]
      simp only [hφ]
      rw [← hfun]
      convert h3 using 1
      ring
    have hcont : ∀ p : Nat.Primes, Continuous (fun β : ℝ => ψ p β) := by
      intro p
      rw [hψ]
      fun_prop
    have hint : ∀ p : Nat.Primes, IntervalIntegrable (ψ p) MeasureTheory.volume (0 : ℝ) α := by
      intro p
      exact (hcont p).intervalIntegrable 0 α
    have hFTC : ∀ p : Nat.Primes, (∫ β in (0 : ℝ)..α, ψ p β) = φ p α - φ p 0 := by
      intro p
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv p x) (hint p)
    have hbound : ∀ (p : Nat.Primes) (β : ℝ), ‖ψ p β‖
        ≤ (2 * Real.pi) * (((p : ℕ) : ℝ) * Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ))) := by
      intro p β
      have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by
        have := p.2.two_le
        exact_mod_cast (by omega : 0 < (p : ℕ))
      have h1 : ‖χ ((p : ℕ))‖ ≤ 1 := norm_dirichletCharacter_apply_le_one χ _
      have h2 : ‖(Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ)‖
          = Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have h3 : ‖((-(2 * Real.pi * (((p : ℕ) : ℝ)))) : ℝ) * Complex.I‖
          = 2 * Real.pi * (((p : ℕ) : ℝ)) := by
        rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_neg,
          abs_of_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hp0)]
      have h4 : ‖Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ = 1 :=
        Complex.norm_exp_ofReal_mul_I _
      rw [hψ]
      simp only [norm_mul, h2, h3, h4, mul_one]
      calc ‖χ ((p : ℕ))‖ * Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) * (2 * Real.pi * (((p : ℕ) : ℝ)))
          ≤ 1 * Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) * (2 * Real.pi * (((p : ℕ) : ℝ))) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = (2 * Real.pi) * (((p : ℕ) : ℝ) * Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ))) := by ring
    have hIntBound : ∀ p : Nat.Primes, (∫ β in (0 : ℝ)..α, ‖ψ p β‖)
        ≤ α * ((2 * Real.pi) * (((p : ℕ) : ℝ) * Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)))) := by
      intro p
      have h1 : (∫ β in (0 : ℝ)..α, ‖ψ p β‖)
          ≤ ∫ β in (0 : ℝ)..α,
              ((2 * Real.pi) * (((p : ℕ) : ℝ) * Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)))) := by
        refine intervalIntegral.integral_mono hα ((hcont p).norm.intervalIntegrable 0 α) ?_
          (fun x => hbound p x)
        exact continuous_const.intervalIntegrable 0 α
      rw [intervalIntegral.integral_const] at h1
      simpa using h1
    have hsumIntNorm : Summable (fun p : Nat.Primes => ∫ β in (0 : ℝ)..α, ‖ψ p β‖) := by
      refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => hIntBound p) ?_
      · exact intervalIntegral.integral_nonneg hα (fun β _ => norm_nonneg _)
      · exact (summable_primes_exp_neg_mul N hN).mul_left (2 * Real.pi) |>.mul_left α
    have hsumφ : ∀ β : ℝ, Summable (fun p : Nat.Primes => φ p β) := by
      intro β
      have hbd : ∀ p : Nat.Primes, ‖φ p β‖ ≤ Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) := by
        intro p
        have h1 : ‖χ ((p : ℕ))‖ ≤ 1 := norm_dirichletCharacter_apply_le_one χ _
        have h2 : ‖(Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ)‖
            = Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have h3 : ‖Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ = 1 :=
          Complex.norm_exp_ofReal_mul_I _
        rw [hφ]
        simp only [norm_mul, h2, h3, mul_one]
        calc ‖χ ((p : ℕ))‖ * Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ))
            ≤ 1 * Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) :=
              mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
          _ = Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) := one_mul _
      exact Summable.of_norm_bounded (summable_primes_exp_neg N hN) hbd
    have hIntRestrict : ∀ p : Nat.Primes,
        MeasureTheory.Integrable (ψ p) (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) α)) := by
      intro p
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hα).mp (hint p)
    have hsumRestrict : Summable (fun p : Nat.Primes =>
        ∫ β, ‖ψ p β‖ ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) α))) := by
      simpa only [intervalIntegral.integral_of_le hα] using hsumIntNorm
    have hswap : (∫ β in (0 : ℝ)..α, ∑' p : Nat.Primes, ψ p β)
        = ∑' p : Nat.Primes, ∫ β in (0 : ℝ)..α, ψ p β := by
      simp only [intervalIntegral.integral_of_le hα]
      exact (MeasureTheory.integral_tsum_of_summable_integral_norm hIntRestrict hsumRestrict).symm
    have hφα : Summable (fun p : Nat.Primes => φ p α) := hsumφ α
    have hφ0 : Summable (fun p : Nat.Primes => φ p 0) := hsumφ 0
    have key : (∑' p : Nat.Primes, φ p α) - (∑' p : Nat.Primes, φ p 0)
        = ∫ β in (0 : ℝ)..α, ∑' p : Nat.Primes, ψ p β := by
      rw [← hφα.tsum_sub hφ0]
      rw [show (∑' p : Nat.Primes, (φ p α - φ p 0))
          = ∑' p : Nat.Primes, (∫ β in (0 : ℝ)..α, ψ p β) from
        tsum_congr (fun p => (hFTC p).symm)]
      exact hswap.symm
    simpa [characterPrime280, hφ, hψ] using key

/-- LEAF: Step 2 of 3: the Cauchy-Schwarz inequality for an interval integral. For
any complex valued function on the line and any nonnegative length alpha, the square
of the norm of the integral from zero to alpha is at most alpha times the integral of
the squared norm. The content is that an integral over a short interval cannot be
large unless the squared norm is large somewhere on it; no arithmetic information
enters, and at alpha equal to zero both sides are zero. -/
theorem near_sup357_integral_norm_sq357 (g : ℝ → ℂ) {α : ℝ} (hα : 0 ≤ α) :
    ‖∫ β in (0 : ℝ)..α, g β‖ ^ 2 ≤ α * ∫ β in (0 : ℝ)..α, ‖g β‖ ^ 2 := by
  sorry

/-- Reduction of step 3 to a pointwise bound. If the differentiated sum is pointwise
`O (N * sqrt q * log N)` on the permitted phase range, then its mean square is bounded:
the integral of the constant bound over an interval of length `alpha` is
`alpha * K ^ 2 * N ^ 2 * q * log N ^ 2`, and `q ^ 2 ≤ N` (from `q ≤ N ^ (1/7)`) together with
`1 ≤ log N` turns that into `alpha * N ^ 3 * log N ^ 5 / q` up to the constant `K ^ 2 + 1`.
The pointwise bound itself is the missing input, so this reduces step 3 to it. -/
private lemma near_sup357_derivative_moment_of_pointwise (K : ℝ) (hK : 0 ≤ K) (N₀ : ℕ)
    (hbd : ∀ (N : ℕ), N₀ < N → ∀ (q : ℕ), 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
      ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ β : ℝ, 0 ≤ β → β ≤ 4 / (N : ℝ) →
        ‖∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) *
            ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) *
            Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖
          ≤ K * (N : ℝ) * Real.sqrt (q : ℝ) * Real.log (N : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∀ α : ℝ, 0 ≤ α → α ≤ 4 / (N : ℝ) →
            (∫ β in (0 : ℝ)..α,
                ‖∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) *
                  ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) *
                  Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ ^ 2)
              ≤ C * α * (N : ℝ) ^ 2 * ((N : ℝ) / (q : ℝ) * Real.log (N : ℝ) ^ 5) := by
  refine ⟨K ^ 2 + 1, by positivity, max N₀ 3, ?_⟩
  intro N hN q hq hqt χ hχ α hα0 hαu
  have hNN₀ : N₀ < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN3 : 3 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN)
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN3
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := hqr.le
  set D : ℝ → ℂ := fun β => ∑' p : Nat.Primes,
    χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) *
      ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) *
      Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) with hD
  set M : ℝ := K * (N : ℝ) * Real.sqrt (q : ℝ) * Real.log (N : ℝ) with hM
  have hDval : ∀ β : ℝ, D β = ∑' p : Nat.Primes,
      χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) *
        ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) *
        Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) := by
    intro β
    rw [hD]
  have hDcont : Continuous D := by
    rw [hD]
    refine TendstoUniformly.continuous
      (tendstoUniformly_tsum ((summable_primes_exp_neg_mul N hN1).mul_left (2 * Real.pi)) ?_)
      ((Filter.Eventually.of_forall fun t => ?_).frequently)
    · intro p β
      have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by
        have h := p.2.two_le
        exact_mod_cast (by omega : 0 < (p : ℕ))
      have h1 : ‖χ ((p : ℕ))‖ ≤ 1 := norm_dirichletCharacter_apply_le_one χ _
      have h2 : ‖(Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ)‖
          = Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have h3 : ‖((-(2 * Real.pi * (((p : ℕ) : ℝ)))) : ℝ) * Complex.I‖
          = 2 * Real.pi * (((p : ℕ) : ℝ)) := by
        rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_neg,
          abs_of_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hp0)]
      have h4 : ‖Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ = 1 :=
        Complex.norm_exp_ofReal_mul_I _
      simp only [norm_mul, h2, h3, h4, mul_one]
      calc ‖χ ((p : ℕ))‖ * Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) * (2 * Real.pi * (((p : ℕ) : ℝ)))
          ≤ 1 * Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) * (2 * Real.pi * (((p : ℕ) : ℝ))) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = (2 * Real.pi) * (((p : ℕ) : ℝ) * Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ))) := by ring
    · fun_prop
  have hmono : (∫ β in (0 : ℝ)..α, ‖D β‖ ^ 2) ≤ α * M ^ 2 := by
    have h1 : (∫ β in (0 : ℝ)..α, ‖D β‖ ^ 2) ≤ ∫ β in (0 : ℝ)..α, M ^ 2 := by
      refine intervalIntegral.integral_mono_on hα0 ((hDcont.norm.pow 2).intervalIntegrable 0 α)
        (continuous_const.intervalIntegrable 0 α) ?_
      intro β hβ
      have hβ0 : 0 ≤ β := hβ.1
      have hβu : β ≤ 4 / (N : ℝ) := le_trans hβ.2 hαu
      have hb : ‖D β‖ ≤ M := by
        rw [hM]
        exact hbd N hNN₀ q hq hqt χ hχ β hβ0 hβu
      rw [hDval β]
      exact pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [intervalIntegral.integral_const] at h1
    simpa using h1
  have hM2 : M ^ 2 = K ^ 2 * (N : ℝ) ^ 2 * (q : ℝ) * Real.log (N : ℝ) ^ 2 := by
    rw [hM]
    calc (K * (N : ℝ) * Real.sqrt (q : ℝ) * Real.log (N : ℝ)) ^ 2
        = (K * (N : ℝ) * Real.log (N : ℝ)) ^ 2 * (Real.sqrt (q : ℝ)) ^ 2 := by ring
      _ = (K * (N : ℝ) * Real.log (N : ℝ)) ^ 2 * (q : ℝ) := by rw [Real.sq_sqrt hq0]
      _ = K ^ 2 * (N : ℝ) ^ 2 * (q : ℝ) * Real.log (N : ℝ) ^ 2 := by ring
  have hq2 : (q : ℝ) ^ 2 ≤ (N : ℝ) := by
    have h1 : (q : ℝ) ^ 2 ≤ ((N : ℝ) ^ (1 / 7 : ℝ)) ^ 2 := pow_le_pow_left₀ hq0 hqt 2
    have h2 : ((N : ℝ) ^ (1 / 7 : ℝ)) ^ 2 = (N : ℝ) ^ (2 / 7 : ℝ) := by
      rw [← Real.rpow_mul_natCast (le_of_lt hNpos) (1 / 7) 2]
      norm_num
    have h3 : (N : ℝ) ^ (2 / 7 : ℝ) ≤ (N : ℝ) := by
      have h := Real.rpow_le_rpow_of_exponent_le hNr (by norm_num : (2 / 7 : ℝ) ≤ 1)
      simpa using h
    calc (q : ℝ) ^ 2 ≤ ((N : ℝ) ^ (1 / 7 : ℝ)) ^ 2 := h1
      _ = (N : ℝ) ^ (2 / 7 : ℝ) := h2
      _ ≤ (N : ℝ) := h3
  have hlog1 : (1 : ℝ) ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le hNpos]
    exact le_trans (le_of_lt Real.exp_one_lt_three) (by exact_mod_cast hN3)
  have hlog2 : Real.log (N : ℝ) ^ 2 ≤ Real.log (N : ℝ) ^ 5 :=
    pow_le_pow_right₀ hlog1 (by norm_num)
  have hkey : K ^ 2 * (q : ℝ) * Real.log (N : ℝ) ^ 2
      ≤ (K ^ 2 + 1) * ((N : ℝ) / (q : ℝ)) * Real.log (N : ℝ) ^ 5 := by
    have heq : (K ^ 2 + 1) * ((N : ℝ) / (q : ℝ)) * Real.log (N : ℝ) ^ 5
        = ((K ^ 2 + 1) * (N : ℝ) * Real.log (N : ℝ) ^ 5) / (q : ℝ) := by
      field_simp
    rw [heq, le_div_iff₀ hqr]
    have h1 : K ^ 2 * (q : ℝ) ^ 2 ≤ (K ^ 2 + 1) * (N : ℝ) := by
      have h2 : K ^ 2 * (q : ℝ) ^ 2 ≤ K ^ 2 * (N : ℝ) :=
        mul_le_mul_of_nonneg_left hq2 (by positivity)
      have h3 : K ^ 2 * (N : ℝ) ≤ (K ^ 2 + 1) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hNpos.le
      linarith
    calc K ^ 2 * (q : ℝ) * Real.log (N : ℝ) ^ 2 * (q : ℝ)
        = (K ^ 2 * (q : ℝ) ^ 2) * Real.log (N : ℝ) ^ 2 := by ring
      _ ≤ ((K ^ 2 + 1) * (N : ℝ)) * Real.log (N : ℝ) ^ 5 :=
          mul_le_mul h1 hlog2 (by positivity) (by positivity)
      _ = (K ^ 2 + 1) * (N : ℝ) * Real.log (N : ℝ) ^ 5 := by ring
  calc (∫ β in (0 : ℝ)..α, ‖D β‖ ^ 2) ≤ α * M ^ 2 := hmono
    _ = α * (N : ℝ) ^ 2 * (K ^ 2 * (q : ℝ) * Real.log (N : ℝ) ^ 2) := by
        rw [hM2]; ring
    _ ≤ α * (N : ℝ) ^ 2 * ((K ^ 2 + 1) * ((N : ℝ) / (q : ℝ)) * Real.log (N : ℝ) ^ 5) := by
        refine mul_le_mul_of_nonneg_left hkey ?_
        exact mul_nonneg hα0 (by positivity)
    _ = (K ^ 2 + 1) * α * (N : ℝ) ^ 2 * ((N : ℝ) / (q : ℝ) * Real.log (N : ℝ) ^ 5) := by ring

/-- LEAF: Step 3 of 3: the mean square estimate for the derivative of the damped
character prime sum over the permitted phase range. There is a fixed positive constant
C such that for large N, every modulus q up to N to the one seventh, every nonprincipal
character mod q and every phase alpha between zero and 4 over N, the integral over the
phase interval from zero to alpha of the squared norm of the differentiated series is
at most C times alpha times N squared times N over q times log N to the fifth. The
factor N squared is the size of the differentiation, and at alpha equal to zero the
claim reads zero at most zero. -/
theorem near_sup357_derivative_moment357 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∀ α : ℝ, 0 ≤ α → α ≤ 4 / (N : ℝ) →
            (∫ β in (0 : ℝ)..α, ‖∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ ^ 2) ≤
              C * α * (N : ℝ) ^ 2 * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := by
  sorry

/-- Assembly of `near_sup357_local_variation357` from the three leaves above: write
the change of the sum as the integral of its derivative, apply Cauchy-Schwarz to that
integral, bound the resulting mean square by step 3, and use the fact that the scaled
phase alpha times N is at most 4 to turn the square of the scaled phase back into the
first power that the statement asks for. The weight N over q times log N to the fifth
is nonnegative, which is where its sign is used. No step uses
`near_sup357_local_variation357` itself. -/
theorem near_sup357_local_variation357_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ∀ α : ℝ, 0 ≤ α → α ≤ 4 / (N : ℝ) →
            ‖characterPrime280 χ N α - characterPrime280 χ N 0‖ ^ 2 ≤
              C * (4 * α * (N : ℝ)) * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := by
  obtain ⟨C, hC, Nd, hder⟩ := near_sup357_derivative_moment357 hG
  refine ⟨C, hC, max 1 Nd, ?_⟩
  intro N hN q hq hqt χ hχ α hα0 hαu
  have hN1 : 1 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN)
  have hNd : Nd < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hW : (0 : ℝ) ≤ (N : ℝ) / (q : ℝ) * Real.log N ^ 5 :=
    near_sup357_weight_nonneg357 (N := N) (q := q) hN1 hq
  have hid := near_sup357_difference_integral357 (χ := χ) (N := N) (α := α) hα0
  have hcs := near_sup357_integral_norm_sq357
    (g := fun β : ℝ => ∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)) hα0
  have hmom := hder N hNd q hq hqt χ hχ α hα0 hαu
  have hstep : ‖characterPrime280 χ N α - characterPrime280 χ N 0‖ ^ 2 ≤
      α * ∫ β in (0 : ℝ)..α, ‖∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ ^ 2 := by
    rw [hid]
    exact hcs
  have hαN4 : α * (N : ℝ) ≤ 4 := by
    have h1 : α * (N : ℝ) ≤ (4 / (N : ℝ)) * (N : ℝ) :=
      mul_le_mul_of_nonneg_right hαu hNpos.le
    have h2 : (4 / (N : ℝ)) * (N : ℝ) = 4 := by
      rw [div_mul_cancel₀ _ (ne_of_gt hNpos)]
    linarith
  have hαN0 : (0 : ℝ) ≤ α * (N : ℝ) := mul_nonneg hα0 hNpos.le
  have hsq : (α * (N : ℝ)) ^ 2 ≤ 4 * (α * (N : ℝ)) := by
    nlinarith [hαN4, hαN0]
  calc ‖characterPrime280 χ N α - characterPrime280 χ N 0‖ ^ 2
      ≤ α * ∫ β in (0 : ℝ)..α, ‖∑' p : Nat.Primes, χ ((p : ℕ)) * (Real.exp (-(((p : ℕ) : ℝ)) / (N : ℝ)) : ℂ) * ((-(2 * Real.pi * (((p : ℕ) : ℝ))) : ℝ) * Complex.I) * Complex.exp ((-(2 * Real.pi * β * (((p : ℕ) : ℝ))) : ℝ) * Complex.I)‖ ^ 2 := hstep
    _ ≤ α * (C * α * (N : ℝ) ^ 2 * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5)) :=
        mul_le_mul_of_nonneg_left hmom hα0
    _ = C * ((α * (N : ℝ)) ^ 2 * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5)) := by ring
    _ ≤ C * ((4 * (α * (N : ℝ))) * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC.le
        exact mul_le_mul_of_nonneg_right hsq hW
    _ = C * (4 * α * (N : ℝ)) * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := by ring

end LeanLab.Linnik1951
