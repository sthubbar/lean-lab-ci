/-
P0069, pages 24 to 27. CODEX task312.
The generic Perron input has no sieve construction or density conclusion.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SieveConditionsC165
import LeanLab.BHP1997.Thm4Statement

namespace LeanLab.BHP1997.Decomp312c
open Classical Complex DecompC165b
open scoped BigOperators

/-- Page 24, the reference width y1 below display 4.2. -/
noncomputable def referenceWidth (x : ℝ) : ℝ :=
  x * Real.exp (-3 * Real.log x ^ (1 / 3 : ℝ))

/-- Pages 24 and 25, the character average on I1 used in the repaired 4.2. -/
noncomputable def referenceAverage (a : ℝ → ℕ → ℝ) (x : ℝ)
    {q : ℕ} (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
    (a x k : ℂ) * χ (k : ZMod q)) / (referenceWidth x : ℂ)

/-- Page 24, display 4.1 with both signs of height as required by the
Perron contour on page 25. This is a paper statement for reviewer inspection. -/
def MeanValue41 (ε : ℝ) (a : ℝ → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
    1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
    ∀ σ ∈ ({-1, 1} : Finset ℝ),
      (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
        ‖∑ k ∈ Finset.Ioc ⌊x / 2⌋₊ ⌊2 * x⌋₊,
          (a x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (σ * t)‖) ≤
        C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)

/-- Pages 24 to 27, the mild arithmetic requirement separated from 4.1.
The normalized I1 average has density delta times u over log x with every
logarithmic saving. This is a paper statement for reviewer inspection. -/
def ReferenceDensity (u : ℝ) (a : ℝ → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
    1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
      ‖referenceAverage a x χ - Thm2.delta χ * u / Real.log x‖ ≤
        C * Real.log x ^ (-A)

/-- Page 25, display 4.5 applied to the two suffixes defining a prefix of I.
Center by the I1 average. This retains the factor 2Y for the full interval I.
This is a paper statement for reviewer inspection. -/
def RelativeDistribution (ε : ℝ) (a : ℝ → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
    1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
    ∀ t : ℝ, t ≤ x →
      ‖∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ t),
        ((a x k : ℂ) * χ (k : ZMod q) - referenceAverage a x χ)‖ ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)

/-- Page 25, display 4.5 after comparison with y1 and finite centering.
Include widths below 2 by the divisor bound. The x power absorbs endpoint
rounding. This is a paper statement for reviewer inspection. -/
def WindowComparison (ε : ℝ) (a : ℝ → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
    1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
    ∀ y : ℝ, 0 ≤ y → y ≤ referenceWidth x →
      ‖∑ k ∈ Finset.Ioc ⌊x - y⌋₊ ⌊x⌋₊,
        ((a x k : ℂ) * χ (k : ZMod q) - referenceAverage a x χ)‖ ≤
        C * (y * Real.log x ^ (-A) + x ^ (0.55 + 11 * ε / 12))

/-- Page 3, condition i, display 1.7, for a real coefficient family.
This is a paper statement for reviewer inspection. -/
def CharacterDistribution (ε u : ℝ) (a : ℝ → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
    1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
    ∀ t : ℝ, t ≤ x →
      ‖∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ t),
        ((a x k : ℂ) * χ (k : ZMod q) - Thm2.delta χ * u / Real.log x)‖ ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)

/-- Pages 26 and 27, the absolute truncation error controlled by 4.11
and 4.12. The actual sifted coefficients and the auxiliary mean-value
coefficients agree on I up to every logarithmic saving.
This is a paper statement for reviewer inspection. -/
def ShortApproximation (ε : ℝ) (a b : ℝ → ℕ → ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
    (∑ k ∈ leftInterval ε x, |a x k - b x k|) ≤
      C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)

/-- LEAF. Pages 24 and 25, Lemma 11, displays 4.1, 4.3, 4.4 and 4.5.
Perron comparison with the normalized I1 mean, for both signs of height.
The finite centering error and widths below 2 use the divisor bound.
This input asserts no density, prime sandwich, discarded-region estimate
or coefficient construction. OPEN. -/
theorem perron_window_comparison (B : ℝ) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ a : ℝ → ℕ → ℝ,
      (∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) →
      MeanValue41 ε a → WindowComparison ε a := by
  sorry

/-- Page 26, pair the divisors d and p times d. Only products crossing gamma remain in the truncated Möbius sum. -/
theorem mobius_truncation_crossing {p m : ℕ} (hp : p.Prime) (hpm : p.Coprime m)
    (γ : ℝ) :
    (∑ d ∈ (p * m).divisors.filter (fun d : ℕ => (d : ℝ) ≤ γ),
      (ArithmeticFunction.moebius d : ℝ)) =
    ∑ d ∈ m.divisors.filter (fun d : ℕ => (d : ℝ) ≤ γ ∧ γ < ((p * d : ℕ) : ℝ)),
      (ArithmeticFunction.moebius d : ℝ) := by
  have hμ (d : ℕ) (hd : d ∈ m.divisors) :
      (ArithmeticFunction.moebius (p * d) : ℝ) = -(ArithmeticFunction.moebius d : ℝ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (hpm.coprime_dvd_right (Nat.mem_divisors.mp hd).1),
      ArithmeticFunction.moebius_apply_prime hp]
    push_cast
    ring
  rw [Finset.sum_filter, Nat.divisors_mul, Finset.mul_def,
    Finset.sum_image hpm.mul_injOn_divisors, Finset.sum_product]
  rw [hp.divisors, Finset.sum_pair (Ne.symm hp.ne_one)]
  simp only [one_mul]
  rw [← Finset.sum_add_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hμ d hd]
  have hle : (d : ℝ) ≤ (p : ℝ) * (d : ℝ) := by
    exact_mod_cast Nat.le_mul_of_pos_left d hp.pos
  simp only [Nat.cast_mul]
  by_cases hpd : (p : ℝ) * (d : ℝ) ≤ γ
  · have hdγ : (d : ℝ) ≤ γ := hle.trans hpd
    simp [hpd, hdγ, not_lt.mpr hpd]
  · by_cases hdγ : (d : ℝ) ≤ γ
    · simp [hpd, hdγ, lt_of_not_ge hpd]
    · simp [hpd, hdγ]

/-- Page 26, inject the crossing products into the intermediate divisor band. Their Möbius coefficients have absolute value at most 1. -/
theorem mobius_truncation_band {p m : ℕ} (hp : p.Prime) (hpm : p.Coprime m)
    {γ w : ℝ} (hγ : 0 < γ) (hpw : (p : ℝ) < w) :
    |∑ d ∈ (p * m).divisors.filter (fun d : ℕ => (d : ℝ) ≤ γ),
      (ArithmeticFunction.moebius d : ℝ)| ≤
    (((p * m).divisors.filter (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w)).card : ℝ) := by
  let S := m.divisors.filter (fun d : ℕ => (d : ℝ) ≤ γ ∧ γ < ((p * d : ℕ) : ℝ))
  let T := (p * m).divisors.filter (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w)
  have hc : S.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (fun d : ℕ => p * d)
    · intro d hd
      obtain ⟨hdm, hdγ, hγd⟩ := Finset.mem_filter.mp hd
      apply Finset.mem_filter.mpr
      refine ⟨Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left p (Nat.mem_divisors.mp hdm).1,
        mul_ne_zero hp.ne_zero (Nat.mem_divisors.mp hdm).2⟩, hγd.le, ?_⟩
      calc
        ((p * d : ℕ) : ℝ) = (p : ℝ) * (d : ℝ) := by norm_cast
        _ ≤ (p : ℝ) * γ := mul_le_mul_of_nonneg_left hdγ (Nat.cast_nonneg _)
        _ < w * γ := mul_lt_mul_of_pos_right hpw hγ
        _ = γ * w := mul_comm _ _
    · intro d hd e he hde
      exact Nat.eq_of_mul_eq_mul_left hp.pos hde
  rw [mobius_truncation_crossing hp hpm]
  calc
    _ ≤ ∑ d ∈ S, |(ArithmeticFunction.moebius d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    _ = (S.card : ℝ) := by simp
    _ ≤ (T.card : ℝ) := by exact_mod_cast hc

/-- Page 26, P of z is squarefree because its prime factors are distinct. -/
theorem primorial_squarefree (z : ℝ) : Squarefree (Thm2.primorialBelow z) := by
  unfold Thm2.primorialBelow
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    (fun p hp => (Finset.mem_filter.mp hp).2.1.squarefree)
  change IsRelPrime p q
  rw [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Finset.mem_filter.mp hp).2.1
    (Finset.mem_filter.mp hq).2.1).mpr hpq

/-- Pages 25 and 26, every prime divisor of P of z is less than z. -/
theorem prime_lt_of_dvd_primorial {p : ℕ} {z : ℝ} (hp : p.Prime)
    (hd : p ∣ Thm2.primorialBelow z) : (p : ℝ) < z := by
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
  obtain ⟨hqprime, hqz⟩ := (Finset.mem_filter.mp hq).2
  have he : p = q := ((Nat.dvd_prime hqprime).mp hpq).resolve_left hp.ne_one
  simpa only [he] using hqz


/-- Page 26, the intermediate-band truncation for a squarefree integer. A prime divisor pairs the two halves of its divisor set. -/
theorem squarefree_mobius_truncation (N : ℕ) (hN : Squarefree N)
    {γ w : ℝ} (hγ : 1 ≤ γ)
    (hw : ∀ p : ℕ, p.Prime → p ∣ N → (p : ℝ) < w) :
    |(if N = 1 then (1 : ℝ) else 0) -
      ∑ d ∈ N.divisors.filter (fun d : ℕ => (d : ℝ) ≤ γ),
        (ArithmeticFunction.moebius d : ℝ)| ≤
    ((N.divisors.filter (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * w)).card : ℝ) := by
  by_cases hN1 : N = 1
  · subst N
    simp only [Nat.divisors_one, Finset.filter_singleton, Nat.cast_one]
    rw [ite_eq_left hγ]
    simp
  · let p := N.minFac
    have hp : p.Prime := Nat.minFac_prime hN1
    have hpd : p ∣ N := Nat.minFac_dvd N
    have hfactor : p * (N / p) = N := Nat.mul_div_cancel' hpd
    have hcop : p.Coprime (N / p) := Nat.coprime_of_squarefree_mul (hfactor.symm ▸ hN)
    have hb := mobius_truncation_band hp hcop (by linarith : 0 < γ) (hw p hp hpd)
    rw [hfactor] at hb
    simpa only [ite_eq_right hN1, zero_sub, abs_neg] using hb

/-- Page 27, an auxiliary finite Rankin reduction for the reciprocal divisor tail.
It leaves a prime product explicit and does not assert Hildebrand 4.13.
Reuses Mathlib's multiplicative divisor Euler product. -/
theorem squarefree_reciprocal_rankin (N : ℕ) (hN : Squarefree N)
    {γ α : ℝ} (hγ : 0 < γ) (hα0 : 0 ≤ α) (hα : α < 1) :
    (∑ d ∈ N.divisors.filter (fun d : ℕ => γ ≤ (d : ℝ)), 1 / (d : ℝ)) ≤
      γ ^ (-α) * ∏ p ∈ N.primeFactors, (1 + (p : ℝ) ^ (α - 1)) := by
  let f : ArithmeticFunction ℝ := ⟨fun n => (n : ℝ) ^ (α - 1), by
    simp only [Nat.cast_zero, Real.zero_rpow (by linarith : α - 1 ≠ 0)]⟩
  have hf : f.IsMultiplicative := by
    rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
    refine ⟨by simp [f], ?_⟩
    intro m n hm hn hmn
    change ((m * n : ℕ) : ℝ) ^ (α - 1) = (m : ℝ) ^ (α - 1) * (n : ℝ) ^ (α - 1)
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  have hp : (∑ d ∈ N.divisors, (d : ℝ) ^ (α - 1)) =
      ∏ p ∈ N.primeFactors, (1 + (p : ℝ) ^ (α - 1)) := by
    simpa only [f, ArithmeticFunction.coe_mk] using
      (hf.prodPrimeFactors_one_add_of_squarefree hN).symm
  let S := N.divisors.filter (fun d : ℕ => γ ≤ (d : ℝ))
  calc
    _ ≤ ∑ d ∈ S, γ ^ (-α) * (d : ℝ) ^ (α - 1) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdγ := (Finset.mem_filter.mp hd).2
      have hd0 : 0 < (d : ℝ) := hγ.trans_le hdγ
      have hpow := Real.rpow_le_rpow_of_nonpos hγ hdγ (neg_nonpos.mpr hα0)
      calc
        1 / (d : ℝ) = (d : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
        _ = (d : ℝ) ^ (-α) * (d : ℝ) ^ (α - 1) := by
          rw [← Real.rpow_add hd0]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = γ ^ (-α) * ∑ d ∈ S, (d : ℝ) ^ (α - 1) := (Finset.mul_sum _ _ _).symm
    _ ≤ γ ^ (-α) * ∑ d ∈ N.divisors, (d : ℝ) ^ (α - 1) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun d hd hdS => Real.rpow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg hγ.le _)
    _ = _ := by rw [hp]

end LeanLab.BHP1997.Decomp312c
