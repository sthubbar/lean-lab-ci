/-
Independent split of the finite endpoint replacement step of the periodic
principal model. The complete period integral is replaced by the exact finite
convolution count, the truncated residue sum carries one uniform envelope, and
the squared count deviation over the even frequency set must save one arbitrary
power of the logarithm. That saving is the only arithmetic input of the split.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.PrincipalData635

namespace LeanLab.BHP1997.Decomp561m
open Classical Complex Thm2 MeasureTheory Set Decomp561d Decomp561e

/-- Integer exponentials are orthogonal on any complete period. -/
private theorem integral_fourier561 (n : ℤ) (c : ℝ) :
    (∫ t in c..c + 1, @fourier 1 n (t : AddCircle (1 : ℝ))) = if n = 0 then 1 else 0 := by
  have h := fourierCoeff_eq_intervalIntegral (T := (1 : ℝ)) (@fourier 1 n) 0 c
  simp only [one_div_one, one_smul] at h
  rw [fourierCoeff_fourier] at h
  simpa [Pi.single_apply, eq_comm] using h.symm

/-- Expand the product of two finite exponential polynomials. -/
private theorem polynomial_product561 (S T : Finset ℕ) (a b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    polynomial512 S a t * polynomial512 T b t * @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ)) =
      ∑ k ∈ S, ∑ m ∈ T, (a k * b m) *
        @fourier 1 ((k : ℤ) + (m : ℤ) - (N : ℤ)) (t : AddCircle (1 : ℝ)) := by
  simp only [polynomial512, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro m hm
  rw [sub_eq_add_neg, fourier_add, fourier_add]
  ring

/-- Orthogonality converts the period integral to the exact convolution. -/
private theorem convolution_integral561 (S T : Finset ℕ) (a b : ℕ → ℂ) (N : ℕ) (c : ℝ) :
    (∫ t in c..c + 1, polynomial512 S a t * polynomial512 T b t *
      @fourier 1 (-(N : ℤ)) (t : AddCircle (1 : ℝ))) =
        ∑ k ∈ S, ∑ m ∈ T, if k + m = N then a k * b m else 0 := by
  have hc (k m : ℕ) : Continuous (fun t : ℝ => (a k * b m) *
      @fourier 1 ((k : ℤ) + (m : ℤ) - (N : ℤ)) (t : AddCircle (1 : ℝ))) :=
    continuous_const.mul ((map_continuous (fourier _)).comp (AddCircle.continuous_mk' 1))
  simp_rw [polynomial_product561]
  rw [intervalIntegral.integral_finsetSum (fun k hk =>
    (continuous_finsetSum T fun m hm => hc k m).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [intervalIntegral.integral_finsetSum (fun m hm => (hc k m).intervalIntegrable _ _)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [intervalIntegral.integral_const_mul, integral_fourier561]
  have he : (k : ℤ) + (m : ℤ) - (N : ℤ) = 0 ↔ k + m = N := by omega
  simp [he]

/-- The filtered product card as a double indicator sum. -/
private theorem product_filter_card561 (S T : Finset ℕ) (N : ℕ) :
    ((S.product T).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card
      = ∑ k ∈ S, ∑ m ∈ T, if k + m = N then 1 else 0 := by
  rw [Finset.card_filter]
  exact Finset.sum_product' S T (fun k m => if k + m = N then 1 else 0)

/-- LEAF. Exact finite convolution count on one complete period: the integral of
the integrand against a complete period of the additive character is the number
of pairs, one from the long support and one from the short support, whose sum is
the even frequency. There is no analytic input, and the short window is already a
complete period. -/
theorem leaf_endpoint_count_identity561 (ε x : ℝ) (N : ℕ) :
    (∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        integrand512 ε x (fun _ => 1) (fun _ => 1) N t) =
      (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) : ℂ) := by
  have hint : (∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        integrand512 ε x (fun _ => 1) (fun _ => 1) N t) =
      ∫ t in (-(1 / 2 : ℝ))..(-(1 / 2 : ℝ)) + 1,
        integrand512 ε x (fun _ => 1) (fun _ => 1) N t := by
    norm_num
  rw [hint]
  simp only [integrand512]
  rw [convolution_integral561]
  rw [product_filter_card561]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro m hm
  by_cases h : k + m = N
  · simp [h]
  · simp [h]

/-- LEAF. Factorization of the endpoint difference: the complete period model and
the truncated main term carry the same prefactor and the same truncated residue
sum, so their difference is that prefactor times that residue sum times the
difference between the complete period integral and the short interval length.
Pure algebra, no estimate. -/
theorem leaf_endpoint_factorization561 (ε D x u v : ℝ) (N : ℕ) :
    completePrincipal561 ε D x u v N - truncatedMain512 ε D x u v N =
      ((u * v / (Real.log x * Real.log (length512 ε x)) : ℝ) : ℂ) *
        (∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
            (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
              ramanujan512 q N) *
        ((∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        integrand512 ε x (fun _ => 1) (fun _ => 1) N t) -
          (length512 ε x : ℂ)) := by
  simp only [completePrincipal561, truncatedMain512, Finset.sum_mul, Finset.mul_sum]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

private theorem phi_card561 (q : ℕ) (hq : 0 < q) :
    ((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card = q.totient := by
  have hf : (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)
      = (Finset.Icc 1 q).filter (fun r => q.Coprime r) := by
    apply Finset.filter_congr
    intro r _
    exact Nat.coprime_comm
  rw [hf, Nat.totient_eq_card_coprime]
  rcases Nat.lt_or_eq_of_le hq with h | h
  · congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, hc⟩
      refine ⟨lt_of_le_of_ne h2 ?_, hc⟩
      rintro rfl
      rw [Nat.coprime_self] at hc
      omega
    · rintro ⟨h1, hc⟩
      refine ⟨⟨?_, le_of_lt h1⟩, hc⟩
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · subst h0
        rw [Nat.coprime_zero_right] at hc
        omega
      · exact h0
  · subst h
    decide

private theorem ramanujan_bound561 (q N : ℕ) (hq : 0 < q) :
    ‖ramanujan512 q N‖ ≤ (q.totient : ℝ) := by
  unfold ramanujan512
  have hterm : ∀ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
      ‖@fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))‖ = 1 := by
    intro r hr
    rw [fourier_apply]
    exact Circle.norm_coe _
  calc ‖∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
        @fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))‖
      ≤ ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q),
          ‖@fourier 1 (-(N : ℤ)) (((r : ℝ) / q : ℝ) : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
    _ = ∑ r ∈ (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q), (1 : ℝ) :=
        Finset.sum_congr rfl hterm
    _ = (((Finset.Icc 1 q).filter (fun r => Nat.Coprime r q)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = (q.totient : ℝ) := by rw [phi_card561 q hq]

private theorem totient_mul_card_divisors_ge561 (q : ℕ) (hq : q ≠ 0) :
    q ≤ q.divisors.card * q.totient := by
  have hBpos : 0 < ∏ p ∈ q.primeFactors, (p - 1) :=
    Finset.prod_pos (fun p hp => Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt)
  have h1 : q.totient * ∏ p ∈ q.primeFactors, p = q * ∏ p ∈ q.primeFactors, (p - 1) :=
    Nat.totient_mul_prod_primeFactors q
  have hcard : q.divisors.card = ∏ p ∈ q.primeFactors, (q.factorization p + 1) :=
    Nat.card_divisors hq
  have hterm : ∀ p ∈ q.primeFactors, p ≤ (q.factorization p + 1) * (p - 1) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hmem : p ∈ q.factorization.support := by
      rw [Nat.support_factorization]; exact hp
    have hk : 1 ≤ q.factorization p := by
      have h0 : q.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hmem
      omega
    have hsub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
    have hsub1 : 1 ≤ p - 1 := by omega
    nlinarith [hk, hsub1, hsub]
  have hprod : ∏ p ∈ q.primeFactors, p
      ≤ ∏ p ∈ q.primeFactors, ((q.factorization p + 1) * (p - 1)) :=
    Finset.prod_le_prod hterm
  rw [Finset.prod_mul_distrib] at hprod
  have h2 : q * ∏ p ∈ q.primeFactors, (p - 1)
      ≤ (q.totient * ∏ p ∈ q.primeFactors, (q.factorization p + 1)) *
        ∏ p ∈ q.primeFactors, (p - 1) := by
    calc q * ∏ p ∈ q.primeFactors, (p - 1)
        = q.totient * ∏ p ∈ q.primeFactors, p := h1.symm
      _ ≤ q.totient * ((∏ p ∈ q.primeFactors, (q.factorization p + 1)) *
            ∏ p ∈ q.primeFactors, (p - 1)) :=
          Nat.mul_le_mul_left _ hprod
      _ = (q.totient * ∏ p ∈ q.primeFactors, (q.factorization p + 1)) *
            ∏ p ∈ q.primeFactors, (p - 1) := by ring
  have h3 : q ≤ q.totient * ∏ p ∈ q.primeFactors, (q.factorization p + 1) :=
    Nat.le_of_mul_le_mul_right h2 hBpos
  rw [hcard]
  calc q ≤ q.totient * ∏ p ∈ q.primeFactors, (q.factorization p + 1) := h3
    _ = (∏ p ∈ q.primeFactors, (q.factorization p + 1)) * q.totient := by ring

private theorem inv_totient_le561 (q : ℕ) (hq : 0 < q) :
    (1 : ℝ) / (q.totient : ℝ) ≤ (q.divisors.card : ℝ) / (q : ℝ) := by
  have hq0 : q ≠ 0 := by omega
  have hphi : (0 : ℝ) < (q.totient : ℝ) := by
    have : 0 < q.totient := Nat.totient_pos.mpr hq
    exact_mod_cast this
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hge : (q : ℝ) ≤ (q.divisors.card : ℝ) * (q.totient : ℝ) := by
    exact_mod_cast totient_mul_card_divisors_ge561 q hq0
  refine (div_le_div_iff₀ hphi hqR).mpr ?_
  simpa using hge

private theorem harmonic_sum_le561 (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 n, (1 : ℝ) / (m : ℝ)) ≤ 1 + Real.log (n : ℝ) := by
  have h := harmonic_le_one_add_log n
  have heq : (∑ m ∈ Finset.Icc 1 n, (1 : ℝ) / (m : ℝ)) = ((harmonic n : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [one_div]
  rw [heq]
  exact h

private theorem sum_inv_totient_le561 (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / (q.totient : ℝ)) ≤
      (1 + Real.log (Q : ℝ)) ^ 2 := by
  rcases Nat.eq_zero_or_pos Q with hQ | hQ
  · rw [hQ]; simp
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hlogQ : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg hQ1
  -- A: compare with tau/q
  have hA : ∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / (q.totient : ℝ)
      ≤ ∑ q ∈ Finset.Icc 1 Q, (q.divisors.card : ℝ) / (q : ℝ) := by
    apply Finset.sum_le_sum
    intro q hq
    exact inv_totient_le561 q (Finset.mem_Icc.mp hq).1
  refine hA.trans ?_
  -- B: tau(q)/q as a double sum over the same index set
  have hB : ∑ q ∈ Finset.Icc 1 Q, (q.divisors.card : ℝ) / (q : ℝ)
      = ∑ q ∈ Finset.Icc 1 Q, ∑ d ∈ Finset.Icc 1 Q,
          (if d ∣ q then (1 : ℝ) / (q : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro q hq
    obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hq
    have hdiv : q.divisors = (Finset.Icc 1 Q).filter (fun d => d ∣ q) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdvd, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdvd) hqQ⟩, hdvd⟩
      · rintro ⟨⟨hd1, -⟩, hdvd⟩
        exact ⟨hdvd, by omega⟩
    rw [hdiv, Finset.card_filter]
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases h : d ∣ q <;> simp [h]
  rw [hB, Finset.sum_comm]
  -- D: bound for each d
  have hD : ∀ d ∈ Finset.Icc 1 Q,
      (∑ q ∈ Finset.Icc 1 Q, (if d ∣ q then (1 : ℝ) / (q : ℝ) else 0))
        ≤ (1 : ℝ) / (d : ℝ) * (1 + Real.log (Q : ℝ)) := by
    intro d hd
    obtain ⟨hd1, hdQ⟩ := Finset.mem_Icc.mp hd
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    let f : ℕ → ℕ := fun m => d * m
    have hinj : Set.InjOn f (Finset.Icc 1 (Q / d) : Set ℕ) := by
      intro a _ b _ hab
      have : d * a = d * b := hab
      exact Nat.mul_left_cancel (by omega) this
    have hsub : (Finset.Icc 1 Q).filter (fun q => d ∣ q) ⊆
        (Finset.Icc 1 (Q / d)).image f := by
      intro q hq
      obtain ⟨hqI, hdvd⟩ := Finset.mem_filter.mp hq
      obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hqI
      have hdle : d ≤ q := Nat.le_of_dvd (by omega) hdvd
      have hq1' : 1 ≤ q / d := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
        simpa using hdle
      refine Finset.mem_image.mpr ⟨q / d, Finset.mem_Icc.mpr ⟨hq1', Nat.div_le_div_right hqQ⟩, ?_⟩
      exact Nat.mul_div_cancel' hdvd
    have hstep1 : ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (1 : ℝ) / (q : ℝ)
        ≤ ∑ m ∈ Finset.Icc 1 (Q / d), (1 : ℝ) / (d * m : ℕ) := by
      have h1 : ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (1 : ℝ) / (q : ℝ)
          ≤ ∑ q ∈ (Finset.Icc 1 (Q / d)).image f, (1 : ℝ) / (q : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
      rwa [Finset.sum_image hinj] at h1
    have hstep2 : ∑ m ∈ Finset.Icc 1 (Q / d), (1 : ℝ) / (d * m : ℕ)
        ≤ (1 / (d : ℝ)) * (∑ m ∈ Finset.Icc 1 (Q / d), (1 : ℝ) / (m : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro m hm
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      have heq : (1 : ℝ) / (d * m : ℕ) = (1 / (d : ℝ)) * (1 / (m : ℝ)) := by
        push_cast
        field_simp
      rw [heq]
    have hstep3 : (1 / (d : ℝ)) * (∑ m ∈ Finset.Icc 1 (Q / d), (1 : ℝ) / (m : ℝ))
        ≤ (1 / (d : ℝ)) * (1 + Real.log ((Q / d : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left (harmonic_sum_le561 (Q / d))
      positivity
    have hstep4 : (1 / (d : ℝ)) * (1 + Real.log ((Q / d : ℕ) : ℝ))
        ≤ (1 / (d : ℝ)) * (1 + Real.log (Q : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rcases Nat.eq_zero_or_pos (Q / d) with h0 | h0
      · rw [h0]
        simp only [Nat.cast_zero, Real.log_zero]
        linarith
      · have hpos : (0 : ℝ) < ((Q / d : ℕ) : ℝ) := by exact_mod_cast h0
        have hle : ((Q / d : ℕ) : ℝ) ≤ (Q : ℝ) := by
          exact_mod_cast Nat.div_le_self Q d
        linarith [Real.log_le_log hpos hle]
    calc ∑ q ∈ Finset.Icc 1 Q, (if d ∣ q then (1 : ℝ) / (q : ℝ) else 0)
        = ∑ q ∈ (Finset.Icc 1 Q).filter (fun q => d ∣ q), (1 : ℝ) / (q : ℝ) :=
          (Finset.sum_filter ..).symm
      _ ≤ _ := hstep1
      _ ≤ _ := hstep2
      _ ≤ _ := hstep3
      _ ≤ _ := hstep4
  refine (Finset.sum_le_sum hD).trans ?_
  have hE : ∑ d ∈ Finset.Icc 1 Q, (1 / (d : ℝ)) * (1 + Real.log (Q : ℝ))
      = (∑ d ∈ Finset.Icc 1 Q, (1 : ℝ) / (d : ℝ)) * (1 + Real.log (Q : ℝ)) :=
    (Finset.sum_mul ..).symm
  rw [hE]
  have hH : (∑ d ∈ Finset.Icc 1 Q, (1 : ℝ) / (d : ℝ)) ≤ 1 + Real.log (Q : ℝ) :=
    harmonic_sum_le561 Q
  have hc : (0 : ℝ) ≤ 1 + Real.log (Q : ℝ) := by linarith
  nlinarith [hH, hc]

private theorem one_lt_log_three561 : (1 : ℝ) < Real.log 3 := by
  have h := Real.log_lt_log (Real.exp_pos 1) Real.exp_one_lt_three
  rwa [Real.log_exp] at h

/-- LEAF. Uniform residue sum envelope: for a fixed exponent and a fixed arc
parameter the logarithm normalized prefactor times the truncated residue sum of
the principal model stays below one constant on the whole half line, uniformly in
the frequency and in the length. Only the trivial size of each residue term is
used, never any cancellation. -/
theorem leaf_endpoint_residue_envelope561 (ε D u v : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → ∀ N : ℕ,
      ((u * v / (Real.log x * Real.log (length512 ε x))) ^ 2 *
          ‖(∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
            (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
              ramanujan512 q N)‖ ^ 2) ≤ C := by
  set e0 : ℝ := 11 / 20 + ε with he0
  by_cases he0z : e0 = 0
  · refine ⟨1, one_pos, ?_⟩
    intro x hx N
    have hlogY : Real.log (length512 ε x) = 0 := by
      rw [show length512 ε x = x ^ (11 / 20 + ε) from rfl,
        Real.log_rpow (by linarith : (0:ℝ) < x), ← he0, he0z, zero_mul]
    rw [hlogY, mul_zero, div_zero]
    simp
  · set M : ℝ := 1 + max (2 * D) 0 with hM
    refine ⟨max 1 ((u * v) ^ 2 * M ^ 4 / e0 ^ 2), lt_max_of_lt_left one_pos, ?_⟩
    intro x hx N
    have hxpos : (0 : ℝ) < x := by linarith
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hlogx3 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have hlogx1' : (1 : ℝ) < Real.log x := lt_of_lt_of_le one_lt_log_three561 hlogx3
    have hlogx1 : (1 : ℝ) ≤ Real.log x := le_of_lt hlogx1'
    set Q : ℕ := ⌊Real.log x ^ (2 * D)⌋₊ with hQdef
    have hM1 : (1 : ℝ) ≤ M := by
      rw [hM]
      have := le_max_right (2 * D) 0
      linarith
    -- each residue term is at most 1/phi
    have hterm : ∀ q ∈ Finset.Icc 1 Q,
        ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
            ramanujan512 q N‖ ≤ (1 : ℝ) / (q.totient : ℝ) := by
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hqpos : 0 < q := by omega
      have hphi : (0 : ℝ) < (q.totient : ℝ) := by
        have : 0 < q.totient := Nat.totient_pos.mpr hqpos
        exact_mod_cast this
      have hmu : ‖(((ArithmeticFunction.moebius q : ℤ)) : ℂ)‖ ≤ 1 := by
        have h := ArithmeticFunction.abs_moebius_le_one (n := q)
        rw [Complex.norm_intCast]
        exact_mod_cast h
      have hram := ramanujan_bound561 q N hqpos
      have hphiC : ‖(Nat.totient q : ℂ)‖ = (q.totient : ℝ) := Complex.norm_natCast q.totient
      have hmu' : ‖(((ArithmeticFunction.moebius q : ℤ)) : ℂ)‖ ^ 2 ≤ 1 := by
        nlinarith [hmu, norm_nonneg (((ArithmeticFunction.moebius q : ℤ)) : ℂ)]
      have hstep1 : ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
            ramanujan512 q N‖ =
          ‖(ArithmeticFunction.moebius q : ℂ) ^ 2‖ / ‖(Nat.totient q : ℂ) ^ 2‖ *
            ‖ramanujan512 q N‖ := by
        rw [norm_mul, norm_div]
      have hstep2 : ‖(ArithmeticFunction.moebius q : ℂ) ^ 2‖ / ‖(Nat.totient q : ℂ) ^ 2‖ *
            ‖ramanujan512 q N‖ =
          ‖(((ArithmeticFunction.moebius q : ℤ)) : ℂ)‖ ^ 2 / (q.totient : ℝ) ^ 2 *
            ‖ramanujan512 q N‖ := by
        rw [norm_pow, norm_pow, hphiC]
      have hstep3 : ‖(((ArithmeticFunction.moebius q : ℤ)) : ℂ)‖ ^ 2 / (q.totient : ℝ) ^ 2 *
            ‖ramanujan512 q N‖ ≤ (1 : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * (q.totient : ℝ) := by
        apply mul_le_mul
        · refine div_le_div_of_nonneg_right ?_ (by positivity)
          rw [one_pow]
          exact hmu'
        · exact hram
        · exact norm_nonneg _
        · positivity
      have hstep4 : (1 : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * (q.totient : ℝ)
          = (1 : ℝ) / (q.totient : ℝ) := by
        rw [one_pow]
        field_simp
      rw [hstep1, hstep2]
      linarith [hstep3, hstep4]
    have hS : ‖(∑ q ∈ Finset.Icc 1 Q,
        (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
          ramanujan512 q N)‖ ≤ (1 + Real.log (Q : ℝ)) ^ 2 := by
      calc ‖(∑ q ∈ Finset.Icc 1 Q,
            (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
              ramanujan512 q N)‖
          ≤ ∑ q ∈ Finset.Icc 1 Q,
              ‖(ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
                ramanujan512 q N‖ := norm_sum_le _ _
        _ ≤ ∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) / (q.totient : ℝ) := Finset.sum_le_sum hterm
        _ ≤ (1 + Real.log (Q : ℝ)) ^ 2 := sum_inv_totient_le561 Q
    -- logarithm of the short length
    have hlogY : Real.log (length512 ε x) = e0 * Real.log x := by
      rw [show length512 ε x = x ^ (11 / 20 + ε) from rfl, Real.log_rpow hxpos, he0]
    have hden : Real.log x * Real.log (length512 ε x) = e0 * (Real.log x) ^ 2 := by
      rw [hlogY]; ring
    -- Q is at most a fixed power of log x
    have hlogQ : Real.log (Q : ℝ) ≤ max (2 * D) 0 * Real.log x := by
      have hllog_pos : 0 < Real.log (Real.log x) := Real.log_pos hlogx1'
      have hllog_le : Real.log (Real.log x) ≤ Real.log x := by
        have := Real.log_le_sub_one_of_pos hlogx
        linarith
      rcases Nat.eq_zero_or_pos Q with h0 | h0
      · rw [h0]
        simp only [Nat.cast_zero, Real.log_zero]
        have h2 : (0:ℝ) ≤ max (2 * D) 0 := le_max_right (2 * D) 0
        have := mul_nonneg h2 hlogx.le
        linarith
      · have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast h0
        have hfloor : (Q : ℝ) ≤ Real.log x ^ (2 * D) := by
          have h := Nat.floor_le (show (0:ℝ) ≤ Real.log x ^ (2 * D) by positivity)
          rw [hQdef]
          exact h
        have hle := Real.log_le_log hQpos hfloor
        rw [Real.log_rpow hlogx] at hle
        by_cases hD : 0 ≤ 2 * D
        · have h3 : 2 * D * Real.log (Real.log x) ≤ 2 * D * Real.log x :=
            mul_le_mul_of_nonneg_left hllog_le hD
          have h4 : 2 * D * Real.log x ≤ max (2 * D) 0 * Real.log x :=
            mul_le_mul_of_nonneg_right (le_max_left (2 * D) 0) hlogx.le
          linarith
        · exfalso
          have hlogQ0 : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg (by exact_mod_cast h0)
          nlinarith [hle, hllog_pos, hlogQ0]
    have hQle : 1 + Real.log (Q : ℝ) ≤ M * Real.log x := by
      have h2 : 1 + max (2 * D) 0 * Real.log x ≤ M * Real.log x := by
        rw [hM]
        nlinarith [hlogx1, le_max_right (2 * D) 0]
      linarith
    -- assemble
    rw [hden]
    have hu : (0:ℝ) < e0 ^ 2 * (Real.log x) ^ 4 := by
      have : e0 ≠ 0 := he0z
      positivity
    have hfac : (u * v / (e0 * (Real.log x) ^ 2)) ^ 2 =
        (u * v) ^ 2 / (e0 ^ 2 * (Real.log x) ^ 4) := by
      have he0ne : e0 ≠ 0 := he0z
      have hxne : Real.log x ≠ 0 := ne_of_gt hlogx
      field_simp
    rw [hfac]
    have hS2 : ‖(∑ q ∈ Finset.Icc 1 Q,
        (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
          ramanujan512 q N)‖ ^ 2 ≤ (M * Real.log x) ^ 4 := by
      have h2 : ‖(∑ q ∈ Finset.Icc 1 Q,
          (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
            ramanujan512 q N)‖ ^ 2 ≤ ((1 + Real.log (Q : ℝ)) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hS 2
      have hQ0 : (0:ℝ) ≤ 1 + Real.log (Q : ℝ) := by
        rcases Nat.eq_zero_or_pos Q with h0 | h0
        · rw [h0]; simp
        · have := Real.log_nonneg (by exact_mod_cast h0 : (1:ℝ) ≤ (Q:ℝ))
          linarith
      calc ‖(∑ q ∈ Finset.Icc 1 Q,
            (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
              ramanujan512 q N)‖ ^ 2
          ≤ ((1 + Real.log (Q : ℝ)) ^ 2) ^ 2 := h2
        _ = (1 + Real.log (Q : ℝ)) ^ 4 := by ring
        _ ≤ (M * Real.log x) ^ 4 := pow_le_pow_left₀ hQ0 hQle 4
    have hfinal : (u * v) ^ 2 / (e0 ^ 2 * (Real.log x) ^ 4) *
        ‖(∑ q ∈ Finset.Icc 1 Q,
          (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
            ramanujan512 q N)‖ ^ 2 ≤ (u * v) ^ 2 * M ^ 4 / e0 ^ 2 := by
      have h1 : (u * v) ^ 2 / (e0 ^ 2 * (Real.log x) ^ 4) *
          ‖(∑ q ∈ Finset.Icc 1 Q,
            (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
              ramanujan512 q N)‖ ^ 2
          ≤ (u * v) ^ 2 / (e0 ^ 2 * (Real.log x) ^ 4) * (M * Real.log x) ^ 4 :=
        mul_le_mul_of_nonneg_left hS2 (by positivity)
      have h2 : (u * v) ^ 2 / (e0 ^ 2 * (Real.log x) ^ 4) * (M * Real.log x) ^ 4
          = (u * v) ^ 2 * M ^ 4 / e0 ^ 2 := by
        have he0ne : e0 ≠ 0 := he0z
        have hxne : Real.log x ≠ 0 := ne_of_gt hlogx
        field_simp
      calc (u * v) ^ 2 / (e0 ^ 2 * (Real.log x) ^ 4) *
            ‖(∑ q ∈ Finset.Icc 1 Q,
              (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
                ramanujan512 q N)‖ ^ 2
          ≤ (u * v) ^ 2 / (e0 ^ 2 * (Real.log x) ^ 4) * (M * Real.log x) ^ 4 := h1
        _ = (u * v) ^ 2 * M ^ 4 / e0 ^ 2 := h2
    exact le_trans hfinal (le_max_right 1 _)

/-- Upper bound: the number of pairs summing to a fixed frequency is at most the
length of the short support, up to one. -/
private theorem count_upper561 (ε x : ℝ) (hx : 0 < x) (N : ℕ) :
    ((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product
        (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter
        (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) ≤ length512 ε x + 1 := by
  set Y := length512 ε x with hY
  set S := Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊ with hS
  set T := Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊ with hT
  set F := (S.product T).filter (fun p : ℕ × ℕ => p.1 + p.2 = N) with hF
  have hinj : ∀ p ∈ F, ∀ q ∈ F, p.2 = q.2 → p = q := by
    intro p hp q hq hpq
    have hpN : p.1 + p.2 = N := (Finset.mem_filter.mp hp).2
    have hqN : q.1 + q.2 = N := (Finset.mem_filter.mp hq).2
    have h12 : p.1 = q.1 := by omega
    exact Prod.ext h12 hpq
  have hcard : (F.image (fun p : ℕ × ℕ => p.2)).card = F.card :=
    Finset.card_image_of_injOn hinj
  have hsub : F.image (fun p : ℕ × ℕ => p.2) ⊆ T := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  have hle : F.card ≤ T.card := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hTcard : T.card = ⌊2 * Y⌋₊ - ⌊Y⌋₊ := by simp [hT]
  have hYpos : (0 : ℝ) < Y := by
    rw [hY]
    exact Real.rpow_pos_of_pos hx _
  have hmono : ⌊Y⌋₊ ≤ ⌊2 * Y⌋₊ := Nat.floor_le_floor (by linarith)
  have hb1 : (⌊2 * Y⌋₊ : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
  have hb2 : Y - 1 < (⌊Y⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one Y
    linarith
  calc (F.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast hle
    _ = ((⌊2 * Y⌋₊ - ⌊Y⌋₊ : ℕ) : ℝ) := by rw [hTcard]
    _ = (⌊2 * Y⌋₊ : ℝ) - (⌊Y⌋₊ : ℝ) := Nat.cast_sub hmono
    _ ≤ Y + 1 := by linarith

/-- Lower bound: all short-support points except possibly the top one pair up with a
long-support point summing to a frequency in the window. -/
private theorem count_lower561 (ε x : ℝ) (hx : 0 < x) (N : ℕ)
    (hNlo : ⌈x⌉₊ ≤ N)
    (hNhi : N ≤ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊)
    (hbig : 2 * length512 ε x + 2 ≤ x)
    (hZY : x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) + 1 ≤ length512 ε x) :
    length512 ε x - 2 ≤
      ((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product
        (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter
        (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) := by
  set Y := length512 ε x with hYdef
  set S := Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊ with hS
  set T := Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊ with hT
  set F := (S.product T).filter (fun p : ℕ × ℕ => p.1 + p.2 = N) with hF
  have hYpos : (0 : ℝ) < Y := by
    rw [hYdef]
    exact Real.rpow_pos_of_pos hx _
  have f1 : (⌊2 * Y⌋₊ : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
  have f2 : Y - 1 < (⌊Y⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one Y
    linarith
  have f3 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have f3' : (⌈x⌉₊ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNlo
  have f4 : (N : ℝ) ≤ x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by
    have h0 : (0 : ℝ) ≤ x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by
      have := Real.rpow_nonneg (le_of_lt hx) ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))
      linarith
    have hle : (N : ℝ) ≤
        (⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊ : ℝ) := by
      exact_mod_cast hNhi
    have := Nat.floor_le h0
    linarith
  have f5 : (⌊x - 2 * Y⌋₊ : ℝ) ≤ x - 2 * Y := Nat.floor_le (by linarith)
  have f6 : x - 1 < (⌊x⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one x
    linarith
  have hYlt : ⌊Y⌋₊ < ⌊2 * Y⌋₊ := by
    have h2 : 2 * Y - 1 < (⌊2 * Y⌋₊ : ℝ) := by
      have h := Nat.lt_floor_add_one (2 * Y)
      linarith
    have hYle : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
    have : (⌊Y⌋₊ : ℝ) < (⌊2 * Y⌋₊ : ℝ) := by linarith
    exact_mod_cast this
  have hmem : ∀ b ∈ T.erase ⌊2 * Y⌋₊, (N - b, b) ∈ F := by
    intro b hb
    obtain ⟨hbne, hbT⟩ := Finset.mem_erase.mp hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_Ioc.mp hbT
    have hblt : b < ⌊2 * Y⌋₊ := lt_of_le_of_ne hb2 hbne
    have hble : b ≤ ⌊2 * Y⌋₊ - 1 := by omega
    have hbR1 : (b : ℝ) ≤ (⌊2 * Y⌋₊ : ℝ) - 1 := by
      have hcast : (b : ℝ) ≤ ((⌊2 * Y⌋₊ - 1 : ℕ) : ℝ) := by exact_mod_cast hble
      have h1 : ((⌊2 * Y⌋₊ - 1 : ℕ) : ℝ) = (⌊2 * Y⌋₊ : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ ⌊2 * Y⌋₊)]
        push_cast
        ring
      rw [h1] at hcast
      exact hcast
    have hbre : (b : ℝ) ≤ 2 * Y - 1 := by linarith
    have hbY : Y ≤ (b : ℝ) := by
      have hb1' : ⌊Y⌋₊ + 1 ≤ b := hb1
      have h : (⌊Y⌋₊ : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hb1'
      linarith
    have hbN : b ≤ N := by
      have hbR : (b : ℝ) ≤ (N : ℝ) := by linarith
      exact_mod_cast hbR
    have hnsub : ((N - b : ℕ) : ℝ) = (N : ℝ) - (b : ℝ) := by
      rw [Nat.cast_sub hbN]
    have hS : N - b ∈ S := by
      refine Finset.mem_Ioc.mpr ⟨?_, ?_⟩
      · have : (⌊x - 2 * Y⌋₊ : ℝ) < ((N - b : ℕ) : ℝ) := by
          rw [hnsub]
          linarith
        exact_mod_cast this
      · have : ((N - b : ℕ) : ℝ) ≤ (⌊x⌋₊ : ℝ) := by
          rw [hnsub]
          linarith
        exact_mod_cast this
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hS, hbT⟩, ?_⟩
    omega
  have hinj : ∀ b ∈ T.erase ⌊2 * Y⌋₊, ∀ c ∈ T.erase ⌊2 * Y⌋₊,
      (N - b, b) = (N - c, c) → b = c := by
    intro b _ c _ h
    exact congrArg Prod.snd h
  have hcardT : T.card = ⌊2 * Y⌋₊ - ⌊Y⌋₊ := by simp [hT]
  have htop : ⌊2 * Y⌋₊ ∈ T := Finset.mem_Ioc.mpr ⟨hYlt, le_rfl⟩
  have hle : (T.erase ⌊2 * Y⌋₊).card ≤ F.card := by
    have himg : (T.erase ⌊2 * Y⌋₊).image (fun b => (N - b, b)) ⊆ F := by
      intro p hp
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
      exact hmem b hb
    have hc : ((T.erase ⌊2 * Y⌋₊).image (fun b => (N - b, b))).card =
        (T.erase ⌊2 * Y⌋₊).card := Finset.card_image_of_injOn hinj
    rw [← hc]
    exact Finset.card_le_card himg
  have hstep : ((T.erase ⌊2 * Y⌋₊).card : ℝ) = (⌊2 * Y⌋₊ : ℝ) - (⌊Y⌋₊ : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem htop, hcardT]
    have h1 : 1 ≤ ⌊2 * Y⌋₊ - ⌊Y⌋₊ := by omega
    rw [Nat.cast_sub h1, Nat.cast_sub (le_of_lt hYlt)]
    push_cast
    ring
  have hYle : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have f1b : 2 * Y - 1 < (⌊2 * Y⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one (2 * Y)
    linarith
  calc Y - 2 = (Y - 1) - 1 := by ring
    _ ≤ (⌊2 * Y⌋₊ : ℝ) - (⌊Y⌋₊ : ℝ) - 1 := by linarith
    _ = ((T.erase ⌊2 * Y⌋₊).card : ℝ) := hstep.symm
    _ ≤ (F.card : ℝ) := by exact_mod_cast hle

/-- LEAF. Power against logarithm threshold for the squared count deviation: on
the even frequency window the squared deviation of the exact convolution count
from the short interval length is at most one constant times the same scale as
the target, uniformly in the length, once the exponent stays below the fixed
positive threshold. This is the only arithmetic input of the split. -/
theorem leaf_endpoint_power_log_threshold561 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ A : ℝ, 0 < A → ∀ D : ℝ,
      ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
        (∑ N ∈ frequencies512 ε x,
            (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) ^ 2) ≤ C * scale512 ε A x := by
  refine ⟨1 / 10, by norm_num, ?_⟩
  intro ε hε hε' A hA D
  have he0pos : (0 : ℝ) < 11 / 20 + ε := by linarith
  have he0ge : (11 : ℝ) / 20 ≤ 11 / 20 + ε := by linarith
  have he0lt : 11 / 20 + ε < 13 / 20 := by linarith
  have hspos : (0 : ℝ) < 2 * (1 / 16 - 1 / 10 ^ 5) := by norm_num
  have hsle4 : 2 * (1 / 16 - 1 / 10 ^ 5) ≤ (1 : ℝ) / 4 := by norm_num
  have h1s : (0 : ℝ) < 1 - 2 * (1 / 16 - 1 / 10 ^ 5) := by norm_num
  have hes1 : (0 : ℝ) < (11 / 20 + ε) * (1 - 2 * (1 / 16 - 1 / 10 ^ 5)) :=
    mul_pos he0pos h1s
  have hexp : (21 : ℝ) / 20 ≤ (11 / 20 + ε) * (2 + 2 * (1 / 16 - 1 / 10 ^ 5)) := by
    have hp : (0 : ℝ) ≤ (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) :=
      le_of_lt (mul_pos he0pos hspos)
    nlinarith [he0ge]
  have hslt : (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) < 1 := by
    have hb : (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) ≤ (13 / 20) * (1 / 4) :=
      mul_le_mul he0lt.le hsle4 (le_of_lt hspos) (by norm_num)
    linarith
  -- eventual facts
  have hx1ev : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ x := Filter.eventually_ge_atTop 1
  have hrev : ∀ᶠ x : ℝ in Filter.atTop, (4 : ℝ) ≤ x ^ (7 / 20 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 20)).eventually
      (Filter.eventually_ge_atTop 4)
  have hrev2 : ∀ᶠ x : ℝ in Filter.atTop,
      (4 : ℝ) ≤ x ^ ((11 / 20 + ε) * (1 - 2 * (1 / 16 - 1 / 10 ^ 5))) :=
    (tendsto_rpow_atTop hes1).eventually (Filter.eventually_ge_atTop 4)
  have hlogev : ∀ᶠ x : ℝ in Filter.atTop, (0 : ℝ) < Real.log x := by
    have h : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) < Real.log x :=
      Real.tendsto_log_atTop.eventually (Filter.eventually_gt_atTop 1)
    exact h.mono (fun x hx => by linarith)
  have hlogAev : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ^ (A + 7) ≤ x ^ (1 / 20 : ℝ) := by
    have hA7 : (0 : ℝ) < A + 7 := by linarith
    have hiso := isLittleO_log_rpow_rpow_atTop (s := (1 / 20 : ℝ)) (A + 7) (by norm_num)
    have hb : ∀ᶠ x : ℝ in Filter.atTop,
        ‖Real.log x ^ (A + 7)‖ ≤ 1 * ‖x ^ (1 / 20 : ℝ)‖ :=
      Asymptotics.isLittleO_iff.mp hiso (c := 1) one_pos
    filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hx0 : (0 : ℝ) ≤ x := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0 _), one_mul] at hx
    exact hx
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      2 * length512 ε x + 2 ≤ x ∧
      (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) + 1 ≤ length512 ε x) ∧
      (x ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * length512 ε x ^ 2 *
        Real.log x ^ (-A - 7)) := by
    filter_upwards [hx1ev, hrev, hrev2, hlogev, hlogAev] with x hx1 hx4 hx4' hlog hp
    have hxpos : (0 : ℝ) < x := by linarith
    have hsq : length512 ε x ^ 2 = x ^ ((11 / 20 + ε) * 2) := by
      rw [show length512 ε x = x ^ (11 / 20 + ε) from rfl]
      rw [← Real.rpow_natCast (x ^ (11 / 20 + ε)) 2]
      exact (Real.rpow_mul (le_of_lt hxpos) (11 / 20 + ε) 2).symm
    refine ⟨?_, ?_, ?_⟩
    · have hYle : length512 ε x ≤ x ^ (13 / 20 : ℝ) := by
        rw [show length512 ε x = x ^ (11 / 20 + ε) from rfl]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      have hx13 : (1 : ℝ) ≤ x ^ (13 / 20 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
      have hmul : x ^ (7 / 20 : ℝ) * x ^ (13 / 20 : ℝ) = x := by
        rw [← Real.rpow_add hxpos]
        norm_num
      nlinarith
    · have hZ1 : (1 : ℝ) ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) :=
        Real.one_le_rpow hx1 (le_of_lt (mul_pos he0pos hspos))
      have hsplit : length512 ε x =
          x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
            x ^ ((11 / 20 + ε) * (1 - 2 * (1 / 16 - 1 / 10 ^ 5))) := by
        rw [show length512 ε x = x ^ (11 / 20 + ε) from rfl, ← Real.rpow_add hxpos]
        congr 1
        ring
      nlinarith
    · have hLpos : 0 < Real.log x ^ (A + 7) := Real.rpow_pos_of_pos hlog (A + 7)
      have hs1 : x * Real.log x ^ (A + 7) ≤ x * x ^ (1 / 20 : ℝ) := by nlinarith
      have hs2 : x * x ^ (1 / 20 : ℝ) = x ^ (21 / 20 : ℝ) := by
        nth_rewrite 1 [← Real.rpow_one x]
        rw [← Real.rpow_add hxpos]
        norm_num
      have hs3 : x ^ (21 / 20 : ℝ) ≤ x ^ ((11 / 20 + ε) * (2 + 2 * (1 / 16 - 1 / 10 ^ 5))) :=
        Real.rpow_le_rpow_of_exponent_le hx1 hexp
      have hs4 : x ^ ((11 / 20 + ε) * (2 + 2 * (1 / 16 - 1 / 10 ^ 5))) =
          x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * length512 ε x ^ 2 := by
        rw [hsq, ← Real.rpow_add hxpos]
        congr 1
        ring
      have hmain : x * Real.log x ^ (A + 7) ≤
          x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * length512 ε x ^ 2 := by
        calc x * Real.log x ^ (A + 7) ≤ x * x ^ (1 / 20 : ℝ) := hs1
          _ = x ^ (21 / 20 : ℝ) := hs2
          _ ≤ x ^ ((11 / 20 + ε) * (2 + 2 * (1 / 16 - 1 / 10 ^ 5))) := hs3
          _ = x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * length512 ε x ^ 2 := hs4
      have hd := (le_div_iff₀ hLpos).mpr hmain
      rw [div_eq_mul_inv] at hd
      rw [show -A - 7 = -(A + 7) by ring, Real.rpow_neg (le_of_lt hlog)]
      exact hd
  obtain ⟨C₀, hC₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max C₀ 12, ?_⟩
  intro x hx
  have hxC : C₀ ≤ x := le_trans (le_max_left _ _) hx
  have hx12 : (12 : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hbig, hZY, hxscale⟩ := hC₀ x hxC
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxpos : (0 : ℝ) < x := by linarith
  simp only [frequencies512, scale512]
  have hterm : ∀ N ∈ (Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
      (fun N => Even N),
      (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product
        (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter
        (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) ^ 2 ≤ 4 := by
    intro N hN
    obtain ⟨hIcc, _⟩ := Finset.mem_filter.mp hN
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hIcc
    have h1 := count_upper561 ε x hxpos N
    have h2 := count_lower561 ε x hxpos N hlo hhi hbig hZY
    nlinarith
  have hZx : x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) ≤ x := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 (le_of_lt hslt)
    simpa using this
  calc (∑ N ∈ (Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
        (fun N => Even N),
        (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product
          (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter
          (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) ^ 2)
      ≤ ∑ N ∈ (Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
          (fun N => Even N), (4 : ℝ) := Finset.sum_le_sum hterm
    _ = (((Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
          (fun N => Even N)).card : ℝ) * 4 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 12 * x := by
        have hcard : ((Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
            (fun N => Even N)).card ≤
            ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊ + 1 := by
          refine le_trans (Finset.card_le_card (Finset.filter_subset _ _)) ?_
          have := Nat.card_Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊
          omega
        have hfloor : (⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊ : ℝ) ≤
            x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) :=
          Nat.floor_le (by positivity)
        have hcast : ((⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊ + 1 : ℕ) : ℝ) =
            (⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊ : ℝ) + 1 := by push_cast; ring
        have : (((Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
            (fun N => Even N)).card : ℝ) ≤ 3 * x := by
          have hcc : (((Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
              (fun N => Even N)).card : ℝ) ≤
              ((⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊ + 1 : ℕ) : ℝ) := by
            exact_mod_cast hcard
          rw [hcast] at hcc
          linarith
        nlinarith
    _ ≤ 12 * (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * length512 ε x ^ 2 *
          Real.log x ^ (-A - 7)) := by nlinarith
    _ ≤ max C₀ 12 * (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * length512 ε x ^ 2 *
          Real.log x ^ (-A - 7)) := by
        have hpos : (0 : ℝ) ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) *
            length512 ε x ^ 2 * Real.log x ^ (-A - 7) := by
          refine mul_nonneg (mul_nonneg ?_ (sq_nonneg _)) ?_
          · exact Real.rpow_nonneg (le_of_lt hxpos) _
          · exact Real.rpow_nonneg (Real.log_nonneg hx1) _
        have : (12 : ℝ) ≤ max C₀ 12 := le_max_right _ _
        exact mul_le_mul_of_nonneg_right this hpos

/-- The finite endpoint replacement step, assembled from the exact count
identity, the algebraic factorization, the uniform residue envelope and the power
against logarithm threshold. -/
theorem leaf_finite_endpoint561_split :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u v : ℝ,
      ∀ A : ℝ, 0 < A → ∀ D : ℝ,
        ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
          endpointError561 ε D x u v ≤ C * scale512 ε A x := by
  obtain ⟨ε₀, hε₀, hthr⟩ := leaf_endpoint_power_log_threshold561
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hε' u v A hA D
  obtain ⟨C₁, hb₁⟩ := hthr ε hε hε' A hA D
  obtain ⟨C₂, hC₂, hb₂⟩ := leaf_endpoint_residue_envelope561 ε D u v
  refine ⟨max (max (C₂ * max C₁ 1) C₂) (max C₁ 3), ?_⟩
  intro x hx
  have hx3 : (3 : ℝ) ≤ x :=
    le_trans (le_trans (le_max_right C₁ 3) (le_max_right _ _)) hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hC₁le : C₁ ≤ max (max (C₂ * max C₁ 1) C₂) (max C₁ 3) :=
    le_trans (le_max_left C₁ 3) (le_max_right _ _)
  have hC₁x : C₁ ≤ x := le_trans hC₁le hx
  have hC₁C₂ : C₂ * C₁ ≤ max (max (C₂ * max C₁ 1) C₂) (max C₁ 3) := by
    refine le_trans (mul_le_mul_of_nonneg_left (le_max_left C₁ 1) hC₂.le) ?_
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hlog0 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hscale : 0 ≤ scale512 ε A x := by
    unfold scale512
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hx0 _) (sq_nonneg (length512 ε x)))
      (Real.rpow_nonneg hlog0 _)
  have hterm : ∀ N ∈ frequencies512 ε x,
      ‖completePrincipal561 ε D x u v N - truncatedMain512 ε D x u v N‖ ^ 2 =
        ((u * v / (Real.log x * Real.log (length512 ε x))) ^ 2 *
          ‖(∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
            (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
              ramanujan512 q N)‖ ^ 2) * (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) ^ 2 := by
    intro N _
    rw [leaf_endpoint_factorization561 ε D x u v N,
      leaf_endpoint_count_identity561 ε x N]
    have hcast :
        ((((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) : ℂ) -
          ((length512 ε x : ℝ) : ℂ)) =
        (((((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) : ℝ) : ℂ) := by
      push_cast
      ring
    have hnormA : ‖((u * v / (Real.log x * Real.log (length512 ε x)) : ℝ) : ℂ)‖ ^ 2
        = (u * v / (Real.log x * Real.log (length512 ε x))) ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hnormD : ‖(((((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) : ℝ) : ℂ)‖ ^ 2 = (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hcast, norm_mul, norm_mul, mul_pow, mul_pow, hnormA, hnormD]
  have hmain : endpointError561 ε D x u v =
      ∑ N ∈ frequencies512 ε x, ((u * v / (Real.log x * Real.log (length512 ε x))) ^ 2 *
          ‖(∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
            (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
              ramanujan512 q N)‖ ^ 2) * (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) ^ 2 := by
    unfold endpointError561
    exact Finset.sum_congr rfl hterm
  rw [hmain]
  calc ∑ N ∈ frequencies512 ε x, ((u * v / (Real.log x * Real.log (length512 ε x))) ^ 2 *
          ‖(∑ q ∈ Finset.Icc 1 ⌊Real.log x ^ (2 * D)⌋₊,
            (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
              ramanujan512 q N)‖ ^ 2) * (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) ^ 2
      ≤ ∑ N ∈ frequencies512 ε x, C₂ * (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) ^ 2 :=
        Finset.sum_le_sum (fun N _ =>
          mul_le_mul_of_nonneg_right (hb₂ x hx3 N) (sq_nonneg _))
    _ = C₂ * (∑ N ∈ frequencies512 ε x, (((((Finset.Ioc ⌊x - 2 * length512 ε x⌋₊ ⌊x⌋₊).product (Finset.Ioc ⌊length512 ε x⌋₊ ⌊2 * length512 ε x⌋₊)).filter (fun p : ℕ × ℕ => p.1 + p.2 = N)).card : ℝ) - length512 ε x) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ C₂ * (C₁ * scale512 ε A x) :=
        mul_le_mul_of_nonneg_left (hb₁ x hC₁x) hC₂.le
    _ = (C₂ * C₁) * scale512 ε A x := by ring
    _ ≤ max (max (C₂ * max C₁ 1) C₂) (max C₁ 3) * scale512 ε A x :=
        mul_le_mul_of_nonneg_right hC₁C₂ hscale

end LeanLab.BHP1997.Decomp561m
