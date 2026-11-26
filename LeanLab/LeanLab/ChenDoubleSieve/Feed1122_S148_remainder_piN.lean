import LeanLab.ChenDoubleSieve.Decomp363b

/-!
# Wu 2004 page 38, Lemma 2.3 with the main term pi of N

Source: Wu 2004, Chen's double sieve, Goldbach's conjecture and the twin prime problem,
https://arxiv.org/pdf/0705.1652, page 38, the remainder display after Lemma 2.3 on page 6.

The target `remainder_piN_small_proved` is the statement of the LEAF `remainder_piN_small` of
`Feed1122_S120_main0Pi_split`. It follows from three proved inputs:
* `Task363.remainder_log_cubic`, the Bombieri-Vinogradov bound with main term `li N / phi d`;
* `LeanLab.PNTPort.BVMax.pi_sub_liD`, the prime number theorem with a log power saving,
  the `q = 1` term of the lab's unconditional Bombieri-Vinogradov theorem;
* the elementary bound `sum_{q <= Q} 1 / phi q <= (1 + log Q) ^ 2`.
The moduli dividing the product of the primes of `Wu41.PS N 0 z` are coprime to `N`.

AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Feed1122.S148
open LeanLab.ChenDoubleSieve.Task275 LeanLab.ChenDoubleSieve.Task348
open Wu04Functional (IsLinearSieve)

section Helpers148R

open LeanLab.PNTPort.BVMax

/-! Helpers copied from `LeanLab/ChenDoubleSieve/Decomp363b.lean`, private there. -/


/-- The antitone integrand of the logarithmic integral on `[2, N]`. -/
private theorem antitone_invlog (N : ℕ) (hN : 2 ≤ N) :
    AntitoneOn (fun t : ℝ => (Real.log t)⁻¹) (Set.Icc (2:ℝ) N) := by
  intro x hx y hy hxy
  simp only
  apply inv_anti₀
  · exact Real.log_pos (by linarith [hx.1])
  · exact Real.log_le_log (by linarith [hx.1]) hxy

/-- `liD N` as a sum from two. -/
private theorem liD_eq (N : ℕ) (hN : 1 ≤ N) :
    liD (N : ℝ) = ∑ n ∈ Finset.Icc 2 N, (Real.log n)⁻¹ := by
  unfold liD liN
  rw [Nat.floor_natCast]
  have h : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [h, sum_insert (by simp)]
  simp [Real.log_one]

/-- The continuous logarithmic integral is below the discrete one. -/
private theorem li_le_liD (N : ℕ) (hN : 2 ≤ N) : Wu04.li N ≤ liD (N : ℝ) := by
  have hanti := antitone_invlog N hN
  have h1 : Wu04.li N ≤ ∑ x ∈ Finset.Ico 2 N, (Real.log x)⁻¹ := by
    simpa [Wu04.li] using
      AntitoneOn.integral_le_sum_Ico (f := fun t : ℝ => (Real.log t)⁻¹) hN hanti
  have h2 : ∑ x ∈ Finset.Ico 2 N, (Real.log x)⁻¹ ≤ ∑ x ∈ Finset.Icc 2 N, (Real.log x)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Ico_subset_Icc_self) (fun _ _ _ => by positivity)
  rw [liD_eq N (by omega)]
  linarith

/-- The discrete logarithmic integral exceeds the continuous one by at most `2 / log 2`. -/
private theorem liD_le_li (N : ℕ) (hN : 2 ≤ N) : liD (N : ℝ) ≤ Wu04.li N + 2 / Real.log 2 := by
  have hanti := antitone_invlog N hN
  have h1 : ∑ i ∈ Finset.Ico 2 N, (Real.log (i+1:ℕ))⁻¹ ≤ Wu04.li N := by
    simpa [Wu04.li] using
      AntitoneOn.sum_le_integral_Ico (f := fun t : ℝ => (Real.log t)⁻¹) hN hanti
  have hsplit : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have himg : Finset.Icc 3 N = (Finset.Ico 2 N).image (fun i => i + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico, Finset.mem_image]
    constructor
    · intro h; exact ⟨n - 1, by omega, by omega⟩
    · rintro ⟨i, h, rfl⟩; omega
  have hsum : ∑ n ∈ Finset.Icc 3 N, (Real.log n)⁻¹ =
      ∑ i ∈ Finset.Ico 2 N, (Real.log ((i+1 : ℕ) : ℝ))⁻¹ := by
    rw [himg, Finset.sum_image]
    intro i hi j hj hij
    simp only at hij
    omega
  rw [liD_eq N (by omega), hsplit, sum_insert (by simp), hsum]
  have h2 : (Real.log (2:ℕ))⁻¹ = (Real.log 2)⁻¹ := by norm_num
  have h3 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : (0:ℝ) ≤ (Real.log 2)⁻¹ := by positivity
  rw [h2, div_eq_mul_inv]
  linarith

/-- The comparison of the discrete and continuous logarithmic integrals. -/
private theorem abs_liD_sub_li (N : ℕ) (hN : 2 ≤ N) :
    |liD (N : ℝ) - Wu04.li N| ≤ 2 / Real.log 2 := by
  have h1 := li_le_liD N hN
  have h2 := liD_le_li N hN
  rw [abs_le]
  constructor <;> linarith

/-! Helpers copied from `LeanLab/BHP1997/SPLIT_leaf_finite_endpoint561.lean`, private there. -/

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

/-- `pi N` as the `q = 1` count of the lab's Bombieri-Vinogradov port. -/
private theorem primeCounting_eq_piAP (N : ℕ) :
    (Nat.primeCounting N : ℝ) = piAP (N : ℝ) 1 1 := by
  unfold piAP piN
  rw [Nat.floor_natCast]
  congr 1
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']
  congr 1
  ext n
  simp only [Nat.primesBelow, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc,
    Nat.mod_one, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h2.one_lt.le, by omega⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by omega, h3⟩

/-- The prime number theorem with a fifth log power saving, comparing `pi N` with the
continuous logarithmic integral `Wu04.li N`. -/
private theorem pi_sub_li_bound :
    ∃ B' : ℝ, 0 < B' ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N →
      1 ≤ Real.sqrt N / Real.log N ^ B' →
        |Wu04.li N - (Nat.primeCounting N : ℝ)| ≤ 2 / Real.log 2 + K * N / Real.log N ^ 5 := by
  obtain ⟨B', hB', K, hK⟩ := pi_sub_liD 5 (by norm_num)
  refine ⟨B', hB', |K|, abs_nonneg K, fun N hN hQ => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h := hK N hN2 hQ N (by positivity) le_rfl
  have hc : Real.log (N : ℝ) ^ (5 : ℝ) = Real.log (N : ℝ) ^ 5 := Real.rpow_natCast _ _
  rw [hc] at h
  have hli := abs_liD_sub_li N hN
  rw [primeCounting_eq_piAP]
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hK' : K * N / Real.log N ^ 5 ≤ |K| * N / Real.log N ^ 5 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
  calc |Wu04.li N - piAP (N : ℝ) 1 1|
      ≤ |Wu04.li N - liD (N : ℝ)| + |liD (N : ℝ) - piAP (N : ℝ) 1 1| := abs_sub_le _ _ _
    _ ≤ 2 / Real.log 2 + K * N / Real.log N ^ 5 := by
        exact add_le_add (by rwa [abs_sub_comm] at hli) (by rwa [abs_sub_comm] at h)
    _ ≤ _ := by linarith

end Helpers148R

/-- Every modulus dividing the product of the primes of `PS N 0 z` is coprime to `N`. -/
private theorem coprime_of_dvd_prod_PS (N d : ℕ) (z : ℝ)
    (hd : d ∣ ∏ p ∈ Wu41.PS N 0 z, p) : d.Coprime N := by
  have hprod : (∏ p ∈ Wu41.PS N 0 z, p).Coprime N := by
    apply Nat.Coprime.prod_left
    intro p hp
    unfold Wu41.PS at hp
    rw [Finset.mem_filter] at hp
    exact hp.2.2.2.2
  exact Nat.Coprime.coprime_dvd_left hd hprod

/-- Wu 2004 page 38, Lemma 2.3 with the main term `pi N / phi d`: the discrepancy sum over
the squarefree moduli of the sifting product up to `sqrt N / (log N) ^ B` is `o(Theta N)`. -/
theorem remainder_piN_small_proved :
    ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        ∑ d ∈ (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B⌋₊).filter
            (fun d => Squarefree d ∧ d ∣ ∏ p ∈ Wu41.PS N 0 ((N : ℝ) ^ kappa1), p),
            |(#((primeSequence N).filter (fun a => d ∣ a)) : ℝ) -
              (Nat.primeCounting N : ℝ) / (d.totient : ℝ)|
          ≤ η * Θ N := by
  intro η hη
  obtain ⟨B, hB, D, hD, N1, hN1⟩ := Task363.remainder_log_cubic
  obtain ⟨B', hB', K, hK0, hK⟩ := pi_sub_li_bound
  have htw : 0 < LeanLab.ChenExplicit.twinC := LeanLab.ChenExplicit.twinC_pos
  set c : ℝ := η * LeanLab.ChenExplicit.twinC / 2 with hc
  have hcpos : 0 < c := by positivity
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  -- eventual facts on the real line, pulled back to the naturals
  have ev1 : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ B' ≤ Real.sqrt N := by
    have h := (isLittleO_log_rpow_rpow_atTop B' (by norm_num : (0 : ℝ) < 1 / 2)).bound
      (by norm_num : (0 : ℝ) < 1)
    have h2 : ∀ᶠ x : ℝ in atTop, Real.log x ^ B' ≤ Real.sqrt x := by
      filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
      have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _),
        Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), one_mul] at hx
      rw [Real.sqrt_eq_rpow]; exact hx
    exact hcast.eventually h2
  have ev2 : ∀ᶠ N : ℕ in atTop, (D + 4 * K) / c ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp hcast).eventually (eventually_ge_atTop _)
  have ev3 : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ 4 ≤ c / (8 / Real.log 2) * (N : ℝ) := by
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h := (Real.isLittleO_pow_log_id_atTop (n := 4)).bound
      (by positivity : (0 : ℝ) < c / (8 / Real.log 2))
    have h2 : ∀ᶠ x : ℝ in atTop, Real.log x ^ 4 ≤ c / (8 / Real.log 2) * x := by
      filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
      rw [Real.norm_of_nonneg (by positivity), id, Real.norm_of_nonneg hx0] at hx
      exact hx
    exact hcast.eventually h2
  have ev4 : ∀ᶠ N : ℕ in atTop, max 3 N1 ≤ N := eventually_ge_atTop _
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (ev1.and (ev2.and (ev3.and ev4)))
  refine ⟨B, hB, N0, fun N hEven hN => ?_⟩
  obtain ⟨e1, e2, e3, e4⟩ := hN0 N hN
  have h3 : 3 ≤ N := le_of_max_le_left e4
  have hN1' : N1 ≤ N := le_of_max_le_right e4
  have hNR : (3 : ℝ) ≤ N := by exact_mod_cast h3
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog1 : 1 ≤ Real.log N := by
    have h := Real.log_three_near_10
    rw [abs_le] at h
    have : Real.log 3 ≤ Real.log N := Real.log_le_log (by norm_num) hNR
    nlinarith [h.1]
  have hlog : 0 < Real.log N := by linarith
  have hlogB' : 0 < Real.log (N : ℝ) ^ B' := Real.rpow_pos_of_pos hlog _
  have hQ' : 1 ≤ Real.sqrt N / Real.log N ^ B' := by
    rw [le_div_iff₀ hlogB', one_mul]; exact e1
  have hE := hK N (by omega) hQ'
  set E : ℝ := |Wu04.li N - (Nat.primeCounting N : ℝ)| with hEdef
  set S := (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B⌋₊).filter
    (fun d => Squarefree d ∧ d ∣ ∏ p ∈ Wu41.PS N 0 ((N : ℝ) ^ kappa1), p) with hS
  set Q : ℕ := ⌊(N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B⌋₊ with hQdef
  have hSsub : S ⊆ Task363.remainderModuli B N := by
    intro d hd
    rw [hS, Finset.mem_filter] at hd
    unfold Task363.remainderModuli Task363.sieveLevel
    rw [Finset.mem_filter]
    exact ⟨hd.1, hd.2.1, coprime_of_dvd_prod_PS N d _ hd.2.2⟩
  have hSsubI : S ⊆ Finset.Icc 1 Q := Finset.filter_subset _ _
  -- the triangle inequality, term by term
  have hterm : ∀ d ∈ S,
      |(#((primeSequence N).filter (fun a => d ∣ a)) : ℝ) -
          (Nat.primeCounting N : ℝ) / (d.totient : ℝ)| ≤
        |(#((primeSequence N).filter (fun a => d ∣ a)) : ℝ) - Wu04.li N / (d.totient : ℝ)| +
          E * (1 / (d.totient : ℝ)) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (hSsubI hd)).1
    have hφ : (0 : ℝ) < (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd1
    have heq : Wu04.li N / (d.totient : ℝ) - (Nat.primeCounting N : ℝ) / (d.totient : ℝ) =
        (Wu04.li N - (Nat.primeCounting N : ℝ)) * (1 / (d.totient : ℝ)) := by ring
    calc _ ≤ |(#((primeSequence N).filter (fun a => d ∣ a)) : ℝ) - Wu04.li N / (d.totient : ℝ)| +
          |Wu04.li N / (d.totient : ℝ) - (Nat.primeCounting N : ℝ) / (d.totient : ℝ)| :=
          abs_sub_le _ _ _
      _ = _ := by
          rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (d.totient : ℝ))]
  have hsum1 : ∑ d ∈ S, |(#((primeSequence N).filter (fun a => d ∣ a)) : ℝ) -
      Wu04.li N / (d.totient : ℝ)| ≤ Task363.rawRemainder B N :=
    Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun _ _ _ => abs_nonneg _)
  have hraw := hN1 N hEven hN1'
  have hsum2 : ∑ d ∈ S, (1 / (d.totient : ℝ)) ≤ 4 * Real.log N ^ 2 := by
    have h1 : ∑ d ∈ S, (1 / (d.totient : ℝ)) ≤ ∑ d ∈ Finset.Icc 1 Q, (1 / (d.totient : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hSsubI (fun _ _ _ => by positivity)
    have h2 := sum_inv_totient_le561 Q
    have hQle : (Q : ℝ) ≤ N := by
      rw [hQdef]
      have hlB : 1 ≤ Real.log N ^ B := Real.one_le_rpow hlog1 hB.le
      have hsq : (N : ℝ) ^ (1 / 2 : ℝ) ≤ N :=
        Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
      have hpos : 0 ≤ (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B := by positivity
      calc (⌊(N : ℝ) ^ (1 / 2 : ℝ) / (log N) ^ B⌋₊ : ℝ)
          ≤ (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B := Nat.floor_le hpos
        _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) / 1 := div_le_div_of_nonneg_left (by positivity) one_pos hlB
        _ ≤ N := by rw [div_one]; exact hsq
    have hlQ : Real.log Q ≤ Real.log N := by
      rcases Nat.eq_zero_or_pos Q with h0 | h0
      · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]; exact hlog.le
      · exact Real.log_le_log (by exact_mod_cast h0) hQle
    have hlQ0 : 0 ≤ Real.log (Q : ℝ) := Real.log_natCast_nonneg Q
    have h3 : (1 + Real.log (Q : ℝ)) ^ 2 ≤ 4 * Real.log N ^ 2 := by nlinarith
    linarith
  have hE0 : 0 ≤ E := abs_nonneg _
  have hmain : ∑ d ∈ S, |(#((primeSequence N).filter (fun a => d ∣ a)) : ℝ) -
      (Nat.primeCounting N : ℝ) / (d.totient : ℝ)| ≤
      D * (N : ℝ) / Real.log N ^ 3 + E * (4 * Real.log N ^ 2) := by
    calc _ ≤ ∑ d ∈ S, (|(#((primeSequence N).filter (fun a => d ∣ a)) : ℝ) -
            Wu04.li N / (d.totient : ℝ)| + E * (1 / (d.totient : ℝ))) := Finset.sum_le_sum hterm
      _ = ∑ d ∈ S, |(#((primeSequence N).filter (fun a => d ∣ a)) : ℝ) -
            Wu04.li N / (d.totient : ℝ)| + E * ∑ d ∈ S, (1 / (d.totient : ℝ)) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := add_le_add (hsum1.trans hraw) (mul_le_mul_of_nonneg_left hsum2 hE0)
  refine hmain.trans ?_
  -- now the arithmetic of the error terms
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL2 : 0 < Real.log N ^ 2 := by positivity
  have hL3 : 0 < Real.log N ^ 3 := by positivity
  have hL5 : 0 < Real.log N ^ 5 := by positivity
  have hEb : E * (4 * Real.log N ^ 2) ≤
      (8 / Real.log 2) * Real.log N ^ 2 + 4 * K * N / Real.log N ^ 3 := by
    have := mul_le_mul_of_nonneg_right hE (by positivity : (0 : ℝ) ≤ 4 * Real.log N ^ 2)
    have h5 : K * N / Real.log N ^ 5 * (4 * Real.log N ^ 2) = 4 * K * N / Real.log N ^ 3 := by
      rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]; ring
    have h6 : 2 / Real.log 2 * (4 * Real.log N ^ 2) = (8 / Real.log 2) * Real.log N ^ 2 := by ring
    nlinarith [this, h5, h6]
  -- the term with `N / log N ^ 3`
  have hA : (D + 4 * K) * N / Real.log N ^ 3 ≤ c * N / Real.log N ^ 2 := by
    rw [div_le_div_iff₀ hL3 hL2]
    have hc' : D + 4 * K ≤ c * Real.log N := by
      have := (div_le_iff₀ hcpos).mp e2; linarith
    have hN0' : (0 : ℝ) ≤ N * Real.log N ^ 2 := by positivity
    calc (D + 4 * K) * N * Real.log N ^ 2 = (D + 4 * K) * (N * Real.log N ^ 2) := by ring
      _ ≤ (c * Real.log N) * (N * Real.log N ^ 2) := mul_le_mul_of_nonneg_right hc' hN0'
      _ = c * N * Real.log N ^ 3 := by ring
  -- the term with `log N ^ 2`
  have hB2 : (8 / Real.log 2) * Real.log N ^ 2 ≤ c * N / Real.log N ^ 2 := by
    rw [le_div_iff₀ hL2]
    have h8 : 0 < 8 / Real.log 2 := by positivity
    have := mul_le_mul_of_nonneg_left e3 h8.le
    have h9 : 8 / Real.log 2 * (c / (8 / Real.log 2) * N) = c * N := by field_simp
    nlinarith [this, h9]
  -- `Θ N` from below
  have hTheta : 2 * c * N / Real.log N ^ 2 ≤ η * Θ N := by
    unfold Θ CN
    have hof := oddFactor_one_le N
    have h1 : LeanLab.ChenExplicit.twinC ≤ oddFactor N * LeanLab.ChenExplicit.twinC := by
      nlinarith
    have key : 2 * c * N / Real.log N ^ 2 =
        η * (LeanLab.ChenExplicit.twinC * N / Real.log N ^ 2) := by rw [hc]; ring
    rw [key]
    apply mul_le_mul_of_nonneg_left _ hη.le
    apply div_le_div_of_nonneg_right _ hL2.le
    exact mul_le_mul_of_nonneg_right h1 hNpos.le
  have hsplit : D * (N : ℝ) / Real.log N ^ 3 + 4 * K * N / Real.log N ^ 3 =
      (D + 4 * K) * N / Real.log N ^ 3 := by ring
  have hsplit2 : c * N / Real.log N ^ 2 + c * N / Real.log N ^ 2 =
      2 * c * N / Real.log N ^ 2 := by ring
  linarith [hEb, hA, hB2, hTheta, hsplit, hsplit2]

end LeanLab.ChenDoubleSieve.Feed1122.S148
