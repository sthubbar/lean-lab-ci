/- AI wrote this Lean code for CODEX task169.
Theorem 6, journal pp. 1231 to 1234. Goldbach is open. -/
import LeanLab.BS2022GRH.DecompC169a

namespace LeanLab.BS2022GRH.DecompC169b
open Real Finset Classical ChenThresholdGRH DecompC169a
noncomputable section

/-- The primes q in the sum of Theorem 6, p. 1231. -/
def qRange (n : ℕ) : Finset ℕ := (U7153.Qset n).filter (fun q => ¬ q ∣ n)

/-- The cardinality of A_q, journal p. 1232. -/
def aqCard (n q : ℕ) : ℝ := (((U7153.Aset n).filter (fun a => q ∣ a)).card : ℝ)

/-- The quotient level D_q, p. 1232 display 22. -/
def quotientLevel (n q : ℕ) (α : ℝ) : ℝ := (n : ℝ) ^ (1 / 2 - α) / q

/-- The sieve parameter s_q, p. 1232 display 22. -/
def quotientParameter (n q : ℕ) (α : ℝ) : ℝ :=
  log (quotientLevel n q α) / log (U7153.zz n)

/-- The upper sieve coefficient at s_q, p. 1232 display 22. -/
def upperCoefficient (n q : ℕ) (α ε C₁ : ℝ) : ℝ :=
  2 * exp eulerMascheroniConstant / quotientParameter n q α +
    ε * C₁ * exp 2 * hS (quotientParameter n q α)

/-- The error r_q at d, p. 1232 display 22. -/
def quotientResidue (n q d : ℕ) : ℝ :=
  aqCard n (q * d) - aqCard n q / (d.totient : ℝ)

/-- The squarefree divisors below QD_q, p. 1232 display 22. -/
def quotientDivisors (n q : ℕ) (α u : ℝ) : Finset ℕ :=
  ((primesBelow n (U7153.zz n)).powerset.image (fun T => ∏ p ∈ T, p)).filter
    (fun d => (d : ℝ) < smallProduct n u * quotientLevel n q α)

/-- The error sum R_q, p. 1232 display 22. -/
def quotientRemainder (n q : ℕ) (α u : ℝ) : ℝ :=
  ∑ d ∈ quotientDivisors n q α u, |quotientResidue n q d|

/-- The total error in display 23, p. 1232. -/
def totalRemainder (n : ℕ) (α u : ℝ) : ℝ :=
  ∑ q ∈ qRange n, quotientRemainder n q α u

/-- The weighted cardinality sum in display 23 before bounding V, p. 1232. -/
def mainSum (n : ℕ) (α ε C₁ : ℝ) : ℝ :=
  ∑ q ∈ qRange n, upperCoefficient n q α ε C₁ * density n * aqCard n q

private lemma qs_exp10_gt : (22024 : ℝ) < exp 10 := by
  have h := Real.exp_one_gt_d9
  have e : exp (10:ℝ) = exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have h1 : (2.7182818283:ℝ) ^ 10 ≤ exp 1 ^ 10 := pow_le_pow_left₀ (by norm_num) h.le 10
  have h2 : (22024:ℝ) ≤ 2.7182818283 ^ 10 := by norm_num
  linarith

private lemma qs_exp2753_gt_1e8 : (1e8:ℝ) < exp 2753 := by
  have h := Real.exp_one_gt_d9
  have e : exp (20:ℝ) = exp 1 ^ 20 := by rw [← Real.exp_nat_mul]; norm_num
  have h20 : (1e8:ℝ) ≤ exp 1 ^ 20 := by
    have h1 : (1e8:ℝ) ≤ 2.7182818283 ^ 20 := by norm_num
    have h2 : 2.7182818283 ^ 20 ≤ exp 1 ^ 20 := pow_le_pow_left₀ (by norm_num) h.le 20
    linarith
  have h20' : (1e8:ℝ) ≤ exp 20 := by rw [e]; exact h20
  have h1 : exp 20 < exp 2753 := exp_lt_exp.2 (by norm_num)
  linarith

private lemma qs_exp2753_gt_2 : (2:ℝ) < exp 2753 := by
  have h := Real.exp_one_gt_d9
  have h1 : exp 1 ≤ exp 2753 := exp_le_exp.2 (by norm_num)
  linarith

private lemma qs_one_le_prod_real {s : Finset ℕ} {f : ℕ → ℝ} (hf : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have h1 := hf a (Finset.mem_insert_self a s)
      have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      calc 1 = 1 * 1 := (one_mul 1).symm
        _ ≤ f a * ∏ i ∈ s, f i := mul_le_mul h1 h2 (by norm_num) (by linarith)

private lemma qs_prod_le_prod_of_subset_real {s t : Finset ℕ} {f : ℕ → ℝ} (h : s ⊆ t) (hf : ∀ i ∈ t, 1 ≤ f i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  have h1 := Finset.prod_sdiff (f := f) h
  have h2 : 1 ≤ ∏ i ∈ t \ s, f i := qs_one_le_prod_real (fun i hi => hf i (Finset.mem_sdiff.1 hi).1)
  have h3 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => by linarith [hf i (h hi)])
  rw [← h1]
  calc ∏ i ∈ s, f i = 1 * ∏ i ∈ s, f i := (one_mul _).symm
    _ ≤ (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i := mul_le_mul_of_nonneg_right h2 h3

private lemma qs_Pz_eq (n : ℕ) :
    @Finset.filter ℕ (fun p => p ∈ ({p : ℕ | p.Prime ∧ ¬ p ∣ n} : Set ℕ) ∧ (p:ℝ) < U7153.zz n)
      (fun p => @instDecidableAnd _ _ (Classical.propDecidable _) (by infer_instance)) (range ⌈U7153.zz n⌉₊)
      = primesBelow n (U7153.zz n) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, primesBelow, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, ⟨h2, h3⟩, h4⟩; exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, ⟨h2, h3⟩, h4⟩

private lemma qs_hpred_equiv (n : ℕ) (x : ℕ) :
    (∀ p ∈ primesBelow n (U7153.zz n), ¬ p ∣ x) ↔ U7153.NoSmallP n (U7153.zz n) x := by
  constructor
  · intro h r hr hrx hrn
    refine h r ?_
    simp only [primesBelow, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, hr, hrn, hrx⟩
    have hc := Nat.le_ceil (U7153.zz n)
    have h2 : (r:ℝ) < ⌈U7153.zz n⌉₊ := by linarith
    exact_mod_cast h2
  · intro h p hp
    simp only [primesBelow, Finset.mem_filter] at hp
    obtain ⟨-, hpr, hnot, hlt⟩ := hp
    exact h p hpr hlt hnot

private lemma qs_SAq_eq_sum (n q : ℕ) :
    (U7153.SAq n q : ℝ) = ∑ x ∈ (U7153.Aset n).filter (fun x => ∀ p ∈ primesBelow n (U7153.zz n), ¬ p ∣ x),
      (if x ∈ U7153.Aset n ∧ q ∣ x then (1:ℝ) else 0) := by
  have hF : (U7153.Aset n).filter (fun x => ∀ p ∈ primesBelow n (U7153.zz n), ¬ p ∣ x)
      = (U7153.Aset n).filter (U7153.NoSmallP n (U7153.zz n)) :=
    Finset.filter_congr fun x _ => qs_hpred_equiv n x
  rw [hF]
  have hsum : ∑ x ∈ (U7153.Aset n).filter (U7153.NoSmallP n (U7153.zz n)),
      (if x ∈ U7153.Aset n ∧ q ∣ x then (1:ℝ) else 0)
      = ∑ x ∈ (U7153.Aset n).filter (U7153.NoSmallP n (U7153.zz n)), (if q ∣ x then (1:ℝ) else 0) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxA : x ∈ U7153.Aset n := (Finset.mem_filter.1 hx).1
    by_cases h : q ∣ x <;> simp [h, hxA]
  rw [hsum, Finset.sum_boole]
  unfold U7153.SAq
  rw [Finset.filter_filter]
  congr 1
  exact congrArg Finset.card (Finset.filter_congr (fun x _ => and_comm (a := q ∣ x) (b := U7153.NoSmallP n (U7153.zz n) x)))

private lemma qs_aqCard_eq_sum (n q : ℕ) :
    aqCard n q = ∑ x ∈ U7153.Aset n, (if x ∈ U7153.Aset n ∧ q ∣ x then (1:ℝ) else 0) := by
  have h : ∑ x ∈ U7153.Aset n, (if x ∈ U7153.Aset n ∧ q ∣ x then (1:ℝ) else 0)
      = ∑ x ∈ U7153.Aset n, (if q ∣ x then (1:ℝ) else 0) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    by_cases h : q ∣ x <;> simp [h, hx]
  rw [h, Finset.sum_boole]
  rfl

private lemma qs_density_eq (n : ℕ) : density n = ∏ p ∈ primesBelow n (U7153.zz n), (1 - 1 / ((p:ℝ) - 1)) := rfl

private lemma qs_X_eq (n q : ℕ) :
    (∑ x ∈ U7153.Aset n, (if x ∈ U7153.Aset n ∧ q ∣ x then (1:ℝ) else 0) *
      ∏ p ∈ primesBelow n (U7153.zz n), (1 - 1 / ((p:ℝ) - 1)))
      = density n * aqCard n q := by
  rw [← Finset.sum_mul, qs_aqCard_eq_sum, ← qs_density_eq]
  ring

private lemma qs_totient_prod_eq (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime) :
    ((∏ p ∈ T, p).totient : ℝ) = ∏ p ∈ (∏ p ∈ T, p).primeFactors, ((p:ℝ) - 1) := by
  have hpf : (∏ p ∈ T, p).primeFactors = T := Nat.primeFactors_prod hT
  have hd0 : (∏ p ∈ T, p) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.2
    intro p hp
    exact (hT p hp).ne_zero
  rw [Nat.totient_eq_div_primeFactors_mul, hpf, Nat.div_self (Nat.pos_of_ne_zero hd0), one_mul]
  rw [Nat.cast_prod]
  exact Finset.prod_congr rfl fun p hp => by rw [Nat.cast_sub (hT p hp).one_le]; ring

private lemma qs_coprime_q_prod {n : ℕ} {q : ℕ} (hqprime : q.Prime) (T : Finset ℕ)
    (hT : T ⊆ primesBelow n (U7153.zz n)) (hzq : U7153.zz n ≤ (q:ℝ)) :
    Nat.Coprime q (∏ p ∈ T, p) := by
  rw [Nat.Prime.coprime_iff_not_dvd hqprime]
  intro hdvd
  obtain ⟨p, hpT, hqp⟩ := (Prime.dvd_finsetProd_iff hqprime.prime (fun x => x)).1 hdvd
  have hpP : p ∈ primesBelow n (U7153.zz n) := hT hpT
  simp only [primesBelow, Finset.mem_filter] at hpP
  obtain ⟨-, hpprime, -, hplt⟩ := hpP
  have h_eq : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hpprime).1 hqp
  rw [← h_eq] at hplt
  linarith

private lemma qs_res_eq {n q : ℕ} (α u : ℝ) (hqprime : q.Prime) (hzq : U7153.zz n ≤ (q:ℝ))
    (T : Finset ℕ) (hT : T ∈ (primesBelow n (U7153.zz n)).powerset) :
    quotientResidue n q (∏ p ∈ T, p)
      = (∑ x ∈ (U7153.Aset n).filter (fun x => (∏ p ∈ T, p) ∣ x), (if x ∈ U7153.Aset n ∧ q ∣ x then (1:ℝ) else 0))
        - ∑ x ∈ U7153.Aset n, (if x ∈ U7153.Aset n ∧ q ∣ x then (1:ℝ) else 0) *
            ∏ p ∈ (∏ p ∈ T, p).primeFactors, (1 / ((p:ℝ) - 1)) := by
  have hTsub : T ⊆ primesBelow n (U7153.zz n) := Finset.mem_powerset.1 hT
  have hTprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    have := hTsub hp
    simp only [primesBelow, Finset.mem_filter] at this
    exact this.2.1
  have hcop : Nat.Coprime q (∏ p ∈ T, p) := qs_coprime_q_prod hqprime T hTsub hzq
  set d := ∏ p ∈ T, p with hd
  have hA : ∑ x ∈ (U7153.Aset n).filter (fun x => d ∣ x), (if x ∈ U7153.Aset n ∧ q ∣ x then (1:ℝ) else 0)
      = aqCard n (q * d) := by
    have h1 : ∑ x ∈ (U7153.Aset n).filter (fun x => d ∣ x), (if x ∈ U7153.Aset n ∧ q ∣ x then (1:ℝ) else 0)
        = ∑ x ∈ (U7153.Aset n).filter (fun x => d ∣ x), (if q ∣ x then (1:ℝ) else 0) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hxA : x ∈ U7153.Aset n := (Finset.mem_filter.1 hx).1
      by_cases h : q ∣ x <;> simp [h, hxA]
    rw [h1, Finset.sum_boole, Finset.filter_filter]
    have hfilt : (U7153.Aset n).filter (fun x => d ∣ x ∧ q ∣ x)
        = (U7153.Aset n).filter (fun x => q * d ∣ x) := by
      refine Finset.filter_congr fun x _ => ?_
      constructor
      · rintro ⟨hdx, hqx⟩
        exact hcop.mul_dvd_of_dvd_of_dvd hqx hdx
      · intro h
        exact ⟨dvd_trans (dvd_mul_left d q) h, dvd_trans (dvd_mul_right q d) h⟩
    rw [hfilt]
    rfl
  have htot : (d.totient : ℝ) = ∏ p ∈ d.primeFactors, ((p:ℝ) - 1) := qs_totient_prod_eq T hTprime
  have hB : ∑ x ∈ U7153.Aset n, (if x ∈ U7153.Aset n ∧ q ∣ x then (1:ℝ) else 0) *
      ∏ p ∈ d.primeFactors, (1 / ((p:ℝ) - 1)) = aqCard n q / (d.totient : ℝ) := by
    rw [← Finset.sum_mul, ← qs_aqCard_eq_sum]
    simp only [one_div]
    rw [Finset.prod_inv_distrib, ← htot, div_eq_mul_inv]
  unfold quotientResidue
  rw [hA, hB]

private lemma qs_remainder_eq {n q : ℕ} (α u : ℝ) (hqprime : q.Prime) (hzq : U7153.zz n ≤ (q:ℝ)) :
    quotientRemainder n q α u
      = ∑ T ∈ (primesBelow n (U7153.zz n)).powerset.filter
          (fun T => ((∏ p ∈ T, p : ℕ) : ℝ) < (∏ p ∈ primesBelow n u, p : ℕ) * quotientLevel n q α),
        |(∑ x ∈ (U7153.Aset n).filter (fun x => (∏ p ∈ T, p) ∣ x), (if x ∈ U7153.Aset n ∧ q ∣ x then (1:ℝ) else 0))
          - ∑ x ∈ U7153.Aset n, (if x ∈ U7153.Aset n ∧ q ∣ x then (1:ℝ) else 0) *
              ∏ p ∈ (∏ p ∈ T, p).primeFactors, (1 / ((p:ℝ) - 1))| := by
  unfold quotientRemainder quotientDivisors
  rw [Finset.sum_filter]
  rw [Finset.sum_image (fun T hT T' hT' h => by
    have h1 := Nat.primeFactors_prod (fun p hp => by
      have := Finset.mem_powerset.1 hT hp
      simp only [primesBelow, Finset.mem_filter] at this
      exact this.2.1)
    have h2 := Nat.primeFactors_prod (fun p hp => by
      have := Finset.mem_powerset.1 hT' hp
      simp only [primesBelow, Finset.mem_filter] at this
      exact this.2.1)
    rw [← h1, ← h2, h])]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [qs_res_eq α u hqprime hzq T (Finset.mem_filter.1 hT).1]

/-- LEAF. Apply the upper linear sieve separately to A_q, p. 1232 display 22.
Use the same V and Q as in Theorem 5. Non-strict inequality suffices here.
The source range of Lemma 7 remains a review obligation on the full sealed domain. -/
theorem quotient_sieve (α A u ε C₁ C₂ X₂ : ℝ) (n q : ℕ)
    (hG : GRH) (hT : LinearSieveT4 ε C₁ C₂) (hL : Lemma7J)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (heps : epsJ u ≤ ε)
    (he0 : 0 < ε) (he1 : ε < 1 / 63) (hα : 0 < α) (hα1 : α < 1 / 24)
    (hA : 0 < A) (hc : Cond19 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) (hq : q ∈ qRange n) :
    (U7153.SAq n q : ℝ) ≤
      upperCoefficient n q α ε C₁ * density n * aqCard n q +
        quotientRemainder n q α u := by
  obtain ⟨hqQ, hqn⟩ := Finset.mem_filter.1 hq
  unfold U7153.Qset at hqQ
  obtain ⟨-, hqprime, hzq, hqy⟩ := Finset.mem_filter.1 hqQ
  unfold U7153.yy at hqy
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith [exp_pos (exp 10), hX, hn]
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by
    have h1 : (1:ℝ) < exp (exp 10) := Real.one_lt_exp_iff.2 (exp_pos 10)
    linarith
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hqprime.pos
  have h2n : 2 ∣ n := hev.two_dvd
  have hzexp : exp 2753 < U7153.zz n := by
    have h1 : (exp (exp 10)) ^ (1/8:ℝ) ≤ (n:ℝ) ^ (1/8:ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have h2 : (exp (exp 10)) ^ (1/8:ℝ) = exp (exp 10 / 8) := by
      rw [Real.rpow_def_of_pos (exp_pos _), log_exp]
      ring_nf
    have h3 : exp 2753 < exp (exp 10 / 8) := by
      refine exp_lt_exp.2 ?_
      have := qs_exp10_gt
      linarith
    calc exp 2753 < exp (exp 10 / 8) := h3
      _ = (exp (exp 10)) ^ (1/8:ℝ) := h2.symm
      _ ≤ (n:ℝ) ^ (1/8:ℝ) := h1
      _ = U7153.zz n := rfl
  have hz2 : (2:ℝ) ≤ U7153.zz n := by linarith [qs_exp2753_gt_2, hzexp]
  have hz : (0:ℝ) < U7153.zz n := by linarith
  -- z ≤ D
  have hzD : U7153.zz n ≤ quotientLevel n q α := by
    have h1 : (n:ℝ) ^ (1/2 - α) / (n:ℝ) ^ (1/3:ℝ) ≤ (n:ℝ) ^ (1/2 - α) / (q:ℝ) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hn0.le _) hq0 (le_of_lt hqy)
    have h2 : (n:ℝ) ^ (1/2 - α) / (n:ℝ) ^ (1/3:ℝ) = (n:ℝ) ^ (1/6 - α) := by
      rw [← Real.rpow_sub hn0]
      congr 1
      ring
    have h3 : (n:ℝ) ^ (1/8:ℝ) ≤ (n:ℝ) ^ (1/6 - α) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith : (1/8:ℝ) ≤ 1/6 - α)
    calc U7153.zz n = (n:ℝ)^(1/8:ℝ) := rfl
      _ ≤ (n:ℝ)^(1/6 - α) := h3
      _ = (n:ℝ)^(1/2-α) / (n:ℝ)^(1/3:ℝ) := h2.symm
      _ ≤ (n:ℝ)^(1/2-α) / (q:ℝ) := h1
      _ = quotientLevel n q α := rfl
  -- s ≤ 3
  have hs3 : quotientParameter n q α ≤ 3 := by
    have hlogz : 0 < log (U7153.zz n) := Real.log_pos (by linarith)
    have hD0 : 0 < quotientLevel n q α := by
      unfold quotientLevel
      exact div_pos (Real.rpow_pos_of_pos hn0 _) hq0
    unfold quotientParameter
    rw [div_le_iff₀ hlogz]
    have h3log : 3 * log (U7153.zz n) = log ((U7153.zz n) ^ (3:ℕ)) := by
      rw [Real.log_pow]; norm_num
    rw [h3log]
    refine log_le_log hD0 ?_
    have hzz3 : (U7153.zz n)^(3:ℕ) = (n:ℝ)^(3/8:ℝ) := by
      have hz8 : (U7153.zz n : ℝ) = (n:ℝ)^(1/8:ℝ) := rfl
      rw [hz8, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      congr 1
      ring
    rw [hzz3]
    have hD1 : quotientLevel n q α ≤ (n:ℝ)^(3/8 - α) := by
      have h1 : (n:ℝ)^(1/2-α) / (q:ℝ) ≤ (n:ℝ)^(1/2-α) / U7153.zz n :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hn0.le _) hz hzq
      have h2 : (n:ℝ)^(1/2-α) / U7153.zz n = (n:ℝ)^(3/8 - α) := by
        have hz8 : (U7153.zz n : ℝ) = (n:ℝ)^(1/8:ℝ) := rfl
        rw [hz8, ← Real.rpow_sub hn0]
        congr 1; ring
      unfold quotientLevel
      linarith
    have hD2 : (n:ℝ)^(3/8 - α) ≤ (n:ℝ)^(3/8:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    linarith
  -- product condition (hypothesis 9 of hT)
  have hprod : ∀ (x : ℕ) (u' : ℝ), 1 < u' → u' < U7153.zz n →
      ∏ p ∈ @Finset.filter ℕ (fun p => p ∈ ({p : ℕ | p.Prime ∧ ¬ p ∣ n} : Set ℕ) ∧ p ∉ primesBelow n u ∧ u' ≤ (p:ℝ) ∧ (p:ℝ) < U7153.zz n)
        (fun p => @instDecidableAnd _ _ (Classical.propDecidable _) (by infer_instance)) (range ⌈U7153.zz n⌉₊),
        (1 - 1 / ((p:ℝ) - 1))⁻¹ ≤ (1 + ε) * (log (U7153.zz n) / log u') := by
    intro x u' hu'1 hu'z
    set z := U7153.zz n with hzdef
    set w := max u' u with hwdef
    set F := @Finset.filter ℕ (fun p => p ∈ ({p : ℕ | p.Prime ∧ ¬ p ∣ n} : Set ℕ) ∧ p ∉ primesBelow n u ∧ u' ≤ (p:ℝ) ∧ (p:ℝ) < z)
      (fun p => @instDecidableAnd _ _ (Classical.propDecidable _) (by infer_instance)) (range ⌈z⌉₊) with hFdef
    set bandL := (range ⌈z⌉₊).filter (fun p : ℕ => p.Prime ∧ w ≤ (p:ℝ) ∧ (p:ℝ) < z) with hbandLdef
    have huw : u ≤ w := le_max_right u' u
    have hu'w : u' ≤ w := le_max_left u' u
    have hwz : w < z := by
      refine max_lt hu'z ?_
      have hu8 : u ≤ 1e8 := hc.2.2.2
      linarith [qs_exp2753_gt_1e8, hzexp]
    obtain ⟨hband, -⟩ := hL z u w hzexp hc.2.2.1 huw hwz
    rw [← hbandLdef] at hband
    have hsub : F ⊆ bandL := by
      intro p hp
      simp only [hFdef, hbandLdef, Finset.mem_filter, Finset.mem_range] at hp ⊢
      obtain ⟨hprange, hpP, hpQ, hu'p, hpz⟩ := hp
      have hpu : u ≤ (p:ℝ) := by
        by_contra hcon
        push_neg at hcon
        apply hpQ
        simp only [primesBelow, Finset.mem_filter, Finset.mem_range]
        refine ⟨?_, hpP.1, hpP.2, hcon⟩
        have hceil : u ≤ ⌈u⌉₊ := Nat.le_ceil u
        have h2 : (p:ℝ) < ⌈u⌉₊ := by linarith
        exact_mod_cast h2
      exact ⟨hprange, hpP.1, max_le hu'p hpu, hpz⟩
    have hone : ∀ p : ℕ, p ∈ bandL → 1 ≤ (1 - 1 / ((p:ℝ) - 1))⁻¹ := by
      intro p hp
      simp only [hbandLdef, Finset.mem_filter] at hp
      obtain ⟨-, -, hpw, -⟩ := hp
      have hp400 : (400:ℝ) ≤ w := by linarith [hc.2.2.1, huw]
      have hp3 : (3:ℝ) ≤ (p:ℝ) := by linarith
      have h1 : 0 < 1 - 1 / ((p:ℝ) - 1) := by
        have hden : (0:ℝ) < (p:ℝ) - 1 := by linarith
        have hlt : 1 / ((p:ℝ) - 1) < 1 := by
          rw [div_lt_one hden]; linarith
        have hnn : 0 ≤ 1 / ((p:ℝ) - 1) := div_nonneg (by norm_num) hden.le
        linarith
      have h2 : 1 - 1 / ((p:ℝ) - 1) ≤ 1 := by
        have hnn : 0 ≤ 1 / ((p:ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
        linarith
      exact (one_le_inv₀ h1).2 h2
    have hple := qs_prod_le_prod_of_subset_real hsub hone
    have hlogu' : 0 < log u' := Real.log_pos hu'1
    have hlogz : 0 < log z := Real.log_pos (by linarith)
    have hlogw0 : 0 < log w := Real.log_pos (by linarith)
    have hlogw : log u' ≤ log w := log_le_log (by linarith) hu'w
    have hdiv : log z / log w ≤ log z / log u' :=
      div_le_div_of_nonneg_left hlogz.le hlogu' hlogw
    have hfinal : ∏ p ∈ F, (1 - 1 / ((p:ℝ) - 1))⁻¹ < (1 + ε) * (log z / log u') := by
      calc ∏ p ∈ F, (1 - 1 / ((p:ℝ) - 1))⁻¹
          ≤ ∏ p ∈ bandL, (1 - 1 / ((p:ℝ) - 1))⁻¹ := hple
        _ < (1 + epsJ u) * (log z / log w) := hband
        _ ≤ (1 + ε) * (log z / log u') := by
            apply mul_le_mul (by linarith) hdiv (div_nonneg hlogz.le hlogw0.le) (by linarith)
    exact hfinal.le
  -- apply hT
  have ha_nn : ∀ x : ℕ, 0 ≤ (if x ∈ U7153.Aset n ∧ q ∣ x then (1:ℝ) else 0) := by
    intro x; split_ifs <;> norm_num
  have ha_supp : ∀ x : ℕ, x ∉ U7153.Aset n → (if x ∈ U7153.Aset n ∧ q ∣ x then (1:ℝ) else 0) = 0 := by
    intro x hx; simp [hx]
  have hPprime : ∀ p ∈ ({p : ℕ | p.Prime ∧ ¬ p ∣ n} : Set ℕ), p.Prime := by
    intro p hp; exact hp.1
  have hQP : (↑(primesBelow n u) : Set ℕ) ⊆ {p : ℕ | p.Prime ∧ ¬ p ∣ n} := by
    intro p hp
    have hp' := Finset.mem_coe.1 hp
    simp only [primesBelow, Finset.mem_filter] at hp'
    exact ⟨hp'.2.1, hp'.2.2.1⟩
  have hg : ∀ x : ℕ, ∀ p : ℕ, p ∈ ({p : ℕ | p.Prime ∧ ¬ p ∣ n} : Set ℕ) → 0 ≤ 1 / ((p:ℝ) - 1) ∧ 1 / ((p:ℝ) - 1) < 1 := by
    intro x p hp
    have hpAnd : p.Prime ∧ ¬ p ∣ n := hp
    have hp3 : 3 ≤ p := by
      by_contra hcon
      push_neg at hcon
      have h2le : 2 ≤ p := hpAnd.1.two_le
      have h22 : p = 2 := by omega
      rw [h22] at hpAnd
      exact hpAnd.2 h2n
    have hden : (2:ℝ) ≤ (p:ℝ) - 1 := by
      have : (3:ℝ) ≤ p := by exact_mod_cast hp3
      linarith
    constructor
    · positivity
    · rw [div_lt_one (by linarith : (0:ℝ) < (p:ℝ) - 1)]
      linarith
  have key := hT (U7153.Aset n) (fun x => if x ∈ U7153.Aset n ∧ q ∣ x then (1:ℝ) else 0)
    ({p : ℕ | p.Prime ∧ ¬ p ∣ n} : Set ℕ) (primesBelow n u) (fun _ p => 1 / ((p:ℝ) - 1)) (U7153.zz n) (quotientLevel n q α)
    ha_nn ha_supp hPprime hQP hg he0 he1 hz2 hprod
  obtain ⟨hup, -⟩ := key
  have hmain := hup hzD hs3
  simp only [] at hmain
  rw [qs_Pz_eq n] at hmain
  rw [← qs_SAq_eq_sum n q] at hmain
  rw [qs_X_eq n q] at hmain
  rw [← qs_remainder_eq α u hqprime hzq] at hmain
  rw [mul_assoc]
  exact hmain


/-- LEAF. Sum the main terms using display 24 and partial summation, pp. 1233 and 1234.
Use Lemma 11 for A, Lemma 13 for r at q, and the reciprocal prime estimates on p. 1234.
The l1 term contains the integral and endpoint correction. The l3 term contains r at q. -/
theorem main_sum_bound (α A u ε C₁ X₂ : ℝ) (n : ℕ)
    (hG : GRH) (h3 : Lemma3J) (hC₁ : 0 ≤ C₁) (he0 : 0 < ε)
    (hα : 0 < α) (hα1 : α < 1 / 24) (hA : 0 < A)
    (hc : Cond19 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    mainSum n α ε C₁ ≤
      8 * (UNfull n * n / log n ^ 2) * l1J α ε C₁ X₂ +
      8 * (UNfull n * n / log n ^ 2) * (l3J α ε C₁ X₂ / log n ^ (A - 1)) := by
  sorry

/-- LEAF. Sum R_q using the injective qd indexing, p. 1233 after display 23.
Use Lemmas 5 and 13 and the identity for r_q to obtain the l2 contribution.
The absolute value estimate is independent of the sign chosen in the residue identity. -/
theorem total_remainder_bound (α A u X₂ : ℝ) (n : ℕ)
    (hG : GRH) (h3 : Lemma3J) (hα : 0 < α) (hα1 : α < 1 / 24)
    (hA : 0 < A) (hc : Cond19 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    totalRemainder n α u ≤
      8 * (UNfull n * n / log n ^ 2) * (l2J X₂ / log n ^ (A - 3)) := by
  sorry

/-- The exact existing Thm6J from the three named leaves. All analytic leaves stay OPEN. -/
theorem thm6J_of_inputs (h3 : Lemma3J) (h7 : Lemma7J) : Thm6J := by
  intro α A u ε C₁ C₂ X₂ n hG hT hC₁ hC₂ heps he0 he1 hα hα1 hA hc hX hn hev
  have hs : (∑ q ∈ qRange n, (U7153.SAq n q : ℝ)) ≤
      mainSum n α ε C₁ + totalRemainder n α u := by
    unfold mainSum totalRemainder
    rw [← sum_add_distrib]
    exact sum_le_sum fun q hq => quotient_sieve α A u ε C₁ C₂ X₂ n q hG hT
      h7 hC₁ hC₂ heps he0 he1 hα hα1 hA hc hX hn hev hq
  have hm := main_sum_bound α A u ε C₁ X₂ n hG h3 hC₁ he0
    hα hα1 hA hc hX hn hev
  have hr := total_remainder_bound α A u X₂ n hG h3
    hα hα1 hA hc hX hn hev
  change (∑ q ∈ qRange n, (U7153.SAq n q : ℝ)) ≤ _
  calc
    _ ≤ mainSum n α ε C₁ + totalRemainder n α u := hs
    _ ≤ (8 * (UNfull n * n / log n ^ 2) * l1J α ε C₁ X₂ +
          8 * (UNfull n * n / log n ^ 2) * (l3J α ε C₁ X₂ / log n ^ (A - 1))) +
          8 * (UNfull n * n / log n ^ 2) * (l2J X₂ / log n ^ (A - 3)) := add_le_add hm hr
    _ = 8 * (UNfull n * n / log n ^ 2) * B6J α A ε C₁ X₂ n := by
      unfold B6J
      ring

/-- Exact Thm6J using the decomposed reciprocal estimates and task164 progression input. -/
theorem thm6J : Thm6J :=
  thm6J_of_inputs DecompC164a.lemma3J DecompC169c.lemma7J

end
end LeanLab.BS2022GRH.DecompC169b

#print axioms LeanLab.BS2022GRH.DecompC169b.quotient_sieve
#print axioms LeanLab.BS2022GRH.DecompC169b.main_sum_bound
#print axioms LeanLab.BS2022GRH.DecompC169b.total_remainder_bound
#print axioms LeanLab.BS2022GRH.DecompC169b.thm6J

#print axioms LeanLab.BS2022GRH.DecompC169b.thm6J_of_inputs
