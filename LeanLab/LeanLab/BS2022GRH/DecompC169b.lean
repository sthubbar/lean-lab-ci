/- AI wrote this Lean code for CODEX task169.
Theorem 6, journal pp. 1231 to 1234. Goldbach is open. -/
import LeanLab.BS2022GRH.DecompC169a
import LeanLab.BS2022GRH.ProgressionC169
import LeanLab.BS2022GRH.CoefficientsC169
import LeanLab.BS2022GRH.PublishedInputs232
import LeanLab.BS2022GRH.Lemma11C164

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




/-- Squarefree moduli coprime to n below a real level, pp. 1230 and 1233. -/
def squarefreeModuli (n : ℕ) (H : ℝ) : Finset ℕ :=
  (Icc 1 ⌊H⌋₊).filter (fun d => Squarefree d ∧ Nat.Coprime d n)

/-- The dependent pairs in the double remainder sum, p. 1233. -/
def quotientPairs (n : ℕ) (α u : ℝ) : Finset (Σ _q : ℕ, ℕ) :=
  (qRange n).sigma (fun q => quotientDivisors n q α u)

/-- Membership gives the prime interval and the exclusion q not dividing n, p. 1232. -/
theorem qRange_spec {n q : ℕ} (hq : q ∈ qRange n) :
    q.Prime ∧ ¬ q ∣ n ∧ U7153.zz n ≤ (q : ℝ) ∧ (q : ℝ) < U7153.yy n := by
  obtain ⟨hqQ, hqn⟩ := mem_filter.mp hq
  obtain ⟨_, hp, hz, hy⟩ := mem_filter.mp hqQ
  exact ⟨hp, hqn, hz, hy⟩

/-- Every quotient divisor is a squarefree product of the small eligible primes, p. 1232. -/
theorem quotientDivisors_spec {n q d : ℕ} {α u : ℝ}
    (hd : d ∈ quotientDivisors n q α u) :
    Squarefree d ∧ Nat.Coprime d n ∧ 0 < d ∧
      (d : ℝ) < smallProduct n u * quotientLevel n q α := by
  obtain ⟨hdI, hdlt⟩ := mem_filter.mp hd
  obtain ⟨T, hT, rfl⟩ := mem_image.mp hdI
  have hp (p : ℕ) (hpT : p ∈ T) : p.Prime ∧ ¬ p ∣ n := by
    have h := mem_powerset.mp hT hpT
    exact ⟨(mem_filter.mp h).2.1, (mem_filter.mp h).2.2.1⟩
  have hsq : Squarefree (∏ p ∈ T, p) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hpT r hrT hpr
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hp p hpT).1 (hp r hrT).1).mpr hpr)
    · intro p hpT
      exact (hp p hpT).1.squarefree
  have hcop : Nat.Coprime (∏ p ∈ T, p) n := by
    apply Nat.coprime_prod_left_iff.mpr
    intro p hpT
    exact ((hp p hpT).1.coprime_iff_not_dvd).mpr (hp p hpT).2
  exact ⟨hsq, hcop, Nat.pos_of_ne_zero hsq.ne_zero, hdlt⟩

/-- Every large prime is coprime to every small quotient divisor, p. 1233. -/
theorem quotientDivisors_coprime {n q d r : ℕ} {α u : ℝ}
    (hr : r ∈ qRange n) (hd : d ∈ quotientDivisors n q α u) : Nat.Coprime r d := by
  obtain ⟨hdI, _⟩ := mem_filter.mp hd
  obtain ⟨T, hT, rfl⟩ := mem_image.mp hdI
  exact qs_coprime_q_prod (qRange_spec hr).1 T (mem_powerset.mp hT)
    (qRange_spec hr).2.2.1

/-- Injectivity of the qd indexing on its actual dependent finite range, p. 1233. -/
theorem quotientPairs_injective (n : ℕ) (α u : ℝ) :
    Set.InjOn (fun x : Σ _q : ℕ, ℕ => x.1 * x.2) (quotientPairs n α u) := by
  rintro ⟨q, d⟩ hqd ⟨r, e⟩ hre heq
  change q * d = r * e at heq
  obtain ⟨hq, hd⟩ := mem_sigma.mp hqd
  obtain ⟨hr, he⟩ := mem_sigma.mp hre
  have hqp := (qRange_spec hq).1
  have hrp := (qRange_spec hr).1
  have hqe : ¬ q ∣ e := hqp.coprime_iff_not_dvd.mp (quotientDivisors_coprime hq he)
  have hqr : q ∣ r := by
    have h : q ∣ r * e := by rw [← heq]; exact dvd_mul_right q d
    exact (hqp.dvd_mul.mp h).resolve_right hqe
  have hqeq : q = r := (Nat.dvd_prime hrp).mp hqr |>.resolve_left hqp.ne_one
  subst r
  have hde : d = e := Nat.eq_of_mul_eq_mul_left hqp.pos heq
  subst e
  rfl

/-- Products in the quotient sum are squarefree and coprime to n, p. 1233. -/
theorem quotientPairs_squarefree {n : ℕ} {α u : ℝ} {x : Σ _q : ℕ, ℕ}
    (hx : x ∈ quotientPairs n α u) :
    Squarefree (x.1 * x.2) ∧ Nat.Coprime (x.1 * x.2) n := by
  obtain ⟨hq, hd⟩ := mem_sigma.mp hx
  obtain ⟨hp, hqn, _, _⟩ := qRange_spec hq
  obtain ⟨hsq, hcop, _, _⟩ := quotientDivisors_spec hd
  exact ⟨Nat.squarefree_mul_iff.mpr
      ⟨quotientDivisors_coprime hq hd, hp.squarefree, hsq⟩,
    (hp.coprime_iff_not_dvd.mpr hqn).mul_left hcop⟩

/-- The absolute residue identity of ResidueC169, used before that downstream import, p. 1233. -/
theorem quotientResidue_abs {n q d : ℕ} (hqd : Nat.Coprime q d) :
    |quotientResidue n q d| ≤ |residue n (q * d)| + |residue n q| / (d.totient : ℝ) := by
  have hid : quotientResidue n q d = residue n (q * d) - residue n q / (d.totient : ℝ) := by
    unfold quotientResidue aqCard residue
    rw [Nat.totient_mul hqd, Nat.cast_mul, div_mul_eq_div_div]
    ring
  rw [hid]
  simpa only [abs_div, abs_of_nonneg (Nat.cast_nonneg d.totient : (0 : ℝ) ≤ d.totient)] using
    (abs_sub (residue n (q * d)) (residue n q / (d.totient : ℝ)))

/-- Exact separation of the two absolute residue contributions, p. 1233. -/
theorem totalRemainder_split (n : ℕ) (α u : ℝ) :
    totalRemainder n α u ≤
      (∑ x ∈ quotientPairs n α u, |residue n (x.1 * x.2)|) +
        ∑ q ∈ qRange n, |residue n q| *
          ∑ d ∈ quotientDivisors n q α u, (1 : ℝ) / d.totient := by
  unfold totalRemainder quotientRemainder
  rw [show (∑ x ∈ quotientPairs n α u, |residue n (x.1 * x.2)|) =
    ∑ q ∈ qRange n, ∑ d ∈ quotientDivisors n q α u, |residue n (q * d)| by
      exact sum_sigma _ _ _]
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro q hq
  rw [mul_sum, ← sum_add_distrib]
  exact sum_le_sum fun d hd => by
    simpa only [mul_one_div] using quotientResidue_abs (quotientDivisors_coprime hq hd)

/-- The squarefree modulus count for any subset, CONDITIONAL ON Lemma 5, p. 1216. -/
theorem squarefree_count_le (hMu : PaperInputs148.Lemma5MuJ) (s : Finset ℕ) (H : ℝ)
    (hH : 1 ≤ H) (hs : ∀ d ∈ s, Squarefree d ∧ 1 ≤ d ∧ (d : ℝ) ≤ H) :
    (s.card : ℝ) ≤ Lemma5Coeffs138.mMu H * H := by
  apply le_trans _ (hMu H hH)
  exact_mod_cast card_le_card (show s ⊆ (Icc 1 ⌊H⌋₊).filter Squarefree from by
    intro d hd
    obtain ⟨hsq, hd1, hdH⟩ := hs d hd
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hd1, Nat.le_floor hdH⟩, hsq⟩)

/-- The reciprocal totient sum for any squarefree subset, CONDITIONAL ON Lemma 5, p. 1216. -/
theorem squarefree_totient_sum_le (hPhi : PaperInputs148.Lemma5PhiJ) (s : Finset ℕ) (H : ℝ)
    (hH : 1 < H) (hs : ∀ d ∈ s, Squarefree d ∧ 1 ≤ d ∧ (d : ℝ) ≤ H) :
    (∑ d ∈ s, (1 : ℝ) / d.totient) ≤ Mphi H * log H := by
  apply le_trans _ (hPhi H hH)
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨hsq, hd1, hdH⟩ := hs d hd
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hd1, Nat.le_floor hdH⟩, hsq⟩
  · intro d _ _
    positivity

/-- Reindexing loses no multiplicity in the first residue sum, p. 1233. -/
theorem product_residue_sum_le (n : ℕ) (α u H : ℝ)
    (hH : 0 ≤ H)
    (hlevel : ∀ q ∈ qRange n, ∀ d ∈ quotientDivisors n q α u, (q * d : ℕ) ≤ H) :
    (∑ x ∈ quotientPairs n α u, |residue n (x.1 * x.2)|) ≤
      ∑ d ∈ squarefreeModuli n H, |residue n d| := by
  rw [← sum_image (f := fun d => |residue n d|) (quotientPairs_injective n α u)]
  apply sum_le_sum_of_subset_of_nonneg
  · intro d hd
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hd
    obtain ⟨hsq, hcop⟩ := quotientPairs_squarefree hx
    obtain ⟨hq, hd⟩ := mem_sigma.mp hx
    exact mem_filter.mpr ⟨mem_Icc.mpr
      ⟨Nat.one_le_iff_ne_zero.mpr hsq.ne_zero, Nat.le_floor (hlevel _ hq _ hd)⟩,
      hsq, hcop⟩
  · intro d _ _
    exact abs_nonneg _




/-- The progression with d dividing n minus p is the usual class of n, p. 1229. -/
theorem progressionPrimes_eq (n d : ℕ) :
    ProgressionC169.progressionPrimes n d =
      (range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d) := by
  apply filter_congr
  intro p hp
  have hpn : p ≤ n := by have := mem_range.mp hp; omega
  exact and_congr_right fun _ => (Nat.modEq_iff_dvd' hpn).symm

/-- The progression error vanishes at modulus one, p. 1230. -/
theorem progressionError_one (n : ℕ) : ProgressionC169.progressionError n 1 = 0 := by
  simp [ProgressionC169.progressionError, ProgressionC169.progressionPrimes]

/-- The totient denominator contributes at most one half for d at least three, p. 1230. -/
theorem half_totient {d : ℕ} (hd : 3 ≤ d) : (2 : ℝ) ≤ d.totient := by
  have hφ : 2 ≤ d.totient := by
    by_contra h
    have hdiv := Nat.dvd_two_of_totient_le_one (by omega : 0 < d) (by omega)
    have := Nat.le_of_dvd (by norm_num : 0 < 2) hdiv
    omega
  exact_mod_cast hφ

/-- Lemma 12 pointwise estimate, CONDITIONAL ON Lemmas 1 and 3 and GRH, p. 1230. -/
theorem progression_error_le (h1 : PaperInputs148.Lemma1J) (h3 : Lemma3J)
    (hG : GRH) (n d : ℕ) (X : ℝ) (hX : 2657 ≤ X) (hn : X ≤ (n : ℝ))
    (hd : 3 ≤ d) (hdn : (d : ℝ) ≤ √(n : ℝ)) (hc : Nat.Coprime n d) :
    |ProgressionC169.progressionError n d| ≤ (0.02 + qG X) * √(n : ℝ) * log n := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hlog : 0 ≤ log (n : ℝ) := log_nonneg hn1
  have hφ := half_totient hd
  have hφ0 : (0 : ℝ) < d.totient := by linarith
  have hpi := PaperInputs148.lemma1_of_grh h1 hG n (hX.trans hn)
  simp only [PaperInputs148.primeCount, Nat.floor_natCast] at hpi
  have hprog := h3 hG d n n n hd hdn le_rfl hc
  simp only [Nat.floor_natCast] at hprog
  have hmono := DecompC164a.qG_antitone X n (by linarith) hn
  have hprog' :
      |(((range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d)).card : ℝ) -
        liPV n / d.totient| ≤ qG X * √(n : ℝ) * log n := by
    exact hprog.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmono (sqrt_nonneg _)) hlog)
  have hcorr :
      |liPV n - (((range (n + 1)).filter Nat.Prime).card : ℝ)| / d.totient ≤
        0.02 * √(n : ℝ) * log n := by
    rw [abs_sub_comm]
    calc
      _ ≤ (√(n : ℝ) * log n / (8 * π)) / d.totient :=
        div_le_div_of_nonneg_right hpi hφ0.le
      _ ≤ (√(n : ℝ) * log n / (8 * π)) / 2 := by gcongr
      _ = (1 / (16 * π)) * (√(n : ℝ) * log n) := by ring
      _ ≤ 0.02 * √(n : ℝ) * log n := by
        have hc : 1 / (16 * π) ≤ (0.02 : ℝ) := by
          rw [div_le_iff₀ (by positivity)]
          linarith [Real.pi_gt_d6]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc
          (mul_nonneg (sqrt_nonneg (n : ℝ)) hlog)
  unfold ProgressionC169.progressionError
  rw [progressionPrimes_eq]
  calc
    _ = |((((range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d)).card : ℝ) -
          liPV n / d.totient) +
          (liPV n - (((range (n + 1)).filter Nat.Prime).card : ℝ)) / d.totient| := by
      congr 1; ring
    _ ≤ |(((range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d)).card : ℝ) -
          liPV n / d.totient| +
          |liPV n - (((range (n + 1)).filter Nat.Prime).card : ℝ)| / d.totient := by
      simpa only [abs_div, abs_of_pos hφ0] using abs_add_le
        ((((range (n + 1)).filter (fun p => p.Prime ∧ p % d = n % d)).card : ℝ) - liPV n / d.totient)
        ((liPV n - (((range (n + 1)).filter Nat.Prime).card : ℝ)) / d.totient)
    _ ≤ qG X * √(n : ℝ) * log n + 0.02 * √(n : ℝ) * log n := add_le_add hprog' hcorr
    _ = _ := by ring

/-- Sum the elementary residue comparison on arbitrary squarefree moduli, pp. 1230 and 1231.
CONDITIONAL ON the squarefree count and the stated progression envelope. -/
theorem squarefree_residue_sum_raw (hMu : PaperInputs148.Lemma5MuJ)
    (n : ℕ) (H E : ℝ) (s : Finset ℕ) (hn : 0 < n) (hH : 1 ≤ H) (hE : 0 ≤ E)
    (hs : ∀ d ∈ s, Squarefree d ∧ 1 ≤ d ∧ (d : ℝ) ≤ H)
    (herr : ∀ d ∈ s, |ProgressionC169.progressionError n d| ≤ E) :
    (∑ d ∈ s, |residue n d|) ≤
      Lemma5Coeffs138.mMu H * H * (E + n.primeFactors.card) := by
  calc
    _ ≤ ∑ d ∈ s, (E + n.primeFactors.card) := sum_le_sum fun d hd =>
      (ProgressionC169.residue_abs_le n d hn).trans (add_le_add (herr d hd) le_rfl)
    _ = (s.card : ℝ) * (E + n.primeFactors.card) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (squarefree_count_le hMu s H hH hs)
      (by positivity)

/-- Condition 19 propagates from the threshold to every larger n, p. 1229.
This uses the already proved logarithmic monotonicity step. -/
theorem cond19_at (α A u X N : ℝ) (hα : 0 < α) (hA : 0 < A)
    (hc : Cond19 α A u X) (hX : 1 < X) (hXN : X ≤ N) :
    exp u ≤ N ^ α / log N ^ (A + 1) := by
  have hX0 : 0 < X := by linarith
  have hN0 : 0 < N := by linarith
  have hLX : 0 < log X := log_pos hX
  have hLN : 0 < log N := log_pos (hX.trans_le hXN)
  have hmono := Journal.mono_step hα (by linarith : 0 < A + 1) hc.1
    (log_le_log hX0 hXN)
  have heq (t : ℝ) (ht : 0 < t) (hlt : 0 < log t) :
      t ^ α / log t ^ (A + 1) = exp (α * log t - (A + 1) * log (log t)) := by
    rw [rpow_def_of_pos ht, rpow_def_of_pos hlt, ← exp_sub]
    congr 1; ring
  exact hc.2.1.trans (by
    rw [heq X hX0 hLX, heq N hN0 hLN]
    exact exp_le_exp.mpr hmono)

/-- Lemma 13 on any squarefree subset below the level, pp. 1230 and 1231.
CONDITIONAL ON Lemmas 1, 3, 4, 5 and GRH. No small-prime support is assumed. -/
theorem squarefree_residue_sum (h1 : PaperInputs148.Lemma1J)
    (h4 : PaperInputs148.Lemma4J) (hMu : PaperInputs148.Lemma5MuJ)
    (h3 : Lemma3J) (hG : GRH) (n : ℕ) (X A : ℝ) (s : Finset ℕ)
    (hX : 4e18 ≤ X) (hn : X ≤ (n : ℝ)) (hA : 0 < A) (hev : Even n)
    (hH : 1e8 ≤ √(n : ℝ) / log n ^ (A + 1))
    (hs : ∀ d ∈ s, Squarefree d ∧ 1 ≤ d ∧
      (d : ℝ) ≤ √(n : ℝ) / log n ^ (A + 1) ∧ Nat.Coprime d n) :
    (∑ d ∈ s, |residue n d|) ≤ cGJ X * n / log n ^ A := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hnNat : 0 < n := by exact_mod_cast hn0
  have hn3 : 3 ≤ n := by exact_mod_cast (show (3 : ℝ) ≤ n by linarith)
  have hL : 42.83 ≤ log (n : ℝ) := logX_bounds.1.trans
    (log_le_log (by norm_num) (hX.trans hn))
  have hLp : 0 < log (n : ℝ) := by linarith
  have hLL : 0 < log (log (n : ℝ)) := log_pos (by linarith)
  have hS : 0 < √(n : ℝ) := sqrt_pos.mpr hn0
  have hP : 0 < log (n : ℝ) ^ A := rpow_pos_of_pos hLp _
  have hP1 : 0 < log (n : ℝ) ^ (A + 1) := rpow_pos_of_pos hLp _
  have hpow : log (n : ℝ) ^ (A + 1) = log n ^ A * log n := by
    rw [rpow_add hLp, rpow_one]
  have hHsqrt : √(n : ℝ) / log n ^ (A + 1) ≤ √(n : ℝ) :=
    div_le_self hS.le (one_le_rpow (by linarith) (by linarith))
  have hq : 0 ≤ qG (n : ℝ) := EndpointC169.qG_nonneg n hn0 (by linarith)
  have hE : 0 ≤ (0.02 + qG (n : ℝ)) * √(n : ℝ) * log n := by positivity
  have herr (d : ℕ) (hd : d ∈ s) :
      |ProgressionC169.progressionError n d| ≤
        (0.02 + qG (n : ℝ)) * √(n : ℝ) * log n := by
    obtain ⟨_, hd1, hdH, hc⟩ := hs d hd
    by_cases hdOne : d = 1
    · subst d
      rw [progressionError_one, abs_zero]
      exact hE
    · have hd3 : 3 ≤ d := by
        by_contra h
        have hd2 : d = 2 := by omega
        subst d
        exact (Nat.prime_two.coprime_iff_not_dvd.mp hc) hev.two_dvd
      exact progression_error_le h1 h3 hG n d n (by linarith) le_rfl hd3
        (hdH.trans hHsqrt) hc.symm
  have hraw := squarefree_residue_sum_raw hMu n
    (√(n : ℝ) / log n ^ (A + 1))
    ((0.02 + qG (n : ℝ)) * √(n : ℝ) * log n) s hnNat
    (by linarith) hE (fun d hd => by obtain ⟨a,b,c,_⟩ := hs d hd; exact ⟨a,b,c⟩) herr
  have hcount := Lemma5Coeffs138.mMu_le0608 _ hH
  have hω := (h4 n hn3).le
  have hid : √(n : ℝ) / log n ^ (A + 1) * (√(n : ℝ) * log n) =
      (n : ℝ) / log n ^ A := by
    rw [hpow]
    field_simp
    nlinarith [sq_sqrt hn0.le]
  have htail :
      0.608 * (√(n : ℝ) / log n ^ (A + 1)) * n.primeFactors.card ≤
        (0.85 / (√(n : ℝ) * log (log n))) * ((n : ℝ) / log n ^ A) := by
    calc
      _ ≤ 0.608 * (√(n : ℝ) / log n ^ (A + 1)) *
          (1.3841 * log n / log (log n)) := by gcongr
      _ = (0.608 * 1.3841) / (√(n : ℝ) * log (log n)) * ((n : ℝ) / log n ^ A) := by
        rw [hpow]
        field_simp
        nlinarith [sq_sqrt hn0.le]
      _ ≤ _ := by
        gcongr
        norm_num
  have hraw' : (∑ d ∈ s, |residue n d|) ≤
      0.608 * (√(n : ℝ) / log n ^ (A + 1)) *
        ((0.02 + qG (n : ℝ)) * √(n : ℝ) * log n + n.primeFactors.card) := by
    apply hraw.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcount (by positivity)) (by positivity)
  have hnorm : (∑ d ∈ s, |residue n d|) ≤ cGJ (n : ℝ) * n / log n ^ A := by
    have heq : 0.608 * (√(n : ℝ) / log n ^ (A + 1)) *
        ((0.02 + qG (n : ℝ)) * √(n : ℝ) * log n) =
        pGJ n * ((n : ℝ) / log n ^ A) := by
      unfold pGJ
      calc
        _ = 0.608 * (0.02 + qG (n : ℝ)) *
            (√(n : ℝ) / log n ^ (A + 1) * (√(n : ℝ) * log n)) := by ring
        _ = _ := by rw [hid]
    calc
      _ ≤ _ := hraw'
      _ = 0.608 * (√(n : ℝ) / log n ^ (A + 1)) *
          ((0.02 + qG (n : ℝ)) * √(n : ℝ) * log n) +
          0.608 * (√(n : ℝ) / log n ^ (A + 1)) * n.primeFactors.card := by ring
      _ ≤ 0.608 * (√(n : ℝ) / log n ^ (A + 1)) *
          ((0.02 + qG (n : ℝ)) * √(n : ℝ) * log n) +
          (0.85 / (√(n : ℝ) * log (log n))) * ((n : ℝ) / log n ^ A) :=
        add_le_add le_rfl htail
      _ = _ := by rw [heq]; unfold cGJ; ring
  exact hnorm.trans (by
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_right
      (CoefficientsC169.cGJ_antitone X n hX hn) (div_nonneg hn0.le hP.le))

/-- The eligible small-prime product is bounded by exp theta, p. 1229. -/
theorem smallProduct_le_exp_theta (n : ℕ) (u : ℝ) :
    (smallProduct n u : ℝ) ≤ exp (Chebyshev.theta u) := by
  have hpos : 0 < (smallProduct n u : ℝ) := by
    rw [smallProduct, Nat.cast_prod]
    apply prod_pos
    intro p hp
    have hprime : p.Prime := (mem_filter.mp hp).2.1
    exact_mod_cast hprime.pos
  rw [← exp_log hpos]
  apply exp_le_exp.mpr
  rw [smallProduct, Nat.cast_prod, log_prod (fun p hp => by
    exact_mod_cast (mem_filter.mp hp).2.1.ne_zero), Chebyshev.theta_eq_sum_Icc]
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨_, hprime, _, hpu⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor hpu.le⟩, hprime⟩
  · intro p hp _
    exact log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le)

/-- The common product cutoff and prime interval lie below H, p. 1233.
CONDITIONAL ON Lemma 2. -/
theorem quotient_cutoffs (h2 : PaperInputs148.Lemma2J)
    (α A u X : ℝ) (n : ℕ) (hα : 0 < α) (hα1 : α < 1 / 24)
    (hA : 0 < A) (hc : Cond19 α A u X) (hX : exp (exp 10) ≤ X) (hn : X ≤ (n : ℝ)) :
    1e8 ≤ √(n : ℝ) / log n ^ (A + 1) ∧
      (smallProduct n u : ℝ) * (n : ℝ) ^ (1 / 2 - α) ≤ √(n : ℝ) / log n ^ (A + 1) ∧
      U7153.yy n ≤ √(n : ℝ) / log n ^ (A + 1) := by
  have hX1 : 1 < X := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hX
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 0 < log (n : ℝ) := log_pos (by linarith)
  have hP : 0 < log (n : ℝ) ^ (A + 1) := rpow_pos_of_pos hL _
  have h19 := cond19_at α A u X n hα hA hc hX1 hn
  have htheta := h2 u (by linarith [hc.2.2.1]) hc.2.2.2
  have hQ : (smallProduct n u : ℝ) ≤ exp u :=
    (smallProduct_le_exp_theta n u).trans (exp_le_exp.mpr htheta)
  have hprod : (n : ℝ) ^ α * (n : ℝ) ^ (1 / 2 - α) = √(n : ℝ) := by
    rw [← rpow_add hn0]
    convert (sqrt_eq_rpow (n : ℝ)).symm using 1 <;> congr 1 <;> ring
  have hD : (n : ℝ) ^ (1 / 2 - α) ≤ √(n : ℝ) / log n ^ (A + 1) := by
    calc
      _ ≤ exp u * (n : ℝ) ^ (1 / 2 - α) := by
        exact le_mul_of_one_le_left (rpow_nonneg hn0.le _) (one_le_exp_iff.mpr (by linarith [hc.2.2.1]))
      _ ≤ ((n : ℝ) ^ α / log n ^ (A + 1)) * (n : ℝ) ^ (1 / 2 - α) :=
        mul_le_mul_of_nonneg_right h19 (rpow_nonneg hn0.le _)
      _ = _ := by rw [div_mul_eq_mul_div, hprod]
  refine ⟨?_, ?_, ?_⟩
  · have h := Journal.remark1_H hn1 (by linarith : α ≤ 1 / 2) hP hc.2.2.1 h19
    norm_num at h ⊢
    exact h
  · calc
      _ ≤ ((n : ℝ) ^ α / log n ^ (A + 1)) * (n : ℝ) ^ (1 / 2 - α) :=
        mul_le_mul_of_nonneg_right (hQ.trans h19) (rpow_nonneg hn0.le _)
      _ = _ := by rw [div_mul_eq_mul_div, hprod]
  · exact (rpow_le_rpow_of_exponent_le hn1 (by linarith : (1 / 3 : ℝ) ≤ 1 / 2 - α)).trans hD

/-- Every product qd is below the common product cutoff, p. 1233. -/
theorem quotient_product_lt {n q d : ℕ} {α u : ℝ}
    (hq : q ∈ qRange n) (hd : d ∈ quotientDivisors n q α u) :
    ((q * d : ℕ) : ℝ) < (smallProduct n u : ℝ) * (n : ℝ) ^ (1 / 2 - α) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (qRange_spec hq).1.pos
  have hdlt := (quotientDivisors_spec hd).2.2.2
  unfold quotientLevel at hdlt
  rw [← mul_div_assoc] at hdlt
  have h := (lt_div_iff₀ hq0).mp hdlt
  simpa only [Nat.cast_mul, mul_comm] using h

/-- The explicit 0.50007 logarithmic bound needed for the inner totient sum, p. 1233. -/
theorem Mphi_sqrt_log_le (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ))
    (hS : 1e8 ≤ √(n : ℝ)) : Mphi (√(n : ℝ)) * log (√(n : ℝ)) ≤ 0.50007 * log n := by
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hn
  have hL := Lemma11C164.log_lower n hn
  have hls : 11000 ≤ log (√(n : ℝ)) := by rw [log_sqrt hn0.le]; linarith
  have hls0 : 0 < log (√(n : ℝ)) := by linarith
  have hss : (10000 : ℝ) ≤ √(√(n : ℝ)) := by
    have h := sqrt_le_sqrt hS
    norm_num at h
    exact h
  have h1 : 1.333 / log (√(n : ℝ)) ≤ (1.333 : ℝ) / 11000 := by gcongr
  have h2 : 2.44 / (√(√(n : ℝ)) * log (√(n : ℝ))) ≤ (2.44 : ℝ) / (10000 * 11000) := by gcongr
  have hφ : Mphi (√(n : ℝ)) ≤ 1.00014 := by
    unfold Mphi
    have hmin : min (2.44 / (√(√(n : ℝ)) * log (√(n : ℝ))))
        (11 / (√(√(n : ℝ)) * log (√(n : ℝ)) ^ 2)) ≤
        2.44 / (√(√(n : ℝ)) * log (√(n : ℝ))) := min_le_left _ _
    linarith
  calc
    _ ≤ 1.00014 * log (√(n : ℝ)) := mul_le_mul_of_nonneg_right hφ hls0.le
    _ = _ := by rw [log_sqrt hn0.le]; ring

/-- The lab normalization has at least the paper's singular factor, p. 1231. -/
theorem UNfull_invTw_ge_one (n : ℕ) : 1 ≤ UNfull n * invTw := by
  have ht : LeanLab.ChenExplicit.twinC ≠ 0 := LeanLab.ChenExplicit.twinC_pos.ne'
  have he := exp_ne_zero (-eulerMascheroniConstant)
  have hid : UNfull n * invTw = 2 * UN n := by
    rw [UNfull_eq]
    unfold invTw
    field_simp
    <;> ring
  rw [hid]
  linarith [one_le_UN n]

/-- Normalize the two remainder contributions to the sealed l2 expression, p. 1233. -/
theorem remainder_normalization (n : ℕ) (X A : ℝ) (hX : 1 < X)
    (hn : X ≤ (n : ℝ)) (hcg : 0 ≤ cGJ X) :
    cGJ X * n / log n ^ A + cGJ X * n / log n ^ A * (0.50007 * log n) ≤
      8 * (UNfull n * n / log n ^ 2) * (l2J X / log n ^ (A - 3)) := by
  have hXp : 0 < X := by linarith
  have hLXp : 0 < log X := log_pos hX
  have hn1 : (1 : ℝ) < n := hX.trans_le hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hLp : 0 < log (n : ℝ) := log_pos hn1
  have hP := rpow_pos_of_pos hLp A
  have hlog := log_le_log hXp hn
  have hratio : 1 ≤ log (n : ℝ) / log X := (one_le_div hLXp).mpr hlog
  have hR : 0 ≤ cGJ X * n / log n ^ A := by positivity
  have hB : 0 ≤ 0.50007 * log (n : ℝ) + log (n : ℝ) / log X := by positivity
  have heq :
      8 * (UNfull n * n / log n ^ 2) * (l2J X / log n ^ (A - 3)) =
        (UNfull n * invTw) * (cGJ X * n / log n ^ A) *
          (0.50007 * log n + log n / log X) := by
    unfold l2J
    rw [rpow_sub hLp]
    norm_num only [rpow_ofNat]
    field_simp
    <;> ring
  rw [heq]
  calc
    _ = (cGJ X * n / log n ^ A) * (0.50007 * log n + 1) := by ring
    _ ≤ (cGJ X * n / log n ^ A) * (0.50007 * log n + log n / log X) := by gcongr
    _ ≤ _ := by
      simpa only [one_mul, mul_assoc] using mul_le_mul_of_nonneg_right
        (UNfull_invTw_ge_one n) (mul_nonneg hR hB)

/-- The full remainder reduction, CONDITIONAL ON the named published inputs, p. 1233. -/
theorem total_remainder_of_inputs
    (h1 : PaperInputs148.Lemma1J) (h2 : PaperInputs148.Lemma2J)
    (h4 : PaperInputs148.Lemma4J) (hMu : PaperInputs148.Lemma5MuJ)
    (hPhi : PaperInputs148.Lemma5PhiJ)
    (α A u X₂ : ℝ) (n : ℕ) (hG : GRH) (h3 : Lemma3J)
    (hα : 0 < α) (hα1 : α < 1 / 24) (hA : 0 < A)
    (hc : Cond19 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    totalRemainder n α u ≤
      8 * (UNfull n * n / log n ^ 2) * (l2J X₂ / log n ^ (A - 3)) := by
  have hN := hX.trans hn
  have hn0 : (0 : ℝ) < n := (exp_pos _).trans_le hN
  have hL := Lemma11C164.log_lower n hN
  have hLp : 0 < log (n : ℝ) := by linarith
  have hHsqrt : √(n : ℝ) / log n ^ (A + 1) ≤ √(n : ℝ) :=
    div_le_self (sqrt_nonneg _) (one_le_rpow (by linarith) (by linarith))
  obtain ⟨hH, hQD, hyH⟩ := quotient_cutoffs h2 α A u X₂ n hα hα1 hA hc hX hn
  have hprod (q : ℕ) (hq : q ∈ qRange n) (d : ℕ)
      (hd : d ∈ quotientDivisors n q α u) :
      ((q * d : ℕ) : ℝ) ≤ √(n : ℝ) / log n ^ (A + 1) :=
    (quotient_product_lt hq hd).le.trans hQD
  have hX18 : 4e18 ≤ X₂ := by
    have hbig : (4e18 : ℝ) ≤ exp (exp 10) := by
      calc
        (4e18 : ℝ) ≤ (1e8 : ℝ) ^ 3 := by norm_num
        _ ≤ exp 2753 ^ 3 := pow_le_pow_left₀ (by norm_num) qs_exp2753_gt_1e8.le 3
        _ = exp (3 * 2753) := by rw [← exp_nat_mul]; norm_num
        _ ≤ exp (exp 10) := exp_le_exp.mpr (by linarith [qs_exp10_gt])
    exact hbig.trans hX
  have hmod := squarefree_residue_sum h1 h4 hMu h3 hG n X₂ A
    (squarefreeModuli n (√(n : ℝ) / log n ^ (A + 1)))
    hX18 hn hA hev hH (by
      intro d hd
      obtain ⟨hdI, hsq, hcop⟩ := mem_filter.mp hd
      obtain ⟨hd1, hdH⟩ := mem_Icc.mp hdI
      have hle : (d : ℝ) ≤ (⌊√(n : ℝ) / log n ^ (A + 1)⌋₊ : ℝ) := by exact_mod_cast hdH
      exact ⟨hsq, hd1, hle.trans (Nat.floor_le (by positivity)), hcop⟩)
  have hqsum := squarefree_residue_sum h1 h4 hMu h3 hG n X₂ A
    (qRange n) hX18 hn hA hev hH (by
      intro q hq
      obtain ⟨hp, hqn, _, hy⟩ := qRange_spec hq
      exact ⟨hp.squarefree, hp.one_le, hy.le.trans hyH, hp.coprime_iff_not_dvd.mpr hqn⟩)
  have hinner (q : ℕ) (hq : q ∈ qRange n) :
      (∑ d ∈ quotientDivisors n q α u, (1 : ℝ) / d.totient) ≤ 0.50007 * log n := by
    apply (squarefree_totient_sum_le hPhi _ (√(n : ℝ)) (by linarith [hH.trans hHsqrt]) ?_).trans
      (Mphi_sqrt_log_le n hN (hH.trans hHsqrt))
    intro d hd
    obtain ⟨hsq, _, hdpos, _⟩ := quotientDivisors_spec hd
    refine ⟨hsq, hdpos, ?_⟩
    calc
      (d : ℝ) ≤ (q : ℝ) * d := le_mul_of_one_le_left (Nat.cast_nonneg _)
        (by exact_mod_cast (qRange_spec hq).1.one_le)
      _ = ((q * d : ℕ) : ℝ) := (Nat.cast_mul _ _).symm
      _ ≤ _ := (hprod q hq d hd).trans hHsqrt
  have hproductSum := (product_residue_sum_le n α u _ (by positivity) hprod).trans hmod
  have hweighted : (∑ q ∈ qRange n, |residue n q| *
      ∑ d ∈ quotientDivisors n q α u, (1 : ℝ) / d.totient) ≤
      (cGJ X₂ * n / log n ^ A) * (0.50007 * log n) := by
    calc
      _ ≤ ∑ q ∈ qRange n, |residue n q| * (0.50007 * log n) := by
        exact sum_le_sum fun q hq => mul_le_mul_of_nonneg_left (hinner q hq) (abs_nonneg _)
      _ = (∑ q ∈ qRange n, |residue n q|) * (0.50007 * log n) := (sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hqsum (by positivity)
  have hcg := (CoefficientsC169.coefficient_ranges X₂ hX18).2.2.1
  exact ((totalRemainder_split n α u).trans (add_le_add hproductSum hweighted)).trans
    (remainder_normalization n X₂ A (by
      exact (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hX) hn hcg)

/-- The exact main term plus residue split from ResidueC169, p. 1233 display 24. -/
theorem mainSum_identity (n : ℕ) (α ε C₁ : ℝ) :
    mainSum n α ε C₁ =
      density n * ((U7153.Aset n).card : ℝ) *
        (∑ q ∈ qRange n, upperCoefficient n q α ε C₁ / ((q : ℝ) - 1)) +
      density n * ∑ q ∈ qRange n, upperCoefficient n q α ε C₁ * residue n q := by
  unfold mainSum
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  have hid : aqCard n q = ((U7153.Aset n).card : ℝ) / ((q : ℝ) - 1) + residue n q := by
    unfold aqCard residue
    rw [Nat.totient_prime (qRange_spec hq).1, Nat.cast_sub (qRange_spec hq).1.one_le]
    norm_num
  rw [hid]
  ring

/-- The sieve density is nonnegative for even n, p. 1227. -/
theorem density_nonneg (n : ℕ) (hev : Even n) : 0 ≤ density n := by
  apply prod_nonneg
  intro p hp
  obtain ⟨_, hprime, hpn, _⟩ := mem_filter.mp hp
  have hp3 : 3 ≤ p := by
    have hp2 := hprime.two_le
    by_contra h
    have hp : p = 2 := by omega
    subst p
    exact hpn hev.two_dvd
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hdiv : 1 / ((p : ℝ) - 1) ≤ (1 : ℝ) := (div_le_one (by linarith)).mpr (by linarith)
  linarith

/-- The display 24 reciprocal-log weight has this positive derivative, p. 1234. -/
theorem reciprocal_log_hasDeriv (D t : ℝ) (ht : 0 < t) (htD : t < D) :
    HasDerivAt (fun x : ℝ => (log D - log x)⁻¹)
      (1 / (t * (log D - log t) ^ 2)) t := by
  have hlog : 0 < log D - log t := sub_pos.mpr
    (log_lt_log ht htD)
  convert (((hasDerivAt_const t (log D)).sub (hasDerivAt_log ht.ne')).inv hlog.ne') using 1
  dsimp
  field_simp
  <;> ring

/-- Abel summation for the exact prime reciprocal-log weight, p. 1234.
The finite endpoint form is explicit, so no endpoint prime is silently dropped. -/
theorem weighted_prime_abel (a b D : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbD : b < D) :
    (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊,
      (log D - log (k : ℝ))⁻¹ * (if k.Prime then (1 : ℝ) / k else 0)) =
      (log D - log b)⁻¹ * (∑ k ∈ Icc 0 ⌊b⌋₊, if k.Prime then (1 : ℝ) / k else 0) -
      (log D - log a)⁻¹ * (∑ k ∈ Icc 0 ⌊a⌋₊, if k.Prime then (1 : ℝ) / k else 0) -
      ∫ t in Set.Ioc a b, (1 / (t * (log D - log t) ^ 2)) *
        ∑ k ∈ Icc 0 ⌊t⌋₊, if k.Prime then (1 : ℝ) / k else 0 := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) :=
    reciprocal_log_hasDeriv D t (ha.trans_le ht.1) (ht.2.trans_lt hbD)
  have hcont : ContinuousOn (fun t : ℝ => 1 / (t * (log D - log t) ^ 2)) (Set.Icc a b) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    have ht0 : 0 < t := ha.trans_le ht.1
    have hlog : 0 < log D - log t := sub_pos.mpr
      (log_lt_log ht0 (ht.2.trans_lt hbD))
    exact continuousAt_const.div
      (continuousAt_id.mul ((continuousAt_const.sub (continuousAt_log ht0.ne')).pow 2))
      (mul_ne_zero ht0.ne' (pow_ne_zero _ hlog.ne'))
  have hint : MeasureTheory.IntegrableOn
      (deriv (fun t : ℝ => (log D - log t)⁻¹)) (Set.Icc a b) := by
    apply hcont.integrableOn_Icc.congr
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with t ht
    exact (hd t ht).deriv.symm
  have h := sum_mul_eq_sub_sub_integral_mul
    (fun k : ℕ => if k.Prime then (1 : ℝ) / k else 0) ha.le hab
    (fun t ht => (hd t ht).differentiableAt) hint
  rw [h]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [(hd t ⟨ht.1.le, ht.2⟩).deriv]


/-- The logarithmic quotient parameter, p. 1233, reused without a downstream import. -/
theorem quotientParameter_eq (n q : ℕ) (α : ℝ) (hn : (1 : ℝ) < n) (hq : 0 < q) :
    quotientParameter n q α = 8 * (1 / 2 - α - log q / log n) := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hlog : log (n : ℝ) ≠ 0 := (log_pos hn).ne'
  unfold quotientParameter quotientLevel U7153.zz
  rw [log_div (rpow_pos_of_pos hn0 _).ne' hq0.ne', log_rpow hn0, log_rpow hn0]
  field_simp
  <;> ring

/-- The parameter lies between k alpha and three, p. 1233 display 24. -/
theorem quotientParameter_range (n q : ℕ) (α : ℝ) (hn : (1 : ℝ) < n)
    (hα : 0 < α) (hα1 : α < 1 / 24) (hq : q ∈ qRange n) :
    1 < kA α ∧ kA α ≤ quotientParameter n q α ∧ quotientParameter n q α < 3 := by
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hprime, _, hqz, hqy⟩ := qRange_spec hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hprime.pos
  have hL : 0 < log (n : ℝ) := log_pos hn
  have hlo : (1 / 8 : ℝ) * log n ≤ log q := by
    rw [← log_rpow hn0]
    exact log_le_log (rpow_pos_of_pos hn0 _) hqz
  have hhi : log q < (1 / 3 : ℝ) * log n := by
    rw [← log_rpow hn0]
    exact log_lt_log hq0 hqy
  have hfraclo : (1 / 8 : ℝ) ≤ log q / log n := (le_div_iff₀ hL).mpr hlo
  have hfrachi : log q / log n < (1 / 3 : ℝ) := (div_lt_iff₀ hL).mpr hhi
  rw [quotientParameter_eq n q α hn hprime.pos]
  unfold kA
  constructor
  · linarith
  · constructor <;> linarith

/-- The sieve error function is bounded by its value at k alpha, p. 1233. -/
theorem hS_quotient_le (n q : ℕ) (α : ℝ) (hn : (1 : ℝ) < n)
    (hα : 0 < α) (hα1 : α < 1 / 24) (hq : q ∈ qRange n) :
    0 ≤ hS (quotientParameter n q α) ∧ hS (quotientParameter n q α) ≤ hS (kA α) := by
  obtain ⟨hk, hks, hs3⟩ := quotientParameter_range n q α hn hα hα1 hq
  have hk2 : kA α ≤ 2 := by unfold kA; linarith
  unfold hS
  rw [if_pos hk2, if_pos hs3.le]
  split_ifs with hs2
  · exact ⟨(exp_pos _).le, le_rfl⟩
  · exact ⟨(exp_pos _).le, exp_le_exp.mpr (by linarith)⟩

/-- Uniform coefficient control for the residue term in display 24, p. 1233. -/
theorem upperCoefficient_bounds (n q : ℕ) (α ε C₁ : ℝ) (hn : (1 : ℝ) < n)
    (hα : 0 < α) (hα1 : α < 1 / 24) (hε : 0 ≤ ε) (hC : 0 ≤ C₁) (hq : q ∈ qRange n) :
    0 ≤ upperCoefficient n q α ε C₁ ∧
      upperCoefficient n q α ε C₁ ≤
        2 * exp eulerMascheroniConstant / kA α + ε * C₁ * exp 2 * hS (kA α) := by
  obtain ⟨hk, hks, _⟩ := quotientParameter_range n q α hn hα hα1 hq
  obtain ⟨hS0, hSle⟩ := hS_quotient_le n q α hn hα hα1 hq
  have hs0 : 0 < quotientParameter n q α := by linarith
  unfold upperCoefficient
  constructor
  · positivity
  · exact add_le_add
      (div_le_div_of_nonneg_left (by positivity) (by linarith) hks)
      (mul_le_mul_of_nonneg_left hSle (by positivity))

/-- Display 24 before the analytic bounds for the two prime sums, p. 1233. -/
theorem mainSum_abs_bound (n : ℕ) (α ε C₁ : ℝ) (hn : (1 : ℝ) < n) (hev : Even n)
    (hα : 0 < α) (hα1 : α < 1 / 24) (hε : 0 ≤ ε) (hC : 0 ≤ C₁) :
    mainSum n α ε C₁ ≤
      density n * ((U7153.Aset n).card : ℝ) *
        (∑ q ∈ qRange n, upperCoefficient n q α ε C₁ / ((q : ℝ) - 1)) +
      density n *
        (2 * exp eulerMascheroniConstant / kA α + ε * C₁ * exp 2 * hS (kA α)) *
        ∑ q ∈ qRange n, |residue n q| := by
  rw [mainSum_identity]
  apply add_le_add le_rfl
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (density_nonneg n hev)
  rw [mul_sum]
  apply sum_le_sum
  intro q hq
  obtain ⟨hco0, hcole⟩ := upperCoefficient_bounds n q α ε C₁ hn hα hα1 hε hC hq
  exact (mul_le_mul_of_nonneg_left (le_abs_self _) hco0).trans
    (mul_le_mul_of_nonneg_right hcole (abs_nonneg _))

/-- Replace q minus one by q with the exact endpoint factor, p. 1234. -/
theorem prime_denominator_le (n q : ℕ) (hn : (1 : ℝ) < n) (hq : q ∈ qRange n) :
    (1 : ℝ) / ((q : ℝ) - 1) ≤ rX n / q := by
  have hz : (1 : ℝ) < U7153.zz n := one_lt_rpow hn (by norm_num)
  have hqz := (qRange_spec hq).2.2.1
  have hq1 : (1 : ℝ) < q := hz.trans_le hqz
  have hq0 : (0 : ℝ) < q := by linarith
  have hratio : (q : ℝ) / ((q : ℝ) - 1) ≤ rX n := by
    unfold rX
    change (q : ℝ) / ((q : ℝ) - 1) ≤ U7153.zz n / (U7153.zz n - 1)
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  calc
    _ = ((q : ℝ) / ((q : ℝ) - 1)) / q := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hratio hq0.le

/-- Put the upper coefficient into the logarithmic form used in display 24, p. 1233. -/
theorem upperCoefficient_log_le (n q : ℕ) (α ε C₁ : ℝ) (hn : (1 : ℝ) < n)
    (hα : 0 < α) (hα1 : α < 1 / 24) (hε : 0 ≤ ε) (hC : 0 ≤ C₁) (hq : q ∈ qRange n) :
    upperCoefficient n q α ε C₁ ≤
      exp eulerMascheroniConstant / 4 * log n / log (quotientLevel n q α) +
        ε * C₁ * exp 2 * hS (kA α) := by
  obtain ⟨hk, hks, _⟩ := quotientParameter_range n q α hn hα hα1 hq
  have hparam : 0 < quotientParameter n q α := by linarith
  have hzlog : 0 < log (U7153.zz n) := log_pos (one_lt_rpow hn (by norm_num))
  have hDlog : 0 < log (quotientLevel n q α) := by
    have h := mul_pos hparam hzlog
    unfold quotientParameter at h
    simpa only [div_mul_cancel₀ _ hzlog.ne'] using h
  have hid : 2 * exp eulerMascheroniConstant / quotientParameter n q α =
      exp eulerMascheroniConstant / 4 * log n / log (quotientLevel n q α) := by
    unfold quotientParameter U7153.zz
    rw [log_rpow (by linarith : (0 : ℝ) < n)]
    field_simp
    <;> ring
  unfold upperCoefficient
  rw [hid]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (hS_quotient_le n q α hn hα hα1 hq).2 (by positivity))

/-- The first prime sum in display 24, CONDITIONAL ON the two explicit prime envelopes.
The q minus one endpoint factor is retained, p. 1234. -/
theorem main_prime_sum_bound (n : ℕ) (α ε C₁ W U : ℝ)
    (hn : (1 : ℝ) < n) (hα : 0 < α) (hα1 : α < 1 / 24)
    (hε : 0 ≤ ε) (hC : 0 ≤ C₁)
    (hW : (∑ q ∈ qRange n, (1 : ℝ) / ((q : ℝ) * log (quotientLevel n q α))) ≤ W)
    (hU : (∑ q ∈ qRange n, (1 : ℝ) / q) ≤ U) :
    (∑ q ∈ qRange n, upperCoefficient n q α ε C₁ / ((q : ℝ) - 1)) ≤
      rX n * (exp eulerMascheroniConstant / 4 * log n * W +
        ε * C₁ * exp 2 * hS (kA α) * U) := by
  have hLp : 0 < log (n : ℝ) := log_pos hn
  have hz1 : (1 : ℝ) < (n : ℝ) ^ (1 / 8 : ℝ) := one_lt_rpow hn (by norm_num)
  have hr : 0 ≤ rX n := by unfold rX; positivity
  have hk2 : kA α ≤ 2 := by unfold kA; linarith
  have hS0 : 0 ≤ hS (kA α) := by unfold hS; rw [if_pos hk2]; positivity
  have hB : 0 ≤ ε * C₁ * exp 2 * hS (kA α) := by positivity
  have hpoint (q : ℕ) (hq : q ∈ qRange n) :
      upperCoefficient n q α ε C₁ / ((q : ℝ) - 1) ≤
        rX n * (exp eulerMascheroniConstant / 4 * log n *
          ((1 : ℝ) / ((q : ℝ) * log (quotientLevel n q α))) +
          ε * C₁ * exp 2 * hS (kA α) * ((1 : ℝ) / q)) := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (qRange_spec hq).1.pos
    have hco := upperCoefficient_log_le n q α ε C₁ hn hα hα1 hε hC hq
    have hco0 := (upperCoefficient_bounds n q α ε C₁ hn hα hα1 hε hC hq).1
    calc
      _ ≤ upperCoefficient n q α ε C₁ * (rX n / q) := by
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (prime_denominator_le n q hn hq) hco0
      _ = rX n * (upperCoefficient n q α ε C₁ / q) := by ring
      _ ≤ rX n * ((exp eulerMascheroniConstant / 4 * log n / log (quotientLevel n q α) +
          ε * C₁ * exp 2 * hS (kA α)) / q) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hco hq0.le) hr
      _ = _ := by ring
  calc
    _ ≤ ∑ q ∈ qRange n, rX n * (exp eulerMascheroniConstant / 4 * log n *
        ((1 : ℝ) / ((q : ℝ) * log (quotientLevel n q α))) +
        ε * C₁ * exp 2 * hS (kA α) * ((1 : ℝ) / q)) := sum_le_sum hpoint
    _ = rX n * (exp eulerMascheroniConstant / 4 * log n *
        (∑ q ∈ qRange n, (1 : ℝ) / ((q : ℝ) * log (quotientLevel n q α))) +
        ε * C₁ * exp 2 * hS (kA α) * (∑ q ∈ qRange n, (1 : ℝ) / q)) := by
      simp only [mul_sum, sum_add_distrib, mul_add]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hW (by positivity))
        (mul_le_mul_of_nonneg_left hU hB)) hr

/-- Positivity of the reciprocal-log denominator on the full prime interval, p. 1234. -/
theorem log_quotientLevel_pos (n q : ℕ) (α : ℝ) (hn : (1 : ℝ) < n)
    (hα1 : α < 1 / 24) (hq0 : 0 < q) (hqy : (q : ℝ) < U7153.yy n) :
    0 < log (quotientLevel n q α) := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  have hD : (n : ℝ) ^ (1 / 6 - α) ≤ quotientLevel n q α := by
    have h := div_le_div_of_nonneg_left (rpow_nonneg hn0.le (1 / 2 - α)) hqr hqy.le
    have hid : (n : ℝ) ^ (1 / 2 - α) / U7153.yy n = (n : ℝ) ^ (1 / 6 - α) := by
      unfold U7153.yy
      rw [← rpow_sub hn0]
      congr 1
      ring
    rw [hid] at h
    exact h
  exact log_pos ((one_lt_rpow hn (by linarith : (0 : ℝ) < 1 / 6 - α)).trans_le hD)

/-- The first display 24 prime sum reduced to the two published envelopes, p. 1234.
CONDITIONAL ON weighted_reciprocal_primes and reciprocal_prime_interval. -/
theorem main_prime_sum_published (n : ℕ) (α ε C₁ : ℝ)
    (hn : exp (exp 10) ≤ (n : ℝ)) (hev : Even n)
    (hα : 0 < α) (hα1 : α < 1 / 24) (hε : 0 ≤ ε) (hC : 0 ≤ C₁) :
    (∑ q ∈ qRange n, upperCoefficient n q α ε C₁ / ((q : ℝ) - 1)) ≤
      rX n * (exp eulerMascheroniConstant / 4 * log n *
        ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / ((1 / 2 - α) * log n) +
          512 / (kA α * log n ^ 3)) +
        ε * C₁ * exp 2 * hS (kA α) * (log (8 / 3) + 64 / log n ^ 2)) := by
  have hn1 : (1 : ℝ) < n := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hn
  apply main_prime_sum_bound n α ε C₁ _ _ hn1 hα hα1 hε hC
  · apply le_trans _ (PublishedInputs232.weighted_reciprocal_primes n α hn hα hα1)
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro q hq _
    obtain ⟨_, hp, _, hqy⟩ := mem_filter.mp hq
    exact div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _)
      (log_quotientLevel_pos n q α hn1 hα1 hp.pos hqy).le)
  · apply le_trans _ (PublishedInputs232.reciprocal_prime_interval n hn hev)
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun q _ _ => by positivity)

/-- The cardinality input for display 24 uses the existing Lemma 11 error budget, p. 1228.
CONDITIONAL ON Lemmas 1 and 4, GRH and the two stated li estimates. -/
theorem cardinality_upper_of_inputs (h1 : PaperInputs148.Lemma1J)
    (h4 : PaperInputs148.Lemma4J) (hG : GRH) (n : ℕ)
    (hn : exp (exp 10) ≤ (n : ℝ))
    (hliL : (1 + 1 / log (n : ℝ)) * n / log n ≤ liPV n)
    (hliU : liPV n ≤ (1 + 1 / log (n : ℝ) + 3 / log n ^ 2) * n / log n) :
    ((U7153.Aset n).card : ℝ) ≤ (1 + 5e-5) * n / log n := by
  have hlarge : (2657 : ℝ) ≤ n := by
    have h := add_one_le_exp (exp 10)
    linarith [qs_exp10_gt]
  have hn3 : 3 ≤ n := by exact_mod_cast (show (3 : ℝ) ≤ n by linarith)
  have hpi := PaperInputs148.lemma1_of_grh h1 hG n hlarge
  simp only [PaperInputs148.primeCount, Nat.floor_natCast] at hpi
  exact (Lemma11C164.cardinality_bounds n hn hpi (h4 n hn3).le hliL hliU).2

/-- The residue contribution of display 24 has exactly the l3 normalization, p. 1233.
CONDITIONAL ON the density and prime residue estimates supplied as inequalities. -/
theorem main_residue_normalization (n : ℕ) (α A ε C₁ X : ℝ)
    (hn : (1 : ℝ) < n) (hev : Even n) (hX : 1 < X)
    (hα : 0 < α) (hα1 : α < 1 / 24) (hε : 0 ≤ ε) (hC : 0 ≤ C₁)
    (hcg : 0 ≤ cGJ X)
    (hdensity : density n ≤ 8 * UNfull n / log n * (1 + 0.62 * log X / X ^ (1 / 16 : ℝ)))
    (hres : (∑ q ∈ qRange n, |residue n q|) ≤ cGJ X * n / log n ^ A) :
    density n * (2 * exp eulerMascheroniConstant / kA α + ε * C₁ * exp 2 * hS (kA α)) *
        (∑ q ∈ qRange n, |residue n q|) ≤
      8 * (UNfull n * n / log n ^ 2) * (l3J α ε C₁ X / log n ^ (A - 1)) := by
  have hLp : 0 < log (n : ℝ) := log_pos hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hk0 : 0 < kA α := by unfold kA; linarith
  have hk2 : kA α ≤ 2 := by unfold kA; linarith
  have hS0 : 0 ≤ hS (kA α) := by unfold hS; rw [if_pos hk2]; positivity
  have hco0 : 0 ≤ 2 * exp eulerMascheroniConstant / kA α + ε * C₁ * exp 2 * hS (kA α) := by positivity
  have hR0 : 0 ≤ cGJ X * n / log n ^ A := by positivity
  calc
    _ ≤ density n * (2 * exp eulerMascheroniConstant / kA α + ε * C₁ * exp 2 * hS (kA α)) *
        (cGJ X * n / log n ^ A) := mul_le_mul_of_nonneg_left hres
      (mul_nonneg (density_nonneg n hev) hco0)
    _ ≤ (8 * UNfull n / log n * (1 + 0.62 * log X / X ^ (1 / 16 : ℝ))) *
        (2 * exp eulerMascheroniConstant / kA α + ε * C₁ * exp 2 * hS (kA α)) *
        (cGJ X * n / log n ^ A) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hdensity hco0) hR0
    _ = _ := by
      unfold l3J
      rw [rpow_sub hLp]
      norm_num only [rpow_one]
      field_simp
      <;> ring

/-- A uniform maximum for the reciprocal-log weight loses the integral coefficient.
This exact limiting-parameter comparison explains the obstruction on p. 1234. -/
theorem uniform_weight_strict_loss :
    log (6 : ℝ) / (1 / 2 : ℝ) < log (8 / 3 : ℝ) / (1 / 6 : ℝ) := by
  have h : log (6 : ℝ) < log ((8 / 3 : ℝ) ^ 3) :=
    log_lt_log (by norm_num) (by norm_num)
  rw [log_pow] at h
  norm_num at h ⊢
  linarith

/-- The coarse Mertens endpoint errors do not recover the log-squared error on p. 1234. -/
theorem coarse_reciprocal_error_too_large (L : ℝ) (hL : 22000 ≤ L) :
    64 / L ^ 2 < 12 / (L / 8) + 13 / (L / 3) := by
  have hLp : 0 < L := by linarith
  field_simp
  nlinarith

/-- The paper threshold exceeds the elementary 4e18 endpoint used by Lemma 13. -/
theorem paper_threshold18 : (4e18 : ℝ) ≤ exp (exp 10) := by
  calc
    (4e18 : ℝ) ≤ (1e8 : ℝ) ^ 3 := by norm_num
    _ ≤ exp 2753 ^ 3 := pow_le_pow_left₀ (by norm_num) qs_exp2753_gt_1e8.le 3
    _ = exp (3 * 2753) := by rw [← exp_nat_mul]; norm_num
    _ ≤ exp (exp 10) := exp_le_exp.mpr (by linarith [qs_exp10_gt])

/-- The endpoint factor q over q minus one decreases with its real endpoint, p. 1234. -/
theorem rX_antitone (X Y : ℝ) (hX : 1 < X) (hXY : X ≤ Y) : rX Y ≤ rX X := by
  have hzX : 1 < X ^ (1 / 8 : ℝ) := one_lt_rpow hX (by norm_num)
  have hzY : 1 < Y ^ (1 / 8 : ℝ) := one_lt_rpow (hX.trans_le hXY) (by norm_num)
  have hzXY := rpow_le_rpow (by linarith : 0 ≤ X) hXY (by norm_num : (0 : ℝ) ≤ 1 / 8)
  unfold rX
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Transfer the density correction to X2 by Mathlib logarithmic monotonicity, p. 1232. -/
theorem density_at_threshold (n : ℕ) (X : ℝ) (hX : exp (exp 10) ≤ X) (hn : X ≤ (n : ℝ))
    (hd : density n ≤ 8 * UNfull n / log n * (1 + 0.62 * log n / (n : ℝ) ^ (1 / 16 : ℝ))) :
    density n ≤ 8 * UNfull n / log n * (1 + 0.62 * log X / X ^ (1 / 16 : ℝ)) := by
  have hX0 : 0 < X := (exp_pos _).trans_le hX
  have hn1 : (1 : ℝ) < n := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le (hX.trans hn)
  have hLp : 0 < log (n : ℝ) := log_pos hn1
  have hU : 0 < UNfull n := by linarith [two_fifths_le_UNfull n]
  have hth : exp ((1 / 16 : ℝ)⁻¹) ≤ X := by
    norm_num
    exact (exp_le_exp.mpr (by linarith [qs_exp10_gt])).trans hX
  have hmono := log_div_self_rpow_antitoneOn (by norm_num : (0 : ℝ) < 1 / 16)
    hth (hth.trans hn) hn
  dsimp only at hmono
  apply hd.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [mul_div_assoc] using add_le_add (le_refl (1 : ℝ))
    (mul_le_mul_of_nonneg_left hmono (by norm_num : (0 : ℝ) ≤ 0.62))

/-- Replace the running endpoint in the first prime sum by X2, p. 1234.
CONDITIONAL ON the two published prime envelopes. -/
theorem prime_sum_at_threshold (n : ℕ) (α ε C₁ X : ℝ)
    (hX : exp (exp 10) ≤ X) (hn : X ≤ (n : ℝ)) (hev : Even n)
    (hα : 0 < α) (hα1 : α < 1 / 24) (hε : 0 ≤ ε) (hC : 0 ≤ C₁) :
    (∑ q ∈ qRange n, upperCoefficient n q α ε C₁ / ((q : ℝ) - 1)) ≤
      rX X * (exp eulerMascheroniConstant / 4 *
        ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) +
          512 / (kA α * log X ^ 2)) +
        ε * C₁ * exp 2 * hS (kA α) * (log (8 / 3) + 64 / log X ^ 2)) := by
  have hX1 : 1 < X := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hX
  have hX0 : 0 < X := by linarith
  have hn1 : (1 : ℝ) < n := hX1.trans_le hn
  have hLX : 0 < log X := log_pos hX1
  have hLn : 0 < log (n : ℝ) := log_pos hn1
  have hlog := log_le_log hX0 hn
  have ha0 : 0 < 1 / 2 - α := by linarith
  have hk0 : 0 < kA α := by unfold kA; linarith
  have hk2 : kA α ≤ 2 := by unfold kA; linarith
  have hS0 : 0 ≤ hS (kA α) := by unfold hS; rw [if_pos hk2]; positivity
  have hB0 : 0 ≤ ε * C₁ * exp 2 * hS (kA α) := by positivity
  have hden : 0 < 3 - 18 * α := by linarith
  have hratio : 1 ≤ (3 - 8 * α) / (3 - 18 * α) := by
    rw [le_div_iff₀ hden]
    linarith
  have hJ : 0 ≤ log (6 : ℝ) + log ((3 - 8 * α) / (3 - 18 * α)) :=
    add_nonneg (log_nonneg (by norm_num)) (log_nonneg hratio)
  have hr0 : 0 ≤ rX X := by
    have hz1 : 1 < X ^ (1 / 8 : ℝ) := one_lt_rpow hX1 (by norm_num)
    unfold rX
    positivity
  have hmain := main_prime_sum_published n α ε C₁ (hX.trans hn) hev hα hα1 hε hC
  have hid : exp eulerMascheroniConstant / 4 * log n *
      ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / ((1 / 2 - α) * log n) +
        512 / (kA α * log n ^ 3)) =
      exp eulerMascheroniConstant / 4 *
        ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) +
          512 / (kA α * log n ^ 2)) := by
    field_simp
    <;> ring
  rw [hid] at hmain
  apply hmain.trans
  apply mul_le_mul (rX_antitone X n hX1 hn) _ _ hr0
  · apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add le_rfl
      gcongr
    · apply mul_le_mul_of_nonneg_left _ hB0
      apply add_le_add le_rfl
      gcongr
  · positivity

/-- Lemma 13 for the prime q range, CONDITIONAL ON Lemmas 1 to 5 and GRH, p. 1233. -/
theorem prime_residue_sum (h1 : PaperInputs148.Lemma1J) (h2 : PaperInputs148.Lemma2J)
    (h4 : PaperInputs148.Lemma4J) (hMu : PaperInputs148.Lemma5MuJ)
    (h3 : Lemma3J) (hG : GRH) (α A u X : ℝ) (n : ℕ)
    (hα : 0 < α) (hα1 : α < 1 / 24) (hA : 0 < A)
    (hc : Cond19 α A u X) (hX : exp (exp 10) ≤ X) (hn : X ≤ (n : ℝ)) (hev : Even n) :
    (∑ q ∈ qRange n, |residue n q|) ≤ cGJ X * n / log n ^ A := by
  obtain ⟨hH, _, hyH⟩ := quotient_cutoffs h2 α A u X n hα hα1 hA hc hX hn
  apply squarefree_residue_sum h1 h4 hMu h3 hG n X A (qRange n)
    (paper_threshold18.trans hX) hn hA hev hH
  intro q hq
  obtain ⟨hp, hqn, _, hy⟩ := qRange_spec hq
  exact ⟨hp.squarefree, hp.one_le, hy.le.trans hyH, hp.coprime_iff_not_dvd.mpr hqn⟩

/-- The last scalar assembly of display 24, CONDITIONAL ON its four explicit estimates, pp. 1233 and 1234. -/
theorem main_sum_from_estimates (n : ℕ) (α A ε C₁ X : ℝ)
    (hn : (1 : ℝ) < n) (hev : Even n) (hX : 1 < X)
    (hα : 0 < α) (hα1 : α < 1 / 24) (hε : 0 ≤ ε) (hC : 0 ≤ C₁) (hcg : 0 ≤ cGJ X)
    (hcard : ((U7153.Aset n).card : ℝ) ≤ (1 + 5e-5) * n / log n)
    (hdensity : density n ≤ 8 * UNfull n / log n * (1 + 0.62 * log X / X ^ (1 / 16 : ℝ)))
    (hprime : (∑ q ∈ qRange n, upperCoefficient n q α ε C₁ / ((q : ℝ) - 1)) ≤
      rX X * (exp eulerMascheroniConstant / 4 *
        ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) +
          512 / (kA α * log X ^ 2)) +
        ε * C₁ * exp 2 * hS (kA α) * (log (8 / 3) + 64 / log X ^ 2)))
    (hres : (∑ q ∈ qRange n, |residue n q|) ≤ cGJ X * n / log n ^ A) :
    mainSum n α ε C₁ ≤
      8 * (UNfull n * n / log n ^ 2) * l1J α ε C₁ X +
      8 * (UNfull n * n / log n ^ 2) * (l3J α ε C₁ X / log n ^ (A - 1)) := by
  have hLn : 0 < log (n : ℝ) := log_pos hn
  have hLX : 0 < log X := log_pos hX
  have hn0 : (0 : ℝ) < n := by linarith
  have hX0 : 0 < X := by linarith
  have hU : 0 < UNfull n := by linarith [two_fifths_le_UNfull n]
  have hP0 : 0 ≤ ∑ q ∈ qRange n, upperCoefficient n q α ε C₁ / ((q : ℝ) - 1) := by
    apply sum_nonneg
    intro q hq
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (qRange_spec hq).1.two_le
    exact div_nonneg (upperCoefficient_bounds n q α ε C₁ hn hα hα1 hε hC hq).1 (by linarith)
  have hfirst : density n * ((U7153.Aset n).card : ℝ) *
      (∑ q ∈ qRange n, upperCoefficient n q α ε C₁ / ((q : ℝ) - 1)) ≤
      8 * (UNfull n * n / log n ^ 2) * l1J α ε C₁ X := by
    calc
      _ ≤ (8 * UNfull n / log n * (1 + 0.62 * log X / X ^ (1 / 16 : ℝ))) *
          ((1 + 5e-5) * n / log n) *
          (∑ q ∈ qRange n, upperCoefficient n q α ε C₁ / ((q : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hdensity hcard (Nat.cast_nonneg _) (by positivity)) hP0
      _ ≤ (8 * UNfull n / log n * (1 + 0.62 * log X / X ^ (1 / 16 : ℝ))) *
          ((1 + 5e-5) * n / log n) *
          (rX X * (exp eulerMascheroniConstant / 4 *
            ((log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / (1 / 2 - α) +
              512 / (kA α * log X ^ 2)) +
            ε * C₁ * exp 2 * hS (kA α) * (log (8 / 3) + 64 / log X ^ 2))) :=
        mul_le_mul_of_nonneg_left hprime (by positivity)
      _ = _ := by unfold l1J; field_simp <;> ring
  exact (mainSum_abs_bound n α ε C₁ hn hev hα hα1 hε hC).trans
    (add_le_add hfirst (main_residue_normalization n α A ε C₁ X hn hev hX
      hα hα1 hε hC hcg hdensity hres))

/-- Derivative of the lower li approximation used on p. 1228. -/
theorem li_lower_approx_hasDeriv (x : ℝ) (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => t / log t + t / log t ^ 2)
      (1 / log x - 2 / log x ^ 3) x := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < log x := log_pos hx
  convert (((hasDerivAt_id x).div (hasDerivAt_log hx0.ne') hL.ne').add
    ((hasDerivAt_id x).div ((hasDerivAt_log hx0.ne').pow 2) (pow_ne_zero _ hL.ne'))) using 1
  · ext t
    rfl
  · norm_num only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, one_mul]
    field_simp
    <;> ring

/-- Derivative of the upper li approximation used on p. 1228. -/
theorem li_upper_approx_hasDeriv (x : ℝ) (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => t / log t + t / log t ^ 2 + 3 * t / log t ^ 3)
      (1 / log x + 1 / log x ^ 3 - 9 / log x ^ 4) x := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < log x := log_pos hx
  convert ((((hasDerivAt_id x).div (hasDerivAt_log hx0.ne') hL.ne').add
    ((hasDerivAt_id x).div ((hasDerivAt_log hx0.ne').pow 2) (pow_ne_zero _ hL.ne'))).add
    (((hasDerivAt_id x).const_mul 3).div ((hasDerivAt_log hx0.ne').pow 3)
      (pow_ne_zero _ hL.ne'))) using 1
  · ext t
    rfl
  · norm_num only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, one_mul]
    field_simp
    <;> ring

/-- The lower approximation has slope at most the li integrand, p. 1228. -/
theorem li_lower_slope_le (x : ℝ) (hx : 1 < x) :
    1 / log x - 2 / log x ^ 3 ≤ 1 / log x := by
  have hL : 0 < log x := log_pos hx
  have hnonneg : 0 ≤ 2 / log x ^ 3 := by positivity
  linarith

/-- The upper approximation has slope at least the li integrand above exp 9, p. 1228. -/
theorem li_upper_slope_ge (x : ℝ) (hx : exp 9 ≤ x) :
    1 / log x ≤ 1 / log x + 1 / log x ^ 3 - 9 / log x ^ 4 := by
  have hx0 : 0 < x := (exp_pos _).trans_le hx
  have hL : 9 ≤ log x := (le_log_iff_exp_le hx0).mpr hx
  have hLp : 0 < log x := by linarith
  have hle : 9 / log x ^ 4 ≤ (1 : ℝ) / log x ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h := mul_le_mul_of_nonneg_right hL (pow_nonneg hLp.le 3)
    nlinarith
  linarith

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
  have hN := hX.trans hn
  have hn1 : (1 : ℝ) < n := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hN
  have hX1 : 1 < X₂ := (one_lt_exp_iff.mpr (exp_pos 10)).trans_le hX
  have h11 : exp 11 ≤ (n : ℝ) :=
    (exp_le_exp.mpr (by linarith [qs_exp10_gt])).trans hN
  obtain ⟨hliL, hliU⟩ := PublishedInputs232.li_bounds_large n h11
  have hcard := cardinality_upper_of_inputs PublishedInputs232.lemma1_schoenfeld
    PublishedInputs232.lemma4_robin hG n hN hliL hliU
  have hd := density_at_threshold n X₂ hX hn (PublishedInputs232.density_upper n hN hev)
  have hp := prime_sum_at_threshold n α ε C₁ X₂ hX hn hev hα hα1 he0.le hC₁
  have hr := prime_residue_sum PublishedInputs232.lemma1_schoenfeld
    PublishedInputs232.lemma2_theta PublishedInputs232.lemma4_robin PublishedInputs232.lemma5_mu
    h3 hG α A u X₂ n hα hα1 hA hc hX hn hev
  have hcg := (CoefficientsC169.coefficient_ranges X₂ (paper_threshold18.trans hX)).2.2.1
  exact main_sum_from_estimates n α A ε C₁ X₂ hn1 hev hX1 hα hα1 he0.le hC₁
    hcg hcard hd hp hr

/-- LEAF. Sum R_q using the injective qd indexing, p. 1233 after display 23.
Use Lemmas 5 and 13 and the identity for r_q to obtain the l2 contribution.
The absolute value estimate is independent of the sign chosen in the residue identity. -/
theorem total_remainder_bound (α A u X₂ : ℝ) (n : ℕ)
    (hG : GRH) (h3 : Lemma3J) (hα : 0 < α) (hα1 : α < 1 / 24)
    (hA : 0 < A) (hc : Cond19 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    totalRemainder n α u ≤
      8 * (UNfull n * n / log n ^ 2) * (l2J X₂ / log n ^ (A - 3)) := by
  exact total_remainder_of_inputs PublishedInputs232.lemma1_schoenfeld
    PublishedInputs232.lemma2_theta PublishedInputs232.lemma4_robin
    PublishedInputs232.lemma5_mu PublishedInputs232.lemma5_phi
    α A u X₂ n hG h3 hα hα1 hA hc hX hn hev

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

#print axioms LeanLab.BS2022GRH.DecompC169b.qRange_spec

#print axioms LeanLab.BS2022GRH.DecompC169b.quotientDivisors_spec

#print axioms LeanLab.BS2022GRH.DecompC169b.quotientDivisors_coprime

#print axioms LeanLab.BS2022GRH.DecompC169b.quotientPairs_injective

#print axioms LeanLab.BS2022GRH.DecompC169b.quotientPairs_squarefree

#print axioms LeanLab.BS2022GRH.DecompC169b.quotientResidue_abs

#print axioms LeanLab.BS2022GRH.DecompC169b.totalRemainder_split

#print axioms LeanLab.BS2022GRH.DecompC169b.squarefree_count_le

#print axioms LeanLab.BS2022GRH.DecompC169b.squarefree_totient_sum_le

#print axioms LeanLab.BS2022GRH.DecompC169b.product_residue_sum_le

#print axioms LeanLab.BS2022GRH.DecompC169b.progressionPrimes_eq

#print axioms LeanLab.BS2022GRH.DecompC169b.progressionError_one

#print axioms LeanLab.BS2022GRH.DecompC169b.half_totient

#print axioms LeanLab.BS2022GRH.DecompC169b.progression_error_le

#print axioms LeanLab.BS2022GRH.DecompC169b.squarefree_residue_sum_raw

#print axioms LeanLab.BS2022GRH.DecompC169b.cond19_at

#print axioms LeanLab.BS2022GRH.DecompC169b.smallProduct_le_exp_theta

#print axioms LeanLab.BS2022GRH.DecompC169b.quotient_cutoffs

#print axioms LeanLab.BS2022GRH.DecompC169b.quotient_product_lt

#print axioms LeanLab.BS2022GRH.DecompC169b.Mphi_sqrt_log_le

#print axioms LeanLab.BS2022GRH.DecompC169b.UNfull_invTw_ge_one

#print axioms LeanLab.BS2022GRH.DecompC169b.remainder_normalization

#print axioms LeanLab.BS2022GRH.DecompC169b.total_remainder_of_inputs

#print axioms LeanLab.BS2022GRH.DecompC169b.mainSum_identity

#print axioms LeanLab.BS2022GRH.DecompC169b.density_nonneg

#print axioms LeanLab.BS2022GRH.DecompC169b.reciprocal_log_hasDeriv

#print axioms LeanLab.BS2022GRH.DecompC169b.weighted_prime_abel

#print axioms LeanLab.BS2022GRH.DecompC169b.quotientParameter_eq

#print axioms LeanLab.BS2022GRH.DecompC169b.quotientParameter_range

#print axioms LeanLab.BS2022GRH.DecompC169b.hS_quotient_le

#print axioms LeanLab.BS2022GRH.DecompC169b.upperCoefficient_bounds

#print axioms LeanLab.BS2022GRH.DecompC169b.mainSum_abs_bound

#print axioms LeanLab.BS2022GRH.DecompC169b.squarefree_residue_sum

#print axioms LeanLab.BS2022GRH.DecompC169b.prime_denominator_le

#print axioms LeanLab.BS2022GRH.DecompC169b.upperCoefficient_log_le

#print axioms LeanLab.BS2022GRH.DecompC169b.main_prime_sum_bound

#print axioms LeanLab.BS2022GRH.DecompC169b.log_quotientLevel_pos

#print axioms LeanLab.BS2022GRH.DecompC169b.main_prime_sum_published

#print axioms LeanLab.BS2022GRH.DecompC169b.cardinality_upper_of_inputs

#print axioms LeanLab.BS2022GRH.DecompC169b.main_residue_normalization

#print axioms LeanLab.BS2022GRH.DecompC169b.uniform_weight_strict_loss

#print axioms LeanLab.BS2022GRH.DecompC169b.coarse_reciprocal_error_too_large

#print axioms LeanLab.BS2022GRH.DecompC169b.paper_threshold18

#print axioms LeanLab.BS2022GRH.DecompC169b.rX_antitone

#print axioms LeanLab.BS2022GRH.DecompC169b.density_at_threshold

#print axioms LeanLab.BS2022GRH.DecompC169b.prime_sum_at_threshold

#print axioms LeanLab.BS2022GRH.DecompC169b.prime_residue_sum

#print axioms LeanLab.BS2022GRH.DecompC169b.main_sum_from_estimates

#print axioms LeanLab.BS2022GRH.DecompC169b.li_lower_approx_hasDeriv

#print axioms LeanLab.BS2022GRH.DecompC169b.li_upper_approx_hasDeriv

#print axioms LeanLab.BS2022GRH.DecompC169b.li_lower_slope_le

#print axioms LeanLab.BS2022GRH.DecompC169b.li_upper_slope_ge
