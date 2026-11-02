import LeanLab.RieselVaughan1983.Lemma5Final
import LeanLab.RieselVaughan1983.SieveWeights93

/-! Decomposition of Lemma 5 at the first row used by the lab.
AI wrote the Lean code. Binary Goldbach is OPEN.
The assembly has no local sorry. Its three analytic leaves remain unproved.
The sieve leaf uses Montgomery and Vaughan 1973 Corollary 1.
The weighted leaf uses Lemma 4 and the printed constant brackets.
-/

namespace LeanLab.RieselVaughan1983.Decomp93
open Real Finset
noncomputable section
open SieveWeights93

/-- The explicit lower polynomial from pages 47 and 54 at lambda = 3/2. -/
def lowerPolynomial (x : ℝ) : ℝ :=
  log x ^ 2 + (8463433 / 1000000) * log x - 9260623 / 1000000 -
    (9310077 / 1000) * x ^ (-(1 / 6 : ℝ)) -
    (2950889 / 100000) * x ^ (-(1 / 2 : ℝ))

/-- LEAF. Page 54 application of Montgomery and Vaughan 1973 Corollary 1,
followed by equations 3.12 and 3.18, for an even positive shift. The published
source is The large sieve, Mathematika 20, 1973, pages 119 to 134. -/
theorem mv_sieve (x : ℝ) (hx : exp 24 ≤ x) (h : ℕ) (hh : 0 < h) (he : Even h) :
    (#((Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ (p + h).Prime)) : ℝ) ≤
      x / Sn h (sqrt (2 / 3 * x)) + 2 * sqrt x := by
  sorry

/-- The odd-prime local weight `Lemma2.localWeight`, continued by `1` off the primes. -/
private def lw (r : ℕ) : ℝ := if r = 2 then 1 else 2 / ((r : ℝ) - 2)

/-- A squarefree coefficient system with local factors `a`. -/
private def cf (a : ℕ → ℝ) (q : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius q : ℤ)) : ℝ) ^ 2 * ∏ p ∈ q.primeFactors, a p

/-- The coefficient system of equation 3.12 with the primes of `S` at `1/(p-1)`. -/
private def aS (S : Finset ℕ) (r : ℕ) : ℝ := if r ∈ S then 1 / ((r : ℝ) - 1) else lw r

/-- The sieved sum with the coefficient system `aS S`. -/
private def Phi (z : ℝ) (S : Finset ℕ) : ℝ :=
  ∑ q ∈ Icc 1 ⌊z⌋₊, cf (aS S) q / (1 + q / z)

private lemma lw_eq_localWeight {p : ℕ} (hp : p.Prime) :
    lw p = Lemma2.localWeight p := rfl

private lemma lw_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ lw p := by
  have hp1 : 1 ≤ p := by have := hp.two_le; omega
  simp only [lw]
  split_ifs with h
  · norm_num
  · have hlt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h)
    have h2 : (2 : ℝ) < (p : ℝ) := by exact_mod_cast hlt
    exact div_nonneg (by norm_num) (by linarith)

private lemma cf_nonneg (a : ℕ → ℝ) (ha : ∀ p, p.Prime → 0 ≤ a p) (q : ℕ) :
    0 ≤ cf a q := by
  unfold cf
  refine mul_nonneg (sq_nonneg _) (prod_nonneg ?_)
  intro p hp
  exact ha p (Nat.prime_of_mem_primeFactors hp)

private lemma cf_mul_prime (a : ℕ → ℝ) {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hpm : ¬ p ∣ m) : cf a (m * p) = cf a m * a p := by
  have hcop : Nat.Coprime m p := ((hp.coprime_iff_not_dvd).mpr hpm).symm
  have hpf : (m * p).primeFactors = insert p m.primeFactors := by
    rw [Nat.primeFactors_mul hm hp.ne_zero, hp.primeFactors, Finset.union_comm,
      Finset.singleton_union]
  have hpnot : p ∉ m.primeFactors := by
    rw [Nat.mem_primeFactors]
    exact fun h => hpm h.2.1
  have hmu := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime
    ArithmeticFunction.isMultiplicative_moebius hcop
  have hmp : ArithmeticFunction.moebius p = -1 := ArithmeticFunction.moebius_apply_prime hp
  unfold cf
  rw [hpf, Finset.prod_insert hpnot, hmu, hmp]
  push_cast
  ring

private lemma cf_zero_sq (a : ℕ → ℝ) {p m : ℕ} (hp : p.Prime) : cf a (p * p * m) = 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [cf]
  · have hns : ¬ Squarefree (p * p * m) := by
      intro hs
      have hd := Nat.squarefree_iff_prime_squarefree.mp hs p hp
      exact hd ⟨m, by ring⟩
    unfold cf
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]
    simp

/-- Changing the local factor at `p` scales the system by the matching ratio. -/
private lemma cf_cons (a b : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (hb : b p ≠ 0) (q : ℕ)
    (h : ∀ r ∈ q.primeFactors, r ≠ p → a r = b r) :
    cf a q = (if p ∣ q then a p / b p else 1) * cf b q := by
  by_cases hq : q = 0
  · subst hq
    simp [cf]
  · by_cases hpq : p ∣ q
    · have hmem : p ∈ q.primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨hp, hpq, hq⟩
      have hsplit : ∀ c : ℕ → ℝ, ∏ r ∈ q.primeFactors, c r
          = c p * ∏ r ∈ q.primeFactors.erase p, c r := by
        intro c
        conv_lhs => rw [← Finset.insert_erase hmem]
        rw [Finset.prod_insert (Finset.notMem_erase p q.primeFactors)]
      have hagree : ∏ r ∈ q.primeFactors.erase p, a r
          = ∏ r ∈ q.primeFactors.erase p, b r := by
        apply Finset.prod_congr rfl
        intro r hr
        exact h r (Finset.mem_of_mem_erase hr) (Finset.ne_of_mem_erase hr)
      unfold cf
      rw [if_pos hpq, hsplit a, hsplit b, hagree]
      field_simp
      try ring
    · have hab : ∏ r ∈ q.primeFactors, a r = ∏ r ∈ q.primeFactors, b r := by
        apply Finset.prod_congr rfl
        intro r hr
        have hrp : r ≠ p := by
          intro hEq
          exact hpq (hEq ▸ (Nat.mem_primeFactors.mp hr).2.1)
        exact h r hr hrp
      unfold cf
      rw [if_neg hpq, one_mul, hab]

/-- The pairing lemma: the paired half of the sum is bounded by the unpaired half. -/
private lemma sum_shift_le (p : ℕ) (hp : p.Prime) (N : ℕ) (z : ℝ) (hz : 0 < z)
    (h : ℕ → ℝ) (hnn : ∀ q, 0 ≤ h q)
    (hinv : ∀ m, ¬ p ∣ m → h (p * m) = h m)
    (hann : ∀ m, h (p * p * m) = 0) :
    (∑ q ∈ (Icc 1 N).filter (fun q => p ∣ q), h q / (1 + q / z))
      ≤ ∑ q ∈ (Icc 1 N).filter (fun q => ¬ p ∣ q), h q / (1 + q / z) := by
  have hp1 : 1 ≤ p := by have := hp.two_le; omega
  set C : Finset ℕ := (Icc 1 N).filter (fun m => p * m ≤ N) with hC
  have himg : (Icc 1 N).filter (fun q => p ∣ q) = C.image (fun m => p * m) := by
    ext q
    simp only [hC, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, hdiv⟩
      have hq0 : 0 < q := h1
      have hdm : q / p * p = q := Nat.div_mul_cancel hdiv
      refine ⟨q / p, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · have hne : q / p ≠ 0 := by
          intro h0
          rw [h0, Nat.zero_mul] at hdm
          omega
        exact Nat.one_le_iff_ne_zero.mpr hne
      · exact le_trans (Nat.div_le_self q p) h2
      · calc p * (q / p) = q / p * p := Nat.mul_comm _ _
          _ = q := hdm
          _ ≤ N := h2
      · rw [Nat.mul_comm]; exact hdm
    · rintro ⟨m, ⟨⟨h1, h2⟩, hmN⟩, rfl⟩
      have hp0 : 0 < p := hp.pos
      have hm0 : 0 < m := h1
      have hpos : 0 < p * m := Nat.mul_pos hp0 hm0
      exact ⟨⟨hpos, hmN⟩, ⟨m, rfl⟩⟩
  have hinj : ∀ x ∈ C, ∀ y ∈ C, p * x = p * y → x = y :=
    fun x _ y _ hxy => Nat.mul_left_cancel hp.pos hxy
  rw [himg, Finset.sum_image hinj]
  simp only [Nat.cast_mul]
  rw [← Finset.sum_filter_add_sum_filter_not (s := C) (p := fun m => p ∣ m)
    (f := fun m => h (p * m) / (1 + (p : ℝ) * (m : ℝ) / z))]
  have hzero : ∑ m ∈ C.filter (fun m => p ∣ m),
      h (p * m) / (1 + (p : ℝ) * (m : ℝ) / z) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨m', rfl⟩ := hm.2
    rw [show p * (p * m') = p * p * m' by ring, hann]
    simp
  rw [hzero, zero_add]
  have hstep : ∑ m ∈ C.filter (fun m => ¬ p ∣ m),
        h (p * m) / (1 + (p : ℝ) * (m : ℝ) / z)
      ≤ ∑ m ∈ C.filter (fun m => ¬ p ∣ m), h m / (1 + m / z) := by
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.mem_filter] at hm
    rw [hinv m hm.2]
    apply div_le_div_of_nonneg_left (hnn m) (by positivity)
    have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hmle : (m : ℝ) ≤ (p : ℝ) * (m : ℝ) := by nlinarith
    have := div_le_div_of_nonneg_right hmle hz.le
    linarith
  refine hstep.trans ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    rw [Finset.mem_filter] at hm
    have hmC : m ∈ C := hm.1
    rw [hC, Finset.mem_filter, Finset.mem_Icc] at hmC
    rw [Finset.mem_filter]
    exact ⟨by rw [Finset.mem_Icc]; exact hmC.1, hm.2⟩
  · intro m _ _
    exact div_nonneg (hnn m) (by positivity)

/-- The single prime step: replacing the local factor `2/(p-2)` by `1/(p-1)` costs at most `(p-1)/(p-2)`. -/
private lemma beta_step (p : ℕ) (hp : p.Prime) (h2 : 2 < p) (N : ℕ) (z : ℝ) (hz : 0 < z)
    (b : ℕ → ℝ) (hb : ∀ r, r.Prime → 0 ≤ b r)
    (v : ℝ) (hvb : b p = v) (hv0 : 0 < v) (hv1 : v ≤ 1) :
    (∑ q ∈ Icc 1 N, (if p ∣ q then 2 / ((p : ℝ) - 2) else 1) * cf b q / (1 + q / z))
      ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) *
        ∑ q ∈ Icc 1 N, (if p ∣ q then 1 / ((p : ℝ) - 1) else 1) * cf b q / (1 + q / z) := by
  have hp2R : (2 : ℝ) < (p : ℝ) := by exact_mod_cast h2
  have hp2pos : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  set h : ℕ → ℝ := fun q => if p ∣ q then cf b q / v else cf b q with hh
  have hnn : ∀ q, 0 ≤ h q := by
    intro q
    simp only [hh]
    split_ifs with hq
    · exact div_nonneg (cf_nonneg b hb q) hv0.le
    · exact cf_nonneg b hb q
  have hinv : ∀ m, ¬ p ∣ m → h (p * m) = h m := by
    intro m hm
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (Nat.dvd_zero p)
    have hpdiv : p ∣ p * m := ⟨m, rfl⟩
    have hcf : cf b (p * m) = cf b m * v := by
      rw [Nat.mul_comm p m, cf_mul_prime b hp hm0 hm, hvb]
    simp only [hh, if_pos hpdiv, if_neg hm, hcf]
    field_simp
    try ring
  have hann : ∀ m, h (p * p * m) = 0 := by
    intro m
    have hpdiv : p ∣ p * p * m := ⟨p * m, by ring⟩
    simp only [hh, if_pos hpdiv, cf_zero_sq b hp]
    simp
  have hkey := sum_shift_le p hp N z hz h hnn hinv hann
  set g : ℕ → ℝ := fun q => cf b q / (1 + q / z) with hg
  have hg0 : ∀ q, 0 ≤ g q := by
    intro q; exact div_nonneg (cf_nonneg b hb q) (by positivity)
  have hS2 : ∑ q ∈ (Icc 1 N).filter (fun q => p ∣ q), h q / (1 + q / z)
      = (∑ q ∈ (Icc 1 N).filter (fun q => p ∣ q), g q) / v := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_filter] at hq
    simp only [hh, hg, if_pos hq.2]
    rw [div_div, div_div, mul_comm]
  have hS1 : ∑ q ∈ (Icc 1 N).filter (fun q => ¬ p ∣ q), h q / (1 + q / z)
      = ∑ q ∈ (Icc 1 N).filter (fun q => ¬ p ∣ q), g q := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mem_filter] at hq
    simp only [hh, hg, if_neg hq.2]
  rw [hS2, hS1] at hkey
  set S2 : ℝ := ∑ q ∈ (Icc 1 N).filter (fun q => p ∣ q), g q with hS2def
  set S1 : ℝ := ∑ q ∈ (Icc 1 N).filter (fun q => ¬ p ∣ q), g q with hS1def
  have hS1nonneg : 0 ≤ S1 := Finset.sum_nonneg fun q _ => hg0 q
  have hle : S2 ≤ S1 := by
    have h2' : S2 / v ≤ S1 := hkey
    have hv : S2 = S2 / v * v := by field_simp; try ring
    rw [hv]
    calc S2 / v * v ≤ S1 * v := mul_le_mul_of_nonneg_right h2' hv0.le
      _ ≤ S1 * 1 := mul_le_mul_of_nonneg_left hv1 hS1nonneg
      _ = S1 := mul_one S1
  have hsplit : ∀ c : ℝ, ∑ q ∈ Icc 1 N, (if p ∣ q then c else 1) * g q
      = c * S2 + S1 := by
    intro c
    rw [← Finset.sum_filter_add_sum_filter_not (s := Icc 1 N) (p := fun q => p ∣ q)
      (f := fun q => (if p ∣ q then c else 1) * g q), hS2def, hS1def, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mem_filter] at hq
      rw [if_pos hq.2]
    · apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mem_filter] at hq
      rw [if_neg hq.2, one_mul]
  have e1 : ∑ q ∈ Icc 1 N, (if p ∣ q then 2 / ((p : ℝ) - 2) else 1) * cf b q / (1 + q / z)
      = 2 / ((p : ℝ) - 2) * S2 + S1 := by
    rw [← hsplit (2 / ((p : ℝ) - 2))]
    apply Finset.sum_congr rfl
    intro q _
    simp only [hg]
    ring
  have e2 : ∑ q ∈ Icc 1 N, (if p ∣ q then 1 / ((p : ℝ) - 1) else 1) * cf b q / (1 + q / z)
      = 1 / ((p : ℝ) - 1) * S2 + S1 := by
    rw [← hsplit (1 / ((p : ℝ) - 1))]
    apply Finset.sum_congr rfl
    intro q _
    simp only [hg]
    ring
  rw [e1, e2]
  have hcoef : ((p : ℝ) - 1) / ((p : ℝ) - 2) * (1 / ((p : ℝ) - 1) * S2 + S1)
      = 2 / ((p : ℝ) - 2) * S2 + S1 + (S1 - S2) / ((p : ℝ) - 2) := by
    have h1 : ((p : ℝ) - 1) ≠ 0 := by
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      exact this.ne'
    have h2 : ((p : ℝ) - 2) ≠ 0 := hp2pos.ne'
    field_simp
    ring
  rw [hcoef]
  have hlast : 0 ≤ (S1 - S2) / ((p : ℝ) - 2) := div_nonneg (by linarith) hp2pos.le
  linarith

private lemma moebius_cast_apply (q : ℕ) :
    ((ArithmeticFunction.moebius : ArithmeticFunction ℝ) q)
      = ((ArithmeticFunction.moebius q : ℤ) : ℝ) := rfl

private lemma cf_lw_eq_sieveCoeff (q : ℕ) : cf lw q = Lemma2.sieveCoeff q := by
  by_cases hq : q = 0
  · subst hq
    simp [cf, Lemma2.sieveCoeff]
  · rw [Lemma2.sieveCoeff, ArithmeticFunction.pmul_apply,
      ArithmeticFunction.ppow_apply (by norm_num : 0 < 2),
      ArithmeticFunction.prodPrimeFactors_apply hq]
    unfold cf
    have h1 : ∀ p ∈ q.primeFactors, lw p = Lemma2.localWeight p :=
      fun p hp => lw_eq_localWeight (Nat.prime_of_mem_primeFactors hp)
    rw [Finset.prod_congr rfl h1, moebius_cast_apply]

private lemma aS_empty : aS ∅ = lw := by
  ext r
  simp [aS]

/-- Equation 3.12's coefficient is the system with the odd primes of `n` at `1/(p-1)`. -/
private lemma cf_aS_eq_coefficient (n : ℕ) (hn : 0 < n) (he : Even n) (q : ℕ) :
    cf (aS (n.primeFactors.filter (2 < ·))) q = coefficient n q := by
  obtain ⟨k, hk⟩ := he
  have h2dvd : 2 ∣ n := ⟨k, by omega⟩
  by_cases hq : q = 0
  · subst hq
    simp [cf, coefficient]
  · unfold cf coefficient
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ n ↔ p ∈ n.primeFactors := by
      rw [Nat.mem_primeFactors]
      exact ⟨fun h => ⟨hpprime, h, hn.ne'⟩, fun h => h.2.1⟩
    simp only [aS]
    by_cases hmem : p ∈ n.primeFactors.filter (2 < ·)
    · have hpdiv : p ∣ n := hpdvd.mpr (Finset.mem_filter.mp hmem).1
      rw [if_pos hmem, localFactor, if_pos hpdiv]
    · rw [if_neg hmem]
      by_cases hp2 : p = 2
      · subst hp2
        rw [lw, if_pos rfl, localFactor, if_pos h2dvd]
        norm_num
      · have hndiv : ¬ p ∣ n := by
          intro hd
          exact hmem (Finset.mem_filter.mpr ⟨hpdvd.mp hd, by have := hpprime.two_le; omega⟩)
        rw [lw, if_neg hp2, localFactor, if_neg hndiv]


/-- The local step, written for the running coefficient systems. -/
private lemma Phi_step (z : ℝ) (hz : 0 < z) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) (p : ℕ) (hpP : p ∈ P) (S : Finset ℕ) (hpS : p ∉ S) :
    Phi z S ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) * Phi z (insert p S) := by
  obtain ⟨hp, h2⟩ := hP p hpP
  set b : ℕ → ℝ := fun r => if r = p then 1 else aS (insert p S) r with hbdef
  have hbp : b p = 1 := by simp [hbdef]
  have hb0 : ∀ r, r.Prime → 0 ≤ b r := by
    intro r hr
    by_cases hrp : r = p
    · subst hrp
      rw [hbp]; norm_num
    · simp only [hbdef, if_neg hrp]
      by_cases hmem : r ∈ insert p S
      · simp only [aS, if_pos hmem]
        have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.two_le
        exact div_nonneg zero_le_one (by linarith)
      · simp only [aS, if_neg hmem]
        exact lw_nonneg hr
  have hstep := beta_step p hp h2 ⌊z⌋₊ z hz b hb0 1 hbp one_pos le_rfl
  have hR : (∑ q ∈ Icc 1 ⌊z⌋₊,
        (if p ∣ q then 1 / ((p : ℝ) - 1) else 1) * cf b q / (1 + q / z))
      = Phi z (insert p S) := by
    rw [Phi]
    apply Finset.sum_congr rfl
    intro q _
    have hratio : cf (aS (insert p S)) q
        = (if p ∣ q then aS (insert p S) p / b p else 1) * cf b q :=
      cf_cons (aS (insert p S)) b hp (by rw [hbp]; norm_num) q
        (fun r _ hrp => by simp only [hbdef, if_neg hrp])
    have hval : aS (insert p S) p / b p = 1 / ((p : ℝ) - 1) := by
      rw [hbp, div_one]
      simp [aS]
    rw [hratio, hval]
  have hL : (∑ q ∈ Icc 1 ⌊z⌋₊,
        (if p ∣ q then 2 / ((p : ℝ) - 2) else 1) * cf b q / (1 + q / z)) = Phi z S := by
    rw [Phi]
    apply Finset.sum_congr rfl
    intro q _
    have hratio : cf (aS S) q = (if p ∣ q then aS S p / b p else 1) * cf b q :=
      cf_cons (aS S) b hp (by rw [hbp]; norm_num) q (fun r _ hrp => by
        simp only [hbdef, if_neg hrp, aS]
        by_cases hrs : r ∈ S
        · rw [if_pos hrs, if_pos (Finset.mem_insert_of_mem hrs)]
        · rw [if_neg hrs, if_neg]
          intro hcon
          rcases Finset.mem_insert.mp hcon with h' | h'
          · exact hrp h'
          · exact hrs h')
    have hval : aS S p / b p = 2 / ((p : ℝ) - 2) := by
      rw [hbp, div_one]
      simp only [aS, if_neg hpS, lw, if_neg (by omega : ¬ p = 2)]
    rw [hratio, hval]
  rw [hL, hR] at hstep
  exact hstep

private lemma Phi_bound (z : ℝ) (hz : 0 < z) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 2 < p) :
    ∀ T : Finset ℕ, T ⊆ P →
      Phi z (P \ T) ≤ (∏ p ∈ T, ((p : ℝ) - 1) / ((p : ℝ) - 2)) * Phi z P := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
      intro _
      simp
  | insert a T ha ih =>
      intro hsub
      have haP : a ∈ P := hsub (Finset.mem_insert_self a T)
      have hTP : T ⊆ P := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have haS : a ∉ P \ insert a T := by
        intro hcon
        rw [Finset.mem_sdiff] at hcon
        exact hcon.2 (Finset.mem_insert_self a T)
      have hins : insert a (P \ insert a T) = P \ T := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_sdiff]
        constructor
        · rintro (rfl | ⟨hxP, hxnot⟩)
          · exact ⟨haP, ha⟩
          · exact ⟨hxP, fun hxT => hxnot (Or.inr hxT)⟩
        · rintro ⟨hxP, hxT⟩
          by_cases hxa : x = a
          · exact Or.inl hxa
          · refine Or.inr ⟨hxP, ?_⟩
            intro hcon
            rcases hcon with h' | h'
            · exact hxa h'
            · exact hxT h'
      have hstep := Phi_step z hz P hP a haP (P \ insert a T) haS
      rw [hins] at hstep
      have hih := ih hTP
      have h2R : (2 : ℝ) < (a : ℝ) := by exact_mod_cast (hP a haP).2
      have hbe : 0 ≤ ((a : ℝ) - 1) / ((a : ℝ) - 2) :=
        div_nonneg (by linarith) (by linarith)
      calc Phi z (P \ insert a T)
          ≤ ((a : ℝ) - 1) / ((a : ℝ) - 2) * Phi z (P \ T) := hstep
        _ ≤ ((a : ℝ) - 1) / ((a : ℝ) - 2) *
              ((∏ p ∈ T, ((p : ℝ) - 1) / ((p : ℝ) - 2)) * Phi z P) :=
            mul_le_mul_of_nonneg_left hih hbe
        _ = (∏ p ∈ insert a T, ((p : ℝ) - 1) / ((p : ℝ) - 2)) * Phi z P := by
            rw [Finset.prod_insert ha]; ring

/-- LEAF. Page 51 equation 3.13, with the product written as 1 divided by wt n. -/
theorem sum_comparison (n : ℕ) (hn : 0 < n) (he : Even n) (z : ℝ) (hz : 1 ≤ z) :
    Lemma3.S2 z / wt n ≤ Sn n z := by
  have hz0 : 0 < z := by linarith
  have hP : ∀ p ∈ n.primeFactors.filter (2 < ·), p.Prime ∧ 2 < p := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact ⟨Nat.prime_of_mem_primeFactors hp.1, hp.2⟩
  have hbound := Phi_bound z hz0 (n.primeFactors.filter (2 < ·)) hP
    (n.primeFactors.filter (2 < ·)) (Finset.Subset.refl _)
  rw [Finset.sdiff_self] at hbound
  have hEmpty : Phi z ∅ = Lemma3.S2 z := by
    rw [Phi, aS_empty, Lemma3.S2]
    exact Finset.sum_congr rfl fun q _ => by rw [cf_lw_eq_sieveCoeff]
  have hSn : Phi z (n.primeFactors.filter (2 < ·)) = Sn n z := by
    rw [Phi, Sn]
    exact Finset.sum_congr rfl fun q _ => by rw [cf_aS_eq_coefficient n hn he]
  have hprodpos : 0 < ∏ p ∈ n.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    apply Finset.prod_pos
    intro p hp
    have h2R : (2 : ℝ) < (p : ℝ) := by exact_mod_cast (hP p hp).2
    exact div_pos (by linarith) (by linarith)
  rw [hEmpty, hSn] at hbound
  simp only [wt]
  rw [div_le_iff₀ hprodpos, mul_comm]
  exact hbound

/-- Page 54 equation 3.19 for the interval 0 < p ≤ x.
CONDITIONAL ON mv_sieve and sum_comparison. -/
theorem sieve319 (x : ℝ) (hx : exp 24 ≤ x) (h : ℕ) (hh : 0 < h) :
    (#((Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ (p + h).Prime)) : ℝ) ≤
      (x / Lemma3.S2 (sqrt (2 / 3 * x)) + 2 * sqrt x) * wt h := by
  have hx25 : (25 : ℝ) ≤ x := by linarith [add_one_le_exp (24 : ℝ)]
  have hx0 : 0 < x := by linarith
  have hz : 1 ≤ sqrt (2 / 3 * x) := one_le_sqrt.mpr (by linarith)
  have hs := S2_pos _ hz
  have hw := one_le_wt h
  have hwp : 0 < wt h := by linarith
  have hroot : 1 ≤ sqrt x := one_le_sqrt.mpr (by linarith)
  by_cases he : Even h
  · have hsn := Sn_pos h he _ hz
    have hcomp := (div_le_iff₀ hwp).mp (sum_comparison h hh he _ hz)
    have hdiv : x / Sn h (sqrt (2 / 3 * x)) ≤
        x / Lemma3.S2 (sqrt (2 / 3 * x)) * wt h := by
      apply (div_le_iff₀ hsn).mpr
      calc x = x / Lemma3.S2 (sqrt (2 / 3 * x)) * Lemma3.S2 (sqrt (2 / 3 * x)) :=
          (div_mul_cancel₀ x hs.ne').symm
        _ ≤ x / Lemma3.S2 (sqrt (2 / 3 * x)) * (Sn h (sqrt (2 / 3 * x)) * wt h) :=
          mul_le_mul_of_nonneg_left hcomp (div_nonneg hx0.le hs.le)
        _ = _ := by ring
    have hrootw : 2 * sqrt x ≤ 2 * sqrt x * wt h :=
      le_mul_of_one_le_right (by positivity) hw
    calc _ ≤ x / Sn h (sqrt (2 / 3 * x)) + 2 * sqrt x := mv_sieve x hx h hh he
      _ ≤ _ := by nlinarith
  · have hcount := odd_shift_count x h he
    have hmain : 0 ≤ x / Lemma3.S2 (sqrt (2 / 3 * x)) := by positivity
    have hwmain : x / Lemma3.S2 (sqrt (2 / 3 * x)) + 2 * sqrt x ≤
        (x / Lemma3.S2 (sqrt (2 / 3 * x)) + 2 * sqrt x) * wt h :=
      le_mul_of_one_le_right (by positivity) hw
    linarith

/-- LEAF. Page 54 application of Lemma 4 with lambda = 3/2, using the lower
A6 and A7 brackets and the upper A8 and A9 brackets in equations 2.20 to 2.22. -/
theorem weighted_lower (x : ℝ) (hx : exp 24 ≤ x) :
    lowerPolynomial x < 8 * Ctw * Lemma3.S2 (sqrt (2 / 3 * x)) := by
  sorry

/-- LEAF. Page 55 bound F x > B at the row L = 24, B = 0.97.
This is stated after multiplication by the positive log x. -/
theorem row24 (x : ℝ) (hx : exp 24 ≤ x) :
    log x * (97 / 100 + log x) < lowerPolynomial x := by

  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos 24) hx
  have hl : 24 ≤ log x := (le_log_iff_exp_le hx0).mpr hx
  have he4 : (5459 / 100 : ℝ) ≤ exp 4 := by
    have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
      exp_one_gt_d9.le 4
    norm_num at he
    linarith
  have he12 : (100000 : ℝ) ≤ exp 12 := by
    have he := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
      exp_one_gt_d9.le 12
    norm_num at he
    linarith
  have hr6 : x ^ (-(1 / 6 : ℝ)) ≤ 100 / 5459 := by
    rw [rpow_def_of_pos hx0, show log x * -(1 / 6 : ℝ) = -(log x / 6) by ring,
      exp_neg]
    have he : (5459 / 100 : ℝ) ≤ exp (log x / 6) :=
      he4.trans (exp_le_exp.mpr (by linarith))
    apply (inv_le_iff_one_le_mul₀ (exp_pos _)).mpr
    nlinarith
  have hr2 : x ^ (-(1 / 2 : ℝ)) ≤ 1 / 100000 := by
    rw [rpow_def_of_pos hx0, show log x * -(1 / 2 : ℝ) = -(log x / 2) by ring,
      exp_neg]
    have he : (100000 : ℝ) ≤ exp (log x / 2) :=
      he12.trans (exp_le_exp.mpr (by linarith))
    apply (inv_le_iff_one_le_mul₀ (exp_pos _)).mpr
    nlinarith
  unfold lowerPolynomial
  nlinarith

/-- LEAF. Page 55 equation 3.21 and its displayed equivalent at L = 24, A = 0. -/
theorem comparison24 (x : ℝ) (hx : exp 24 ≤ x) :
    8 * Ctw * x / (log x * (97 / 100 + log x)) + 102 * sqrt x <
      8 * Ctw * x / (log x * (0 + log x)) := by
  exact key_102 24 0 (97 / 100) x eq321_24 (by norm_num) le_rfl (by norm_num) hx

/-- The cited Prop exactly as the lab states it at the first table row.
CONDITIONAL ON the unresolved sieve319 and weighted_lower leaves. -/
theorem lemma5Used24_decomposed : Lemma5Used 24 0 := by
  intro x hx h hh
  have hx0 : 0 < x := lt_of_lt_of_le (exp_pos 24) hx
  have hl : 24 ≤ log x := (le_log_iff_exp_le hx0).mpr hx
  have hl0 : 0 < log x := by linarith
  have hd : 0 < log x * (97 / 100 + log x) := by positivity
  have hC := Ctw_pos
  have hw := wt_nonneg h
  have hlow := (row24 x hx).trans (weighted_lower x hx)
  have hs : 0 < Lemma3.S2 (sqrt (2 / 3 * x)) := by nlinarith
  have hdiv : x / Lemma3.S2 (sqrt (2 / 3 * x)) ≤
      8 * Ctw * x / (log x * (97 / 100 + log x)) := by
    apply (div_le_div_iff₀ hs hd).mpr
    nlinarith [mul_le_mul_of_nonneg_right hlow.le hx0.le]
  have hbound := sieve319 x hx h hh
  have hcmp := comparison24 x hx
  have hroot := sqrt_nonneg x
  apply hbound.trans
  apply mul_le_mul_of_nonneg_right _ hw
  linarith

end
end LeanLab.RieselVaughan1983.Decomp93

#print axioms LeanLab.RieselVaughan1983.Decomp93.mv_sieve
#print axioms LeanLab.RieselVaughan1983.Decomp93.sum_comparison
#print axioms LeanLab.RieselVaughan1983.Decomp93.sieve319
#print axioms LeanLab.RieselVaughan1983.Decomp93.weighted_lower
#print axioms LeanLab.RieselVaughan1983.Decomp93.row24
#print axioms LeanLab.RieselVaughan1983.Decomp93.comparison24
#print axioms LeanLab.RieselVaughan1983.Decomp93.lemma5Used24_decomposed
