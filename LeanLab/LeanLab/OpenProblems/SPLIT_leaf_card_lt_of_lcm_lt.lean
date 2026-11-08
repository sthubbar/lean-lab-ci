import LeanLab.OpenProblems.DecompJ1235

/-!
# SPLIT of `leaf_card_lt_of_lcm_lt`, folder OpenProblems, module DecompJ1235

The target bounds the number of congruences of a covering system whose moduli are the distinct
numbers `p - 1` with `p ≥ 5` prime and whose lcm stays below `8000000`. The statement is a finite
verification, not a consequence of the reciprocal test alone: the moduli of such a system are
divisors of the lcm, and for `L = 6006000` there are already `104` divisors of that shape with
reciprocal sum above `1`, so no estimate on the sum can refuse `100` congruences there. What the
split below does is cut the lcm range:

* below `1965600` no lcm has `100` divisors of the required shape, and that is pure counting, with
  no covering hypothesis at all;
* at the four lcm values `5012280`, `7022400`, `7425600`, `7876440`, which are the only ones below
  `8000000` whose required divisors number at least `100` and whose full reciprocal sum is below
  `1`, the reciprocal test refuses `100` congruences with no covering argument;
* on the two remaining windows of the lcm the claim needs the congruence search itself.

The assembly `leaf_card_lt_of_lcm_lt_split` proves the target from the leaves with no `sorry`.
-/

namespace LeanLab.OpenProblems.Novelty1615

open LeanLab.OpenProblems.Erdos273

/-- LEAF: counting step on the low range. A finite set of numbers, each of the shape `p - 1` for a
prime `p ≥ 5`, all of them divisors of a nonzero `L` below `1965600`, has fewer than `100` members.
No covering and no residue class enters here: this is the size of the set of divisors of `L` of that
shape, and it says that `1965600` is the first lcm which can carry `100` of them. The hypothesis
`0 < L` is needed: every positive `d` divides `0`. -/
theorem leaf_candidate_count_small (L : ℕ) (hL0 : 0 < L) (hL : L < 1965600) (T : Finset ℕ)
    (hdvd : ∀ d ∈ T, d ∣ L) (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    T.card < 100 := by
  sorry


/-! ### Private helpers for `leaf_inv_sum_lt_of_special`

The reciprocal test only needs the modulus set to sit inside the explicit finite set of divisors
`d` of `L` with `d + 1` prime. Everything below is bookkeeping that identifies that set: a divisor
of `L` is reconstructed from the exponent vector of `L`'s prime factorization, the exponents are
bounded by the ones of `L`, and the finitely many resulting values are checked one by one. -/

open scoped BigOperators in
/-- A prime dividing a product of primes is one of the factors. -/
private lemma prime_mem_of_dvd_listprod (l : List ℕ) (p : ℕ) (hp : p.Prime)
    (hpr : ∀ q ∈ l, q.Prime) (hd : p ∣ l.prod) : p ∈ l := by
  induction l with
  | nil =>
      simp only [List.not_mem_nil, List.prod_nil] at hd ⊢
      exact absurd (Nat.dvd_one.mp hd) hp.ne_one
  | cons a t ih =>
      rw [List.prod_cons] at hd
      rcases hp.dvd_mul.mp hd with h | h
      · have hpr_a : a.Prime := hpr a (by simp)
        rw [Nat.dvd_prime hpr_a] at h
        rcases h with h | h
        · exact absurd h hp.ne_one
        · simp [h]
      · exact List.mem_cons_of_mem a (ih (fun q hq => hpr q (by simp [hq])) h)

/-- Every divisor of a nonzero `n` is the product of `p ^ v p` over the support of a vector `v`
bounded by the exponent vector of `n`. -/
private lemma exists_factorization_le {n d : ℕ} (hn : n ≠ 0) (hd : d ∣ n) :
    ∃ v : ℕ →₀ ℕ, v ≤ n.factorization ∧ v.prod (· ^ ·) = d := by
  have hmem : d ∈ (↑n.divisors : Set ℕ) := Nat.mem_divisors.mpr ⟨hd, hn⟩
  rw [Nat.coe_divisors_eq_prod_pow_le_factorization hn] at hmem
  exact hmem

/-- The exponent of a prime in a divisor is at most its exponent in the number. -/
private lemma factor_le_of_not_dvd_pow {n p a : ℕ} (hn : n ≠ 0) (hp : p.Prime)
    (h : ¬ (p ^ (a + 1) ∣ n)) (v : ℕ →₀ ℕ) (hv : v ≤ n.factorization) : v p ≤ a := by
  have h1 : v p ≤ n.factorization p := hv p
  have h2 : n.factorization p ≤ a := by
    by_contra hcon
    push Not at hcon
    exact h ((hp.pow_dvd_iff_le_factorization hn).mpr hcon)
  omega

/-- A vector supported in a finite set of primes writes its product as a product over that set. -/
private lemma prod_eq_prod_of_support_subset (v : ℕ →₀ ℕ) (S : Finset ℕ)
    (hsub : v.support ⊆ S) : v.prod (· ^ ·) = ∏ q ∈ S, q ^ v q := by
  rw [Finsupp.prod]
  exact Finset.prod_subset hsub (fun x _ hx => by simp [Finsupp.notMem_support_iff.mp hx])

/-- If every prime dividing `L` lies in `S`, then so does the support of any exponent vector bounded
by the one of `L`. -/
private lemma support_subset_of {L : ℕ} {S : Finset ℕ} (hpd : ∀ p : ℕ, p.Prime → p ∣ L → p ∈ S)
    (v : ℕ →₀ ℕ) (hv : v ≤ L.factorization) : v.support ⊆ S := by
  intro p hpmem
  have hvp : v p ≠ 0 := Finsupp.mem_support_iff.mp hpmem
  have hfac : L.factorization p ≠ 0 := by
    intro h0
    have hle : v p ≤ 0 := by
      have := hv p
      rwa [h0] at this
    exact hvp (Nat.le_zero.mp hle)
  have hpdvd : p ∣ L := Nat.dvd_of_factorization_pos hfac
  have hpp : p.Prime := by
    by_contra hnp
    exact hfac (Nat.factorization_eq_zero_of_not_prime _ hnp)
  exact hpd p hpp hpdvd

/-- Positive terms: a subset has the smaller reciprocal sum. -/
private lemma inv_sum_lt_of_subset {T E : Finset ℕ} (hsub : T ⊆ E)
    (hE : ∑ d ∈ E, (1 : ℚ) / (d : ℚ) < 1) : ∑ d ∈ T, (1 : ℚ) / (d : ℚ) < 1 := by
  refine lt_of_le_of_lt (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) hE
  intro x _ _
  positivity

private lemma prime_dvd_5012280 {p : ℕ} (hp : p.Prime) (hd : p ∣ 5012280) :
    p ∈ ({2, 3, 5, 7, 13, 17} : Finset ℕ) := by
  have hpr : ∀ q ∈ ([2,2,2,3,3,3,3,5,7,13,17] : List ℕ), q.Prime := by decide
  have hl : p ∈ ([2,2,2,3,3,3,3,5,7,13,17] : List ℕ) := by
    refine prime_mem_of_dvd_listprod _ p hp hpr ?_
    rwa [show ([2,2,2,3,3,3,3,5,7,13,17] : List ℕ).prod = 5012280 by norm_num]
  simpa using hl

private lemma support_5012280 (v : ℕ →₀ ℕ) (hv : v ≤ (5012280 : ℕ).factorization) :
    v.support ⊆ ({2, 3, 5, 7, 13, 17} : Finset ℕ) :=
  support_subset_of (fun p hp hd => prime_dvd_5012280 hp hd) v hv

set_option maxRecDepth 10000 in
/-- The divisors `d` of `5012280` with `d + 1` prime (and `d ≥ 4`) are exactly the listed `104`
numbers. Checked by the prime factorization of `5012280` and one case per combination of exponents. -/
private lemma mem_E_5012280 {d : ℕ} (hdvd : d ∣ 5012280) (hp : (d + 1).Prime) (h4 : 4 ≤ d) :
    d ∈ ({
  4, 6, 10, 12, 18, 28, 30, 36, 40, 42, 52, 60, 70, 72, 78, 102, 108, 126, 130, 136, 156, 162, 180,
 210, 238, 270, 280, 306, 312, 378, 408, 420, 442, 520, 540, 546, 612, 630, 756, 810, 910, 918,
 936, 952, 1020, 1092, 1170, 1326, 1428, 1530, 1620, 2142, 2268, 2340, 2380, 2520, 2730, 2856,
 3060, 3510, 3570, 3672, 4420, 4590, 6120, 6426, 6552, 7560, 8190, 9180, 9282, 9828, 10530, 10710,
 12376, 12852, 14280, 15912, 16380, 19890, 21060, 23868, 24570, 27540, 27846, 30940, 35802, 38556,
 42840, 46410, 47736, 59670, 79560, 92820, 128520, 167076, 185640, 192780, 238680, 417690, 501228,
 1002456, 1253070, 1670760} : Finset ℕ) := by
  obtain ⟨v, hv, hprod⟩ := exists_factorization_le (by norm_num : (5012280 : ℕ) ≠ 0) hdvd
  have b2 : v 2 ≤ 3 := factor_le_of_not_dvd_pow (by norm_num) Nat.prime_two (by norm_num) v hv
  have b3 : v 3 ≤ 4 := factor_le_of_not_dvd_pow (by norm_num) Nat.prime_three (by norm_num) v hv
  have b5 : v 5 ≤ 1 := factor_le_of_not_dvd_pow (by norm_num) (by norm_num) (by norm_num) v hv
  have b7 : v 7 ≤ 1 := factor_le_of_not_dvd_pow (by norm_num) (by norm_num) (by norm_num) v hv
  have b13 : v 13 ≤ 1 := factor_le_of_not_dvd_pow (by norm_num) (by norm_num) (by norm_num) v hv
  have b17 : v 17 ≤ 1 := factor_le_of_not_dvd_pow (by norm_num) (by norm_num) (by norm_num) v hv
  have hsupp := support_5012280 v hv
  have hpp := prod_eq_prod_of_support_subset v ({2, 3, 5, 7, 13, 17} : Finset ℕ) hsupp
  have hexp : (∏ q ∈ ({2, 3, 5, 7, 13, 17} : Finset ℕ), q ^ v q) = 2 ^ v 2 * 3 ^ v 3 * 5 ^ v 5 * 7 ^ v 7 * 13 ^ v 13 * 17 ^ v 17 := by
    simp [Finset.prod_insert]
    ring
  rw [← hprod, hpp, hexp] at hp h4 ⊢
  set a2 := v 2 with ha2
  set a3 := v 3 with ha3
  set a5 := v 5 with ha5
  set a7 := v 7 with ha7
  set a13 := v 13 with ha13
  set a17 := v 17 with ha17
  have hb2 : a2 ≤ 3 := ha2.trans_le b2
  have hb3 : a3 ≤ 4 := ha3.trans_le b3
  have hb5 : a5 ≤ 1 := ha5.trans_le b5
  have hb7 : a7 ≤ 1 := ha7.trans_le b7
  have hb13 : a13 ≤ 1 := ha13.trans_le b13
  have hb17 : a17 ≤ 1 := ha17.trans_le b17
  interval_cases a2 <;> interval_cases a3 <;> interval_cases a5 <;> interval_cases a7 <;> interval_cases a13 <;> interval_cases a17
    <;> first
      | decide
      | (exfalso; omega)
      | (exfalso; norm_num at hp)

private lemma subset_E_5012280 (T : Finset ℕ) (hdvd : ∀ d ∈ T, d ∣ 5012280)
    (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) : T ⊆ ({
  4, 6, 10, 12, 18, 28, 30, 36, 40, 42, 52, 60, 70, 72, 78, 102, 108, 126, 130, 136, 156, 162, 180,
 210, 238, 270, 280, 306, 312, 378, 408, 420, 442, 520, 540, 546, 612, 630, 756, 810, 910, 918,
 936, 952, 1020, 1092, 1170, 1326, 1428, 1530, 1620, 2142, 2268, 2340, 2380, 2520, 2730, 2856,
 3060, 3510, 3570, 3672, 4420, 4590, 6120, 6426, 6552, 7560, 8190, 9180, 9282, 9828, 10530, 10710,
 12376, 12852, 14280, 15912, 16380, 19890, 21060, 23868, 24570, 27540, 27846, 30940, 35802, 38556,
 42840, 46410, 47736, 59670, 79560, 92820, 128520, 167076, 185640, 192780, 238680, 417690, 501228,
 1002456, 1253070, 1670760} : Finset ℕ) := by
  intro d hd
  obtain ⟨p, hpp, h5, hdp⟩ := hform d hd
  have hp1 : d + 1 = p := by omega
  have h4 : 4 ≤ d := by omega
  exact mem_E_5012280 (hdvd d hd) (hp1 ▸ hpp) h4

private lemma sum_E_5012280 : ∑ d ∈ ({
  4, 6, 10, 12, 18, 28, 30, 36, 40, 42, 52, 60, 70, 72, 78, 102, 108, 126, 130, 136, 156, 162, 180,
 210, 238, 270, 280, 306, 312, 378, 408, 420, 442, 520, 540, 546, 612, 630, 756, 810, 910, 918,
 936, 952, 1020, 1092, 1170, 1326, 1428, 1530, 1620, 2142, 2268, 2340, 2380, 2520, 2730, 2856,
 3060, 3510, 3570, 3672, 4420, 4590, 6120, 6426, 6552, 7560, 8190, 9180, 9282, 9828, 10530, 10710,
 12376, 12852, 14280, 15912, 16380, 19890, 21060, 23868, 24570, 27540, 27846, 30940, 35802, 38556,
 42840, 46410, 47736, 59670, 79560, 92820, 128520, 167076, 185640, 192780, 238680, 417690, 501228,
 1002456, 1253070, 1670760} : Finset ℕ), (1 : ℚ) / (d : ℚ) < 1 := by
  norm_num

private lemma prime_dvd_7022400 {p : ℕ} (hp : p.Prime) (hd : p ∣ 7022400) :
    p ∈ ({2, 3, 5, 7, 11, 19} : Finset ℕ) := by
  have hpr : ∀ q ∈ ([2,2,2,2,2,2,3,5,5,7,11,19] : List ℕ), q.Prime := by decide
  have hl : p ∈ ([2,2,2,2,2,2,3,5,5,7,11,19] : List ℕ) := by
    refine prime_mem_of_dvd_listprod _ p hp hpr ?_
    rwa [show ([2,2,2,2,2,2,3,5,5,7,11,19] : List ℕ).prod = 7022400 by norm_num]
  simpa using hl

private lemma support_7022400 (v : ℕ →₀ ℕ) (hv : v ≤ (7022400 : ℕ).factorization) :
    v.support ⊆ ({2, 3, 5, 7, 11, 19} : Finset ℕ) :=
  support_subset_of (fun p hp hd => prime_dvd_7022400 hp hd) v hv

set_option maxRecDepth 10000 in
/-- The divisors `d` of `7022400` with `d + 1` prime (and `d ≥ 4`) are exactly the listed `100`
numbers. Checked by the prime factorization of `7022400` and one case per combination of exponents. -/
private lemma mem_E_7022400 {d : ℕ} (hdvd : d ∣ 7022400) (hp : (d + 1).Prime) (h4 : 4 ≤ d) :
    d ∈ ({
  4, 6, 10, 12, 16, 22, 28, 30, 40, 42, 60, 66, 70, 88, 96, 100, 112, 150, 190, 192, 210, 228, 240,
 280, 330, 336, 352, 400, 418, 420, 448, 456, 462, 570, 600, 616, 660, 672, 700, 760, 880, 1050,
 1200, 1216, 1320, 1596, 1600, 1900, 2112, 2128, 2280, 2310, 2800, 2850, 2926, 3040, 3300, 3360,
 3696, 3850, 4200, 4560, 4620, 4800, 5280, 5700, 6270, 6688, 7392, 8512, 8778, 9240, 11550, 12540,
 15400, 18480, 25536, 33600, 39900, 40128, 41800, 43890, 46816, 53200, 62700, 63840, 79800, 92400,
 117040, 127680, 140448, 212800, 219450, 280896, 292600, 319200, 351120, 501600, 1003200, 3511200} : Finset ℕ) := by
  obtain ⟨v, hv, hprod⟩ := exists_factorization_le (by norm_num : (7022400 : ℕ) ≠ 0) hdvd
  have b2 : v 2 ≤ 6 := factor_le_of_not_dvd_pow (by norm_num) Nat.prime_two (by norm_num) v hv
  have b3 : v 3 ≤ 1 := factor_le_of_not_dvd_pow (by norm_num) Nat.prime_three (by norm_num) v hv
  have b5 : v 5 ≤ 2 := factor_le_of_not_dvd_pow (by norm_num) (by norm_num) (by norm_num) v hv
  have b7 : v 7 ≤ 1 := factor_le_of_not_dvd_pow (by norm_num) (by norm_num) (by norm_num) v hv
  have b11 : v 11 ≤ 1 := factor_le_of_not_dvd_pow (by norm_num) (by norm_num) (by norm_num) v hv
  have b19 : v 19 ≤ 1 := factor_le_of_not_dvd_pow (by norm_num) (by norm_num) (by norm_num) v hv
  have hsupp := support_7022400 v hv
  have hpp := prod_eq_prod_of_support_subset v ({2, 3, 5, 7, 11, 19} : Finset ℕ) hsupp
  have hexp : (∏ q ∈ ({2, 3, 5, 7, 11, 19} : Finset ℕ), q ^ v q) = 2 ^ v 2 * 3 ^ v 3 * 5 ^ v 5 * 7 ^ v 7 * 11 ^ v 11 * 19 ^ v 19 := by
    simp [Finset.prod_insert]
    ring
  rw [← hprod, hpp, hexp] at hp h4 ⊢
  set a2 := v 2 with ha2
  set a3 := v 3 with ha3
  set a5 := v 5 with ha5
  set a7 := v 7 with ha7
  set a11 := v 11 with ha11
  set a19 := v 19 with ha19
  have hb2 : a2 ≤ 6 := ha2.trans_le b2
  have hb3 : a3 ≤ 1 := ha3.trans_le b3
  have hb5 : a5 ≤ 2 := ha5.trans_le b5
  have hb7 : a7 ≤ 1 := ha7.trans_le b7
  have hb11 : a11 ≤ 1 := ha11.trans_le b11
  have hb19 : a19 ≤ 1 := ha19.trans_le b19
  interval_cases a2 <;> interval_cases a3 <;> interval_cases a5 <;> interval_cases a7 <;> interval_cases a11 <;> interval_cases a19
    <;> first
      | decide
      | (exfalso; omega)
      | (exfalso; norm_num at hp)

private lemma subset_E_7022400 (T : Finset ℕ) (hdvd : ∀ d ∈ T, d ∣ 7022400)
    (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) : T ⊆ ({
  4, 6, 10, 12, 16, 22, 28, 30, 40, 42, 60, 66, 70, 88, 96, 100, 112, 150, 190, 192, 210, 228, 240,
 280, 330, 336, 352, 400, 418, 420, 448, 456, 462, 570, 600, 616, 660, 672, 700, 760, 880, 1050,
 1200, 1216, 1320, 1596, 1600, 1900, 2112, 2128, 2280, 2310, 2800, 2850, 2926, 3040, 3300, 3360,
 3696, 3850, 4200, 4560, 4620, 4800, 5280, 5700, 6270, 6688, 7392, 8512, 8778, 9240, 11550, 12540,
 15400, 18480, 25536, 33600, 39900, 40128, 41800, 43890, 46816, 53200, 62700, 63840, 79800, 92400,
 117040, 127680, 140448, 212800, 219450, 280896, 292600, 319200, 351120, 501600, 1003200, 3511200} : Finset ℕ) := by
  intro d hd
  obtain ⟨p, hpp, h5, hdp⟩ := hform d hd
  have hp1 : d + 1 = p := by omega
  have h4 : 4 ≤ d := by omega
  exact mem_E_7022400 (hdvd d hd) (hp1 ▸ hpp) h4

private lemma sum_E_7022400 : ∑ d ∈ ({
  4, 6, 10, 12, 16, 22, 28, 30, 40, 42, 60, 66, 70, 88, 96, 100, 112, 150, 190, 192, 210, 228, 240,
 280, 330, 336, 352, 400, 418, 420, 448, 456, 462, 570, 600, 616, 660, 672, 700, 760, 880, 1050,
 1200, 1216, 1320, 1596, 1600, 1900, 2112, 2128, 2280, 2310, 2800, 2850, 2926, 3040, 3300, 3360,
 3696, 3850, 4200, 4560, 4620, 4800, 5280, 5700, 6270, 6688, 7392, 8512, 8778, 9240, 11550, 12540,
 15400, 18480, 25536, 33600, 39900, 40128, 41800, 43890, 46816, 53200, 62700, 63840, 79800, 92400,
 117040, 127680, 140448, 212800, 219450, 280896, 292600, 319200, 351120, 501600, 1003200, 3511200} : Finset ℕ), (1 : ℚ) / (d : ℚ) < 1 := by
  norm_num

private lemma prime_dvd_7425600 {p : ℕ} (hp : p.Prime) (hd : p ∣ 7425600) :
    p ∈ ({2, 3, 5, 7, 13, 17} : Finset ℕ) := by
  have hpr : ∀ q ∈ ([2,2,2,2,2,2,3,5,5,7,13,17] : List ℕ), q.Prime := by decide
  have hl : p ∈ ([2,2,2,2,2,2,3,5,5,7,13,17] : List ℕ) := by
    refine prime_mem_of_dvd_listprod _ p hp hpr ?_
    rwa [show ([2,2,2,2,2,2,3,5,5,7,13,17] : List ℕ).prod = 7425600 by norm_num]
  simpa using hl

private lemma support_7425600 (v : ℕ →₀ ℕ) (hv : v ≤ (7425600 : ℕ).factorization) :
    v.support ⊆ ({2, 3, 5, 7, 13, 17} : Finset ℕ) :=
  support_subset_of (fun p hp hd => prime_dvd_7425600 hp hd) v hv

set_option maxRecDepth 10000 in
/-- The divisors `d` of `7425600` with `d + 1` prime (and `d ≥ 4`) are exactly the listed `104`
numbers. Checked by the prime factorization of `7425600` and one case per combination of exponents. -/
private lemma mem_E_7425600 {d : ℕ} (hdvd : d ∣ 7425600) (hp : (d + 1).Prime) (h4 : 4 ≤ d) :
    d ∈ ({
  4, 6, 10, 12, 16, 28, 30, 40, 42, 52, 60, 70, 78, 96, 100, 102, 112, 130, 136, 150, 156, 192, 210,
 238, 240, 280, 312, 336, 400, 408, 420, 442, 448, 520, 546, 600, 672, 700, 910, 952, 1020, 1050,
 1092, 1200, 1248, 1300, 1326, 1360, 1428, 1600, 1950, 2080, 2380, 2550, 2730, 2800, 2856, 3120,
 3360, 3570, 4200, 4420, 4800, 5100, 5440, 8160, 8736, 9282, 9520, 12376, 14280, 14560, 15600,
 17680, 17850, 21840, 23800, 30940, 33150, 33600, 40800, 42432, 44200, 46410, 54600, 62400, 66300,
 74256, 77350, 92820, 109200, 145600, 148512, 185640, 212160, 218400, 232050, 371280, 436800,
 495040, 530400, 571200, 3712800, 7425600} : Finset ℕ) := by
  obtain ⟨v, hv, hprod⟩ := exists_factorization_le (by norm_num : (7425600 : ℕ) ≠ 0) hdvd
  have b2 : v 2 ≤ 6 := factor_le_of_not_dvd_pow (by norm_num) Nat.prime_two (by norm_num) v hv
  have b3 : v 3 ≤ 1 := factor_le_of_not_dvd_pow (by norm_num) Nat.prime_three (by norm_num) v hv
  have b5 : v 5 ≤ 2 := factor_le_of_not_dvd_pow (by norm_num) (by norm_num) (by norm_num) v hv
  have b7 : v 7 ≤ 1 := factor_le_of_not_dvd_pow (by norm_num) (by norm_num) (by norm_num) v hv
  have b13 : v 13 ≤ 1 := factor_le_of_not_dvd_pow (by norm_num) (by norm_num) (by norm_num) v hv
  have b17 : v 17 ≤ 1 := factor_le_of_not_dvd_pow (by norm_num) (by norm_num) (by norm_num) v hv
  have hsupp := support_7425600 v hv
  have hpp := prod_eq_prod_of_support_subset v ({2, 3, 5, 7, 13, 17} : Finset ℕ) hsupp
  have hexp : (∏ q ∈ ({2, 3, 5, 7, 13, 17} : Finset ℕ), q ^ v q) = 2 ^ v 2 * 3 ^ v 3 * 5 ^ v 5 * 7 ^ v 7 * 13 ^ v 13 * 17 ^ v 17 := by
    simp [Finset.prod_insert]
    ring
  rw [← hprod, hpp, hexp] at hp h4 ⊢
  set a2 := v 2 with ha2
  set a3 := v 3 with ha3
  set a5 := v 5 with ha5
  set a7 := v 7 with ha7
  set a13 := v 13 with ha13
  set a17 := v 17 with ha17
  have hb2 : a2 ≤ 6 := ha2.trans_le b2
  have hb3 : a3 ≤ 1 := ha3.trans_le b3
  have hb5 : a5 ≤ 2 := ha5.trans_le b5
  have hb7 : a7 ≤ 1 := ha7.trans_le b7
  have hb13 : a13 ≤ 1 := ha13.trans_le b13
  have hb17 : a17 ≤ 1 := ha17.trans_le b17
  interval_cases a2 <;> interval_cases a3 <;> interval_cases a5 <;> interval_cases a7 <;> interval_cases a13 <;> interval_cases a17
    <;> first
      | decide
      | (exfalso; omega)
      | (exfalso; norm_num at hp)

private lemma subset_E_7425600 (T : Finset ℕ) (hdvd : ∀ d ∈ T, d ∣ 7425600)
    (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) : T ⊆ ({
  4, 6, 10, 12, 16, 28, 30, 40, 42, 52, 60, 70, 78, 96, 100, 102, 112, 130, 136, 150, 156, 192, 210,
 238, 240, 280, 312, 336, 400, 408, 420, 442, 448, 520, 546, 600, 672, 700, 910, 952, 1020, 1050,
 1092, 1200, 1248, 1300, 1326, 1360, 1428, 1600, 1950, 2080, 2380, 2550, 2730, 2800, 2856, 3120,
 3360, 3570, 4200, 4420, 4800, 5100, 5440, 8160, 8736, 9282, 9520, 12376, 14280, 14560, 15600,
 17680, 17850, 21840, 23800, 30940, 33150, 33600, 40800, 42432, 44200, 46410, 54600, 62400, 66300,
 74256, 77350, 92820, 109200, 145600, 148512, 185640, 212160, 218400, 232050, 371280, 436800,
 495040, 530400, 571200, 3712800, 7425600} : Finset ℕ) := by
  intro d hd
  obtain ⟨p, hpp, h5, hdp⟩ := hform d hd
  have hp1 : d + 1 = p := by omega
  have h4 : 4 ≤ d := by omega
  exact mem_E_7425600 (hdvd d hd) (hp1 ▸ hpp) h4

private lemma sum_E_7425600 : ∑ d ∈ ({
  4, 6, 10, 12, 16, 28, 30, 40, 42, 52, 60, 70, 78, 96, 100, 102, 112, 130, 136, 150, 156, 192, 210,
 238, 240, 280, 312, 336, 400, 408, 420, 442, 448, 520, 546, 600, 672, 700, 910, 952, 1020, 1050,
 1092, 1200, 1248, 1300, 1326, 1360, 1428, 1600, 1950, 2080, 2380, 2550, 2730, 2800, 2856, 3120,
 3360, 3570, 4200, 4420, 4800, 5100, 5440, 8160, 8736, 9282, 9520, 12376, 14280, 14560, 15600,
 17680, 17850, 21840, 23800, 30940, 33150, 33600, 40800, 42432, 44200, 46410, 54600, 62400, 66300,
 74256, 77350, 92820, 109200, 145600, 148512, 185640, 212160, 218400, 232050, 371280, 436800,
 495040, 530400, 571200, 3712800, 7425600} : Finset ℕ), (1 : ℚ) / (d : ℚ) < 1 := by
  norm_num

private lemma prime_dvd_7876440 {p : ℕ} (hp : p.Prime) (hd : p ∣ 7876440) :
    p ∈ ({2, 3, 5, 11, 13, 17} : Finset ℕ) := by
  have hpr : ∀ q ∈ ([2,2,2,3,3,3,3,5,11,13,17] : List ℕ), q.Prime := by decide
  have hl : p ∈ ([2,2,2,3,3,3,3,5,11,13,17] : List ℕ) := by
    refine prime_mem_of_dvd_listprod _ p hp hpr ?_
    rwa [show ([2,2,2,3,3,3,3,5,11,13,17] : List ℕ).prod = 7876440 by norm_num]
  simpa using hl

private lemma support_7876440 (v : ℕ →₀ ℕ) (hv : v ≤ (7876440 : ℕ).factorization) :
    v.support ⊆ ({2, 3, 5, 11, 13, 17} : Finset ℕ) :=
  support_subset_of (fun p hp hd => prime_dvd_7876440 hp hd) v hv

set_option maxRecDepth 10000 in
/-- The divisors `d` of `7876440` with `d + 1` prime (and `d ≥ 4`) are exactly the listed `102`
numbers. Checked by the prime factorization of `7876440` and one case per combination of exponents. -/
private lemma mem_E_7876440 {d : ℕ} (hdvd : d ∣ 7876440) (hp : (d + 1).Prime) (h4 : 4 ≤ d) :
    d ∈ ({
  4, 6, 10, 12, 18, 22, 30, 36, 40, 52, 60, 66, 72, 78, 88, 102, 108, 130, 136, 156, 162, 180, 198,
 270, 306, 312, 330, 396, 408, 442, 520, 540, 612, 660, 810, 858, 918, 936, 990, 1020, 1122, 1170,
 1320, 1326, 1530, 1620, 1782, 1870, 2340, 2376, 2860, 2970, 3060, 3432, 3510, 3672, 4420, 4590,
 6120, 6732, 7128, 7480, 7722, 8580, 9180, 10098, 10530, 15912, 16830, 19890, 21060, 22440, 23166,
 23868, 25740, 27540, 29172, 35802, 38610, 43758, 47736, 51480, 59670, 60588, 72930, 79560, 87516,
 97240, 100980, 115830, 145860, 151470, 201960, 231660, 238680, 291720, 302940, 463320, 656370,
 1575288, 1969110, 2625480} : Finset ℕ) := by
  obtain ⟨v, hv, hprod⟩ := exists_factorization_le (by norm_num : (7876440 : ℕ) ≠ 0) hdvd
  have b2 : v 2 ≤ 3 := factor_le_of_not_dvd_pow (by norm_num) Nat.prime_two (by norm_num) v hv
  have b3 : v 3 ≤ 4 := factor_le_of_not_dvd_pow (by norm_num) Nat.prime_three (by norm_num) v hv
  have b5 : v 5 ≤ 1 := factor_le_of_not_dvd_pow (by norm_num) (by norm_num) (by norm_num) v hv
  have b11 : v 11 ≤ 1 := factor_le_of_not_dvd_pow (by norm_num) (by norm_num) (by norm_num) v hv
  have b13 : v 13 ≤ 1 := factor_le_of_not_dvd_pow (by norm_num) (by norm_num) (by norm_num) v hv
  have b17 : v 17 ≤ 1 := factor_le_of_not_dvd_pow (by norm_num) (by norm_num) (by norm_num) v hv
  have hsupp := support_7876440 v hv
  have hpp := prod_eq_prod_of_support_subset v ({2, 3, 5, 11, 13, 17} : Finset ℕ) hsupp
  have hexp : (∏ q ∈ ({2, 3, 5, 11, 13, 17} : Finset ℕ), q ^ v q) = 2 ^ v 2 * 3 ^ v 3 * 5 ^ v 5 * 11 ^ v 11 * 13 ^ v 13 * 17 ^ v 17 := by
    simp [Finset.prod_insert]
    ring
  rw [← hprod, hpp, hexp] at hp h4 ⊢
  set a2 := v 2 with ha2
  set a3 := v 3 with ha3
  set a5 := v 5 with ha5
  set a11 := v 11 with ha11
  set a13 := v 13 with ha13
  set a17 := v 17 with ha17
  have hb2 : a2 ≤ 3 := ha2.trans_le b2
  have hb3 : a3 ≤ 4 := ha3.trans_le b3
  have hb5 : a5 ≤ 1 := ha5.trans_le b5
  have hb11 : a11 ≤ 1 := ha11.trans_le b11
  have hb13 : a13 ≤ 1 := ha13.trans_le b13
  have hb17 : a17 ≤ 1 := ha17.trans_le b17
  interval_cases a2 <;> interval_cases a3 <;> interval_cases a5 <;> interval_cases a11 <;> interval_cases a13 <;> interval_cases a17
    <;> first
      | decide
      | (exfalso; omega)
      | (exfalso; norm_num at hp)

private lemma subset_E_7876440 (T : Finset ℕ) (hdvd : ∀ d ∈ T, d ∣ 7876440)
    (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) : T ⊆ ({
  4, 6, 10, 12, 18, 22, 30, 36, 40, 52, 60, 66, 72, 78, 88, 102, 108, 130, 136, 156, 162, 180, 198,
 270, 306, 312, 330, 396, 408, 442, 520, 540, 612, 660, 810, 858, 918, 936, 990, 1020, 1122, 1170,
 1320, 1326, 1530, 1620, 1782, 1870, 2340, 2376, 2860, 2970, 3060, 3432, 3510, 3672, 4420, 4590,
 6120, 6732, 7128, 7480, 7722, 8580, 9180, 10098, 10530, 15912, 16830, 19890, 21060, 22440, 23166,
 23868, 25740, 27540, 29172, 35802, 38610, 43758, 47736, 51480, 59670, 60588, 72930, 79560, 87516,
 97240, 100980, 115830, 145860, 151470, 201960, 231660, 238680, 291720, 302940, 463320, 656370,
 1575288, 1969110, 2625480} : Finset ℕ) := by
  intro d hd
  obtain ⟨p, hpp, h5, hdp⟩ := hform d hd
  have hp1 : d + 1 = p := by omega
  have h4 : 4 ≤ d := by omega
  exact mem_E_7876440 (hdvd d hd) (hp1 ▸ hpp) h4

private lemma sum_E_7876440 : ∑ d ∈ ({
  4, 6, 10, 12, 18, 22, 30, 36, 40, 52, 60, 66, 72, 78, 88, 102, 108, 130, 136, 156, 162, 180, 198,
 270, 306, 312, 330, 396, 408, 442, 520, 540, 612, 660, 810, 858, 918, 936, 990, 1020, 1122, 1170,
 1320, 1326, 1530, 1620, 1782, 1870, 2340, 2376, 2860, 2970, 3060, 3432, 3510, 3672, 4420, 4590,
 6120, 6732, 7128, 7480, 7722, 8580, 9180, 10098, 10530, 15912, 16830, 19890, 21060, 22440, 23166,
 23868, 25740, 27540, 29172, 35802, 38610, 43758, 47736, 51480, 59670, 60588, 72930, 79560, 87516,
 97240, 100980, 115830, 145860, 151470, 201960, 231660, 238680, 291720, 302940, 463320, 656370,
 1575288, 1969110, 2625480} : Finset ℕ), (1 : ℚ) / (d : ℚ) < 1 := by
  norm_num

/-- LEAF: the reciprocal test at the four exceptional lcm values. For `L` one of `5012280`,
`7022400`, `7425600`, `7876440`, the sum of `1 / d` over the divisors `d` of `L` of the shape
`p - 1`, `p ≥ 5` prime, is below `1`, so every subset of them is too. These are the values below
`8000000` where the sum over all of them already fails the `1` that a covering forces. -/
theorem leaf_inv_sum_lt_of_special (L : ℕ)
    (hL : L ∈ ({5012280, 7022400, 7425600, 7876440} : Finset ℕ)) (T : Finset ℕ)
    (hdvd : ∀ d ∈ T, d ∣ L) (hform : ∀ d ∈ T, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1) :
    ∑ d ∈ T, (1 : ℚ) / d < 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hL
  rcases hL with rfl | rfl | rfl | rfl
  · exact inv_sum_lt_of_subset (subset_E_5012280 T hdvd hform) (sum_E_5012280)
  · exact inv_sum_lt_of_subset (subset_E_7022400 T hdvd hform) (sum_E_7022400)
  · exact inv_sum_lt_of_subset (subset_E_7425600 T hdvd hform) (sum_E_7425600)
  · exact inv_sum_lt_of_subset (subset_E_7876440 T hdvd hform) (sum_E_7876440)

/-- LEAF: the congruence search on the middle window of the lcm, `1965600 ≤ lcm < 4600000`. A
covering system with distinct moduli `p - 1`, `p ≥ 5` prime, and with lcm in that window, other
than at the four lcm values handled by the reciprocal test, has fewer than `100` congruences. This
is the search over the residue data for the lcm values in the window. -/
theorem leaf_cover_search_mid {S : Finset (ℕ × ℤ)} (hS : Covers S)
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1)
    (hlo : 1965600 ≤ S.lcm Prod.fst) (hhi : S.lcm Prod.fst < 4600000)
    (hout : S.lcm Prod.fst ∉ ({5012280, 7022400, 7425600, 7876440} : Finset ℕ)) :
    S.card < 100 := by
  sorry

/-- LEAF: the congruence search on the top window of the lcm, `4600000 ≤ lcm < 8000000`. Same
claim as the middle window, for the residue data whose lcm lies in the upper part of the range, the
four lcm values handled by the reciprocal test again excluded. -/
theorem leaf_cover_search_top {S : Finset (ℕ × ℤ)} (hS : Covers S)
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
    (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1)
    (hlo : 4600000 ≤ S.lcm Prod.fst) (hhi : S.lcm Prod.fst < 8000000)
    (hout : S.lcm Prod.fst ∉ ({5012280, 7022400, 7425600, 7876440} : Finset ℕ)) :
    S.card < 100 := by
  sorry

/-- Every modulus of `S` divides the lcm of the moduli, so the moduli are divisors of one number.
Bookkeeping for the two arithmetic leaves. -/
private lemma moduli_dvd_lcm {S : Finset (ℕ × ℤ)} {s : ℕ × ℤ} (hs : s ∈ S) :
    s.1 ∣ S.lcm Prod.fst :=
  Finset.dvd_lcm (f := Prod.fst) hs

/-- Distinctness of the moduli turns a sum over the congruences into a sum over the moduli. -/
private lemma sum_inv_eq_sum_image {S : Finset (ℕ × ℤ)}
    (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ))) :
    ∑ s ∈ S, (1 : ℚ) / ((s.1 : ℕ) : ℚ) = ∑ d ∈ S.image Prod.fst, (1 : ℚ) / ((d : ℕ) : ℚ) :=
  (Finset.sum_image (s := S) (g := Prod.fst) (f := fun d : ℕ => (1 : ℚ) / ((d : ℕ) : ℚ))
    hi).symm

/-- The split of `leaf_card_lt_of_lcm_lt`: the same statement, proved from the four leaves above,
with no `sorry` and without using the target theorem. -/
theorem leaf_card_lt_of_lcm_lt_split {S : Finset (ℕ × ℤ)} (hS : Covers S) (hi : Set.InjOn Prod.fst (S : Set (ℕ × ℤ)))
  (hp : ∀ s ∈ S, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ s.1 = p - 1) (hlcm : S.lcm Prod.fst < 8000000) : S.card < 100 := by
  have hdvd : ∀ d ∈ S.image Prod.fst, d ∣ S.lcm Prod.fst := by
    intro d hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
    exact moduli_dvd_lcm hs
  have hform : ∀ d ∈ S.image Prod.fst, ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ d = p - 1 := by
    intro d hd
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hd
    exact hp s hs
  have hpos : ∀ s ∈ S, 0 < s.1 := by
    intro s hs
    obtain ⟨p, _, h5, hsp⟩ := hp s hs
    omega
  have hlcmpos : 0 < S.lcm Prod.fst := by
    rw [Nat.pos_iff_ne_zero]
    refine Finset.lcm_ne_zero_iff.mpr ?_
    intro s hs
    have h := hpos s hs
    omega
  by_cases h1 : S.lcm Prod.fst < 1965600
  · have hlt := leaf_candidate_count_small (S.lcm Prod.fst) hlcmpos h1 (S.image Prod.fst) hdvd hform
    have hcard : (S.image Prod.fst).card = S.card := Finset.card_image_of_injOn hi
    omega
  · by_cases h2 : S.lcm Prod.fst ∈ ({5012280, 7022400, 7425600, 7876440} : Finset ℕ)
    · exfalso
      have hd := one_le_sum_inv hS hpos
      rw [sum_inv_eq_sum_image hi] at hd
      have hlt := leaf_inv_sum_lt_of_special (S.lcm Prod.fst) h2 (S.image Prod.fst) hdvd hform
      linarith
    · by_cases h3 : S.lcm Prod.fst < 4600000
      · exact leaf_cover_search_mid hS hi hp (by omega) h3 h2
      · exact leaf_cover_search_top hS hi hp (by omega) hlcm h2

end LeanLab.OpenProblems.Novelty1615

#print axioms LeanLab.OpenProblems.Novelty1615.leaf_card_lt_of_lcm_lt_split
