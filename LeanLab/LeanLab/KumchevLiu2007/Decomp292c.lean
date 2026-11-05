/-
Smooth remainder in display 50, page 14 of arXiv 0801.0130.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp292b

namespace LeanLab.KumchevLiu2007.Task292c

open Real Complex Task129 Task129b Task292a
open scoped BigOperators

/-- Page 14 before display 50. Q2 is the product of primes at most Q. -/
noncomputable def smoothModulus (Q : ℝ) : ℕ :=
  ∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime, p

private lemma primeFactors_smoothModulus (Q : ℝ) :
    (smoothModulus Q).primeFactors = (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime := by
  rw [smoothModulus]
  exact Nat.primeFactors_prod (fun p hp => (Finset.mem_filter.mp hp).2)

private lemma squarefree_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.prod_insert hat]
    have hpa : a.Prime := hs a (Finset.mem_insert_self a t)
    have ht : ∀ p ∈ t, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hne : (∏ p ∈ t, p) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro p hp
      exact (ht p hp).ne_zero
    have hcop : a.Coprime (∏ p ∈ t, p) := by
      refine (Nat.Prime.coprime_iff_not_dvd hpa).mpr ?_
      intro hdvd
      have hmem : a ∈ (∏ p ∈ t, p).primeFactors := Nat.mem_primeFactors.mpr ⟨hpa, hdvd, hne⟩
      rw [Nat.primeFactors_prod ht] at hmem
      exact hat hmem
    exact (Nat.squarefree_mul hcop).mpr
      ⟨Prime.squarefree (Nat.prime_iff.mp hpa), ih ht⟩

private lemma squarefree_smoothModulus (Q : ℝ) : Squarefree (smoothModulus Q) := by
  rw [smoothModulus]
  exact squarefree_prod_primes _ (fun p hp => (Finset.mem_filter.mp hp).2)

private lemma one_le_smoothModulus (Q : ℝ) : 1 ≤ smoothModulus Q := by
  rw [smoothModulus]
  exact Finset.one_le_prod (fun p hp => (Finset.mem_filter.mp hp).2.one_le)

/-- Every prime in the range of `smoothModulus Q` is at most `Q`. -/
private lemma prime_le_of_mem_range (p : ℕ) (Q : ℝ)
    (hp : p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime) : (p : ℝ) ≤ Q := by
  have h1 : p ≤ ⌊Q⌋₊ := by
    have := (Finset.mem_filter.mp hp).1
    rw [Finset.mem_range, Nat.lt_succ_iff] at this
    exact this
  have h2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
  have h3 : (0 : ℕ) < ⌊Q⌋₊ := by omega
  have h4 : (1 : ℝ) ≤ Q := Nat.floor_pos.mp h3
  exact le_trans (by exact_mod_cast h1) (Nat.floor_le (by linarith))

/-! ### Leaf 1: `smoothWeight` and the finite Euler product -/

private lemma smoothWeight_eq_one_of_forall (q : ℕ) (Q : ℝ)
    (h : ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q) : smoothWeight q Q = 1 := by
  unfold smoothWeight
  exact if_pos h

private lemma smoothWeight_eq_one (q : ℕ) (Q : ℝ) (hq1 : 1 ≤ q) (hqQ : (q : ℝ) ≤ Q) :
    smoothWeight q Q = 1 := by
  refine smoothWeight_eq_one_of_forall q Q ?_
  intro p hp hpq
  have hle : p ≤ q := Nat.le_of_dvd (by omega) hpq
  exact le_trans (by exact_mod_cast hle) hqQ

private lemma dvd_smoothModulus {q : ℕ} {Q : ℝ} (hsq : Squarefree q)
    (hq : ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q) : q ∣ smoothModulus Q := by
  classical
  have hsub : q.primeFactors ⊆ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hle : (p : ℝ) ≤ Q := hq p hpp (Nat.dvd_of_mem_primeFactors hp)
    refine Finset.mem_filter.mpr ⟨?_, hpp⟩
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.le_floor hle
  have h1 : ∏ p ∈ q.primeFactors, p = q := Nat.prod_primeFactors_of_squarefree hsq
  have h2 : (∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime, p) = smoothModulus Q := rfl
  rw [← h1, ← h2]
  exact Finset.prod_dvd_prod_of_subset _ _ _ hsub

/-- The sum of `A2` over the divisors of the smooth modulus is the Euler product. -/
private lemma sum_divisors_A2 (n : ℕ) (Q : ℝ) :
    ∑ q ∈ (smoothModulus Q).divisors, U1534.A2 n q = product2 n Q := by
  have hM : Squarefree (smoothModulus Q) := squarefree_smoothModulus Q
  let f : ArithmeticFunction ℂ := ⟨U1534.A2 n, by simp [U1534.A2]⟩
  have hf : f.IsMultiplicative :=
    ⟨U1534.A2_one n, fun {a b} hab => A2_coprime_mul n a b hab⟩
  have h := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree hf hM
  rw [primeFactors_smoothModulus Q] at h
  have h2 : ∑ d ∈ (smoothModulus Q).divisors, f d
      = ∑ d ∈ (smoothModulus Q).divisors, U1534.A2 n d := rfl
  rw [← h2, ← h]
  rfl

/-- The finite sum over `1 ≤ q ≤ smoothModulus Q` of the weighted coefficient is the
Euler product: this is the exact content of display 50's cancellation. -/
private lemma sum_Icc_smooth_eq_product2 (n : ℕ) (Q : ℝ) :
    ∑ q ∈ Finset.Icc 1 (smoothModulus Q), (smoothWeight q Q : ℂ) * U1534.A2 n q
      = product2 n Q := by
  classical
  have hM0 : smoothModulus Q ≠ 0 := by
    have := one_le_smoothModulus Q; omega
  have hsub : (smoothModulus Q).divisors ⊆ Finset.Icc 1 (smoothModulus Q) := by
    intro q hq
    obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.mp hq
    have hq0 : q ≠ 0 := fun h => hne (by rw [h] at hdvd; exact zero_dvd_iff.mp hdvd)
    have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
    have hqM : q ≤ smoothModulus Q := Nat.le_of_dvd (by omega) hdvd
    exact Finset.mem_Icc.mpr ⟨hq1, hqM⟩
  have hzero : ∀ q ∈ Finset.Icc 1 (smoothModulus Q), q ∉ (smoothModulus Q).divisors →
      (smoothWeight q Q : ℂ) * U1534.A2 n q = 0 := by
    intro q hq hqnot
    have hndvd : ¬ q ∣ smoothModulus Q := by
      intro hd
      exact hqnot (Nat.mem_divisors.mpr ⟨hd, hM0⟩)
    by_cases hsq : Squarefree q
    · have hw : smoothWeight q Q = 0 := by
        rw [smoothWeight, if_neg]
        intro hcond
        exact hndvd (dvd_smoothModulus hsq hcond)
      rw [hw]
      simp
    · rw [A2_eq_zero_of_not_squarefree n q hsq, mul_zero]
  have hdiv : ∑ q ∈ (smoothModulus Q).divisors, (smoothWeight q Q : ℂ) * U1534.A2 n q
      = ∑ q ∈ (smoothModulus Q).divisors, U1534.A2 n q := by
    refine Finset.sum_congr rfl ?_
    intro q hq
    obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.mp hq
    have hqQ : ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q := by
      intro p hp hpq
      have hpM : p ∈ (smoothModulus Q).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp, dvd_trans hpq hdvd, hM0⟩
      rw [primeFactors_smoothModulus Q] at hpM
      exact prime_le_of_mem_range p Q hpM
    rw [smoothWeight_eq_one_of_forall q Q hqQ]
    simp
  calc ∑ q ∈ Finset.Icc 1 (smoothModulus Q), (smoothWeight q Q : ℂ) * U1534.A2 n q
      = ∑ q ∈ (smoothModulus Q).divisors, (smoothWeight q Q : ℂ) * U1534.A2 n q :=
        (Finset.sum_subset hsub hzero).symm
    _ = ∑ q ∈ (smoothModulus Q).divisors, U1534.A2 n q := hdiv
    _ = product2 n Q := sum_divisors_A2 n Q

/-! ### Leaf 1: the Finset rearrangement -/

private lemma sum_Icc_split (f : ℕ → ℂ) {a b : ℕ} (hab : a ≤ b) :
    ∑ q ∈ Finset.Icc 1 b, f q = ∑ q ∈ Finset.Icc 1 a, f q + ∑ q ∈ Finset.Ioc a b, f q := by
  have hunion : Finset.Icc 1 b = Finset.Icc 1 a ∪ Finset.Ioc a b := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
    constructor
    · rintro ⟨hx1, hx2⟩
      by_cases h : x ≤ a
      · exact Or.inl ⟨hx1, h⟩
      · exact Or.inr ⟨by omega, hx2⟩
    · rintro (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩) <;> omega
  have hd : Disjoint (Finset.Icc 1 a) (Finset.Ioc a b) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_Icc] at hx1
    simp only [Finset.mem_Ioc] at hx2
    omega
  rw [hunion, Finset.sum_union hd]

private lemma sum_split_three (f : ℕ → ℂ) {M a b : ℕ} (hM : 1 ≤ M) (hab : a ≤ b)
    (hzero : ∀ q, M < q → f q = 0) :
    ∑ q ∈ Finset.Icc 1 M, f q
      = ∑ q ∈ Finset.Icc 1 a, f q + ∑ q ∈ Finset.Ioc a b, f q
        + ∑ q ∈ Finset.Ioc b M, f q := by
  classical
  by_cases hbM : b ≤ M
  · have haM : a ≤ M := le_trans hab hbM
    have hunion : Finset.Icc 1 M = Finset.Icc 1 b ∪ Finset.Ioc b M := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
      constructor
      · rintro ⟨hx1, hx2⟩
        by_cases h : x ≤ b
        · exact Or.inl ⟨hx1, h⟩
        · exact Or.inr ⟨by omega, hx2⟩
      · rintro (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩) <;> omega
    have hd : Disjoint (Finset.Icc 1 b) (Finset.Ioc b M) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_Icc] at hx1
      simp only [Finset.mem_Ioc] at hx2
      omega
    rw [hunion, Finset.sum_union hd, sum_Icc_split f hab]
  · have hMb : M < b := by omega
    have hIocM : Finset.Ioc b M = ∅ := Finset.Ioc_eq_empty_iff.mpr (by omega)
    rw [hIocM, Finset.sum_empty, add_zero]
    by_cases haM : a ≤ M
    · have hunion : Finset.Icc 1 M = Finset.Icc 1 a ∪ Finset.Ioc a M := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
        constructor
        · rintro ⟨hx1, hx2⟩
          by_cases h : x ≤ a
          · exact Or.inl ⟨hx1, h⟩
          · exact Or.inr ⟨by omega, hx2⟩
        · rintro (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩) <;> omega
      have hd : Disjoint (Finset.Icc 1 a) (Finset.Ioc a M) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_Icc] at hx1
        simp only [Finset.mem_Ioc] at hx2
        omega
      have hunion2 : Finset.Ioc a b = Finset.Ioc a M ∪ Finset.Ioc M b :=
        (Finset.Ioc_union_Ioc_eq_Ioc haM (le_of_lt hMb)).symm
      have hd2 : Disjoint (Finset.Ioc a M) (Finset.Ioc M b) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_Ioc] at hx1 hx2
        omega
      have htail : ∑ q ∈ Finset.Ioc M b, f q = 0 :=
        Finset.sum_eq_zero (fun q hq => hzero q (Finset.mem_Ioc.mp hq).1)
      rw [hunion, Finset.sum_union hd, hunion2, Finset.sum_union hd2, htail, add_zero]
    · have hMa : M < a := by omega
      have hunion : Finset.Icc 1 a = Finset.Icc 1 M ∪ Finset.Ioc M a := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
        constructor
        · rintro ⟨hx1, hx2⟩
          by_cases h : x ≤ M
          · exact Or.inl ⟨hx1, h⟩
          · exact Or.inr ⟨by omega, hx2⟩
        · rintro (⟨hx1, hx2⟩ | ⟨hx1, hx2⟩) <;> omega
      have hd : Disjoint (Finset.Icc 1 M) (Finset.Ioc M a) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_Icc] at hx1
        simp only [Finset.mem_Ioc] at hx2
        omega
      have hmid : ∑ q ∈ Finset.Ioc M a, f q = 0 :=
        Finset.sum_eq_zero (fun q hq => hzero q (Finset.mem_Ioc.mp hq).1)
      have hrest : ∑ q ∈ Finset.Ioc a b, f q = 0 :=
        Finset.sum_eq_zero (fun q hq => hzero q (by have := (Finset.mem_Ioc.mp hq).1; omega))
      rw [hunion, Finset.sum_union hd, hmid, add_zero, hrest, add_zero]

/-- The weighted coefficient vanishes above the smooth modulus. -/
private lemma smooth_coeff_eq_zero_of_lt {n : ℕ} {Q : ℝ} {q : ℕ}
    (hq : smoothModulus Q < q) : (smoothWeight q Q : ℂ) * U1534.A2 n q = 0 := by
  classical
  have hM1 : 1 ≤ smoothModulus Q := one_le_smoothModulus Q
  have hq1 : 1 ≤ q := by omega
  by_cases hsq : Squarefree q
  · have hw : smoothWeight q Q = 0 := by
      rw [smoothWeight, if_neg]
      intro hcond
      have hdvd : q ∣ smoothModulus Q := dvd_smoothModulus hsq hcond
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    rw [hw]
    simp
  · rw [A2_eq_zero_of_not_squarefree n q hsq, mul_zero]

/-! ### Leaf 1: the assembly -/

private lemma smooth_remainder_identity_proved (n : ℕ) (P Q T : ℝ)
    (hP : 0 < P) (hPQ : P ≤ Q) (hQT : Q ≤ T) :
    (series2 n P - product2 n Q) - tail2 n P T Q =
      -(∑ q ∈ Finset.Ioc ⌊T⌋₊ (smoothModulus Q),
        (smoothWeight q Q : ℂ) * U1534.A2 n q) := by
  classical
  have hPT : P ≤ T := le_trans hPQ hQT
  have hab : ⌊P⌋₊ ≤ ⌊T⌋₊ := Nat.floor_mono hPT
  have hM1 : 1 ≤ smoothModulus Q := one_le_smoothModulus Q
  have hser : series2 n P
      = ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, (smoothWeight q Q : ℂ) * U1534.A2 n q := by
    rw [series2]
    refine Finset.sum_congr rfl ?_
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqP : q ≤ ⌊P⌋₊ := (Finset.mem_Icc.mp hq).2
    have hqQ : (q : ℝ) ≤ Q := by
      have h1 : (q : ℝ) ≤ (⌊P⌋₊ : ℝ) := by exact_mod_cast hqP
      have h2 : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le (le_of_lt hP)
      linarith
    rw [smoothWeight_eq_one q Q hq1 hqQ]
    simp
  have htail : tail2 n P T Q
      = -∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊T⌋₊, (smoothWeight q Q : ℂ) * U1534.A2 n q := by
    rw [tail2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro q hq
    rw [neg_mul]
  have hF : ∑ q ∈ Finset.Icc 1 (smoothModulus Q), (smoothWeight q Q : ℂ) * U1534.A2 n q
      = product2 n Q := sum_Icc_smooth_eq_product2 n Q
  have hsplit := sum_split_three (fun q => (smoothWeight q Q : ℂ) * U1534.A2 n q)
    hM1 hab (fun q hq => smooth_coeff_eq_zero_of_lt hq)
  have hE2 : ∑ q ∈ Finset.Ioc ⌊T⌋₊ (smoothModulus Q), (smoothWeight q Q : ℂ) * U1534.A2 n q
      = ∑ q ∈ Finset.Icc 1 (smoothModulus Q), (smoothWeight q Q : ℂ) * U1534.A2 n q
        - ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, (smoothWeight q Q : ℂ) * U1534.A2 n q
        - ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊T⌋₊, (smoothWeight q Q : ℂ) * U1534.A2 n q := by
    rw [hsplit]
    ring
  rw [hser, htail, ← hF, hE2]
  ring

/-- LEAF. Page 14 display 50 and the subtraction immediately below it.
For P at most Q at most T, subtract the finite Euler product expansion
and cancel the coefficients up to P. Only the smooth tail above T
remains. This is an exact finite identity, with no analytic estimate. -/
theorem smooth_remainder_identity (n : ℕ) (P Q T : ℝ)
    (hP : 0 < P) (hPQ : P ≤ Q) (hQT : Q ≤ T) :
    (series2 n P - product2 n Q) - tail2 n P T Q =
      -(∑ q ∈ Finset.Ioc ⌊T⌋₊ (smoothModulus Q),
        (smoothWeight q Q : ℂ) * U1534.A2 n q) :=
  smooth_remainder_identity_proved n P Q T hP hPQ hQT

private lemma log_rpow_le_third {ε x y : ℝ} (hε : 0 < ε) (hx0 : 0 < x)
    (hL : max 1 ((3 / ε) ^ (1 / ε)) ≤ Real.log x) (hxy : x ^ ε ≤ y) :
    Real.log x ^ (1 - ε) ≤ Real.log y / 3 := by
  have hLpos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hL)
  have h3 : 0 < 3 / ε := by positivity
  -- `log x ^ ε ≥ 3 / ε`
  have hpow : (3 / ε) ≤ Real.log x ^ ε := by
    have hbase : 0 ≤ 3 / ε := le_of_lt h3
    have hmul : 1 / ε * ε = (1 : ℝ) := by field_simp
    have hkey : ((3 / ε) ^ (1 / ε)) ^ ε = 3 / ε := by
      rw [← Real.rpow_mul hbase, hmul, Real.rpow_one]
    rw [← hkey]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hbase _)
      (le_trans (le_max_right _ _) hL) (le_of_lt hε)
  -- `log x ^ (1 - ε) = log x / log x ^ ε`
  have hsplit : Real.log x ^ (1 - ε) = Real.log x / Real.log x ^ ε := by
    rw [Real.rpow_sub hLpos, Real.rpow_one]
  -- `ε log x ≤ log y`
  have hlogy : ε * Real.log x ≤ Real.log y := by
    have h1 : Real.log (x ^ ε) ≤ Real.log y :=
      Real.log_le_log (Real.rpow_pos_of_pos hx0 ε) hxy
    rwa [Real.log_rpow hx0] at h1
  rw [hsplit]
  have hstep : Real.log x / Real.log x ^ ε ≤ Real.log x / (3 / ε) :=
    div_le_div_of_nonneg_left hLpos.le h3 hpow
  have hsimp : Real.log x / (3 / ε) = ε * Real.log x / 3 := by
    field_simp
  rw [hsimp] at hstep
  linarith

private lemma cutoff_order_proved (ε : ℝ) (hε : 0 < ε) :
    ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      Q ≤ y ^ (1 / 3 : ℝ) := by
  have hx0ge : (2 : ℝ) ≤ Real.exp (max 1 ((3 / ε) ^ (1 / ε))) + 2 := by
    have := Real.exp_pos (max 1 ((3 / ε) ^ (1 / ε)))
    linarith
  refine ⟨Real.exp (max 1 ((3 / ε) ^ (1 / ε))) + 2, hx0ge, ?_⟩
  intro x y Q hx hxy hQ
  have hexp0 : 0 < Real.exp (max 1 ((3 / ε) ^ (1 / ε))) := Real.exp_pos _
  have hxlog : Real.log (Real.exp (max 1 ((3 / ε) ^ (1 / ε))) + 2) ≤ Real.log x :=
    Real.log_le_log (by linarith) hx
  have hxlog2 : max 1 ((3 / ε) ^ (1 / ε)) ≤
      Real.log (Real.exp (max 1 ((3 / ε) ^ (1 / ε))) + 2) := by
    have h1 : Real.log (Real.exp (max 1 ((3 / ε) ^ (1 / ε)))) ≤
        Real.log (Real.exp (max 1 ((3 / ε) ^ (1 / ε))) + 2) :=
      Real.log_le_log hexp0 (by linarith)
    rwa [Real.log_exp] at h1
  have hL : max 1 ((3 / ε) ^ (1 / ε)) ≤ Real.log x := le_trans hxlog2 hxlog
  have hx0 : 0 < x := by linarith [le_max_left 1 ((3 / ε) ^ (1 / ε) : ℝ), hx]
  have hθ : Real.log x ^ (1 - ε) ≤ Real.log y / 3 :=
    log_rpow_le_third hε hx0 hL hxy
  have hy0 : 0 < y := by
    have h0 : (0 : ℝ) < x ^ ε := Real.rpow_pos_of_pos hx0 ε
    linarith
  have hmono : Real.exp (Real.log x ^ (1 - ε)) ≤ Real.exp (Real.log y / 3) :=
    Real.exp_le_exp.mpr hθ
  have hthird : Real.exp (Real.log y / 3) = y ^ (1 / 3 : ℝ) := by
    rw [Real.rpow_def_of_pos hy0]
    congr 1
    ring
  calc Q ≤ Real.exp (Real.log x ^ (1 - ε)) := hQ
    _ ≤ Real.exp (Real.log y / 3) := hmono
    _ = y ^ (1 / 3 : ℝ) := hthird

/-! ### Leaf 1: `smooth_remainder_identity` — basic facts about `smoothModulus` -/

/-- LEAF. Page 14 proof of display 50. The allowed Q is eventually
below Q0 equals y to the one third. This is the parameter reduction
needed to cancel the initial segment of the Euler product expansion. -/
theorem cutoff_order (ε : ℝ) (hε : 0 < ε) :
    ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      Q ≤ y ^ (1 / 3 : ℝ) :=
  cutoff_order_proved ε hε

/-- LEAF. Page 14 smooth tail bound below display 50, from Lemma 3.5
on page 12 and display 47. This numerical weighted smooth reciprocal
tail has no A2 coefficient or singular product. The exponent is A/2
because the target squares the complex norm. -/
theorem smooth_reciprocal_tail (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (smoothModulus Q),
        smoothWeight q Q * (localMajorant q / (q : ℝ))) ≤
          C / Real.log x ^ (A / 2) := by
  sorry

/-- Page 14 below display 50. Bound the complex tail by its numerical
majorant. CONDITIONAL on A2_coprime_mul. -/
theorem smooth_tail_norm (n : ℕ) (T Q : ℝ) :
    ‖∑ q ∈ Finset.Ioc ⌊T⌋₊ (smoothModulus Q),
      (smoothWeight q Q : ℂ) * U1534.A2 n q‖ ≤
    ∑ q ∈ Finset.Ioc ⌊T⌋₊ (smoothModulus Q),
      smoothWeight q Q * (localMajorant q / (q : ℝ)) := by
  calc
    _ ≤ ∑ q ∈ Finset.Ioc ⌊T⌋₊ (smoothModulus Q),
        ‖(smoothWeight q Q : ℂ) * U1534.A2 n q‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
      have hw : 0 ≤ smoothWeight q Q := by unfold smoothWeight; split <;> norm_num
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (coefficient_product_bound n q hqn) hw

/-- Page 14 display 50. Exact Task271a.smooth_remainder_pointwise
statement. CONDITIONAL on the exact finite identity, cutoff order,
numerical smooth reciprocal tail, and A2_coprime_mul. -/
theorem smooth_remainder_pointwise (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) → ∀ n : ℕ,
      ‖(series2 n P - product2 n Q) - tail2 n P (y ^ (1 / 3 : ℝ)) Q‖ ^ 2 ≤
        C / Real.log x ^ A := by
  obtain ⟨C, x0, hC, hx0, hb⟩ := smooth_reciprocal_tail A ε hA hε
  obtain ⟨x1, hx1, ho⟩ := cutoff_order ε hε
  refine ⟨C ^ 2, max x0 x1, by positivity, hx0.trans (le_max_left _ _), ?_⟩
  intro x y P Q hx hy hyx hP hPQ hQ n
  have hx0' : x0 ≤ x := (le_max_left _ _).trans hx
  have hx1' : x1 ≤ x := (le_max_right _ _).trans hx
  have hx2 : 2 ≤ x := hx0.trans hx0'
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  rw [smooth_remainder_identity n P Q _ hP hPQ (ho x y Q hx1' hy hQ), norm_neg]
  calc
    _ ≤ (C / Real.log x ^ (A / 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _)
        ((smooth_tail_norm n _ Q).trans (hb x y Q hx0' hy hyx (hP.trans_le hPQ) hQ)) 2
    _ = C ^ 2 / Real.log x ^ A := by
      have hp : (Real.log x ^ (A / 2)) ^ (2 : ℕ) = Real.log x ^ A := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le]
        congr 1
        push_cast
        ring
      rw [div_pow, hp]

end LeanLab.KumchevLiu2007.Task292c
