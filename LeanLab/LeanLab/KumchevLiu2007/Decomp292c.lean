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

set_option maxHeartbeats 2000000

/-! ### Smoothness bridges -/

private lemma le_of_smoothWeight_eq_one {q : ℕ} {Q : ℝ} (h : smoothWeight q Q = 1) :
    ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q := by
  by_cases hcond : ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q
  · exact hcond
  · rw [smoothWeight, if_neg hcond] at h
    exact absurd h (by norm_num)

private lemma smoothWeight_eq_zero_or_one (q : ℕ) (Q : ℝ) :
    smoothWeight q Q = 0 ∨ smoothWeight q Q = 1 := by
  unfold smoothWeight
  split <;> simp

/-- The file's smooth indicator is Mathlib's set of smooth numbers. -/
private lemma smoothWeight_eq_one_iff_mem_smoothNumbers (q : ℕ) (Q : ℝ) :
    smoothWeight q Q = 1 ↔ q ∈ Nat.smoothNumbers (⌊Q⌋₊ + 1) := by
  constructor
  · intro hw
    have hc := le_of_smoothWeight_eq_one hw
    refine Nat.mem_smoothNumbers'.mpr ?_
    intro p hp hpq
    have hle : (p : ℝ) ≤ Q := hc p hp hpq
    have hple : p ≤ ⌊Q⌋₊ := Nat.le_floor hle
    omega
  · intro hmem
    refine smoothWeight_eq_one_of_forall q Q ?_
    intro p hp hpq
    have hlt : p < ⌊Q⌋₊ + 1 := Nat.mem_smoothNumbers'.mp hmem p hp hpq
    have hple : p ≤ ⌊Q⌋₊ := by omega
    have hQ0 : (0 : ℝ) ≤ Q := by
      have h2 : 2 ≤ p := hp.two_le
      have hpos : 0 < ⌊Q⌋₊ := by omega
      linarith [Nat.floor_pos.mp hpos]
    exact le_trans (by exact_mod_cast hple) (Nat.floor_le hQ0)

/-- Product monotonicity for `ℝ` by hand. -/
private lemma prod_le_prod_real {ι : Type*} {s : Finset ι} {f g : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons ha, Finset.prod_cons ha]
    simp only [Finset.mem_cons, forall_eq_or_imp] at h0 h
    have hfs : 0 ≤ ∏ x ∈ s, f x := Finset.prod_nonneg h0.2
    exact mul_le_mul h.1 (ih h0.2 h.2) hfs (h0.1.trans h.1)

/-! ### Weak Mertens and elementary bounds (transplanted from Decomp271a) -/

private lemma prod_one_add_le_exp (s : Finset ℕ) (y : ℕ → ℝ) (hy : ∀ p ∈ s, 0 ≤ y p) :
    ∏ p ∈ s, (1 + y p) ≤ Real.exp (∑ p ∈ s, y p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Real.exp_add]
    have h1 : 1 + y a ≤ Real.exp (y a) := by
      simpa [add_comm] using Real.add_one_le_exp (y a)
    have h2 : ∏ p ∈ s, (1 + y p) ≤ Real.exp (∑ p ∈ s, y p) :=
      ih (fun p hp => hy p (Finset.mem_insert_of_mem hp))
    have h3 : (0 : ℝ) ≤ ∏ p ∈ s, (1 + y p) :=
      Finset.prod_nonneg (fun p hp => by
        have := hy p (Finset.mem_insert_of_mem hp); linarith)
    exact mul_le_mul h1 h2 h3 (Real.exp_nonneg _)

/-- The `sigma`-shifted weight is at most `7 p^(sigma-1)`. -/

private lemma one_div_succ_le_log_sub (K : ℕ) (hK : 1 ≤ K) :
    1 / ((K : ℝ) + 1) ≤ Real.log ((K : ℝ) + 1) - Real.log (K : ℝ) := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have h := Real.one_sub_inv_le_log_of_pos (x := ((K : ℝ) + 1) / (K : ℝ)) (by positivity)
  rw [Real.log_div (by positivity) (ne_of_gt hK0)] at h
  have hinv : (((K : ℝ) + 1) / (K : ℝ))⁻¹ = 1 - 1 / ((K : ℝ) + 1) := by
    field_simp
    ring
  rw [hinv] at h
  linarith

/-- Harmonic sum: `∑_{k<K} 1/(k+1) ≤ 1 + log K`. -/

private lemma sum_range_one_div_add_one_le (K : ℕ) :
    (∑ k ∈ Finset.range K, 1 / ((k : ℝ) + 1)) ≤ 1 + Real.log K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; norm_num
    · have hstep := one_div_succ_le_log_sub K hK
      have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith

/-- `∑_{j=1}^{K} 1/j ≤ 1 + log K`. -/

private lemma sum_Icc_one_div_le (K : ℕ) :
    (∑ j ∈ Finset.Icc 1 K, 1 / (j : ℝ)) ≤ 1 + Real.log K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; norm_num
    · rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1)]
      have hstep := one_div_succ_le_log_sub K hK
      have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith

/-- Chebyshev bounds the number of primes in a dyadic block. -/

private lemma card_primes_block_le (k : ℕ) (hk : 1 ≤ k) (s : Finset ℕ)
    (hsp : ∀ p ∈ s, p.Prime) (hlo : ∀ p ∈ s, 2 ^ k ≤ p) (hhi : ∀ p ∈ s, p ≤ 2 ^ (k + 1)) :
    (s.card : ℝ) ≤ Real.log 4 * (2 : ℝ) ^ (k + 1) / ((k : ℝ) * Real.log 2) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hpt : ∀ p ∈ s, (k : ℝ) * Real.log 2 ≤ Real.log (p : ℝ) := by
    intro p hp
    have hp2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hcast : (((2 ^ k : ℕ)) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
    have hkp : (2 : ℝ) ^ k ≤ (p : ℝ) := by
      have h : (((2 ^ k : ℕ)) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlo p hp
      rwa [hcast] at h
    have h := Real.log_le_log hp2 hkp
    rwa [Real.log_pow] at h
  have hsum : (s.card : ℝ) * ((k : ℝ) * Real.log 2) ≤ ∑ p ∈ s, Real.log (p : ℝ) := by
    have h := Finset.sum_le_sum hpt
    simpa [Finset.sum_const, nsmul_eq_mul] using h
  have htheta : (∑ p ∈ s, Real.log (p : ℝ)) ≤ Real.log 4 * (((2 ^ (k + 1) : ℕ)) : ℝ) := by
    have hsub : s ⊆ Nat.primesLE (2 ^ (k + 1)) := by
      intro p hp
      exact Nat.mem_primesLE.mpr ⟨hhi p hp, hsp p hp⟩
    have h1 : (∑ p ∈ s, Real.log (p : ℝ))
        ≤ ∑ p ∈ Nat.primesLE (2 ^ (k + 1)), Real.log (p : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
      intro p hp _
      exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
    rw [← Chebyshev.theta_eq_sum_primesLE_log (2 ^ (k + 1))] at h1
    have h3 := Chebyshev.theta_le_log4_mul_x
      (x := (((2 ^ (k + 1) : ℕ)) : ℝ)) (by positivity)
    linarith
  have hcast2 : (((2 ^ (k + 1) : ℕ)) : ℝ) = (2 : ℝ) ^ (k + 1) := by push_cast; ring
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) * Real.log 2)]
  calc (s.card : ℝ) * ((k : ℝ) * Real.log 2) ≤ ∑ p ∈ s, Real.log (p : ℝ) := hsum
    _ ≤ Real.log 4 * (((2 ^ (k + 1) : ℕ)) : ℝ) := htheta
    _ = Real.log 4 * (2 : ℝ) ^ (k + 1) := by rw [hcast2]

/-- `2 ^ Nat.log2 z ≤ z < 2 ^ (Nat.log2 z + 1)`. -/

private lemma log2_spec {z : ℕ} (hz : 0 < z) : 2 ^ Nat.log2 z ≤ z ∧ z < 2 ^ (Nat.log2 z + 1) := by
  refine ⟨(Nat.le_log2 hz.ne').mp le_rfl, ?_⟩
  by_contra hcon
  simp only [not_lt] at hcon
  have hle := (Nat.le_log2 hz.ne').mpr hcon
  omega

/-- Weak Mertens: the reciprocal prime sum is at most a constant times `log log`. -/

private lemma prime_sum_inv_le (z : ℕ) (hz : 2 ≤ z) :
    (∑ p ∈ Nat.primesLE z, 1 / (p : ℝ)) ≤ 40 * (1 + Real.log (1 + Real.log z)) := by
  classical
  have hz0 : z ≠ 0 := by omega
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (by omega : 1 < z)
  have hlogz : (0 : ℝ) < Real.log z := Real.log_pos hz1
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hKspec := log2_spec (z := z) (by omega : 0 < z)
  obtain ⟨h2K, -⟩ := hKspec
  have hmaps : ∀ p ∈ Nat.primesLE z, Nat.log2 p ∈ Finset.Icc 1 (Nat.log2 z) := by
    intro p hp
    obtain ⟨hpz, hpp⟩ := Nat.mem_primesLE.mp hp
    have hpne : p ≠ 0 := hpp.ne_zero
    have h2p : 2 ^ Nat.log2 p ≤ p := (Nat.le_log2 hpne).mp le_rfl
    have h2z : 2 ^ Nat.log2 p ≤ z := le_trans h2p hpz
    refine Finset.mem_Icc.mpr ⟨?_, (Nat.le_log2 hz0).mpr h2z⟩
    rw [Nat.le_log2 hpne]
    calc 2 ^ 1 = 2 := by norm_num
      _ ≤ p := hpp.two_le
  have hfiber : ∀ j ∈ Finset.Icc 1 (Nat.log2 z),
      (∑ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), 1 / (p : ℝ)) ≤ 6 / (j : ℝ) := by
    intro j hj
    obtain ⟨hj1, hjK⟩ := Finset.mem_Icc.mp hj
    have hsp : ∀ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), p.Prime :=
      fun p hp => (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
    have hlo : ∀ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), 2 ^ j ≤ p := by
      intro p hp
      have hpe : Nat.log2 p = j := (Finset.mem_filter.mp hp).2
      have hpne : p ≠ 0 := (hsp p hp).ne_zero
      rw [← hpe]
      exact (Nat.le_log2 hpne).mp le_rfl
    have hhi : ∀ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), p ≤ 2 ^ (j + 1) := by
      intro p hp
      have hpe : Nat.log2 p = j := (Finset.mem_filter.mp hp).2
      have hpne : p ≠ 0 := (hsp p hp).ne_zero
      have hlt : p < 2 ^ (Nat.log2 p + 1) := (log2_spec hpne.bot_lt).2
      rw [hpe] at hlt
      omega
    have hcard := card_primes_block_le j hj1 _ hsp hlo hhi
    have hpoint : ∀ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j),
        1 / (p : ℝ) ≤ 1 / (2 : ℝ) ^ j := by
      intro p hp
      have hp2 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
      have hpj : (2 : ℝ) ^ j ≤ (p : ℝ) := by
        have hcast : (((2 ^ j : ℕ)) : ℝ) = (2 : ℝ) ^ j := by push_cast; ring
        have h : (((2 ^ j : ℕ)) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlo p hp
        rwa [hcast] at h
      exact one_div_le_one_div_of_le hp2 hpj
    have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    calc (∑ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), 1 / (p : ℝ))
        ≤ ∑ _p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), 1 / (2 : ℝ) ^ j :=
          Finset.sum_le_sum hpoint
      _ = (((Nat.primesLE z).filter (fun p => Nat.log2 p = j)).card : ℝ) * (1 / (2 : ℝ) ^ j) := by
          simp [Finset.sum_const, nsmul_eq_mul]
      _ = (((Nat.primesLE z).filter (fun p => Nat.log2 p = j)).card : ℝ) / (2 : ℝ) ^ j := by ring
      _ ≤ (Real.log 4 * (2 : ℝ) ^ (j + 1) / ((j : ℝ) * Real.log 2)) / (2 : ℝ) ^ j :=
          div_le_div_of_nonneg_right hcard h2j.le
      _ = 4 / (j : ℝ) := by
          rw [hlog4]
          field_simp
          ring
      _ ≤ 6 / (j : ℝ) := div_le_div_of_nonneg_right (by norm_num) hjR.le
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun p => 1 / (p : ℝ))]
  have hKpos : 1 ≤ Nat.log2 z := by
    have hmem : Nat.log2 2 ∈ Finset.Icc 1 (Nat.log2 z) :=
      hmaps 2 (Nat.mem_primesLE.mpr ⟨hz, Nat.prime_two⟩)
    rw [show Nat.log2 2 = 1 by decide] at hmem
    exact (Finset.mem_Icc.mp hmem).2
  have hKle : ((Nat.log2 z : ℕ) : ℝ) * Real.log 2 ≤ Real.log z := by
    have hcast : (((2 ^ Nat.log2 z : ℕ)) : ℝ) = (2 : ℝ) ^ Nat.log2 z := by push_cast; ring
    have h : (((2 ^ Nat.log2 z : ℕ)) : ℝ) ≤ (z : ℝ) := by exact_mod_cast h2K
    rw [hcast] at h
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ Nat.log2 z := by positivity
    have hlog := Real.log_le_log h2pos h
    rw [Real.log_pow] at hlog
    exact hlog
  have hKle' : ((Nat.log2 z : ℕ) : ℝ) ≤ Real.log z / Real.log 2 := by
    rw [le_div_iff₀ hlog2]
    exact hKle
  have hloglog : Real.log ((Nat.log2 z : ℕ) : ℝ) ≤ Real.log (Real.log z) + 1 := by
    have hKR : (0 : ℝ) < ((Nat.log2 z : ℕ) : ℝ) := by exact_mod_cast hKpos
    have h1 : Real.log ((Nat.log2 z : ℕ) : ℝ) ≤ Real.log (Real.log z / Real.log 2) :=
      Real.log_le_log hKR hKle'
    rw [Real.log_div hlogz.ne' hlog2.ne'] at h1
    have h2 : -Real.log (Real.log 2) ≤ 1 := by
      have hexp : Real.exp (-1) < Real.log 2 := by
        have h1 : Real.exp (-1) < 0.4 := by
          rw [Real.exp_neg]
          rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num : (0:ℝ) < 0.4)]
          have := Real.exp_one_gt_d9
          norm_num
          linarith
        linarith [Real.log_two_gt_d9]
      have h3 := Real.le_log_iff_exp_le hlog2 |>.mpr hexp.le
      linarith
    linarith
  have hlog1 : Real.log (1 + Real.log z) ≥ 0 := Real.log_nonneg (by linarith)
  calc (∑ j ∈ Finset.Icc 1 (Nat.log2 z),
        ∑ p ∈ (Nat.primesLE z).filter (fun p => Nat.log2 p = j), 1 / (p : ℝ))
      ≤ ∑ j ∈ Finset.Icc 1 (Nat.log2 z), 6 / (j : ℝ) := Finset.sum_le_sum hfiber
    _ = 6 * ∑ j ∈ Finset.Icc 1 (Nat.log2 z), 1 / (j : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ 6 * (1 + Real.log ((Nat.log2 z : ℕ) : ℝ)) := by
        have := sum_Icc_one_div_le (Nat.log2 z)
        linarith
    _ ≤ 40 * (1 + Real.log (1 + Real.log z)) := by
        have hLL : Real.log (Real.log z) ≤ Real.log (1 + Real.log z) :=
          Real.log_le_log hlogz (by linarith)
        linarith

/-- The elementary bound `log u ≤ u^t / t` at `u ≥ 1`. -/

private lemma log_le_rpow_div {u t : ℝ} (hu : 1 ≤ u) (ht : 0 < t) :
    Real.log u ≤ u ^ t / t := by
  have hu0 : (0 : ℝ) < u := by linarith
  have h1 : Real.log (u ^ t) = t * Real.log u := Real.log_rpow hu0 t
  have h2 : Real.log (u ^ t) ≤ u ^ t - 1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hu0 t)
  have hut : (1 : ℝ) ≤ u ^ t := Real.one_le_rpow hu ht.le
  rw [le_div_iff₀ ht]
  nlinarith [h1, h2]


/-- `log u + 2 ≤ 6 u^(ε/4)/ε` for `u ≥ 1`, `0 < ε ≤ 1`. -/

private lemma logu_add_two_le {u ε : ℝ} (hu : 1 ≤ u) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.log u + 2 ≤ 6 * u ^ (ε / 4) / ε := by
  have hu0 : (0 : ℝ) < u := by linarith
  have ht : (0 : ℝ) < ε / 4 := by linarith
  have hP : (0 : ℝ) < u ^ (ε / 4) := Real.rpow_pos_of_pos hu0 _
  have h1 : Real.log u ≤ u ^ (ε / 4) / (ε / 4) := log_le_rpow_div hu ht
  have h2 : u ^ (ε / 4) / (ε / 4) = 4 * u ^ (ε / 4) / ε := by field_simp
  rw [h2] at h1
  have h3 : (1 : ℝ) ≤ u ^ (ε / 4) := Real.one_le_rpow hu ht.le
  have h5 : 2 ≤ 2 * u ^ (ε / 4) / ε := by
    rw [le_div_iff₀ hε]
    nlinarith [hP, h3, hε1]
  have h7 : 4 * u ^ (ε / 4) / ε + 2 * u ^ (ε / 4) / ε = 6 * u ^ (ε / 4) / ε := by ring
  linarith

/-- `(X^(4/(3ε)))^((3ε)/4) = X`. -/

private lemma rpow_mul_self {X ε : ℝ} (hX : 0 ≤ X) (hε : 0 < ε) :
    (X ^ (4 / (3 * ε))) ^ ((3 * ε) / 4) = X := by
  rw [← Real.rpow_mul hX]
  rw [show 4 / (3 * ε) * ((3 * ε) / 4) = 1 by field_simp]
  rw [Real.rpow_one]

/-- Crossing a `rpow` threshold: `u ≥ X^(4/(3ε))` gives `X ≤ u^((3ε)/4)`. -/

private lemma rpow_threshold {X ε u : ℝ} (hX : 0 ≤ X) (hε : 0 < ε)
    (hu : X ^ (4 / (3 * ε)) ≤ u) : X ≤ u ^ ((3 * ε) / 4) := by
  have h1 : (X ^ (4 / (3 * ε))) ^ ((3 * ε) / 4) ≤ u ^ ((3 * ε) / 4) := by
    apply Real.rpow_le_rpow (Real.rpow_nonneg hX _) hu
    positivity
  rwa [rpow_mul_self hX hε] at h1


/-- Stage 1 of the assembly: the remainder is bounded by the numerical majorant of
the `A2` mass of the subset tail above `Q0`. -/

private lemma exp_majorant_le {A u L M σ T : ℝ} (hA0 : 0 ≤ A) (hu : 1 ≤ u)
    (hX : 0 ≤ 1 + Real.log (1 + L)) (hσM : σ * M = 2 * T) (hσL : σ * L ≤ 1)
    (hT : T = A * Real.log u + 800 * (1 + Real.log (1 + L)) + 2) :
    Real.exp (-(σ * M) + 7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L)))))
      ≤ 1 / u ^ A := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have h1 : Real.exp (σ * L) ≤ Real.exp 1 := Real.exp_le_exp.mpr hσL
  have h2 : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
  have h3 : 7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))))
      ≤ 7 * (2.72 * (40 * (1 + Real.log (1 + L)))) := by
    have h4 : Real.exp (σ * L) * (40 * (1 + Real.log (1 + L)))
        ≤ 2.72 * (40 * (1 + Real.log (1 + L))) :=
      mul_le_mul_of_nonneg_right (le_trans h1 h2) (by linarith)
    linarith
  have h5 : -(σ * M) + 7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))))
      ≤ -A * Real.log u - 1 := by
    rw [hσM, hT]
    nlinarith [h3, hlogu, hX, hA0]
  have h6 : Real.exp (-(σ * M) + 7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L)))))
      ≤ Real.exp (-A * Real.log u - 1) := Real.exp_le_exp.mpr h5
  have h7 : Real.exp (-A * Real.log u - 1) ≤ Real.exp (-A * Real.log u) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h8 : Real.exp (-A * Real.log u) = u ^ (-A) := by
    rw [Real.rpow_def_of_pos hu0]
    congr 1
    ring
  have h9 : u ^ (-A) = 1 / u ^ A := by
    rw [Real.rpow_neg hu0.le, one_div]
  calc Real.exp (-(σ * M) + 7 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L)))))
      ≤ Real.exp (-A * Real.log u - 1) := h6
    _ ≤ Real.exp (-A * Real.log u) := h7
    _ = u ^ (-A) := h8
    _ = 1 / u ^ A := h9


/-! ### The local majorant: positivity and multiplicativity -/

private lemma localMajorant_pos (q : ℕ) : 0 < localMajorant q := by
  rw [localMajorant]
  refine Finset.prod_pos (fun p hp => ?_)
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have h6 : (0 : ℝ) ≤ 6 / (p : ℝ) := by positivity
  linarith

private lemma localMajorant_nonneg (q : ℕ) : 0 ≤ localMajorant q := (localMajorant_pos q).le

private lemma localMajorant_one : localMajorant 1 = 1 := by
  simp [localMajorant]

private lemma localMajorant_mul {a b : ℕ} (hab : a.Coprime b) :
    localMajorant (a * b) = localMajorant a * localMajorant b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have hb : b = 1 := (Nat.coprime_zero_left b).mp hab
    subst hb
    simp [localMajorant]
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    have ha1 : a = 1 := (Nat.coprime_zero_right a).mp hab
    subst ha1
    simp [localMajorant]
  rw [localMajorant, localMajorant, localMajorant, Nat.primeFactors_mul ha.ne' hb.ne']
  refine Finset.prod_union ?_
  rw [Finset.disjoint_left]
  intro p hpa hpb
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpa
  have hpa' : p ∣ a := Nat.dvd_of_mem_primeFactors hpa
  have hpb' : p ∣ b := Nat.dvd_of_mem_primeFactors hpb
  have hg : p ∣ a.gcd b := Nat.dvd_gcd hpa' hpb'
  rw [show a.gcd b = 1 from hab] at hg
  exact hp.ne_one (Nat.dvd_one.mp hg)

private lemma localMajorant_prime_pow (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    localMajorant (p ^ k) = 1 + 6 / (p : ℝ) := by
  rw [localMajorant, Nat.primeFactors_pow p (by omega : k ≠ 0), Nat.Prime.primeFactors hp,
    Finset.prod_singleton]

private lemma localMajorant_zero : localMajorant 0 = 1 := by
  simp [localMajorant]

/-- `(a^k)^e = (a^e)^k` for `a ≥ 0`. -/
private lemma rpow_pow_comm (a : ℝ) (ha : 0 ≤ a) (e : ℝ) (k : ℕ) :
    ((a ^ k : ℝ)) ^ e = (a ^ e) ^ k := by
  rw [← Real.rpow_natCast a k, ← Real.rpow_natCast (a ^ e) k, ← Real.rpow_mul ha,
    ← Real.rpow_mul ha]
  congr 1
  ring

/-! ### The local Euler factor of the Rankin-weighted smooth sum -/

private lemma local_factor_le (p : ℕ) (hp : p.Prime) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2) :
    (∑' n : ℕ, localMajorant (p ^ n) * (((p ^ n : ℕ)) : ℝ) ^ (σ - 1))
      ≤ 1 + 28 * (p : ℝ) ^ (σ - 1) := by
  classical
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  set x : ℝ := (p : ℝ) ^ (σ - 1) with hxdef
  have hx0 : 0 ≤ x := Real.rpow_nonneg hp0.le _
  have hσm : σ - 1 < 0 := by linarith
  have hx1 : x < 1 := by
    rw [hxdef, Real.rpow_lt_one_iff hp0.le]
    exact Or.inr (Or.inl ⟨hp1, hσm⟩)
  -- numeric: `x ≤ 3/4`
  have hsq : ((2 : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = 2 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (1 / 2 : ℝ)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hs0 : 0 ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h34 : (4 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := by nlinarith [hsq, hs0]
  have hx34 : x ≤ 3 / 4 := by
    have hexp1 : 0 ≤ 1 - σ := by linarith
    have h1 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 - σ) :=
      (Real.rpow_le_rpow_left_iff (by norm_num)).mpr (by linarith)
    have h2 : (2 : ℝ) ^ (1 - σ) ≤ (p : ℝ) ^ (1 - σ) :=
      Real.rpow_le_rpow (by norm_num) hp2 hexp1
    have h3 : (4 / 3 : ℝ) ≤ (p : ℝ) ^ (1 - σ) := le_trans h34 (le_trans h1 h2)
    have h4 : ((p : ℝ) ^ (1 - σ))⁻¹ = x := by
      rw [hxdef, ← Real.rpow_neg hp0.le]
      congr 1
      ring
    have hinv : ((p : ℝ) ^ (1 - σ))⁻¹ ≤ ((4 / 3 : ℝ))⁻¹ :=
      (inv_le_inv₀ (a := (p : ℝ) ^ (1 - σ)) (b := 4 / 3)
        (Real.rpow_pos_of_pos hp0 _) (by norm_num)).mpr h3
    rw [h4] at hinv
    have : ((4 / 3 : ℝ))⁻¹ = 3 / 4 := by norm_num
    rwa [this] at hinv
  have hxpos : 0 < x := Real.rpow_pos_of_pos hp0 _
  -- the sequence and its two-term description
  set g : ℕ → ℝ := fun n => localMajorant (p ^ n) * (((p ^ n : ℕ)) : ℝ) ^ (σ - 1) with hgdef
  have hg0 : g 0 = 1 := by
    simp only [hgdef, pow_zero, Nat.cast_one, Real.one_rpow, localMajorant_one, mul_one]
  have hgsucc : ∀ n : ℕ, g (n + 1) = (1 + 6 / (p : ℝ)) * x ^ (n + 1) := by
    intro n
    have hk : 1 ≤ n + 1 := by omega
    have hlm : localMajorant (p ^ (n + 1)) = 1 + 6 / (p : ℝ) :=
      localMajorant_prime_pow p (n + 1) hp hk
    have hcast : (((p ^ (n + 1) : ℕ)) : ℝ) = (p : ℝ) ^ (n + 1) := by push_cast; ring
    have hpow : ((((p ^ (n + 1) : ℕ)) : ℝ)) ^ (σ - 1) = x ^ (n + 1) := by
      rw [hcast, hxdef]
      exact rpow_pow_comm (p : ℝ) hp0.le (σ - 1) (n + 1)
    simp only [hgdef, hlm, hpow]
  -- summability
  have hgeo : Summable (fun n : ℕ => (1 + 6 / (p : ℝ)) * x ^ n) :=
    (summable_geometric_of_lt_one hx0 hx1).mul_left _
  have hsumm : Summable g := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgeo
    · have h1 : (0 : ℝ) ≤ localMajorant (p ^ n) := localMajorant_nonneg _
      have h2 : (0 : ℝ) ≤ (((p ^ n : ℕ)) : ℝ) ^ (σ - 1) :=
        Real.rpow_nonneg (by positivity) _
      exact mul_nonneg h1 h2
    · rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        rw [hg0]
        have h6 : (0 : ℝ) ≤ 6 / (p : ℝ) := by positivity
        have : (1 : ℝ) * x ^ 0 = 1 := by simp
        calc (1 : ℝ) ≤ 1 + 6 / (p : ℝ) := by linarith
          _ = (1 + 6 / (p : ℝ)) * x ^ 0 := by simp
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
        subst hk
        rw [hgsucc]
  -- the value of the series
  have htsum : (∑' n : ℕ, g n) = 1 + (1 + 6 / (p : ℝ)) * (x * (1 - x)⁻¹) := by
    rw [hsumm.tsum_eq_zero_add, hg0]
    have hshift : (∑' n : ℕ, g (n + 1)) = (1 + 6 / (p : ℝ)) * (x * (1 - x)⁻¹) := by
      have h1 : (∑' n : ℕ, g (n + 1)) = ∑' n : ℕ, (1 + 6 / (p : ℝ)) * x ^ (n + 1) :=
        tsum_congr hgsucc
      rw [h1, tsum_mul_left]
      congr 1
      have h2 : (fun n : ℕ => x ^ (n + 1)) = fun n : ℕ => x * x ^ n := by
        funext n; rw [pow_succ]; ring
      rw [h2, tsum_mul_left, tsum_geometric_of_lt_one hx0 hx1]
    rw [hshift]
  rw [htsum]
  -- final numerical comparison
  have h4inv : (1 - x)⁻¹ ≤ 4 := by
    have h1 : (1 / 4 : ℝ) ≤ 1 - x := by linarith
    have h2 : (0 : ℝ) < 1 - x := by linarith
    calc (1 - x)⁻¹ ≤ ((1 / 4 : ℝ))⁻¹ :=
          (inv_le_inv₀ (a := 1 - x) (b := 1 / 4) h2 (by norm_num)).mpr h1
      _ = 4 := by norm_num
  have h6 : 1 + 6 / (p : ℝ) ≤ 7 := by
    have : 6 / (p : ℝ) ≤ 3 := by
      rw [div_le_iff₀ hp0]; linarith
    linarith
  have h7 : 1 + 6 / (p : ℝ) ≤ 7 := h6
  have hxr : x * (1 - x)⁻¹ ≤ 4 * x := by
    have := mul_le_mul_of_nonneg_left h4inv hx0
    linarith
  have hstep : (1 + 6 / (p : ℝ)) * (x * (1 - x)⁻¹) ≤ 7 * (4 * x) := by
    have h1 : (0 : ℝ) ≤ x * (1 - x)⁻¹ := by
      have : (0 : ℝ) ≤ (1 - x)⁻¹ := by positivity
      positivity
    exact mul_le_mul h6 hxr h1 (by norm_num)
  linarith

/-- Summability of the local factors. -/
private lemma local_factor_summable (p : ℕ) (hp : p.Prime) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ1 : σ ≤ 1 / 2) :
    Summable (fun n : ℕ => localMajorant (p ^ n) * (((p ^ n : ℕ)) : ℝ) ^ (σ - 1)) := by
  classical
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  set x : ℝ := (p : ℝ) ^ (σ - 1) with hxdef
  have hx0 : 0 ≤ x := Real.rpow_nonneg hp0.le _
  have hσm : σ - 1 < 0 := by linarith
  have hx1 : x < 1 := by
    rw [hxdef, Real.rpow_lt_one_iff hp0.le]
    exact Or.inr (Or.inl ⟨hp1, hσm⟩)
  have hgeo : Summable (fun n : ℕ => (1 + 6 / (p : ℝ)) * x ^ n) :=
    (summable_geometric_of_lt_one hx0 hx1).mul_left _
  have hgsucc : ∀ n : ℕ,
      localMajorant (p ^ (n + 1)) * (((p ^ (n + 1) : ℕ)) : ℝ) ^ (σ - 1)
        = (1 + 6 / (p : ℝ)) * x ^ (n + 1) := by
    intro n
    have hk : 1 ≤ n + 1 := by omega
    have hlm : localMajorant (p ^ (n + 1)) = 1 + 6 / (p : ℝ) :=
      localMajorant_prime_pow p (n + 1) hp hk
    have hcast : (((p ^ (n + 1) : ℕ)) : ℝ) = (p : ℝ) ^ (n + 1) := by push_cast; ring
    have hpow : ((((p ^ (n + 1) : ℕ)) : ℝ)) ^ (σ - 1) = x ^ (n + 1) := by
      rw [hcast, hxdef]
      exact rpow_pow_comm (p : ℝ) hp0.le (σ - 1) (n + 1)
    rw [hlm, hpow]
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgeo
  · exact mul_nonneg (localMajorant_nonneg _) (Real.rpow_nonneg (by positivity) _)
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      have h6 : (0 : ℝ) ≤ 6 / (p : ℝ) := by positivity
      simp only [pow_zero, Nat.cast_one, Real.one_rpow, localMajorant_one, mul_one]
      linarith
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      subst hk
      rw [hgsucc]

/-- Rankin-weighted smooth sum bounded by the Euler product over the primes below `⌊Q⌋₊ + 1`. -/
private lemma sum_smooth_le_euler (B : ℕ) (Q : ℝ) (hQ : 1 ≤ Q)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2) :
    (∑ q ∈ (Finset.range (B + 1)).filter (fun q => q ∈ Nat.smoothNumbers (⌊Q⌋₊ + 1)),
        localMajorant q * (q : ℝ) ^ (σ - 1))
      ≤ Real.exp (28 * (Real.exp (σ * Real.log (⌊Q⌋₊ + 1))
          * (40 * (1 + Real.log (1 + Real.log (⌊Q⌋₊ + 1)))))) := by
  classical
  set K : ℕ := ⌊Q⌋₊ + 1 with hKdef
  have hQ0 : (0 : ℝ) ≤ Q := by linarith
  have hfloor : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ)
  have hK2 : 2 ≤ K := by omega
  set f : ℕ → ℝ := fun q => localMajorant q * (q : ℝ) ^ (σ - 1) with hfdef
  have hf1 : f 1 = 1 := by
    simp only [hfdef, Nat.cast_one, Real.one_rpow, localMajorant_one, mul_one]
  have hmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    have hlm : localMajorant (m * n) = localMajorant m * localMajorant n :=
      localMajorant_mul hmn
    have hcast : (((m * n : ℕ)) : ℝ) = (m : ℝ) * (n : ℝ) := by push_cast; ring
    have hrpow : (((m * n : ℕ)) : ℝ) ^ (σ - 1)
        = (m : ℝ) ^ (σ - 1) * (n : ℝ) ^ (σ - 1) := by
      rw [hcast, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    simp only [hfdef, hlm, hrpow]
    ring
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ => ‖f (p ^ n)‖) := by
    intro p hp
    have h1 := local_factor_summable p hp hσ0 hσ1
    refine h1.congr (fun n => ?_)
    have hnn : (0 : ℝ) ≤ localMajorant (p ^ n) * (((p ^ n : ℕ)) : ℝ) ^ (σ - 1) :=
      mul_nonneg (localMajorant_nonneg _) (Real.rpow_nonneg (by positivity) _)
    simp only [hfdef, Real.norm_eq_abs, abs_of_nonneg hnn]
  obtain ⟨-, hHas⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum (R := ℝ)
      (f := f) hf1 hmul hsum K
  have hHas_ind : HasSum ((K.smoothNumbers : Set ℕ).indicator f)
      (∏ p ∈ K.primesBelow, ∑' n : ℕ, f (p ^ n)) :=
    hasSum_subtype_iff_indicator.mp hHas
  have hnonneg : ∀ i : ℕ, 0 ≤ ((K.smoothNumbers : Set ℕ).indicator f) i := by
    intro i
    by_cases hi : i ∈ (K.smoothNumbers : Set ℕ)
    · rw [Set.indicator_of_mem hi]
      exact mul_nonneg (localMajorant_nonneg _) (Real.rpow_nonneg (by positivity) _)
    · rw [Set.indicator_of_notMem hi]
  have hstep1 : (∑ q ∈ (Finset.range (B + 1)).filter (fun q => q ∈ Nat.smoothNumbers K), f q)
      ≤ ∏ p ∈ K.primesBelow, ∑' n : ℕ, f (p ^ n) := by
    have h1 : (∑ q ∈ (Finset.range (B + 1)).filter (fun q => q ∈ Nat.smoothNumbers K), f q)
        = ∑ q ∈ Finset.range (B + 1), ((K.smoothNumbers : Set ℕ).indicator f) q := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      by_cases hq : q ∈ Nat.smoothNumbers K
      · rw [if_pos hq, Set.indicator_of_mem hq]
      · rw [if_neg hq, Set.indicator_of_notMem hq]
    rw [h1]
    exact sum_le_hasSum _ (fun i _ => hnonneg i) hHas_ind
  refine hstep1.trans ?_
  -- bound the product of local factors
  have hloc : ∀ p ∈ K.primesBelow, (∑' n : ℕ, f (p ^ n)) ≤ 1 + 28 * (p : ℝ) ^ (σ - 1) := by
    intro p hp
    have hpp : p.Prime := (Nat.mem_primesBelow.mp hp).2
    exact local_factor_le p hpp hσ0 hσ1
  have hprod : (∏ p ∈ K.primesBelow, ∑' n : ℕ, f (p ^ n))
      ≤ ∏ p ∈ K.primesBelow, (1 + 28 * (p : ℝ) ^ (σ - 1)) := by
    refine prod_le_prod_real (fun p _ => tsum_nonneg (fun n => ?_)) hloc
    exact mul_nonneg (localMajorant_nonneg _) (Real.rpow_nonneg (by positivity) _)
  refine hprod.trans ?_
  have hprod2 : (∏ p ∈ K.primesBelow, (1 + 28 * (p : ℝ) ^ (σ - 1)))
      ≤ Real.exp (∑ p ∈ K.primesBelow, 28 * (p : ℝ) ^ (σ - 1)) :=
    prod_one_add_le_exp _ _ (fun p _ => by positivity)
  refine hprod2.trans (Real.exp_le_exp.mpr ?_)
  -- bound the prime sum
  have hlogK : 0 < Real.log (K : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < K)
  have hterm : ∀ p ∈ K.primesBelow, (p : ℝ) ^ (σ - 1) ≤ Real.exp (σ * Real.log (K : ℝ)) * (1 / (p : ℝ)) := by
    intro p hp
    obtain ⟨hpK, hpp⟩ := Nat.mem_primesBelow.mp hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hpK' : (p : ℝ) ≤ (K : ℝ) := by exact_mod_cast le_of_lt hpK
    have hsplit : (p : ℝ) ^ (σ - 1) = (p : ℝ) ^ σ / (p : ℝ) := by
      rw [Real.rpow_sub hp0 σ 1, Real.rpow_one]
    have h1 : (p : ℝ) ^ σ ≤ (K : ℝ) ^ σ := Real.rpow_le_rpow hp0.le hpK' hσ0.le
    have h2 : (K : ℝ) ^ σ = Real.exp (σ * Real.log (K : ℝ)) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      congr 1
      ring
    have hgoal : (p : ℝ) ^ σ / (p : ℝ) ≤ (K : ℝ) ^ σ * (1 / (p : ℝ)) := by
      calc (p : ℝ) ^ σ / (p : ℝ) ≤ (K : ℝ) ^ σ / (p : ℝ) :=
            div_le_div_of_nonneg_right h1 hp0.le
        _ = (K : ℝ) ^ σ * (1 / (p : ℝ)) := by ring
    rw [hsplit]
    calc (p : ℝ) ^ σ / (p : ℝ) ≤ (K : ℝ) ^ σ * (1 / (p : ℝ)) := hgoal
      _ = Real.exp (σ * Real.log (K : ℝ)) * (1 / (p : ℝ)) := by rw [h2]
  have hsum1 : (∑ p ∈ K.primesBelow, (p : ℝ) ^ (σ - 1))
      ≤ Real.exp (σ * Real.log (K : ℝ)) * (40 * (1 + Real.log (1 + Real.log (K : ℝ)))) := by
    have h1 : (∑ p ∈ K.primesBelow, (p : ℝ) ^ (σ - 1))
        ≤ ∑ p ∈ K.primesBelow, Real.exp (σ * Real.log (K : ℝ)) * (1 / (p : ℝ)) :=
      Finset.sum_le_sum hterm
    have h2 : (∑ p ∈ K.primesBelow, Real.exp (σ * Real.log (K : ℝ)) * (1 / (p : ℝ)))
        = Real.exp (σ * Real.log (K : ℝ)) * ∑ p ∈ K.primesBelow, 1 / (p : ℝ) := by
      rw [Finset.mul_sum]
    have h3 : (∑ p ∈ K.primesBelow, 1 / (p : ℝ)) ≤ ∑ p ∈ Nat.primesLE K, 1 / (p : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p _ _ => by positivity)
      exact Nat.mem_primesLE.mpr ⟨le_of_lt (Nat.mem_primesBelow.mp hp).1, (Nat.mem_primesBelow.mp hp).2⟩
    have h4 : (∑ p ∈ Nat.primesLE K, 1 / (p : ℝ))
        ≤ 40 * (1 + Real.log (1 + Real.log (K : ℝ))) := prime_sum_inv_le K hK2
    calc (∑ p ∈ K.primesBelow, (p : ℝ) ^ (σ - 1))
        ≤ ∑ p ∈ K.primesBelow, Real.exp (σ * Real.log (K : ℝ)) * (1 / (p : ℝ)) := h1
      _ = Real.exp (σ * Real.log (K : ℝ)) * ∑ p ∈ K.primesBelow, 1 / (p : ℝ) := h2
      _ ≤ Real.exp (σ * Real.log (K : ℝ)) * (40 * (1 + Real.log (1 + Real.log (K : ℝ)))) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) (Real.exp_pos _).le
  have hfin : (∑ p ∈ K.primesBelow, 28 * (p : ℝ) ^ (σ - 1))
      ≤ 28 * (Real.exp (σ * Real.log (K : ℝ)) * (40 * (1 + Real.log (1 + Real.log (K : ℝ))))) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsum1 (by norm_num)
  simpa [hKdef, Nat.cast_add, Nat.cast_one] using hfin

/-- Rankin's trick: the smooth reciprocal tail is at most `N^{-σ}` times the
Rankin-weighted smooth sum over `[1, M]`. -/
private lemma smooth_sum_rankin (N M : ℕ) (Q : ℝ) {σ : ℝ} (hσ : 0 < σ) (hN : 1 ≤ N) :
    (∑ q ∈ Finset.Ioc N M, smoothWeight q Q * (localMajorant q / (q : ℝ)))
      ≤ (N : ℝ) ^ (-σ) *
          (∑ q ∈ (Finset.range (M + 1)).filter (fun q => q ∈ Nat.smoothNumbers (⌊Q⌋₊ + 1)),
            localMajorant q * (q : ℝ) ^ (σ - 1)) := by
  classical
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hpoint : ∀ q ∈ Finset.Ioc N M,
      smoothWeight q Q * (localMajorant q / (q : ℝ))
        ≤ (N : ℝ) ^ (-σ) * (if q ∈ Nat.smoothNumbers (⌊Q⌋₊ + 1)
            then localMajorant q * (q : ℝ) ^ (σ - 1) else 0) := by
    intro q hq
    obtain ⟨hqN, -⟩ := Finset.mem_Ioc.mp hq
    have hqpos : 0 < q := by omega
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
    by_cases hsm : q ∈ Nat.smoothNumbers (⌊Q⌋₊ + 1)
    · rw [if_pos hsm, (smoothWeight_eq_one_iff_mem_smoothNumbers q Q).mpr hsm, one_mul]
      have hge : (1 : ℝ) ≤ (q : ℝ) / (N : ℝ) := by
        rw [le_div_iff₀ hNpos]
        have hle : (N : ℝ) ≤ (q : ℝ) := by exact_mod_cast le_of_lt hqN
        linarith
      have h1 : (1 : ℝ) ≤ ((q : ℝ) / (N : ℝ)) ^ σ := Real.one_le_rpow hge hσ.le
      have h2 : ((q : ℝ) / (N : ℝ)) ^ σ = (q : ℝ) ^ σ * (N : ℝ) ^ (-σ) := by
        rw [Real.div_rpow hq0.le hNpos.le, Real.rpow_neg hNpos.le]
        ring
      have h3 : (q : ℝ) ^ (σ - 1) = (q : ℝ) ^ (-1 : ℝ) * (q : ℝ) ^ σ := by
        rw [← Real.rpow_add hq0]
        congr 1
        ring
      have hkey : (q : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-σ) * (q : ℝ) ^ (σ - 1) := by
        have h4 : (N : ℝ) ^ (-σ) * (q : ℝ) ^ (σ - 1)
            = (q : ℝ) ^ (-1 : ℝ) * ((q : ℝ) / (N : ℝ)) ^ σ := by
          rw [h3, h2]
          ring
        rw [h4]
        exact le_mul_of_one_le_right (Real.rpow_nonneg hq0.le _) h1
      have hqinv : localMajorant q / (q : ℝ) = localMajorant q * (q : ℝ) ^ (-1 : ℝ) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      calc localMajorant q / (q : ℝ) = localMajorant q * (q : ℝ) ^ (-1 : ℝ) := hqinv
        _ ≤ localMajorant q * ((N : ℝ) ^ (-σ) * (q : ℝ) ^ (σ - 1)) :=
            mul_le_mul_of_nonneg_left hkey (localMajorant_nonneg q)
        _ = (N : ℝ) ^ (-σ) * (localMajorant q * (q : ℝ) ^ (σ - 1)) := by ring
    · rw [if_neg hsm]
      have hw : smoothWeight q Q = 0 := by
        rcases smoothWeight_eq_zero_or_one q Q with h | h
        · exact h
        · exact absurd ((smoothWeight_eq_one_iff_mem_smoothNumbers q Q).mp h) hsm
      rw [hw, zero_mul, mul_zero]
  refine (Finset.sum_le_sum hpoint).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hNpos.le _)
  have hleft : (∑ q ∈ Finset.Ioc N M,
        (if q ∈ Nat.smoothNumbers (⌊Q⌋₊ + 1) then localMajorant q * (q : ℝ) ^ (σ - 1) else 0))
      = ∑ q ∈ (Finset.Ioc N M).filter (fun q => q ∈ Nat.smoothNumbers (⌊Q⌋₊ + 1)),
          localMajorant q * (q : ℝ) ^ (σ - 1) :=
    (Finset.sum_filter _ _).symm
  rw [hleft]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨?_, hq2⟩
    rw [Finset.mem_range]
    have := (Finset.mem_Ioc.mp hq1).2
    omega
  · intro q _ _
    exact mul_nonneg (localMajorant_nonneg _) (Real.rpow_nonneg (by positivity) _)

/-- The leaf `smooth_reciprocal_tail`, proved. -/
private lemma smooth_reciprocal_tail_proved (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y Q : ℝ,
      x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ q ∈ Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ (smoothModulus Q),
        smoothWeight q Q * (localMajorant q / (q : ℝ))) ≤
          C / Real.log x ^ (A / 2) := by
  classical
  have hA0 : 0 ≤ A := by linarith
  have hεpos : 0 < ε := hε
  set X₀ : ℝ := 2000 * (A + 6002) / ε ^ 2 with hX0def
  have hX0pos : 0 < X₀ := by rw [hX0def]; positivity
  set U : ℝ := max 8 (max (X₀ ^ (4 / (3 * ε))) (8 + 6 * Real.log 2 / ε)) with hUdef
  have hU8 : 8 ≤ U := le_max_left _ _
  have hUrpow : X₀ ^ (4 / (3 * ε)) ≤ U :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hUlog : 8 + 6 * Real.log 2 / ε ≤ U :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨1, Real.exp U, one_pos, ?_, ?_⟩
  · have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc (2 : ℝ) ≤ Real.exp 1 := h2
      _ ≤ Real.exp U := Real.exp_le_exp.mpr (by linarith)
  intro x y Q hx hy hyx hQ hQe
  have hu : U ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos U) hx
    rwa [Real.log_exp] at h
  have hu8 : 8 ≤ Real.log x := le_trans hU8 hu
  have hu0 : 0 < Real.log x := by linarith
  have hu1 : 1 ≤ Real.log x := by linarith
  have hu2 : 2 ≤ Real.log x := by linarith
  have hxpos0 : (0 : ℝ) < x := by
    have h1 : (0 : ℝ) < Real.exp U := Real.exp_pos U
    linarith
  have hx1 : (1 : ℝ) < x := by
    have h1 : (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
    rw [h1, ← Real.exp_log hxpos0]
    exact Real.exp_lt_exp.mpr hu0
  have hlogu2 : 2 ≤ Real.log (Real.log x) := by
    have h1 : Real.log 8 ≤ Real.log (Real.log x) :=
      Real.log_le_log (by norm_num) hu8
    have h2 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast
      ring
    have h3 : (2 : ℝ) ≤ 3 * Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith
  by_cases hε1 : ε ≤ 1
  · -- main case
    have h1me : 0 ≤ 1 - ε := by linarith
    have hy1 : (1 : ℝ) < y := by
      have h : (1 : ℝ) < x ^ ε := Real.one_lt_rpow hx1 hε
      linarith
    have hy0 : (0 : ℝ) < y := by linarith
    have hy13 : (1 : ℝ) < y ^ (1 / 3 : ℝ) := Real.one_lt_rpow hy1 (by norm_num)
    have hN1 : 1 ≤ ⌊y ^ (1 / 3 : ℝ)⌋₊ := by
      have h2 : (0 : ℕ) < ⌊y ^ (1 / 3 : ℝ)⌋₊ := Nat.floor_pos.mpr (le_of_lt hy13)
      omega
    by_cases hQ1 : 1 ≤ Q
    · -- the interval is where the work is
      have hQ0 : (0 : ℝ) < Q := by linarith
      set K : ℕ := ⌊Q⌋₊ + 1 with hKdef
      set L : ℝ := Real.log (K : ℝ) with hLdef
      have hK2 : 2 ≤ K := by
        have h1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ1)
        omega
      have hLpos : 0 < L := by
        rw [hLdef]
        apply Real.log_pos
        exact_mod_cast (by omega : 1 < K)
      -- `L ≤ 2 (log x)^{1-ε}`
      have hLb : L ≤ 2 * (Real.log x) ^ (1 - ε) := by
        have h1 : L = Real.log (K : ℝ) := hLdef
        rw [h1]
        have h2 : (K : ℝ) ≤ 2 * Q := by
          rw [hKdef]
          push_cast
          have hfl : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le (le_of_lt hQ0)
          linarith
        have h3 : Real.log (K : ℝ) ≤ Real.log (2 * Q) :=
          Real.log_le_log (by positivity) h2
        have h4 : Real.log (2 * Q) = Real.log 2 + Real.log Q :=
          Real.log_mul (by norm_num) (ne_of_gt hQ0)
        rw [h4] at h3
        have h5 : Real.log Q ≤ Real.log x ^ (1 - ε) := by
          have h := Real.log_le_log hQ0 hQe
          rwa [Real.log_exp] at h
        have h6 : (1 : ℝ) ≤ (Real.log x) ^ (1 - ε) := Real.one_le_rpow hu1 h1me
        have h7 : Real.log 2 ≤ (Real.log x) ^ (1 - ε) := by linarith [Real.log_two_lt_d9]
        linarith
      -- `(log x)^{1-ε} ≤ log x`
      have hu1me : (Real.log x) ^ (1 - ε) ≤ Real.log x := by
        calc (Real.log x) ^ (1 - ε) ≤ (Real.log x) ^ (1 : ℝ) :=
              (Real.rpow_le_rpow_left_iff (by linarith : (1 : ℝ) < Real.log x)).mpr
                (by linarith)
          _ = Real.log x := Real.rpow_one _
      have hLb2 : L ≤ 2 * Real.log x := by linarith
      -- `(log x)^{3ε/4} ≥ X₀` and hence `(log x)^{1-3ε/4}`
      have hthr : X₀ ≤ (Real.log x) ^ ((3 * ε) / 4) :=
        rpow_threshold hX0pos.le hε (hUrpow.trans hu)
      have hlogu : 0 ≤ Real.log (Real.log x) := by linarith
      -- the parameter `T`
      set T : ℝ := A * Real.log (Real.log x) + 2000 * (1 + Real.log (1 + L)) + 2 with hTdef
      have hone : 1 + Real.log (1 + L) ≤ Real.log (Real.log x) + 3 := by
        have h1 : 1 + L ≤ 4 * Real.log x := by linarith
        have h2 : Real.log (1 + L) ≤ Real.log (4 * Real.log x) :=
          Real.log_le_log (by linarith [hLpos]) h1
        have h3 : Real.log (4 * Real.log x) = Real.log 4 + Real.log (Real.log x) :=
          Real.log_mul (by norm_num) (ne_of_gt hu0)
        have h4 : Real.log 4 ≤ 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          push_cast
          linarith [Real.log_two_lt_d9]
        linarith
      have hTnn : 0 ≤ T := by
        have h1 : 0 ≤ Real.log (1 + L) := Real.log_nonneg (by linarith)
        have h2 : 0 ≤ A * Real.log (Real.log x) := mul_nonneg hA0 hlogu
        have h3 : (0 : ℝ) ≤ 2000 * (1 + Real.log (1 + L)) := by linarith
        simp only [hTdef]
        linarith
      have hTle : T ≤ 2 * (A + 6002) * Real.log (Real.log x) := by
        have h1 : 2000 * (1 + Real.log (1 + L))
            ≤ 2000 * (Real.log (Real.log x) + 3) := by linarith
        have h2 : (1 : ℝ) ≤ Real.log (Real.log x) := by linarith
        have h3 : (0 : ℝ) ≤ A := hA0
        simp only [hTdef]
        nlinarith [h1, h2, h3, hlogu]
      -- `(4 + 2L) T ≤ M`
      have hLsum : 4 + 2 * L ≤ 8 * (Real.log x) ^ (1 - ε) := by
        have h1 : (1 : ℝ) ≤ (Real.log x) ^ (1 - ε) := Real.one_le_rpow hu1 h1me
        linarith
      have hlogbound : Real.log (Real.log x) ≤ 4 * (Real.log x) ^ (ε / 4) / ε := by
        have h := log_le_rpow_div (u := Real.log x) (t := ε / 4) hu1 (by positivity)
        calc Real.log (Real.log x) ≤ (Real.log x) ^ (ε / 4) / (ε / 4) := h
          _ = 4 * (Real.log x) ^ (ε / 4) / ε := by field_simp
      have hsplit : (Real.log x) ^ (1 - ε) * (Real.log x) ^ (ε / 4)
          = (Real.log x) ^ (1 - 3 * ε / 4) := by
        rw [← Real.rpow_add hu0]
        congr 1
        ring
      have hkey : (Real.log x) ^ (1 - 3 * ε / 4) * (Real.log x) ^ ((3 * ε) / 4) = Real.log x := by
        rw [← Real.rpow_add hu0]
        rw [show 1 - 3 * ε / 4 + (3 * ε) / 4 = 1 by ring]
        rw [Real.rpow_one]
      have hX0le : 384 * (A + 6002) / ε ^ 2 ≤ X₀ := by
        rw [hX0def]
        have h1 : 384 * (A + 6002) ≤ 2000 * (A + 6002) := by nlinarith
        have h2 : (0 : ℝ) < ε ^ 2 := by positivity
        exact div_le_div_of_nonneg_right h1 h2.le
      -- the numerical endgame for `(4 + 2L) T ≤ M`
      have hTLM : (4 + 2 * L) * T ≤ (ε / 6) * Real.log x := by
        have hstep1 : (4 + 2 * L) * T
            ≤ (8 * (Real.log x) ^ (1 - ε)) * (2 * (A + 6002) * Real.log (Real.log x)) := by
          refine mul_le_mul hLsum hTle (by linarith [hTnn]) (by positivity)
        have hstep2 : (8 * (Real.log x) ^ (1 - ε)) * (2 * (A + 6002) * Real.log (Real.log x))
            ≤ (8 * (Real.log x) ^ (1 - ε)) *
                (2 * (A + 6002) * (4 * (Real.log x) ^ (ε / 4) / ε)) := by
          have h1 : (0 : ℝ) ≤ 8 * (Real.log x) ^ (1 - ε) := by positivity
          have h2 : 2 * (A + 6002) * Real.log (Real.log x)
              ≤ 2 * (A + 6002) * (4 * (Real.log x) ^ (ε / 4) / ε) := by
            have h3 : (0 : ℝ) ≤ 2 * (A + 6002) := by linarith
            exact mul_le_mul_of_nonneg_left hlogbound h3
          exact mul_le_mul_of_nonneg_left h2 h1
        have hstep3 : (8 * (Real.log x) ^ (1 - ε)) * (2 * (A + 6002) * (4 * (Real.log x) ^ (ε / 4) / ε))
            = (64 * (A + 6002) / ε) * ((Real.log x) ^ (1 - ε) * (Real.log x) ^ (ε / 4)) := by
          ring
        have hstep4 : (64 * (A + 6002) / ε) * ((Real.log x) ^ (1 - ε) * (Real.log x) ^ (ε / 4))
            = (64 * (A + 6002) / ε) * (Real.log x) ^ (1 - 3 * ε / 4) := by rw [hsplit]
        have hstep5 : (64 * (A + 6002) / ε) * (Real.log x) ^ (1 - 3 * ε / 4)
            ≤ (ε / 6) * Real.log x := by
          have hcoef : 64 * (A + 6002) / ε ≤ (ε / 6) * (Real.log x) ^ ((3 * ε) / 4) := by
            have h1 : 384 * (A + 6002) / ε ^ 2 ≤ (Real.log x) ^ ((3 * ε) / 4) :=
              le_trans hX0le hthr
            have h1' : 384 * (A + 6002) ≤ (Real.log x) ^ ((3 * ε) / 4) * ε ^ 2 := by
              have h2 : (0 : ℝ) < ε ^ 2 := by positivity
              have h3 := mul_le_mul_of_nonneg_right h1 h2.le
              rwa [div_mul_cancel₀ _ (ne_of_gt h2)] at h3
            rw [div_le_iff₀ hε]
            nlinarith [h1', hε]
          have h1 : (64 * (A + 6002) / ε) * (Real.log x) ^ (1 - 3 * ε / 4)
              ≤ ((ε / 6) * (Real.log x) ^ ((3 * ε) / 4)) *
                  (Real.log x) ^ (1 - 3 * ε / 4) :=
            mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hu0.le _)
          have h2 : ((ε / 6) * (Real.log x) ^ ((3 * ε) / 4)) *
                (Real.log x) ^ (1 - 3 * ε / 4)
              = (ε / 6) * Real.log x := by
            rw [mul_assoc, ← Real.rpow_add hu0,
              show (3 * ε) / 4 + (1 - 3 * ε / 4) = 1 by ring, Real.rpow_one]
          linarith [h1, h2]
        linarith [hstep1, hstep2, hstep3, hstep4, hstep5]
      -- `M` from `N`
      set N : ℕ := ⌊y ^ (1 / 3 : ℝ)⌋₊ with hNdef
      set Mr : ℝ := Real.log (N : ℝ) with hMrdef
      have hNpos : (0 : ℝ) < (N : ℝ) := by
        have : 0 < N := by omega
        exact_mod_cast this
      have hy13two : (2 : ℝ) ≤ y ^ (1 / 3 : ℝ) := by
        have hexp : Real.log 2 ≤ (ε / 3) * Real.log x := by
          have h1 : 6 * Real.log 2 / ε ≤ Real.log x := by linarith [hUlog, hu]
          rw [div_le_iff₀ hε] at h1
          nlinarith [h1, hε]
        have h2 : (2 : ℝ) ≤ x ^ (ε / 3) := by
          rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          calc Real.exp (Real.log 2) ≤ Real.exp ((ε / 3) * Real.log x) := Real.exp_le_exp.mpr hexp
            _ = x ^ (ε / 3) := by
                rw [Real.rpow_def_of_pos hxpos0]
                congr 1
                ring
        have h3 : (x ^ ε) ^ (1 / 3 : ℝ) ≤ y ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hy (by norm_num)
        have h4 : (x ^ ε) ^ (1 / 3 : ℝ) = x ^ (ε / 3) := by
          rw [← Real.rpow_mul hxpos0.le]
          congr 1
          ring
        linarith [h2, h3, h4]
      have hMb : (ε / 6) * Real.log x ≤ Mr := by
        rw [hMrdef, hNdef]
        have h1 : (1 : ℝ) ≤ y ^ (1 / 3 : ℝ) := le_of_lt hy13
        have h2 : y ^ (1 / 3 : ℝ) - 1 < (((⌊y ^ (1 / 3 : ℝ)⌋₊ : ℕ)) : ℝ) := by
          have h3 := Nat.lt_floor_add_one (y ^ (1 / 3 : ℝ))
          linarith
        have h4 : y ^ (1 / 3 : ℝ) / 2 ≤ (((⌊y ^ (1 / 3 : ℝ)⌋₊ : ℕ)) : ℝ) := by
          linarith [hy13two]
        have h5 : Real.log (y ^ (1 / 3 : ℝ) / 2)
            ≤ Real.log ((((⌊y ^ (1 / 3 : ℝ)⌋₊ : ℕ)) : ℝ)) :=
          Real.log_le_log (by positivity) h4
        have h6 : Real.log (y ^ (1 / 3 : ℝ) / 2)
            = Real.log (y ^ (1 / 3 : ℝ)) - Real.log 2 :=
          Real.log_div (by positivity) (by norm_num)
        rw [h6] at h5
        have h7 : Real.log (y ^ (1 / 3 : ℝ)) = (1 / 3 : ℝ) * Real.log y := Real.log_rpow hy0 _
        rw [h7] at h5
        have h8 : Real.log (x ^ ε) ≤ Real.log y := Real.log_le_log (by positivity) hy
        rw [Real.log_rpow (by linarith : (0 : ℝ) < x)] at h8
        have h9 : Real.log 2 ≤ (ε / 6) * Real.log x := by
          have h10 : 6 * Real.log 2 / ε ≤ Real.log x := by
            have h11 : 6 * Real.log 2 / ε ≤ 8 + 6 * Real.log 2 / ε := by linarith
            linarith [hUlog, hu]
          rw [div_le_iff₀ hε] at h10
          nlinarith [h10, hε]
        linarith
      have hTpos : 0 < T := by
        have h1 : (0 : ℝ) ≤ Real.log (1 + L) := Real.log_nonneg (by linarith)
        have h2 : (0 : ℝ) ≤ A * Real.log (Real.log x) := mul_nonneg hA0 hlogu
        simp only [hTdef]
        linarith
      have hMrpos : 0 < Mr :=
        lt_of_lt_of_le (by positivity : (0 : ℝ) < (ε / 6) * Real.log x) hMb
      -- the Rankin parameter
      set σ : ℝ := 2 * T / Mr with hσdef
      have hσpos : 0 < σ := by
        rw [hσdef]
        exact div_pos (by linarith [hTpos]) hMrpos
      have hσM : σ * Mr = 2 * T := by
        rw [hσdef]
        field_simp
      have hσhalf : σ ≤ 1 / 2 := by
        have h1 : 4 * T ≤ Mr := by
          have h2 : (4 + 2 * L) * T ≤ Mr := le_trans hTLM hMb
          have h3 : (0 : ℝ) ≤ T := hTnn
          have h4 : (0 : ℝ) ≤ L := hLpos.le
          nlinarith [h2, h3, h4]
        rw [hσdef, div_le_iff₀ hMrpos]
        nlinarith [h1, hTnn]
      have hσL : σ * L ≤ 1 := by
        have h1 : 2 * T * L ≤ Mr := by
          have h2 : (4 + 2 * L) * T ≤ Mr := le_trans hTLM hMb
          have h3 : (0 : ℝ) ≤ T := hTnn
          have h4 : (0 : ℝ) ≤ L := hLpos.le
          nlinarith [h2, h3, h4]
        rw [hσdef, div_mul_eq_mul_div, div_le_one hMrpos]
        linarith
      -- Rankin plus the Euler product
      have hrankin := smooth_sum_rankin N (smoothModulus Q) Q hσpos hN1
      have hEuler := sum_smooth_le_euler (smoothModulus Q) Q hQ1 hσpos hσhalf
      have hNK : (N : ℝ) ^ (-σ) = Real.exp (-(σ * Mr)) := by
        rw [Real.rpow_def_of_pos hNpos, hMrdef]
        congr 1
        ring
      have hexp_arg : -(σ * Mr) + 28 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))))
          ≤ -((A / 2) * Real.log (Real.log x) + 1) := by
        have h1 : Real.exp (σ * L) ≤ Real.exp 1 := Real.exp_le_exp.mpr hσL
        have h2 : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
        have h3 : 28 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))))
            ≤ 28 * (2.72 * (40 * (1 + Real.log (1 + L)))) := by
          have h4 : Real.exp (σ * L) * (40 * (1 + Real.log (1 + L)))
              ≤ 2.72 * (40 * (1 + Real.log (1 + L))) :=
            mul_le_mul_of_nonneg_right (le_trans h1 h2)
              (by have hLL : (0 : ℝ) ≤ Real.log (1 + L) := Real.log_nonneg (by linarith)
                  linarith)
          linarith
        rw [hσM, hTdef]
        nlinarith [h3, hlogu, hA0, hone, hlogu2]
      have htail : (∑ q ∈ Finset.Ioc N (smoothModulus Q),
          smoothWeight q Q * (localMajorant q / (q : ℝ)))
          ≤ Real.exp (-((A / 2) * Real.log (Real.log x) + 1)) := by
        refine hrankin.trans ?_
        have h1 : (N : ℝ) ^ (-σ) *
            (∑ q ∈ (Finset.range (smoothModulus Q + 1)).filter
              (fun q => q ∈ Nat.smoothNumbers (⌊Q⌋₊ + 1)),
              localMajorant q * (q : ℝ) ^ (σ - 1))
            ≤ (N : ℝ) ^ (-σ) *
              Real.exp (28 * (Real.exp (σ * L) * (40 * (1 + Real.log (1 + L))))) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hNpos.le _)
          have h2 : Real.log ((⌊Q⌋₊ : ℝ) + 1) = L := by
            rw [hLdef, hKdef]
            push_cast
            ring
          simpa [h2] using hEuler
        refine h1.trans ?_
        rw [hNK, ← Real.exp_add]
        exact Real.exp_le_exp.mpr hexp_arg
      have hfinal : Real.exp (-((A / 2) * Real.log (Real.log x) + 1))
          ≤ 1 / Real.log x ^ (A / 2) := by
        have h1 : Real.exp (-((A / 2) * Real.log (Real.log x) + 1))
            ≤ Real.exp (-((A / 2) * Real.log (Real.log x))) := by
          apply Real.exp_le_exp.mpr
          linarith
        have h2 : Real.exp (-((A / 2) * Real.log (Real.log x)))
            = (Real.log x) ^ (-(A / 2)) := by
          rw [Real.rpow_def_of_pos hu0]
          congr 1
          ring
        have h3 : (Real.log x) ^ (-(A / 2)) = 1 / Real.log x ^ (A / 2) := by
          rw [Real.rpow_neg hu0.le, one_div]
        linarith [h1, h2, h3]
      exact htail.trans hfinal
    · -- `Q < 1`: the smooth modulus is `1` and the interval is empty
      have hQlt : Q < 1 := by linarith
      have hfloor : ⌊Q⌋₊ = 0 := Nat.floor_eq_zero.mpr hQlt
      have hM : smoothModulus Q = 1 := by
        rw [smoothModulus, hfloor]
        simp
        exact Nat.not_prime_zero
      rw [hM]
      have hempty : Finset.Ioc ⌊y ^ (1 / 3 : ℝ)⌋₊ 1 = ∅ :=
        Finset.Ioc_eq_empty_iff.mpr (by omega)
      rw [hempty, Finset.sum_empty]
      have h1 : (0 : ℝ) < Real.log x ^ (A / 2) := Real.rpow_pos_of_pos hu0 _
      positivity
  · -- `1 < ε` contradicts `x^ε ≤ y ≤ x`
    exfalso
    push_neg at hε1
    have h2 : x < x ^ ε := by
      simpa using (Real.rpow_lt_rpow_left_iff hx1).mpr hε1
    linarith

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
          C / Real.log x ^ (A / 2) :=
  smooth_reciprocal_tail_proved A ε hA hε

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
