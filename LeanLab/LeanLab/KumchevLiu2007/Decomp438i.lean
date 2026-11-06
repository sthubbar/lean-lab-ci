/-
Finite smooth support for the three-square singular product.
Source page 14 display 50. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp438d
import LeanLab.KumchevLiu2007.Decomp342f

namespace LeanLab.KumchevLiu2007.Task438i

open Real Complex Task129b Task129c Task292c Task403c
open scoped BigOperators

/-- Page 14 display 50. A nonzero smooth coefficient divides the full support
four times the squarefree prime product. Powers at 2 through 8 are retained. -/
theorem smooth_coefficient_support (n q : ℕ) (hq : 0 < q) (Q : ℝ)
    (hs : ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q) (hc : A3 n q ≠ 0) :
    q ∣ 4 * smoothModulus Q := by
  classical
  have hall : ∀ q : ℕ, 0 < q →
      (∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q) → A3 n q ≠ 0 →
        q ∣ 4 * smoothModulus Q := by
    intro q
    induction q using Nat.recOnPrimeCoprime with
    | zero => intro h; omega
    | prime_pow p k hp =>
      intro hq hs hc
      by_cases hk0 : k = 0
      · subst k
        simp
      have hk : 0 < k := Nat.pos_of_ne_zero hk0
      have hpQ : (p : ℝ) ≤ Q := hs p hp (dvd_pow_self _ hk0)
      have hpM : p ∣ smoothModulus Q := by
        apply Nat.dvd_of_mem_primeFactors
        rw [(Task342f.smoothModulus_facts Q).2]
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
          (Nat.lt_succ_iff.mpr (Nat.le_floor hpQ)), hp⟩
      by_cases htwo : p = 2
      · subst p
        have hk3 : k ≤ 3 := by
          by_contra he
          exact hc (Task438f.A3_prime_power_vanish n 2 k hp (Or.inr ⟨rfl, by omega⟩))
        apply (pow_dvd_pow 2 hk3).trans
        obtain ⟨t, ht⟩ := hpM
        refine ⟨t, ?_⟩
        rw [ht]
        ring
      · have hk1 : k = 1 := by
          by_contra he
          exact hc (Task438f.A3_prime_power_vanish n p k hp (Or.inl ⟨htwo, by omega⟩))
        simpa [hk1] using hpM.trans (dvd_mul_left (smoothModulus Q) 4)
    | coprime a b ha hb hab iha ihb =>
      intro hq hs hc
      have hca : A3 n a ≠ 0 := by
        intro hz
        apply hc
        rw [Task438e.A3_coprime_mul n a b hab, hz, zero_mul]
      have hcb : A3 n b ≠ 0 := by
        intro hz
        apply hc
        rw [Task438e.A3_coprime_mul n a b hab, hz, mul_zero]
      exact hab.mul_dvd_of_dvd_of_dvd
        (iha (by omega) (fun p hp hd => hs p hp (hd.trans (dvd_mul_right a b))) hca)
        (ihb (by omega) (fun p hp hd => hs p hp (hd.trans (dvd_mul_left b a))) hcb)
  exact hall q hq hs hc

/-- Page 14 display 50. When Q is at least 2, the smooth weighted coefficient
is exactly the divisor supported coefficient of four times the prime product. -/
theorem smooth_coefficient_dvd (n q : ℕ) (hq : 0 < q) (Q : ℝ) (hQ : 2 ≤ Q) :
    (smoothWeight q Q : ℂ) * A3 n q =
      if q ∣ 4 * smoothModulus Q then A3 n q else 0 := by
  classical
  have hM0 : smoothModulus Q ≠ 0 := (Task342f.smoothModulus_facts Q).1.ne_zero
  have hprime (p : ℕ) (hp : p.Prime) (hd : p ∣ 4 * smoothModulus Q) : (p : ℝ) ≤ Q := by
    rcases hp.dvd_mul.mp hd with h4 | hM
    · have h2 : p = 2 := by
        have hd2 : p ∣ 2 ^ 2 := by simpa using h4
        exact (Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hd2) |>.resolve_left hp.ne_one
      subst p
      exact hQ
    · have hm := (Nat.mem_primeFactors.mpr ⟨hp, hM, hM0⟩)
      rw [(Task342f.smoothModulus_facts Q).2] at hm
      have hle : p ≤ ⌊Q⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hm).1)
      exact (Nat.cast_le.mpr hle).trans (Nat.floor_le (by linarith))
  by_cases hd : q ∣ 4 * smoothModulus Q
  · rw [ite_eq_left hd]
    have hs : smoothWeight q Q = 1 := by
      unfold smoothWeight
      exact ite_eq_left (fun p hp hpq => hprime p hp (hpq.trans hd))
    simp [hs]
  · rw [ite_eq_right hd]
    by_cases hs : ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q
    · have hz : A3 n q = 0 := by
        by_contra hc
        exact hd (smooth_coefficient_support n q hq Q hs hc)
      simp [hz]
    · simp [smoothWeight, hs]

/-- Page 14 display 50. The three-square Euler product is the divisor sum
at four times the prime product when Q is at least 2. -/
theorem product3_divisor_sum (n : ℕ) (Q : ℝ) (hQ : 2 ≤ Q) :
    product3 n Q = ∑ q ∈ (4 * smoothModulus Q).divisors, A3 n q := by
  classical
  let S := (Finset.range (⌊Q⌋₊ + 1)).filter (fun p => p.Prime ∧ 2 < p)
  let O := ∏ p ∈ S, p
  have hS : ∀ p ∈ S, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2.1
  have hO0 : O ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hS p hp).ne_zero)
  have hpf : O.primeFactors = S := Nat.primeFactors_prod hS
  have hsq : Squarefree O := by
    have hs : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime) → Squarefree (∏ p ∈ T, p) := by
      intro T
      induction T using Finset.induction_on with
      | empty => simp
      | insert p T hp ih =>
        intro h
        have hprime := h p (Finset.mem_insert_self p T)
        have ht : ∀ r ∈ T, r.Prime := fun r hr => h r (Finset.mem_insert_of_mem hr)
        have hc : p.Coprime (∏ r ∈ T, r) := by
          apply Nat.Coprime.prod_right
          intro r hr
          exact (Nat.coprime_primes hprime (ht r hr)).mpr (by rintro rfl; exact hp hr)
        rw [Finset.prod_insert hp, Nat.squarefree_mul hc]
        exact ⟨hprime.squarefree, ih ht⟩
    exact hs S hS
  have h2not : ¬2 ∣ O := by
    intro hd
    have hm := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hd, hO0⟩
    rw [hpf] at hm
    have hgt := (Finset.mem_filter.mp hm).2.2
    omega
  have hcop : Nat.Coprime 8 O := by
    have hc : Nat.Coprime 2 O := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2not
    exact hc.pow_left 3
  have h2S : 2 ∉ S := by simp [S]
  have hprimes : (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime = insert 2 S := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, S]
    constructor
    · rintro ⟨hpq, hprime⟩
      by_cases hp2 : p = 2
      · exact Or.inl hp2
      · exact Or.inr ⟨hpq, hprime, by have := hprime.two_le; omega⟩
    · rintro (rfl | ⟨hpq, hp, hgt⟩)
      · exact ⟨Nat.lt_succ_iff.mpr (Nat.le_floor hQ), Nat.prime_two⟩
      · exact ⟨hpq, hp⟩
  have hM : 4 * smoothModulus Q = 8 * O := by
    rw [smoothModulus, hprimes, Finset.prod_insert h2S]
    dsimp [O]
    ring
  let f : ArithmeticFunction ℂ := ⟨A3 n, by simp [A3]⟩
  have hf : f.IsMultiplicative :=
    ⟨Task438d.A3_one n, fun {a b} hab => Task438e.A3_coprime_mul n a b hab⟩
  have hg := hf.mul (ArithmeticFunction.isMultiplicative_zeta.natCast (R := ℂ))
  have hmul : (∑ q ∈ (8 * O).divisors, A3 n q) =
      (∑ q ∈ Nat.divisors 8, A3 n q) * (∑ q ∈ O.divisors, A3 n q) := by
    have hm := hg.map_mul_of_coprime hcop
    simp only [ArithmeticFunction.coe_mul_zeta_apply] at hm
    exact hm
  have h8 : (∑ q ∈ Nat.divisors 8, A3 n q) = 1 + A3 n 2 + A3 n 4 + A3 n 8 := by
    have hd : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hd]
    simp [Task438d.A3_one]
    ring
  have hO : (∑ q ∈ O.divisors, A3 n q) = ∏ p ∈ S, (1 + A3 n p) := by
    simpa [hpf, f] using (hf.prodPrimeFactors_one_add_of_squarefree hsq).symm
  rw [hM, hmul, h8, hO]
  simp only [product3, ite_eq_left hQ, S]

/-- Page 14 display 50. The Euler product is the full finite smooth
coefficient sum with the even prime powers through 8. -/
theorem product3_smooth_sum (n : ℕ) (Q : ℝ) (hQ : 2 ≤ Q) :
    product3 n Q = ∑ q ∈ Finset.Icc 1 (4 * smoothModulus Q),
      (smoothWeight q Q : ℂ) * A3 n q := by
  classical
  rw [product3_divisor_sum n Q hQ]
  have hM0 : 4 * smoothModulus Q ≠ 0 :=
    Nat.mul_ne_zero (by norm_num) (Task342f.smoothModulus_facts Q).1.ne_zero
  have hdiv : (Finset.Icc 1 (4 * smoothModulus Q)).filter
      (fun q => q ∣ 4 * smoothModulus Q) = (4 * smoothModulus Q).divisors := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨hq, hd⟩
      exact ⟨hd, hM0⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hM0),
        Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hd⟩, hd⟩
  rw [← hdiv, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  exact (smooth_coefficient_dvd n q (Finset.mem_Icc.mp hq).1 Q hQ).symm

/-- Page 14 display 50. The finite smooth expansion also covers positive Q
below 2. In that case the only surviving modulus is 1. -/
theorem product3_smooth_sum_all (n : ℕ) (Q : ℝ) (hQ : 0 < Q) :
    product3 n Q = ∑ q ∈ Finset.Icc 1 (4 * smoothModulus Q),
      (smoothWeight q Q : ℂ) * A3 n q := by
  classical
  by_cases hQ2 : 2 ≤ Q
  · exact product3_smooth_sum n Q hQ2
  have hQlt : Q < 2 := lt_of_not_ge hQ2
  have hemp : (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hprange, hp⟩
    have hle : (p : ℝ) ≤ Q := (Nat.cast_le.mpr
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hprange))).trans (Nat.floor_le hQ.le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have hemp' : (Finset.range (⌊Q⌋₊ + 1)).filter (fun p => p.Prime ∧ 2 < p) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hm : p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.1⟩
    rw [hemp] at hm
    exact Finset.notMem_empty _ hm
  have hM : smoothModulus Q = 1 := by simp [smoothModulus, hemp]
  have hw (q : ℕ) (hq : 0 < q) (hne : q ≠ 1) : smoothWeight q Q = 0 := by
    unfold smoothWeight
    apply if_neg
    intro hs
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hle := hs p hp hpd
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  simp only [product3, ite_eq_right hQ2, hemp', Finset.prod_empty, mul_one, hM]
  symm
  trans (smoothWeight 1 Q : ℂ) * A3 n 1
  · apply Finset.sum_eq_single 1
    · intro q hq hne
      rw [hw q (Finset.mem_Icc.mp hq).1 hne]
      simp
    · intro hnot
      exact False.elim (hnot (by norm_num))
  · simp [smoothWeight, Task438d.A3_one, Nat.not_prime_one]

/-- Page 14 display 50. Exact Task438a finite remainder supply, including
positive cutoffs below 2 and the full even prime support through 8. -/
theorem smooth_remainder_identity (n : ℕ) (P Q T : ℝ)
    (hP : 0 < P) (hPQ : P ≤ Q) (hQT : Q ≤ T) :
    (series3 n P - product3 n Q) - tail3 n P T Q =
      -(∑ q ∈ Finset.Ioc ⌊T⌋₊ (4 * smoothModulus Q),
        (smoothWeight q Q : ℂ) * A3 n q) := by
  classical
  have hQ : 0 < Q := hP.trans_le hPQ
  let w : ℕ → ℂ := fun q => (smoothWeight q Q : ℂ) * A3 n q
  have hser : series3 n P = ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, w q := by
    unfold series3
    apply Finset.sum_congr rfl
    intro q hq
    have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
    have hs : smoothWeight q Q = 1 := by
      unfold smoothWeight
      apply if_pos
      intro p hp hpq
      have hpq' := Nat.le_of_dvd hqpos hpq
      exact ((Nat.cast_le.mpr (hpq'.trans (Finset.mem_Icc.mp hq).2)).trans
        (Nat.floor_le hP.le)).trans hPQ
    simp [w, hs]
  have htail : tail3 n P T Q = -∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊T⌋₊, w q := by
    simp only [tail3, w, neg_mul, Finset.sum_neg_distrib]
  have hPT : ⌊P⌋₊ ≤ ⌊T⌋₊ := Nat.floor_mono (hPQ.trans hQT)
  have hsplit : (∑ q ∈ Finset.Icc 1 ⌊P⌋₊, w q) +
      (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊T⌋₊, w q) = ∑ q ∈ Finset.Icc 1 ⌊T⌋₊, w q := by
    have he := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊T⌋₊)
      (fun q => q ≤ ⌊P⌋₊) w
    convert he using 2 <;> congr 1 <;> ext q <;>
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] <;> omega
  have hsum : (∑ q ∈ Finset.Icc 1 ⌊T⌋₊, w q) +
      (∑ q ∈ Finset.Ioc ⌊T⌋₊ (4 * smoothModulus Q), w q) = product3 n Q := by
    rw [product3_smooth_sum_all n Q hQ]
    change _ = ∑ q ∈ Finset.Icc 1 (4 * smoothModulus Q), w q
    by_cases hTM : ⌊T⌋₊ ≤ 4 * smoothModulus Q
    · have he := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (4 * smoothModulus Q))
        (fun q => q ≤ ⌊T⌋₊) w
      convert he using 2 <;> congr 1 <;> ext q <;>
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] <;> omega
    · have hMT : 4 * smoothModulus Q ≤ ⌊T⌋₊ := by omega
      rw [Finset.Ioc_eq_empty_of_le hMT, Finset.sum_empty, add_zero]
      symm
      apply Finset.sum_subset
      · intro q hq
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hq).1, (Finset.mem_Icc.mp hq).2.trans hMT⟩
      · intro q hq hnot
        have hqpos := (Finset.mem_Icc.mp hq).1
        have hMq : 4 * smoothModulus Q < q := by
          simp only [Finset.mem_Icc, not_and, not_le] at hnot
          exact hnot hqpos
        dsimp [w]
        by_cases hs : ∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q
        · have hz : A3 n q = 0 := by
            by_contra hc
            have hd := smooth_coefficient_support n q hqpos Q hs hc
            have hM0 : 0 < 4 * smoothModulus Q := Nat.mul_pos (by norm_num)
              (Nat.pos_of_ne_zero (Task342f.smoothModulus_facts Q).1.ne_zero)
            exact (Nat.not_le_of_gt hMq) (Nat.le_of_dvd hM0 hd)
          simp [hz]
        · simp [smoothWeight, hs]
  rw [hser, htail]
  linear_combination hsplit + hsum

#print axioms smooth_coefficient_support
#print axioms smooth_coefficient_dvd
#print axioms product3_divisor_sum
#print axioms product3_smooth_sum
#print axioms product3_smooth_sum_all
#print axioms smooth_remainder_identity

end LeanLab.KumchevLiu2007.Task438i
