/-
Finite divisor expansion for display 50 on page 14.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp342e

namespace LeanLab.KumchevLiu2007.Task342f

open Task129 Task129b Task292a Task292c
open scoped BigOperators

/-- Page 14 before display 50. The finite prime product is squarefree and has the specified prime factors. -/
theorem smoothModulus_facts (Q : ℝ) :
    Squarefree (smoothModulus Q) ∧
      (smoothModulus Q).primeFactors = (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime := by
  classical
  let S := (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime
  have hs : ∀ p ∈ S, Nat.Prime p := fun p hp => (Finset.mem_filter.mp hp).2
  have hsq : ∀ t : Finset ℕ, (∀ p ∈ t, Nat.Prime p) → Squarefree (∏ p ∈ t, p) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert p t hp ih =>
      intro h
      have hpprime := h p (Finset.mem_insert_self p t)
      have ht : ∀ r ∈ t, Nat.Prime r := fun r hr => h r (Finset.mem_insert_of_mem hr)
      have hc : p.Coprime (∏ r ∈ t, r) := by
        apply Nat.Coprime.prod_right
        intro r hr
        exact (Nat.coprime_primes hpprime (ht r hr)).mpr (by rintro rfl; exact hp hr)
      rw [Finset.prod_insert hp, Nat.squarefree_mul hc]
      exact ⟨hpprime.squarefree, ih ht⟩
  exact ⟨hsq S hs, Nat.primeFactors_prod hs⟩

/-- Page 14 display 50. On positive moduli, the weighted coefficient is its divisor supported form. -/
theorem smooth_coefficient_dvd (n q : ℕ) (hq : 0 < q) (Q : ℝ) (hQ : 0 ≤ Q) :
    (smoothWeight q Q : ℂ) * U1534.A2 n q =
      if q ∣ smoothModulus Q then U1534.A2 n q else 0 := by
  classical
  by_cases hs : Squarefree q
  · have he : (∀ p : ℕ, p.Prime → p ∣ q → (p : ℝ) ≤ Q) ↔ q ∣ smoothModulus Q := by
      have hd : q ∣ smoothModulus Q ↔ q.primeFactors ⊆ (smoothModulus Q).primeFactors := by
        conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hs]
        exact Nat.prod_primeFactors_dvd_iff (smoothModulus_facts Q).1.ne_zero
      rw [hd, (smoothModulus_facts Q).2]
      constructor
      · intro h p hp
        rcases Nat.mem_primeFactors.mp hp with ⟨hpprime, hpq, hq0⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
          (Nat.lt_succ_iff.mpr ((Nat.le_floor_iff hQ).mpr (h p hpprime hpq))), hpprime⟩
      · intro h p hp hpq
        have hm := h ((Nat.mem_primeFactors_of_ne_zero hq.ne').mpr ⟨hp, hpq⟩)
        exact (Nat.le_floor_iff hQ).mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp
          (Finset.mem_filter.mp hm).1))
    unfold smoothWeight
    rw [he]
    split <;> simp_all
  · rw [Task129b.A2_eq_zero_of_not_squarefree n q hs]
    split <;> simp

/-- Page 14 display 50. The Euler product equals the full finite smooth coefficient sum. -/
theorem product2_smooth_sum (n : ℕ) (Q : ℝ) (hQ : 0 ≤ Q) :
    product2 n Q = ∑ q ∈ Finset.Icc 1 (smoothModulus Q),
      (smoothWeight q Q : ℂ) * U1534.A2 n q := by
  classical
  let f : ArithmeticFunction ℂ := ⟨U1534.A2 n, by simp [U1534.A2]⟩
  have hf : f.IsMultiplicative :=
    ⟨U1534.A2_one n, fun {a b} hab => A2_coprime_mul n a b hab⟩
  have hexp := hf.prodPrimeFactors_one_add_of_squarefree (smoothModulus_facts Q).1
  unfold product2
  rw [← (smoothModulus_facts Q).2]
  change (∏ p ∈ (smoothModulus Q).primeFactors, (1 + f p)) =
    ∑ q ∈ Finset.Icc 1 (smoothModulus Q), (smoothWeight q Q : ℂ) * U1534.A2 n q
  rw [hexp]
  have hdiv : (Finset.Icc 1 (smoothModulus Q)).filter (fun q => q ∣ smoothModulus Q) =
      (smoothModulus Q).divisors := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    have hM0 := (smoothModulus_facts Q).1.ne_zero
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

/-- Page 14 display 50. Exact finite smooth remainder identity supply. -/
theorem smooth_remainder_identity (n : ℕ) (P Q T : ℝ)
    (hP : 0 < P) (hPQ : P ≤ Q) (hQT : Q ≤ T) :
    (series2 n P - product2 n Q) - tail2 n P T Q =
      -(∑ q ∈ Finset.Ioc ⌊T⌋₊ (smoothModulus Q),
        (smoothWeight q Q : ℂ) * U1534.A2 n q) := by
  classical
  have hQ : 0 ≤ Q := (hP.trans_le hPQ).le
  let w : ℕ → ℂ := fun q => (smoothWeight q Q : ℂ) * U1534.A2 n q
  have hser : series2 n P = ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, w q := by
    unfold series2
    apply Finset.sum_congr rfl
    intro q hq
    have hqpos : 0 < q := (Finset.mem_Icc.mp hq).1
    have hs : smoothWeight q Q = 1 := by
      unfold smoothWeight
      rw [if_pos]
      intro p hp hpq
      have hpq' := Nat.le_of_dvd hqpos hpq
      exact ((Nat.cast_le.mpr (hpq'.trans (Finset.mem_Icc.mp hq).2)).trans
        (Nat.floor_le hP.le)).trans hPQ
    simp [w, hs]
  have htail : tail2 n P T Q = -∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊T⌋₊, w q := by
    simp only [tail2, w, neg_mul, Finset.sum_neg_distrib]
  have hPT : ⌊P⌋₊ ≤ ⌊T⌋₊ := Nat.floor_mono (hPQ.trans hQT)
  have hsplit : (∑ q ∈ Finset.Icc 1 ⌊P⌋₊, w q) +
      (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊T⌋₊, w q) = ∑ q ∈ Finset.Icc 1 ⌊T⌋₊, w q := by
    have he := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 ⌊T⌋₊)
      (fun q => q ≤ ⌊P⌋₊) w
    convert he using 2 <;> congr 1 <;> ext q <;>
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] <;> omega
  have hsum : (∑ q ∈ Finset.Icc 1 ⌊T⌋₊, w q) +
      (∑ q ∈ Finset.Ioc ⌊T⌋₊ (smoothModulus Q), w q) = product2 n Q := by
    rw [product2_smooth_sum n Q hQ]
    change _ = ∑ q ∈ Finset.Icc 1 (smoothModulus Q), w q
    by_cases hTM : ⌊T⌋₊ ≤ smoothModulus Q
    · have he := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (smoothModulus Q))
        (fun q => q ≤ ⌊T⌋₊) w
      convert he using 2 <;> congr 1 <;> ext q <;>
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] <;> omega
    · have hMT : smoothModulus Q ≤ ⌊T⌋₊ := by omega
      rw [Finset.Ioc_eq_empty_of_le hMT, Finset.sum_empty, add_zero]
      symm
      apply Finset.sum_subset
      · intro q hq
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hq).1, (Finset.mem_Icc.mp hq).2.trans hMT⟩
      · intro q hq hnot
        have hqpos := (Finset.mem_Icc.mp hq).1
        have hMq : smoothModulus Q < q := by
          simp only [Finset.mem_Icc, not_and, not_le] at hnot
          exact hnot hqpos
        have hnd : ¬ q ∣ smoothModulus Q := by
          intro hd
          exact (Nat.not_le_of_gt hMq) (Nat.le_of_dvd
            (Nat.pos_of_ne_zero (smoothModulus_facts Q).1.ne_zero) hd)
        exact (smooth_coefficient_dvd n q hqpos Q hQ).trans (if_neg hnd)
  rw [hser, htail]
  change (_ - product2 n Q) - (-_) = -_
  rw [sub_neg_eq_add]
  linear_combination hsplit + hsum

end LeanLab.KumchevLiu2007.Task342f
