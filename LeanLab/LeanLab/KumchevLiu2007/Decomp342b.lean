/-
The numerical double sum on page 15, third display.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp342a

namespace LeanLab.KumchevLiu2007.Task342b

open Real Complex Task292a
open scoped BigOperators

/-- Page 14 display 47. Each sufficiently large prime factor is absorbed by any positive power. -/
theorem local_factor_power (ε : ℝ) (hε : 0 < ε) (p : ℕ)
    (hp : 1 ≤ p) (hlarge : (7 : ℝ) ^ ε⁻¹ ≤ (p : ℝ)) :
    1 + 6 / (p : ℝ) ≤ (p : ℝ) ^ ε := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hsmall : 1 + 6 / (p : ℝ) ≤ 7 := by
    have : 6 / (p : ℝ) ≤ 6 := (div_le_iff₀ (by linarith)).mpr (by linarith)
    linarith
  have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 7 ^ ε⁻¹) hlarge hε.le
  rw [Real.rpow_inv_rpow (by norm_num) hε.ne'] at hpow
  exact hsmall.trans hpow

/-- Page 14 display 47 and page 15 third display. The local prime product has arbitrary positive power growth. -/
theorem localMajorant_power_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℕ, 0 < q → localMajorant q ≤ K * (q : ℝ) ^ ε := by
  classical
  let N : ℕ := ⌈(7 : ℝ) ^ ε⁻¹⌉₊
  refine ⟨(7 : ℝ) ^ N, by positivity, ?_⟩
  intro q hq
  let S := q.primeFactors.filter (fun p => p < N)
  let T := q.primeFactors.filter (fun p => ¬ p < N)
  have hpos (p : ℕ) (hp : p ∈ q.primeFactors) : (1 : ℝ) ≤ p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
  have hS : (∏ p ∈ S, (1 + 6 / (p : ℝ))) ≤ (7 : ℝ) ^ N := by
    calc
      _ ≤ ∏ _p ∈ S, (7 : ℝ) := by
        apply Finset.prod_le_prod₀ (fun p hp => by positivity)
        intro p hp
        have hpR := hpos p (Finset.mem_filter.mp hp).1
        have : 6 / (p : ℝ) ≤ 6 := (div_le_iff₀ (by linarith)).mpr (by linarith)
        linarith
      _ = (7 : ℝ) ^ S.card := by simp
      _ ≤ (7 : ℝ) ^ N := by
        apply pow_le_pow_right₀ (by norm_num)
        have hsub : S ⊆ Finset.range N := by
          intro p hp
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
        simpa using Finset.card_le_card hsub
  have hT : (∏ p ∈ T, (1 + 6 / (p : ℝ))) ≤ (q : ℝ) ^ ε := by
    calc
      _ ≤ ∏ p ∈ T, (p : ℝ) ^ ε := by
        apply Finset.prod_le_prod₀ (fun p hp => by positivity)
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hp, hpN⟩
        apply local_factor_power ε hε p (by exact_mod_cast hpos p hp)
        exact (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_of_not_gt hpN))
      _ = (∏ p ∈ T, (p : ℝ)) ^ ε :=
        Real.finsetProd_rpow T (fun p => (p : ℝ)) (fun p hp => by positivity) ε
      _ ≤ (q : ℝ) ^ ε := by
        apply Real.rpow_le_rpow (by positivity) _ hε.le
        have hprod : ∏ p ∈ T, p ≤ q := by
          apply Nat.le_of_dvd hq
          exact (Finset.prod_dvd_prod_of_subset T q.primeFactors (fun p => p)
            (Finset.filter_subset _ _)).trans
            (Nat.prod_primeFactors_dvd q)
        have hc : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hprod
        simpa only [Nat.cast_prod] using hc
  rw [localMajorant, ← Finset.prod_filter_mul_prod_filter_not q.primeFactors (fun p => p < N)]
  exact mul_le_mul hS hT (by positivity) (by positivity)

/-- Page 15 third display. A bound for the sum of the local majorants up to a real cutoff. -/
theorem majorant_sum_bound (K ε : ℝ) (hK : 0 < K) (hε : 0 ≤ ε)
    (hb : ∀ q : ℕ, 0 < q → localMajorant q ≤ K * (q : ℝ) ^ ε)
    (P Y : ℝ) (hY : 1 ≤ Y) :
    (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊Y⌋₊, localMajorant q) ≤ K * Y ^ (1 + ε) := by
  have hpoint (q : ℕ) (hq : q ∈ Finset.Ioc ⌊P⌋₊ ⌊Y⌋₊) :
      localMajorant q ≤ K * Y ^ ε := by
    have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
    have hqY : (q : ℝ) ≤ Y :=
      (Nat.cast_le.mpr (Finset.mem_Ioc.mp hq).2).trans (Nat.floor_le (by linarith))
    exact (hb q hqn).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hqY hε) hK.le)
  calc
    _ ≤ ∑ _q ∈ Finset.Ioc ⌊P⌋₊ ⌊Y⌋₊, K * Y ^ ε :=
      Finset.sum_le_sum hpoint
    _ = ((Finset.Ioc ⌊P⌋₊ ⌊Y⌋₊).card : ℝ) * (K * Y ^ ε) := by simp
    _ ≤ Y * (K * Y ^ ε) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hcard : (Finset.Ioc ⌊P⌋₊ ⌊Y⌋₊).card ≤ ⌊Y⌋₊ := by
        simp only [Nat.card_Ioc]
        omega
      exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le (by linarith))
    _ = K * Y ^ (1 + ε) := by rw [Real.rpow_add (by linarith), Real.rpow_one]; ring

/-- Page 15 third display. Exact numerical double sum supply for Task292b. -/
theorem majorant_pair_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ y P : ℝ, 1 ≤ y → 0 < P →
      (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊,
        ∑ r ∈ (Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊).erase q,
          localMajorant q * localMajorant r) ≤ C * y ^ (3 / 4 : ℝ) := by
  classical
  obtain ⟨K, hK, hb⟩ := localMajorant_power_bound (1 / 8 : ℝ) (by norm_num)
  refine ⟨K ^ 2, by positivity, ?_⟩
  intro y P hy hP
  let S := Finset.Ioc ⌊P⌋₊ ⌊y ^ (1 / 3 : ℝ)⌋₊
  have hnonneg (q : ℕ) : 0 ≤ localMajorant q := by
    unfold localMajorant
    exact Finset.prod_nonneg (fun p hp => by positivity)
  have hsum0 : 0 ≤ ∑ q ∈ S, localMajorant q := Finset.sum_nonneg (fun q hq => hnonneg q)
  have hY : 1 ≤ y ^ (1 / 3 : ℝ) := Real.one_le_rpow hy (by norm_num)
  have hsum := majorant_sum_bound K (1 / 8 : ℝ) hK (by norm_num) hb P _ hY
  change (∑ q ∈ S, ∑ r ∈ S.erase q, _) ≤ _
  calc
    _ ≤ ∑ q ∈ S, ∑ r ∈ S, localMajorant q * localMajorant r := by
      apply Finset.sum_le_sum
      intro q hq
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset q S)
        (fun r hr hnot => mul_nonneg (hnonneg q) (hnonneg r))
    _ = (∑ q ∈ S, localMajorant q) ^ 2 := by rw [sq, Finset.sum_mul_sum]
    _ ≤ (K * (y ^ (1 / 3 : ℝ)) ^ (1 + (1 / 8 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ hsum0 hsum 2
    _ = K ^ 2 * y ^ (3 / 4 : ℝ) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by linarith : 0 ≤ y)]
      norm_num

end LeanLab.KumchevLiu2007.Task342b
