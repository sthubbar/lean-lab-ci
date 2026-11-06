/-
Numerical diagonal supply from the proved lab Mertens upper bound.
Source page 15 first display. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp438j
import LeanLab.PNTSieve.MertensUpper

namespace LeanLab.KumchevLiu2007.Task438k

open Real Complex Task129b Task292a
open scoped BigOperators

/-- Page 15 first display. The sixth power of the local product is bounded
by a constant times log x uniformly for positive q at most x to one third. -/
theorem localMajorant_sixth_log_bound :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ (x : ℝ) (q : ℕ),
      x0 ≤ x → 0 < q → (q : ℝ) ≤ x ^ (1 / 3 : ℝ) →
        localMajorant q ^ 6 ≤ C * Real.log x := by
  classical
  refine ⟨Real.exp 504 * ((Nat.factorial 36 : ℕ) : ℝ) * 2,
    max 2 (Real.exp 2), by positivity, le_max_left _ _, ?_⟩
  intro x q hx hq hqx
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  let L := Real.log x
  have hL2 : 2 ≤ L := by
    apply (Real.le_log_iff_exp_le hx0).mpr
    exact (le_max_right _ _).trans hx
  let N : ℕ := ⌈L⌉₊
  have hLN : L ≤ (N : ℝ) := Nat.le_ceil L
  have hN2 : 2 ≤ N := by exact_mod_cast (show (2 : ℝ) ≤ N from hL2.trans hLN)
  have hNupper : (N : ℝ) ≤ 2 * L := by
    have hceil := Nat.ceil_lt_add_one (by linarith : 0 ≤ L)
    dsimp [N]
    linarith
  have hlogq : Real.log (q : ℝ) ≤ L / 3 := by
    have h := Real.log_le_log (by positivity : 0 < (q : ℝ)) hqx
    rw [Real.log_rpow hx0] at h
    dsimp [L]
    linarith
  have hcard : (q.primeFactors.card : ℝ) ≤ 2 * L := by
    have hprod : (2 : ℕ) ^ q.primeFactors.card ≤ q := by
      calc
        _ = ∏ _p ∈ q.primeFactors, (2 : ℕ) := by simp
        _ ≤ ∏ p ∈ q.primeFactors, p := Finset.prod_le_prod
          (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
        _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
    have hcast : (2 : ℝ) ^ q.primeFactors.card ≤ (q : ℝ) := by exact_mod_cast hprod
    have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ q.primeFactors.card) hcast
    rw [Real.log_pow] at hl
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith
  let S := q.primeFactors.filter (fun p => p ≤ N)
  let T := q.primeFactors.filter (fun p => ¬ p ≤ N)
  have hsmall : (∑ p ∈ S, 1 / (p : ℝ)) ≤ Real.log (Real.log (N : ℝ)) + 12 := by
    have hsub : S ⊆ (Finset.Icc 1 N).filter Nat.Prime := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpq, hpN⟩
      have hprime := Nat.prime_of_mem_primeFactors hpq
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hprime.one_le, hpN⟩, hprime⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp hnot => by positivity)).trans
      (LeanLab.PNTSieve.Mertens.sum_inv_primes_le N hN2)
  have hlarge : (∑ p ∈ T, 1 / (p : ℝ)) ≤ 2 := by
    calc
      _ ≤ ∑ _p ∈ T, 1 / L := by
        apply Finset.sum_le_sum
        intro p hp
        have hpN : N < p := Nat.lt_of_not_ge (Finset.mem_filter.mp hp).2
        exact one_div_le_one_div_of_le (by linarith) (hLN.trans (by exact_mod_cast hpN.le))
      _ = (T.card : ℝ) / L := by simp [div_eq_mul_inv]
      _ ≤ (q.primeFactors.card : ℝ) / L := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun p => ¬ p ≤ N) q.primeFactors)
      _ ≤ 2 := (div_le_iff₀ (by linarith : 0 < L)).mpr (by linarith)
  have hsum : (∑ p ∈ q.primeFactors, 1 / (p : ℝ)) ≤ Real.log (Real.log (N : ℝ)) + 14 := by
    have he := Finset.sum_filter_add_sum_filter_not q.primeFactors (fun p => p ≤ N)
      (fun p => 1 / (p : ℝ))
    change (∑ p ∈ S, 1 / (p : ℝ)) + (∑ p ∈ T, 1 / (p : ℝ)) = _ at he
    linarith
  have hMpos : 0 < localMajorant q := by
    unfold localMajorant
    exact Finset.prod_pos (fun p hp => by positivity)
  have hlogM : Real.log (localMajorant q) ≤ 6 * (Real.log (Real.log (N : ℝ)) + 14) := by
    rw [localMajorant, Real.log_prod (fun p hp => by positivity)]
    have ht : ∀ p ∈ q.primeFactors, Real.log (1 + 6 / (p : ℝ)) ≤ 6 * (1 / (p : ℝ)) := by
      intro p hp
      have hb := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 6 / (p : ℝ))
      convert hb using 1 <;> ring
    exact (Finset.sum_le_sum ht).trans (by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hsum (by norm_num))
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hM : localMajorant q ^ 6 ≤ Real.exp 504 * (Real.log (N : ℝ)) ^ 36 := by
    have hl : Real.log (localMajorant q ^ 6) ≤ 36 * Real.log (Real.log (N : ℝ)) + 504 := by
      rw [Real.log_pow]
      have hh := mul_le_mul_of_nonneg_left hlogM (by norm_num : (0 : ℝ) ≤ 6)
      convert hh using 1 <;> ring
    have hh := (Real.log_le_iff_le_exp (by positivity : 0 < localMajorant q ^ 6)).mp hl
    have he : Real.exp (36 * Real.log (Real.log (N : ℝ)) + 504) =
        Real.exp 504 * (Real.log (N : ℝ)) ^ 36 := by
      rw [Real.exp_add, show (36 : ℝ) = ((36 : ℕ) : ℝ) by norm_num,
        Real.exp_nat_mul, Real.exp_log hlogN]
      ring
    exact hh.trans_eq he
  have hfac : (Real.log (N : ℝ)) ^ 36 ≤ ((Nat.factorial 36 : ℕ) : ℝ) * (N : ℝ) := by
    have h := Real.pow_div_factorial_le_exp (Real.log (N : ℝ)) hlogN.le 36
    rw [Real.exp_log (by exact_mod_cast (show 0 < N by omega)),
      div_le_iff₀ (by positivity : 0 < ((Nat.factorial 36 : ℕ) : ℝ))] at h
    nlinarith
  calc
    _ ≤ Real.exp 504 * (((Nat.factorial 36 : ℕ) : ℝ) * (N : ℝ)) :=
      hM.trans (mul_le_mul_of_nonneg_left hfac (by positivity))
    _ ≤ Real.exp 504 * (((Nat.factorial 36 : ℕ) : ℝ) * (2 * L)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNupper (by positivity)) (by positivity)
    _ = _ := by dsimp [L]; ring

/-- Page 15 first display. Exact Task438b numerical reciprocal square tail
supply from the sixth power product bound and the proved real cutoff tail. -/
theorem majorant_square_tail :
    ∃ K x0 : ℝ, 0 < K ∧ 2 ≤ x0 ∧ ∀ x P : ℝ,
      x0 ≤ x → 0 < P →
      (∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊x ^ (1 / 3 : ℝ)⌋₊,
        localMajorant q ^ 6 / (q : ℝ) ^ 2) ≤
          K * (Real.log x / P) := by
  obtain ⟨C, x0, hC, hx0, hb⟩ := localMajorant_sixth_log_bound
  refine ⟨2 * C, x0, by positivity, hx0, ?_⟩
  intro x P hx hP
  have hx2 : 2 ≤ x := hx0.trans hx
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  calc
    _ ≤ ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊x ^ (1 / 3 : ℝ)⌋₊,
        C * Real.log x / (q : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      have hqn : 0 < q := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
      have hqx : (q : ℝ) ≤ x ^ (1 / 3 : ℝ) :=
        (Nat.cast_le.mpr (Finset.mem_Ioc.mp hq).2).trans (Nat.floor_le (by positivity))
      exact div_le_div_of_nonneg_right (hb x q hx hqn hqx) (by positivity)
    _ = C * Real.log x * ∑ q ∈ Finset.Ioc ⌊P⌋₊ ⌊x ^ (1 / 3 : ℝ)⌋₊,
        1 / (q : ℝ) ^ 2 := by simp [Finset.mul_sum, div_eq_mul_inv]
    _ ≤ C * Real.log x * (2 / P) :=
      mul_le_mul_of_nonneg_left (Task292a.reciprocal_square_tail P _ hP) (by positivity)
    _ = (2 * C) * (Real.log x / P) := by ring

#print axioms localMajorant_sixth_log_bound
#print axioms majorant_square_tail
#print axioms LeanLab.PNTSieve.Mertens.sum_inv_primes_le

end LeanLab.KumchevLiu2007.Task438k
