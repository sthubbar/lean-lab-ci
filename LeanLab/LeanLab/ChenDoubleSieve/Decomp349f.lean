import LeanLab.ChenDoubleSieve.Decomp349e
import LeanLab.ChenDoubleSieve.Decomp363h

/-!
Finite Euler product preparation for the common factor error in Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, page 40 before equation 10.8.
Only the logarithmic upper order is asserted here.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task349

/-- The squarefree reciprocal totient sum is bounded by its finite Euler product.
This uses Mathlib's squarefree divisor product identity on the primorial. -/
theorem squarefree_totient_sum_le_product (N : ℕ) :
    (∑ d ∈ (Finset.range (N + 1)).filter Squarefree,
      1 / (d.totient : ℝ)) ≤
        ∏ p ∈ N.primesLE, (1 + 1 / ((p : ℝ) - 1)) := by
  let g : ArithmeticFunction ℝ := ⟨fun n => 1 / (n.totient : ℝ), by simp⟩
  have hg : g.IsMultiplicative := by
    constructor
    · simp [g]
    · intro m n h
      change 1 / ((m * n).totient : ℝ) =
        (1 / (m.totient : ℝ)) * (1 / (n.totient : ℝ))
      rw [Nat.totient_mul h, Nat.cast_mul, one_div_mul_one_div]
  have hidentity := hg.prodPrimeFactors_one_add_of_squarefree (squarefree_primorial N)
  have hproduct : (∏ p ∈ N.primesLE, (1 + 1 / ((p : ℝ) - 1))) =
      ∑ d ∈ (primorial N).divisors, 1 / (d.totient : ℝ) := by
    calc
      _ = ∏ p ∈ N.primesLE, (1 + g p) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hprime := Nat.prime_of_mem_primesLE hp
        change 1 + 1 / ((p : ℝ) - 1) = 1 + 1 / (p.totient : ℝ)
        rw [Nat.totient_prime hprime, Nat.cast_sub hprime.one_lt.le, Nat.cast_one]
      _ = ∑ d ∈ (primorial N).divisors, g d := by
        simpa only [primeFactors_primorial] using hidentity
      _ = _ := rfl
  rw [hproduct]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_range] at hd
    have hdN : d ≤ N := by omega
    exact Nat.mem_divisors.mpr
      ⟨dvd_trans hd.2.dvd_primorial (primorial_dvd_primorial hdN), (primorial_pos N).ne'⟩
  · intro d hd hnot
    positivity

/-- The prime reciprocal totient product is bounded by an existing local density. -/
theorem prime_totient_product_le_density {N : ℕ} (hN : 2 ≤ N) :
    (∏ p ∈ N.primesLE, (1 + 1 / ((p : ℝ) - 1))) ≤
      2 / Task363.localDensity 2 ((N : ℝ) + 1) := by
  have htwo : 2 ∈ N.primesLE := Nat.mem_primesLE.mpr ⟨hN, Nat.prime_two⟩
  have hset : N.primesLE.erase 2 = Wu41.PS 2 0 ((N : ℝ) + 1) := by
    ext p
    simp only [Finset.mem_erase, Nat.mem_primesLE, Wu41.mem_PS]
    constructor
    · rintro ⟨hp2, hpN, hprime⟩
      refine ⟨hprime, Nat.cast_nonneg p, ?_,
        (Nat.coprime_primes hprime Nat.prime_two).mpr hp2⟩
      exact_mod_cast (show p < N + 1 by omega)
    · rintro ⟨hprime, hp0, hpN, hcop⟩
      refine ⟨?_, ?_, hprime⟩
      · intro hp2
        subst p
        norm_num at hcop
      · have hpN' : p < N + 1 := by exact_mod_cast hpN
        omega
  have hpgt : ∀ p ∈ Wu41.PS 2 0 ((N : ℝ) + 1), (2 : ℝ) < p := by
    intro p hp
    have hs := Wu41.mem_PS.mp hp
    have hp2 : p ≠ 2 := by intro heq; subst p; norm_num at hs
    exact_mod_cast (show 2 < p by have := hs.1.two_le; omega)
  calc
    _ = 2 * ∏ p ∈ Wu41.PS 2 0 ((N : ℝ) + 1), (1 + 1 / ((p : ℝ) - 1)) := by
      rw [← Finset.mul_prod_erase N.primesLE (fun p => (1 + 1 / ((p : ℝ) - 1))) htwo,
        hset]
      norm_num
    _ ≤ 2 * ∏ p ∈ Wu41.PS 2 0 ((N : ℝ) + 1), (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.prod_le_prod₀
      · intro p hp
        have h := hpgt p hp
        exact add_nonneg zero_le_one (div_nonneg zero_le_one (by linarith))
      · intro p hp
        have h := hpgt p hp
        have hleft : (1 + 1 / ((p : ℝ) - 1)) = (p : ℝ) / ((p : ℝ) - 1) := by
          field_simp [show (p : ℝ) - 1 ≠ 0 by linarith]
          <;> ring
        have hright : (1 - 1 / ((p : ℝ) - 1))⁻¹ =
            ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
          have heq : (1 - 1 / ((p : ℝ) - 1)) =
              ((p : ℝ) - 2) / ((p : ℝ) - 1) := by
            field_simp [show (p : ℝ) - 1 ≠ 0 by linarith]
            <;> ring
          rw [heq, inv_div]
        rw [hleft, hright, div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith
    _ = 2 / Task363.localDensity 2 ((N : ℝ) + 1) := by
      rw [Task363.localDensity, Finset.prod_inv_distrib]
      ring

/-- The finite prime product has a uniform logarithmic upper bound.
Only the already proved local density dimension estimate is used. -/
theorem prime_totient_product_log_bounded : ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 2 ≤ N →
      (∏ p ∈ N.primesLE, (1 + 1 / ((p : ℝ) - 1))) ≤ C * log ((N : ℝ) + 1) := by
  obtain ⟨K, hK, hbound⟩ := Task363.localDensity_dimension
  have hl : 0 < log (2 : ℝ) := log_pos (by norm_num)
  let C : ℝ := 2 * (1 + K / log 2) / log 2
  have hKpos : 0 < K := by linarith
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hd := hbound 2 (by decide) 2 ((N : ℝ) + 1) (by norm_num) (by linarith)
  rw [Task363.localDensity_below_three (show Even (2 : ℕ) by decide)
    (by norm_num : (2 : ℝ) ≤ 3)] at hd
  calc
    _ ≤ 2 / Task363.localDensity 2 ((N : ℝ) + 1) := prime_totient_product_le_density hN
    _ = 2 * (1 / Task363.localDensity 2 ((N : ℝ) + 1)) := by ring
    _ ≤ 2 * (log ((N : ℝ) + 1) / log 2 * (1 + K / log 2)) :=
      mul_le_mul_of_nonneg_left hd (by norm_num)
    _ = C * log ((N : ℝ) + 1) := by dsimp [C]; ring

/-- The squarefree reciprocal totient sum has the upper order used in 10.8.
This is an upper bound, not the two-sided asymptotic printed in the paper. -/
theorem squarefree_totient_sum_log_bounded : ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, 2 ≤ N →
      (∑ d ∈ (Finset.range (N + 1)).filter Squarefree,
        1 / (d.totient : ℝ)) ≤ C * log ((N : ℝ) + 1) := by
  obtain ⟨C, hC, hbound⟩ := prime_totient_product_log_bounded
  exact ⟨C, hC, fun N hN => (squarefree_totient_sum_le_product N).trans (hbound N hN)⟩

end LeanLab.ChenDoubleSieve.Task349
