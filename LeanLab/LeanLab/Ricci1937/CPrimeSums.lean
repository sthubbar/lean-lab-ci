import Mathlib

/-!
Elementary auxiliary bounds for the identity polynomial count in Ricci 1937, page 74.
The bounds below are bookkeeping for an upper count, not printed claims of the paper.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Real Finset
noncomputable section

/-- Legendre's formula, with the prime sum written over primes through n. -/
lemma ricci_log_factorial (n : ℕ) :
    Real.log (n.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE n, (n.factorial.factorization p : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization] at hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.Prime.dvd_factorial hprime).mp
      (Nat.dvd_of_mem_primeFactors hp), hprime⟩
  · intro p _
    simp

/-- The first term of Legendre's formula is a lower bound. -/
lemma ricci_div_le_factorization_factorial (n p : ℕ) (hp : p.Prime) :
    n / p ≤ n.factorial.factorization p := by
  rw [Nat.factorization_factorial hp (b := Nat.log p n + 2) (by omega)]
  have hmem : 1 ∈ Ico 1 (Nat.log p n + 2) := by simp
  simpa using single_le_sum (fun i _ => Nat.zero_le (n / p ^ i)) hmem

/-- An elementary weak first Mertens bound from factorials and Chebyshev's theta bound. -/
theorem ricci_sum_log_div_primes_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + Real.log 4 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hterm : ∀ p ∈ Nat.primesLE n,
      ((n : ℝ) / p - 1) * Real.log p ≤
        (n.factorial.factorization p : ℝ) * Real.log p := by
    intro p hp
    have hprime := Nat.mem_primesLE.mp hp |>.2
    have hppos : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hfloor : (n : ℝ) / p - 1 ≤ ((n / p : ℕ) : ℝ) := by
      have h := Nat.lt_div_mul_add (a := n) hprime.pos
      have hR : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
      rw [sub_le_iff_le_add, div_le_iff₀ hppos]
      nlinarith
    have hfac : ((n / p : ℕ) : ℝ) ≤ (n.factorial.factorization p : ℝ) := by
      exact_mod_cast ricci_div_le_factorization_factorial n p hprime
    exact mul_le_mul_of_nonneg_right (hfloor.trans hfac)
      (Real.log_nonneg (by exact_mod_cast hprime.one_le))
  have hlower := sum_le_sum hterm
  rw [← ricci_log_factorial] at hlower
  have hleft : (∑ p ∈ Nat.primesLE n, ((n : ℝ) / p - 1) * Real.log p) =
      n * (∑ p ∈ Nat.primesLE n, Real.log p / p) - ∑ p ∈ Nat.primesLE n, Real.log p := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    ring
  rw [hleft] at hlower
  have hupper : Real.log (n.factorial : ℝ) ≤ n * Real.log n := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < n.factorial)
      (show (n.factorial : ℝ) ≤ (n : ℝ) ^ n by exact_mod_cast Nat.factorial_le_pow n)
    simpa only [Real.log_pow] using h
  have htheta := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  rw [Chebyshev.theta_eq_sum_primesLE_log] at htheta
  nlinarith

/-- A bounded reciprocal sum for primes in a block away from the origin. -/
theorem ricci_largePrime_reciprocal_sum_le (n : ℕ) (hn : 2 ≤ n)
    (S : Finset ℕ) (hS : S ⊆ Nat.primesLE n) {α : ℝ} (hα : 0 < α)
    (hlog : ∀ p ∈ S, α * Real.log n ≤ Real.log p) :
    ∑ p ∈ S, (1 : ℝ) / p ≤ (Real.log n + Real.log 4) / (α * Real.log n) := by
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  apply (le_div_iff₀ (mul_pos hα hln)).mpr
  calc
    (∑ p ∈ S, (1 : ℝ) / p) * (α * Real.log n) =
        ∑ p ∈ S, α * Real.log n / p := by rw [sum_mul]; congr 1; ext p; ring
    _ ≤ ∑ p ∈ S, Real.log p / p := by
      apply sum_le_sum
      intro p hp
      exact div_le_div_of_nonneg_right (hlog p hp) (Nat.cast_nonneg p)
    _ ≤ ∑ p ∈ Nat.primesLE n, Real.log p / p := by
      apply sum_le_sum_of_subset_of_nonneg hS
      intro p hp _
      have hprime := Nat.mem_primesLE.mp hp |>.2
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hprime.one_le)) (Nat.cast_nonneg _)
    _ ≤ Real.log n + Real.log 4 := ricci_sum_log_div_primes_le n (by omega)

/-- A fixed ratio block has a reciprocal prime sum bounded independently of n. -/
theorem ricci_prime_block_reciprocals (n : ℕ) (hn : 4 ≤ n)
    (S : Finset ℕ) (hS : S ⊆ Nat.primesLE n) {α : ℝ} (hα : 0 < α)
    (hsize : ∀ p ∈ S, (n : ℝ) ^ α ≤ p) :
    ∑ p ∈ S, (1 : ℝ) / p ≤ 2 / α := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hln : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hlog : ∀ p ∈ S, α * Real.log n ≤ Real.log p := by
    intro p hp
    have h := Real.log_le_log (Real.rpow_pos_of_pos hnpos α) (hsize p hp)
    rw [Real.log_rpow hnpos] at h
    exact h
  have h := ricci_largePrime_reciprocal_sum_le n (by omega) S hS hα hlog
  apply h.trans
  rw [div_le_div_iff₀ (mul_pos hα hln) hα]
  have hln4 : Real.log 4 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  nlinarith

example : ∑ p ∈ Nat.primesLE 4, Real.log p / p ≤ Real.log 4 + Real.log 4 :=
  ricci_sum_log_div_primes_le 4 (by norm_num)

example : (5 / 2 : ℕ) ≤ (5 : ℕ).factorial.factorization 2 :=
  ricci_div_le_factorization_factorial 5 2 Nat.prime_two

end
end LeanLab.Ricci1937
