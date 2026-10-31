import LeanLab.Pintz2021.DivisorTask53

/-!
Divisor weights for P0054 page 5 display 2.4 and page 14 display 4.9.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.DivisorSumTask53

open Finset ElementaryTask08 DivisorTask53

attribute [local instance] Classical.propDecidable

/-- The positive squarefree divisor weight on odd integers. -/
noncomputable def divisorWeight (d : ℕ) : ℝ :=
  ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) - 2))

/-- Reindex the exact singular series expansion by odd squarefree divisors. -/
theorem Sing_eq_divisor_sum {m : ℕ} (hm : m ≠ 0) :
    Sing m = 2 * C0 * ∑ d ∈ oddSquarefreeDivisors m, divisorWeight d := by
  rw [Sing_eq_subset_sum]
  congr 1
  rw [← subset_products_eq hm, sum_image (subset_prod_injective m)]
  apply sum_congr rfl
  intro s hs
  have hp : ∀ p ∈ s, p.Prime := fun p h =>
    Nat.prime_of_mem_primeFactors (mem_filter.mp ((mem_powerset.mp hs) h)).1
  simp only [divisorWeight, Nat.primeFactors_prod hp]

/-- A fixed divisor range for the translated differences in Lemma 2. -/
noncomputable def oddSquarefreeUpTo (m : ℕ) : Finset ℕ :=
  (Icc 1 m).filter fun d => Odd d ∧ Squarefree d

/-- Extend a divisor sum to a fixed upper bound using divisibility. -/
theorem divisor_sum_eq_fixed {n m : ℕ} (hn : n ≠ 0) (hnm : n ≤ m) :
    ∑ d ∈ oddSquarefreeDivisors n, divisorWeight d =
      ∑ d ∈ oddSquarefreeUpTo m, if d ∣ n then divisorWeight d else 0 := by
  have hset : (oddSquarefreeUpTo m).filter (fun d => d ∣ n) =
      oddSquarefreeDivisors n := by
    ext d
    simp only [oddSquarefreeUpTo, oddSquarefreeDivisors, mem_filter, mem_Icc,
      Nat.mem_divisors]
    constructor
    · rintro ⟨⟨⟨_, _⟩, ho, hsq⟩, hd⟩
      exact ⟨⟨hd, hn⟩, ho, hsq⟩
    · rintro ⟨⟨hd, _⟩, ho, hsq⟩
      exact ⟨⟨⟨hsq.ne_zero.bot_lt, (Nat.le_of_dvd hn.bot_lt hd).trans hnm⟩,
        ho, hsq⟩, hd⟩
  rw [← sum_filter, hset]

/-- The finite exponent range in Lemma 2 with an arbitrary natural cutoff. -/
noncomputable def eligibleExponents (m q K : ℕ) : Finset ℕ :=
  (Icc 1 K).filter fun ν => 2 ^ ν < m ∧ q ∣ m - 2 ^ ν

/-- Interchange the divisor and exponent sums without an analytic input. -/
theorem lemma2_sum_eq_divisor_count (m q K : ℕ) :
    ∑ ν ∈ eligibleExponents m q K, Sing (m - 2 ^ ν) =
      2 * C0 * ∑ d ∈ oddSquarefreeUpTo m,
        divisorWeight d * ((eligibleExponents m q K).filter
          (fun ν => d ∣ m - 2 ^ ν)).card := by
  have expand : ∀ ν ∈ eligibleExponents m q K,
      Sing (m - 2 ^ ν) = 2 * C0 * ∑ d ∈ oddSquarefreeUpTo m,
        if d ∣ m - 2 ^ ν then divisorWeight d else 0 := by
    intro ν hν
    have hpos := (mem_filter.mp hν).2.1
    rw [Sing_eq_divisor_sum (Nat.sub_pos_of_lt hpos).ne',
      divisor_sum_eq_fixed (Nat.sub_pos_of_lt hpos).ne' (Nat.sub_le _ _)]
  calc
    _ = 2 * C0 * ∑ ν ∈ eligibleExponents m q K,
        ∑ d ∈ oddSquarefreeUpTo m,
          if d ∣ m - 2 ^ ν then divisorWeight d else 0 := by
      rw [mul_sum]
      exact sum_congr rfl expand
    _ = _ := by
      congr 1
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]

/-- The exact divisor expansion with the two moduli combined. -/
theorem lemma2_sum_eq_lcm_count (m q K : ℕ) :
    ∑ ν ∈ eligibleExponents m q K, Sing (m - 2 ^ ν) =
      2 * C0 * ∑ d ∈ oddSquarefreeUpTo m,
        divisorWeight d * (eligibleExponents m (Nat.lcm d q) K).card := by
  rw [lemma2_sum_eq_divisor_count]
  congr 1
  apply sum_congr rfl
  intro d _
  have hset : (eligibleExponents m q K).filter (fun ν => d ∣ m - 2 ^ ν) =
      eligibleExponents m (Nat.lcm d q) K := by
    ext ν
    simp only [eligibleExponents, mem_filter, Nat.lcm_dvd_iff]
    tauto
  rw [hset]

end LeanLab.Pintz2021.DivisorSumTask53

#print axioms LeanLab.Pintz2021.DivisorSumTask53.Sing_eq_divisor_sum
#print axioms LeanLab.Pintz2021.DivisorSumTask53.divisor_sum_eq_fixed
#print axioms LeanLab.Pintz2021.DivisorSumTask53.lemma2_sum_eq_divisor_count
#print axioms LeanLab.Pintz2021.DivisorSumTask53.lemma2_sum_eq_lcm_count
