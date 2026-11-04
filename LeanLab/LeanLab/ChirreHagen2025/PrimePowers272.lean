import LeanLab.ChirreHagen2025.Additional122

/-!
P0075 page 14, the prime-power identity in Lemma A.1 part 2.
AI wrote this Lean code. Goldbach is open.
-/
open ArithmeticFunction
namespace LeanLab.ChirreHagen2025.PrimePowers272

/-- P0075 page 14, the displayed prime-power identity in Lemma A.1 part 2.
Reuse Mathlib's prime-power reindexing and its geometric sum theorem.
The Mangoldt series is already proved summable in Additional122. -/
theorem mangoldt_sum_eq_prime_sum :
    (∑' n : ℕ, vonMangoldt (n + 1) ^ 2 / ((n : ℝ) + 1) ^ 2) =
    (∑' p : Nat.Primes, Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)) := by
  have hall : Summable (fun n : ℕ => vonMangoldt n ^ 2 / (n : ℝ) ^ 2) := by
    rw [← summable_nat_add_iff 1]
    simpa only [Nat.cast_add, Nat.cast_one] using Additional122.mangoldt_sq_summable
  have hsupp : Function.support (fun n : ℕ => vonMangoldt n ^ 2 / (n : ℝ) ^ 2) ⊆
      {n | IsPrimePow n} := by
    intro n hn
    by_contra hp
    have hz : vonMangoldt n = 0 := vonMangoldt_eq_zero_iff.mpr hp
    simp [hz, Function.mem_support] at hn
  have hreindex := tsum_eq_tsum_primes_of_support_subset_prime_powers hall hsupp
  have hshift : (∑' n : ℕ, vonMangoldt (n + 1) ^ 2 / ((n : ℝ) + 1) ^ 2) =
      ∑' n : ℕ, vonMangoldt n ^ 2 / (n : ℝ) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one, ArithmeticFunction.map_zero, zero_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_div, zero_add]
      using hall.tsum_eq_zero_add.symm
  rw [hshift, hreindex]
  apply tsum_congr
  intro p
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hr : |(p : ℝ)⁻¹ ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hp) (by norm_num)
  have hg := (hasSum_geometric_of_abs_lt_one hr).mul_left
    (Real.log (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ 2)
  have heq : (fun k : ℕ => vonMangoldt ((p : ℕ) ^ (k + 1)) ^ 2 /
      (((p : ℕ) ^ (k + 1) : ℕ) : ℝ) ^ 2) =
      (fun k : ℕ => (Real.log (p : ℝ) ^ 2 * (p : ℝ)⁻¹ ^ 2) * ((p : ℝ)⁻¹ ^ 2) ^ k) := by
    funext k
    rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime p.property]
    push_cast
    simp only [div_eq_mul_inv, inv_pow, pow_succ, mul_pow]
    ring
  rw [heq, hg.tsum_eq]
  field_simp

end LeanLab.ChirreHagen2025.PrimePowers272
