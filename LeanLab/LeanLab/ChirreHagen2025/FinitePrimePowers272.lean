import LeanLab.ChirreHagen2025.Summability272

/-!
P0075 page 14, equation A.1, comparison of prime-power tails.
AI wrote this Lean code. Goldbach is open.
-/
open ArithmeticFunction
namespace LeanLab.ChirreHagen2025.FinitePrimePowers272

/-- P0075 page 14, equation A.1, evaluation of the full geometric prime-power tail. -/
theorem prime_power_tail (p : Nat.Primes) :
    HasSum (fun k : ℕ => Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ (k + 2))
      (Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (p : ℝ))) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp2 : (p : ℝ) ^ 2 - (p : ℝ) ≠ 0 := by nlinarith
  have hr : |(p : ℝ)⁻¹| < 1 := by
    rw [abs_of_pos (by positivity)]
    exact inv_lt_one_of_one_lt₀ hp
  have hg := (hasSum_geometric_of_abs_lt_one hr).mul_left
    (Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2)
  convert hg using 1
  · funext k
    simp only [pow_add, div_eq_mul_inv, inv_pow]
    ring
  · field_simp

/-- P0075 page 14, equation A.1, bounding a finite prime-power tail by the full tail. -/
theorem prime_power_partial (p : Nat.Primes) (K : ℕ) :
    (∑ k ∈ Finset.Icc 2 K, Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ k) ≤
      Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (p : ℝ)) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  have he : K + 1 - 2 = K - 1 := by omega
  rw [he]
  calc
    (∑ k ∈ Finset.range (K - 1), Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ (2 + k)) =
        ∑ k ∈ Finset.range (K - 1), Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ (k + 2) := by
      simp only [Nat.add_comm 2]
    _ ≤ ∑' k : ℕ, Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ (k + 2) :=
      (prime_power_tail p).summable.sum_le_tsum _ (fun k hk => by positivity)
    _ = _ := (prime_power_tail p).tsum_eq

/-- P0075 page 14, equation A.1, the finite prime-power comparison.
This has exactly the statement of DecompJ611.leaf_sum_prime_powers.
Convergence of the outer series has a proved elementary source in Summability272. -/
theorem leaf_sum_prime_powers (x : ℝ) (hx : 10 ^ 13 ≤ x) :
    (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊Real.sqrt x⌋₊),
      ∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log (p : ℝ)⌋₊,
        Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ k) ≤
          ∑' p : Nat.Primes, Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (p : ℝ)) := by
  let s := Finset.filter Nat.Prime (Finset.Icc 1 ⌊Real.sqrt x⌋₊)
  have hs : ∀ p ∈ s, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  change (∑ p ∈ s, ∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log (p : ℝ)⌋₊,
    Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ k) ≤ _
  rw [← Finset.sum_subtype_of_mem
    (fun p : ℕ => ∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log (p : ℝ)⌋₊,
      Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ k) hs]
  change (∑ p ∈ s.subtype Nat.Prime,
    ∑ k ∈ Finset.Icc 2 ⌊Real.log x / Real.log (p : ℝ)⌋₊,
      Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ k) ≤
        ∑' p : {n : ℕ // Nat.Prime n}, Real.log (p : ℝ) ^ 2 /
          ((p : ℝ) ^ 2 - (p : ℝ))
  have hseries' : Summable (fun p : {n : ℕ // Nat.Prime n} =>
      Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (p : ℝ))) := Summability272.part3_summable
  calc
    _ ≤ ∑ p ∈ s.subtype Nat.Prime,
        Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact prime_power_partial p _
    _ ≤ _ := hseries'.sum_le_tsum _ (fun p hp => by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
      have hd : 0 < (p : ℝ) ^ 2 - (p : ℝ) := by nlinarith
      positivity)

end LeanLab.ChirreHagen2025.FinitePrimePowers272
