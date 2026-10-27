/-
Derived elementary bounds for the even correction in P0013 page 9 equation 2.23.
All even nonzero von Mangoldt terms are powers of two.
The divisor sum identity bounds their total mass by log N below N.
AI wrote the Lean code for CODEX task119. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.FiniteS

namespace LeanLab.HelfgottArcs.EvenPrimePowers119
open ArithmeticFunction Finset

/-- Page 9 equation 2.23, derived support fact for the even correction. -/
theorem even_vonMangoldt_dvd (n N : ℕ) (hn : n < N) (he : Even n)
    (hv : vonMangoldt n ≠ 0) : n ∣ 2 ^ Nat.log 2 N := by
  rcases (isPrimePow_nat_iff n).mp (vonMangoldt_ne_zero_iff.mp hv) with ⟨p, k, hp, hk, hpow⟩
  have htwo : 2 ∣ p ^ k := by rw [hpow]; exact even_iff_two_dvd.mp he
  have hp2 : p = 2 :=
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow htwo)).symm
  subst p
  have hkN : k ≤ Nat.log 2 N := Nat.le_log_of_pow_le Nat.one_lt_two (by omega)
  rw [← hpow]
  exact Nat.pow_dvd_pow 2 hkN

/-- Page 9 equation 2.23, derived mass bound by the divisor sum at a power of two. -/
theorem sum_even_vonMangoldt_le_log (N : ℕ) :
    (∑ n ∈ range N, if Even n then vonMangoldt n else 0) ≤ Real.log N := by
  classical
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  let s := (range N).filter (fun n => Even n ∧ vonMangoldt n ≠ 0)
  have heq : (∑ n ∈ range N, if Even n then vonMangoldt n else 0) =
      ∑ n ∈ s, vonMangoldt n := by
    rw [show s = (range N).filter (fun n => Even n ∧ vonMangoldt n ≠ 0) from rfl,
      sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases he : Even n <;> by_cases hv : vonMangoldt n = 0 <;> simp [he, hv]
  have hsub : s ⊆ (2 ^ Nat.log 2 N).divisors := by
    intro n hn
    rcases mem_filter.mp hn with ⟨hn, he, hv⟩
    exact Nat.mem_divisors.mpr ⟨even_vonMangoldt_dvd n N (mem_range.mp hn) he hv,
      pow_ne_zero _ (by norm_num)⟩
  rw [heq]
  calc
    _ ≤ ∑ n ∈ (2 ^ Nat.log 2 N).divisors, vonMangoldt n :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)
    _ = Real.log (2 ^ Nat.log 2 N : ℕ) := vonMangoldt_sum
    _ ≤ Real.log N := Real.log_le_log (by positivity)
      (by exact_mod_cast Nat.pow_log_le_self 2 hN)

/-- Page 9 equation 2.23, derived triangle bound with the paper's exact weight. -/
theorem norm_even_sum_le (α x : ℝ) (hx : 0 < x) :
    ‖∑ n ∈ range ⌈x⌉₊, if Even n then
        (vonMangoldt n : ℂ) * e (α * n) * (eta2 (n / x) : ℂ) else 0‖ ≤
      4 * Real.log 2 * Real.log (⌈x⌉₊ : ℝ) := by
  calc
    _ ≤ ∑ n ∈ range ⌈x⌉₊, ‖if Even n then
        (vonMangoldt n : ℂ) * e (α * n) * (eta2 (n / x) : ℂ) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ range ⌈x⌉₊, (4 * Real.log 2) *
        (if Even n then vonMangoldt n else 0) := by
      apply sum_le_sum
      intro n hn
      split_ifs with he
      · rw [norm_mul, norm_mul, norm_e, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg,
          abs_of_nonneg (eta2_nonneg _)]
        nlinarith [mul_le_mul_of_nonneg_left (eta2_le ((n : ℝ) / x))
          (vonMangoldt_nonneg (n := n))]
      · simp
    _ = (4 * Real.log 2) * ∑ n ∈ range ⌈x⌉₊, if Even n then vonMangoldt n else 0 :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_even_vonMangoldt_le_log _)
      (by positivity)

end LeanLab.HelfgottArcs.EvenPrimePowers119
