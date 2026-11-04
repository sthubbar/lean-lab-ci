import LeanLab.ChirreHagen2025.Additional122
import LeanLab.ChirreHagen2025.DecompJ207

/-!
Convergence and series comparison from P0075 Lemma A.1, pages 13 and 14.
AI wrote this Lean code. Goldbach is open.
-/

open ArithmeticFunction
namespace LeanLab.ChirreHagen2025.Summability272

/-- P0075 page 14, Lemma A.1 part 2, the prime subseries of the squared Mangoldt series.
This asserts convergence and no numerical bound. -/
theorem prime_square_sum_summable :
    Summable (fun p : Nat.Primes => Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2) := by
  have hall : Summable (fun n : ℕ => vonMangoldt n ^ 2 / (n : ℝ) ^ 2) := by
    rw [← summable_nat_add_iff 1]
    simpa only [Nat.cast_add, Nat.cast_one] using Additional122.mangoldt_sq_summable
  have hp := hall.subtype Nat.Prime
  exact hp.congr (fun p => by simp only [Function.comp_apply, vonMangoldt_apply_prime p.property])

/-- P0075 page 14, Lemma A.1 part 3, convergence before the numerical estimate.
Compare with twice the prime subseries already proved summable. -/
theorem part3_summable :
    Summable (fun p : Nat.Primes => Real.log (p : ℝ) ^ 2 /
      ((p : ℝ) ^ 2 - (p : ℝ))) := by
  apply (prime_square_sum_summable.mul_left 2).of_nonneg_of_le
  · intro p
    have hp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
    have hd : 0 < (p : ℝ) ^ 2 - (p : ℝ) := by nlinarith
    positivity
  · intro p
    have hp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
    have hd : 0 < (p : ℝ) ^ 2 - (p : ℝ) := by nlinarith
    calc
      Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (p : ℝ))
          ≤ Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 / 2) :=
            div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
      _ = 2 * (Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2) := by
        have hp0 : (p : ℝ) ≠ 0 := by linarith
        field_simp


/-- P0075 pages 13 and 14, Lemma A.1 part 1, convergence before the numerical estimate.
The elementary comparison with eight times the p to minus five quarters series suffices. -/
theorem part1_summable :
    Summable (fun p : Nat.Primes => Real.log (p : ℝ) /
      (Real.sqrt (p : ℝ) * ((p : ℝ) - 1))) := by
  have hbase : Summable (fun p : Nat.Primes => 1 / (p : ℝ) ^ (5 / 4 : ℝ)) :=
    (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 5 / 4)).subtype Nat.Prime
  apply (hbase.mul_left 8).of_nonneg_of_le
  · intro p
    have hp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
    have hpm : 0 < (p : ℝ) - 1 := by linarith
    have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
    positivity
  · intro p
    have hp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hpm : 0 < (p : ℝ) - 1 := by linarith
    have hd : 0 < Real.sqrt (p : ℝ) * ((p : ℝ) - 1) := by positivity
    have hr : 0 < (p : ℝ) ^ (5 / 4 : ℝ) := by positivity
    rw [mul_one_div, div_le_div_iff₀ hd hr]
    have hl := Real.log_le_rpow_div hp0.le (by norm_num : (0 : ℝ) < 1 / 4)
    have he : (p : ℝ) ^ (1 / 4 : ℝ) * (p : ℝ) ^ (5 / 4 : ℝ) =
        (p : ℝ) * Real.sqrt (p : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      calc
        (p : ℝ) ^ (1 / 4 : ℝ) * (p : ℝ) ^ (5 / 4 : ℝ)
            = (p : ℝ) ^ (3 / 2 : ℝ) := by rw [← Real.rpow_add hp0]; norm_num
        _ = (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hp0]; norm_num
        _ = (p : ℝ) * (p : ℝ) ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
    calc
      Real.log (p : ℝ) * (p : ℝ) ^ (5 / 4 : ℝ)
          ≤ ((p : ℝ) ^ (1 / 4 : ℝ) / (1 / 4)) * (p : ℝ) ^ (5 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_right hl hr.le
      _ = 4 * ((p : ℝ) * Real.sqrt (p : ℝ)) := by rw [div_eq_mul_inv]; norm_num; nlinarith [he]
      _ ≤ 8 * (Real.sqrt (p : ℝ) * ((p : ℝ) - 1)) := by
        nlinarith [Real.sqrt_nonneg (p : ℝ)]


/-- P0075 page 14, Lemma A.1 part 2, the denominator comparison with part 3.
This has exactly the statement of DecompJ207.prime_sum_le_part3 and asserts no
numerical bound. Both series are proved summable before comparing their sums. -/
theorem prime_sum_le_part3 :
    (∑' (p : Nat.Primes), Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)) ≤
    (∑' (p : Nat.Primes), Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (p : ℝ))) := by
  have hpoint (p : Nat.Primes) :
      Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1) ≤
        Real.log (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - (p : ℝ)) := by
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left (DecompJ207.prime_fraction_le p p.property)
        (sq_nonneg (Real.log (p : ℝ)))
  have hleft := part3_summable.of_nonneg_of_le (fun p => by
    have hp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
    have hd : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
    positivity) hpoint
  exact Summable.tsum_le_tsum hpoint hleft part3_summable

end LeanLab.ChirreHagen2025.Summability272
