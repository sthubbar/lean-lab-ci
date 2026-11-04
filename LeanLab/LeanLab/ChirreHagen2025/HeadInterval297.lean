import LeanLab.ChirreHagen2025.TailIntegral297

/-!
Rational interval bounds for P0075 Lemma A.1, page 14.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.HeadInterval297
open TailIntegral297

/-- P0075 page 14, a rational upper interval endpoint for log q. -/
def logUpper (q : ℚ) (m : ℕ) : ℚ :=
  let z := (q - 1) / (q + 1)
  2 * ((∑ i ∈ Finset.range m, z ^ (2 * i + 1) / (2 * i + 1)) +
    z ^ (2 * m + 1) / (1 - z ^ 2))

/-- P0075 page 14, correctness of the rational logarithm interval. -/
theorem log_le_logUpper (q : ℚ) (hq : 1 ≤ q) (m : ℕ) :
    Real.log (q : ℝ) ≤ (logUpper q m : ℝ) := by
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqp : (0 : ℝ) < (q : ℝ) + 1 := by linarith
  have hz0 : (0 : ℝ) ≤ ((q : ℝ) - 1) / ((q : ℝ) + 1) := by positivity
  have hz1 : ((q : ℝ) - 1) / ((q : ℝ) + 1) < 1 := by
    apply (div_lt_one hqp).mpr
    linarith
  have he : (1 + ((q : ℝ) - 1) / ((q : ℝ) + 1)) /
      (1 - ((q : ℝ) - 1) / ((q : ℝ) + 1)) = q := by field_simp; ring
  have h := Real.log_div_le_sum_range_add hz0 hz1 m
  rw [he] at h
  unfold logUpper
  push_cast
  linarith

/-- P0075 page 14, dyadic scaling keeps the logarithm interval computation short. -/
theorem log_le_dyadic_upper (n k m : ℕ) (hn : 2 ^ k ≤ n) :
    Real.log (n : ℝ) ≤
      (k : ℝ) * (logUpper 2 m : ℝ) + (logUpper ((n : ℚ) / 2 ^ k) m : ℝ) := by
  have hk0 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity : 0 < 2 ^ k) hn
  have hq : (1 : ℚ) ≤ (n : ℚ) / 2 ^ k := by
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 2 ^ k)).mpr
    simpa only [one_mul] using (show (2 : ℚ) ^ k ≤ n by exact_mod_cast hn)
  have h := log_le_logUpper ((n : ℚ) / 2 ^ k) hq m
  push_cast at h
  rw [Real.log_div (by exact_mod_cast hn0.ne') hk0.ne', Real.log_pow] at h
  have htwo := log_le_logUpper 2 (by norm_num) m
  have hm := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (α := ℝ) k)
  norm_num at hm
  linarith

/-- P0075 page 14, interval data bounds one extended prime summand. -/
theorem weight_le_of_intervals {x L S : ℝ} (hx : 2 ≤ x) (hL : Real.log x ≤ L)
    (hS : 0 < S) (hroot : S ^ 2 ≤ x) :
    weight x ≤ L / (S * (x - 1)) := by
  have hm : 0 < x - 1 := by linarith
  have hl0 := Real.log_nonneg (show 1 ≤ x by linarith)
  have hL0 : 0 ≤ L := hl0.trans hL
  have hs : S ≤ Real.sqrt x := (Real.le_sqrt hS.le (by linarith)).mpr hroot
  unfold weight
  exact (div_le_div_of_nonneg_right hL (by positivity)).trans
    (div_le_div_of_nonneg_left hL0 (by positivity) (mul_le_mul_of_nonneg_right hs hm.le))

/-- P0075 page 14, a prime bucket is bounded by its certified count and left endpoint.
The count hypothesis must be checked before this theorem certifies a computation. -/
theorem prime_bucket_bound (a b c : ℕ) (ha : 8 ≤ a)
    (hcount : ((Finset.Ico a b).filter Nat.Prime).card ≤ c)
    {U : ℝ} (hU : weight a ≤ U) :
    (∑ p ∈ (Finset.Ico a b).filter Nat.Prime, weight p) ≤ (c : ℝ) * U := by
  have ha8 : (8 : ℝ) ≤ a := by exact_mod_cast ha
  have hu0 : 0 ≤ U := (weight_nonneg (show 2 ≤ (a : ℝ) by linarith)).trans hU
  calc
    _ ≤ ∑ p ∈ (Finset.Ico a b).filter Nat.Prime, U := by
      apply Finset.sum_le_sum
      intro p hp
      have hp1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
      have hpa : (a : ℝ) ≤ p := by exact_mod_cast hp1
      exact (weight_antitone (exp_two_lt_eight.le.trans ha8)
        (exp_two_lt_eight.le.trans (ha8.trans hpa)) hpa).trans hU
    _ = (((Finset.Ico a b).filter Nat.Prime).card : ℝ) * U := by simp
    _ ≤ (c : ℝ) * U := mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hu0

end LeanLab.ChirreHagen2025.HeadInterval297
