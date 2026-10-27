import Mathlib

/-!
Certified logarithm bounds for P0032 page 46 equation 2.2.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RieselVaughan1983.StieltjesCert

open Real Finset

def logPoly (z : ℚ) : ℚ :=
  ∑ k ∈ range 12, 2 * (1 / (2 * (k : ℚ) + 1)) * z ^ (2 * k + 1)

lemma log_series_bounds (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1 / 3) :
    (∑ k ∈ range 12, 2 * (1 / (2 * (k : ℝ) + 1)) * z ^ (2 * k + 1)) ≤
        Real.log (1 + z) - Real.log (1 - z) ∧
      Real.log (1 + z) - Real.log (1 - z) ≤
        (∑ k ∈ range 12, 2 * (1 / (2 * (k : ℝ) + 1)) * z ^ (2 * k + 1)) + 1 / 1000000000 := by
  have hz1 : |z| < 1 := by rw [abs_of_nonneg hz]; linarith
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hz1
  have hl := sum_le_hasSum (range 12) (fun k _ => by positivity) hs
  refine ⟨hl, ?_⟩
  rw [← hasSum_nat_add_iff' 12] at hs
  have hg := (hasSum_geometric_of_lt_one (sq_nonneg z)
    (show z ^ 2 < 1 by nlinarith)).mul_left (2 * z ^ 25)
  have hu := hasSum_le (fun k => ?_) hs hg
  · have hb : 2 * z ^ 25 * (1 - z ^ 2)⁻¹ ≤ 1 / 1000000000 := by
      have hpow : z ^ 25 ≤ (1 / 3 : ℝ) ^ 25 := pow_le_pow_left₀ hz hz' 25
      have hinv : (1 - z ^ 2)⁻¹ ≤ (9 / 8 : ℝ) := by
        rw [inv_eq_one_div, div_le_iff₀ (by nlinarith)]
        nlinarith
      calc 2 * z ^ 25 * (1 - z ^ 2)⁻¹ ≤ 2 * (1 / 3 : ℝ) ^ 25 * (9 / 8) := by
              apply mul_le_mul _ hinv (le_of_lt (inv_pos.mpr (by nlinarith))) (by positivity)
              linarith
        _ ≤ 1 / 1000000000 := by norm_num
    linarith
  · have hp : z ^ (2 * (k + 12) + 1) = z ^ 25 * (z ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    have hk : (1 : ℝ) / (2 * ((k + 12 : ℕ) : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; push_cast; nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    rw [hp]
    have hnon : 0 ≤ z ^ 25 * (z ^ 2) ^ k := by positivity
    nlinarith

def dyadicExponent (m : ℕ) : ℕ := Nat.log 2 m

def reduced (m : ℕ) : ℚ :=
  ((m : ℚ) - 2 ^ dyadicExponent m) / ((m : ℚ) + 2 ^ dyadicExponent m)

def logLower (m : ℕ) : ℚ :=
  dyadicExponent m * (693147180 / 1000000000) + logPoly (reduced m)

def logUpper (m : ℕ) : ℚ := logLower m + (dyadicExponent m + 1) / 1000000000

lemma log_bounds (m : ℕ) (hm : 1 ≤ m) :
    (logLower m : ℝ) ≤ Real.log m ∧ Real.log m ≤ (logUpper m : ℝ) := by
  let b := dyadicExponent m
  let p : ℝ := 2 ^ b
  have hp : 0 < p := by dsimp [p]; positivity
  have hpm : p ≤ m := by
    dsimp [p, b, dyadicExponent]
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : m ≠ 0)
  have hmp : (m : ℝ) ≤ 2 * p := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
    have h' : (m : ℝ) < (2 : ℝ) ^ (Nat.log 2 m + 1) := by exact_mod_cast h
    simpa [pow_succ, p, b, dyadicExponent, mul_comm] using h'.le
  have hmc : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  let z : ℝ := ((m : ℝ) - p) / ((m : ℝ) + p)
  have hz : 0 ≤ z := div_nonneg (by linarith) (by positivity)
  have hz' : z ≤ 1 / 3 := by
    dsimp [z]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  obtain ⟨hl, hu⟩ := log_series_bounds z hz hz'
  have heq : Real.log (1 + z) - Real.log (1 - z) = Real.log m - b * Real.log 2 := by
    have hmz : 0 < 1 - z := by linarith
    rw [← Real.log_div (by positivity) hmz.ne']
    have he : (1 + z) / (1 - z) = (m : ℝ) / p := by
      dsimp [z]
      field_simp [hp.ne']
      <;> ring
    rw [he, Real.log_div hmc.ne' hp.ne']
    dsimp [p]; rw [Real.log_pow]
  have hcast : (logPoly (reduced m) : ℝ) =
      ∑ k ∈ range 12, 2 * (1 / (2 * (k : ℝ) + 1)) * z ^ (2 * k + 1) := by
    simp only [logPoly, Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_one,
      Rat.cast_add, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow]
    congr 1; ext k
    congr 1
    dsimp [reduced, z, p, b]
    push_cast
    rfl
  rw [heq, ← hcast] at hl hu
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  constructor
  · dsimp [logLower]; push_cast
    have : (b : ℝ) * (693147180 / 1000000000) ≤ b * Real.log 2 := by
      gcongr; linarith
    dsimp [b] at this; linarith
  · dsimp [logUpper, logLower]; push_cast
    have : (b : ℝ) * Real.log 2 ≤ b * (693147181 / 1000000000) := by
      gcongr; linarith
    dsimp [b] at this; linarith

end LeanLab.RieselVaughan1983.StieltjesCert

#print axioms LeanLab.RieselVaughan1983.StieltjesCert.log_series_bounds
#print axioms LeanLab.RieselVaughan1983.StieltjesCert.log_bounds
