/-
Asymptotic removal of higher prime powers in the weighted Goldbach count.
Source: P0029 page 4 and the implication on page 13.
These are derived error estimates, not extra analytic assumptions.
The sealed DecompJ1034 statements stay unchanged.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp384b
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace LeanLab.BhowmikGrimmelt2026

open Filter Topology Asymptotics

/-- The entire higher prime power error has square root times logarithm squared size.
Source: a derived quantitative form of the omission on P0029 page 4. -/
theorem r2_sub_primeR2_isBigO384 :
    (fun N : ℕ => r2 N - primeR2_384 N) =O[atTop]
      (fun N : ℕ => Real.sqrt N * (Real.log N) ^ 2) := by
  apply IsBigO.of_bound 4
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_of_nonneg (sub_nonneg.mpr (primeR2_bounds384 N).2),
    Real.norm_of_nonneg (by positivity : 0 ≤ Real.sqrt (N : ℝ) * (Real.log N) ^ 2)]
  simpa only [mul_assoc] using r2_sub_primeR2_sqrt_log_sq384 N hN

/-- The omitted higher prime power error has the sharper square root times logarithm bound.
Source: derived estimate for P0029 page 4, using Chebyshev.psi_sub_theta_le_mul_sqrt.
The constant is uniform in N and no prime representation assumption is used. -/
theorem prime_power_error_sqrt_log384 :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      r2 N - primeR2_384 N ≤ C * Real.sqrt N * Real.log N := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨2 * max C 1, by positivity, fun N hN => ?_⟩
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  calc
    _ ≤ 2 * Real.log N * (Chebyshev.psi N - Chebyshev.theta N) :=
      r2_sub_primeR2_le384 N hN
    _ ≤ 2 * Real.log N * (C * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left (hC N) (by positivity)
    _ ≤ 2 * Real.log N * (max C 1 * Real.sqrt N) := by
      gcongr
      exact le_max_left C 1
    _ = _ := by ring

/-- Square root times logarithm squared is little o of N.
Source: a derived growth comparison for the prime power omission on P0029 page 4. -/
theorem sqrt_mul_log_sq_isLittleO384 :
    (fun N : ℕ => Real.sqrt N * (Real.log N) ^ 2) =o[atTop] (fun N : ℕ => (N : ℝ)) := by
  have hlog : (fun N : ℕ => (Real.log (N : ℝ)) ^ 2) =o[atTop]
      (fun N : ℕ => Real.sqrt N) := by
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).natCast_atTop
  have h := (isBigO_refl (fun N : ℕ => Real.sqrt (N : ℝ)) atTop).mul_isLittleO hlog
  simpa only [Real.mul_self_sqrt (Nat.cast_nonneg _)] using h

/-- Higher prime powers change the weighted Goldbach count by little o of N.
Source: the error omitted on P0029 page 4, justified without a Goldbach assumption. -/
theorem r2_sub_primeR2_isLittleO384 :
    (fun N : ℕ => r2 N - primeR2_384 N) =o[atTop] (fun N : ℕ => (N : ℝ)) :=
  r2_sub_primeR2_isBigO384.trans_isLittleO sqrt_mul_log_sq_isLittleO384


/-- Removing higher prime powers preserves every normalization at least as large as N.
Source: derived consequence of the omission on P0029 page 4 and Conjecture 2.1 on page 7.
The lower bound on the normalizing function is an explicit hypothesis. -/
theorem normalized_prime_power_error384 (s : ℕ → ℝ)
    (hs : ∀ᶠ N in atTop, 1 ≤ s N) :
    Tendsto (fun N : ℕ => (r2 N - primeR2_384 N) / ((N : ℝ) * s N)) atTop (𝓝 0) := by
  have hscale : (fun N : ℕ => (N : ℝ)) =O[atTop] (fun N : ℕ => (N : ℝ) * s N) := by
    apply IsBigO.of_bound 1
    filter_upwards [hs] with N hN
    rw [Real.norm_of_nonneg (Nat.cast_nonneg N),
      Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg N) (by linarith)), one_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg (α := ℝ) N)
  exact (r2_sub_primeR2_isLittleO384.trans_isBigO hscale).tendsto_div_nhds_zero

/-- The normalized von Mangoldt and weighted prime counts have the same limit.
Source: derived justification of the omission on P0029 page 4.
This proves neither of the two asserted limits. -/
theorem normalized_prime_count_limit_iff384 (s : ℕ → ℝ)
    (hs : ∀ᶠ N in atTop, 1 ≤ s N) (L : ℝ) :
    Tendsto (fun N : ℕ => r2 N / ((N : ℝ) * s N)) atTop (𝓝 L) ↔
      Tendsto (fun N : ℕ => primeR2_384 N / ((N : ℝ) * s N)) atTop (𝓝 L) := by
  have hz := normalized_prime_power_error384 s hs
  constructor
  · intro h
    convert h.sub hz using 1
    · ext N
      rw [sub_div]
      ring
    · simp
  · intro h
    convert h.add hz using 1
    · ext N
      rw [sub_div]
      ring
    · simp

/-- No fixed logarithm cubed budget dominates the square root times logarithm squared budget.
This refutes only a comparison of upper bounds, not the sealed r2 leaf or a paper statement.
Source: derived route test for the omission on P0029 page 4. -/
theorem sqrt_budget_not_polylog384 :
    ¬ ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      4 * Real.sqrt N * (Real.log N) ^ 2 ≤ C * (Real.log N) ^ 3 := by
  rintro ⟨C, N₀, h⟩
  have hsmall : (fun N : ℕ => C * Real.log (N : ℝ)) =o[atTop]
      (fun N : ℕ => Real.sqrt N) := by
    simpa only [Real.sqrt_eq_rpow] using
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).natCast_atTop).const_mul_left C
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hsmall.bound (by norm_num : (0 : ℝ) < 2))
  let N := max N₀ (max M 2)
  have hN₀ : N₀ ≤ N := le_max_left _ _
  have hMN : M ≤ N := (le_max_left M 2).trans (le_max_right _ _)
  have hN2 : 2 ≤ N := (le_max_right M 2).trans (le_max_right _ _)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < N by omega))
  have hb : (4 * Real.sqrt (N : ℝ)) * (Real.log N) ^ 2 ≤
      (C * Real.log N) * (Real.log N) ^ 2 := by nlinarith [h N hN₀]
  have hc := (mul_le_mul_iff_left₀ (sq_pos_of_pos hlog)).mp hb
  have hnorm := hM N hMN
  rw [Real.norm_of_nonneg hsqrt.le] at hnorm
  have hC : C * Real.log (N : ℝ) ≤ 2 * Real.sqrt N :=
    (le_abs_self _).trans hnorm
  linarith

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.r2_sub_primeR2_isBigO384
#print axioms LeanLab.BhowmikGrimmelt2026.sqrt_mul_log_sq_isLittleO384
#print axioms LeanLab.BhowmikGrimmelt2026.r2_sub_primeR2_isLittleO384

#print axioms LeanLab.BhowmikGrimmelt2026.normalized_prime_power_error384
#print axioms LeanLab.BhowmikGrimmelt2026.normalized_prime_count_limit_iff384

#print axioms LeanLab.BhowmikGrimmelt2026.prime_power_error_sqrt_log384

#print axioms LeanLab.BhowmikGrimmelt2026.sqrt_budget_not_polylog384
