import Mathlib

/-!
# The theta input for modulus twelve

AI wrote the Lean code. Goldbach is open.
Source: Ramaré and Rumely, Primes in arithmetic progressions, Math. Comp. 65, 1996,
https://doi.org/10.1090/S0025-5718-96-00669-2
Theorems 1 and 2, page 398. Table 1, page 419, row 12, has epsilon 0.002781
at x0 = 10^10. Table 2, page 422, row 12, has theta constant 1.735502.
Both constants were checked on the printed page images.
The named input below is only the lower half of these published theta bounds.
It is a hypothesis, not an axiom or a proved analytic result.
-/

noncomputable section
namespace LeanLab.AlmostPrimes.AP12Theta

open Finset Real MeasureTheory

/-- The sum of log p over primes p at most x in the class a modulo twelve. -/
def theta12 (a : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ Icc 0 ⌊x⌋₊, if p.Prime ∧ p % 12 = a % 12 then log p else 0

/-- The number of primes at most x in the class a modulo twelve. -/
def count12 (a : ℕ) (x : ℝ) : ℝ :=
  (((Icc 0 ⌊x⌋₊).filter (fun p => p.Prime ∧ p % 12 = a % 12)).card : ℝ)

/-- CONDITIONAL input. Ramaré and Rumely 1996 Theorems 1 and 2 with Tables 1 and 2,
restricted to modulus twelve and to their lower bounds. The denominator four is phi of twelve.
The small range starts at one, as in Theorem 2. -/
def RR12ThetaLower : Prop :=
  (∀ a : ℕ, Nat.Coprime a 12 → ∀ x : ℝ, 1 ≤ x → x ≤ 10 ^ 10 →
    x / 4 - 1.735502 * sqrt x ≤ theta12 a x) ∧
  (∀ a : ℕ, Nat.Coprime a 12 → ∀ x : ℝ, 10 ^ 10 ≤ x →
    (1 - 0.002781) * x / 4 ≤ theta12 a x)

/-- The theta sum is nonnegative. -/
lemma theta12_nonneg (a : ℕ) (x : ℝ) : 0 ≤ theta12 a x := by
  apply sum_nonneg
  intro p hp
  split_ifs with h
  · exact log_nonneg (by exact_mod_cast h.1.one_lt.le)
  · exact le_rfl

/-- Abel summation for primes in one class modulo twelve. This is a finite identity. -/
theorem count12_eq_theta_div_log_add_integral (a : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    count12 a x = theta12 a x / log x +
      ∫ t in 2..x, theta12 a t / (t * log t ^ 2) := by
  let c : ℕ → ℝ := fun n => if n.Prime ∧ n % 12 = a % 12 then log n else 0
  have hc0 : c 0 = 0 := by simp [c]
  have hc1 : c 1 = 0 := by simp [c]
  have hs : count12 a x = ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * c n := by
    simp only [count12, card_eq_sum_ones, sum_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]
    apply sum_congr rfl
    intro n hn
    by_cases h : n.Prime ∧ n % 12 = a % 12
    · have hnlog : log (n : ℝ) ≠ 0 :=
        log_ne_zero_of_pos_of_ne_one (by exact_mod_cast h.1.pos)
          (by exact_mod_cast h.1.ne_one)
      simp [c, h, hnlog]
    · simp [c, h]
  rw [hs, sum_mul_eq_sub_integral_mul₁ c (f := fun t : ℝ => (log t)⁻¹) hc0 hc1]
  · rw [← intervalIntegral.integral_of_le hx]
    have hi : (∫ u in 2..x, deriv (fun t : ℝ => (log t)⁻¹) u *
        ∑ n ∈ Icc 0 ⌊u⌋₊, c n) =
        -(∫ u in 2..x, theta12 a u / (u * log u ^ 2)) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro u hu
      simp [theta12, c, field]
    rw [hi]
    simp [theta12, c, div_eq_mul_inv, mul_comm]
  · intro z hz
    have : z ≠ 0 := by linarith [hz.1]
    have : log z ≠ 0 := log_ne_zero_of_pos_of_ne_one (by linarith [hz.1])
      (by linarith [hz.1])
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun z hz => ContinuousWithinAt.congr ?_
      (fun _ _ => deriv_inv_log_apply) deriv_inv_log_apply
    have : z ≠ 0 := by linarith [hz.1]
    have : log z ^ 2 ≠ 0 := pow_ne_zero 2
      (log_ne_zero_of_pos_of_ne_one (by linarith [hz.1]) (by linarith [hz.1]))
    exact ContinuousAt.continuousWithinAt (by fun_prop)

/-- The remainder in Abel summation is nonnegative. -/
lemma theta12_div_log_le_count12 (a : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    theta12 a x / log x ≤ count12 a x := by
  rw [count12_eq_theta_div_log_add_integral a hx]
  have hi : 0 ≤ ∫ t in 2..x, theta12 a t / (t * log t ^ 2) := by
    apply intervalIntegral.integral_nonneg hx
    intro t ht
    exact div_nonneg (theta12_nonneg a t) (mul_nonneg (by linarith [ht.1]) (sq_nonneg _))
  linarith

/-- The exact printed constants give a uniform theta lower bound from one billion.
CONDITIONAL ON RR12ThetaLower. -/
theorem theta12_lower_from_1e9 (h : RR12ThetaLower) (a : ℕ) (ha : Nat.Coprime a 12)
    {x : ℝ} (hx : 10 ^ 9 ≤ x) : 0.249 * x ≤ theta12 a x := by
  by_cases h10 : x ≤ 10 ^ 10
  · have hs := h.1 a ha x (by linarith) h10
    have hx0 : 0 ≤ x := by linarith
    have hsq : sqrt x ^ 2 = x := sq_sqrt hx0
    have hroot : 30000 ≤ sqrt x := by
      have := sqrt_nonneg x
      nlinarith
    have herr : 1.735502 * sqrt x ≤ 0.001 * x := by nlinarith
    linarith
  · have hs := h.2 a ha x (le_of_not_ge h10)
    have hx0 : 0 ≤ x := by linarith
    nlinarith

/-- One published theta input implies the requested prime count lower bound.
CONDITIONAL ON RR12ThetaLower. -/
theorem count12_lower_from_1e9 (h : RR12ThetaLower) (a : ℕ) (ha : Nat.Coprime a 12)
    {x : ℝ} (hx : 10 ^ 9 ≤ x) : 0.21 * x / log x < count12 a x := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < log x := log_pos (by linarith)
  have ht := theta12_lower_from_1e9 h a ha hx
  have hc := theta12_div_log_le_count12 a (by linarith : 2 ≤ x)
  have hstrict : 0.21 * x < theta12 a x := by nlinarith
  exact lt_of_lt_of_le ((div_lt_div_iff_of_pos_right hlog).mpr hstrict) hc

/-- A concrete instance of the small range lower bound at x = one. -/
lemma rr_small_at_one : (1 : ℝ) / 4 - 1.735502 * sqrt 1 ≤ theta12 1 1 := by
  have := theta12_nonneg 1 1
  norm_num at *
  linarith

/-- The arithmetic hypotheses at the first required point are inhabited. -/
lemma threshold_instance : Nat.Coprime 1 12 ∧
    (10 ^ 9 : ℝ) ≤ 1000000000 ∧ 0 < log (1000000000 : ℝ) := by
  refine ⟨by decide, by norm_num, log_pos (by norm_num)⟩

end LeanLab.AlmostPrimes.AP12Theta

#print axioms LeanLab.AlmostPrimes.AP12Theta.theta12_nonneg
#print axioms LeanLab.AlmostPrimes.AP12Theta.count12_eq_theta_div_log_add_integral
#print axioms LeanLab.AlmostPrimes.AP12Theta.theta12_div_log_le_count12
#print axioms LeanLab.AlmostPrimes.AP12Theta.theta12_lower_from_1e9
#print axioms LeanLab.AlmostPrimes.AP12Theta.count12_lower_from_1e9

#print axioms LeanLab.AlmostPrimes.AP12Theta.rr_small_at_one
#print axioms LeanLab.AlmostPrimes.AP12Theta.threshold_instance
