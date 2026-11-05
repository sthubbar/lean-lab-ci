/-
P0028 https://arxiv.org/abs/1610.02017v2, pages 11 and 12, equation 5.1.
Make the sieve majorant explicit before leaving its Fourier estimate OPEN.
At n zero the finite extension is set by the displayed finite sums.
Only positive n occur in the paper comparison.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSTransference

namespace LeanLab.Ternary.MMS.Task361
open Finset

/-- The rough number indicator from P0028 page 11, before equation 5.1. -/
noncomputable def roughIndicator (n : ℕ) (y : ℝ) : ℝ := by
  classical
  exact if ∀ p : ℕ, p.Prime → (p : ℝ) < y → ¬ p ∣ n then 1 else 0

/-- The explicit Harman sieve majorant in P0028 page 11, equation 5.1.
Each ordered prime triple determines its remaining factor by division.
The finite bounds cover every such factorization when n is positive. -/
noncomputable def harmanMajorant (x : ℝ) (n : ℕ) : ℝ := by
  classical
  exact roughIndicator n (x ^ (1 / 4 : ℝ)) +
    ∑ p₁ ∈ range (n + 1), ∑ p₂ ∈ range (n + 1), ∑ p₃ ∈ range (n + 1),
      if p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ x ^ (1 / 10 : ℝ) < p₁ ∧
          p₁ < p₂ ∧ p₂ < p₃ ∧ (p₃ : ℝ) < x ^ (1 / 4 : ℝ) ∧ p₁ * p₂ * p₃ ∣ n then
        roughIndicator (n / (p₁ * p₂ * p₃)) p₁ else 0

/-- The rough number indicator is nonnegative. Directly from its paper definition. -/
theorem roughIndicator_nonneg (n : ℕ) (y : ℝ) : 0 ≤ roughIndicator n y := by
  classical
  unfold roughIndicator
  split_ifs <;> norm_num

/-- A prime at least y has no prime divisor below y.
P0028 page 11, the majorization behind equation 5.1. -/
theorem roughIndicator_prime {n : ℕ} (hn : n.Prime) {y : ℝ} (hy : y ≤ n) :
    roughIndicator n y = 1 := by
  classical
  unfold roughIndicator
  rw [if_pos]
  intro p hp hpy hpn
  rcases (Nat.dvd_prime hn).mp hpn with hp1 | hpeq
  · exact hp.ne_one hp1
  · subst p
    linarith

/-- The correction terms in equation 5.1 are nonnegative. -/
theorem harmanMajorant_nonneg (x : ℝ) (n : ℕ) : 0 ≤ harmanMajorant x n := by
  classical
  unfold harmanMajorant
  apply add_nonneg (roughIndicator_nonneg _ _)
  apply sum_nonneg
  intro p₁ hp₁
  apply sum_nonneg
  intro p₂ hp₂
  apply sum_nonneg
  intro p₃ hp₃
  split_ifs
  · exact roughIndicator_nonneg _ _
  · exact le_rfl

/-- The explicit sieve majorant dominates the prime indicator above its roughness cutoff.
P0028 page 11, equation 5.1. -/
theorem primeIndicator_le_harmanMajorant {x : ℝ} {n : ℕ}
    (hcut : x ^ (1 / 4 : ℝ) ≤ n) : ρ n ≤ harmanMajorant x n := by
  classical
  by_cases hn : n.Prime
  · unfold harmanMajorant
    rw [roughIndicator_prime hn hcut]
    have hsum : 0 ≤ ∑ p₁ ∈ range (n + 1), ∑ p₂ ∈ range (n + 1), ∑ p₃ ∈ range (n + 1),
        if p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ x ^ (1 / 10 : ℝ) < p₁ ∧
          p₁ < p₂ ∧ p₂ < p₃ ∧ (p₃ : ℝ) < x ^ (1 / 4 : ℝ) ∧ p₁ * p₂ * p₃ ∣ n then
          roughIndicator (n / (p₁ * p₂ * p₃)) p₁ else 0 := by
      apply sum_nonneg
      intro p₁ hp₁
      apply sum_nonneg
      intro p₂ hp₂
      apply sum_nonneg
      intro p₃ hp₃
      split_ifs
      · exact roughIndicator_nonneg _ _
      · exact le_rfl
    simpa [ρ, hn] using hsum
  · simpa [ρ, hn] using harmanMajorant_nonneg x n

/-- The whole Theorem 2.1 interval lies above the roughness cutoff once x is at least 16.
Derived interval arithmetic for P0028 pages 3 and 11. -/
theorem interval_above_rough_cutoff {x θ : ℝ} (hx : 16 ≤ x) (hθ : θ ≤ 1) :
    x ^ (1 / 4 : ℝ) ≤ x - x ^ θ / 3 := by
  have hxpos : 0 < x := by linarith
  have hroot : (x ^ (1 / 4 : ℝ)) ^ (4 : ℕ) = x := by
    rw [← Real.rpow_mul_natCast hxpos.le]
    norm_num
  have hpow : (16 : ℝ) ^ (3 : ℕ) ≤ x ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) hx _
  have hfour : x ≤ (x / 2) ^ (4 : ℕ) := by nlinarith [mul_nonneg hxpos.le (sub_nonneg.mpr hpow)]
  have hhalf : x ^ (1 / 4 : ℝ) ≤ x / 2 :=
    le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) (by rwa [hroot])
  have htheta : x ^ θ ≤ x := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x) hθ
  linarith

/-- LEAF. The Fourier estimate for the explicit majorant has a fixed mean below 2.9.
P0028 page 11 Proposition 5.1 and page 12 unsmoothing and Buchstab mean displays.
This leaf contains no prime representation or progression lower bound. -/
theorem harman_fourier_input (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) :
    ∃ αp : ℝ, 0 < αp ∧ αp < 2.9 ∧
      ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        Hyp1 θ x αp η (harmanMajorant x) := by sorry

end LeanLab.Ternary.MMS.Task361
