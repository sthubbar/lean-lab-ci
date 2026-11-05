/-
P0028 https://arxiv.org/abs/1610.02017v2, page 3, Theorem 2.1.
Elementary consequences of the two distinct prime distribution inputs.
Each implication is CONDITIONAL ON its explicit Hyp1 or Hyp2 assumption.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSTransference

namespace LeanLab.Ternary.MMS.Task361
open Finset

/-- At frequency zero Hyp1 is a real mean estimate for the sieve majorant.
P0028 page 3, Theorem 2.1 condition 1 at gamma zero.
CONDITIONAL ON Hyp1. -/
theorem hyp1_zero_frequency {θ x αp η : ℝ} {ρp : ℕ → ℝ}
    (H : Hyp1 θ x αp η ρp) (c : ℕ) (hc : Nat.Coprime c (wheel x)) :
    |(∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter
          (fun n => n ≡ c [MOD wheel x]), ρp n) -
      (αp / Real.log x * (wheel x / (wheel x).totient)) *
        ((ints (x - x ^ θ / 3) (x + x ^ θ)).filter
          (fun n => n ≡ c [MOD wheel x])).card| ≤
      η * x ^ θ / ((wheel x).totient * Real.log x) := by
  have h := H c hc 0
  simp only [e, mul_zero, Complex.ofReal_zero, Complex.exp_zero, mul_one, Finset.sum_const, nsmul_eq_mul] at h
  rw [← Complex.ofReal_natCast] at h
  simpa only [← Complex.ofReal_sum, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using h

/-- Prime majorization turns the mean Fourier estimate into a prime count upper bound.
P0028 page 3, Theorem 2.1 condition 1 and the majorization premise.
CONDITIONAL ON Hyp1 and the supplied majorant. -/
theorem hyp1_prime_count_upper {θ x αp η : ℝ} {ρp : ℕ → ℝ}
    (H : Hyp1 θ x αp η ρp)
    (hρ : ∀ n ∈ ints (x - x ^ θ / 3) (x + x ^ θ), ρ n ≤ ρp n)
    (c : ℕ) (hc : Nat.Coprime c (wheel x)) :
    (∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter
        (fun n => n ≡ c [MOD wheel x]), ρ n) ≤
      (αp / Real.log x * (wheel x / (wheel x).totient)) *
        ((ints (x - x ^ θ / 3) (x + x ^ θ)).filter
          (fun n => n ≡ c [MOD wheel x])).card +
      η * x ^ θ / ((wheel x).totient * Real.log x) := by
  have hmean := (abs_le.mp (hyp1_zero_frequency H c hc)).2
  have hsum : (∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter
        (fun n => n ≡ c [MOD wheel x]), ρ n) ≤
      ∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter
        (fun n => n ≡ c [MOD wheel x]), ρp n :=
    sum_le_sum fun n hn => hρ n (mem_filter.mp hn).1
  linarith

/-- The full interval meets the length condition in Hyp2.
P0028 page 3, Theorem 2.1 condition 2, derived interval arithmetic. -/
theorem hyp2_full_interval_length {θ ε x : ℝ} (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    x ^ (θ - ε) ≤ (x + x ^ θ) - (x - x ^ θ / 3) := by
  have hpow := Real.rpow_le_rpow_of_exponent_le hx (by linarith : θ - ε ≤ θ)
  have hp : 0 ≤ x ^ θ := Real.rpow_nonneg (by linarith) _
  linarith

/-- Hyp2 with modulus one lower bounds the prime count in the full interval.
P0028 page 3, Theorem 2.1 condition 2 at d one.
CONDITIONAL ON Hyp2. -/
theorem hyp2_full_prime_count {θ ε x αm : ℝ} (hx : 1 ≤ x) (hε : 0 ≤ ε)
    (hlog : 1 ≤ Real.log x) (H : Hyp2 θ ε x αm) :
    αm * (4 * x ^ θ / 3) / Real.log x ≤
      ∑ n ∈ ints (x - x ^ θ / 3) (x + x ^ θ), ρ n := by
  have h := H (x - x ^ θ / 3) (x + x ^ θ) le_rfl le_rfl
    (hyp2_full_interval_length hx hε) 1 1 (by norm_num) (by simpa using hlog) (by norm_num)
  have hwidth : (x + x ^ θ) - (x - x ^ θ / 3) = 4 * x ^ θ / 3 := by ring
  simpa [Nat.ModEq, Nat.mod_one, hwidth] using h

end LeanLab.Ternary.MMS.Task361
