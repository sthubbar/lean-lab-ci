/-
P0059 Section 3.1, repeated integration by parts for the polynomial weight.
This supports the higher derivative norm in arXiv page 9 equation 3.2.
AI wrote this Lean code, CODEX task64, 2026-10-25.
-/
import LeanLab.KadiriLumley2014.WeightMass

namespace LeanLab.KadiriLumley2014.Task64
open Real Set MeasureTheory intervalIntegral Polynomial

/-- Analytic and polynomial iterated derivatives agree. -/
theorem iteratedDeriv_eval (p : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => p.eval t) =
      fun t => (Polynomial.derivative^[n] p).eval t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [Function.iterate_succ_apply']
    exact (Polynomial.hasDerivAt _ t).deriv

/-- Iterated integration by parts when the first polynomial and all required
lower derivatives vanish at zero and one. -/
theorem polynomial_parts (n : ℕ) (p q : ℝ[X])
    (hzero : ∀ k < n, (Polynomial.derivative^[k] p).eval 0 = 0)
    (hone : ∀ k < n, (Polynomial.derivative^[k] p).eval 1 = 0) :
    (∫ t in (0 : ℝ)..1, (Polynomial.derivative^[n] p).eval t * q.eval t) =
      (-1 : ℝ) ^ n * (∫ t in (0 : ℝ)..1, p.eval t * (Polynomial.derivative^[n] q).eval t) := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
    have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      q.continuous.continuousOn (Polynomial.continuous (Polynomial.derivative^[n] p)).continuousOn
      (fun t _ => q.hasDerivAt t)
      (fun t _ => (Polynomial.derivative^[n] p).hasDerivAt t)
      (q.derivative.continuous.intervalIntegrable 0 1)
      ((Polynomial.derivative (Polynomial.derivative^[n] p)).continuous.intervalIntegrable 0 1)
    have hparts' :
        (∫ t in (0 : ℝ)..1, (Polynomial.derivative^[n + 1] p).eval t * q.eval t) =
          -(∫ t in (0 : ℝ)..1, (Polynomial.derivative^[n] p).eval t * q.derivative.eval t) := by
      simpa only [Function.iterate_succ_apply', hone n (by omega), hzero n (by omega),
        mul_zero, zero_mul, sub_self, zero_sub, mul_comm] using hparts
    rw [hparts', ih q.derivative (fun k hk => hzero k (by omega))
      (fun k hk => hone k (by omega)), Function.iterate_succ_apply, pow_succ]
    ring

/-- The unscaled polynomial on the integration interval. -/
noncomputable def unitWeightPoly (m : ℕ) : ℝ[X] :=
  X ^ m * (1 - X) ^ m

/-- All derivatives below m vanish at the left endpoint. -/
theorem unitWeightPoly_zero {m k : ℕ} (hk : k < m) :
    (Polynomial.derivative^[k] (unitWeightPoly m)).eval 0 = 0 := by
  have hd : (X : ℝ[X]) ^ m ∣ unitWeightPoly m := by
    exact dvd_mul_right _ _
  have hd' := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd k hd
  obtain ⟨p, hp⟩ := hd'
  rw [hp]
  simp [ne_of_gt (Nat.sub_pos_of_lt hk)]

/-- All derivatives below m vanish at the right endpoint. -/
theorem unitWeightPoly_one {m k : ℕ} (hk : k < m) :
    (Polynomial.derivative^[k] (unitWeightPoly m)).eval 1 = 0 := by
  have hd : (1 - (X : ℝ[X])) ^ m ∣ unitWeightPoly m := by
    exact dvd_mul_left _ _
  have hd' := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd k hd
  obtain ⟨p, hp⟩ := hd'
  rw [hp]
  simp [ne_of_gt (Nat.sub_pos_of_lt hk)]

end LeanLab.KadiriLumley2014.Task64
