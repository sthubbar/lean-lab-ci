import LeanLab.HardyLittlewood1923.Decomp354d

/-!
AI wrote this Lean code for CODEX task354.
P0004 page 5 equation 1.31 and page 23 equation 3.121.
These bounds witness the finite transfer hypotheses.
They do not supply the asymptotic uniform error estimate.
Goldbach is OPEN.
-/

namespace LeanLab.HardyLittlewood1923.Decomp354j

open Real
open LeanLab.HardyLittlewood1923.Decomp276b

/-- P0004 page 5 equation 1.31.
Absolute convergence bounds the prime series by the absolute coefficient sum at the same real part. -/
theorem primeSeries_norm_le {z : ℂ} (hz : 0 < z.re) :
    ‖primeSeries z‖ ≤ ∑' m : ℕ,
      ‖if m.Prime then (Real.log m : ℂ) * Complex.exp (-(m : ℂ) * (z.re : ℂ)) else 0‖ := by
  have hs := (primeSeries_summable hz).norm
  calc
    _ ≤ ∑' m : ℕ, ‖if m.Prime then (Real.log m : ℂ) * Complex.exp (-(m : ℂ) * z) else 0‖ :=
      norm_tsum_le_tsum_norm hs
    _ = _ := by
      apply tsum_congr
      intro m
      by_cases hm : m.Prime
      · simp [hm, norm_mul, Complex.norm_exp]
      · simp [hm]

/-- P0004 page 23 before equation 3.121.
For positive n and q the rational model has norm at most n. -/
theorem localPhi_norm_le {n q : ℕ} (hn : 0 < n) (hq : 1 ≤ q) (θ : ℝ) :
    ‖localPhi n q θ‖ ≤ n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hphi : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hphi1 : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast (show 1 ≤ q.totient by have := Nat.totient_pos.mpr (by omega : 0 < q); omega)
  have hmu : ‖(ArithmeticFunction.moebius q : ℂ)‖ ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := q)
  have hc : ‖(ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)‖ ≤ 1 := by
    rw [norm_div]
    simp only [Complex.norm_natCast]
    exact (div_le_one hphi).mpr (hmu.trans hphi1)
  have hy := LeanLab.HardyLittlewood1923.Decomp354d.localY_norm_lower hn θ
  have hy0 : 0 < ‖localY n θ‖ := lt_of_lt_of_le (by positivity) hy
  have hi : 1 / ‖localY n θ‖ ≤ n := by
    have := one_div_le_one_div_of_le (by positivity : 0 < 1 / (n : ℝ)) hy
    simpa using this
  rw [localPhi, norm_div, div_eq_mul_inv]
  calc
    _ ≤ 1 * (n : ℝ) := mul_le_mul hc (by simpa only [one_div] using hi) (by positivity) (by norm_num)
    _ = _ := one_mul _

/-- P0004 pages 5 and 23 equations 1.31 and 3.121.
For each positive n there is a finite nonnegative uniform error bound on all rational angles.
This witnesses the finite coefficient transfer premise without asserting the required asymptotic rate. -/
theorem localError_bounded {n : ℕ} (hn : 0 < n) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ q : ℕ, 1 ≤ q → ∀ p : ℕ, ∀ θ : ℝ,
      ‖localError n p q θ‖ ≤ E := by
  let B : ℝ := ∑' m : ℕ,
    ‖if m.Prime then (Real.log m : ℂ) * Complex.exp (-(m : ℂ) * (1 / (n : ℂ))) else 0‖
  have hB : 0 ≤ B := tsum_nonneg (fun m => norm_nonneg _)
  refine ⟨B + n, by positivity, fun q hq p θ => ?_⟩
  have hz : 0 < (localY n (2 * π * (p : ℝ) / q + θ)).re := by rw [localY_re]; positivity
  have hp := primeSeries_norm_le hz
  have hp' : ‖primeSeries (localY n (2 * π * (p : ℝ) / q + θ))‖ ≤ B := by
    simpa only [localY_re, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast] using hp
  calc
    _ ≤ ‖primeSeries (localY n (2 * π * (p : ℝ) / q + θ))‖ + ‖localPhi n q θ‖ := norm_sub_le _ _
    _ ≤ B + n := add_le_add hp' (localPhi_norm_le hn hq θ)

#print axioms primeSeries_norm_le
#print axioms localPhi_norm_le
#print axioms localError_bounded

end LeanLab.HardyLittlewood1923.Decomp354j
