import LeanLab.LanguascoPerelli1996.Statements

/-!
P0071 Section 5, page 360 display 25. This is a cited analytic input.
The published argument extends reference 11, Languasco and Perelli 1994.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Section5108
open Real ArithmeticFunction

/-- Page 360 display 25. The damped character exponential sum.
The n equals zero term vanishes by the definition of the von Mangoldt function. -/
noncomputable def dampedSum (N η : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑' n : ℕ, (Λ n : ℂ) * χ (n : ZMod q) * (Real.exp (-(n : ℝ) / N) : ℂ) * e (n * η)

/-- Page 360 display 25. The damped sum converges absolutely for positive N,
so its tsum does not use the value assigned to a divergent series. -/
theorem dampedSum_summable {N : ℝ} (hN : 0 < N) (η : ℝ)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Summable (fun n : ℕ => (Λ n : ℂ) * χ (n : ZMod q) *
      (Real.exp (-(n : ℝ) / N) : ℂ) * e (n * η)) := by
  have hr : ‖Real.exp (-1 / N)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hn : -1 / N < (0 : ℝ) := div_neg_of_neg_of_pos (by norm_num) hN
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hn
  have hs : Summable (fun n : ℕ => (n : ℝ) * Real.exp (-1 / N) ^ n) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have he (x : ℝ) : ‖e x‖ = 1 := by
    unfold e
    rw [Complex.norm_exp]
    simp
  apply hs.of_norm_bounded
  intro n
  rw [norm_mul, norm_mul, norm_mul, he, mul_one]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (vonMangoldt_nonneg (n := n)), abs_of_pos (Real.exp_pos _)]
  have hχ : ‖χ (n : ZMod q)‖ ≤ 1 := χ.norm_le_one _
  have hLambda : Λ n ≤ (n : ℝ) := vonMangoldt_le_log.trans (Real.log_le_self (Nat.cast_nonneg n))
  calc
    Λ n * ‖χ (n : ZMod q)‖ * Real.exp (-(n : ℝ) / N) ≤
        Λ n * Real.exp (-(n : ℝ) / N) := by
      have hh := mul_le_mul_of_nonneg_left hχ (vonMangoldt_nonneg (n := n))
      exact mul_le_mul_of_nonneg_right (by simpa only [mul_one] using hh) (Real.exp_pos _).le
    _ ≤ (n : ℝ) * Real.exp (-(n : ℝ) / N) :=
      mul_le_mul_of_nonneg_right hLambda (Real.exp_pos _).le
    _ = (n : ℝ) * Real.exp (-1 / N) ^ n := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring

/-- Page 359, the parameter z used in display 25. -/
noncomputable def laplaceParameter (N η : ℝ) : ℂ :=
  ((N⁻¹ : ℝ) : ℂ) - 2 * Real.pi * Complex.I * η

/-- CITED. Page 360 display 25. Under GRH the character mean square is
bounded by an absolute constant times N log squared N divided by q Q,
uniformly for all characters modulo q with q at most Q at most N. -/
def Estimate25 : Prop :=
  GRH → ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℝ, 2 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
    ∀ Q : ℝ, 1 ≤ Q → Q ≤ N → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Q →
      ∀ χ : DirichletCharacter ℂ q,
        (∫ η in (-(1 / ((q : ℝ) * Q)))..(1 / ((q : ℝ) * Q)),
          ‖dampedSum N η χ - (if χ = 1 then (1 : ℂ) else 0) / laplaceParameter N η‖ ^ 2) ≤
            C * N * Real.log N ^ 2 / ((q : ℝ) * Q)

/-- Page 359. The real part of z is positive, so its reciprocal is well defined. -/
theorem laplaceParameter_ne_zero {N : ℝ} (hN : 0 < N) (η : ℝ) :
    laplaceParameter N η ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hz
  have hp : 0 < N⁻¹ := inv_pos.mpr hN
  simp [laplaceParameter] at hr
  exact hN.ne' hr

end LeanLab.LanguascoPerelli1996.Section5108
