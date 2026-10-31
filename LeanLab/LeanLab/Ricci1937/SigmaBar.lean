import LeanLab.Ricci1937.BetaBar
import LeanLab.Ricci1937.Section2

/-!
Ricci 1937, page 81, the positive lower sieve constant in formula 2.6.
The infinite tail is bounded in BetaBar. No sieve estimate is assumed.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
open Real Finset
noncomputable section

/-- Sigma bar at the printed lower sieve parameters, including its infinite series. -/
def ricciSigmaBarLower : ℝ :=
  exp (0.90 + 0.56 + 0.52) *
    ((Ebar3 (90 / 100) (56 / 100) (52 / 100) : ℝ) -
      (0.90 * 0.56 ^ (2 : ℕ) * 0.52 ^ (2 : ℕ) /
        (0.50 ^ (5 : ℕ) * exp (3 * 0.50))) *
      ∑' k : ℕ, ricciBetaBarTerm (exp (0.5 : ℝ) / 4) (4 + k))

/-- Formula 2.6, with the series now proved and no cited numerical input. -/
theorem ricciSigmaBarLower_gt : (0.00066 : ℝ) < ricciSigmaBarLower := by
  let E : ℝ := (Ebar3 (90 / 100) (56 / 100) (52 / 100) : ℝ)
  let K : ℝ := 0.90 * 0.56 ^ (2 : ℕ) * 0.52 ^ (2 : ℕ) /
    (0.50 ^ (5 : ℕ) * exp (3 * 0.50))
  let T : ℝ := ∑' k : ℕ, ricciBetaBarTerm (exp (0.5 : ℝ) / 4) (4 + k)
  have hE : (0.0122847 : ℝ) < E := by
    norm_num [E, Ebar3]
  have hT : T < (0.02185 : ℝ) := ricciBetaBar_lowerParameters_lt
  have he15 : (4.41 : ℝ) ≤ exp 1.5 := ricci_exp_lower (by norm_num)
    (by norm_num [sum_range_succ, Nat.factorial])
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hK : K ≤ (0.555 : ℝ) := by
    dsimp [K]
    rw [div_le_iff₀ (by positivity)]
    norm_num
    linarith
  have hKT : K * T ≤ (0.555 : ℝ) * 0.02185 :=
    (mul_le_mul_of_nonneg_left hT.le hK0).trans
      (mul_le_mul_of_nonneg_right hK (by norm_num))
  have hcore : (0.0001 : ℝ) ≤ E - K * T := by linarith
  have he198 : (7 : ℝ) ≤ exp 1.98 := ricci_exp_lower (by norm_num)
    (by norm_num [sum_range_succ, Nat.factorial])
  have hmul := mul_le_mul he198 hcore (by norm_num : (0 : ℝ) ≤ 0.0001) (exp_pos _).le
  change (0.00066 : ℝ) < exp (0.90 + 0.56 + 0.52) * (E - K * T)
  rw [show (0.90 + 0.56 + 0.52 : ℝ) = 1.98 by norm_num]
  linarith

end
end LeanLab.Ricci1937
