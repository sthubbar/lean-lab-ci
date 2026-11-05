import LeanLab.LiuWang2002.Decomp345a
import LeanLab.LiuWang2002.Decomp345c
import LeanLab.LiuWang2002.PrimePower345

/-!
Task345. Two components of the psi estimate used on Liu and Wang page 169.
Schoenfeld 1976 gives the stronger coefficient 1.001093 on page 356.
The source is https://doi.org/10.1090/S0025-5718-1976-0457374-X.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.LiuWang2002.Task345

open Real Finset ArithmeticFunction
open scoped ArithmeticFunction

/-- Schoenfeld 1976, page 356, Theorem 6 star, display 5.1 star.
CONDITIONAL ON the three ranges in Decomp345c.
The prime contribution theta X is less than 1.001093 X for positive X.
This bounds only the primes, not the full Mangoldt sum in psi_bound.
The written proof occupies page 356 and uses the table in that paper
and Rosser and Schoenfeld 1962, display 4.5. -/
theorem theta_upper (X : ℝ) (hX : 0 < X) :
    Chebyshev.theta X < 1.001093 * X := by
  exact theta_upper_from_regions X hX

/-- Schoenfeld 1976, page 356, Theorem 6 star, display 5.3 star.
CONDITIONAL ON the theta estimate assembled from the three source ranges.
The contribution of proper prime powers is less than
1.001093 times square root X plus 3 times cube root X.
This contains no contribution from primes themselves.
The source reduces this display to its theta estimates as in Section 5
of Rosser and Schoenfeld 1975. PrimePower345 proves this reduction using
Mathlib and a compressed certificate for the entire initial range. -/
theorem prime_power_upper (X : ℝ) (hX : 0 < X) :
    Chebyshev.psi X - Chebyshev.theta X <
      1.001093 * √X + 3 * X ^ (1 / 3 : ℝ) := by
  exact prime_power_of_theta theta_upper X hX

/-- Arithmetic assembly of the two components of the display in Lemma 6.2,
Liu and Wang page 169, using the stronger displays on Schoenfeld page 356.
CONDITIONAL ON the two explicitly supplied component estimates. -/
theorem psi_bound_of_components (X : ℝ) (hX : 0 ≤ X)
    (hTheta : Chebyshev.theta X ≤ 1.001093 * X)
    (hPower : Chebyshev.psi X - Chebyshev.theta X ≤
      1.001093 * √X + 3 * X ^ (1 / 3 : ℝ)) :
    (∑ n ∈ Finset.range (Nat.floor X + 1), Λ n) ≤
      1.001102 * (X + X ^ (1 / 2 : ℝ)) + 3 * X ^ (1 / 3 : ℝ) := by
  rw [← psi_eq_sum_range]
  have hs := Real.sqrt_nonneg X
  rw [Real.sqrt_eq_rpow] at hPower hs
  nlinarith

/-- The exact statement of Decomp109b.psi_bound on Liu and Wang page 169.
CONDITIONAL ON theta_upper and prime_power_upper from Schoenfeld 1976.
The final arithmetic weakens their coefficient to the printed 1.001102. -/
theorem psi_bound (X : ℝ) (hX : exp 9.634 ≤ X) :
    (∑ n ∈ Finset.range (Nat.floor X + 1), Λ n) ≤
      1.001102 * (X + X ^ (1 / 2 : ℝ)) + 3 * X ^ (1 / 3 : ℝ) := by
  have hXp : 0 < X := (exp_pos _).trans_le hX
  exact psi_bound_of_components X hXp.le (theta_upper X hXp).le
    (prime_power_upper X hXp).le

/-- The exact statement of U1543.lemma62_S1 on Liu and Wang page 169.
CONDITIONAL ON theta_upper and prime_power_upper. All other steps reuse
proved lemmas. The existing lemma62_S1 and psi_bound are not used. -/
theorem lemma62_S1 (c : ℝ) (N : ℕ) (hL : 3100 ≤ Real.log N) (α : ℝ) :
    ‖U1543.Ssum (U1543.lam1 (U1543.Uf N)) c N α‖ ≤ 1.02 * U1543.Uf N := by
  apply lemma62_S1_of_psi c N hL α
  rw [psi_eq_sum_range]
  have hNp := (U1543.task141_logs N hL).1
  have hNlarge : exp 30.95 ≤ (N : ℝ) :=
    (le_log_iff_exp_le hNp).mp (by linarith)
  have hU : exp 9.634 ≤ U1543.Uf N := by
    simpa only [Vaughan109.U, U1543.Uf, neg_div] using Decomp109b.U_lower (N : ℝ) hNlarge
  exact psi_bound (U1543.Uf N) hU

end LeanLab.LiuWang2002.Task345

#print axioms LeanLab.LiuWang2002.Task345.theta_upper
#print axioms LeanLab.LiuWang2002.Task345.prime_power_upper
#print axioms LeanLab.LiuWang2002.Task345.psi_bound_of_components
#print axioms LeanLab.LiuWang2002.Task345.psi_bound

#print axioms LeanLab.LiuWang2002.Task345.lemma62_S1
