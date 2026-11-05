import Mathlib

/-!
Task345. The three ranges in the written proof of Schoenfeld Theorem 6 star.
Source page 356 and the table on page 358.
https://doi.org/10.1090/S0025-5718-1976-0457374-X
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.LiuWang2002.Task345
open Real

/-- LEAF. Schoenfeld 1976, page 356, proof of display 5.1 star, small range.
The proof cites Rosser and Schoenfeld 1962, display 4.5, for this range.
This leaf bounds only theta on the finite interval through 10 to the eighth.
The cited 1962 original is inaccessible in this run. -/
theorem theta_small (X : ℝ) (hX : 0 < X) (hSmall : X ≤ 10 ^ 8) :
    Chebyshev.theta X < 1.001093 * X := by
  sorry

/-- LEAF. Schoenfeld 1976, page 356, proof of display 5.1 star, middle range.
The written proof uses display 9.3, the table on page 358 and the cutoffs
exp 18.43, exp 18.45 and exp 18.5. All endpoints are retained inside this
bounded interval. This leaf contains no estimate for arbitrary large X. -/
theorem theta_middle (X : ℝ) (hSmall : 10 ^ 8 < X) (hLarge : X < exp 18.7) :
    Chebyshev.theta X < 1.001093 * X := by
  sorry

/-- LEAF. Schoenfeld 1976, page 358, table row b equal to 18.7.
The table gives the relative psi error 1.0765 times 10 to the minus 3.
Its upper side is the large range input used on page 356 to prove 5.1 star.
The meaning and monotonic use of the table are explained on page 353.
This is only the large range psi error, without the prime power correction. -/
theorem psi_large (X : ℝ) (hLarge : exp 18.7 ≤ X) :
    Chebyshev.psi X - X < 0.0010765 * X := by
  sorry

/-- The exact global theta estimate of display 5.1 star on page 356.
CONDITIONAL ON theta_small, theta_middle and psi_large.
The large range uses Mathlib theta_le_psi and the printed table margin. -/
theorem theta_upper_from_regions (X : ℝ) (hX : 0 < X) :
    Chebyshev.theta X < 1.001093 * X := by
  by_cases hSmall : X ≤ 10 ^ 8
  · exact theta_small X hX hSmall
  · by_cases hLarge : exp 18.7 ≤ X
    · have hp := psi_large X hLarge
      have ht := Chebyshev.theta_le_psi X
      nlinarith
    · exact theta_middle X (lt_of_not_ge hSmall) (lt_of_not_ge hLarge)

end LeanLab.LiuWang2002.Task345

#print axioms LeanLab.LiuWang2002.Task345.theta_small
#print axioms LeanLab.LiuWang2002.Task345.theta_middle
#print axioms LeanLab.LiuWang2002.Task345.psi_large
#print axioms LeanLab.LiuWang2002.Task345.theta_upper_from_regions
