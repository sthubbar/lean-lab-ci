import Mathlib

open Real Chebyshev

-- Enumerate what Mathlib knows about Chebyshev.theta bounds.
#check @Chebyshev.theta_le_log4_mul_x
#check @Chebyshev.theta
#check @Chebyshev.psi_le_log4_mul_x

-- Direct search attempt on the actual goal shape.
example (x : ℝ) (hx : exp 37 < x) :
    |Chebyshev.theta x - x| ≤ 8.6315e-7 * x / log x := by
  exact?
