/- AI wrote the Lean code. Goldbach is open.
Task616 U-1690, the exact finite rational endpoint for P0072 p. 63 Lemma 4.
The arithmetic certificate is separate from analytic sieve validity. -/
import LeanLab.AlmostPrimeSums.Certificate616Step30
namespace LeanLab.AlmostPrimeSums.Certificate616

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The last checked table has exact lower numerator 26768752 at exponent six. -/
theorem endpoint_value : (row table30 2000).1 = 26768752 := by
  decide +kernel

/-- The rational step certificate exceeds the printed lower coefficient. -/
theorem endpoint : (26.4612 : ℚ) ≤ (row table30 2000).1 / (scale : ℚ) := by
  rw [endpoint_value]
  norm_num [scale]

/-- The exact remaining rational slack is 0.307552. -/
theorem endpoint_margin :
    ((row table30 2000).1 : ℚ) / scale - 26.4612 = 0.307552 := by
  rw [endpoint_value]
  norm_num [scale]

end LeanLab.AlmostPrimeSums.Certificate616
