import LeanLab.Zhao2025.GOrder

/-!
The denominator in the density ratios is uniformly positive.
Source: Zhao 2025, displays 3.22 and 3.23, page 10.
https://arxiv.org/abs/2511.05631v2
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task56
open LeanLab.Zhao2025.U6841

/-- For nonpositive z, G at z is at least its exact value 8 over 9 at zero. -/
theorem Gz_negative_lower (z : ℝ) (hz : z ≤ 0) : 8 / 9 ≤ Gz z := by
  have h := (Gz_order z 0 hz).2
  simpa only [Gz, G_zero] using h

#print axioms Gz_negative_lower
end LeanLab.Zhao2025.Task56
