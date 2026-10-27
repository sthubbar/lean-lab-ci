/-
P0080 Hathi 2021, arXiv 2109.13174v3, pages 7 to 8, the coefficient bookkeeping in the proof of
Lemma 2.3 that gives (2.10), `c_{0,l} = 75/32 c_{1,l} + 105/32 c_{2,l}`.
* `S' = (2/5) S'' = -S''`: the Legendre symbol `(2/5) = -1`, so the `(h/5)` part of `κ(h)` cancels.
* What remains of `κ(h) = 15(5 - 3(h/5))/32` on `3 ∣ h`, `5 ∤ h` is `15 · 5/32 = 75/32`.
* `45/8 = 75/32 + 105/32`, the split of the `15 ∣ h` term into the `3 ∣ h` sum and the `15 ∣ h` sum.
Unit U-6160, CLOUD 20261020T0717Z-cloud37. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.Hathi2021.Coeffs

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- `(2/5) = -1`. -/
theorem legendre_two_five : legendreSym 5 2 = -1 := by
  rw [legendreSym.at_two (by norm_num)]
  decide

/-- The mean part of `κ(h)` on `3 ∣ h`, `5 ∤ h`. -/
theorem kappa_mean : (15 * 5 / 32 : ℚ) = 75 / 32 := by norm_num

/-- The split behind (2.10). -/
theorem coeff_split : (45 / 8 : ℚ) = 75 / 32 + 105 / 32 := by norm_num

end LeanLab.Hathi2021.Coeffs
