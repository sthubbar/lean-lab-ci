import LeanLab.HelfgottMajor.Prep1121TailRepair
import LeanLab.HelfgottMajor.Gaussian123Base

/-!
PREP session 2026-11-21, burst unit P1122-0059, REPAIR EASY wiring. Wires the repaired bound
`Prep1121TailRepair.tail_mass_bound_repaired` as the budget B into
`SplitGaussian123.high_zero_bound_of_mass`, which accepts any B.

The repaired bound from `Prep1121TailRepair` gives a summability and an upper bound on the
tsum of `mellinMassTerm` over `TailIdx χ T`. The type `TailIdx χ T` is exactly the index type
used by `high_zero_bound_of_mass`, so the wiring is a direct application: take B to be the
repaired bound, feed the summability and budget into `high_zero_bound_of_mass`, and get the
norm bound on `highZeros`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.Prep1121TailWire
open Real LeanLab.HelfgottArcs
open LeanLab.HelfgottMajor.SplitGaussian123
open LeanLab.HelfgottMajor.Prep1121TailRepair

/-- PROVED. Wiring: plug the repaired bound from `Prep1121TailRepair.tail_mass_bound_repaired`
as B into `SplitGaussian123.high_zero_bound_of_mass`. The repaired bound gives both the
summability and the budget; `high_zero_bound_of_mass` accepts any B, so the repaired bound
slots in directly. The index type `TailIdx χ T` is definitionally the same as the subtype in
`high_zero_bound_of_mass`. -/
theorem tail_mass_integral_repaired (hB : MainHyps123.BookZeroCount)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (δ x T : ℝ)
    (hx : 1 ≤ x)
    (hT : max (4 * π ^ 2 * |δ|) 100 ≤ T)
    (hcor : ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → max 100 (4 * π ^ 2 * |δ|) ≤ |s.im| →
      ‖gaussianMellin δ s‖ + ‖gaussianMellin δ (1 - s)‖ ≤ 4.226 * corEnvelope δ s.im) :
    ‖highZeros χ δ x T‖ ≤
      (2 * 4.226 * (TailIntegral123.expTailIntegral q T +
        TailIntegral123.gaussianTailIntegral q δ T) +
      4 * 4.226 * tailEnv δ T * ZeroCount1623.bookError q T) * x := by
  obtain ⟨hsum, hbudget⟩ := tail_mass_bound_repaired hB q χ hχ δ T hT hcor
  exact high_zero_bound_of_mass χ δ x T
    (2 * 4.226 * (TailIntegral123.expTailIntegral q T +
      TailIntegral123.gaussianTailIntegral q δ T) +
    4 * 4.226 * tailEnv δ T * ZeroCount1623.bookError q T)
    hx hsum hbudget

end LeanLab.HelfgottMajor.Prep1121TailWire

#print axioms LeanLab.HelfgottMajor.Prep1121TailWire.tail_mass_integral_repaired
