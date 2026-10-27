/-
The minor arc L4 input reduced to a sup bound, U-0996, run 20261019T0103Z-31797, T2.
∑_{k∈m} |S(k)|⁴ ≤ (sup_m |S|)² · M ∑ |Φ|², by Parseval. With Vinogradov's minor arc bound
sup_m |S| ≪ x (log x)^{-A}, this is the L4 input of MVInputs at log power strength.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.MVConditional

open ZMod Finset

namespace LeanLab.ExceptionalSet.MV
open LeanLab.Routes.R0001

variable {M : ℕ} [NeZero M]

theorem minor_L4_le_sup (Φ : ZMod M → ℂ) (m : Finset (ZMod M)) {U : ℝ}
    (hU : ∀ k ∈ m, ‖𝓕 Φ k‖ ≤ U) :
    ∑ k ∈ m, ‖𝓕 Φ k‖ ^ 4 ≤ U ^ 2 * ((M : ℝ) * ∑ j, ‖Φ j‖ ^ 2) := by
  rw [← dft_parseval_norm]
  calc ∑ k ∈ m, ‖𝓕 Φ k‖ ^ 4 = ∑ k ∈ m, ‖𝓕 Φ k‖ ^ 2 * ‖𝓕 Φ k‖ ^ 2 := by
        refine Finset.sum_congr rfl fun k _ => by ring
    _ ≤ ∑ k ∈ m, U ^ 2 * ‖𝓕 Φ k‖ ^ 2 := by
        refine Finset.sum_le_sum fun k hk => ?_
        gcongr
        exact hU k hk
    _ = U ^ 2 * ∑ k ∈ m, ‖𝓕 Φ k‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ U ^ 2 * ∑ k, ‖𝓕 Φ k‖ ^ 2 := by
        gcongr
        exact Finset.subset_univ _

/-- The minor arc term of the skeleton from a sup bound: `M · L4 / T² ≤ M² U² ‖Φ‖₂² / T²`. -/
theorem minorTerm_le_sup (Φ : ZMod M → ℂ) (m : Finset (ZMod M)) {U T : ℝ}
    (hU : ∀ k ∈ m, ‖𝓕 Φ k‖ ≤ U) :
    (M : ℝ) * (∑ k ∈ m, ‖𝓕 Φ k‖ ^ 4) / T ^ 2
      ≤ (M : ℝ) * (U ^ 2 * ((M : ℝ) * ∑ j, ‖Φ j‖ ^ 2)) / T ^ 2 := by
  gcongr
  exact minor_L4_le_sup Φ m hU

end LeanLab.ExceptionalSet.MV
