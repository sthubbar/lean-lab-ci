import LeanLab.ExceptionalSet.TailParameters385

/-!
A clean supply for the sealed tail leaf of Decomp371b.
Source: P0082 page 365 display 24.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.TailSupply385

open Real MeasureTheory Set
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (calE majorArcs)
open LeanLab.ExceptionalSet.DecompJ200 (minorInt)
open LeanLab.ExceptionalSet.Decomp371b (truncatedMinor)

/-- The exact sealed tail leaf follows from the proved absolute tail and growth estimates.
Source: P0082 page 365 display 24. This uses no admitted analytic input. -/
theorem leaf_tail_supplied (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (δ κ : ℝ) (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℕ,
      ‖minorInt γ δ κ N n - truncatedMinor γ δ κ N n‖ ≤
        F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2 := by
  obtain ⟨N₀, hN₀⟩ := TailParameters385.tail_parameters_eventually γ h1 h2 δ κ hδ hκ
  refine ⟨N₀, fun N hN n => ?_⟩
  obtain ⟨hX, hP, hd0, hd1, hb⟩ := hN₀ N hN
  have ht := PrimeTail385.truncation_error_le
    (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N ^ (-(1 / 8 : ℝ)))
    (F γ n) (F γ N ^ (6 * δ)) hX hd0 hd1 hP
    (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ
  simpa only [minorInt, truncatedMinor, PrimeTail385.integrand] using ht.trans hb

end LeanLab.ExceptionalSet.TailSupply385
