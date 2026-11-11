import LeanLab.LanguascoPintzZaccagnini2007.Decomp481b

open Finset Real
open scoped Classical

theorem leaf_real_zero_conductor481 (hzero : LeanLab.LPZ2007.RealZeroStatement481)
    (H : ℝ) (hH : 1 ≤ H) :
    ∃ c : ℝ, 0 < c ∧ ∀ X : ℕ, ∀ r : ℕ, 1 ≤ r → ∀ χ : LeanLab.LPZ2007.DirichletCharacter ℂ r,
      (∀ a, (χ a).im = 0) → ∀ δ : ℝ, 0 < δ → δ ≤ H / Real.log X →
        LeanLab.LPZ2007.Lfun481 χ (1 - (δ : ℂ)) = 0 → c * LeanLab.LPZ2007.Lg (X : ℝ) ^ 2 ≤ (r : ℝ) := by
  sorry
