/-
P0079 page 10, Section 5, the full weighted trivial-arc moment.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.ScaledMoment396
import LeanLab.LZPowersOfTwo.Decomp375a

open Real Finset MeasureTheory Filter
noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 10, Section 5. This is the exact trivial_moment353
statement. Chebyshev's bound and periodic tail summation discharge it
without a prime number theorem input or an OPEN leaf. -/
theorem trivial_moment396 (s : ℕ) (l : ℝ) (μ : ℕ → ℝ) (η ε : ℝ)
    (hs : 2 ≤ s) (hl : l ≠ 0) (hμ : ∀ i, μ i ≠ 0)
    (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℝ in atTop,
      (∫ α in trivial293 X (cutoff293 s μ ε X), primeMoment353 l η ε X α) ≤
        C * X / log X := by
  exact trivial_moment375 s l μ η ε hs hl hμ hη hε hε'

end LeanLab.LZPowersOfTwo
