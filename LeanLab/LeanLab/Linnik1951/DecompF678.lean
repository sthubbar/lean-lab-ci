/-
Decomposition of continuous_lnL_line1622 into elementary continuity steps.
The continuity of the principal logarithm of the L-function along the Mellin line
follows from: (1) the L-function is continuous along the line, (2) the L-function
avoids the negative real axis when it is nonvanishing on the line, (3) the principal
logarithm is continuous on the slit plane, and (4) the composition of continuous
functions is continuous.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_lineBound_lnL1622
import LeanLab.Linnik1951.Supply471
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Log
import Mathlib.Topology.Algebra.Order

namespace LeanLab.Linnik1951

/-- LEAF. The L-function of a nonprincipal character is continuous along the Mellin line
1/2 + 1/ln N + i t as a function of t. This follows from the holomorphy of the L-function
and the continuity of the Mellin line in t. -/
theorem LEAF_continuous_LFunction_on_mellinLine (N q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Continuous fun t : ℝ => DirichletCharacter.LFunction χ (mellinLine1622 N t) := by
  sorry

/-- LEAF. If the L-function of a nonprincipal character is nonvanishing on the Mellin line,
then its image avoids the negative real axis (the branch cut of the principal logarithm).
That is, the image is contained in the slit plane ℂ \ {z : ℝ | z ≤ 0}. -/
theorem LEAF_mellinLine_image_in_slitPlane_of_nonzero (N q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hz : ∀ t : ℝ, DirichletCharacter.LFunction χ (mellinLine1622 N t) ≠ 0) :
    ∀ t : ℝ, DirichletCharacter.LFunction χ (mellinLine1622 N t) ∈ Complex.slitPlane := by
  sorry

/-- LEAF. The principal complex logarithm is continuous on the slit plane ℂ \ {z : ℝ | z ≤ 0}. -/
theorem LEAF_continuous_complex_log_on_slitPlane :
    ContinuousOn Complex.log Complex.slitPlane := by
  sorry

/-- LEAF. If a function f : ℝ → ℂ is continuous and its image is contained in the slit plane,
then the composition Complex.log ∘ f is continuous on ℝ. -/
theorem LEAF_continuous_composition_with_slitPlane {f : ℝ → ℂ} (hf : Continuous f)
    (himg : ∀ t : ℝ, f t ∈ Complex.slitPlane) :
    Continuous fun t : ℝ => Complex.log (f t) := by
  sorry

/-- Assembly: The principal logarithm of the L-function along the Mellin line is continuous
in the height parameter t, provided the L-function is nonvanishing on the line.
This is proved by combining the four LEAF lemmas above. -/
theorem continuous_lnL_line1622_F678 :
    ∀ (N : ℕ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      (∀ t : ℝ, DirichletCharacter.LFunction χ (mellinLine1622 N t) ≠ 0) →
        Continuous fun t : ℝ =>
          Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t)) := by
  intro N q _ χ hχ hz
  have h₁ : Continuous fun t : ℝ => DirichletCharacter.LFunction χ (mellinLine1622 N t) :=
    LEAF_continuous_LFunction_on_mellinLine N q χ hχ
  have h₂ : ∀ t : ℝ, DirichletCharacter.LFunction χ (mellinLine1622 N t) ∈ Complex.slitPlane :=
    LEAF_mellinLine_image_in_slitPlane_of_nonzero N q χ hχ hz
  have h₃ : Continuous fun t : ℝ => Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t)) :=
    LEAF_continuous_composition_with_slitPlane h₁ h₂
  exact h₃

end LeanLab.Linnik1951