/-
P0088 pages 7 and 8, minor arc transference from the kernel routes.
The shared definitions and elementary identities are in Kernel634Base.
Every moved declaration retains its statement and proof byte for byte.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Eq33RouteA
import LeanLab.KumchevLiu2007.Eq33RouteB

namespace LeanLab.KumchevLiu2007.Task556d

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF. P0088 page 7 display 29 with I1 bounded by a constant times Y.
This is the short Dirichlet kernel and Cauchy step. It has no logarithmic
saving hypothesis and no short interval character input. The bound M is
any nonnegative uniform majorant for the weighted quadratic minor mass. -/
theorem minor_mean_square_of_kernel (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ K X0 : ℝ, 0 < K ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ M : ℝ, 0 ≤ M →
      (∀ β ∈ Set.Icc (0 : ℝ) 1,
        kernelMass (windowY X ε) H (Real.log X ^ B) β ≤ M) →
      (∑ n ∈ intervalNumbers X H,
        ‖minorCoefficient X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2) ≤
          K * windowY X ε * M := by
  exact Eq33RouteA.minor_mean_square_of_kernel_route B ε hB hε

/-- LEAF. P0088 page 8 displays 30 and 31 and Gallagher's lemma applied
to the explicit rough A2.3 input. Only the local quadratic mass is bounded.
There is no representation count and no mean square over n in this leaf. -/
theorem kernel_mass_of_A23 (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B) (hε : 0 < ε)
    (hinput : ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
      (∫ t in windowY X ε / 4..windowY X ε,
        ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
          C * H ^ 2 / Real.log X ^ (A + 2)) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ β ∈ Set.Icc (0 : ℝ) 1,
        kernelMass (windowY X ε) H (Real.log X ^ B) β ≤ C * H / Real.log X ^ A := by
  exact Eq33RouteB.kernel_mass_of_A23_route A B ε hA hB hε hinput

/-- Exact minor transference statement from the two smaller kernel tasks.
CONDITIONAL ON the weighted Fourier and local Gallagher leaves. -/
theorem minor_arc_transference_from_kernel (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hε : 0 < ε)
    (hinput : ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
      (∫ t in windowY X ε / 4..windowY X ε,
        ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
          C * H ^ 2 / Real.log X ^ (A + 2)) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      (∑ n ∈ intervalNumbers X H,
        ‖minorCoefficient X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2) ≤
          C * H * windowY X ε / Real.log X ^ A := by
  obtain ⟨K, Xk, hK, hXk, hfourier⟩ := minor_mean_square_of_kernel B ε hB hε
  obtain ⟨C, Xc, hC, hXc, hmass⟩ := kernel_mass_of_A23 A B ε hA hB hε hinput
  refine ⟨K * C, max Xk Xc, mul_pos hK hC, hXk.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHX
  have hX2 : 2 ≤ X := hXk.trans ((le_max_left _ _).trans hX)
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hH0 : 0 < H := (Real.rpow_pos_of_pos (by linarith : 0 < X) _).trans_le hH
  have hm : 0 ≤ C * H / Real.log X ^ A := by positivity
  have hs := hfourier X H ((le_max_left _ _).trans hX) hH hHX
    (C * H / Real.log X ^ A) hm (hmass X H ((le_max_right _ _).trans hX) hH hHX)
  calc
    _ ≤ _ := hs
    _ = _ := by ring

end LeanLab.KumchevLiu2007.Task556d
