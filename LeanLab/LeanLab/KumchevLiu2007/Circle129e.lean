/-
Kumchev and Liu, arXiv 0801.0130, paper P0088. Route burst session 8, p3, 2026-11-12.
Upstream file for `Decomp129`: the major and minor arc LEAF statements, displays 28
and 32 of pages 6 and 7, on the range of the leaf `prop1_meansq_large`, epsilon
in 5/18 to 11/18 and H above X to the 1 minus epsilon, at most Y. The paper does
not write this range; the leaves keep that status. The circle method setup is the
one of `Circle129d`. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Circle129d

namespace LeanLab.KumchevLiu2007.Task129e

open Real Complex LeanLab.KumchevLiu2007 Task129d
open scoped BigOperators

/-- LEAF, route burst session 8 p3. Display 28 on the unwritten range. LEAF, route burst session 8 p3, UNWRITTEN RANGE. Page 6 display 28 with eta
equal to 1/4 for lambda1 equal to varpi and lambda2 equal to lambda0, on the range
of `prop1_meansq_large`: epsilon in 5/18 to 11/18, H at least the smaller of
X to the 7/18 plus epsilon and Y, H above X to the 1 minus epsilon and at most Y,
with Y equal to X to the 7/12 plus epsilon over 2, P equal to L to the B and Q
equal to H over P, where Y is replaced by Y P to the minus 2 in the bounds for H as
in `major_arc_display28` of `Circle129d`. The argument of pages 5 and 6 is the same, but the paper
verifies its hypotheses on page 15 only on the written range. -/
theorem major_arc_display28_large : (
  ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → 5 / 18 < ε → ε ≤ 11 / 18 →
      min (X ^ (7 / 18 + ε)) (X ^ (7 / 12 + ε / 2) / (Real.log X ^ B) ^ 2) ≤ H → X ^ (1 - ε) < H →
      H ≤ X ^ (7 / 12 + ε / 2) / (Real.log X ^ B) ^ 2 → ∀ n : ℕ,
        ‖majorInt X (X ^ (7 / 12 + ε / 2)) (Real.log X ^ B) (H / Real.log X ^ B) n -
          series2W n (Real.log X ^ B) *
            (singIntW X (X ^ (7 / 12 + ε / 2)) (Real.log X ^ B) n : ℂ)‖ ≤
          C * Real.sqrt (X ^ (7 / 12 + ε / 2)) * (Real.log X ^ B) ^ (-(1 / 4 : ℝ))
  ) := by
  sorry

/- The statement above is proved in `Circle129f` from display 29 and a narrower
kernel leaf, route burst session 8 p3. -/

end LeanLab.KumchevLiu2007.Task129e
