/-
Kumchev and Liu 2007, sums of primes and squares of primes in short intervals.
SPLIT of Task628.major_arc_block, BlockInputs628.lean, FREE-nv-glm2 task2981.

The major-arc estimate is obtained from the four-term Fourier decomposition and
four error estimates already isolated in Prep1121KLMajorArc. Its two analytic
character-defect bounds are the only inputs left open by this file.

The assembly major_arc_block_F2981 has the exact statement of the target and
is proved from the two leaves with no sorry of its own.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.BlockInputs628
import LeanLab.KumchevLiu2007.Prep1121KLMajorArc

namespace LeanLab.KumchevLiu2007.F2981

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Task628
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF. Prime-character correction estimate for the major-arc proof. For
every positive logarithmic parameter B and positive epsilon at most seven
eighteenths, there are C and X0 such that every Dirichlet character defect on
a prime subwindow is at most C times the window length times the fourth
negative logarithmic power. -/
theorem major_arc_prime_correction_F2981 :
    Prep1121KLMajor.A12Corr := by
  sorry

/-- LEAF. Rough-weight character correction estimate for the major-arc proof.
For every positive logarithmic parameter B and positive epsilon at most seven
eighteenths, there are C and X0 such that the squared integral of every
Dirichlet-character defect for the rough weight is at most C times the squared
block width times the fourth negative logarithmic power. -/
theorem major_arc_rough_correction_F2981 :
    Prep1121KLMajor.A22Corr := by
  sorry

/-- Assembly. The exact statement of Task628.major_arc_block, proved from the
prime-character and rough-weight correction leaves with no sorry of its own. -/
theorem major_arc_block_F2981 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ n : ℕ, ‖majorError X (windowY X ε) H (Real.log X ^ B) n‖ ^ 2 ≤
          C * windowY X ε / Real.log X ^ A := by
  exact Prep1121KLMajor.major_arc_block_of_char_inputs
    major_arc_prime_correction_F2981 major_arc_rough_correction_F2981 A hA

end LeanLab.KumchevLiu2007.F2981

#print axioms LeanLab.KumchevLiu2007.F2981.major_arc_block_F2981
