/-
CODEX task59. AI wrote the Lean code. Binary Goldbach is open.
The 4.45 constant is a lab bound using the method of Chirre and Hagen.
The conclusion remains CONDITIONAL ON every named input below and RH.
The split U6806 import exports the existing theorem with its unchanged statement.
-/
import LeanLab.Routes.U1505Theta6HSW
import LeanLab.ChirreHagen2025.U6806Theorem2Sp

namespace LeanLab.Routes.U1505

open Real Chebyshev
open LeanLab.ChirreHagen2025
open LeanLab.Dudek2014.Section22
open LeanLab.Dudek2014.SigmaH (HSWN70)
open LeanLab.PNTPort.ExplicitPsi1.FirstDiff (HSWHead14)
open LeanLab.PNTPort.ExplicitPsi1.Trivial (gZ ZIdx)

/-- The U6806 J bound composed with the HSW theta bound at the true ordinates.
CONDITIONAL ON the displayed inputs. -/
theorem goldbach_445_of_u6806_hsw {Z : ℕ → Finset ZIdx}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 →
      SmoothT2.ExplicitA gZ Z δ)
    (hH : RiemannHypothesis → SmoothT2.HadamardK gZ)
    (h14 : SmoothT2.Ordinates14 gZ)
    (hN : RiemannHypothesis → Lemma26B.BPTN gZ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18))
    (hNz : HSWN70 gZ) (hHz : HSWHead14 gZ) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 4.45 * Real.log x ^ 2 :=
  goldbach_445_of_J_hsw
    (fun hRH => SmoothT2.theorem2_u6806 (hE hRH) (hH hRH) h14 (hN hRH))
    hEv hNz hHz h14

end LeanLab.Routes.U1505

#print axioms LeanLab.Routes.U1505.goldbach_445_of_u6806_hsw
#check LeanLab.Routes.U1505.goldbach_445_of_u6806_hsw
