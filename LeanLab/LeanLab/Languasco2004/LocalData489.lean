/-
Local rational data for PP1993 pages 43, 46 and 47.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp489f
import LeanLab.Languasco2004.MinorData489

namespace LeanLab.Languasco2004.Decomp489b
open Finset Real MeasureTheory Decomp279b Decomp413a Decomp413b Decomp489a Decomp489f
noncomputable section

/-- Page 43: Q equals the square root of H divided by two. -/
def fareyOrder (H : ℝ) : ℝ := Real.sqrt H / 2

/-- Page 46 before display 14: a symmetric envelope of the punctured Farey arc.
For q at most L to B the small major interval is removed. -/
def puncturedEnvelope (N Y H B : ℝ) (q : ℕ) : Set ℝ :=
  Set.Icc (-(1 / ((q : ℝ) * fareyOrder H))) (1 / ((q : ℝ) * fareyOrder H)) \
    (if (q : ℝ) ≤ Real.log N ^ B then
      Set.Ioo (-(Real.log N ^ (2 * B) / ((q : ℝ) * Y)))
        (Real.log N ^ (2 * B) / ((q : ℝ) * Y)) else ∅)

/-- Page 47 display 15: principal mass on the punctured rational envelope. -/
def principalArcMass (N Y H B : ℝ) (q : ℕ) : ℝ :=
  ∫ t in puncturedEnvelope N Y H B q, ‖rationalWeight q * secondModel Y t‖ ^ 2

/-- Page 47 display 20: remainder mass on the punctured rational envelope. -/
def remainderArcMass (N Y H B : ℝ) (q a : ℕ) : ℝ :=
  ∫ t in puncturedEnvelope N Y H B q, ‖secondRemainder Y q a t‖ ^ 2

/-- Page 47 display 16: good characters have no zero in the printed rectangle.
The principal pole is excluded by the existing zero counting convention. -/
def goodCharacters (q : ℕ) (N Y B : ℝ) : Finset (DirichletCharacter ℂ q) :=
  by
  classical
  exact if h : q = 0 then ∅ else
    letI : NeZero q := ⟨h⟩
    Finset.univ.filter (fun χ => ∀ ρ : ℂ,
    (χ ≠ 1 ∨ ρ ≠ 1) → 1 - 2 * B * Real.log (Real.log N) / Real.log N ≤ ρ.re →
    ρ.re ≤ 1 → |ρ.im| ≤ Y → DirichletCharacter.LFunction χ ρ ≠ 0)

/-- Page 47 display 20: the good character energy including q divided by phi q. -/
def goodEnergy (q : ℕ) (N Y H B : ℝ) : ℝ :=
  (q : ℝ) / Nat.totient q * ∑ χ ∈ goodCharacters q N Y B,
    ∫ t in Set.Icc (-(1 / ((q : ℝ) * fareyOrder H)))
      (1 / ((q : ℝ) * fareyOrder H)), ‖characterSum χ Y t‖ ^ 2

end
end LeanLab.Languasco2004.Decomp489b
