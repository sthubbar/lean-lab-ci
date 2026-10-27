/-
P0095 Lu 2010, pages 2391 to 2392 equations 84 to 86 and Theorem.
CODEX task47, unit U-8106. AI wrote this Lean code. Binary Goldbach is open.
The theorem now takes the cited major formulas and zero mass 39.
Neither equation 86 nor the textbook minor arc bound is a hypothesis.
-/
import LeanLab.ExceptionalSet.Lu2010Eq63
import LeanLab.ExceptionalSet.Lu2010Singular
import LeanLab.ExceptionalSet.Lu2010Bound12

namespace LeanLab.ExceptionalSet.Lu2010Main63
open Finset Real
open LeanLab.ExceptionalSet.Lu2010Assembly
open LeanLab.ExceptionalSet.Lu2010Arcs
open LeanLab.ExceptionalSet.Lu2010Formula63
open LeanLab.ExceptionalSet.Lu2010Eq63
open LeanLab.ExceptionalSet.Lu2010Dirichlet

/-- The cited major arc displays, for the concrete expression 63 and the explicit singular product. -/
structure MajorInputs63 (family : ℕ → Finset Exponent) (M : ℕ → ℝ) where
  N0 : ℕ
  Cerr : ℝ
  c1 : ℝ
  c1_pos : 0 < c1
  lower : ∀ N, N0 ≤ N →
    (∀ k ∈ Win N, Even k →
      LeanLab.ExceptionalSet.BG2026.Sing k * (bb N - aa N) * dd N *
        ((Real.log (Real.log (Real.log N)))⁻¹ - Cerr * (Real.log (Real.log N)) ^ (-(1 / 2) : ℝ))
        - ‖printed63 N (family N) (M N) k‖ < (D1c N k).re) ∨
    (∀ k ∈ Win N, Even k →
      LeanLab.ExceptionalSet.BG2026.Sing k * (bb N - aa N) * dd N * c1 * PP N ^ (-0.00001 : ℝ) *
        Real.log (PP N) * (2 * c⁻¹ - Cerr * (Real.log (Real.log (Real.log N))) ^ (-0.1 : ℝ))
        - ‖printed63 N (family N) (M N) k‖ ≤ (D1c N k).re)

/-- Equation 86 and the singular product bound supply the other fields of the previous bundle. -/
noncomputable def MajorInputs63.toInputsL {family : ℕ → Finset Exponent} {M : ℕ → ℝ}
    (J : MajorInputs63 family M) (h39 : Mass39 family) : InputsL := by
  let hex := eq86_of_eq63_and_mass39 family M h39
  let C86 := hex.choose
  let N1 := hex.choose_spec.2.choose
  have h86 := hex.choose_spec.2.choose_spec
  exact
    { D6 := fun N k => printed63 N (family N) (M N) k
      S := LeanLab.ExceptionalSet.BG2026.Sing
      S_ge := fun k _ => LeanLab.ExceptionalSet.Lu2010Singular.singular_product_ge_one k
      N0 := max J.N0 N1
      Cerr := J.Cerr
      c1 := J.c1
      c1_pos := J.c1_pos
      C86 := C86
      lower := fun N hN => J.lower N (le_trans (le_max_left _ _) hN)
      eq86 := fun N hN => h86 N (le_trans (le_max_right _ _) hN) }

/-- Lu's printed theorem, conditional on displays 84 or 85 and the cited zero mass 39. -/
theorem lu_of_major_and_mass39 {family : ℕ → Finset Exponent} {M : ℕ → ℝ}
    (J : MajorInputs63 family M) (h39 : Mass39 family) : LeanLab.ExceptionalSet.PowerBound 0.879 :=
  LeanLab.ExceptionalSet.Lu2010Bound12.lu_of_major_and_eq86 (J.toInputsL h39)

end LeanLab.ExceptionalSet.Lu2010Main63

#print axioms LeanLab.ExceptionalSet.Lu2010Main63.MajorInputs63.toInputsL
#print axioms LeanLab.ExceptionalSet.Lu2010Main63.lu_of_major_and_mass39
